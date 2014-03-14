Require Import Bool Arith List CpdtTactics CorgiTactics.
Set Implicit Arguments.

Definition tuple : Set :=
  list nat.

Definition relation : Set :=
  list tuple.

Inductive Bool : Set :=
  | BTrue : Bool
  | BFalse : Bool.

(**
  Query language syntax
**) 
Inductive Pred : Set :=
  | PredBool : Bool -> Pred
  | PredFirst1 : Pred.  (* represents true if tuple[0]=1 *)

Inductive Query : Set := 
  | Select : Bool -> Query
  | Project : nat -> Query
  | SelectIf : Pred -> Query(* overlaps with Select *)
  | JoinFirst : Query. 
(**
  end (Query language syntax)
**)


Fixpoint projectTuple (t: tuple) (index: nat) : option tuple :=
  match t with
  | nil => None
  | n :: rem => match index with
                   | 0 => Some (n :: nil)
                   | S index' => projectTuple rem index'
                   end
  end.

Fixpoint project (input: relation) (index: nat) :=
      match input with
      | nil => Some nil
      | tup :: rem => match (projectTuple tup index) with
                            | None => None
                            | Some tup' => let remres := project rem index in
                               match remres with 
                                 | None => None
                                 | Some remres' => Some (tup' :: remres')       
                               end
                         end
      end.

Fixpoint select (pr: Pred)  (input: relation) :=
  match pr with
    | PredBool b =>
      match b with
        | BTrue => match input with
                   | nil => nil
                   | tup :: rem => tup :: (select pr rem)
               end
        | BFalse => match input with
                  | nil => nil
                  | _ :: rem => select pr rem
                end
      end
    | PredFirst1 => match input with
                      | nil => nil
                      | t :: rem => match t with
                                      | 1 :: _ => t :: (select pr rem)
                                     (* picking semantics that length 0 tuples just fail the predicate rather than fail *)
                                      | _ => select pr rem
                                    end
                    end                  
    end.
(*
match input with
    | nil => nil
    | tup :: rem => match b with
                      | BTrue => tup :: (select rem b)
                      | BFalse => select rem b
                    end
    end.
*)


Definition joineq (t1 : tuple) (t2 : tuple) : bool :=
  match t1, t2 with
    | t1first :: _, t2first :: _ => beq_nat t1first t2first
    | _, _ => false
  end. 

Fixpoint nljoin_inner (t : tuple) (r : relation) : relation :=
match r with
      | t' :: r' => if joineq t t' then (t ++ t') :: nljoin_inner t r' else nljoin_inner t r'
      | nil => nil
    end.

Fixpoint nljoin (r1 : relation) (r2 : relation) : relation :=
  match r1 with
    | t1 :: r1' => (nljoin_inner t1 r2) ++ nljoin r1' r2
    | nil => nil
  end.


Eval simpl in project ((1 :: nil) :: (2 :: nil) :: nil) 0.

Definition runQuery (q : Query) (inputRelation1 : relation) (inputRelation2 : relation) : option relation :=
  match q with 
  | Select b => match b with 
                | BTrue => Some inputRelation1
                | BFalse => Some nil
                end
  | SelectIf pr => Some (select pr inputRelation1)
  | Project index => project inputRelation1 index
  | JoinFirst => Some (nljoin inputRelation1 inputRelation2)
  end.

Eval compute in runQuery JoinFirst ((1::2::nil) :: (2::3::nil) :: nil) ((3::4::nil) :: (1::10::nil) :: (1::12::nil) :: nil).

(**
  IMP syntax
**)
Inductive VarName : Set :=
  | ResultName : VarName
  | IndexedVarName : nat -> VarName.

Inductive BExp : Set :=
  | BoolBExp : Bool -> BExp
  | Pred1Exp : BExp. 

Inductive Exp : Set :=
  | InputRelation1 : Exp
  | InputRelation2 : Exp
  | RelationExp : relation -> Exp
(*  | TupleExp : tuple -> Exp *)
  | NatExp : nat -> Exp
  | BoolExp : BExp -> Exp.

(* It turns out that Forall is already defined in Coq, so I used ForAll *)
Inductive Statement : Set :=
  | Assign : VarName -> Exp -> Statement
  | ForAll : VarName -> Exp -> Statement -> Statement
  | ProjectTuple : Exp -> VarName -> Statement
  | SelectTuple : Exp -> VarName -> Statement
  | MatchTuples : VarName -> VarName -> Statement.

Inductive ImpProgram : Set :=
  | Seq : Statement -> ImpProgram -> ImpProgram
  | Skip.

(**
   end (IMP syntx
**)

Definition queryToImp (q : Query) : option ImpProgram :=
  match q with
  | Select b => match b with
                | BTrue => Some (Seq (Assign ResultName InputRelation1) Skip) 
                | BFalse => Some (Seq (Assign ResultName (RelationExp nil)) Skip)   
                end
  | Project index => Some 
                     (Seq 
                      (Assign ResultName (RelationExp nil))
                      (Seq
                        (ForAll (IndexedVarName 0) InputRelation1
                          (ProjectTuple (NatExp index) (IndexedVarName 0)))
                        Skip))
  | SelectIf pr => match pr with
                     | PredBool b =>  
                       Some 
                     (Seq 
                      (Assign ResultName (RelationExp nil))
                      (Seq
                        (ForAll (IndexedVarName 0) InputRelation1
                          (SelectTuple (BoolExp (BoolBExp b)) (IndexedVarName 0)))
                        Skip))
                     | PredFirst1 =>
                       Some 
                     (Seq 
                      (Assign ResultName (RelationExp nil))
                      (Seq
                        (ForAll (IndexedVarName 0) InputRelation1
                          (SelectTuple (BoolExp Pred1Exp) (IndexedVarName 0)))
                        Skip))
                    end
   | JoinFirst => Some
                     (Seq
                       (Assign ResultName (RelationExp nil))
                       (Seq
                         (ForAll (IndexedVarName 0) InputRelation1
                           (ForAll (IndexedVarName 1) InputRelation2
                             (MatchTuples (IndexedVarName 0) (IndexedVarName 1))))
                         Skip))

                        
  end.

(* heap is a tuple *)
Fixpoint runStatement (s: Statement) (input1: relation) (input2: relation) (heap: tuple * tuple) (nested: bool) : option relation :=
  match s with
  | Assign ResultName e => match e with
                           | InputRelation1 => Some input1
                           | RelationExp rexp => Some rexp 
                           | _ => None
                           end
  | Assign _ _ => None
  | ProjectTuple (NatExp index) (IndexedVarName vnIndex) =>
          match projectTuple (fst heap) index with
          | Some tup => Some (tup :: nil)
          | None => None
          end
  | ProjectTuple _ _ => None
  | SelectTuple (BoolExp bexp) (IndexedVarName vnIndex) =>
      match bexp with
        | BoolBExp b => match b with
                          | BTrue => Some ((fst heap) :: nil)
                          | BFalse => Some nil
                        end
        | Pred1Exp => match (fst heap) with
                        | 1 :: _ => Some ((fst heap) :: nil)
                        | _ => Some nil
                      end
      end
  | SelectTuple _ _ => None
  | ForAll (IndexedVarName index) _ s' =>
      let fix helper (rel: relation) (nested' : bool) :=
        match rel with
        | nil => Some nil
        | t :: rem => 
          let heap' := if nested' then pair (fst heap) t else pair t nil in
          match (runStatement s' input1 input2 heap' true) with
          | None => None
          | Some res => match (helper rem nested') with
                        | Some rem' => Some (res ++ rem')
                        | None => None
                        end
          end
        end
      in if nested then helper input2 true else helper input1 false 
  | ForAll _ _ _ => None
  | MatchTuples (IndexedVarName vn1) (IndexedVarName vn2) =>
       let (t1, t2) := ((fst heap), (snd heap)) in
       if joineq t1 t2 then Some ((t1 ++ t2) :: nil) else Some nil
  | MatchTuples _ _ => None
  end.

(* proof that the inner loops for nested loop join are equivalent *)
Lemma innerjoinequivalence : forall r''' a r, Some (nljoin_inner a r) = runStatement (ForAll (IndexedVarName 1) InputRelation2 (MatchTuples (IndexedVarName 0) (IndexedVarName 1))) r''' r (pair a nil) true.
Proof.
intros r'''.
intros a.
induction r.
crush.

unfold nljoin_inner.
destruct (joineq a a0) eqn:?.  (* important to keep this for reusing the case assignment later *)
fold nljoin_inner.
unfold runStatement.
break_match; try discriminate.
break_match; try discriminate. 
simpl in Heqo.
rewrite Heqb in Heqo.
unfold runStatement in IHr.
rewrite <- IHr in Heqo0. clear IHr. crush.

simpl in Heqo.
rewrite Heqb in Heqo.
unfold runStatement in IHr.
rewrite <- IHr in Heqo0. clear IHr.
discriminate.

simpl in Heqo.
rewrite Heqb in Heqo.
discriminate.

unfold runStatement; [repeat break_match; try discriminate]; simpl in Heqb0.
crush.
unfold runStatement in IHr; rewrite <- IHr in Heqo0; clear IHr; crush.
crush.
unfold runStatement in IHr; rewrite <- IHr in Heqo0; clear IHr; crush.
Qed.

Lemma innerjoinequivalence' : forall r''' a r, nljoin_inner a r = match runStatement
         (ForAll (IndexedVarName 1) InputRelation2
            (MatchTuples (IndexedVarName 0) (IndexedVarName 1))) r''' r
         (a, nil) true with | Some res => res | None => nil end.
intros; break_match; try discriminate; rewrite <- innerjoinequivalence in Heqo; crush.
Qed.

Section test.
Variable r''' : relation.
Variable r : relation.
Variable a : tuple.
Eval simpl in runStatement
         (ForAll (IndexedVarName 1) InputRelation2
            (MatchTuples (IndexedVarName 0) (IndexedVarName 1))) r''' r
         (a, nil) true.
End test.
Lemma innerjoinequivalence'' : forall a r, Some (nljoin_inner a r) = (fix helper (rel : relation) (nested' : bool) {struct rel} :
          option (list tuple) :=
          match rel with
          | nil => Some nil
          | t :: rem =>
              match
                (if joineq (fst (if nested' then (a, t) else (t, nil)))
                      (snd (if nested' then (a, t) else (t, nil)))
                 then
                  Some
                    ((fst (if nested' then (a, t) else (t, nil)) ++
                      snd (if nested' then (a, t) else (t, nil))) :: nil)
                 else Some nil)
              with
              | Some res =>
                  match helper rem nested' with
                  | Some rem' => Some (res ++ rem')
                  | None => None
                  end
              | None => None
              end
          end) r true.
Proof.
intros.
erewrite innerjoinequivalence. crush.
Grab Existential Variables.
constructor.
Qed.

(* It turns out that we do not (and should not) have
   runImpSmall (small step semantics). Because otherwise
   Coq cannot figure out that our function is structurally
   recursive. Special thanks go to Eric Mullen and Zach
   Tatlock.
*)
Definition runImp (p : ImpProgram) (input1 : relation) (input2 : relation) : option relation :=
  let fix helper (p : ImpProgram) (result: relation) : option relation := 
    match p with
    | Skip => Some result
    | Seq s p' => match (runStatement s input1 input2 (pair nil nil) false) with
                    | Some res => helper p' (result ++ res)
                    | None => None
                  end
    end
  in helper p nil.


Fixpoint runImp' (p: ImpProgram) (input1: relation) (input2 : relation) : option relation :=
  match p with
    | Skip => Some nil
    | Seq s p' => match (runStatement s input1 input2 (pair nil nil) false) with
                    | Some res => match runImp' p' input1 input2 with
                                    | Some remres => Some (res ++ remres)
                                    | None => None
                                      end
                    | None => None
                      end
end.


(** 
  Test cases
**)
Eval compute in let p := queryToImp (Project 0) in
                        match p with 
                          | None => None
                          | Some p' => runImp' p' ((1 :: 2 :: nil) :: (3 :: 4 :: nil) :: nil) nil
end.
(* = Some [(1),(3)] *)

Eval compute in let p := queryToImp (Project 2) in
                        match p with 
                          | None => None
                          | Some p' => runImp' p' ((1 :: 2 :: nil) :: (3::4::nil) :: nil) nil
end.
(* = None *)

Eval compute in let p := queryToImp (Project 1) in
                        match p with 
                          | None => None
                          | Some p' => runImp' p' ((1 :: 2 :: nil) :: (3::4::nil) :: nil) nil
end.
(* = Some [(2),(4)] *)

Eval compute in let p := queryToImp (SelectIf (PredBool BTrue)) in
                          match p with
                            | None => None
                            | Some p' => runImp' p' ((1 :: 2 :: nil) :: (3::4::nil) :: nil) nil
end.
(* = Some [(1,2),(3,4)] *)

Eval compute in let p := queryToImp (SelectIf (PredBool BFalse)) in
                          match p with
                            | None => None
                            | Some p' => runImp' p' ((1 :: 2 :: nil) :: (3::4::nil) :: nil) nil
end.

Eval compute in let p := queryToImp (SelectIf PredFirst1) in
                        match p with 
                          | None => None
                          | Some p' => runImp' p' ((1::2::nil) :: (3::4::nil) :: (0::1::nil) :: (1::6::nil) :: nil) nil
end. 

Eval compute in let p := queryToImp JoinFirst in
  match p with
    | None => None
    | Some p' => runImp' p' ((1::2::nil) :: (2::3::nil) :: nil) ((3::4::nil) :: (1::10::nil) :: (1::12::nil) :: nil)
end.
(* = Some [(1,2),(1,6)] *)

(**
   end (Test cases)
**)

(* this appears to be less straight forward to convert to non-tail calls, but I think
it is possible if we rely on monotonic query processing *)

Ltac inv H := inversion H; subst; clear H.
Ltac unfold_all := repeat match goal with 
                  | [ |- runImp' _ _ _ = _ ] => unfold runImp'; [repeat break_match; try discriminate]
                  | [H: runImp' _ _ _ = _ |- _ ] => unfold runImp' in H; [repeat break_match; try discriminate]
                  | [H: runQuery _ _ _ = _ |- _ ] => unfold runQuery in H; [repeat break_match; try discriminate]
                  | H: project _ _ = _ |- _ => unfold project in H                 
                  | [H: runStatement _ _ _ _ _ = _ |- _ ] => unfold runStatement in H; [repeat break_match; try discriminate]
                end.
Ltac inv_somes := repeat match goal with
                           | [ H: Some _ = Some _ |- _ ] => inv H
                         end.

Lemma some_eq' : forall (A:Type) (p:A) (q:A), Some p = Some q -> p = q.
crush.
Qed.
Lemma some_eq : forall (A:Type) (p : A) (q : A), p = q -> Some p = Some q.
  crush.
Qed.

(* breaking apart a list relation; a Lemma seems unnecessary *)
Lemma some_list_eq : forall (A : Type ) (h : A) t t' (h' : A), Some (h :: t) = Some (h' :: t') -> (t = t') /\ (h = h').
crush.
Qed.

(* breaking apart a list relation; a Lemma seems unnecessary *)
Lemma list_eq : forall (A : Type ) (h : A) t t' (h' : A), h :: t = h' :: t' -> (t = t') /\ (h = h').
crush.
Qed.

Ltac massage_ihr1 := match goal with
                              | H:context [ forall r2 _, runQuery _ _ _ = _ -> runImp' _ _ _ = _ ] |- _  => specialize (H r2); unfold runQuery in H
                     end.

Theorem queryEquivalence'': 
  forall (q : Query) (p : ImpProgram),
    queryToImp q = Some p ->
      forall (r1 r2 r' : relation), runQuery q r1 r2 = Some r' ->
        runImp' p r1 r2 = Some r'. 
  
(* automagic!
  induction q; [
    (* select cases *) 
    intros; destruct b; crush; f_equal; crush
    (* Project case *)
   | intros p Hc; inv Hc; induction r; [
      crush  (* base case *) 
      | intros; [repeat match goal with 
                  | [ |- runImp' _ _ = _ ] => unfold runImp'; [repeat break_match; try discriminate]
                  | [H: runImp' _ _ = _ |- _ ] => unfold runImp' in H; [repeat break_match; try discriminate]
                  | [H: runQuery _ _ = _ |- _ ] => unfold runQuery in H; 
                                                   match goal with 
                                                     | H: project _ _ = _ |- _ => unfold project in H
                                                   end; [repeat break_match; try discriminate]
                  | [H: runStatement _ _ _ = _ |- _ ] => unfold runStatement; [repeat break_match; try discriminate]
               end]]].

Restart.
*)

induction q.

(* Select case *)
intros; destruct b; crush; f_equal; crush.

(* Project case *)
intros p Hc; inv Hc.
induction r1. crush. 

  intros.

unfold_all.
f_equal.
massage_ihr1.
unfold project in IHr1.
apply IHr1 in Heqo6. clear IHr1.
unfold_all.
rewrite Heqo9 in Heqo3. clear Heqo9.
unfold fst in Heqo4.
crush.

fold project in Heqo6.
massage_ihr1.
apply IHr1 in Heqo6. clear IHr1.
unfold_all.
crush.

fold project in Heqo5.      (* new case *)
massage_ihr1.
apply IHr1 in Heqo5. clear IHr1.
unfold_all.
crush.

(* SelectIf case *)
intros p0 Hc; inv Hc.
destruct p.
induction r1; destruct b. crush. crush.

inv H0.
intros.

unfold runQuery in H. simpl in H. inversion H. clear H.
destruct r'. crush. inversion H1. subst a. clear H2.
massage_ihr1.
assert (Some (select (PredBool BTrue) r1) = Some r'). crush.
apply IHr1 in H. clear IHr1.

rewrite H1.

unfold runImp' in H.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
inv Heqo0. inversion H. clear H. 
unfold runStatement in Heqo. inv Heqo.
unfold runStatement in Heqo1.
simpl in H1.
unfold runImp'.
break_match; try discriminate.
break_match.
break_match; try discriminate.
f_equal. simpl. inv Heqo0.
unfold runStatement in Heqo2.
break_match; try discriminate. 
(* crush. *)
inv Heqo2. inv Heqo1. 
unfold runStatement in Heqo. inv Heqo.
unfold select in H1.
(* Note that I cannot prove the remaining with explicit commands. crush 
   (of course) takes care of it. *) 
crush.


break_match; try discriminate.
inv H1. clear Heqo0.
unfold runStatement in Heqo2. 
(* This unfolds brings the contradiction that is required to prove 
   both cases. *)
break_match; discriminate.

(* SelectIf PredBool False *)
intros.
inv H0.
unfold_all.
massage_ihr1.
unfold select in H. fold select in H. (* gets rid of "a" *)
apply IHr1 in H. clear IHr1.
unfold_all.
rewrite Heqo5 in Heqo2.
inv_somes.
simpl. reflexivity.

unfold select in H. fold select in H. (* gets rid of "a" *)
massage_ihr1.
apply IHr1 in H. clear IHr1.
unfold_all.
rewrite Heqo5 in Heqo2.
inv_somes.
discriminate.


(* SelectIf PredFirst1 *)
induction r1. crush.

intros.
inversion H0. clear H0.
unfold runQuery in H.
unfold select in H.
break_match.
massage_ihr1. 
apply IHr1 in H. clear IHr1.
inversion H2 in H. clear H2 H0.
unfold_all.
rewrite Heqo4 in Heqo6. clear Heqo4.
crush.

rewrite Heqo4 in Heqo6. clear Heqo4.
discriminate.

break_match; try discriminate.
unfold_all.
massage_ihr1.
apply IHr1 in H. clear IHr1.
inv H2. clear H0.
unfold_all.
rewrite Heqo3 in Heqo6. clear Heqo3.
crush.

massage_ihr1.
apply IHr1 in H. clear IHr1.
inv H2; clear H0.
unfold_all.
rewrite Heqo3 in Heqo6. clear Heqo3.
discriminate.

break_match; try discriminate.
destruct r'.
discriminate.
apply some_list_eq in H.
destruct H. 
massage_ihr1.
apply some_eq in H. 
apply IHr1 in H. clear IHr1.
inv H2. clear H1.
unfold_all.
rewrite Heqo4 in Heqo6. clear Heqo4.
crush.

destruct r'; rewrite Heqo4 in Heqo6; clear Heqo4; crush.

massage_ihr1.
apply IHr1 in H. clear IHr1.
inv H2. clear H0.
unfold_all; rewrite Heqo4 in Heqo6; clear Heqo4; crush.


(* Join first case *)

Lemma complex_list_eq : forall (A:Type) (a:A) b c d e, Some ((a::b) ++ c) = Some (d :: e) -> (a = d) /\ Some (b++c) = Some e.
Proof.
crush.
Qed. 
intros p0 Hc; inv Hc. 
induction r1. crush. intros.


unfold runQuery in H.
unfold nljoin in H.
unfold runQuery in IHr1. 
unfold nljoin in IHr1.
(* problem here is that I really need to know what r' is to apply IHr1, and despite
relating the result of nljoin_inner to runStatement, innerjoinequiv does not help to apply IHr1 *)
Check innerjoinequivalence'.
erewrite innerjoinequivalence' in H.
simpl in H. break_match; try discriminate.
destruct r'.
Lemma list_nil : forall (A:Type) (a:list A) b, a++b =nil -> a= nil /\ b=nil.
intros.
destruct a; crush.
Qed.


simpl in H. apply IHr1 in H. clear IHr1. unfold_all; rewrite Heqo4 in Heqo5; clear Heqo4; crush.
intros.
simpl in H. destruct (joineq a a0) eqn:?.
(* isn't useful: destruct r'. crush.*)



erewrite innerjoinequivalence' in H.
unfold runStatement in H.
break_match; try discriminate.
fold (runStatement
             (ForAll (IndexedVarName 1) InputRelation2
                (MatchTuples (IndexedVarName 0) (IndexedVarName 1))) 
             r1 r2 (a, nil) true) in Heqo.
unfold runImp'.
repeat break_match; try discriminate. 
inv Heqo0. simpl. unfold runStatement in Heqo2.
repeat break_match; try discriminate. simpl in Heqo0.   Print innerjoinequivalence''.
(*erewrite <- innerjoinequivalence'' in Heqo0.*) assert (Some (nljoin_inner a r2) = Some l0). admit.
clear Heqo0.


(* rest below here *)
induction r2.
intros.
unfold_all.
unfold runQuery in IHr1. unfold nljoin in IHr1.
unfold nljoin in H. simpl in H.

apply IHr1 in H. clear IHr1.
unfold_all; rewrite Heqo5 in Heqo2; clear Heqo5; crush.
unfold runQuery in IHr1.
unfold nljoin in IHr1.
unfold nljoin in H. simpl in H.
apply IHr1 in H. clear IHr1.
unfold_all; rewrite Heqo5 in Heqo2; clear Heqo5; crush.

intros.
unfold runQuery in H.
unfold nljoin in H.
destruct (joineq a a0) eqn:?. 

admit.
unfold runQuery in IHr2. fold nljoin in H.
unfold nljoin in IHr2. fold nljoin in IHr2.

(* see if I can even prove afterwards... *)
assert (Some
           ((fix nljoin_inner (t : tuple) (r : relation) {struct r} :
               relation :=
               match r with
               | nil => nil
               | t' :: r'0 =>
                   if joineq t t'
                   then (t ++ t') :: nljoin_inner t r'0
                   else nljoin_inner t r'0
               end) a r2 ++ nljoin r1 r2) = Some r'). admit.

apply IHr2 in H0. clear IHr2.
unfold runQuery in  IHr1.
unfold runImp' in H0. unfold_all. 


Qed.
(* wish list:
- unify ProjectTuple and SelectTuple by bringing back AppendTuple
- try to remove duplication in proof
*)


Theorem queryEquivalence: 
  forall (q : Query) (p : ImpProgram),
    queryToImp q = Some p ->
      forall (r r' : relation), runQuery q r = Some r' ->
        runImp p r = Some r'.
Proof.
    intros. (* tends to cause weakest induction hyp *)
    induction q.
    (* select cases *)
    destruct b;
    simpl in H; inversion H; crush.

    (* project *)
    revert r' H0. inv H. simpl. 
    induction r; crush. 
    destruct (projectTuple a n) eqn:?.
    destruct (project r n) eqn:?.
    inv H0. 
    

    induction r. crush.
    intros.
    inversion H. clear H2.
    

(* below gets the left hand side of ind hyp *)
    unfold runImp; simpl. 
    repeat break_match. 
    simpl in H0.
    repeat break_match.
    specialize (IHr l1). simpl in IHr. apply IHr in Heqo4.
    f_equal.

    
    inv Heqo. 
    inv Heqo0.
    inv Heqo2.
    inv H0.
  
    unfold runImp in Heqo4. inversion H. inv H1. simpl in *.
    f_equal. inv H0. inv H. 
             

    fold (runStatement  r) in Heqo1.

Focus 2. inv Heqo. inv Heqo0. simpl. f_equal.
    
(* At this point we need to ask how to introduce r'' inductive hyothesis instead *)
    


destruct r. crush. simpl in H0. 
    unfold runImp. unfold runStatement.

    induction p.
    destruct q.
    

    (* Select TRUE and Select FALSE *)
    destruct b;
    simpl in H; inversion H; clear H; clear H2; clear H3;
    compute;
    assumption.
    
    (* Project <index> *)
    
    simpl in H; inversion H.
induction r. crush. 
unfold runImp.
unfold runStatement. 
destruct (tupleHeapLookup (updateTupleHeap nil 0 a) 0).
destruct (projectTuple t n). simpl. 

rewrite <- H3 in IHp.
 
unfold runQuery in H0.
unfold project in H0. 
unfold runImp.
unfold runStatement. 

    
    induction r. 
    unfold runImp. simpl in H0. destruct (projectTuple t n) eqn:?. 
    
        (* r = RCons t r  case *)
    admit.
        (* r = Rnil case *)
        crush.
   
(*
    simpl in H0.
    inversion H0.
    simpl in H. inversion H.
    clear H4. clear H3. clear H2.
    compute.
    intros.
*)

    simpl in H0.
    

    simpl in H0. inversion H0.

    simpl in H0. inversion H0. compute in H2. simpl in H2.
    
    simpl in H. inversion H. clear H. simpl in H0. inversion H0. clear H0. simpl H1.


    induction p. admit. admit.


(* p = Skip  *)    
destruct q. 
(* q = Select *)
destruct b. simpl in H. inversion H. clear H. simpl in H0. inversion H0. compute. reflexivity.
(* q = Project *)
crush.

Qed.

    (* P = Seq s p AND Skip*)
    destruct q;
    (* Query = SELECT *)
    destruct b;
    (* boolean = TRUE and FALSE *)
    simpl in H; inversion H; clear H; clear H2; clear H3;
    simpl in H0;
    
    compute;
    assumption.
Qed.
