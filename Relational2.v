Require Import Bool Arith List CpdtTactics CorgiTactics.
Set Implicit Arguments.

Inductive tuple : Set :=
  | TCons : nat -> tuple -> tuple
  | TNil : tuple.


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
  | SelectIf : Pred -> Query. (* overlaps with Select *)
(**
  end (Query language syntax)
**)


Fixpoint projectTuple (t: tuple) (index: nat) : option tuple :=
  match t with
  | TNil => None
  | TCons n rem => match index with
                   | 0 => Some (TCons n TNil)
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
                                      | TCons 1 _ => t :: (select pr rem)
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

Eval simpl in project ((TCons 1 TNil) :: (TCons 2 TNil) :: nil) 0.

Definition runQuery (q : Query) (inputRelation : relation) : option relation :=
  match q with 
  | Select b => match b with 
                | BTrue => Some inputRelation
                | BFalse => Some nil
                end
  | SelectIf pr => Some (select pr inputRelation)
  | Project index => project inputRelation index
  end.

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
  | InputRelation : Exp
  | RelationExp : relation -> Exp
(*  | TupleExp : tuple -> Exp *)
  | NatExp : nat -> Exp
  | BoolExp : BExp -> Exp.

(* It turns out that Forall is already defined in Coq, so I used ForAll *)
Inductive Statement : Set :=
  | Assign : VarName -> Exp -> Statement
  | ForAll : VarName -> Statement -> Statement
  | ProjectTuple : Exp -> VarName -> Statement
  | SelectTuple : Exp -> VarName -> Statement.

Inductive ImpProgram : Set :=
  | Seq : Statement -> ImpProgram -> ImpProgram
  | Skip.

(**
   end (IMP syntx
**)

Definition queryToImp (q : Query) : option ImpProgram :=
  match q with
  | Select b => match b with
                | BTrue => Some (Seq (Assign ResultName InputRelation) Skip) 
                | BFalse => Some (Seq (Assign ResultName (RelationExp nil)) Skip)   
                end
  | Project index => Some 
                     (Seq 
                      (Assign ResultName (RelationExp nil))
                      (Seq
                        (ForAll (IndexedVarName 0)
                          (ProjectTuple (NatExp index) (IndexedVarName 0)))
                        Skip))
  | SelectIf pr => match pr with
                     | PredBool b =>  
                       Some 
                     (Seq 
                      (Assign ResultName (RelationExp nil))
                      (Seq
                        (ForAll (IndexedVarName 0)
                          (SelectTuple (BoolExp (BoolBExp b)) (IndexedVarName 0)))
                        Skip))
                     | PredFirst1 =>
                       Some 
                     (Seq 
                      (Assign ResultName (RelationExp nil))
                      (Seq
                        (ForAll (IndexedVarName 0)
                          (SelectTuple (BoolExp Pred1Exp) (IndexedVarName 0)))
                        Skip))
                    end

                        
  end.

(* heap is a tuple *)
Fixpoint runStatement (s: Statement) (input: relation) (heap: tuple) : option relation :=
  match s with
  | Assign ResultName e => match e with
                           | InputRelation => Some input
                           | RelationExp rexp => Some rexp 
                           | _ => None
                           end
  | Assign _ _ => None
  | ProjectTuple (NatExp index) (IndexedVarName vnIndex) =>
          match projectTuple heap index with
          | Some tup => Some (tup :: nil)
          | None => None
          end
  | ProjectTuple _ _ => None
  | SelectTuple (BoolExp bexp) (IndexedVarName vnIndex) =>
      match bexp with
        | BoolBExp b => match b with
                          | BTrue => Some (heap :: nil)
                          | BFalse => Some nil
                        end
        | Pred1Exp => match heap with
                        | TCons 1 _ => Some (heap :: nil)
                        | _ => Some nil
                      end
      end
  | SelectTuple _ _ => None
  | ForAll (IndexedVarName index)  s' =>
      let fix helper (rel: relation) :=
        match rel with
        | nil => Some nil
        | t :: rem => 
          match (runStatement s' input t) with
          | None => None
          | Some res => match (helper rem) with
                        | Some rem' => Some (res ++ rem')
                        | None => None
                        end
          end
        end
      in helper input
  | ForAll _ _ => None
  end.



(* It turns out that we do not (and should not) have
   runImpSmall (small step semantics). Because otherwise
   Coq cannot figure out that our function is structurally
   recursive. Special thanks go to Eric Mullen and Zach
   Tatlock.
*)
Definition runImp (p : ImpProgram) (input : relation) : option relation :=
  let fix helper (p : ImpProgram) (result: relation) : option relation := 
    match p with
    | Skip => Some result
    | Seq s p' => match (runStatement s input TNil) with
                    | Some res => helper p' (result ++ res)
                    | None => None
                  end
    end
  in helper p nil.

Fixpoint runImp' (p: ImpProgram) (input: relation) : option relation :=
  match p with
    | Skip => Some nil
    | Seq s p' => match (runStatement s input TNil) with
                    | Some res => match runImp' p' input with
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
                          | Some p' => runImp p' ((TCons 1 (TCons 2 TNil)) :: (TCons 3 (TCons 4 TNil)) :: nil)
end.
(* = Some [(1),(3)] *)

Eval compute in let p := queryToImp (Project 2) in
                        match p with 
                          | None => None
                          | Some p' => runImp p' ((TCons 1 (TCons 2 TNil)) :: (TCons 3 (TCons 4 TNil)) :: nil)
end.
(* = None *)

Eval compute in let p := queryToImp (Project 1) in
                        match p with 
                          | None => None
                          | Some p' => runImp p' ((TCons 1 (TCons 2 TNil)) :: (TCons 3 (TCons 4 TNil)) :: nil)
end.
(* = Some [(2),(4)] *)

Eval compute in let p := queryToImp (SelectIf (PredBool BTrue)) in
                          match p with
                            | None => None
                            | Some p' => runImp p' ((TCons 1 (TCons 2 TNil)) :: (TCons 3 (TCons 4 TNil)) :: nil)
end.
(* = Some [(1,2),(3,4)] *)

Eval compute in let p := queryToImp (SelectIf (PredBool BFalse)) in
                          match p with
                            | None => None
                            | Some p' => runImp p' ((TCons 1 (TCons 2 TNil)) :: (TCons 3 (TCons 4 TNil)) :: nil)
end.

Eval compute in let p := queryToImp (SelectIf PredFirst1) in
                        match p with 
                          | None => None
                          | Some p' => runImp p' ((TCons 1 (TCons 2 TNil)) :: (TCons 3 (TCons 4 TNil)) :: (TCons 0 (TCons 1 TNil)) :: (TCons 1 (TCons 6 TNil)) :: nil)
end. 
(* = Some [(1,2),(1,6)] *)

(**
   end (Test cases)
**)

(* this appears to be less straight forward to convert to non-tail calls, but I think
it is possible if we rely on monotonic query processing *)

Ltac inv H := inversion H; subst; clear H.
Ltac unfold_all := repeat match goal with 
                  | [ |- runImp' _ _ = _ ] => unfold runImp'; [repeat break_match; try discriminate]
                  | [H: runImp' _ _ = _ |- _ ] => unfold runImp' in H; [repeat break_match; try discriminate]
                  | [H: runQuery _ _ = _ |- _ ] => unfold runQuery in H; [repeat break_match; try discriminate]
                  | H: project _ _ = _ |- _ => unfold project in H                 
                  | [H: runStatement _ _ _ = _ |- _ ] => unfold runStatement in H; [repeat break_match; try discriminate]
                end.
Ltac inv_somes := repeat match goal with
                           | [ H: Some _ = Some _ |- _ ] => inv H
                         end.

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

Theorem queryEquivalence'': 
  forall (q : Query) (p : ImpProgram),
    queryToImp q = Some p ->
      forall (r r' : relation), runQuery q r = Some r' ->
        runImp' p r = Some r'. 
  
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
induction r. crush. 

  intros.

unfold_all.
f_equal.
fold project in Heqo5.
fold (runQuery (Project n) r) in Heqo5.
apply IHr in Heqo5. clear IHr.       (* apply is smart, no need to specialize IHr's r'*)
unfold_all.
rewrite Heqo8 in Heqo3. clear Heqo8.
inv_somes.
trivial.

fold project in Heqo5.
fold (runQuery (Project n) r) in Heqo5.
apply IHr in Heqo5. clear IHr.
unfold_all.
inv_somes.
crush.


(* SelectIf case *)
intros p0 Hc; inv Hc.
destruct p.
induction r; destruct b. crush. crush.

inv H0.
intros.

unfold runQuery in H. simpl in H. inversion H. clear H.
destruct r'. crush. inversion H1. subst a. clear H2.
unfold runQuery in IHr.
assert (Some (select (PredBool BTrue) r) = Some r'). crush.
apply IHr in H. clear IHr.

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
unfold runQuery in IHr.
unfold select in H. fold select in H. (* gets rid of "a" *)
apply IHr in H. clear IHr.
unfold_all.
rewrite Heqo5 in Heqo2.
inv_somes.
simpl. reflexivity.

unfold select in H. fold select in H. (* gets rid of "a" *)
apply IHr in H. clear IHr.
unfold_all.
rewrite Heqo5 in Heqo2.
inv_somes.
discriminate.


(* SelectIf PredFirst1 *)
induction r. crush.

intros.
inversion H0. clear H0.
unfold runQuery in H.
unfold select in H.
break_match.
break_match.
unfold runQuery in IHr.
unfold select in IHr.
apply IHr in H. clear IHr.
inversion H2 in H. clear H2 H0.
unfold_all.
rewrite Heqo4 in Heqo5. clear Heqo4.
crush. 

rewrite Heqo4 in Heqo5. clear Heqo4.
discriminate.

break_match; try discriminate.
unfold_all.
unfold runQuery in IHr.
unfold select in IHr.
destruct r'.
crush.

apply some_list_eq in H.
destruct H. fold select in H. fold select in IHr.
apply some_eq in H.
apply IHr in H. clear IHr.
inv H2. clear H1.
unfold_all.
rewrite Heqo2 in Heqo5. clear Heqo2.
inv_somes. trivial.

destruct r'. discriminate.
fold select in H.
apply some_list_eq in H.
destruct H.
unfold runQuery in IHr.
apply some_eq in H.
apply IHr in H. clear IHr.
inv H2. clear H1.
unfold_all.
rewrite Heqo2 in Heqo5. clear Heqo2.
discriminate.

fold select in H.
unfold runQuery in IHr.
apply IHr in H. clear IHr.
inv H2. clear H0.
unfold_all.
rewrite Heqo4 in Heqo5. clear Heqo4.
inv_somes. trivial.

rewrite Heqo4 in Heqo5. clear Heqo4.
discriminate.

fold select in H.
unfold runQuery in IHr.
inv H2. clear H0.
apply IHr in H. clear IHr.  (* applying IHr probably crushable if we first unfold_all inside IHr *)
unfold_all.
rewrite Heqo4 in Heqo5. clear Heqo4.
inv_somes.
trivial.

rewrite Heqo4 in Heqo5. clear Heqo4.
inv_somes.
discriminate.
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
