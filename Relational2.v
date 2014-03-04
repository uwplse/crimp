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

Inductive Query : Set := 
  | Select : Bool -> Query
  | Project : nat -> Query
  | SelectIf : Bool -> Query. (* currently as expressive only as Select *) 

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

Fixpoint select (b: Bool)  (input: relation) :=
  match b with
    | BTrue => match input with
                   | nil => nil
                   | tup :: rem => tup :: (select b rem)
               end
    | BFalse => match input with
                  | nil => nil
                  | _ :: rem => select b rem
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
  | SelectIf b => Some (select b inputRelation)
  | Project index => project inputRelation index
  end.

Inductive VarName : Set :=
  | ResultName : VarName
  | IndexedVarName : nat -> VarName.

Inductive Exp : Set :=
  | InputRelation : Exp
  | RelationExp : relation -> Exp
(*  | TupleExp : tuple -> Exp *)
  | NatExp : nat -> Exp
  | BoolExp : Bool -> Exp.

(* It turns out that Forall is already defined in Coq, so I used ForAll *)
Inductive Statement : Set :=
  | Assign : VarName -> Exp -> Statement
  | ForAll : VarName -> Statement -> Statement
  | ProjectTuple : Exp -> VarName -> Statement
  | SelectTuple : Exp -> VarName -> Statement.

Inductive ImpProgram : Set :=
  | Seq : Statement -> ImpProgram -> ImpProgram
  | Skip.

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
  | SelectIf b => Some 
                     (Seq 
                      (Assign ResultName (RelationExp nil))
                      (Seq
                        (ForAll (IndexedVarName 0)
                          (SelectTuple (BoolExp b) (IndexedVarName 0)))
                        Skip))
                        
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
  | SelectTuple (BoolExp b) (IndexedVarName vnIndex) =>
      match b with
         | BTrue => Some (heap :: nil)
         | BFalse => Some nil
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


Eval compute in let p := queryToImp (Project 1) in
                        match p with 
                          | None => None
                          | Some p' => runImp p' ((TCons 1 (TCons 2 TNil)) :: (TCons 3 (TCons 4 TNil)) :: nil)
end.


(* this appears to be less straight forward to convert to non-tail calls, but I think
it is possible if we rely on monotonic query processing *)

Ltac inv H := inversion H; subst; clear H.
Theorem queryEquivalence'': 
  forall (q : Query) (p : ImpProgram),
    queryToImp q = Some p ->
      forall (r r' : relation), runQuery q r = Some r' ->
        runImp' p r = Some r'. Print Ltac break_match.
  
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
intros; destruct b; crush; f_equal; crush.

intros p Hc; inv Hc.
induction r. crush. 

  intros.

unfold runImp'.

break_match; try discriminate.
break_match. (* discriminate not work on 2nd subgoal *) 
break_match; try discriminate.
f_equal.
inv Heqo0.

unfold runQuery in H.
unfold project in H.
break_match; try discriminate.
break_match; try discriminate. 
inv H.
fold project in Heqo2.
fold (runQuery (Project n) r) in Heqo2.

apply IHr in Heqo2.       (* apply is smart, no need to specialize IHr's r'*)
unfold runImp' in Heqo2.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
inv Heqo4. inv Heqo2.

(* imp side *)
unfold runStatement in Heqo1.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
crush.

break_match; try discriminate.
clear Heqo0.
unfold runStatement in Heqo1.
break_match.  (* discriminate not work on 2nd subgoal *)
break_match; try discriminate.
break_match; try discriminate.
inv Heqo0. clear Heqo1. 
unfold runStatement in Heqo.
inv Heqo.
unfold runQuery in H.
unfold project in H.
break_match; try discriminate.
break_match; try discriminate.
inv Heqo3.
fold project in Heqo0.
unfold runQuery in IHr. (* here we unify by unfolding instead of folding Heqo0 which is neater *)
apply IHr in Heqo0.
unfold runImp' in Heqo0.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
crush.

break_match; try discriminate.
clear Heqo0 Heqo1.
unfold runQuery in H.
unfold project in H.
break_match; discriminate.


(* SelectIf case *)
intros p Hc; inv Hc.
induction r.  
destruct b; trivial.

intros.
unfold runImp'.
break_match; try discriminate.
break_match.
break_match; try discriminate.
inv Heqo0.
f_equal.

unfold runStatement in Heqo1.
break_match.
break_match; try discriminate.
inv Heqo1. 
unfold runStatement in Heqo.
inv Heqo.
break_match; try discriminate.
inv Heqo0.
simpl.

unfold runQuery in IHr.
unfold runQuery in H.

(* This trick lets us get rid of the 'a' appended to Select BTrue r 
   so that we can use it in the induction hypothesis.
   Special thanks go to Colin. *)
simpl in H. destruct r'; inversion H. clear H. subst a. rewrite H2.
(* Adding 'some' back so that we can unify with the induction hypothesis. *)
assert (Some (select BTrue r) = Some r'). crush. clear H2. apply IHr in H. clear IHr. 

f_equal. unfold runImp' in H.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
crush.
(* This is what the above crush actually does!
inv Heqo0. inv H.
unfold runStatement in Heqo. inv Heqo. simpl. f_equal.
unfold runStatement in Heqo1. rewrite Heqo1 in Heqo2. clear Heqo1. inv Heqo2. trivial.
*)


simpl. clear Heqb0. inv Heqo0. simpl.
unfold runQuery in H. simpl in H. inversion H. clear H.
unfold runQuery in IHr.
assert (Some (select BFalse r) = Some r'). crush. rewrite H1. clear H1.
apply IHr in H. clear IHr.
unfold runImp' in H.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
crush.
(* This is what the above crush actually does
inv Heqo0. inv H.
unfold runStatement in Heqo. inv Heqo.
unfold runStatement in Heqo1. rewrite Heqo1 in Heqo2. clear Heqo1. inv Heqo2. simpl. reflexivity.
*)

discriminate.

break_match; try discriminate.
clear Heqo0.
unfold runStatement in Heqo. inv Heqo.

destruct b.
unfold runStatement in Heqo1.
break_match; try discriminate.
clear Heqo1.
unfold runQuery in H. simpl in H. inversion H. clear H. 
destruct r'. crush. 
inversion H1. subst a. rewrite H1. clear H1.
unfold runQuery in IHr.
assert (Some (select BTrue r) = Some r'). crush. clear H2.

apply IHr in H. clear IHr. unfold runImp' in H.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
crush.
(* This is what the above crush does! 
inv Heqo1. inv H.
unfold runStatement in Heqo0. inv Heqo0.
unfold runStatement in Heqo2. rewrite Heqo in Heqo2. clear Heqo. inv Heqo2.
*)

unfold runStatement in Heqo1.
break_match; try discriminate.
clear Heqo1.
unfold runQuery in H. simpl in H. inversion H. clear H.
unfold runQuery in IHr.
assert (Some (select BFalse r) = Some r'). crush.  
rewrite H1. clear H1.
apply IHr in H. clear IHr.
unfold runImp' in H.
break_match; try discriminate.
break_match; try discriminate.
break_match; try discriminate.
crush.
(* This is what the above crush does!
inv Heqo1. inv H.
unfold runStatement in Heqo0. inv Heqo0.
unfold runStatement in Heqo2. rewrite Heqo in Heqo2. clear Heqo. inv Heqo2.
*)
Qed.
(* wish list:
- unify ProjectTuple and SelectTuple by bringing back AppendTuple
- Ltac for unfolding and break matching
- Ltac for break_match; try discr and/or repeat
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
