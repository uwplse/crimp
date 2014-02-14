Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

Inductive relation : Set :=
  | Relation : relation
  | Rnil : relation.

Inductive Bool : Set :=
  | BTrue : Bool
(*  | BFalse : Bool. *).

Inductive Query : Set := 
 | Select : Bool -> Query.

Definition runQuery (q : Query) (r : relation) : option relation :=
  match q with 
   | Select b => match b with 
                  | BTrue => Some r
                (*  | BFalse => Some Rnil *)
                 end 
  end.


Inductive Exp : Set :=
  | InputRelation : Exp
  | RelationExp : relation -> Exp.

Inductive VarName : Set :=
  | ResultName : VarName.

Inductive Statement : Set :=
  | Assign : VarName -> Exp -> Statement.

Inductive ImpProgram : Set :=
  | Seq : Statement -> ImpProgram -> ImpProgram
  | Skip.

Definition queryToImp (q : Query) : option ImpProgram :=
  match q with
   | Select b => match b with
                   | BTrue => Some (Seq (Assign ResultName InputRelation) Skip) 
                  (* | BFalse => Some (Assign ResultName Rnil) *)
                 end
  end.

Fixpoint runStatement (s: Statement) (input: relation) : option relation :=
  match s with
  | Assign vn e => match vn with
                   | ResultName => match e with
                                   | InputRelation => Some input
                                   | RelationExp rexp => Some rexp 
                                   end
                   end
  end.

Fixpoint runImpSmall (p: ImpProgram) (result: option relation) (input: relation) 
    : ImpProgram  * option relation :=
  match p with
  | Seq s p' => let result' := runStatement s input
                in (p', result')
  | Skip => (Skip, None) (* Make this case an exception? *)
  end.

Definition runImp (p : ImpProgram) (input : relation) : option relation :=
  let fix helper (p : ImpProgram) (result: option relation) : option relation := 
    match p with
      | Skip => result
      | _ => let (p', result') := runImpSmall p result input
            in helper p' result'
    end
  in helper p (Some Rnil).

(* KM: I did not have a chance to look at below, it is very much chaotic. *)

(*
Lemma SkipNoop: forall (p: ImpProgram) (r r': relation), 
   runImp (Seq p Skip) r = Some r' -> runImp p r = Some r'.
   intros.
   induction p.
   
   compute in IHp1.
   crush.
admit.


Lemma SkipNoop' : forall (p: ImpProgram) (r r': relation), 
    runImp p r = Some r' -> runImp (Seq p Skip) r = Some r'.    
    intros.
    induction p.
    
    .
*)

Theorem queryEquivalence : forall (q : Query) (p : ImpProgram),
                              queryToImp q = Some p ->
                                 forall (r r' : relation), runQuery q r = Some r' ->
                                                           runImp p r = Some r'.
    intros.
    (*
    unfold queryToImp in H.
    destruct q in H.
    destruct b in H.
    inversion H.
    *)
    induction p.

    
    unfold queryToImp in H.
    destruct q in H.
    destruct b in H.
    inversion H.
    unfold runImp.
    rewrite <- H3 in IHp2. clear H3.
    rewrite <- H2 in IHp1. clear H2.
    apply H0.
    
    admit.
    
    (* program = Assign v e *)
    unfold queryToImp in H.
    destruct q in H.
    destruct b in H.
    inversion H.

    unfold queryToImp in H.
    destruct q in H.
    destruct b in H.
    inversion H.
Qed.
 unfold runImp in 
 
 crush.

 unfold runImp.
 destruct p.
 destruct v.
 destruct e.
 reflexivity.
Qed.