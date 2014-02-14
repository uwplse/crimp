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

(* It turns out that we do not (and should not) have
   runImpSmall (small step semantics). Because otherwise
   Coq cannot figure out that our function is structurally
   recursive. Special thanks go to Eric Mullen and Zach
   Tatlock.
*)
Definition runImp (p : ImpProgram) (input : relation) : option relation :=
  let fix helper (p : ImpProgram) (result: option relation) : option relation := 
    match p with
    | Skip => result
    | Seq s p' => helper p' (runStatement s input)
    end
  in helper p (Some Rnil).

Theorem queryEquivalence: 
  forall (q : Query) (p : ImpProgram),
    queryToImp q = Some p ->
      forall (r r' : relation), runQuery q r = Some r' ->
        runImp p r = Some r'.
Proof.
    intros.
    induction p.
    
    (* P = Seq s p *)
    clear IHp.

    destruct q.
    destruct b.
    simpl in H; inversion H; clear H; clear H2; clear H3.
    simpl in H0.
    
    simpl.
    assumption.
    
    (* P = Skip *)
    destruct q.
    destruct b.
    simpl in H; inversion H. 
Qed.
