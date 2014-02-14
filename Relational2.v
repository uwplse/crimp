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

Inductive ImpProgram : Set :=
  | Seq : ImpProgram -> ImpProgram -> ImpProgram
  | Assign : VarName -> Exp -> ImpProgram
  | Skip : ImpProgram.

Definition queryToImp (q : Query) : option ImpProgram :=
  match q with
   | Select b => match b with
                   | BTrue => Some (Seq (Assign ResultName InputRelation) Skip) 
                  (* | BFalse => Some (Assign ResultName Rnil) *)
                 end
  end.

Definition runImp (p : ImpProgram) (r : relation) : option relation :=
 let fix helper (p : ImpProgram) (result : relation) : ImpProgram * relation := 
  match p with
   | Seq p1 p2 => match p1 with
                    | Skip => (p2, result) 
                    | _ => let (p1', result') := helper p1 result in
                      (Seq p1' p2, result')
                  end
   | Assign vn e => match vn with
                     | ResultName => match e with
                                       | InputRelation => (Skip, r)
                                       | RelationExp rexp => (Skip, rexp) 
                                     end
                    end
   | Skip => (Skip, result)
  end
  in 
  let (_, result ) := helper p Rnil in
    Some result.



Theorem queryEquivalence : forall (q : Query) (p : ImpProgram),
                              queryToImp q = Some p ->
                                 forall (r r' : relation), runQuery q r = Some r' ->
                                                           runImp p r = Some r'.                intros.
 induction p.
 unfold runImp in 
 
 crush.

 unfold runImp.
 destruct p.
 destruct v.
 destruct e.
 reflexivity.
Qed.