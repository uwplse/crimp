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

Fixpoint runImp (p : ImpProgram) (r : relation) (result : relation) : ImpProgram * (option relation) := 
  match p with
   | Seq Skip p2 => (p2, Some result)
   | Seq p1 p2 => let (p1', oresult') := runImp p1 r result in
                      match oresult' with
                        | Some result' => runImp (Seq p1' p2) r result'  (* this seq built up *)
                        | None => (Skip, None)
                      end
   | Assign vn e => match vn with
                     | ResultName => match e with
                                       | InputRelation => (Skip, Some r)
                                       | RelationExp rexp => (Skip, Some rexp) 
                                     end
                    end
   | Skip => (Skip, Some result)
  end.



Theorem queryEquivalence : forall (q : Query) (p : ImpProgram),
                              queryToImp q = Some p ->
                                 forall (r r' : relation), runQuery q r = Some r' ->
                                                           exists p', runImp p r Rnil = (p', Some r').
  intros.
  exists Skip.
  induction p.
  unfold queryToImp in H.
  destruct q in H.
  destruct b in H.
  inversion H.
  unfol
  
  
 (* Assign case *)
  unfold queryToImp in H.
  destruct q in H.
  destruct b in H.
  discriminate H.
  
 (* skip case *)
  unfold queryToImp in H.
  destruct q in H.
  destruct b in H.
  discriminate H.
  
   
             intros.
 induction p.
 unfold runImp in 
 
 crush.

 unfold runImp.
 destruct p.
 destruct v.
 destruct e.
 reflexivity.
Qed.