Inductive relation : Set :=
  | Relation : relation.

Inductive Query : Set := 
 | Select : Query.

Definition runQuery (q : Query) (r : relation) : Option relation :=
  match q with 
   | Select => Some r
  end.


Inductive Exp : Set :=
  | InputRelation : Exp.

Inductive VarName : Set :=
  | ResultName : VarName.

Inductive ImpProgram : Set :=
  | Assign : VarName -> Exp -> ImpProgram.

Definition queryToImp (q : Query) : Option ImpProgram :=
  match q with
   | Select => Some (Assign ResultName InputRelation)
  end.

Definition runImp (p : ImpProgram) (r : relation) : Option relation :=
  match p with
   | Assign vn e => match vn with
                     | ResultName => match e with
                                       | InputRelation => Some r
                                     end
                    end
  end.


Theorem queryEquivalence : forall (q : Query) (p : ImpProgram),
                              queryToImp q = Some p ->
                                 forall (r r' : relation), runQuery q r = Some r' ->
                                                           runImp p r = Some r'.                       
