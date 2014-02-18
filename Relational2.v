Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

Inductive tuple : Set :=
  | TCons : nat -> tuple -> tuple
  | TNil : tuple.

Inductive relation : Set :=
  | RCons : tuple -> relation -> relation
  | RNil : relation.

Inductive Bool : Set :=
  | BTrue : Bool
  | BFalse : Bool.

Inductive Query : Set := 
  | Select : Bool -> Query
  | Project : nat -> Query. 

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
      | RNil => Some RNil
      | RCons tup rem => match (projectTuple tup index) with
                            | None => None
                            | Some tup' => let remres := project rem index in
                               match remres with 
                                 | None => None
                                 | Some remres' => Some (RCons tup' remres')       
                               end
                         end
      end.

Eval simpl in project (RCons (TCons 1 TNil) (RCons (TCons 2 TNil) RNil)) 0.

Definition runQuery (q : Query) (inputRelation : relation) : option relation :=
  match q with 
  | Select b => match b with 
                | BTrue => Some inputRelation
                | BFalse => Some RNil
                end 
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
  | ProjectTuple : Exp -> VarName -> Exp.

(* It turns out that Forall is already defined in Coq, so I used ForAll *)
Inductive Statement : Set :=
  | Assign : VarName -> Exp -> Statement
  | AppendTuple: VarName -> Exp -> Statement
  | ForAll : VarName -> Exp -> Statement -> Statement.

Inductive ImpProgram : Set :=
  | Seq : Statement -> ImpProgram -> ImpProgram
  | Skip.

Definition queryToImp (q : Query) : option ImpProgram :=
  match q with
  | Select b => match b with
                | BTrue => Some (Seq (Assign ResultName InputRelation) Skip) 
                | BFalse => Some (Seq (Assign ResultName (RelationExp RNil)) Skip)   
                end
  | Project index => Some 
                     (Seq 
                      (Assign ResultName (RelationExp RNil))
                      (Seq
                        (ForAll (IndexedVarName 0) InputRelation
                          (AppendTuple ResultName (ProjectTuple (NatExp index) (IndexedVarName 0))))
                        Skip))
                        
  end.

Fixpoint tupleHeapLookup (heap: relation) (index: nat) : option tuple :=
  match heap with
  | RNil => None
  | RCons t rem => match index with
                   | 0 => Some t
                   | S index' => tupleHeapLookup rem index'
                   end
  end.

Fixpoint updateTupleHeap (heap: relation) (index: nat) (t: tuple) : relation :=
  match heap with
  | RNil => match index with
            | 0 => RCons t RNil
            | S index' => RCons (TCons 0 TNil) (updateTupleHeap heap index' t)
            end
  | RCons tup rem => match index with
                     | 0 => RCons t rem
                     | S index' => RCons tup (updateTupleHeap rem index' t)
                     end
  end.

Fixpoint runStatement (s: Statement) (input: relation) (heap: relation) (result: relation) : option relation :=
  match s with
  | Assign ResultName e => match e with
                           | InputRelation => Some input
                           | RelationExp rexp => Some rexp 
                           | _ => None
                           end
  | Assign _ _ => None
  | AppendTuple ResultName e => 
      match e with
      | ProjectTuple (NatExp index) (IndexedVarName vnIndex) =>
          match tupleHeapLookup heap vnIndex with
          | Some tuple' => 
              match projectTuple tuple' index with
              | Some t' => Some (RCons t' result)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | AppendTuple _ _ => None
  | ForAll (IndexedVarName index) InputRelation  s' =>
      let fix helper (rel: relation) (res: option relation) :=
        match res with
        | None => None
        | Some res' => match rel with
                      | RNil => res
                      | RCons t rem => helper rem (runStatement s' input (updateTupleHeap heap index t) res')
                      end
        end
      in helper input (Some result)
  | ForAll _ _ _ => None
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
    | Seq s p' => helper p' (runStatement s input RNil RNil)
    end
  in helper p (Some RNil).

Theorem queryEquivalence: 
  forall (q : Query) (p : ImpProgram),
    queryToImp q = Some p ->
      forall (r r' : relation), runQuery q r = Some r' ->
        runImp p r = Some r'.
Proof.
    intros.
    induction p.
    destruct q.
    
    (* Select TRUE and Select FALSE *)
    destruct b;
    simpl in H; inversion H; clear H; clear H2; clear H3;
    simpl in H0;
    
    compute;
    assumption.
    
    (* Project <index> *)
    simpl in H0. inversion H0.

    simpl in H0. inversion H0. compute in H2. simpl in H2.
    
    simpl in H. inversion H. clear H. simpl in H0. inversion H0. clear H0. simpl H1.


    induction p;
    
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
