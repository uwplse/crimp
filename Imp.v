Require Import Bool Arith List Query.
Set Implicit Arguments.

(**
  IMP syntax
**)

(*
    Nameholders for variables.
    Currently, there are two types:
    1. Result: a special variable to initialize/update the return value of the program.
    (Note: at this point, the result cannot be read. Only new tuples can be added to the current result)
    2. Heap variables: special indexed variables that initialize/update global data. Currently, there are 2 heap variables:
        a. 0 => Special index reserved for the tuple bound to each iteration of the outer ForAll loop (alternatively the only ForAll loop in the program, if applicable).
        b. 1 => Special index reserved for the tuple bound to each iteration of the inner ForAll loop. Only valid for programs with multiple loops (e.g., Jo)
*)
Inductive VarName : Set :=
  | ResultName : VarName
  | IndexedVarName : nat -> VarName.

(*
    Boolean expressions.
    Currenty, there are two ways to construct a boolean expression:
    1. BoolBExp: Specifying the boolean value
    2. Pred1Exp: ???
*)
(* KM: Brandon, why do we have a special BExp for booleans rather than having these under Exp? *)
Inductive BExp : Set :=
  | BoolBExp : Bool -> BExp
  | Pred1Exp : BExp. 

(*
    Expressions. Current values are:
    1. InputRelation1: First input relation to the program. This is also the relation for one-relation programs (e.g., SELECT)
    2. InputRelation2: Second input relation to the program. Only valid for programs that need a second relation (e.g., JOIN)
    3. RelationExp: Constructor to wrap the input relation to an expression.
    4. NatExp: Constructor to wrap the input natural number to an expression.
    5. BoolExp: Constructor to wrap the input boolean expression to an expression.
*)
Inductive Exp : Set :=
  | InputRelation1 : Exp
  | InputRelation2 : Exp
  | RelationExp : relation -> Exp
  | NatExp : nat -> Exp
  | BoolExp : BExp -> Exp.

(*
    Statements. Current values are:
    1. Assign: Execute the statement and assign the result to the input expression.
    2. ForAll: Iterate over the relation specified by the input expression, bind each tuple in this relation to the input variable name and execute the input statement for each of these tuples. 
        Simulates the following loop.
        for (Tuple tuple: relation.getTuples()) { 
            runStatement(statement, tuple); 
        }
    3. ProjectTuple: For each tuple of the input relation, projects the element located at the specified index (NatExp) of the input expression, wraps it into a new tuple, and appends it to the result.
        Note: The second argument (IndexedVarName) is not used at this point but is kept for extensibility.
        Previously ProjectTuple was an expression (instead of statement) where the result of this projection needed to be stored in the heap. In future, this IndexedVarName will represent this heap variable.
    4. SelectTuple: Retrieves the tuple located at the specified index (NatExp) of the input relation and appends it to the result.
        Note: The second argument (IndexedVarName) is not used at this point but is kept for extensibility.
        Previously ProjectTuple was an expression (instead of statement) where the result of this projection needed to be stored in the heap. In future, this IndexedVarName will represent this heap variable.
    5. MatchTuples: ???
*)
Inductive Statement : Set :=
  | Assign : VarName -> Exp -> Statement
  | ForAll : VarName -> Exp -> Statement -> Statement
  | ProjectTuple : Exp -> VarName -> Statement 
  | SelectTuple : Exp -> VarName -> Statement
  | MatchTuples : VarName -> VarName -> Statement.

(*
    Imperative program representation.
    We decided to differentiate Seq from other statements, so that Coq can immediately know that imperative programs nest Sequence over the second argument.
    An imperative program is basically a list (Seq) of statements that end with a special program called Skip.
*)
Inductive ImpProgram : Set :=
  | Seq : Statement -> ImpProgram -> ImpProgram
  | Skip.


(**
   end (IMP syntx
**)

Definition queryToImp (q : Query) : option ImpProgram :=
  let structure (inner : Statement) :=
     Some (Seq 
                            (Assign ResultName (RelationExp nil))
                            (Seq
                              (ForAll (IndexedVarName 0) InputRelation1 inner)
                              Skip))
 in

  match q with
  | Select b => match b with
                | BTrue => Some (Seq (Assign ResultName InputRelation1) Skip) 
                | BFalse => Some (Seq (Assign ResultName (RelationExp nil)) Skip)   
                end
  | Project index => structure (ProjectTuple (NatExp index) (IndexedVarName 0))
  | SelectIf pr => match pr with 
                       | PredBool b => structure (SelectTuple (BoolExp (BoolBExp b)) (IndexedVarName 0))
                       | PredFirst1 => structure (SelectTuple (BoolExp Pred1Exp) (IndexedVarName 0))
                    end
  | JoinFirst => structure (ForAll (IndexedVarName 1) InputRelation2
                             (MatchTuples (IndexedVarName 0) (IndexedVarName 1)))
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
(* this appears to be less straight forward to convert to non-tail calls, but I think
it is possible if we rely on monotonic query processing *)



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
(* = Some [] *)

Eval compute in let p := queryToImp (SelectIf PredFirst1) in
                        match p with 
                          | None => None
                          | Some p' => runImp' p' ((1::2::nil) :: (3::4::nil) :: (0::1::nil) :: (1::6::nil) :: nil) nil
end. 
(* = Some [(1,2),(1,6)] *)

Eval compute in let p := queryToImp JoinFirst in
  match p with
    | None => None
    | Some p' => runImp' p' ((1::2::nil) :: (2::3::nil) :: nil) ((3::4::nil) :: (1::10::nil) :: (1::12::nil) :: nil)
end.
(* = Some [(1,2,1,10), (1,2,1,12)] *)


(**
   end (Test cases)
**)
