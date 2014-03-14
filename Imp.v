Require Import Bool Arith List Query.
Set Implicit Arguments.

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
