Require Import Bool Arith List.
Set Implicit Arguments.

(** Relational formalism **)
(* A tuple is a list of natural numbers. *)
Definition tuple : Set :=
  list nat.

(* A relation is a list of tuples. *)
Definition relation : Set :=
  list tuple.

(* A boolean is either true or false. *)
Inductive Bool : Set :=
  | BTrue : Bool
  | BFalse : Bool.

(** Query language syntax **) 
(*
    Predicates. Currently supported values are:
    PredBool: predicate created by the input boolean. Always returns that boolean.
    PredFirst1: a predicate that returns true iff tuple[0] (first element of the tuple) evaluates to 1.
*)
Inductive Pred : Set :=
  | PredBool : Bool -> Pred
  | PredFirst1 : Pred.

(*
    Queries. Current supported values are:
    Select: Represents 
        BTrue: SELECT * FROM <input relation> WHERE 1=1
        BFalse: SELECT * FROM <input relation> WHERE 1=0
    Project: Represents
        SELECT <attribute at the input index> FROM <input relation> WHERE 1=1
    SelectIf: Represents
        SELECT * FROM <input relation> WHERE <pred>
        Note that SelectIf subsumes Select.
    JoinFirst: Represents
        SELECT * FROM <input relation1>, <input relation2> WHERE <input relation1>.<attribute1> = <input relation2>.<attribute2>
*)
Inductive Query : Set := 
  | Select : Bool -> Query
  | Project : nat -> Query
  | SelectIf : Pred -> Query
  | JoinFirst : Query. 
(** end (Query language syntax) **)

(* Returns a tuple containing the element at the given index of the input tuple. *)
Fixpoint projectTuple (t: tuple) (index: nat) : option tuple :=
  match t with
  | nil => None
  | n :: rem => match index with
                | 0 => Some (n :: nil)
                | S index' => projectTuple rem index'
                end
  end.

(* Returns the tuple at the input index of the input relation. *)
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

(* Returns a relation that is equal to the input relation filtered (selected) by the input predicate. *)
Fixpoint select (pr: Pred) (input: relation) :=
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
                                | 1 :: _ => t :: (select pr rem)
                                (* picking semantics that length 0 tuples just fail the predicate rather than fail *)
                                | _ => select pr rem
                                end
                  end                  
  end.

(* KM: Brandon, do we need this code? *)
(*
match input with
    | nil => nil
    | tup :: rem => match b with
                      | BTrue => tup :: (select rem b)
                      | BFalse => select rem b
                    end
    end.
*)

(* 
    Join equality. 
    Returns true iff the first elements of the input tuples are equal to each other.
*)
Definition joineq (t1 : tuple) (t2 : tuple) : bool :=
match t1, t2 with
  | t1first :: _, t2first :: _ => beq_nat t1first t2first
  | _, _ => false
end. 

(*
    Inner loop of the join operation.
    Returns a relation representing the join of the input tuple and the input relation.
*)
Fixpoint nljoin_inner (t : tuple) (r : relation) : relation :=
match r with
  | t' :: r' => if joineq t t' 
                then (t ++ t') :: nljoin_inner t r' 
                else nljoin_inner t r'
  | nil => nil
end.

(*
    Join implementation.
    Returns a relation representing the join of the input relations. 
*)
Fixpoint nljoin (r1 : relation) (r2 : relation) : relation :=
match r1 with
  | t1 :: r1' => (nljoin_inner t1 r2) ++ nljoin r1' r2
  | nil => nil
end.

(* Tests *)
Eval simpl in project ((1 :: nil) :: (2 :: nil) :: nil) 0.
(* Some([1, 2]) *)

(* Runs the input query on the input relations. Relation2 is used only for join operations. *)
Definition runQuery (q : Query) (inputRelation1 : relation) (inputRelation2 : relation) : option relation :=
match q with 
  | Select b => match b with 
                | BTrue => Some inputRelation1
                | BFalse => Some nil
                end
  | SelectIf pr => Some (select pr inputRelation1)
  | Project index => project inputRelation1 index
  | JoinFirst => Some (nljoin inputRelation1 inputRelation2)
end.

(* Tests *)
Eval compute in runQuery JoinFirst ((1::2::nil) :: (2::3::nil) :: nil) ((3::4::nil) :: (1::10::nil) :: (1::12::nil) :: nil).
(* Some( [1, 2, 1, 10], [1, 2, 1, 12] *)