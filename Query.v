Require Import Bool Arith List.
Set Implicit Arguments.

Definition tuple : Set :=
  list nat.

Definition relation : Set :=
  list tuple.

Inductive Bool : Set :=
  | BTrue : Bool
  | BFalse : Bool.

(**
  Query language syntax
**) 
Inductive Pred : Set :=
  | PredBool : Bool -> Pred
  | PredFirst1 : Pred.  (* represents true if tuple[0]=1 *)


Inductive Query : Set :=
  | FromInput : Query
  | Project : nat -> Query -> Query
  | SelectIf : Pred -> Query -> Query(* overlaps with Select *)
  | JoinFirst : Query -> Query -> Query.
(**
  end (Query language syntax)
**)


Fixpoint projectTuple (t: tuple) (index: nat) : option tuple :=
  match t with
  | nil => None
  | n :: rem => match index with
                   | 0 => Some (n :: nil)
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

Fixpoint select (pr: Pred)  (input: relation) :=
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
(*
match input with
    | nil => nil
    | tup :: rem => match b with
                      | BTrue => tup :: (select rem b)
                      | BFalse => select rem b
                    end
    end.
*)


Definition joineq (t1 : tuple) (t2 : tuple) : bool :=
  match t1, t2 with
    | t1first :: _, t2first :: _ => beq_nat t1first t2first
    | _, _ => false
  end. 

Fixpoint nljoin_inner (t : tuple) (r : relation) : relation :=
match r with
      | t' :: r' => if joineq t t' then (t ++ t') :: nljoin_inner t r' else nljoin_inner t r'
      | nil => nil
    end.

Fixpoint nljoin (r1 : relation) (r2 : relation) : relation :=
  match r1 with
    | t1 :: r1' => (nljoin_inner t1 r2) ++ nljoin r1' r2
    | nil => nil
  end.


Eval simpl in project ((1 :: nil) :: (2 :: nil) :: nil) 0.

Fixpoint runQuery (q : Query) (inputRelation1 : relation) : option relation :=
  match q with 
  | FromInput => Some inputRelation1
  | SelectIf pr q' => match runQuery q' inputRelation1 with
                        | Some inp' => Some (select pr inp')
                        | None => None
                      end
  | Project index q' => match runQuery q' inputRelation1 with
                          | Some inp' => project inp' index
                          | None => None
                        end
  | JoinFirst q1' q2' => match runQuery q1' inputRelation1, runQuery q2' inputRelation1 with 
                           | Some inp1', Some inp2' => Some (nljoin inp1' inp2')
                           | _, _ => None
                         end
  end.

Eval compute in runQuery (Project 1 FromInput) ((1::nil) :: nil).

Eval compute in runQuery (JoinFirst FromInput FromInput) ((1::2::nil) :: (2::3::nil) :: nil).

Eval compute in runQuery (Project 1 (SelectIf PredFirst1 FromInput)) ((1::2::nil) :: (2::3::nil) :: nil). 
