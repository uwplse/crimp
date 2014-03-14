(*
    NOTES: 
    - ultimately we want to denote an Imp program from
    the RA. For select it seems like this will allow us
    to write proofs that the impExecute(impDenote ra) = raExecute ra. impDenote will be like the datalogcompiler code

    First we would like to skip the pseudo-denotation process
    and just write a single operator alone: that selectRA = selectImp. This means
    our select Imp will have an apply-pred operation. Then to
    support other query plans we will add denotation.
        *)
    
(*
    choices: untyped and write proofs as execute produces something
    vs if typed then proceeds*)

Load Relational.
(* If Relational.vo exists, then can Require Import Relational. *)

Module Imp.

(* Initial typed start

(* operators that go from type*type -> BExp *)
Inductive binop : Set :=
    | Eq.

Inductive IIBinop : Set :=
    | Plus.

Inductive IValue : Set :=
 | Int : nat -> IValue.   (* sticking to nats *)

Inductive IExp : Set :=
 | IExpValue : IValue -> IExp.

Inductive bbinop : Set :=
  | And
  | Or.

Inductive BValue : Set :=
 | Bool : bool -> Value.

Inductive BExp : Set :=
 | BExpValue : BValue -> BExp
 | BBinop : bbinop -> BExp -> BExp -> BExp
 | IBinop : ibinop -> IExp -> IExp -> BExp.

*)

Inductive Val : Set :=
    | Int : nat -> Val
    | Bool : bool -> Val.

Inductive Tuple : Set :=
    | Tnil : Tuple
    | Tcons : Val -> Tuple -> Tuple.

Inductive Relation : Set :=
    | Rnil : Relation
    | Rcons : Tuple -> Relation -> Relation.

Inductive Exp : Set :=
    | ValExp : Val -> Exp
    | TupleExp : Tuple -> Exp
    | Append : Exp -> Exp -> Exp  (* Exp are Tuple, Relation *)
    | Var : nat -> Exp
    | RelationExp : Relation -> Exp
    | ApplyPred : Pred -> Exp -> Exp.

Inductive VarName : Set :=
    | VarLHS : nat -> VarName.

Inductive Statement : Set :=
    | Seq : Statement -> Statement -> Statement
    | Forall : VarName -> Relation -> Statement -> Statement
    | If : Exp -> Statement -> Statement -> Statement
    | Assign : VarName -> Exp -> Statement
    | Skip : Statement.

(* Pred: t -> bool *)




(* Fill in exactly Relational.Pred.
It is not technically in the Imp language, but we will pretend 
until we have denotation *)

(* t = var 1
   ans = var 0 *)
Definition ImpSelect (pred : Pred) (rel : Relation) : Statement :=
    Seq (Assign (VarLHS 0) (RelationExp Rnil)) (Forall (VarLHS 1) rel (If (ApplyPred pred (Var 1)) (Assign (VarLHS 0) (Append (Var 1) (Var 0))) Skip )).

Eval compute in ImpSelect (BConst true) (Rcons (Tcons (Int 1) Tnil) Rnil).

(* TODO: semantics for execute, then theorem *)


Inductive heap : Set :=
  | hnil : heap
  | hcons : nat (*key*) -> nat (*value*) -> heap -> heap.

Fixpoint impExecuteStep (h : heap) (s : Statement) : heap * Statement :=
  match s with
    | Seq s1 s2 => match s1 with 
                     | Skip => (h, s2)
                     | _ => let (h', s1') := impExecuteStep h s1 in
                       (h', (Seq s1' s2))
                   end
    | If e s1 s2 => let c := impEvalExp h e in
                       if c then (h, s1) else (h, s2)
    | Assign vn e => let c := impEvalExp h e in
                       (insert h vn c, Skip)
    | Forall vn r s' => match r with
                            | Rnil => (h, Skip)
                            | Rcons t rem => let h' := (replaceH h vn t) in
                              (h', Seq s' (Forall vn rem s'))  
                        end
    end.



(* steps 

choose simplest query
define Query
define semantics separately

define IMP-
define semantics separately

prove equivalance of semantics(RA)=semantics(IMP query)

update compile


queries:
true
false
project
select(t.0) where tuple vals are boolean
...
*)
