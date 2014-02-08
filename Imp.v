(*
    NOTES: 
    - ultimately we want to denote an Imp program from
    the RA. For select it seems like this will allow us
    to write proofs that the impExecute(impDenote ra) = raExecute ra. impDenote will be like the datalogcompiler code

    First we would like to skip the denotation process
    and just write a single operator alone: that selectRA = selectImp. This means
    our select Imp will have an apply-pred operation. Then to
    support other query plans we will add denotation.
        *)
    
(*
    choices: untyped and write proofs as execute produces something
    vs if typed then proceeds*)

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
    | Bool : bool -> bool.

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

Inductive Statement : Set :=
    | Seq : Statement -> Statement -> Statement
    | Forall : VarName -> Relation -> Statement -> Statement
    | If : Exp -> Statement -> Statement
    | Assign : VarName -> Exp -> Statement.

(* Pred: t -> bool *)

Inductive VarName : Set :=
    | VarLHS : nat -> VarName.


(* Fill in exactly Relational.Pred.
It is not technically in the Imp language, but we will pretend 
until we have denotation *)

(* t = var 1
   ans = var 0 *)
Definition ImpSelect (pred : Pred) (rel : Relation) : Set :=
    Seq (Assign (VarLHS 0) (RelationExp Rnil)) (Forall (VarLHS 1) rel (If (ApplyPred pred (Var 1)) (Assign (Var 0) (Append (Var 1) (Var 0))))).

(* TODO: semantics for execute, then theorem *)

