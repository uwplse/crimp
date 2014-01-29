Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

Print list.
(*Inductive tuplen (n : nat) : Set :=
 | nil : tuplen n
 | cons : nat -> tuplen (n-1) -> tuplen n.
*)

Inductive tuplen (T: Set) : nat -> Set :=
| tnnil : tuplen T 0
| tncons : T -> forall l, tuplen T l -> tuplen T (S l).

Definition relation_n (T: Set) (r n: nat) : Set :=
  tuplen (tuplen T r) n.

Definition relation (T: Set) (r: nat) : Set :=
  list (tuplen T r).

Print sig.

Definition length_refined_lists (T: Set) (l: list T) (n: nat) : Set :=
  { l | @length T l = n }.

Inductive nattuplen : nat -> Set :=
| ntnnil : nattuplen 0
| ntncons : nat -> forall l, nattuplen l -> nattuplen (S l).

(* TODO length as part of tuple type *)
Inductive tuple : Set :=
  | tnil : tuple
  | tcons : nat -> tuple -> tuple.

Eval simpl in tcons 1 tnil.

Inductive Relation : Set :=
| rnil : Relation
| rcons : tuple -> Relation -> Relation.


Eval simpl in rcons (tcons 1 tnil) rnil.
Eval simpl in rcons (tcons 1 tnil) (rcons (tcons 2 tnil) rnil).

Print bool.


Inductive AttrRef : Set :=
 | Unnamed : nat -> AttrRef.


Inductive NExp : Set :=
 | NConst : nat -> NExp
 | AConst : AttrRef -> NExp.

Inductive nbinop : Set :=
 | Eq.

Inductive bbinop : Set :=
  | And
  | Or.

Inductive Pred : Set :=
  | BConst : bool -> Pred
  | NBinop : nbinop -> NExp -> NExp -> Pred
  | BBinop : bbinop -> Pred -> Pred -> Pred.

Eval simpl in BConst true.
Eval simpl in BConst false.
Eval simpl in BBinop And (BConst true) (BConst true).
Eval simpl in BBinop Or (NBinop Eq (AConst (Unnamed 0)) (NConst 3)) (NBinop Eq (NConst 2) (AConst (Unnamed 4))).


Fixpoint attrLookupHelper (t : tuple) (pos : nat) : option nat :=
 match t with
   | tnil => None
   | tcons attr rem => if (beq_nat pos 0) then (Some attr) else attrLookupHelper rem (pos-1)
end.

Definition attrLookup (t : tuple) (a : AttrRef) : option nat :=
 match a with
     | Unnamed pos => attrLookupHelper t pos
end.

Eval simpl in attrLookup (tcons 10 (tcons 20 tnil)) (Unnamed 1).
Eval simpl in attrLookup tnil (Unnamed 0).
Eval simpl in attrLookup (tcons 10 (tcons 20 (tcons 30 tnil))) (Unnamed 3).

Definition evalNExp (e : NExp) (t : tuple) : option nat :=
  match e with
  | NConst n => Some n
  | AConst aref => attrLookup t aref
end. 

(* check it out : http://compcert.inria.fr/doc/html/Compiler.html *)

Fixpoint evalPred (p : Pred) (t : tuple) : option bool :=
  match p with
   | BConst b => Some b
   | NBinop op e1 e2 => let r1 := evalNExp e1 t in 
                        match r1 with
                          | None => None
                          | Some n1 => 
                            let r2 := evalNExp e2 t in
                            match r2 with
                             | None => None
                             | Some n2 => 
                              match op with
                                 | Eq => Some (beq_nat n1 n2)
                              end
                           end
                        end
  | BBinop op p1 p2 => let r1 := evalPred p1 t in
                       match r1 with
                         | None => None
                         | Some b1 => 
                            let r2 := evalPred p2 t in
                            match r2 with
                              | None => None
                              | Some b2 =>
                                 match op with
                                   | And => Some (andb b1 b2) 
                                   | Or => Some (orb b1 b2)
                                 end
                            end
                     end
   end.

Eval simpl in evalPred (NBinop Eq (NConst 3) (AConst (Unnamed 1))) (tcons 3 (tcons 3 tnil)).

Fixpoint selectHelper (src : Relation) (p : Pred) (res : Relation) : option Relation :=
  match src with
    | rnil => Some res
    | rcons t rem => let pres := evalPred p t in
                       match pres with
                         | None => None
                         | Some b => if b then selectHelper rem p (rcons t res)
                                          else selectHelper rem p res
                       end
 end.

Definition select (r : Relation) (p : Pred) : option Relation :=
 selectHelper r p rnil.

Fixpoint select' (r: Relation) (p: Pred) : option Relation :=
  match r with
    | rnil => Some rnil
    | rcons t r' =>
      match select' r' p with
        | None => None
        | Some r'' => 
          match evalPred p t with
            | None => None
            | Some true => Some (rcons t r'')
            | Some false => Some r''
          end
      end
  end.

Check select.

Eval simpl in rcons (tcons 1 (tcons 2 tnil)) (rcons (tcons 1 (tcons 3 tnil)) rnil).

Eval compute in select (rcons (tcons 1 (tcons 2 tnil)) (rcons (tcons 1 (tcons 3 tnil)) rnil)) (NBinop Eq (NConst 1) (AConst (Unnamed 0))).

Eval compute in select (rcons (tcons 1 (tcons 2 tnil)) (rcons (tcons 1 (tcons 3 tnil)) rnil)) (NBinop Eq (NConst 2) (AConst (Unnamed 1))).

Fixpoint rlength (r : Relation) : nat :=
  match r with
   | rnil => 0
   | rcons t rem => 1 + (rlength rem)
end. 

Ltac inv H :=
  inversion H; subst; clear H.

Theorem select'_decreasing :
  forall rel pred sel,
  select' rel pred = Some sel ->
  rlength sel <= rlength rel.
Proof.
  induction rel; intros.
  inv H; auto.

  remember H as H'; clear HeqH'.
  simpl in H'.
  destruct (select' rel pred) eqn:?; try discriminate.
  destruct (evalPred pred t) eqn:?; try discriminate.
  destruct b; inv H'; simpl.
  apply le_n_S. eapply IHrel; eauto.
  specialize (IHrel pred sel).
  apply IHrel in Heqo. omega.
Qed.  
  

Theorem select_decreasing :
  forall rel pred sel,
  select rel pred = Some sel ->
  rlength sel <= rlength rel.
Proof.
(*
  induction rel; simpl; intros.
  inversion H; subst. simpl; auto.
  destruct pred; simpl in H.
  destruct b. constructor.
*)
  


 forall pred rel, let rsel := select rel pred in
     match rsel with
       | None => True
       | Some rsel' => (rlength rsel') <= (rlength rel)
     end.
  induction rel.
  induction pred.
  intros.
  subst rsel.
  simpl.
  reflexivity.

  intros.
  subst rsel.
  simpl.
  reflexivity.
  
  Restart.
  induction pred.
  admit.
  admit.
  intros.
  subst rsel.
  (* actually need forall over preds *)
  Restart.

  intros.
  subst rsel.
  induction rel.
  induction pred.
  simpl.
  reflexivity.

  simpl.
  reflexivity.

  crush.

  (* here we dont have forall rel so can't unify *)
  apply IHrel.

