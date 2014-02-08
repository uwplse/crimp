Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

(* Defines a tuple of length 'n'. Zach's defition, not used. *)
Inductive tuplen (T: Set) : nat -> Set :=
| tnnil : tuplen T 0
| tncons : T -> forall l, tuplen T l -> tuplen T (S l).

(* Defines a relation of length 'n' re-using the tuplen definition. Zach's definition, not used. *)
Definition relation_n (T: Set) (r n: nat) : Set :=
  tuplen (tuplen T r) n.

(* Defines a relation of arbitrary length tuples. Zach's definition, not used. *)
Definition relation (T: Set) (r: nat) : Set :=
  list (tuplen T r).

(* Defines a list of length 'n' using refined types. 
   According to Zach, might make proofs harder.
   Zach's definition, not used. *)
Definition length_refined_lists (T: Set) (l: list T) (n: nat) : Set :=
  { l | @length T l = n }.

(* KM: What does this define, again? *)
Inductive nattuplen : nat -> Set :=
| ntnnil : nattuplen 0
| ntncons : nat -> forall l, nattuplen l -> nattuplen (S l).


(* Here starts the formalism done by Brandon and Kivanc. *)

(* Tuple, defined as a list of natural numbers. *)
Inductive tuple : Set :=
  | tnil : tuple
  | tcons : nat -> tuple -> tuple.

Eval simpl in tcons 1 tnil.

(* Relation defined as a list of tuples. *) 
Inductive Relation : Set :=
| rnil : Relation
| rcons : tuple -> Relation -> Relation.

Eval simpl in rcons (tcons 1 tnil) rnil.
Eval simpl in rcons (tcons 1 tnil) (rcons (tcons 2 tnil) rnil).

(* Attribute reference takes a natural number (unnamed index for that attribute). *)
Inductive AttrRef : Set :=
 | Unnamed : nat -> AttrRef.

(* Ways to construct natural expressions. *)
Inductive NExp : Set :=
 | NConst : nat -> NExp
 | AConst : AttrRef -> NExp.

(* Natural binary operations: takes two naturals. *)
Inductive nbinop : Set :=
 | Eq.

(* Boolean binary operations: takes two booleans. *)
Inductive bbinop : Set :=
  | And
  | Or.

(* Predicates:
   pred := bool
         | nbinop nat nat
         | bbinop pred pred *)
(* KM: Why does nbinop constructor take two NExp instead of two nat? *)
Inductive Pred : Set :=
  | BConst : bool -> Pred
  | NBinop : nbinop -> NExp -> NExp -> Pred
  | BBinop : bbinop -> Pred -> Pred -> Pred.

Eval simpl in BConst true.
Eval simpl in BConst false.
Eval simpl in BBinop And (BConst true) (BConst true).
Eval simpl in BBinop Or (NBinop Eq (AConst (Unnamed 0)) (NConst 3)) (NBinop Eq (NConst 2) (AConst (Unnamed 4))).

(* Returns the element (nat) in the given position (index) of the given tuple. 
   Returns None if the index is invalid (e.g., out of bounds.) *)
Fixpoint attrLookupHelper (t : tuple) (pos : nat) : option nat :=
 match t with
   | tnil => None
   | tcons attr rem => 
       if (beq_nat pos 0) 
       then (Some attr) 
       else attrLookupHelper rem (pos-1)
end.

(* Returns the element (nat) in the given attribute reference (position) of the given tuple.
   Returns None if the index is invalid. 
   @See attrLookupHelper. *)
Definition attrLookup (t : tuple) (a : AttrRef) : option nat :=
 match a with
     | Unnamed pos => attrLookupHelper t pos
end.

Eval simpl in attrLookup (tcons 10 (tcons 20 tnil)) (Unnamed 1).
Eval simpl in attrLookup tnil (Unnamed 0).
Eval simpl in attrLookup (tcons 10 (tcons 20 (tcons 30 tnil))) (Unnamed 3).

(* Evaluates an expression that returns a nat with the given tuple. 
   Tuple is required since the expression might be an attribute refrence. 
   If there is a violation, None is returned. *)
Definition evalNExp (e : NExp) (t : tuple) : option nat :=
  match e with
  | NConst n => Some n
  | AConst aref => attrLookup t aref
end. 

(* KM: I remember Zach putting this, but I don't rememeber why. *)
(* check it out : http://compcert.inria.fr/doc/html/Compiler.html *)

(* Evaluates the predicate (which returns a boolean) with the given tuple.
   If there is a violation, None is returned. *)
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

(* Our initial implementation for select with the helper function.
   Is there any reason to keep this (since we are using Zach's non-tail recursive version)? 
   Note: the loops in IMP will be defined tail recursive. *)
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

(* Alternative select implementation, non tail recursive.
   Given a relation and a predicate, returns a relation where the result only contains the tuples, which evaluated to true wrt to the predicate, in the original relation. 
   If there is a violation, returns None. *)
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

Eval simpl in rcons (tcons 1 (tcons 2 tnil)) (rcons (tcons 1 (tcons 3 tnil)) rnil).
Eval compute in select (rcons (tcons 1 (tcons 2 tnil)) (rcons (tcons 1 (tcons 3 tnil)) rnil)) (NBinop Eq (NConst 1) (AConst (Unnamed 0))).
Eval compute in select (rcons (tcons 1 (tcons 2 tnil)) (rcons (tcons 1 (tcons 3 tnil)) rnil)) (NBinop Eq (NConst 2) (AConst (Unnamed 1))).

(* Returns the number of tuples in a relation. *)
Fixpoint rlength (r : Relation) : nat :=
  match r with
   | rnil => 0
   | rcons t rem => 1 + (rlength rem)
end. 

(* KM: Left here. *)

Ltac inv H :=
  inversion H; subst; clear H.

Lemma ConsLength : forall rel1 rel2 t, rlength (rcons t rel1) <= rlength (rcons t rel2) -> rlength rel1 <= rlength rel2.
Proof.
  crush.
Qed.
Lemma ConsLength' : forall rel1 rel2 t, rlength rel1 <= rlength rel2 -> rlength (rcons t rel1) <= rlength (rcons t rel2).
Proof.
  crush.
Qed.
Lemma SucCons : forall rel t, rlength (rcons t rel) = S (rlength rel).
Proof.
crush.
Qed.
Lemma SucCons' : forall rel t, S (rlength rel) = rlength (rcons t rel).
Proof.
crush.
Qed.
Lemma MoveSuc : forall rel1 rel2 rel1', rlength rel1 <= S (rlength rel2) -> match rel1 with 
                                                                           | rnil => rlength rel1 <= rlength rel2
                                                                           | _ => S (rlength rel1') = rlength rel1 -> rlength rel1' <= rlength rel2
                                                                          end.
Proof.
intros.
destruct rel1 eqn:?.
crush.
crush.
Qed.

Lemma MoveSuc' : forall rel1 rel2, match rel1 with 
                                              | rnil => rlength rel1 <= rlength rel2
                                              | _ => exists rel1', S (rlength rel1') = rlength rel1 /\ rlength rel1' <= rlength rel2
                                            end ->  rlength rel1 <= S (rlength rel2).  
Proof.
intros.
destruct rel1 eqn:?.
crush.
crush.
Qed.
 Lemma ConsLengthTrans : forall rel1 rel2 rel3 t, rel1 = rcons t rel3 /\ rlength rel1 <= rlength rel2 -> rlength rel3 <= rlength rel2.
Proof.
crush.
Qed.


Theorem select'_decreasing :
  forall rel pred sel,
  select' rel pred = Some sel ->
  rlength sel <= rlength rel.
Proof.
  induction rel; intros.
  inv H; auto.

  remember H as H'; clear HeqH'. (* make a copy of H to keep it around *)
  simpl in H'.
  destruct (select' rel pred) eqn:?; try discriminate.
  destruct (evalPred pred t) eqn:?; try discriminate.
  destruct b; inv H'; simpl.
  Check le_n_S.
  apply le_n_S. eapply IHrel; eauto.  (* somehow avoided getting r0 and r mixed up *)
  specialize (IHrel pred sel). (* fill in pred and sel *)
  apply IHrel in Heqo. omega. (* tactic for inequalities on nats *)

  (* Qed here *)

  Restart.
  induction rel. 
  intros.
  simpl.
  unfold select' in H.
  inversion H. (* get rid of Some's both sides *)
  simpl.
  reflexivity.
  (* base case done *)

  intros.
  remember H as H'. clear HeqH'.
  inversion H.
  destruct (select' rel pred) eqn:?. (* eqn:? preserves the matched r'' relational *)
  destruct (evalPred pred t) eqn:?.
  destruct b. (* cases of pred true false *)
  (* b=true case *)
  inversion H1.
  apply ConsLength'.
  apply IHrel with pred.
  assumption.

  (*b = false case*)
  inversion H1.
  rewrite SucCons.
  apply MoveSuc'.
  destruct sel eqn:?.
  crush.
  exists r0.
  split.
  crush.
  apply ConsLengthTrans with r t0.
  split.
  assumption.
  apply IHrel with pred.
  assumption.
  
  (* evalPred => None case *)
  discriminate.

  (* select' => None case *)
  discriminate.
Qed.