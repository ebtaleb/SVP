
(** * Etude de cas : sémantiques opérationnelles *)

Require Import ZArith.

Open Scope Z_scope.

Inductive ArithExpr : Set :=
| aval : Z -> ArithExpr
| aplus : ArithExpr -> ArithExpr -> ArithExpr
| atimes: ArithExpr -> ArithExpr -> ArithExpr.

(** ** Exercice 1 : sémantique à grands pas *)

Inductive BigSem : ArithExpr -> Z -> Set :=
| aval_big: forall n : Z, BigSem (aval n) n
| aplus_big: forall a1 a2 : ArithExpr, forall v1 v2 : Z,
        BigSem a1 v1 -> BigSem a2 v2
        -> BigSem (aplus a1 a2) (v1 + v2)
| atimes_big: forall a1 a2 : ArithExpr, forall v1 v2 : Z,
        BigSem a1 v1 -> BigSem a2 v2
        -> BigSem (atimes a1 a2) (v1 * v2).

Check BigSem_ind.


(* <<<REPONDRE ICI>>> *)

(** *** Question 2 *)

Example big_ex1:
  BigSem (atimes (aplus (aval 2) (aval 3)) (aval 5))
         (* ==> *) 25.
Proof.
change (BigSem (atimes (aplus (aval 2) (aval 3)) (aval 5)) (5 * 5)) .
apply atimes_big.
- change (BigSem (aplus (aval 2) (aval 3)) (2 + 3)).
  apply aplus_big.
    + apply aval_big.
    + apply aval_big.
- apply aval_big.
Qed.

(** *** Question 3 *)

Theorem BigSem_determinist:
  forall a : ArithExpr, forall v1 v2 : Z,
    BigSem a v1
    -> BigSem a v2
    -> v1 = v2.
Proof.
intros a v1 v2 BS1 BS2.
inversion BS1.
-   inversion BS2.
    + rewrite <- H in H1.
      inversion H1.
      rewrite H4 in H2.
      rewrite H0 in H2.
      exact H2.
    + inversion H1.
      * inversion H2.
      { - inversion H3.
          + }
exact H4.
Qed.

(** ** Exercice 2 : sémantique à petits pas *)

Inductive SmallSem: ArithExpr -> ArithExpr -> Prop :=
| aplusl_small: forall a1 a1' a2: ArithExpr,
                  SmallSem a1 (* --> *) a1'
                  (*------------------------------------------*)
                  -> SmallSem (aplus a1 a2) (aplus a1' a2)
| aplusr_small: forall a1 a2 a2' : ArithExpr,
                  SmallSem a2 (* --> *) a2'
                  (*------------------------------------------*)
                  -> SmallSem (aplus a1 a2) (aplus a1 a2')
| aplusv_small: forall v1 v2 : Z,
                  (*----------------------------------------------------*)
                  SmallSem (aplus (aval v1) (aval v2)) (aval (v1 + v2)).

(** *** Question 1 *)

(* <<< Répondre sur papier >>> *)

(** *** Question 2 *)

(* <<< Répondre sur paper et ci-dessus >>> *)


(** *** Question 3 *)

Inductive value: ArithExpr -> Prop :=
| const_value: forall n, value (aval n).

Theorem Strong_Progress:
  forall a: ArithExpr,
    value a \/ exists a' : ArithExpr, SmallSem a a'.
Proof.
  (* <<< COMPLETER ICI >>> *)

(** ** Exercice 3 : formes normales *)

Definition NormalForm (a : ArithExpr) : Prop :=
  not (exists a' : ArithExpr, SmallSem a a').

(** *** Question 1 *)

Lemma value_is_NF:
  forall a : ArithExpr,
    value a -> NormalForm a.
Proof.
  (* <<< COMPLETER ICI >>> *)

Lemma NF_is_value:
  forall a : ArithExpr,
    NormalForm a -> value a.
Proof.
  (* <<< COMPLETER ICI >>> *)

(** *** Question 2 *)

(* <<< REPONDRE ICI >>> *)

(** *** Question 3 *)

Lemma Reduce_refl: forall a : ArithExpr,
  Reduce a a.
Proof.
  (* <<< COMPLETER ICI >>> *)

Lemma Reduce_Small: forall a a' : ArithExpr,
  SmallSem a a' -> Reduce a a'.
Proof.
  (* <<< COMPLETER ICI >>> *)

(** *** Question 4 *)

Lemma Reduce_trans: forall a a' a'' : ArithExpr,
  Reduce a a' -> Reduce a' a'' -> Reduce a a''.
Proof.
  (* <<< COMPLETER ICI >>> *)

(** ** Exercice 4 : correspondance des sémantiques  *)

(** *** Question 1 *)

Lemma Reduce_plus_congl: forall a1 a2 a1' : ArithExpr,
  Reduce a1 a1'
  -> Reduce (aplus a1 a2) (aplus a1' a2).
Proof.
  (* <<< COMPLETER ICI >>> *)

Lemma Reduce_plus_congr: forall a1 a2 a2' : ArithExpr,
  Reduce a2 a2'
  -> Reduce (aplus a1 a2) (aplus a1 a2').
Proof.
  (* <<< COMPLETER ICI >>> *)

Lemma Reduce_plus_congv:
  forall n1 n2 : Z, forall a1 a2 : ArithExpr,
    Reduce a1 (aval n1)
    -> Reduce a2 (aval n2)
    -> Reduce (aplus a1 a2) (aval (n1+n2)).
Proof.
  (* <<< COMPLETER ICI >>> *)

(** *** Question 2 *)

Lemma Reduce_times_congl: forall a1 a2 a1' : ArithExpr,
  Reduce a1 a1'
  -> Reduce (atimes a1 a2) (atimes a1' a2).
Proof.
    (* <<< COMPLETER ICI >>> *)

Lemma Reduce_times_congr: forall a1 a2 a2' : ArithExpr,
  Reduce a2 a2'
  -> Reduce (atimes a1 a2) (atimes a1 a2').
Proof.
    (* <<< COMPLETER ICI >>> *)

Lemma Reduce_times_congv:
  forall n1 n2 : Z, forall a1 a2 : ArithExpr,
    Reduce a1 (aval n1)
    -> Reduce a2 (aval n2)
    -> Reduce (atimes a1 a2) (aval (n1 * n2)).
Proof.
    (* <<< COMPLETER ICI >>> *)

(** *** Question 3 *)

Lemma Big_implies_Small:
  forall a : ArithExpr, forall v : Z,
    BigSem a v -> Reduce a (aval v).
Proof.
    (* <<< COMPLETER ICI >>> *)


(** *** Question 4 *)

Lemma Small1_Big_implies_Big_plus:
  forall a a' : ArithExpr, forall v : Z,
    SmallSem a a'
    -> BigSem a' v
    -> BigSem a v.
Proof.
    (* <<< COMPLETER ICI >>> *)

(** *** Question 5 *)

Lemma SmallNF_implies_Big:
  forall a a': ArithExpr,
    Reduce a a'
    -> NormalForm a'
    -> (exists v : Z, (a' = aval v)  /\ (BigSem a v)).
Proof.
  (* <<< COMPLETER ICI >>> *)


(** *** Question 6 *)

Lemma Small_implies_Big:
  forall a : ArithExpr, forall v : Z,
    Reduce a (aval v)
    -> BigSem a v.
Proof.
  (* <<< COMPLETER ICI >>> *)

(** *** Question 7 *)

Theorem Small_equiv_Big:
  forall a : ArithExpr, forall v : Z,
    Reduce a (aval v) <-> BigSem a v.
Proof.
    (* <<< COMPLETER ICI >>> *)



