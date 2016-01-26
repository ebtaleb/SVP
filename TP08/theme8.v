
Require Import Arith.
Require Import List.


(*-----------------------------------------------------------*)

(**  * Fonctions calculables vs. relations logiques *)

Fixpoint sum_fun (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => n + sum_fun m
  end.

Example sum_fun_5:
  sum_fun 5 = 15.
Proof.
  compute. reflexivity.
Qed.

Example sum_fun_10:
  sum_fun 10 = 55.
Proof.
  compute. reflexivity.
Qed.

Lemma two_times:
  forall n : nat, 2 * n = n + n.
Proof.
  intro n. ring.
Qed.

Theorem sum_fun_Gauss:
  forall n : nat, 2 * (sum_fun n) = n * (n + 1).
Proof.
  intro n.
  rewrite two_times.
  induction n as [| n'].
  - (* cas n=0 *)
    simpl.
    reflexivity.
  - (* cas n=S n' *)
    simpl.    
    (* SearchPattern (S _ = S _).
       eq_S: forall x y : nat, x = y -> S x = S y *)
    apply eq_S.
    assert (H:  n' + sum_fun n' + S (n' + sum_fun n')
                = sum_fun n' + sum_fun n' + n' + S n').
    { ring. }
    rewrite H. clear H.
    rewrite IHn'.
    ring.
Qed.


(*  Règles : 

                             n s : nat   sum_rel n s
   ============= (sum_O)    ============================ (sum_S)
    sum_rel 0 0              sum_rel (S n) ( (S n) + s)

*)

Inductive sum_rel : nat -> nat -> Set :=
| sum_O: sum_rel 0 0
| sum_S: forall n s:nat,
           sum_rel n s -> sum_rel (S n) ( (S n) + s).

Example sum_rel_3:
  sum_rel 3 6.
Proof.
  change (sum_rel 3 (3 + 3)).
  apply sum_S.
  change (sum_rel 2 (2 + 1)).
  apply sum_S.
  change (sum_rel 1 (1 + 0)).
  apply sum_S.
  apply sum_O.
Qed.

Theorem sum_rel_Gauss:
  forall n s : nat, (sum_rel n s) -> 2 * s = n * (n + 1).
Proof.
  induction n as [|n'].
  - (* cas n=0 *)
    intros s Hsum.
    inversion Hsum.
    simpl.
    reflexivity.
  - (* cas n=S n' *)
    intros s Hsum.
    inversion Hsum. clear Hsum n H H1.
    apply IHn' in H0. clear IHn'.
    rewrite two_times in *.
    assert (H1: S n' + s0 + (S n' + s0) = s0 + s0 + S n' + S n').
    { ring. }
    rewrite H1. clear H1.
    rewrite H0.
    ring.
Qed.

Theorem sum_rel_Gauss':
  forall n s : nat, (sum_rel n s) -> 2 * s = n * (n + 1).
Proof.
  intros n s H.
  induction H.  (* rule induction *)
  - (* cas sum_O *)
    simpl.
    reflexivity.
  - (* cas sum_S *)
    rewrite two_times in *.
    assert (H1: S n + s + (S n + s) = s + s + S n + S n).
    { ring. }
    rewrite H1. clear H1.
    rewrite IHsum_rel.
    ring.
Qed.


(** ** Exercice 1 *)

(** *** Question 1 *)

Fixpoint concat_fun {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
    | nil => l2
    | a :: l1 => a :: concat_fun l1 l2
  end.

(** *** Question 2 *)

Inductive concat_rel (A : Set) : list A -> list A -> list A -> Prop :=
| concat_nil: forall l : list A, concat_rel A nil l l
| concat_cons: forall e1 : A,
               forall l1 l2 l3 : list A,
                 concat_rel A l1 l2 l3
                 -> concat_rel A (e1::l1) l2 (e1::l3).

Arguments concat_nil [A] _.
Arguments concat_cons [A] _ _ _ _ _.

Print concat_rel.

Check concat_rel_ind.

(** *** Question 3 *)

Lemma concat_fun_cons:
  forall A : Set, forall e : A, forall l1 l2 : list A,
    concat_fun (e::l1) l2 = e::(concat_fun l1 l2).
Proof.
intros A e l1 l2.
destruct l1.
-simpl.
 reflexivity.
-simpl.
 reflexivity.
Qed.

(** *** Question 5 *)

Lemma concat_fun_length:
  forall A : Set, forall l1 l2 : list A,
    length (concat_fun l1 l2) = (length l1) + (length l2).
Proof.
  intros A l1 l2.
  induction l1 as [|l' ll'].
  -simpl.
   reflexivity.
  -simpl.
   rewrite IHll'.
   reflexivity.
Qed.

  (** *** Question 4 *)

Lemma concat_rel_cons:
  forall A : Set, forall e : A, forall l1 l2 l3 : list A,
    concat_rel A l1 l2 l3 -> concat_rel A (e::l1) l2 (e::l3).
Proof.
  intros A e l1 l2 l3 Hrel.
  induction Hrel.
  - apply concat_cons.
    apply concat_nil.
  - apply concat_cons.
    apply concat_cons.
    exact Hrel.
Qed.
    (** *** Question 6 *)

Lemma concat_rel_length:
  forall A : Set, forall l1 l2 l3 : list A,
    concat_rel A l1 l2 l3 
    -> length l3 = (length l1) + (length l2).
Proof.
  intros A l1 l2 l3 Hrel.
  induction Hrel.  (* rule induction *)
  - simpl.
    reflexivity.
  - (* cas concat_cons *)
    simpl.
    SearchPattern (S (_) = S (_)).
    apply eq_S.
    exact IHHrel.
Qed.
(** ** Exercice 2 : appartenance à une liste *)

Section is_in.

Variable A : Set.
Variable A_eq_dec : forall a b : A, {a = b} + {a <> b}.

Fixpoint is_in_fun (e : A) (l : list A) : bool :=
  match l with
    | nil => false
    | e'::l' => match A_eq_dec e e' with
                  | left _ => true
                  | right _ => is_in_fun e l'
                end
  end.

End is_in.

Check is_in_fun.

Example is_in_fun_ex1:
  is_in_fun nat (eq_nat_dec) 3 (1::2::3::4::5::nil) = true.
Proof.
  compute. reflexivity.
Qed.

(** *** Question 1 *)

Inductive is_in_rel (A:Set) : A -> list A -> Prop :=
  is_in_head: forall a : A, forall l : list A, is_in_rel A a (a::l)
| is_in_tail: forall a b : A, forall l : list A, a <> b -> is_in_rel A a l -> is_in_rel A a (b::l).

(** *** Question 2 *)
    
Example is_in_rel_ex1:
  is_in_rel nat 3 (1::2::3::4::5::nil).
Proof.
  apply is_in_tail.
  discriminate.
  apply is_in_tail.
  discriminate.
  apply is_in_head.
Qed.
(** ** Exercice 3 : liste préfixe *)

Section is_prefix.

Variable A : Set.
Variable A_eq_dec : forall a b : A, {a = b} + {a <> b}.

Fixpoint is_prefix_fun (l1 l2 : list A) : bool :=
  match l1 with
    | nil => true
    | e1::l1' => match l2 with
                   | nil => false
                   | e2::l2' => match A_eq_dec e1 e2 with
                                  | left _ => is_prefix_fun l1' l2'
                                  | right _ => false
                                end
                 end
  end.

End is_prefix.


(** *** Question 1 *)

Inductive is_prefix_rel (A : Set) : list A -> list A -> bool -> Prop :=
| is_prefix_nil: forall l : list A, is_prefix_rel A nil l l
| is_prefix_cons: forall e1 : A,
               forall l1 l2 l3 : list A,
                 is_prefix_rel A l1 l2 l3
                 -> is_prefix_rel A (e1::l1) l2 (e1::l3).

(** *** Question 2 *)

[[
Lemma is_prefix_is_in_fun: 
  forall A : Set, forall A_eq_dec : forall a b : A, {a = b} + {a <> b},
    forall l2 l1 : list A,
      (is_prefix_fun A A_eq_dec l1 l2) = true 
      -> (forall e :  A, is_in_fun A A_eq_dec e l1 = true -> is_in_fun A A_eq_dec e l2 = true).
Proof.
  intros A A_eq_dec.
  induction l2 as [| e2 l2'].
  - (* cas l2 = nil *)
    (* <<< A COMPLETER >>>> *)
  - (* cas l2=e2::l2' *)
    intros l1 H1 e H2.
    simpl.
    destruct (A_eq_dec e e2).
    + (* cas e=e2 *)
      reflexivity.
    + (* cas e<>e2 *)
      { destruct l1 as [| e1 l1'].
        - (* cas l1=nil *)
          (* <<< A COMPLETER >>> *)
        - (* cas l1=e1::l1' *)
          { apply IHl2' with (l1:=l1').
              (* <<< A COMPLETER >>> *)
          }
      }
Qed.

(** *** Question 3 *)

Lemma is_prefix_is_in_rel: 
  forall A : Set,
  forall l1 l2 : list A,
    (is_prefix_rel A l1 l2)
    -> (forall e :  A, is_in_rel A e l1 -> is_in_rel A e l2).
Proof.
  intros A l1 l2 Hprefix.
  induction Hprefix.
  (* <<<A COMPLETER>>> *)


