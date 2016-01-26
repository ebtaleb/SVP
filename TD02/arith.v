
(*

Script du thème 2 : arithmétique.

*)

Require Import Arith.

Print nat.

Example Zero: 0 = O.
Proof. reflexivity. Qed.

Example Cinq: 5 = S (S (S (S (S O)))).
Proof. reflexivity. Qed.

Definition double (n : nat) : nat := 2 * n. 

Example square_2_is_2plus2: 
  double 2 = 2 + 2.
Proof.
compute.
reflexivity.
Qed.

Lemma double_plus:
forall n : nat, double n = n + n.
Proof.
destruct n as [| n']. (* raisonnement par cas *)
  - (* cas de base: n=0 *)
    compute.  (* remarque : terme clos *)
    reflexivity.
  - (* cas récursif: n=S n' *)
    unfold double.
    simpl.
    SearchPattern ( S _ = S _ ).
    (* eq_S: forall x y : nat, x = y -> S x = S y *)
    apply eq_S.
    SearchPattern ( ?X + 0 = ?X).
    (* plus_0_r: forall n : nat, n + 0 = n *)
    rewrite plus_0_r.
    reflexivity.
Qed.

Lemma double_plus':
forall n : nat, double n = n + n.
Proof.
intro n.
unfold double.
ring.
Qed.

Check nat_ind.

Lemma plus_0_r':
  forall n : nat, n + 0 = n.
Proof.
intro n.
induction n as [| n'].
  - (* cas n=0 *)
    trivial.
  - (* cas n = S n' *)
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Lemma plus_0_r'':
  forall n : nat, n + 0 = n.
Proof.
  auto with arith.
Qed.

(* ** Exercice

La relation naturelle entre les listes et les entiers naturels est bien sûr la notion de longueur de liste.

 *** Question 1

Définir une fonction [longueur] retournant la longueur d'une liste.

*)
Print length.
Require Import List.
Fixpoint longueur {A: Set}(l : list A) : nat :=
  match l with
    | nil => 0
    | (e::l') => S (longueur l')
end.

(**

  *** Question 2

*)

Print length.

(**

Montrer que les deux fonctions [longueur] et [length]
effectuent le même calcul.
  
*)

Lemma len_long : forall A : Set, forall l : list A,
 length l = longueur l.
Proof.
induction l as [|e l'].
-compute.
 trivial.

-simpl.
inversion IHl'.
trivial.
Qed.


(**

 *** Question 3

Démontrer le lemme suivant :

*)

Lemma length_app:
  forall A : Set, forall l1 l2 : list A,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
intros A l1 l2.
induction l1 as [|e l'].
-simpl.
 trivial.

-simpl.
rewrite IHl'.
trivial.

Qed.

(** 

 *** Question 4

Montrer que [length (map f l) = length l].

*)
Require Import List.
Lemma id_lenmap_len:
  forall A B : Set, forall l: list A, forall f : A -> B, 
   length (map f l) = length l.
Proof.
intros A B l f.
induction l as [|e l'].
-simpl.
 trivial.

-simpl.
 rewrite IHl'.
 trivial.

Qed.


(** 

** Exercice 

*** Question 1

Définir la fonction [sum] calculant : $\sum_{i=0}^{n} i$.

*)

(*Fixpoint sum_it (n : nat) (a : nat) : nat :=
  match n with
   | 0 => a
   | S m => sum (m) (a + n)
end.*)

Fixpoint sum (n : nat) : nat :=
  match n with
   | 0 => 0
   | S m => n + sum m
end.

(**

  *** Question 2  (un peu plus corsée)

Démontrer le théorème classique de la somme : $2 \times \sum^n_{i=1} = n * (n + 1)$.

*)

Example sum1 : forall n : nat, sum 3 = 6.
Proof.
compute.
reflexivity.
Qed.

Theorem arith_sum :
forall n: nat, 2 * sum n = n * (n + 1).

Proof.
induction n as [| n'].
-simpl.
 trivial.

-simpl.
 SearchRewrite ( _ * S (_) ).
 rewrite mult_succ_r.
 SearchPattern ( S _ = S _ ).
 apply eq_S.
 rewrite <- IHn'.
 ring.
Qed.

(**

 ** Exercice : la factorielle


 *** Question 1

Soit la fonction factorielle sur les entiers naturels.

*)

Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S m => fact m * n
  end.

Example fact_5: fact 5 = 120.
Proof.
  compute.
  reflexivity.
Qed.

(**

Définir une version [fact_it] récursive terminale de la factorielle.

*)

Fixpoint fact_it (n:nat) (a:nat) : nat :=
  match n with
    | O => a
    | S m => fact_it m (a * n)
  end.

Example factit_5: fact_it 5 1 = 120.
Proof.
  compute.
  reflexivity.
Qed.

(**

 *** Question 2

Démontrer le lemme suivant :

*)

Lemma fact_it_lemma:
  forall n k:nat, fact_it n k = k * (fact n).
Proof.
intros n.
induction n as [| n'].
-intro k.
 simpl.
 SearchRewrite( _ * 1).
 rewrite mult_1_r.
 reflexivity.

- intro k.
  simpl.
  rewrite IHn'.
  SearchRewrite ( _ * ( _ * _) ).
  rewrite mult_assoc.
  ring.
Qed.


(** 

 *** Question 3

En déduire un théorème permettant de relier
 les deux versions de la factorielle.

*)

Theorem eq_fact_factit :
  forall n:nat, fact_it n 1 = fact n.
Proof.
intros n.
induction n as [| n'].

-simpl.
 trivial.

-simpl.
rewrite fact_it_lemma.
ring.
Qed.


(**

  ** Exercice : Fibonacci

  *** Question 1

Définir une fonction [fib] de calcul de la suite
 de Fibonacci.

*)

Fixpoint fib (n:nat) : nat :=
match n with
  | 0 => 1
  | 1 => 1
  | S m => fib (S m) + fib (m)
end.

Example fib_ex: fib 4 = 5.
Proof.
  compute.
  reflexivity.
Qed.

(**

  *** Question 2

Démontrer par cas le lemme suivant :

*)

Lemma fib_plus_2: 
  forall n:nat, fib (S (S n)) = fib n + fib (S n).
Proof.
intro n.
induction n as [| n'].

-simpl.
 reflexivity.

-Abort.


(**

 *** Question 3 :

Donner une définition [fib_it] récursive terminale de Fibonacci. 

*)

Fixpoint fib_aux (n:nat) (a:nat) (b:nat) : nat :=
    match n with
      | 0 => b
      | S (m) => fib_aux m (b) (a + b)
end.

Definition fib_it (n:nat) : nat := fib_aux n 0 1.

(**

  *** Question 4

Démontrer le théorème suivant :

*)
 
Theorem fib_it_fib:
  forall n:nat, fib_it n 1 1 = fib n.
Proof.
  (* <<COMPLETER ICI>> *)


