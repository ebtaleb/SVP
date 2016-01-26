
(*

Script du thème 2 : les booléens

*)

Require Import List.

Check True. 
Check False.

Check true.
Check false.
Check bool.

Print bool.

Definition et (a:bool) (b:bool) : bool :=
  if a then b else false.

Example et_ex1:
  et true true = true.
Proof.
compute. reflexivity.
Qed.

Lemma et_false:
  forall b : bool, et false b = false.
Proof.
intro b.
unfold et.
reflexivity.
Qed.

(*

  ** Exercice

Définir la disjonction [ou] et démontrer un lemme comparable à [et_false] ci-dessus.

*)

Definition ou (a:bool) (b:bool) : bool :=
  if a then true else b.

Lemma ou_true:
  forall b : bool, ou true b = true.
Proof.
intro b.
unfold ou.
reflexivity.
Qed.

(*

  ** Exercice

  *** Question 1 :

Définir la fonction [filter] :

*)

Fixpoint filter {A : Set} (f : A -> bool) (l : list A) :=
match l with
    | nil => nil
    | e :: l' => if f e then e :: filter f l' else filter f l'
end.

Example filter_ex1:
  filter (fun a:bool => a)  (false::true::false::false::true::nil) = true::true::nil.
Proof.
compute.
trivial.
Qed.

(*

  *** Question 2 

Montrer deux lemmes qui vous semblent des propriétés "limites" de
 [filter].

*)

Lemma filter_true: forall A : Set, forall l : list A,
filter (fun a:A => true) l = l.
Proof.
intros A l.
induction l as [| e l'].
  - simpl.
    reflexivity.

  - simpl.
    rewrite IHl'.
    reflexivity.
Qed.

Lemma filter_false: forall A : Set, forall l : list A,
filter (fun a:A => false) l = nil.
Proof.
intros A l.
induction l as [| e l'].
  - simpl.
    reflexivity.

  - simpl.
    rewrite IHl'.
    reflexivity.
Qed.
