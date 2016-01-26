
(*

Script du thème 2 : couples.

*)
Require Import List.
Check (1, true).

Print prod.

Check (pair 1 true).

Check (1, true, (1::2::3::nil)).

Check (pair 1 (pair true (1::2::3::nil))).

Check (pair (pair 1 true) (1::2::3::nil)).

Eval compute in fst (1, true).

Eval compute in snd (1, true).

Theorem product_arrow:
  forall A B : Type,
  forall P : (A * B) -> Prop,
  exists P' : A -> B -> Prop,
    forall a : A, forall b : B,
      P (a, b) = P' a b.
Proof.
intros A B P.
exists (fun (a:A) (b:B) => P (a,b)).
intros a b.
reflexivity.
Qed.

(**

  ** Exercice 

Montrer le théorème réciproque [arrow_product].

*)

Theorem arrow_product:
  forall A B : Type,
  forall P : A -> B -> Prop,
  exists P' : (A * B) -> Prop,
    forall a : A, forall b : B,
      P a b = P' (a, b).
Proof.
intros A B P.
(*exists (fun (a:(A*B)) => P(a)).*)
Abort.


(**

  ** Exercice : le zip/unzip

  *** Question 1

Définir la fonction [zip].

*)

Fixpoint zip {A B : Type} (ass : list A) (bss : list B) : list (A * B) :=
match ass, bss with
    | nil, _ | _, nil => nil
    | (a::asl), (b::bsl) => ((a, b)::nil) ++ (zip asl bsl)
end.

(**

  *** Question 2

Montrer le lemme suivant :

*)

Lemma zip_length_l: 
  forall A B : Set, forall l1 : list A, forall l2 : list B,
    length l1 = length l2
    -> length (zip l1 l2) = length l1.
Proof.
intros A B l1 l2.
simpl.

(*

En déduire le lemme complémentaire [zip_length_r].

*)

(* <<REPONDRE ICI>> *)


(**

  *** Question 3

Démontrer un lemme intéressant nommé [zip_map] et reliant comme 
son nom l'indique les fonctions [zip] et [map].

*)

(* <<REPONDRE ICI>> *)



(**

  *** Question 4  (plus difficile)

Définir la fonction complémentaire [unzip] qui à partir d'une liste
 de couples produit un couple de listes.

*)

(* <<REPONDRE ICI>> *)

(** 

Montrer les propriétés suivantes :

*)

Lemma unzip_cons_fst:
  forall A B : Set, forall l : list (A * B), forall e : A * B,
    fst (unzip (e::l)) = (fst e)::(fst (unzip l)).
Proof.
  (* <<COMPLETER ICI>> *)


Lemma unzip_cons_snd:
  forall A B : Set, forall l : list (A * B), forall e : A * B,
    snd (unzip (e::l)) = (snd e)::(snd (unzip l)).
Proof.
  (* <<COMPLETER ICI>> *)



Theorem zip_unzip:
  forall A B : Set, forall l : list (A * B),
    let (l1, l2) := unzip l
    in zip l1 l2 = l.
Proof.
  (* <<COMPLETER ICI>> *)

(**

Démontrer finalement le lemme symétrique [unzip_zip].

*)

(* <<REPONDRE ICI>> *)

