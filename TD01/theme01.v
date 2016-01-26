
(*

  Script du Thème 01 :  fonctions récursives

*)

(*

 * Fonctions simples

let id (e:'a) : 'a = e
val id : 'a -> 'a = <fun>

*)

Definition id {A:Set} (a:A) : A := a.

(*

# id 12 ;;
- : int = 12
# id true ;;
- : bool = true


*)

Eval compute in id 12.

Eval compute in id true.

Example id_12: id 12 = 12.
Proof.
compute.
reflexivity.
Qed.

Lemma id_id:
  forall A : Set, forall a : A,
    id a = a.
Proof.
intros A a.
compute.
reflexivity.
Qed.

(**

  ** Exercice : fonction constante

Définir en Ocaml puis traduire en Coq la fonction [constant] qui retourne toujours le premier
de ses deux arguments.

Tester avec [constant 12 true]

Montrer que [constant (id a) b = a].

*)

Definition constant {A B : Set} (a: A) (b : B) : A := a.

Example cst_12: constant 12 true = 12.
Proof.
  compute.
  reflexivity.
Qed.

Lemma cst_ab:
  forall A B : Set,  forall a : A, forall b : B,  constant (id a) b = a.
Proof.
  intros A B a b.
  compute.
  reflexivity.
Qed.



(*

  Un autre exemple de fonction.

*)

Definition flip {A B C:Set} (f:A -> B -> C) : B -> A ->  C :=
  fun (b:B) (a:A) => f a b.

(*

let flip (f:'a -> 'b -> 'c) : 'b -> 'a -> 'c =
   fun (b:B) (a:A) -> f a b.

*)

Lemma flip_flip:
  forall A B C : Set, forall f : A -> B -> C,
    flip (flip f) = f.
Proof.
intros A B C f.
unfold flip.
reflexivity.
Qed.

Lemma flip_flip_flip_flip:
  forall A B C : Set, forall f : A -> B -> C,
    f = flip (flip (flip (flip f))).
Proof.
intros A B C f.
rewrite flip_flip.
rewrite flip_flip.
reflexivity.
Qed.

Lemma flip_flip_flip_flip':
  forall A B C : Set, forall f : A -> B -> C,
    f = flip (flip (flip (flip f))).
Proof.
repeat rewrite flip_flip ; reflexivity.
Qed.


(*

 ** Fonctions totales

# let rec until (pred: 'a -> bool) (f:'a -> 'a) (a:'a) : 'a =
     if pred a then until pred f (f a)
     else a ;;

*)

(*

<<DECOMMENTER POUR ESSAYER>>

Fixpoint until {A:Set} (pred: A -> bool) (f:A -> A) (a:A) : A :=
  if pred a then until pred f (f a)
  else a.

*)

Fixpoint untiln {A:Set} (n:nat) (pred: A -> bool) (f:A -> A) (a:A) : A :=
  if pred a then match n with
                     | 0 => a
                     | S n' => untiln n' pred f (f a)
                 end
  else a.

Lemma untiln_id:
  forall A : Set, forall n:nat,
  forall pred:A -> bool, forall a : A,
    untiln n pred id a = a.
Proof.
intros A n pred a.
induction n as [|n'].
  - (* cas n=0 *)
    simpl.
    case (pred a) ; reflexivity.
  - (* cas n=S n' *)
    simpl.
    destruct (pred a).
    + (* cas (pred a) = True *)
      rewrite id_id.
      rewrite IHn'.
      reflexivity.
    + (* cas (pred a) = False *)
      reflexivity.
Qed.


(*

  * Fonctions sur les listes

*)

Require Import List.

Print list.

Check cons 1 (cons 2 (cons 3 nil)).

Example cons_infixe:
 1::2::3::nil = cons 1 (cons 2 (cons 3 nil)).
Proof.
reflexivity.
Qed.


(*

 ** Une première fonction

let rec concat (l1 : 'a list) (l2 : 'a list) : 'a list =
  match l1 with
  | [] -> l2
  | e::l1' -> e::(concat l1' l2)

*)

Fixpoint concat {A : Set} (l1 l2 : list A) : list A :=
  match l1 with
    | nil => l2
    | e::l1' => e::(concat l1' l2)
  end.

Eval compute in concat (1::2::nil) (3::4::5::nil).

Example concat_ex1:
  concat (1::2::3::nil) (4::5::nil)  = 1::2::3::4::5::nil.
Proof.
compute.
reflexivity.
Qed.

Lemma nil_concat:
  forall A : Set, forall l : list A,
    concat nil l = l.
Proof.
intros A l.
simpl.
reflexivity.   (* ou [trivial] *)
Qed.

Lemma concat_nil_fails:
  forall A : Set, forall l : list A,
  concat l nil = l.
Proof.
intros A l.
simpl.  (* bloqué *)
Abort.

Lemma concat_nil_destruct:
  forall A : Set, forall l : list A,
  concat l nil = l.
Proof.
intros A l.
destruct l as [| e l'].
  - (* cas nil : l=nil *)
    simpl.
    reflexivity.
  - (* cas cons: l=e::l' *)
    simpl.  (* bloqué *)
Abort.

Lemma concat_nil:
  forall A : Set, forall l : list A,
  concat l nil = l.
Proof.
induction l as [|e l'].
  - (* cas de base : l=nil *)
    simpl.
    reflexivity.
  - (* cas inductif: l=e::l' *)
    simpl.
    rewrite IHl'.
    reflexivity.
Qed.

(* Le schéma de preuve qui a été
suivi : *)

Check list_ind.

(*

  ** Fonctions partielles

# exception Boum ;;
exception Boum
# let boum (e:'a) = raise Boum ;;
val boum : 'a -> 'b = <fun>

*)

Print option.

Definition head {A:Set} (l:list A) : option A :=
  match l with
      | nil => None
      | e::_ => Some e
  end.

Example head_ex1:
  head (1::2::3::4::nil) = Some 1.
Proof.
compute.
reflexivity.
Qed.

Lemma head_concat:
  forall A : Set, forall l1 l2 : list A,
    head (concat l1 l2) =
    match l1 with
      | nil => head l2
      | e1::l1' =>  Some e1
    end.
Proof.
intros A l1 l2.
destruct l1 as [| e1'' l1''].
  - (* cas l1 = nil *)
    simpl.
    reflexivity.
  - (* cas l1 = e1''::l1'' *)
    simpl.
    reflexivity.
Qed.

(*

one-liner

*)

Lemma head_concat':
  forall A : Set, forall l1 l2 : list A,
    head (concat l1 l2) =
    match l1 with
      | nil => head l2
      | e1::l1' =>  Some e1
    end.
Proof.
  destruct l1 ; trivial.
Qed.

Definition tail {A:Set} (l:list A) : list A :=
  match l with
      | nil => nil
      | _::l' => l'
  end.

Lemma tail_amb:
  forall A : Set, forall e : A,
    tail nil = tail (e::nil).
Proof.
intros A e.
simpl.
reflexivity.
Qed.

Lemma head_tail:
  forall A : Set, forall e : A, forall l : list A,
    head l = Some e -> e :: tail l = l.
Proof.
intros A e l Hhead.
destruct l as [| e' l'].
  - (* cas l = nil *)
    inversion Hhead. (* contradiction *)
  - (* cas l = e'::l' *)
    simpl.
    inversion Hhead as [ He ].
    reflexivity.
Qed.


(*

 ** Exercice : [untiln] partielle

La fonction [untiln] vue précédemment devrait être réécrite pour
être une fonction partielle. En particulier, si la borne d'approximation
est atteinte, le résultat devrait être [None].

Réécrire la fonction [untiln] en conséquence. Que faire du lemme démontré
 sur cette fonction ?

*)

Fixpoint untiln_part { A : Set } ( n : nat ) ( pred : A -> bool ) ( f : A -> A ) ( a : A ) : option A :=
  if pred a
  then Some(a)
  else
    match n with
      | 0 => None
      | S n' => untiln_part n' pred f ( f a )
    end.

(*
Réponse : On oublie le lemme, (c'est plus compliqué)
*)

Lemma untiln_part_id:
  forall A : Set, forall n:nat,
  forall pred:A -> bool, forall a : A, forall x:A,
    untiln_part n pred id a = Some(x) -> x = a.
Proof.
intros A n pred a x.
induction n as [|n'].
  - (* cas n=0 *)
    simpl.
    case (pred a).
      +intros H.
      inversion H.
      reflexivity.
      +intros H.
      inversion H.
  - (* cas n=S n' *)
    simpl.
    destruct (pred a).
    + intros H.
      inversion H.
      reflexivity.
    + (* cas (pred a) = False *)
      exact IHn'.
Qed.

(*

 ** Exercice : Renversement de liste

 *** Question 1

Définir la fonction [rev] qui renverse les élément d'une liste.

*)

Fixpoint rev {A: Set} (l : list A) : list A :=
match l with
  | nil => nil
  | e :: l1' => concat (rev l1') (e :: nil)
end .


(*
 *** Question 2

Compléter l'exemple suivant :

*)


Example rev_ex1:
  rev (1::2::3::4::5::nil) = 5::4::3::2::1::nil.
Proof.
  simpl.
  reflexivity.
Qed.

(**

 *** Question 3

On souhaite montrer que [rev] est idempotent, mais la preuve suivante
 bloque.

*)

Theorem rev_rev_fails:
  forall A : Set, forall l : list A,
    rev (rev l) = l.
Proof.
intros A l.
induction l as [| e l'].
  - (* cas l=nil *)
    simpl.
    reflexivity.
  - (* cas l=e::l' *)
    simpl. (* bloqué *)
Abort.

(*

Il nous manque une propriété importante reliant [rev], [concat] et [nil].

Démonter le lemme [rev_concat_nil] correspondant. En déduire une preuve
complète pour le théorème [rev_rev].

*)


Lemma rev_concat_nil:
    forall A : Set, forall l : list A, forall e : A, 
    rev (concat l (e::nil)) = e :: rev l.
Proof.
  induction l as [|e' l'].
  -intro.
   simpl.
   reflexivity.

  -intro.
   simpl.
   rewrite IHl'.
   simpl.
   reflexivity.
   Qed.

Theorem rev_rev:
  forall A : Set, forall l : list A,
    rev (rev l) = l.
Proof.
  intros A l.
  induction l as [|e l'].

  -simpl.
   reflexivity.

  -simpl.
   rewrite rev_concat_nil.
   rewrite IHl'.
   reflexivity.  
Qed.


(*

 ** Exercice : dernier élément

 *** Question 1

Définir la fonction [last] qui retourne le dernier élément d'une
liste non-vide.  Cette fonction prendra un argument [d]  (pour défaut) que l'on retournera si la liste est vide.

*)

Fixpoint last {A : Set} (l : list A) (d:A) : A :=
  match l with
    | nil => d
    | e :: nil => e
    | e :: l' => last l' d
  end.
    
       

(*

*** Question 2

Montrer le lemme suivant.

*)

Lemma last_single:
  forall A : Set, forall d e : A,
    last (e::nil) d = e.
Proof.
  intros A d e.
  simpl.
  trivial.
Qed.


(*

*** Question 3

Montrer par induction le lemme suivant.

*)

Lemma concat_cons_not_nil:
  forall A : Set, forall l1 l2 : list A, forall e : A,
    concat l1 (e::l2) <> nil.
Proof.
  intros A l1 l2 e.
  unfold not.
  intro Hcontra.
  destruct l1 as [| e1 l1'].
  - (* cas l1=nil *)
    simpl in Hcontra.
    inversion Hcontra.
  - (* cas l1=e1::l1' *)
    simpl in Hcontra.
    inversion Hcontra.
Qed.

Lemma last_concat:
  forall A : Set, forall l1 l2 : list A, forall d e : A,
    last (concat l1 (e::l2)) d = last (e::l2) d.
Proof.
  intros A l1 l2 d e.
  induction l1 as [|e1 l1'].

  -rewrite nil_concat.
   trivial.

  - cut (concat (e1 :: l1') (e :: l2) = e1 :: (concat l1' (e :: l2) )).
    +intros H.
    rewrite H.
    cut (last (e1 :: concat l1' (e :: l2)) d = last (concat l1' (e::l2)) d).
    *intros H1.
    rewrite H1.
    exact IHl1'.
    *
    simpl.
    destruct (concat l1' (e :: l2)).
      {-simpl.
    Abort.


(*

  * Fonctions d'ordre supérieur

 ** Exercice : la fonction map

*)

Fixpoint map {A B :Set} (f:A -> B) (l:list A) : list B :=
  match l with
    | nil => nil
    | e::l' => (f e) :: map f l'
  end.

(**

  *** Question

Démontrer les lemmes suivants :

*)


Lemma head_map:
  forall A B : Set, forall e : A, forall l : list A, forall f : A -> B,
    head (map f (e::l)) = Some (f e).
Proof.
  intros A B e l f.
  simpl.
  reflexivity.
Qed.


Lemma map_id:
  forall A : Set, forall l : list A,
    map id l = l.
Proof.
  intros A l.
  induction l as [|e l'].
  - simpl.
    reflexivity.

  - simpl.
    rewrite IHl'.
    reflexivity.
Qed.
   
Lemma map_concat:
  forall A B : Set, forall l1 l2 : list A, forall f : A -> B,
    map f (concat l1 l2) = concat (map f l1) (map f l2).
Proof.
  intros A B l1 l2 f.
  induction l1 as [|e l1'].

  - simpl.
    reflexivity.

  -simpl.
   rewrite IHl1'.
   reflexivity.
Qed.

(*

  ** Exercice : la fonction foldr

*)

Fixpoint foldr {A B :Set} (f:A -> B -> B) (u:B) (l:list A) : B :=
  match l with
    | nil => u
    | e::l' => f e (foldr f u l')
  end.

(*

  *** Question 1

Définir une fonction [folder_id] : *)

Definition folder_id {A :Type} (a : A) (b : list A) : list A := a :: b.

(* telle que l'exemple suivant est prouvable : *)


Example foldr_id_ex1:
  foldr folder_id nil (1::2::3::nil) = (1::2::3::nil).
Proof.
  compute.
  reflexivity.
Qed.

(* En déduire le théorème général suivant : *)

Theorem foldr_id:
  forall A : Set, forall l : list A,
    foldr folder_id nil l = l.
Proof.
  intros A l.
  induction l as [|e l'].
    - simpl.
      reflexivity.

    -simpl.
     rewrite IHl'.
     reflexivity.     
Qed.


(*

  *** Question 2

En vous inspirant de l'exemple suivant  (à compléter) :

*)

Example folder_id_ex2:
 foldr folder_id (4::5::6::nil) (1::2::3::nil) = 1::2::3::4::5::6::nil.
Proof.
  compute.
  reflexivity.
Qed.


Theorem fold_concat:
  forall A : Set, forall l1 l2 : list A,
    foldr folder_id l2 l1 = concat l1 l2.
Proof.
  intros A l1 l2.
  induction l2 as [|e2' l2'].
    +rewrite concat_nil.
     rewrite foldr_id.
     reflexivity.
    +
Abort.


(*

  *** Question 3

Selon les mêmes principes, redéfinir la fonction [map] en utilisant [foldr].

Tester avec l'exemple correspondant à [map (fun n : nat => S n) (1::2::3::4::5::nil)].

Démontrer le théorème général reliant [map] et [foldr].

*)

Definition foldmap {A B :Set} (f:A -> B) (l:list A) : list B :=
foldr (fun (le :A) (les :(list B)) => (f le)::les) nil l.

Example foldmap_ex1:
foldmap (fun n : nat => S n) (1::2::3::4::5::nil) = (2::3::4::5::6::nil).
Proof.
compute.
reflexivity.
Qed.


(*

  *** Question 4

Mêmes questions pour la fonction [rev]

*)

Definition foldrev {A:Set} (l:list A) : list A :=
 foldr (fun (le :A) (les :(list A)) => concat les (le::nil)) nil l.

Example foldrev_ex1:
foldrev (1::2::3::4::5::nil) = (5::4::3::2::1::nil).
Proof.
compute.
reflexivity.
Qed.

(*

  ** Exercice : pliage à gauche (difficile)

La fonction de pliage à gauche est la suivante :

*)

Fixpoint foldl {A B :Set} (f:A -> B -> A) (u:A) (l:list B) : A :=
  match l with
    | nil => u
    | e::l' => foldl f (f u e) l'
  end.

(*

  *** Question 1

Définir une fonction _non-récursive_ [foldl'] de pliage à gauche à partir de [foldr].

*)

(* wrong def*)
Definition foldl' {A B :Set} (f:A -> B -> A) (u:A) (l:list B) : A :=
  foldr (fun (b:B)(g:A -> B)(x:A) =>  (g (f (x) (b)))) u l.

(* Démontrer le théorème suivant : *)

Theorem foldl'_foldl:
  forall A B : Set, forall f : A -> B -> A,
  forall l : list B, forall u : A,
    foldl f u l = foldl' f u l.
Proof.
  intros A B f l u.
  induction l as [|e l'].

  - compute.
    reflexivity.

  - simpl.
 unfold foldl' in IHl'.
    unfold foldl'.
    simpl.
    rewrite <- IHl'.
    fold.
Abort.


(*

  *** Question 2

Reconstruire les fonctions [id], [concat], [rev] et [map] avec
 [foldl] et [foldl'].

Démontrer les lemmes et théorèmes qui
semblent les plus pertinents. Alterner des preuves pour [foldl]
 et des preuves pour [foldl']   ainsi que des preuves
 exploitant le théorème [foldl'_foldl] ci-dessus.

*)

