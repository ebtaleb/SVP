
(**

----------------------------------------------

  Num anonymat : 6

  NOM:

  PRENOM:

  No Ano: 3264851

-----------------------------------------------

  * Spécification et Validation de Programmes - Examen Février 2016

Cet examen est un examen sur machine. 

_Durée_ : 3 heures

_Documents_ :  tous documents autorisés


L'objectif est de répondre directement dans ce fichier et de
soumettre ce dernier sur le site du master (cf. instructions données
lors de l'examen).   Repérez les mots  "QUESTION"  au fil du texte.

_Important_ : le temps de soumission est compris dans les 3 heures,
 toute soumission tardive est comptée comme copie vide.


Dans les réponses, les [admit]  ou [Admitted]  doivent etre effacés ou commentés sinon aucun point ne sera accordé à la question.   Le sujet est à priori à répondre dans l'ordre
 des questions mais il est possible de laisser un [admit] ou [Admitted] pour passer à la suite
 en supposant la réponse fournie.

La difficulté relative et ressentie par les enseignants pour chaque question est notée de
la façon suivante :

  [+]   question facile
  [++]  question non-triviale mais simple
  [+++] question demandant un peu plus de réflexion
  [++++] question difficile et/ou prenant du temps


Le sujet est composé de deux exercices:

  - exercice 1 : spécification et validation d'un programme de tri

  - exercice 2 : modélisation événementielle d'une file d'attente triée.

_Remarque_ : l'exercice 2 utilise les définitions de l'exercice 1
 et n'est donc pas indépendant. Cependant, on pourra passer à l'exercice
 2 avant de compléter l'exercice 1 en acceptant certains résultats.


*)

Require Import Bool.
Require Import Arith.
Require Import List.

(**

* Exercice 1 : du tri certifié ...

Dans cet exercice nous spécifions le principe des listes
 triées et développons un programme de tri certifié.

Voici une spécification inductive de la notion
de liste triée.

 *)

Inductive Sorted : list nat -> Prop :=
| sorted_nil: Sorted nil
| sorted_one: forall a : nat, Sorted (a::nil)
| sorted_cons:
    forall a b : nat, forall l : list nat,
      a <= b -> Sorted (b::l)
      -> Sorted (a::b::l).

(**

 ** QUESTION 1 [+]

Compléter les preuves des exemples suivant.

*)


Example Sorted_ex1:
  Sorted (1::2::3::4::5::nil).
Proof.
  repeat apply sorted_cons.
  SearchPattern ( _ <= _).
  apply le_S; reflexivity.
  auto.
  auto.
  auto.
  apply sorted_one.
Qed.

Example Sorted_ex2:
  not (Sorted (1::2::3::2::4::nil)).
Proof.
  unfold not.
  intros HF.
  assert (Sorted (1 :: 2 :: 3 :: 2 :: 4 :: nil) -> True).
  - intros HFF.
  inversion HF.
Admitted.

(**

  ** QUESTION 2 [+]

Compléter la définition de la fonction [fsorted]
 ci-dessous, de sorte que les deux tests
suivant passent.

 *)

Fixpoint fsorted (l:list nat) : bool :=
match l with
    | nil => true
    | x :: nil => true
    | x :: xs => match xs with
                   | nil => true
                   | y :: ys => if (leb x y) then fsorted xs else false
                 end
end.

Example fsorted_ex1:
  fsorted (1::2::3::4::5::nil) = true.
Proof.
  compute.
  reflexivity.
Qed.

Example fsorted_ex2:
  fsorted (1::2::3::2::4::nil)= false.
Proof.
 compute.
  reflexivity.
Qed.


(**

  * QUESTION 3 [++]

On se donne le lemme suivant (avec sa preuve
qui devrait passer en la décommentant...).

*)

Lemma fsorted_tail:
  forall a b : nat, forall l : list nat,
    leb a b && fsorted (b::l) = true
    -> fsorted (a::b::l) = true.
Proof.
  intros a b l H.
  induction l as [| c l'].
  - (* cas l=nil *)
    simpl.
    simpl in H.
    exact H.
  - (* cas l=c::l' *)
    simpl.
    case_eq (leb a b).
    + (* cas a <= b *)
      intro Htrue.
      rewrite Htrue in *.
      simpl in *.
      case_eq (leb b c).
      * (* cas b <= c *)
        intro Htrue'.
        rewrite Htrue' in *.
        simpl in *.
        { destruct l' as [|d l''].
          - (* cas l'=nil *)
            reflexivity.
          - (* cas l''=d l'' *)
            simpl.
            exact H.
        }
      * (* cas b > c *)
        intro Hfalse.
        rewrite Hfalse in *.
        simpl in *.
        inversion H.
    + (* cas a > b *)
      intro Hfalse.
      rewrite Hfalse in *.
      simpl in *.
      inversion H.
Qed.


(**

Montrer le Lemme suivant en suivant
 le principe d'induction des listes triées.

_Remarque_ : on pourra bien sûr utiliser le Lemme
précédent. On s'intéressera également à la conversion entre
les expressions (a <= b)   et  (leb a b = true).

*)

Lemma Sorted_fsorted:
  forall l : list nat,
    Sorted l -> fsorted l = true.
Proof.
  intros l H.
  induction H.
  +simpl.
   trivial.
  +simpl.
   trivial.
  + apply fsorted_tail.
    rewrite IHSorted.
    destruct (leb a b).
    *simpl.
     auto.
    *
     simpl.
     admit.
Qed.
(**

  ** QUESTION 4 [++] 

On se donne le Lemme complémentaire suivant :

*)

Lemma fsorted_Sorted:
  forall l : list nat,
    fsorted l = true -> Sorted l.
Proof.
  intros l H.
  induction l as [|a l'].
  - apply sorted_nil.
  - destruct l' as [|b l''].
    + apply sorted_one.
    + apply sorted_cons.
      * inversion H.
        Check andb_prop.
        apply andb_prop in H1.
        destruct H1 as [ H2 H3 ].
        SearchPattern ( leb _ _ = true -> _ <= _ ).
        apply leb_complete.
        exact H2.
      * apply IHl'.
        inversion H.
        apply andb_prop in H1.
        destruct H1 as [H2 H3].
        rewrite H2 in *.
        simpl.
        reflexivity.
Qed.


(**

Démontrer les deux lemmes ci-dessous.

*)

Lemma Sorted_tail_conv:
  forall n : nat, forall l : list nat,
    Sorted (n::l) -> Sorted l.
Proof.
  intros n l S.
  inversion S.
  constructor.
  exact H2.
Qed.
 
Lemma fsorted_tail_conv:
  forall n : nat, forall l : list nat,
    fsorted (n::l) = true -> fsorted l = true.
Proof.
  intros n l S.
  induction l as [|x l'].
  -simpl.
   auto.
  -rewrite <- IHl'.
   +apply fsorted_tail in S.
Admitted.

(**

  ** QUESTION 5 [+++]

On définit maintenant la notion de permutation.

*)

Fixpoint frequence (n:nat) (l:list nat) : nat :=
  match l with
    | nil => 0
    | m::l' => if beq_nat n m then S (frequence n (l'))
               else frequence n l'
  end.

Example frequence_ex:
  let l := (1::2::2::3::4::1::2::5::nil)
  in (frequence 3 l = 1)
     /\ (frequence 2 l = 3)
     /\ (frequence 6 l = 0).
Proof.
  compute ; repeat split ; reflexivity.
Qed.

Definition Permutation (l1 l2 : list nat) : Prop :=
  (length l1 = length l2) /\
  forall n : nat, frequence n l1 = frequence n l2.

Example Perm_ex1:
  Permutation (1::2::3::3::4::nil) (3::2::3::1::4::nil).
Proof.
  unfold Permutation.
  split.
  - simpl. reflexivity.
  - intro n.
    simpl.
    destruct (beq_nat n 1).
    + destruct (beq_nat n 2).
      * destruct (beq_nat n 3) ; reflexivity.
      * destruct (beq_nat n 3) ; reflexivity.
    + destruct (beq_nat n 2).
      * destruct (beq_nat n 3) ; reflexivity.
      * destruct (beq_nat n 3) ; reflexivity.
Qed.

(**

  Ainsi que le fait d'un algorithm de tri correct.

*)

Definition Correct_Sort (l1 l2 : list nat) : Prop :=
  Sorted l2 /\ Permutation l1 l2.


(**

On se donne la fonction [insert] ci-dessous effectuant
l'insertion d'un élément "à la bonne place" dans une liste
 [l]  déjà triée. Et compléter la preuve du Lemme [Sorted_insert]
 qui suit.

*)

Fixpoint insert (n:nat) (l:list nat) : list nat :=
  match l with
    | nil => n::nil
    | m::l' => if leb n m then n::m::l'
               else m::(insert n l')
  end.

Lemma Sorted_insert:
  forall l : list nat,
    Sorted l -> forall n : nat, Sorted (insert n l).
Proof.
  intros l H n.
  induction H.
  - simpl.
    apply sorted_one.
  - simpl.
    destruct (leb n a).
    + apply sorted_cons.
      * admit.
      * apply sorted_one.
    + apply sorted_cons.
      *admit.
      *apply sorted_one.
  - simpl.
    admit.
Qed.

(**

On en déduit le Lemme suivant :

*)

Lemma fsorted_insert:
  forall l : list nat,
    fsorted l = true -> forall n : nat, fsorted (insert n l) = true.
Proof.
  intros l H n.
  apply Sorted_fsorted.
  apply fsorted_Sorted in H.
  apply Sorted_insert ; assumption.
Qed.

(**

  ** QUESTION 6 [+++]

Démontrer le Lemme suivant :

*)

Lemma frequence_insert:
  forall n : nat, forall l : list nat,
    frequence n (insert n l) = S (frequence n l).
Proof.
  intros n l.
  induction l as [|x l'].
  -simpl.
   rewrite <- beq_nat_refl.
   reflexivity.
  - simpl.
   admit.
Qed.

(**

On se donne également le Lemme suivant.

*)

Lemma frequence_insert_neq:
  forall n m : nat, forall l : list nat,
    n<>m -> frequence m (insert n l) = frequence m l.
Proof.
  intros n m l.
  generalize m as p. clear m.
  induction l as [| m l'].
  - intros p Hneq.
    simpl.
    case_eq (beq_nat p n).
    + intro Htrue.
      SearchPattern (beq_nat _ _ = true -> _ = _ ).
      apply beq_nat_true in Htrue.
      apply eq_sym in Htrue.
      contradiction.
    + reflexivity.  
  - intros p H.
    simpl.
    case_eq (leb n m).
    + intro Heq.
      simpl.
      case_eq (beq_nat p n).
      * intro Htrue.
        apply beq_nat_true in Htrue.
        apply eq_sym in Htrue.
        contradiction.
      * intro Hfalse.
        reflexivity.
    + intro Hfalse.
      simpl.
      destruct (beq_nat p m).
      * apply eq_S.
        { rewrite IHl'.
          - reflexivity.
          - exact H.
        }
      * apply IHl'.
        exact H.
Qed.

(**

  ** QUESTION 7 [++]

Définir la fonction [tri_insert] de tri par insertion
 et démontrer le lemme [tri_insert_Sorted] ci-dessous.

*)

Fixpoint tri_insert (l:list nat) : list nat :=
  match l with
    | nil => nil
    | x :: xs => insert x (tri_insert xs)
  end.

Example tri_insert_ex:
  tri_insert (5::3::4::2::3::3::1::2::9::nil)
  = (1::2::2::3::3::3::4::5::9::nil).
Proof.
simpl. reflexivity.
Qed.

Lemma tri_insert_Sorted:
  forall l : list nat,
    Sorted (tri_insert l).
Proof.
  intro l.
  induction l as [|x l'].
  -simpl.
   apply sorted_nil.
  -simpl.
   apply Sorted_insert.
   exact IHl'.
Qed.
(**

** QUESTION 8 [+++]

Démontrer le lemme suivant :

*)

Lemma tri_insert_frequence:
  forall n : nat, forall l : list nat,
    frequence n (tri_insert l) = frequence n l.
Proof.
  intros n l.
  induction l as [|x l'].
  - simpl.
    reflexivity.
  -simpl.
   destruct (beq_nat n x).
   +rewrite <- IHl'.
    rewrite <- frequence_insert.
    admit.
   + inversion IHl'.
     admit.
Qed.  


(**

** QUESTION 9 [+++]

Prouver que l'implémentation du tri par insertion
 est correcte (Théorème [tri_insert_correct]).

_Remarque_ : il faudra sans doute définir quelques
 lemmes utilitaires.

*)

Theorem tri_insert_correct:
  forall l : list nat,
    Correct_Sort l (tri_insert l).
Proof.
  (* A COMPLETER *)
Admitted.


(* ------------------------------------------------------------------------ *)

(**

  * Exercice 2 : modélisation événementielle d'une file d'attente triée.

On se donne la machine abstraite suivante :

 *)

Module AbstractQueue.

Record State : Set :=
  mkState {
      queue : list nat
    }.

Definition Inv_1 (st:State) : Prop :=
  Sorted st.(queue).

Module Init.

Definition action : State := mkState nil.

Theorem PO_Safety:
  Inv_1 (action).
Proof.
  unfold Inv_1.
  simpl.
  apply sorted_nil.
Qed.

End Init.

Module Push.

Definition action_Prop_1 (n:nat) (st st' : State) : Prop :=
  Permutation st'.(queue) (n::(st.(queue))).

Definition action_Prop_2 (n:nat) (st st' : State) : Prop :=
  Sorted st'.(queue).

(** QUESTION 1 [++]

Compléter la définition et la preuve de l'obligation de preuve suivante.

*)

Theorem PO_Safety:
  forall n : nat, forall st st' : State,  (* True. *)
    Inv_1 st -> action_Prop_1 n st st' -> action_Prop_2 n st st'
    -> Inv_1 st'.
Proof.
  intros n st st'.
  unfold Inv_1.
  unfold action_Prop_1.
  unfold action_Prop_2.
  intros I1 P S.
  induction (queue st') as [|x xs].
  +exact S.
  +exact S.
Qed.

End Push.

(** On complète la machine. *)

Module Pull.

Definition Guard (st:State) : Prop :=
  st.(queue) <> nil.

Definition action_Prop_1 (st st' : State) : Prop :=
  S (length st'.(queue)) = length st.(queue).

Definition action_Prop_2 (st st' : State) : Prop :=
  Sorted st'.(queue).

Theorem PO_Safety:
  forall st st' : State,
    Inv_1 st -> Guard st
    -> action_Prop_1 st st' -> action_Prop_2 st st'
    -> Inv_1 st'.
Proof.
  intros st st' HInv_1 HGuard HProp1 HProp2.
  unfold Inv_1 in *.
  unfold action_Prop_2 in *.
  exact HProp2.
Qed.

End Pull.


End AbstractQueue.

(** QUESTION 2 [++]

Compléter la machine concrète [ConcreteQueue] ci-dessous en utilisant [insert]   (insertion triée)
 pour l'événement [Push],  le plus petit élément pour l'événement
 [Pull].

Définir et prouver toutes les obligations de preuves nécessaires
 pour démontrer que le raffinement est correct.

Remarque : dans cette partie, il sera plus important d'énoncer les lemmes auxiliaires nécessaires que de les prouver en détail. On les admettra donc et on terminera les preuves si le temps le permet.

 *)


Module ConcreteQueue.


Record State : Set :=
  mkState {
      queue : list nat
    }.


Definition Glue_Inv_1 (st:State) (ast:AbstractQueue.State) : Prop :=
  Permutation st.(queue) (AbstractQueue.queue ast).

Definition Inv_1 (st:State) : Prop :=
  Sorted st.(queue).

Module Init.

Definition action : State := mkState nil.

Theorem PO_Safety:
  Inv_1 (action).
Proof.
  unfold Inv_1.
  simpl.
  apply sorted_nil.
Qed.

Theorem PO_Simulation:
    let st := action in
    let ast := AbstractQueue.Init.action in
    Glue_Inv_1 st ast.
Proof.
  unfold AbstractQueue.Init.action.
  unfold action.
  unfold Glue_Inv_1.
  unfold Permutation.
  induction queue as [|e q'].
  *simpl.
   auto.
  * simpl.
    split.
Admitted.

End Init.

Module Push.

Definition action (n:nat) (st:State) : State :=
  mkState (insert n (st.(queue))).


Theorem PO_Safety:
  forall st : State,
    Inv_1 st
    -> forall n : nat,
         let st' := action n st in
         Inv_1 st'.
Proof.
  intros st.
  unfold Inv_1.
  unfold action.
  intros S n.
  simpl.
  apply Sorted_insert.
  exact S.
Qed.

(**  ** QUESTION 3 [++++]

Compléter la preuve ci-dessous.

_Remarque_ : il faut un certain nombre de lemmes intermédiaires
concernant Permutation : réflexivité, symmétrie, transitivité,
 comportement vis-à-vis de insert et cons (e::l)...

 *)

Theorem PO_Simulation:
  forall st : State, forall ast : AbstractQueue.State,
    AbstractQueue.Inv_1 ast
    -> Inv_1 st
    -> Glue_Inv_1 st ast
    -> forall n : nat, forall ast' : AbstractQueue.State,
         AbstractQueue.Push.action_Prop_1 n ast ast'
         -> AbstractQueue.Push.action_Prop_2 n ast ast'
         -> let st' := action n st in
            Glue_Inv_1 st' ast'.
Proof.
  (* A COMPLETER *)
Admitted.

End Push.

Module Pull.

(**  QUESTION 4 [+++]

Donner les spécifications et les obligationres de l'événement [Pull].

*)
  
End Pull.

End ConcreteQueue.

(** QUESTION 5 [+++]

Modifier la machine concrète pour garantir la _convergence_
 de l'événement [Pull].

*)

(** QUESTION 6 [+++]

Démontrer l'obligation de preuve _Deadlock freedom_  sur
la machine concrète.

 *)


