
(**

  * Spécification et Validation de Programmes - Examen Février 2015

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

*)

Require Import Bool.
Require Import Arith.

(**

* Les Ensembles finis en Coq.

L'objectif de cet examen est de proposer une formalisation de la notion d'ensemble fini (typé) dans le logiciel Coq.

*)

Section Ensembles.

Variable Elem : Set.  (*  le type générique des éléménts des ensembles. *)

(**

* (1) Egalité sur les éléments

La notion d'ensemble est dépendante de la notion d'égalité sur
leurs éléménts. On fera donc l'hypothèse que l'égalité sur les éléments des ensembles est décidable.

*)

Hypothesis Elem_eq_dec: forall a b : Elem, { a = b } + { a <> b }.

(**

Voici quelques définitions et lemmes importants sur cette égalité entre éléments.

*)

Definition elem_eq (a b : Elem) : bool :=
  match Elem_eq_dec a b with
    | left _ => true
    | right _ => false
  end.

Proposition elem_eq_eq:
  forall a b : Elem,
    elem_eq a b = true -> a = b.
Proof.
  intros a b H.
  unfold elem_eq in H.
  destruct (Elem_eq_dec a b) as [Heq | Hneq].
  + (* cas a = b *)
    exact Heq.
  + (* cas a <> b *)
    inversion H. (* contradiction *)
Qed.

(**

 ** QUESTION 1.1 [+] : réflexivité de l'égalité

Complétez la preuve du lemme suivant :

*)

Lemma elem_eq_refl:
  forall a : Elem, elem_eq a a = true.
Proof.
  intro a.
  unfold elem_eq.
  destruct (Elem_eq_dec a a) as [Heq | Hneq].
  + (* cas a = a *)
    reflexivity.
  + (* cas a <> a *)
    unfold not in Hneq.
    assert (HFalse: False).
    {
      apply Hneq.
      reflexivity.
    }    
    elim HFalse.
Qed.    

(**

 ** QUESTION 1.2 [+]

En déduire une démonstration pour la proposition suivante :
    
*)

Proposition eq_elem_eq:
  forall a b : Elem,
    a = b -> elem_eq a b = true.
Proof.
  intros a b H.
  subst.
  rewrite elem_eq_refl.
  reflexivity.
Qed.

(**

On se donne des propositions complémentaires pour la négation.

*)

Proposition neq_elem_neq:
  forall a b : Elem,
    a <> b -> elem_eq a b = false.
Proof.
  intros a b Hneq.
  case_eq (elem_eq a b).
  - (* cas Htrue *)
    intro Htrue.
    assert (Heq: a = b). 
    { apply elem_eq_eq.
      exact Htrue.
    }
    contradiction.
  - (* cas Hfalse *)
    reflexivity.
Qed.


Proposition elem_neq_neq:
  forall a b : Elem,
    elem_eq a b = false -> a <> b.
Proof.
  intros a b Hfalse.
  unfold not.
  intro Heq.
  rewrite Heq in Hfalse.
  rewrite elem_eq_refl in Hfalse.
  inversion Hfalse.
Qed.

(** 

 *  (2) Définition d'ensemble et appartenance

La notion d'ensemble fini proposée est assez naive et définie par
le type suivant.

*)

Inductive Ens : Set :=
| vide : Ens
| elem : Elem -> Ens -> Ens.

(**

On souhaite définir la notion d'appartenance à un ensemble, basée
 sur la définition précédente.

 ** QUESTION 2.1 [+] : appartenance fonctionnelle

La première définition d'appartenance est un prédicat booléen fonctionnel.

Complétez la définition suivante :

*)

Fixpoint appartient (a:Elem) (E:Ens) : bool :=
  match E with
    | vide => false
    | elem e ES => if elem_eq a e then true else appartient a ES
  end.


(**

  ** QUESTION 2.2 [+] : propriété de l'appartenance

Démontrer la propriété suivante (par cas):

*)

Proposition appartient_elem:
  forall a b : Elem, forall E : Ens,
      appartient a E = true -> appartient a (elem b E) = true.
Proof.
  intros a b E H.
  simpl.
  destruct (elem_eq a b).
  +reflexivity.
  +exact H.
   Qed.
(**
 

On donne maintenant une définition alternative à l'aide
d'un type inductif de nom  Appartient   (avec A majuscule)
et implémentant les règles suivantes :

 - règle : app_debut    

    ---------------------------
      Appartient a (elem a E)

 - règle : app_reste

      Appartient a E
    --------------------------
      Appartient a (elem b E)

*)

Inductive Appartient : Elem -> Ens -> Prop :=
| app_debut: forall E : Ens, forall a : Elem, Appartient a (elem a E)
| app_reste: forall E : Ens, forall a b : Elem, Appartient a E 
                                                -> Appartient a (elem b E).

(**  

  ** QUESTION 2.3 [+]

 Montrer la proposition suivante :

*)

Proposition Appartient_elem:
  forall a b : Elem, forall E : Ens,
      Appartient a E -> Appartient a (elem b E).
Proof.
  intros a b E H.
  apply app_reste.
  exact H.
Qed.

(**

  ** QUESTION 2.4 [+++] : Du récursif à l'inductif

Montrer par induction le lemme suivant :

*)

Lemma appartient_Appartient:
  forall a : Elem, forall E : Ens,
      appartient a E = true -> Appartient a E.
Proof.
  intros a E.
  intros H.
  induction E as [|v ee].
  +inversion H.
  +apply Appartient_elem.
   apply IHee.
   inversion H.
   destruct (elem_eq a v).
  -destruct ee.
   *simpl.
    simpl in H.

Admitted.

(**

  ** QUESTION 2.5 [++] : De l'inductif au récursif 

Montrer par induction sur le type inductif Appartient 
le lemme suivant :


*)

Lemma Appartient_appartient:
  forall a : Elem, forall E : Ens,
      Appartient a E -> appartient a E = true.
Proof.
  intros a E.
  intros H.
  induction E as [|v ee].
  + inversion H.
  + apply appartient_elem.
    destruct (appartient a ee).
    *trivial.
    *simpl.
Admitted.

(**

 ** QUESTION 2.6 [++]

En utilisant les deux lemmes précédents, déduire de la proposition Appartient_elem (avec A majuscule) une preuve alternative de la proposition appartient_elem  (avec a minuscule).

*)

Proposition appartient_elem':
  forall a b : Elem, forall E : Ens,
      appartient a E = true -> appartient a (elem b E) = true.
Proof.
  intros a b E.
  rewrite Appartient_appartient.
  + intros HT.
    rewrite Appartient_appartient.
    exact HT.
    apply Appartient_elem.
    apply appartient_Appartient.
    simpl.
Admitted. (* <== REMPLACER le Admitted. *)

(**

  * (3)  Union ensembliste

Dans cette partie nous nous intéressons à l'opérateur d'union ensembliste.

Nous donnons la définition fonctionnelle suivante :

*)

Fixpoint union (E F : Ens) : Ens :=
  match E with
    | vide => F
    | elem a E' => elem a (union E' F)
  end.

(**

  ** QUESTION 3.1 [++]

Démontrer le lemme suivant :

*)

Lemma union_Appartient_l:
  forall a : Elem, forall E F : Ens,
      Appartient a E -> Appartient a (union E F).
Proof.
  intros a E F.
  intros H.
  induction E as [|e ee].
  +simpl.
   inversion H.
  +simpl.
   apply Appartient_elem.
   destruct (union ee F).
  -apply IHee.
   inversion H.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

Le lemme complémentaire : union_Appartient_r

qui permet de déduire :

    Appartient a (union E F)

à partir de 

    Appartient a F

est plus difficile à démontrer, car l'union effectue la récursion
sur E et non sur F.

Nous passons en mode "calcul"  (en utilisant la définition fonctionnelle
 de appartient) et nous procédons par étapes.

*)

(**

  ** Question 3.2 [++]

Démontrer le lemme suivant par induction sur E :

*)

Proposition union_appartient_elem_r_eq:
  forall a b : Elem, forall E F : Ens,
      a = b 
      -> appartient a (union E (elem b F)) = true.
Proof.
  intros a b E F.
  intros H.
  induction E as [|e E'].
  - apply appartient_elem.
    destruct F.
    +simpl.
     admit.
    +apply appartient_elem.
     admit.
  -simpl.
   rewrite IHE'.
   destruct (elem_eq a e).
   +trivial.
   +trivial.
Qed.

(**

  ** Question 3.3 [++]

Démontrer le lemme suivant par induction sur E :

*)

Proposition union_appartient_elem_r:
  forall a b : Elem, forall E F : Ens,
      appartient a (union E F) = true
      -> appartient a (union E (elem b F)) = true.
Proof.
  intros a b E F H.
  induction E as [|e E'].
  +apply appartient_elem.
   simpl.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

  ** QUESTION 3.4 [+++]

En utilisant les deux propositions précédentes, démontrer
par induction sur F la proposition suivante :

*)

Proposition union_appartient_r:
  forall a : Elem, forall E F : Ens,
      appartient a F = true -> appartient a (union E F) = true.
Proof.
  intros a E F.
  induction F as [|f F'].
  +intros H.
   inversion H.
   +
Admitted. (* <== REMPLACER LE Admitted. *)

(** 

  ** QUESTION 3.5 [++]

En déduire le lemme suivant :

*)

Lemma union_Appartient_r:
  forall a : Elem, forall E F : Ens,
      Appartient a F -> Appartient a (union E F).
Proof.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

  ** QUESTION 3.6 [++]

Finalement, en déduire le théorème de l'union :

*)

Theorem union_Appartient:
  forall a : Elem, forall E F : Ens,
      Appartient a E \/ Appartient a F
      -> Appartient a (union E F).
Proof.
Admitted. (* <== REMPLACER LE Admitted. *) 

(**

  * (4) Elimination des doublons

Dans cette partie, nous souhaitons éliminer les éléments doublons
dans les ensembles.

*)

(**

  ** QUESTION 4.1 [+]

Définir la fonction retirer telle que (retirer a E)
 élimine toutes les occurrences de l'élément a dans l'ensemble E.

*)

Fixpoint retirer (a : Elem) (E : Ens) : Ens :=
  vide.  (* <== REMPLACER vide PAR UNE DEFINITION RECURSIVE. *)

(**

  ** QUESTION 4.2 [++]

Prouver le lemme suivant :

*)

Lemma retirer_present:
  forall a : Elem, forall E : Ens,
      appartient a (retirer a E) = false.
Proof.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

  ** QUESTION 4.3 [++]

Démontrer le lemme suivant :

*)

Lemma Appartient_retirer_elem:
  forall a b : Elem, forall E : Ens,
      b <> a -> Appartient a E ->  Appartient a (retirer b E).
Proof.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

  ** QUESTION 4.4 [+]

Donner une définition de la fonction sans_doublons
telle que (sans_doublons E) retire tous les éléments répétés
 dans E.

*)

Fixpoint sans_doublons (E : Ens) : Ens :=
  vide.  (* <== REMPLACER vide PAR UNE DEFINITION RECURSIVE. *)

  
(**

  ** QUESTION 4.5 [+++]

En déduire le théorème suivant :

*)

Theorem Appartient_sans_doublons:
  forall a : Elem, forall E : Ens,
      Appartient a E -> Appartient a (sans_doublons E).
Proof.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

  * (5) Différence ensembliste

Dans cette dernière partie on souhaite formaliser l'opérateur de
 différence ensembliste.

*)

(**

  ** Question 5.1 [++]

Définir la fonction difference retournant la
différence entre deux ensembles.

*)

Fixpoint difference (E1 : Ens) (E2 : Ens) : Ens :=
  vide.  (* <== REMPLACER vide PAR UNE DEFINITION RECURSIVE. *)

(**

Notre objectif est de montrer le théorème suivant :

Theorem difference_Appartient:
  forall e : Elem, forall E2 E1 : Ens,
      Appartient e E2
      -> ~ (Appartient e (difference E1 E2)).


Cependant, la preuve est non-triviale et nous allons
réaliser les étapes nécessaires en passant à la fonction
 de calcul appartient (avec a minuscule).

*)

(**

 ** Question 5.2 [+++]

Compléter la preuve du Lemme suivant :

*)

Lemma nappartient_retirer_elem:
  forall a b : Elem, forall E : Ens,
      b <> a -> appartient a E = false ->  appartient a (retirer b E) = false.
Proof.
Admitted. (* <== RETIRER LE Admitted. *)
  (*  <=== DECOMMENTER SINON CELA NE PASSE PAS 
  intros a b E Hneq Happ.
  induction E as [|e E'].
  - (* cas E = vide *)
    simpl.
    reflexivity.
  - (* cas E = (elem e E') *)
    simpl.
    case_eq (elem_eq b e).
    + (* cas b = e vrai *)
      intro Htrue.
      apply IHE'.
      admit. (* <== REMPLACER LE admit *)
      (* etc ... *) 
    + (* cas b = e faux *)
      intro Hfalse.
      admit. (* <== REMPLACER LE admit *)
      (* etc ... *)
Qed. DECOMMENTER ===> *)

(**

 ** Question 5.3 [+++]

Compléter la preuve du Lemme suivant :

*)

Lemma difference_appartient_aux:
  forall e : Elem, forall E2 E1: Ens,
      appartient e E1 = false
      -> appartient e (difference E1 E2) = false.
Proof.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

 ** Question 5.4 [+++]

En déduire le lemme ci-dessous :

*)

Lemma difference_appartient:
  forall e : Elem, forall E2 E1 : Ens,
    appartient e E2 = true
    -> appartient e (difference E1 E2) = false.
Proof.
Admitted. (* <== REMPLACER LE Admitted. *)

(**

  ** Question 5.5 [++]

En déduire notre théorème principal.

*)

Theorem difference_Appartient:
  forall e : Elem, forall E2 E1 : Ens,
      Appartient e E2
      -> ~ (Appartient e (difference E1 E2)).
Proof.
Admitted. (* <== REMPLACER LE Admitted *)
  
(**

  * (6) Intersection (réponse libre)  [+++]

Dans cette dernière partie on souhaite formaliser l'opérateur
 d'intersection entre deux ensembles.

En vous inspirant de la partie (3), proposer une formalisation
permettant finalement de démontrer le théorème suivant :

*)

(* A DECOMMENTER  ==>

Theorem intersection_Appartient:
  forall a : Elem, forall E F : Ens,
      Appartient a E /\ Appartient a F
      -> Appartient a (intersection E F).

*)

