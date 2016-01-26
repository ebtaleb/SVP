
(* Script Coq pour le Thème 7 : types inductifs *)

Require Import Arith.
Require Import List.

(*---------------------------------------------------------------*)
(** * Types énumérés *)

Print bool.

Inductive Couleur : Set :=
 | pique : Couleur
 | coeur : Couleur
 | carreau : Couleur
 | trefle : Couleur.

Fixpoint valeur_couleur (c:Couleur) : nat :=
  match c with
  | pique => 1
  | coeur => 2
  | carreau => 3
  | trefle => 4
  end.

Example ex_valeur_couleur1: valeur_couleur coeur = 2.
Proof.
  compute. reflexivity.
Qed.

Check Couleur_ind.

Lemma couleur_surj: 
  forall c : Couleur,
    c = pique \/ c = coeur \/ c = carreau \/ c = trefle.
Proof.
  destruct c. (* essayer aussi avec induction c *)
  - (* cas pique *)
    left.
    reflexivity.
  - (* cas coeur *)
    right.
    left.
    reflexivity.
  - (* cas carreau *)
    right. right.
    left.
    reflexivity.
  - (* cas trefle *)
    right. right. right.
    reflexivity.
Qed.

(** ** Exercice *)

Lemma borne_valeur:
  forall c : Couleur,
    (0 < (valeur_couleur c)) /\ ((valeur_couleur c) <= 4).
Proof.
  destruct c.
  - simpl.
   split.
   SearchPattern ( 0 < _ ).
   apply lt_0_Sn.
   SearchPattern ( _ <= _ ).
   apply le_n_S.
   SearchPattern ( 0 <= _ ).
   apply le_0_n.
  -simpl; auto with arith.
  -simpl; auto with arith.
  -simpl; auto with arith.
Qed.

(*---------------------------------------------------------------*)
(** * Types paramétrés *)

Inductive geom : Set :=
  | point: nat -> nat -> geom
  | segment: nat -> nat -> nat -> nat -> geom
  | triangle: nat -> nat -> nat -> nat -> nat -> nat -> geom
  | nogeom : geom.

Fixpoint compose_geom (g1 g2:geom) : geom := 
  match g1 with
  | point x1 y1 => match g2 with
                   | point x2 y2 => segment x1 y1 x2 y2
                   | segment x2 y2 x3 y3 => triangle x1 y1 x2 y2 x3 y3
                   | _ => nogeom
                   end
  | segment x1 y1 x2 y2 => match g2 with
                   | point x3 y3 => triangle x1 y1 x2 y2 x3 y3
                   | _ => nogeom
                   end
  | _ => nogeom
  end.

Example ex_segment: compose_geom (point 0 0) (point 1 1) =
  segment 0 0 1 1.
Proof.
  compute. reflexivity.
Qed.

Check geom_ind.

(** ** Exercice *)

Lemma compose_nogeom: 
  forall g : geom, compose_geom nogeom g = nogeom.
Proof.
  intro geom.
simpl.
reflexivity.
Qed.
(*---------------------------------------------------------------*)
(** * Types polymorphes *)

Inductive maybe (A:Set) : Type :=
  Nothing : maybe A
| Just : A -> maybe A.

Arguments Nothing [A].
Arguments Just [A] _.

Check maybe_ind.

Definition maybe_map {A B:Set} (f:A->B) : maybe A -> maybe B :=
  fun (ma:maybe A) => match ma with
                        | Nothing => Nothing
                        | Just a => Just (f a)
                      end.

Lemma maybe_map_id:
  forall A : Set, forall ma : maybe A,
    maybe_map (fun a:A => a) ma = (fun (ma:maybe A) => ma) ma.
Proof.
  intros A ma.
  unfold maybe_map.
  destruct ma as [|a].
  reflexivity.
  reflexivity.
Qed.

(** ** Exercice *)

Definition maybe_compose {A B C : Set} (f:A->B) (g:B->C) : A->C :=
  fun (a:A) => g (f a).

Lemma maybe_map_compose:
  forall A B C : Set, forall ma : maybe A,
  forall f : A->B, forall g: B->C,
    maybe_map (maybe_compose f g) ma 
    = (maybe_compose (maybe_map f) (maybe_map g)) ma.
Proof.
  intros A B C ma f g.
  compute.
  destruct ma as [|a].
  reflexivity.
  reflexivity.
Qed.
  (*---------------------------------------------------------------*)
(** * Types récursifs simples *)

Check nat_ind.

Inductive list_Couleur : Set :=
  | Nil_Couleur: list_Couleur
  | Cons_Couleur: Couleur -> list_Couleur -> list_Couleur.

(* Ecrire ci-dessous le principe d'induction. *)

(*list_Couleur_ind : forall P : list_Couleur -> Prop,
                     P Nil_Couleur ->
                     (forall (c:Couleur l:list_Couleur), P l -> (Cons_Couleur c l)) ->
                     forall l : list_Couleur, P l. 
*)
(* Et pour vérifier votre solution ... *)
Check list_Couleur_ind.

(** ** Exercice *)

Fixpoint meme_couleur (c : Couleur) (l : list_Couleur) : Prop :=
  match l with
    | Nil_Couleur => True
    | Cons_Couleur e l' => (e = c) /\ meme_couleur c l'
  end.

Fixpoint somme_couleurs (l : list_Couleur) : nat :=
  match l with
    | Nil_Couleur => 0
    | Cons_Couleur e l' => (valeur_couleur e) + (somme_couleurs l')
  end.

Fixpoint longueur (l : list_Couleur) : nat :=
  match l with
    | Nil_Couleur => 0
    | Cons_Couleur _ l' => S (longueur l')
  end.

Lemma couleur_unique:
  forall c : Couleur, forall l : list_Couleur,
    meme_couleur c l
    -> (somme_couleurs l) = (longueur l) * (valeur_couleur c).
Proof.
  intros c l.
  induction l as [|c' cl'].
    - simpl.
      intro.
      reflexivity.
    - simpl.
      intros cc.
      destruct cc as [H1 H2].
      rewrite H1.
      rewrite IHcl'.
      + reflexivity.
      + exact H2. 
Qed.
(*---------------------------------------------------------------*)
(** * Types récursifs polymorphes *)

Print list.

Check list_ind.

(** ** Exercice *)

(** *** Question 1 *)
Inductive bintree (A:Set) : Set :=
leaf : bintree A
| node : A -> bintree A -> bintree A -> bintree A.

Arguments leaf [A].
Arguments node [A] _ _ _.


Check bintree_ind.
            

(** *** Question 2 *)

Fixpoint nsize {A:Set} (t : bintree A) : nat :=
  match t with
    | leaf => 0
    | node _ g d => 1 + nsize g + nsize d
  end.

          
Definition bintree_ex1 : bintree nat :=
  (node 1 
        (node 2 
              (node 3 leaf leaf)
              (node 4 
                    (node 5 leaf leaf)
                    (node 6 leaf (node 7 leaf leaf))))
        (node 8
              (node 9 leaf leaf)
              leaf)).


Example nsize_ex1: 
  nsize bintree_ex1 = 9.
Proof.
  compute. reflexivity.
Qed.          

(** *** Question 3 *)

Fixpoint lsize {A:Set} (t : bintree A) : nat :=
  match t with
    | leaf => 1
    | node _ g d => lsize g + lsize d
  end.

Example lsize_ex1:
  lsize bintree_ex1 = 10.
Proof.
  compute. reflexivity.
Qed.

Lemma node_leaf_size:
  forall A : Set, forall t : bintree A,
    (lsize t) = S (nsize t).
Proof.
  intros A t.
  induction t as [| g d].
  + simpl.
    reflexivity.
  +simpl.
   rewrite IHd.
   rewrite IHt1.
   SearchRewrite( S (_)).
   simpl.
   rewrite <- plus_n_Sm.
   reflexivity.
Qed.
(** ** Exercice *)

(** *** Question 1 *)
  
Fixpoint lprefix {A: Set} (t : bintree A) : list A :=
  match t with
    | leaf => nil
    | node a g d => ((a :: (lprefix g)) ++ lprefix d)
                      end.

Example lprefix_ex1:
  lprefix bintree_ex1 = 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil.
Proof.
  compute. reflexivity.
Qed.

(** *** Question 2 *)

Lemma nsize_length: 
  forall A : Set, forall t : bintree A,
    nsize t = length (lprefix t).
Proof.
  intros A t.
  induction t as [| l n].
  -simpl.
   reflexivity.
  -simpl.
   rewrite IHn.
   rewrite IHt1.
   SearchRewrite ( length _ ).
   rewrite app_length.
   reflexivity.
Qed.

(** ** Exercice *)

(** *** Question 1 *)
  
Fixpoint bmap {A B: Set} (f : A -> B) (t : bintree A) : bintree B :=
  match t with
    | leaf => leaf
    | node a g d => node (f a) (bmap f g) (bmap f d)
  end.

Example bmap_ex1:
  bmap (fun (n:nat) =>  n + n) bintree_ex1
  = node 2
         (node 4
               (node 6 leaf leaf)
               (node 8
                     (node 10 leaf leaf)
                     (node 12 leaf (node 14 leaf leaf))))
         (node 16 (node 18 leaf leaf) leaf).
Proof.
  compute. reflexivity.
Qed.

(** *** Question 2 *)

Lemma map_bmap:
  forall A B : Set, 
  forall f : A->B, forall t : bintree A,
    lprefix (bmap f t) = map f (lprefix t).
Proof.
  intros A B f t.
  induction t as [| l n].
  -simpl.
   reflexivity.
  -simpl.
   rewrite IHn.
   rewrite IHt1.
   SearchRewrite( _ ++ _ ).
   rewrite map_app.
   reflexivity.
Qed.
(*---------------------------------------------------------------*)
(** * Récursion mutuelle *)

Inductive gentree (A:Set) : Set :=
| gnode: A -> forest A -> gentree A
with forest (A:Set) : Set :=
| fnil: forest A
| fcons: gentree A -> forest A -> forest A.

Arguments gnode [A] _ _.
Arguments fnil [A].
Arguments fcons [A] _ _.

Check gentree_ind.

Check forest_ind.

Fixpoint gsize {A:Set} (t:gentree A) : nat :=
  match t with
    | gnode _ f => S (fsize f)
  end
with fsize {A:Set} (f:forest A) : nat :=
       match f with
         | fnil => 0
         | fcons e f' => (gsize e) + (fsize f')
       end.

Fixpoint lgprefix {A:Set} (t:gentree A) : list A :=
  match t with
    | gnode e f => e::(lfprefix f)
  end
with lfprefix {A:Set} (f:forest A) : list A :=
    match f with
      | fnil => nil
      | fcons e f' => (lgprefix e) ++ (lfprefix f')
    end.

Lemma gsize_length:
  forall A : Set, forall t : gentree A,
    gsize t = length (lgprefix t).
Proof.
  intros A t.
  induction t.
  simpl.
Abort.

Scheme gentree_ind' :=
  Induction for gentree Sort Prop
  with forest_ind' :=
    Induction for forest Sort Prop.

Check gentree_ind'.

Lemma gsize_length:
  forall A : Set, forall t : gentree A,
    gsize t = length (lgprefix t).
Proof.
  intros A t.
  elim t using gentree_ind' with 
  (P0:= fun f:forest A => fsize f = length (lfprefix f)).
  - (* cas des noeuds *)
    intros a f H1.
    simpl.
    rewrite H1.
    reflexivity.
  - (* cas des forêts vides *)
    simpl.
    reflexivity.
  - (* cas des forêts non-vides *)
    intros g Hg f Hf.
    simpl.
    rewrite Hg.
    rewrite Hf.
    (* SearchRewrite (length (_ ++ _))
       app_length:
         forall (A : Type) (l l' : list A), 
             length (l ++ l') = length l + length l' *)
    rewrite app_length.
    reflexivity.
Qed.

(** ** Exercice *)

(** *** Question 1 *)

Fixpoint gmap {A B:Set} (fn : A -> B) (t:gentree A) : gentree B :=
  match t with
    | gnode e f => gnode (fn e) (fmap fn f)
  end
with fmap {A B:Set} (fn : A -> B) (f:forest A) : forest B :=
    match f with
      | fnil => fnil
      | fcons e f' => fcons (gmap fn e) (fmap fn f')
    end.

(** *** Question 2 *)

Lemma map_gmap:
  forall A B : Set, 
  forall h : A->B, forall t : gentree A,
    lgprefix (gmap h t) = map h (lgprefix t).
Proof.
  intros A B h t.
  elim t using gentree_ind' with 
  (P0:= fun f : forest A => lfprefix (fmap h f) = map h (lfprefix f)).
  -intros a f H1.
   simpl.
   rewrite H1.
   reflexivity.
  -simpl.
   reflexivity.
  -intros g Hg f Hf.
   simpl.
   rewrite Hg.
   rewrite Hf.
   SearchRewrite(map _ (_ ++ _)).
   rewrite map_app.
   reflexivity.
Qed.


(*---------------------------------------------------------------*)
(** * Types dépendants *)

Inductive domino : nat -> nat -> Type :=
  | block: forall m n, domino m n 
  | chain: forall m n p, domino m n -> domino n p -> domino m p.

Arguments chain [m n p] _ _.

Eval compute in (chain (chain (block 3 8) (block 8 4)) (block 4 9)).

Inductive vector (A:Set) : nat -> Set :=
  | vNil : vector A O
  | vCons : forall n, A -> vector A n -> vector A (S n).

Arguments vNil [A].
Arguments vCons [A][n] _ _.

Check vector_ind.

Fixpoint vapp {A:Set} {n1:nat} (v1:vector A n1) {n2:nat} (v2:vector A n2) : vector A (n1 + n2) :=
  match v1 in (vector _ n1) return (vector A (n1 + n2)) with
    | vNil => v2
    | vCons _ e v1' => vCons e (vapp v1' v2)
  end.

Example vapp_ex1:
  vapp (vCons 1 (vCons 2 (vCons 3 vNil)))
       (vCons 4 (vCons 5 vNil))
  = vCons 1 (vCons 2 (vCons 3 (vCons 4 (vCons 5 vNil)))).
Proof.
  compute.
  reflexivity.
Qed.

Definition vlength {A:Set} {n:nat} (v:vector A n) : nat := n.


(** ** Exercice *)

Lemma vappa_vlength:
  forall A : Set,
  forall n1 n2 : nat,
  forall v1 : vector A n1,
  forall v2 : vector A n2,
    vlength (vapp v1 v2) = n1 + n2.
Proof.
  intros A n1 n2 v1 v2.
  induction v1 as [|v v'].
  -compute.
   reflexivity.
  -simpl.
   rewrite <- IHv1.

(** ** Exercice *)

(* <<DEFINIR vmap ICI>> *)

Example vmap_ex1:
  vmap (fun b:bool => match b with
                        | true => 1
                        | false => 0
                      end) (vCons true (vCons false vNil))
  = vCons 1 (vCons 0 vNil).
Proof.
  compute. reflexivity.
Qed. 


(** ** Exercice *)

(* <<DEFINIR list_from_vect ICI>>> *)

Example list_from_vect_ex1:
  list_from_vect (vCons true (vCons false vNil)) = true :: false :: nil.
Proof.
  compute. reflexivity.
Qed.

(** ** Exercice *)

Lemma vmap_map:
  forall A B:Set,
  forall f : A->B,
  forall n:nat,
  forall v : vector A n,
    list_from_vect (vmap f v) = map f (list_from_vect v).
Proof.
  (* <<COMPLETER ICI>> *)

(** ** Exercice *)

(* <<DEFINIR vect_from_list ICI>> *)

 Example vect_from_list_ex1:
  vect_from_list (true::false::nil) = vCons true (vCons false vNil).
Proof.
  compute. reflexivity.
Qed.

(** ** Exercice *)

Theorem vect_list_convert:
  forall A : Set,
  forall l : list A,
    list_from_vect (vect_from_list l) = l.
Proof.
  (* <<COMPLETER ICI>> *)