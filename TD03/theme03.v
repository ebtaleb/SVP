
(* Script pour le thème 3 : Correspondance de Curry-Howard *)

Require Import Arith.


(**

 * La vérité

*)

Print True.

(* En Ocaml :

type vrai = V

*)

Lemma True_est_Vrai: True.
  apply I.
Qed.

Example ex_true_prop: 1 + 1 = 2.
Proof.
  simpl.
  reflexivity.
Qed.

Example ex_true_prop_true: (1 + 1 = 2) -> True.
Proof.
  intro H.
  apply I.
Qed.

Example ex_true_true_prop: True -> 1 + 1 = 2.
Proof.
  intro H.
  simpl.
  reflexivity.
Qed.

(**

  * Le faux

*)

Print False.

(**

_Question_ : peut-on définir un type non-habité en Ocaml ?

*)

Check False_ind.

Example false_elim_ex1:
  False -> 2 + 2 = 5.
Proof.
  intro HFalse.
  elim HFalse.  (* élimination *)
Qed.

Example false_elim_ex1':
  False -> 2 + 2 = 4.
Proof.
  intro HFalse.
  elim HFalse.  (* élimination *)
Qed.

Example false_elim_ex2:
  2 + 2 = 5 -> 8 * 0 = 42.
Proof.
  intro Hcontra.
  compute in Hcontra.
  absurd (4 = 5).
  SearchPattern ( _ <> _ ).
  (* n_Sn: forall n : nat, n <> S n *)
  apply n_Sn.
  exact Hcontra.
Qed.

Example false_elim_ex2':
  2 + 2 = 5 -> 8 * 0 = 42.
Proof.
  intro Hcontra.
  inversion Hcontra. (* preuve terminée ! *)
Qed.

Example false_elim_ex2'':
  2 + 2 = 5 -> 8 * 0 = 42.
Proof.
  intro Hcontra.
  assert (H: 2 + 2 <> 5).
  { simpl.
    apply n_Sn.
  }
  contradiction.
Qed.

(**

  ** Exercice

Montrer les lemmes suivant :

*)

Lemma times_two:
  forall n : nat, 2 * n = n + n.
Proof.
induction n as [|n'].
- simpl.
 reflexivity.
- simpl.
 SearchPattern ( S _ = S _ ).
 apply eq_S.
 SearchRewrite ( _ + 0 ).
 rewrite plus_0_r.
 reflexivity.
Qed.

Lemma plus_one_S:
  forall n : nat, n + 1 = S n.
Proof.
induction n as [|n'].
- simpl.
  reflexivity.
- SearchRewrite ( S _ ).
  rewrite <- IHn'.
  rewrite plus_n_Sm.
  SearchRewrite ( _ + ( _ + _ ) ).
  rewrite plus_assoc_reverse.
  rewrite ex_true_prop.
  reflexivity.
Qed.

Lemma false_exo:
  forall n k : nat,
    2 * n = k -> n + n = k + 1
    -> n * 4 = k.
Proof.
  intros n k H1F H2F.
  SearchRewrite ( _ * _ ).
  rewrite times_two in H1F.
  rewrite H1F in H2F.
  SearchRewrite ( _ + 1).
  rewrite plus_one_S in H2F.
  assert (k <> S k).    (*  absurd E = assert (not E) .... contradiction *)
  { SearchPattern (?X <> S ?X).
    apply n_Sn.
  }
  contradiction.
  Qed.
(**

  * La négation logique

*)

Print not.

Lemma not_not:
  forall P : Prop,  P -> not (not P).
Proof.
  intros P HP.
  unfold not.
  intro Hfalse.
  apply Hfalse.
  exact HP.
Qed.

Section not_not_classic.

  Hypothesis exluded_middle: forall P : Prop, P \/ not P.

  Lemma not_not': forall P : Prop, not (not P) -> P.
  Proof.
    intros P HnnP.
    unfold not in HnnP.
    assert (Hem: P \/ not P).
    apply exluded_middle.
    destruct Hem as [HP | HnP]. (* cf. disjonction *)
    - (* cas P *)
      exact HP.
    - (* cas (not P) *)
      assert (Hfalse: False).
      { apply HnnP.
        exact HnP.
      }
      inversion Hfalse.
  Qed.

End not_not_classic.

Example use_not_not':
  not (not True) -> True.
Proof.
  apply not_not'.
  (* bloqué *)
Abort.


(**

  ** Exercice

*** Question 1

Montrer que $\lnot \left ( 2 * 3 = 5 \right) $.

*)

Example q1 : not (2 * 3 = 5).
Proof.
  unfold not.
  simpl.
  intro HF.
  assert (HF1: 6 <> 5).
  { discriminate.
  }
  contradiction.
Qed.
(**

*** Question 2

Montrer par induction (et sans utiliser de lemme auxiliaire) :

*)

Lemma S_inject_r:
  forall n : nat, not (n = S n).  (* ou  not (n = S n) *)
Proof.
  induction n as [| n'].
  - simpl.
    trivial.
  -unfold not.
   intro HF.
   inversion HF.
   contradiction.
Qed.
(***
   assert (HF1: n' = S n').
   {
     apply eq_add_S.
     exact HF.
   }
   contradiction.

   SearchPattern (S _ = S _ -> _).
   apply eq_add_S in HF.
   contradiction.
   **)
(**

  *** Question 3

Démontrer [neq_sym] :  [x <> y -> y <> x]

*)

Lemma neq_sym: forall (A:Type) (x y: A), not (x = y) -> not (y = x).
Proof.
intros A x y.
unfold not.
intro HF.
intro eq.
apply HF.
inversion eq.
reflexivity.
Qed.


(**

  *** Question 4

Démontrer le lemme [S_inject_l] symétrique de [S_inject_r]
 en utilisant [neq_sym].

*)

(**

 * L'implication

*)

Lemma impl_refl: forall P:Prop, P -> P.
Proof.
  intros P HP.
  exact HP.
Qed.

Lemma impl_lemma:
  forall P Q : Prop,  (P -> Q) -> P -> Q.
Proof.
  intros P Q.
  intros Himpl HP.
  apply Himpl.
  exact HP.
Qed.

(**

En Ocaml :

let id : 'p -> 'p = fun x -> x

*)

Lemma impl_refl_direct: forall P : Prop, P -> P.
Proof.
  exact (fun (P:Prop) (p:P) => p).
Qed.

Print impl_refl.

(**

En Ocaml :

# fun (x:vrai) -> id x ;;
- : vrai -> vrai = <fun>

*)

Example V_impl_V: True -> True.
Proof.
  apply impl_refl.
Qed.

Example V_impl_V_direct: True -> True.
Proof.
  exact (impl_refl True).
Qed.

Example F_impl_F: False -> False.
Proof.
apply impl_refl.
Qed.


(**

 ** Exercice

 *** Question 1

Compléter la preuve ci-dessous :

*)

Lemma impl_trans: forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R i1 i2.
  intros p.
  apply i2.
  apply i1.
  exact p.
Qed.

(**

  *** Question 2

Démontrer le même résultat par une preuve manuelle en Ocaml.

*)

(*

 <<REPONDRE ICI>>
 (tester dans le top-level ocaml)

*)

Print impl_trans.

(**

 * la conjonction

En Ocaml :

type ('a,'b) conj = Et of ('a * 'b)

let et_intro: 'a -> 'b -> ('a,'b) conj =
  fun p1 p2 -> Et (p1, p2)

*)

Print and.

Lemma and_split:
  forall P : Prop, P  -> P /\ P.
Proof.
  intros P HP.
  split.
  - (* cas left *)
    exact HP.
  - (* cas right *)
    exact HP.
Qed.

Lemma and_split3:
  forall P : Prop, P  -> P /\ P /\ P.
Proof.
  intros P HP.
  split.
  - (* cas left *)
    exact HP.
  - (* cas right *)
    split.  (* on doit resplitter *)
    + (* cas left *)
      exact HP.
    + (* cas right *)
      exact HP.
Qed.

Lemma and_split3':
  forall P : Prop, P  -> P /\ P /\ P.
Proof.
  intros P HP.
  repeat split ; exact HP.
Qed.

Lemma et_elim_gauche:
  forall P Q:Prop, P /\ Q -> P.
Proof.
  intros P Q H.
  elim H.
  intros HP HQ.
  exact HP.
Qed.

Lemma et_elim_gauche':
  forall P Q:Prop, P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  exact HP.
Qed.

Lemma et_elim4_gauche:
  forall P Q R S:Prop, P /\ Q /\ R /\ S -> P.
Proof.
  intros P Q R S [HP [HQ [HR HS]]].
  exact HP.
Qed.

Lemma et_elim4_gauche':
  forall P Q R S:Prop, P /\ ( Q /\ ( R /\ S ) ) -> P.
Proof.
  intros P Q R S [HP [HQ [HR HS]]].
  exact HP.
Qed.

Lemma et_elim_gauche'':
  forall P Q:Prop, P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP HQ].
  exact HP.
Qed.


(**

En Ocaml :

let et_elim_gauche : ('p,'q) conj -> 'p = fun (Et x) -> fst x

*)

(**

  ** Exercice

  *** Question 1

Définir l'élimination à droite de la conjonction en Ocaml puis en Coq,
 en utilisant [elim] explicitement, puis avec un [intro] structuré et
 enfin avec un [destruct] structuré.

*)

(*

En Ocaml :

<<REPONDRE ICI>>  (tester dans le top-level ocaml)

*)

(* En Coq : avec elim *)

Lemma et_elim_droite:
  forall P Q:Prop, P /\ Q -> Q.
Proof.
  intros P Q H.
  elim H.
  intros HP HQ.
  exact HQ.
Qed.

(* En Coq : avec intros structuré *)

Lemma et_elim_droite':
  forall P Q:Prop, P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  exact HQ.
Qed.

(* En Coq : avec destruct structuré *)

Lemma et_elim_droite'':
  forall P Q:Prop, P /\ Q -> Q.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP HQ].
  exact HQ.
Qed.

(**

  *** Question 2

Démontrer avec un [intro] structuré :

[\forall P Q R S T : Prop, P /\ Q /\ R /\ S /\ T -> Q /\ S.]

*)


(**

 * l'équivalence logique

*)

Print iff.

(**

  ** Exercice

  *** Question 1

Définir en ocaml la fonction correspondante [ssi].

*)

(*

En Ocaml :

<<REPONDRE ICI>>  (tester dans le top-level ocaml)

*)

(**

  *** Question 2

Démontrer les lemmes:

 -  [iff_refl:  forall P:Prop, P <-> P] ainsi que la fonction Ocaml correspondante [ssi_refl].
 -  [iff_sym: forall P Q:Prop, (P <-> Q) -> (Q <-> P)] ainsi que la fonction Ocaml [ssi_sym].
 -  mêmes questions pour la transitivité de l'équivalence.

*)

(* iff_refl :  en OCaml

<<REPONDRE ICI>>  (tester dans le top-level ocaml)

*)

(* En Coq *)

Lemma iff_refl:
  forall P:Prop, P <-> P.
Proof.
  intros P.
  unfold iff.
  split.
  +intro HP.
   exact HP.
  +intro HP.
   exact HP.
Qed.

(* iff_sym :  en OCaml

<<REPONDRE ICI>>  (tester dans le top-level ocaml)

*)

(* En Coq *)

Lemma iff_sym:
  forall P Q:Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q.
  unfold iff.

Qed.

(* iff_trans : en Ocaml *)

(* En Coq *)

Lemma iff_trans:
  forall P Q R:Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ.
  destruct HPQ as [HP HQ].
  exact HQ.
Qed.

(**

  ** Exercice

  *** Question 1

Montrer les propriétés suivantes (si possible en utilisant des [intros] structurés) :

 - [(P /\ Q) /\ R <-> P /\ (Q /\ R)]
 - [(P /\ Q) <-> (Q /\ P)]
 - [(P /\ Q) /\ (Q /\ R) -> P /\ R]
*)

<<REPONDRE ICI>>

(**

 * la disjonction

*)

Print or.

Lemma ou_intro_l:
  forall P Q : Prop, P -> P \/ Q.
Proof.
  intros P Q HP.
  left.
  exact HP.
Qed.

(**

En Ocaml

# let ou_intro_l : 'p -> ('p, 'q) disj = fun (hp:'p) -> Ou_gauche hp ;;
val ou_intro_l : 'p -> ('p, 'q) disj = <fun>

*)

Lemma ou_intro_r:
  forall P Q : Prop, Q -> P \/ Q.
Proof.
  intros P Q HQ.
  right.
  exact HQ.
Qed.

(**

En Ocaml :

# let ou_intro_r : 'q -> ('p, 'q) disj = fun (hq:'q) -> Ou_droite hq ;;
val ou_intro_r : 'q -> ('p, 'q) disj = <fun>

*)

(**

  ** Exercice

  Montrer [ou_intro_3: forall P Q R S : Prop, Q -> P \/ R \/ Q \/ S].

*)

<<REPONDRE ICI>>

Lemma or_idem:
  forall P : Prop, P \/ P -> P.
Proof.
  intros P Hor.
  elim Hor.
  - (* cas left *)
    intro HP.
    exact HP.
  - (* cas right *)
    intro HP.
    exact HP.
Qed.

Lemma or_idem':
  forall P : Prop, P \/ P -> P.
Proof.
  intros P [ HP1 | HP2 ].
  - (* cas left *)
    exact HP1.
  - (* cas right *)
    exact HP2.
Qed.

Lemma or_idem'':
  forall P : Prop, P \/ P -> P.
Proof.
  intros P Hor.
  destruct Hor as [HP1 | HP2].
  - (* cas left *)
    exact HP1.
  - (* cas right *)
    exact HP2.
Qed.

Lemma or_idem3:
  forall P : Prop, P \/ P \/ P -> P.
Proof.
  intros P [ HP1 | [ HP2 | HP3 ] ].
  - (* cas left/left *)
    exact HP1.
  - (* cas right/left *)
    exact HP2.
  - (* cas right/right *)
    exact HP3.
Qed.


(**

  ** Exercice

  *** Question 1

Montrer la commutativité [or_sym] de la disjonction.

*)

<<REPONDRE ICI>>

(**

 * Quantificateur universel

*)

Example forall_impl:
  forall A B : Prop,
    (forall pa : A, B) = (A -> B).
Proof.
  intros A B.
  reflexivity.
Qed.

Lemma nat_refl:
  forall n : nat, n = n.
Proof.
  intro n.
  reflexivity.
Qed.

Lemma lt_lt_silly:
  (forall n:nat, n > 0)
  -> forall m:nat, m > 0.
Proof.
  intros Hforall m.
  apply Hforall with (n:=m).
Qed.

Lemma lt_lt_silly':
  (forall n:nat, n > 0)
  -> forall m:nat, m > 0.
Proof.
  intros Hforall m.
  apply (Hforall m).
Qed.

Lemma lt_lt_silly'':
  (forall n:nat, n > 0)
  -> forall m:nat, m > 0.
Proof.
  intros Hforall m.
  apply Hforall.
Qed.

(**

  ** Exercice

Démontrer le lemme suivant :

*)

Lemma forall_impl_point:
  forall E : Type, forall e : E, forall P Q : E -> Prop,
   (forall x : E, P x -> Q x) -> P e -> Q e.
Proof.
  <<COMPLETER ICI>>

(**

 * la quantification existentielle

*)

Print ex.

Lemma ex_forall: forall E : Set, forall y : E, forall P Q : E -> Prop,
  (forall x : E, P x -> Q x) -> P y -> exists z : E, Q z.
Proof.
  intros E y P Q H1 H2.
  exists y.
  apply H1.
  exact H2.
Qed.

(**

  ** Exercice

Montrer :

*)

Lemma pred_ex:
  forall n : nat,
    n <> 0
    -> exists p : nat, S p = n.
Proof.
  <<COMPLETER ICI>>

Lemma lt_neq_0:
  forall m : nat,
  (exists n : nat,  n < m) -> 0 <> m.
Proof.
  intros m Hex.
  elim Hex. clear Hex.
  intros x Hlt.
  destruct m as [|m'].
  inversion Hlt. (* contradition *)
  SearchPattern (0 <> S _ ).
  (* O_S: forall n : nat, 0 <> S n *)
  apply O_S.
Qed.

(**

  ** Exercice

Montrer :

*)

Lemma encadrement:
  forall n p : nat,
    (exists m : nat, (n <= m) /\ (m < p)) -> n < p.
Proof.
  <<COMPLETER ICI>>

(**

 * l'égalité

*)

Print eq.

Lemma eq_refl': forall a:Type, a = a.
Proof.
  intro a.
  apply eq_refl. (* ou reflexivity *)
Qed.

Lemma eq_sym': forall a b : Type, a = b -> b = a.
Proof.
  intros a b Heq.
  rewrite Heq.
  reflexivity. (* ou apply eq_refl ou apply eq_refl' *)
Qed.

Lemma eq_sym'': forall a b : Type, a = b -> b = a.
Proof.
  intros a b Heq.
  rewrite <- Heq.
  reflexivity.
Qed.

(**

 ** Exercice

Démontrer la transititivé de l'égalité : [eq_trans'].

*)

<<REPONDRE ICI>>

Check eq_nat_dec.

Lemma nat_split:
  forall n m : nat, (n = m) \/ (n <> m).
Proof.
  intros n m.
  destruct (eq_nat_dec n m) as [Heq | Hneq].
  - (* cas n=m *)
    left.
    exact Heq.
  - (* cas n<>m *)
    right.
    exact Hneq.
Qed.

Require Import List.

Section member.

Variable A : Set.

Hypothesis eq_dec: forall a b : A, {a = b} + {a <> b}.

Fixpoint member (e:A) (l: list A) : bool :=
  match l with
    | nil => false
    | e'::l' => match eq_dec e e' with
                  | left _ => true
                  | right _ => member e l'
                end
  end.

End member.


Example member_ex1:
  member nat eq_nat_dec 3 (1::2::3::4::5::nil) = true.
Proof.
  compute. reflexivity.
Qed.

Arguments member [A] _ _ _.

Example member_ex2:
  member eq_nat_dec 3 (1::2::3::4::5::nil) = true.
Proof.
  compute. reflexivity.
Qed.

(**

  ** Exercice

Compléter le lemme suivant :

*)

Section member_cons.

Variable A : Set.

Hypothesis eq_dec : forall a b : A, {a = b} + {a <> b}.

Lemma member_cons:
  forall e : A, forall l : list A,
    member eq_dec e (e::l) = true.
Proof.
  <<COMPLETER ICI>>>

End member_cons. (* fermeture de section *)

