(**

Nous allons utiliser la méthode du formalisme B pour
spécifier un problème de gestion des feux d'un carrefour. Cet
exemple est largement inspiré d'une petite étude de cas que
J.-Y. Chauvet a publiée dans '1st Conference on the B
method, Proceedings, ed. Henri Habrias, Nantes 1996'.

*)

(** * Spécification

Le système se compose de deux feux tricolores dont les couleurs sont vert, orange 
ou rouge.

Le système a deux états: hors service ou en service.

Le système implémente deux opérations: mise en service et changement
de couleur des feux. 

Lorsque le système est hors service, les deux feux sont oranges.

Lorsque le système est en service, un et un seul des deux feux est au 
rouge.

Les feux changent de couleur selon le cycle suivant: orange, rouge, vert, orange.

*)

(** * Formalisation
  La spécification du système et ses obligations de preuve sont rassemblées dans 
le module [TraficLights].
*)

Module TraficLights.


  (** ** Contexte du système 
     Le contexte du système définit l'ensemble des couleurs:
     «les couleurs sont vert, orange et rouge»
   *)

  Module Context.

    Inductive color := red | yellow | green.

  End Context.

  Import Context.

  (** ** Etat du système 
    L'état du système doit permetre de déterminer si celui-ci est «en service ou hors service» 
    et de connaître la couleur des «deux feux tricolores».
   *)

  Record State : Set := mkState {
                            service : bool;
                            light1 : color;
                            light2 : color
                          }.

  (** Pour alléger les écritures, on définit trois opérations d'affection de l'état *)

  Definition set_service (b:bool) (st:State) := 
    (mkState b st.(light1) st.(light2)).

  Definition set_light1 (c:color) (st:State) :=
    (mkState st.(service) c st.(light2)).

  Definition set_light2 (c:color) (st:State) :=
    (mkState st.(service) st.(light1) c).

  (** ** Invariants du système *)
  (** Système hors service:
      «lorsque le système est hors service, les deux feux sont oranges» 
   *)

  Definition Inv_1 (st:State) : Prop := st.(service) = false -> st.(light1) = yellow /\ st.(light2) = yellow.

  (** Système en service:
    «Lorsque le système est en service, un et un seul des deux feux est au rouge.
   *)
  Definition xor (a:bool) (b:bool) : bool :=
    match a, b with
      | true, true | false, false => false
      | _, _ => true
        end. 

  Example xor_1 : xor true false = true.
  Proof.
    simpl.
    reflexivity.
  Qed.
  
  Definition Inv_2 (st:State) : Prop := st.(service) = true -> not (st.(light1) = red /\ st.(light2) = red) /\ (st.(light1) = red \/ st.(light2) = red) . 

  (** ** Initialisation du service 
     La «mise en service» est réalisée dans le module [Init].
   *)

  Module MiseEnService.

    (** NB: l'initialisation du système est inconditionnelle *)

    Definition Guard (st:State) := True.

    (** Transition de mise en service *)
    
    Definition action (st:State) := mkState true red green.
    
    (** *** Obligations de preuve *)

    Theorem PO_Safety_1 : forall s: State, Guard s -> let next := action s in Inv_1 next.
    Proof.
      intros s.
      simpl.
      compute.
      intros t.
      intros Hf.
      inversion Hf.
    Qed.

    Theorem PO_Safety_2 : forall s: State, Guard s -> let next := action s in Inv_2 next.
    Proof.
      intros s.
      compute.
      intros t.
      intros tt.
      split.
      -intro h1.
       elim h1.
       intro h2.
       intro h3.
       inversion h3.
      -left.
       reflexivity.
    Qed.

  End MiseEnService.

  (** ** Changement de couleur *)

  Module ChangeColor.

    (** Guarde: le système est en service *)

    Definition Guard (st:State) := st.(service) = true.

    (** Transition de changement de couleur:
      «Les feux changent de couleur selon le cycle suivant: orange, rouge, vert, orange»
     *)

    Definition rotate1 (st:State) :=
      match st.(light1) with
        | yellow => set_light1 red st
        | red => set_light1 green st
        | green => set_light1 yellow st
      end.

    Definition rotate2 (st:State) :=
      match st.(light2) with
        | yellow => set_light2 red st
        | red => set_light2 green st
        | green => set_light2 yellow st
      end.

   (* Definition action (st:State) :=
      match st.(service) with
        | false => set_light1 yellow (set_light2 yellow st)
        | true => rotate1 (rotate2 st)
      end.*)
    Definition action (st:State) :=
      match st.(light1), st.(light2) with
        | red, red => (mkState st.(service) red red)
        | yellow, yellow => (mkState st.(service) yellow yellow)
        | green, green => (mkState st.(service) green green)
        | red, yellow => (mkState st.(service) green red)
        | red, green => (mkState st.(service) green yellow)
        | yellow, red => (mkState st.(service) red green)
        | yellow, green => (mkState st.(service) red yellow)
        | green, red => (mkState st.(service) yellow green)
        | green, yellow => (mkState st.(service) yellow red)
      end.
    
    (**
      Propriété utile du changement de couleur: 
         le champ [service] n'est pas affecté par la transition.
     *)

    Lemma change_service :
      forall (st:State),
        (action st).(service) = st.(service).
    Proof.
      intro st.
      unfold action.
      destruct (light1 st);  (destruct (light2 st); auto).
      (*- (* light1 green *)
        destruct (light2 st); auto.
      - (* light1 red *)
        destruct (light2 st); auto.
      - (* light1 yellow *)
        destruct (light2 st); auto.*)
    Qed.

    (** *** Obligations de preuve *)

    Theorem PO_Safety_1 :  forall s: State, Guard s -> Inv_1 s -> let next := action s in Inv_1 next.
    Proof.
      intro s.
      unfold Guard.
      intro t.
      intro inv.
      unfold Inv_1.
      intros hs.
      rewrite change_service in hs.
      rewrite t in hs.
      discriminate hs.
    Qed.

    Theorem PO_Safety_2 :  forall s: State, Guard s -> Inv_2 s -> let next := action s in Inv_2 next. 
    Proof. 
      intros s.
      unfold Guard.
      intro t.
      unfold Inv_2.
      intro inv.
      elim (inv t).
      intros Inv_2a Inv_2b.
      intro sa.
      split.
      - intros rr.
        unfold action in rr.
        destruct (light1 s).
        + destruct (light2 s).
          * compute in rr.
            absurd (red = red /\ red = red); assumption.
          * compute in rr.
            elim rr.
            intros rr1 rr2.
            discriminate rr1.
          * compute in rr.
            elim rr.
            intros rr1 rr2.
            discriminate rr1.
        + destruct (light2 s).
          * compute in rr; elim rr; intros rr1 rr2; discriminate rr2.
          * compute in rr; elim rr; intros rr1 rr2; discriminate rr2.
          * compute in rr; elim rr; intros rr1 rr2; discriminate rr2.
        + destruct (light2 s).
          * compute in rr; elim rr; intros rr1 rr2; discriminate rr2.
          * compute in rr; elim rr; intros rr1 rr2; discriminate rr1.
          * compute in rr; elim rr; intros rr1 rr2; discriminate rr2.
      -unfold action.
       auto.
    Qed.
    
  End ChangeColor.

End TraficLights.
