Require Setoid.

(** * La machine abstraite *)
Module TraficLights.

(** Coller ici votre spécification de la machine abstraite *)

End TraficLights.

(** * Le raffinement *)

(** Nous vous proposons de réaliser un raffinement de la machine
abstraite de gestion des feux qui repose sur le principe suivant
(raffinement de données): chaque feu est représenté par 3 valurs
booléennes.

En effet, un feu est concrètement impléméenté par 3 lampes dont
chaucune possède une couleur. Un lampe doit être allumée ou éteinte,
d'où les 2 valeurs booléenne: \txt{true} peut valoir pour «allumée»;
\txt{false} peut valoir pour «éteinte».

*)

Module TraficLights_R.


  (** ** Etat du système *)
  Record State : Set := mkState {
                            service : bool;
                            light1 : color;
                            light2 : color
                          }.

  (** ** Invariant de collage 
      Il établit la relation entre l'état du raffinement et l'état de la machine 
      abstraite.

      Conseil: l'invariant risque d'être un peu long, utilisez des définitions
      auxilaires.
  *)

  Definition Glue (st:State) (abs_st:TraficLights.State) : Prop :=
    (* A DEFINIR *).

  (** ** Invariants du système.
      Définir les deux invariants [Inv1] et [Inv2] de la machine abstraite
      pour le raffinement.
   *)

  Definition Inv1 (st:State) : Prop :=
    (* A DEFINIR *).

  Definition Inv2 (st:State) : Prop :=
    (* A DEFINIR *).
  
  (** ** Initialisation *)
  Module Init.

    Definition action (st : State) : State :=
      (* A DEFINIR *).

    (** *** Obligations de preuve *)
    Theorem PO_Safety_1 : forall (st:State), (Inv1 (action st)). 
    Proof
      (* A FAIRE *)
    Qed.

    Theorem PO_Safety_2 : forall (st:State), (Inv2 (action st)).
    Proof
      (* A FAIRE *)
    Qed.

  End Init.

  (** ** Mise en service *)
  Module StartService.

    (** Guarde: le système est hors service *)
    Definition Guard (st:State) := 
      (* A DEFINIR *).

    
    Definition action (st:State) :=
      (* A DEFINIR *).

    (** *** Obligations de preuves 
       L'obligation de preuve d'un raffinement doit prendre en compte l'état
       du système concret et l'état du système abstrait pour énoncer la
       préservation de l'invariant de l'abstrait au concret.
     *)
    Theorem PO_Safety_1 : forall (st:State) (abs_st:TraficLights.State),
                            (* A COMPLETER *).
    Proof
      (* A FAIRE *)
    Qed.

    Theorem PO_Safety_2 : forall (st:State) (abs_st:TraficLights.State),
                            (* A COMPLETER *).
    Proof.
      (* A FAIRE *)
    Qed.

    (** *** Simulation La propriété de simulation doit énoncer que
        l'action préserve l'invariant de collage. 
     *)
    Theorem PO_Simul : forall (st:State) (abs_st:TraficLights.State),
                         (* A COMPLETER *).
    Proof.
      (* A FAIRE *)
    Qed.

  End StartService.

  (** ** Changement de couleur *)
  Module ChangeColor.

    (** Guarde: le systèm est en service *)
    Definition Guard (st:State) :=
      (* A DEFINIR *).

    (** Action *)
    Definition action (st:State) :=
      (* A DEFINIR *).
    
    Require Import Bool.
    
    (** Lemme utile *)
    Theorem service_unchanged: forall (st:State),
      (service (action st)) = (service st).
    Proof.
      (* A FAIRE *)
    Qed.

    (** Obligations de preuves *)
    Theorem P0_Safety_1 : forall (st:State) (abs_st:TraficLights.State),
                            (* A COMPLETER *).
    Proof.
      (* A FAIRE *)
    Qed.

    Theorem P0_Safety_2 : forall (st:State) (abs_st:TraficLights.State),
                            (* A COMPLETER *).
    Proof.
      (* A FAIRE *)
    Qed.

  End ChangeColor.

End TraficLights_R.