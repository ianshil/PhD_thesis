Require Import List.
Export ListNotations.

Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import K_Syntax.
Require Import K_Kripke_sem.


(* Define the notion of bisimulation. *)

Definition bisimulation (M0 M1 : kmodel) (B : (@nodes M0) -> (@nodes M1) -> Prop) : Prop :=
  forall (w0 : @nodes M0) (w1 : @nodes M1), (B w0 w1) ->
 (* B1 *) ((forall p, (@val M0) w0 p <-> (@val M1) w1 p) /\
 (* B2 *) (forall v1, ((@reachable M1) w1 v1) -> (exists v0, ((@reachable M0) w0 v0) /\ (B v0 v1))) /\
 (* B3 *) (forall v0, ((@reachable M0) w0 v0) -> (exists v1, ((@reachable M1) w1 v1) /\ (B v0 v1)))).

(* Show that bisimulation implies logical equivalence. *)

Lemma bisimulation_imp_modal_equiv : forall M0 M1 B,
  (bisimulation M0 M1 B) ->
  (forall A w0 w1, (B w0 w1) -> ((wforces M0 w0 A) <-> (wforces M1 w1 A))).
Proof.
intros M0 M1 B H.
induction A ; split ; intro.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. inversion H1.
  * simpl. inversion H1.
  * simpl. simpl in H1. intros. pose (IHA1 w0 w1 H0).
    apply i in H2. apply H1 in H2. pose (IHA2 w0 w1 H0).
    apply i0 in H2. auto.
  * simpl. simpl in H1. intros. pose (IHA1 w0 w1 H0).
    apply i in H2. apply H1 in H2. pose (IHA2 w0 w1 H0).
    apply i0 in H2. auto.
  * simpl. simpl in H1. unfold bisimulation in H. intros.
    pose (H w0 w1 H0). destruct a. destruct H4. apply H4 in H2.
    destruct H2. apply IHA with (w0:=x) ; auto. destruct H2 ; auto.
    apply H1 ; auto. destruct H2 ; auto.
  * simpl. simpl in H1. unfold bisimulation in H. intros.
    pose (H w0 w1 H0). destruct a. destruct H4. apply H5 in H2.
    destruct H2. apply IHA with (w1:=x) ; auto. destruct H2 ; auto.
    apply H1 ; auto. destruct H2 ; auto.
Qed.




