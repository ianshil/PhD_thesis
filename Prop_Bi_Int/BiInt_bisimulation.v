Require Import List.
Export ListNotations.

Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import BiInt_GHC.
Require Import BiInt_Kripke_sem.


(* Define the notion of bisimulation. *)

Definition bisimulation (M0 M1 : model) (B : (@nodes M0) -> (@nodes M1) -> Prop) : Prop :=
  forall (w0 : @nodes M0) (w1 : @nodes M1), (B w0 w1) ->
 (* B1 *) ((forall p, (@val M0) w0 p <-> (@val M1) w1 p) /\
 (* B2 *) (forall v1, ((@reachable M1) w1 v1) -> (exists v0, ((@reachable M0) w0 v0) /\ (B v0 v1))) /\
 (* B3 *) (forall v0, ((@reachable M0) w0 v0) -> (exists v1, ((@reachable M1) w1 v1) /\ (B v0 v1)))) /\
 (* B4 *) (forall v1, ((@reachable M1) v1 w1) -> (exists v0, ((@reachable M0) v0 w0) /\ (B v0 v1))) /\
 (* B5 *) (forall v0, ((@reachable M0) v0 w0) -> (exists v1, ((@reachable M1) v1 w1) /\ (B v0 v1))).

(* Show that bisimulation implies bi-intuitionistic equivalence. *)

Lemma bisimulation_imp_bi_int_equiv : forall (M0 M1 : model) (B :(@nodes M0) -> (@nodes M1) -> Prop),
  (bisimulation M0 M1 B) ->
  (forall A w0 w1, (B w0 w1) ->
    ((wforces M0 w0 A) <-> (wforces M1 w1 A))).
Proof.
intros M0 M1 B H.
induction A ; split ; intro.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. inversion H1.
  * simpl. inversion H1.
  * simpl in H1. apply I.
  * apply I.
  * simpl in H1. destruct H1. simpl. split. pose (IHA1 w0 w1 H0). apply i. auto.
    pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. destruct H1. simpl. split. pose (IHA1 w0 w1 H0). apply i. auto.
    pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. simpl. destruct H1. left. pose (IHA1 w0 w1 H0). apply i. auto.
    right. pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. simpl. destruct H1. left. pose (IHA1 w0 w1 H0). apply i. auto.
    right. pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl. simpl in H1. intros. unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H5. destruct H4. clear H4. destruct H5. clear H5.
    pose (H4 _ H2). destruct e. destruct H5.
    pose (IHA1 x v H6). apply i in H3. apply H1 in H3. 2: auto.
    pose (IHA2 x v H6). apply i0. auto.
  * simpl. simpl in H1. intros. unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H5. destruct H4. clear H4.
    destruct H5. clear H4.
    pose (H5 _ H2). destruct e. destruct H4.
    pose (IHA1 v x H6). apply i in H3. apply H1 in H3. 2: auto.
    pose (IHA2 v x H6). apply i0. auto.
  * simpl. simpl in H1. destruct H1. destruct H1. destruct H2.
    unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H4. destruct H5. clear H4.
    pose (H5 _ H1). destruct e. destruct H4. exists x0.
    pose (IHA1 x x0 H6). apply i in H2.
    pose (IHA2 x x0 H6). repeat split ; auto. intro.
    apply i0 in H7. apply H3. auto.
  * simpl. simpl in H1. destruct H1. destruct H1. destruct H2.
    unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H4. destruct H5. clear H5.
    pose (H4 _ H1). destruct e. destruct H5. exists x0.
    pose (IHA1 x0 x H6). apply i in H2.
    pose (IHA2 x0 x H6). repeat split ; auto. intro.
    apply i0 in H7. apply H3. auto.
Qed.








