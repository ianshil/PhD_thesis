Require Import Classical.
(* Used only in deciding whether a consecutions is provable or not. *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import K_Syntax.
Require Import K_GHC.
Require Import K_logics.
Require Import K_extens_interactions.
Require Import K_wKH_meta_interactions.
Require Import K_sKH_meta_interactions.
Require Import K_Kripke_sem.
Require Import K_bisimulation.
Require Import wKH_Lindenbaum_lem.
Require Import wKH_completeness.

Fixpoint n_reachable {W : Type} (R : W -> W -> Prop) (n: nat) (w v : W) : Prop :=
  match n with
  | 0 => w = v
  | S m => exists u, (R u v) /\ (n_reachable R m w u)
  end.

Lemma Box_form_Box : forall n A, (Box_power (S n) A) = (Box_power n (Box A)).
Proof.
induction n.
- intros. simpl. auto.
- intros. simpl. pose (IHn A). rewrite <- e. simpl. auto.
Qed.

Lemma n_reachable_Box_clos : forall M n w A,
  (wforces M w (Box_power n A)) ->
    (forall v, (n_reachable (@reachable M) n w v) -> (wforces M v A)).
Proof.
intro M. induction n.
- intros. simpl in H. inversion H0. subst. auto.
- intros. inversion H0. destruct H1.
  pose (IHn w (Box A)). pose (Box_form_Box n A). rewrite e in H.
  pose (w0 H x H2). simpl in w1. pose (w1 v H1). auto.
Qed.

Lemma Box_clos_Box_form : forall n Γ A, (In _ Γ A) -> (In _ (Box_clos_set Γ) (Box_power n A)).
Proof.
induction n.
- intros. simpl. apply InitClo. auto.
- intros. simpl. apply IndClo. apply IHn. auto.
Qed.

(* We use the model given by wCompleteness: we restrict the model. *)

Definition is_reachable {W : Type} R w v : Prop :=
  exists n, @n_reachable W R n w v.

Definition restr_worlds {W : Type} R w : Type :=
  { x : W | is_reachable R w x}.

Definition restr_rel {W : Type} R w (rw0 rw1 : @restr_worlds W R w) : Prop :=
  R (proj1_sig rw0) (proj1_sig rw1).

Definition restr_val {W : Type} R (val : W -> V -> Prop) w (rw : @restr_worlds W R w) (q : V) : Prop :=
  val (proj1_sig rw) q.

(* So, we can define a restricted model out of a model. *)

Definition restr_model (M : kmodel) (w : nodes) : kmodel :=
      {| nodes := (restr_worlds (@reachable M) w) ;
        reachable := (restr_rel (@reachable M) w) ;
        val := (restr_val (@reachable M) (@val M) w) |}.

(* This gives us completeness. *)

Theorem sCounterCompleteness : forall Γ A,
    (sKH_prv (Γ, A) -> False) -> ((glob_conseq Γ A) -> False).
Proof.
intros Γ A SD.
assert (J1: sKH_prv (Box_clos_set Γ, A) -> False).
intro. apply SD. unfold sKH_prv in H. unfold sKH_prv.
pose (sKH_comp _ H Γ). simpl in s. apply s. clear s. intros.
induction H0. apply Ids. apply IdRule_I. assumption.
apply sNec with (ps:=[(Γ, A0)]). intros. inversion H1. subst. auto.
inversion H2. apply sNecRule_I.
assert (J2: wKH_prv (Box_clos_set Γ, A) -> False).
intro. apply J1. apply sKH_extens_wKH ; auto.
pose (wCounterCompleteness _ _ J2).
intro. apply f. intro. intros. unfold glob_conseq in H.

assert (Bisim: bisimulation M (restr_model M w)
(fun (x : (@nodes M)) (y : (restr_worlds (@reachable M) w)) => x = (proj1_sig y))).
{ unfold bisimulation. intros. subst. repeat split.
  - intro. unfold restr_val. auto.
  - intro. unfold restr_val. auto.
  - intros. exists (proj1_sig v1). split ; auto.
  - intros. assert (J20: is_reachable (@reachable M) w v0).
    unfold is_reachable. destruct w1. simpl in H1. unfold is_reachable in i.
    destruct i. exists (S x0). simpl. exists x. split ; auto.
    pose(@exist  (@nodes M) (@is_reachable (@nodes M) (@reachable M) w) v0 J20). exists s.
    auto. }

(* All formulae in Γ are globally true in the restricted model. *)
assert (SAT: forall (pw : @nodes (restr_model M w)) A, (In _ Γ A) ->
wforces (restr_model M w) pw A).
{ intros. pose (bisimulation_imp_modal_equiv _ _ _ Bisim).
  pose (i A0 (proj1_sig pw) pw). apply i0. auto. clear i0. clear i. destruct pw. simpl.
  unfold is_reachable in i. destruct i.
  assert (J5: wforces M w (Box_power x0 A0)).
  { apply H0. apply Box_clos_Box_form ; auto. }
  pose (n_reachable_Box_clos M x0 w A0 J5 x). auto. }

assert (J20: is_reachable (@reachable M) w w). unfold is_reachable. exists 0.
unfold n_reachable. auto.
pose (@exist (@nodes M) (is_reachable (@reachable M) w) w J20).
pose (bisimulation_imp_modal_equiv _ _ _ Bisim A w s). apply i ; auto.
apply H. intros. intro. apply SAT. auto.
Qed.

Theorem sCompleteness : forall Γ A,
    (glob_conseq Γ A) -> sKH_prv (Γ, A).
Proof.
intros Γ A GC. pose (sCounterCompleteness Γ A).
pose (classic (sKH_prv (Γ, A))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.