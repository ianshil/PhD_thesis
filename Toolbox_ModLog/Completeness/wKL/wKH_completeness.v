Require Import Classical.

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
Require Import wKH_Lindenbaum_lem.

Definition is_mcs (Γ: Ensemble MPropF) : Prop :=
  ((forall B, (Γ B) \/ (Γ (B --> Bot))) /\ (wKH_prv (Γ, Bot) -> False)).

Lemma clos_deriv : forall Γ, is_mcs Γ ->
                                (forall A, wKH_prv (Γ, A) -> (In _ Γ A)).
Proof.
intros. destruct H. pose (H A). destruct o ; auto.
exfalso. apply H1.
apply MP with  (ps:=[(Γ, A --> Bot);(Γ, A)]).
2: apply MPRule_I. intros. inversion H3 ; subst.
apply Id. apply IdRule_I ; auto. inversion H4. 2: inversion H5.
subst. auto.
Qed.

Definition Canon_worlds : Type := {x : Ensemble MPropF | is_mcs x}.

Definition Canon_rel (P0 P1 : Canon_worlds) : Prop :=
  forall A, (In _ (proj1_sig P0) (Box A)) -> (In _ (proj1_sig P1) A).

Definition Canon_val (P : Canon_worlds) (q : V) : Prop :=
  In _ (proj1_sig P) (# q).

Instance CM : kmodel :=
      {|
        nodes := Canon_worlds ;
        reachable := Canon_rel ;
        val := Canon_val
      |}.

Lemma existence_lemma : forall A (cw : Canon_worlds),
  (forall cw0, Canon_rel cw cw0 -> In _ (proj1_sig cw0) A) -> (In _ (proj1_sig cw) (Box A)).
Proof.
intros. destruct cw.
pose (@exist (Ensemble MPropF) is_mcs x i).
inversion i. simpl. pose (H0 (Box A)) ; destruct o ; auto.
assert (J0: wKH_prv (fun y : MPropF => (exists B : MPropF, In MPropF x (Box B) /\ y = B) \/ y = (A --> Bot), Bot) -> False).
{ intro. assert ((fun y : MPropF => (exists B : MPropF, In MPropF x (Box B) /\ y = B) \/ y = A --> Bot) =
  (Union _ (fun y : MPropF => (exists B : MPropF, In MPropF x (Box B) /\ y = B)) (Singleton _ (A --> Bot)))).
  apply Extensionality_Ensembles. split ; intro ; intros. inversion H4. destruct H5.
  destruct H5. subst. apply Union_introl ; auto. unfold In. exists x1 ; auto. subst.
  apply Union_intror. apply In_singleton. inversion H4. subst. inversion H5.
  destruct H6. subst. unfold In. left. exists x1 ; auto. subst. inversion H5.
  subst. unfold In ; auto.
  rewrite H4 in H3. clear H4.
  assert (J0: Union MPropF
     (fun y : MPropF => exists B : MPropF, In MPropF x (Box B) /\ y = B)
     (Singleton MPropF (A --> Bot)) =
   Union MPropF
     (fun y : MPropF => exists B : MPropF, In MPropF x (Box B) /\ y = B)
     (Singleton MPropF (A --> Bot)) ). auto.
  assert (J1: Bot = Bot). auto.
  pose (wKH_Deduction_Theorem _ H3 (A --> Bot) Bot
  (fun y : MPropF => exists B : MPropF, In MPropF x (Box B) /\ y = B) J0 J1).
  apply NegNeg_elim in w. clear J0. clear J1.
  apply K_rule in w. apply H1.
  apply MP with (ps:=[(x, Box A --> Bot);(x, Box A)]). 2: apply MPRule_I.
  intros. inversion H4. subst. apply Id. apply IdRule_I. auto. inversion H5.
  2: inversion H6. subst.
  pose (wKH_monot _ w). apply w0 ; simpl. clear w0.
  intro. intros. destruct H6. inversion H6. subst.
  inversion H7. destruct H8. subst. auto. }
pose (Lindenbaum_lemma (fun y => (exists B, (In _ x (Box B)) /\ y = B) \/ y = (A --> Bot)) Bot J0).
destruct e. destruct H3. destruct H4.
assert (J1: is_mcs x0). unfold is_mcs. auto.
pose (@exist (Ensemble MPropF) is_mcs x0 J1).
assert (J2: Canon_rel (exist (fun x : Ensemble MPropF => is_mcs x) x i) s0).
intro. intros. simpl. apply H3. simpl in H6. unfold In. left. exists A0 ; auto.
pose (H s0 J2). simpl in i0.
exfalso. apply H5.
apply MP with (ps:=[(x0, A --> Bot);(x0, A)]). 2 : apply MPRule_I.
intros. inversion H6 ; subst. apply Id. apply IdRule_I. apply H3.
unfold In. auto. inversion H7. subst. apply Id. apply IdRule_I. auto.
inversion H8.
Qed.

Lemma truth_lemma : forall A (cw : Canon_worlds),
  (wforces CM cw A) <-> (In _ (proj1_sig cw) A).
Proof.
induction A ; intro ; split ; intros ; destruct cw ; simpl ; try simpl in H ; auto.
(* Bot V *)
- inversion H.
- unfold is_mcs in i. destruct i. apply H1. apply Id. apply IdRule_I. auto.
(* Imp A1 A2 *)
- assert (J0: is_mcs x). auto.
  pose (@exist (Ensemble MPropF) is_mcs x i).
  unfold is_mcs in J0. destruct J0.
  pose (H0 A1). destruct o. pose (IHA1 s). simpl in i0. apply i0 in H2.
  clear i0. apply H in H2. apply IHA2 in H2. simpl in H2.
  apply clos_deriv ; auto.
  apply MP with (ps:=[(x, A2 --> A1 --> A2);(x, A2)]). 2: apply MPRule_I.
  intros. inversion H3 ; subst. apply Ax. apply AxRule_I. apply MA2_I.
  exists A2 ; exists A1 ; auto. inversion H4 ; subst. 2: inversion H5.
  apply Id. apply IdRule_I. auto.
  apply clos_deriv ; auto.
  apply wKH_Deduction_Theorem with (s:=(Union _ x (Singleton _ A1), A2)) ; auto.
  apply MP with (ps:=[(Union MPropF x (Singleton MPropF A1), Bot --> A2);
  (Union MPropF x (Singleton MPropF A1), Bot)]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply MA4_I. exists A2 ; auto. inversion H4. 2: inversion H5. subst.
  apply MP with (ps:=[(Union MPropF x (Singleton MPropF A1), A1 --> Bot);
  (Union MPropF x (Singleton MPropF A1), A1)]). 2: apply MPRule_I.
  intros. inversion H5. subst. apply Id. apply IdRule_I. apply Union_introl ; auto.
  inversion H6. subst. apply Id. apply IdRule_I. apply Union_intror. apply In_singleton.
  inversion H7.
- intros. apply IHA1 in H0. simpl in H0. apply IHA2. simpl.
  apply clos_deriv ; auto.
  apply MP with (ps:=[(x, A1 --> A2);(x, A1)]). 2: apply MPRule_I.
  intros. inversion H1. subst. apply Id. apply IdRule_I ; auto.
  inversion H2 ; subst. 2: inversion H3. apply Id. apply IdRule_I ; auto.
(* Box A1 *)
- pose (@exist (Ensemble MPropF) is_mcs x i).
  pose (existence_lemma A s). apply i0. intros. apply IHA. auto.
- intros. apply IHA. auto.
Qed.

Theorem wCounterCompleteness : forall Γ A,
    (wKH_prv (Γ, A) -> False) -> ((loc_conseq Γ A) -> False).
Proof.
intros Γ A WD.
apply Lindenbaum_lemma in WD. destruct WD. destruct H. destruct H0.
intro. unfold loc_conseq in H2.
assert (J1: is_mcs x). unfold is_mcs. split ; auto. intro. apply H1.
apply MP with (ps:=[(x, Bot --> A);(x, Bot)]). 2: apply MPRule_I.
intros. inversion H4. subst. apply Ax. apply AxRule_I. apply MA4_I.
exists A ; auto. inversion H5 ; subst. 2: inversion H6. auto.
pose (@exist (Ensemble MPropF) is_mcs x J1).
pose (H2 CM s).
assert (forall B : MPropF, In MPropF Γ B -> wforces CM s B). intros. apply truth_lemma. auto.
apply w in H3. apply truth_lemma in H3. simpl in H3.
apply H1. apply Id. apply IdRule_I ; auto.
Qed.

Theorem wCompleteness : forall Γ A,
    (loc_conseq Γ A) -> wKH_prv (Γ, A).
Proof.
intros Γ A LC. pose (wCounterCompleteness Γ A).
pose (classic (wKH_prv (Γ, A))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.
