Require Import List.
Export ListNotations.

Require Import PeanoNat.

Require Import Ensembles.
Require Import BiInt_GHC.
Require Import BiInt_logics.

Lemma extens_diff_sBIH : forall (p : V),
    (sBIH_rules (Singleton _ (# p), Neg (wNeg (# p)))).
Proof.
intro p. apply DNs with (ps:=[(Singleton _ (# p), #p)]).
intros. inversion H. subst. apply Ids. apply IdRule_I. apply In_singleton.
inversion H0. apply DNsRule_I.
Qed.

Theorem sBIH_extens_wBIH : forall s,
    (wBIH_rules s) -> (sBIH_rules s).
Proof.
intros s D. induction D.
(* Id *)
- inversion H. subst. apply Ids. apply IdRule_I. auto.
(* Ax *)
- inversion H. subst. apply Axs. apply AxRule_I. auto.
(* MP *)
- inversion H1. subst. assert (J1: List.In (Γ, A → B) [(Γ, A → B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A → B) J1). assert (J2: List.In (Γ, A) [(Γ, A → B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). apply MPs with (ps:=[(Γ, A → B); (Γ, A)]).
  intros. inversion H1. subst. auto. apply MPRule_I.
(* DN *)
- inversion H1. subst. assert (J1: List.In (Empty_set (BPropF V), A) [(Empty_set (BPropF V), A)]). apply in_eq.
  pose (H0 (Empty_set (BPropF V), A) J1). assert (Included _ (Empty_set _) Γ).
  intro. intro. inversion H2. pose (@sBIH_monot (Empty_set _, A) s Γ H2).
  apply DNs with (ps:=[(Γ, A)]). intros. inversion H3. subst.
  assumption. inversion H4. apply DNsRule_I.
Qed.

Theorem pair_sBIH_extens_wBIH : forall P,
    (wpair_derrec P) -> (spair_derrec P).
Proof.
intros P wpair.
unfold spair_derrec. unfold wpair_derrec in wpair.
destruct wpair. destruct H. destruct H0. exists x. repeat split ; auto.
apply sBIH_extens_wBIH. auto.
Qed.

Theorem sBIH_same_thms_wBIH : forall s,
    (sBIH_rules s) ->
    (forall A, ((Empty_set _, A) = s) -> (wBIH_rules s)).
Proof.
intros s D. induction D.
(* Ids *)
- intros A id. inversion H. subst. inversion H2. subst.
  apply Id. apply IdRule_I. auto.
(* Axs *)
- intros A id. inversion H. subst. inversion H2. subst.
  apply Ax. apply AxRule_I. auto.
(* MPs *)
- intros A id. inversion H1. subst. inversion H3. subst.
  assert (J1: List.In (Empty_set (BPropF V), A0 → A) [(Empty_set (BPropF V), A0 → A); (Empty_set (BPropF V), A0)]). apply in_eq.
  pose (H0 (Empty_set (BPropF V), A0 → A) J1).
  assert (J2: List.In (Empty_set (BPropF V), A0) [(Empty_set (BPropF V), A0 → A); (Empty_set (BPropF V), A0)]). apply in_cons. apply in_eq.
  pose (H0 (Empty_set (BPropF V), A0) J2).
  apply MP with (ps:=[(Empty_set _, A0 → A); (Empty_set _, A0)]).
  intros. inversion H2. subst. apply w with (A1:=A0 → A). auto.
  inversion H4. subst. apply w0 with (A:=A0). auto. inversion H5. apply MPRule_I.
(* DNs *)
- intros A id. inversion H1. subst. inversion H3. subst.
  assert (J1: List.In (Empty_set (BPropF V), A0) [(Empty_set (BPropF V), A0)]). apply in_eq.
  pose (H0 (Empty_set (BPropF V), A0) J1).
  apply DNw with (ps:=[(Empty_set _, A0)]). intros. inversion H2. subst.
  apply w with (A:=A0). auto. inversion H4. apply DNwRule_I.
Qed.

Theorem wBIH_same_thms_sBIH : forall s,
    (wBIH_rules s) ->
    (forall A, ((Empty_set _, A) = s) -> (sBIH_rules s)).
Proof.
intros. apply sBIH_extens_wBIH. assumption.
Qed.

