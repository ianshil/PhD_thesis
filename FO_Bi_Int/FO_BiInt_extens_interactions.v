Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Ensembles.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_logics.

Section Extens.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Lemma extens_diff_FOsBIH : forall P vec,
    (FOsBIH_rules (Singleton _ (atom P vec), ¬ ∞ (atom P vec))).
Proof.
intros. apply DNs with (ps:=[(Singleton _ (atom P vec), atom P vec)]).
intros. inversion H. subst. apply Ids. apply IdRule_I. apply In_singleton.
inversion H0. apply DNsRule_I.
Qed.

Theorem FOsBIH_extens_FOwBIH : forall s,
    (FOwBIH_rules s) -> (FOsBIH_rules s).
Proof.
intros s D. induction D.
(* Id *)
- inversion H. subst. apply Ids. apply IdRule_I. auto.
(* Ax *)
- inversion H. subst. apply Axs. apply AxRule_I. auto.
(* MP *)
- inversion H1. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1). assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). apply MPs with (ps:=[(Γ, A --> B); (Γ, A)]).
  intros. inversion H1. subst. auto. apply MPRule_I.
(* DNw *)
- inversion H1. subst. assert (J1: List.In (Empty_set form, A) ((Empty_set _, A) :: nil)). apply in_eq.
  pose (H0 (Empty_set _ , A) J1). pose (FOsBIH_monot (Empty_set _ , A) f Γ). simpl in f0.
  apply DNs with (ps:=[(Γ, A)]). intros. inversion H2. subst. apply f0.
  intro. intro. inversion H3. inversion H3. apply DNsRule_I.
(* Gen *)
- inversion H1. subst. assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1). apply Gens with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A)]). intros. inversion H2. subst.
  assumption. inversion H3. apply GenRule_I.
(* EC *)
- inversion H1. subst. assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) J1). apply ECs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑])]). intros. inversion H2. subst.
  assumption. inversion H3. apply ECRule_I.
Qed.

Theorem pair_FOsBIH_extens_FOwBIH : forall P,
    (wpair_der P) -> (spair_der P).
Proof.
intros P wpair.
unfold spair_der. unfold wpair_der in wpair.
destruct wpair. destruct H. destruct H0. exists x. repeat split ; auto.
apply FOsBIH_extens_FOwBIH. auto.
Qed.

Theorem FOsBIH_same_thms_FOwBIH : forall s,
    (FOsBIH_rules s) ->
    (forall A, ((Empty_set _, A) = s) -> (FOwBIH_rules s)).
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
  assert (J1: List.In (@Empty_set form, A0 --> A) ((Empty_set _, A0 --> A) :: (Empty_set _, A0) :: nil)). apply in_eq.
  pose (H0 (Empty_set _, A0 --> A) J1).
  assert (J2: List.In (@Empty_set form, A0) ((Empty_set _, A0 --> A) :: (Empty_set _, A0) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Empty_set _, A0) J2).
  apply MP with (ps:=[(Empty_set _, A0 --> A); (Empty_set _, A0)]).
  intros. inversion H2. subst. apply f with (A1:=A0 --> A). auto.
  inversion H4. subst. apply f0 with (A:=A0). auto. inversion H5. apply MPRule_I.
(* DNs *)
- intros A id. inversion H1. subst. inversion H3. subst.
  assert (J1: List.In (@Empty_set form, A0) ((Empty_set _, A0) :: nil)). apply in_eq.
  pose (H0 (Empty_set _, A0) J1).
  apply DNw with (ps:=[(Empty_set _, A0)]). intros. inversion H2. subst.
  apply f with (A:=A0). auto. inversion H4. apply DNwRule_I.
(* Gen *)
- intros A id. inversion H1. subst. inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0) ((fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0) J1 A0). apply Gen with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0)]). intros. inversion H2. subst.
  2: inversion H4. apply f ; auto. assert (Empty_set form = fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B).
  apply Extensionality_Ensembles. split ; intro ; intro ; inversion H4.
  destruct H5. subst. inversion H6. rewrite <- H4. auto. apply GenRule_I.
(* EC *)
- intros A id. inversion H1. subst. inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0 --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0 --> B[↑]) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0 --> B[↑]) J1 (A0 --> B[↑])). apply EC with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B, A0 --> B[↑])]). intros. inversion H2. subst.
  2: inversion H4. apply f ; auto.
  assert (Empty_set form = fun x : form => exists B : form, x = B[↑] /\ In form (Empty_set form) B).
  apply Extensionality_Ensembles. split ; intro ; intro ; inversion H4.
  destruct H5. subst. inversion H6. rewrite <- H4. auto. apply ECRule_I.
Qed.

Theorem FOwBIH_same_thms_FOsBIH : forall s,
    (FOwBIH_rules s) ->
    (forall A, ((Empty_set _, A) = s) -> (FOsBIH_rules s)).
Proof.
intros. apply FOsBIH_extens_FOwBIH. assumption.
Qed.

End Extens.

