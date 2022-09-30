Require Import List.
Export ListNotations.

Require Import PeanoNat.

Require Import Ensembles.
Require Import K_Syntax.
Require Import K_GHC.
Require Import K_logics.

Lemma extens_diff_sKH : forall (p : V),
    sKH_prv (Singleton _ (# p), Box (# p)).
Proof.
intro p. apply sNec with (ps:=[(Singleton _ (# p), #p)]).
intros. inversion H. subst. apply Ids. apply IdRule_I. apply In_singleton.
inversion H0. apply sNecRule_I.
Qed.

Theorem sKH_extens_wKH : forall s,
    (wKH_prv s) -> (sKH_prv s).
Proof.
intros s D. induction D.
(* Id *)
- inversion H. subst. apply Ids. apply IdRule_I. auto.
(* Ax *)
- inversion H. subst. apply Axs. apply AxRule_I. auto.
(* MP *)
- inversion H1. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1). assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). apply MPs with (ps:=[(Γ, A --> B); (Γ, A)]).
  intros. inversion H2. subst. auto. inversion H3. subst. auto. inversion H4. apply MPRule_I.
(* wNec *)
- inversion H1. subst. assert (J1: List.In (Empty_set MPropF, A) [(Empty_set MPropF, A)]). apply in_eq.
  pose (H0 (Empty_set MPropF, A) J1). assert (Included _ (Empty_set _) Γ).
  intro. intro. inversion H2. pose (@sKH_monot (Empty_set _, A) s Γ H2).
  apply sNec with (ps:=[(Γ, A)]). intros. inversion H3. subst.
  assumption. inversion H4. apply sNecRule_I.
Qed.

Theorem sKH_same_thms_wKH : forall s,
    (sKH_prv s) ->
    (forall A, ((Empty_set _, A) = s) -> (wKH_prv s)).
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
  assert (J1: List.In (Empty_set MPropF, A0 --> A) [(Empty_set MPropF, A0 --> A); (Empty_set MPropF, A0)]). apply in_eq.
  pose (H0 (Empty_set MPropF, A0 --> A) J1).
  assert (J2: List.In (Empty_set MPropF, A0) [(Empty_set MPropF, A0 --> A); (Empty_set MPropF, A0)]). apply in_cons. apply in_eq.
  pose (H0 (Empty_set MPropF, A0) J2).
  apply MP with (ps:=[(Empty_set _, A0 --> A); (Empty_set _, A0)]).
  intros. inversion H2. subst. apply w with (A1:=A0 --> A). auto.
  inversion H4. subst. apply w0 with (A:=A0). auto. inversion H5. apply MPRule_I.
(* sNec *)
- intros A id. inversion H1. subst. inversion H3. subst.
  assert (J1: List.In (Empty_set MPropF, A0) [(Empty_set MPropF, A0)]). apply in_eq.
  pose (H0 (Empty_set MPropF, A0) J1).
  apply wNec with (ps:=[(Empty_set _, A0)]). intros. inversion H2. subst.
  apply w with (A:=A0). auto. inversion H4. apply wNecRule_I.
Qed.

Theorem wKH_same_thms_sKH : forall s,
    (wKH_prv s) ->
    (forall A, ((Empty_set _, A) = s) -> (sKH_prv s)).
Proof.
intros. apply sKH_extens_wKH. assumption.
Qed.

Theorem wKH_sKH_same_thms : forall A,
    wKH_prv (Empty_set _, A) <-> sKH_prv (Empty_set _, A).
Proof.
intros. split ; intro. apply wKH_same_thms_sKH with (A:=A) ; auto.
apply sKH_same_thms_wKH with (A:=A) ; auto.
Qed.

