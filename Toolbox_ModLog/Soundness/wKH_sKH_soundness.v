Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Classical.

Require Import Ensembles.
Require Import K_Syntax.
Require Import K_GHC.
Require Import K_Kripke_sem.


Lemma Ax_valid : forall A, KAxioms A -> (forall M w, wforces M w A).
Proof.
intros A Ax. inversion Ax ; destruct H ; subst ; simpl ; intros ; auto.
- destruct H ; destruct H ; subst ; simpl ; intros ; auto.
- destruct H ; subst ; simpl ; intros ; auto.
- destruct H ; subst ; simpl. intros.
  destruct (classic (wforces M w x)) ; auto.
  assert ((wforces M w x -> wforces M w x0) -> False).
  intros. apply H0. auto. apply H. intros. exfalso ; auto.
- destruct H ; subst ; simpl ; intros ; auto.
- destruct H ; subst ; simpl ; intros ; auto.
Qed.

Theorem wSoundness0 : forall s, (wKH_prv s) ->
        (loc_conseq (fst s) (snd s)).
Proof.
intros s D. induction D.
(* Id *)
- inversion H. subst. simpl. intro. intros. apply H1. assumption.
(* Ax *)
- inversion H. subst. simpl. intro. intros. apply Ax_valid. assumption.
(* MP *)
- inversion H1. subst. simpl. assert (J1: loc_conseq Γ (A --> B)).
  apply H0 with (prem:=(Γ, A --> B)). apply in_eq.
  assert (J2: loc_conseq Γ A).
  apply H0 with (prem:=(Γ, A)). apply in_cons. apply in_eq.
  intro. intros. unfold loc_conseq in J1.
  pose (J1 M w H2). simpl in w0. apply w0.
  pose (J2 M w H2). auto.
(* DNw *)
- inversion H1. subst. simpl. assert (J1: loc_conseq (Empty_set _) A).
  apply H0 with (prem:=(Empty_set _, A)) ; apply in_eq.
  intro. intros. simpl. intros.
  assert (J2: (forall A, In _ (Empty_set _) A -> wforces M v A)).
  intros. inversion H4.
  pose (J1 M v J2). auto.
Qed.

Theorem wSoundness : forall Γ A, wKH_prv (Γ, A) -> (loc_conseq Γ A).
Proof.
intros. apply wSoundness0 in H ; auto.
Qed.

Theorem sSoundness0 : forall s, (sKH_prv s) ->
        (glob_conseq (fst s) (snd s)).
Proof.
intros s D. induction D.
(* Ids *)
- inversion H. subst. simpl. intro. intros. apply H1. assumption.
(* Axs *)
- inversion H. subst. simpl. intro. intros. unfold mforces. apply Ax_valid. assumption.
(* MPs *)
- inversion H1. subst. simpl. assert (J1: glob_conseq Γ (A --> B)).
  apply H0 with (prem:=(Γ, A --> B)). apply in_eq.
  assert (J2: glob_conseq Γ A).
  apply H0 with (prem:=(Γ, A)). apply in_cons. apply in_eq.
  intro. intros. unfold glob_conseq in J1.
  pose (J1 M H2). intro.
  pose (J2 M H2). apply m. apply m0.
(* DNs *)
- inversion H1. subst. simpl. assert (J1: glob_conseq Γ A).
  apply H0 with (prem:=(Γ, A)) ; apply in_eq.
  intro. intros. intro. pose (J1 M H2). intro. intro. apply m.
Qed.

Theorem sSoundness : forall Γ A, sKH_prv (Γ, A) -> (glob_conseq Γ A).
Proof.
intros. apply sSoundness0 in H ; auto.
Qed.

(* Consequences of soundness results. *)

Variable p : V.

Definition nat_val n (q : V) : Prop := n = 0.

Instance M : kmodel :=
      {|
        nodes := nat ;
        reachable := lt ;
        val := nat_val
      |}.

Lemma Consequences_Soundness1 :
  exists s, (sKH_prv s) /\ ((wKH_prv s) -> False).
Proof.
exists (Singleton _ # p , Box # p). split.
apply sNec with (ps:=[(Singleton MPropF # p, # p)]).
2: apply sNecRule_I. intros. inversion H ; subst. 2: inversion H0.
apply Ids. apply IdRule_I. apply In_singleton.
intro. apply wSoundness in H.
assert (J0: forall B : MPropF, In MPropF (Singleton MPropF # p) B -> wforces M 0 B).
intros. inversion H0. cbn. unfold nat_val. auto.
pose (H M 0 J0).
simpl in w. assert (J1: 0 < 1). lia.
pose (w 1 J1). unfold nat_val in n. inversion n.
Qed.

Lemma Consequences_Soundness2 :
  (sKH_prv (Singleton _ # p , Box # p)) /\ ((sKH_prv (Empty_set _, (# p) --> (Box # p))) -> False).
Proof.
split.
apply sNec with (ps:=[(Singleton MPropF # p, # p)]).
2: apply sNecRule_I. intros. inversion H ; subst. 2: inversion H0.
apply Ids. apply IdRule_I. apply In_singleton.
intro. apply sSoundness in H.
assert (J0: forall B : MPropF, In MPropF (Empty_set MPropF) B -> mforces M B).
intros. inversion H0.
pose (H M J0).
pose (m 0). simpl in w.
assert (J1: nat_val 0 p). unfold nat_val ; auto.
assert (J2: 0 < 1). lia.
pose (w J1 1 J2). unfold nat_val in n. inversion n.
Qed.



