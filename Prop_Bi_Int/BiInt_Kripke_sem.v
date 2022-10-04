Require Import Classical.
(* Used in the decidability of the forcing relation. *)

Require Import List.
Export ListNotations.

Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import BiInt_GHC.

    Class model :=
      {
        nodes : Type ;
        reachable : nodes -> nodes -> Prop ;
        val : nodes -> V -> Prop ;

        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        persist :  forall u v, reachable u v -> forall p, val u p -> val v p;
      }.

Fixpoint wforces (M : model) w (A : BPropF V) : Prop :=
  match A with
  | Var p => val w p
  | Bot _ => False
  | Top _ => True
  | And A B => (wforces M w A) /\ (wforces M w B)
  | Or A B => (wforces M w A) \/ (wforces M w B)
  | Imp A B => forall v, reachable w v -> wforces M v A -> wforces M v B
  | Excl A B => exists v, (reachable v w) /\ wforces M v A /\ (wforces M v B -> False)
  end.

Definition mforces M (A : BPropF V) : Prop := forall w, wforces M w A.

Definition valid_form A := forall M, mforces M A.

Definition loc_conseq (Γ Δ : @Ensemble (BPropF V)) :=
  forall M w,
    (forall A, (In _ Γ A) -> wforces M w A) ->
    (exists B, (In _ Δ B) /\ (wforces M w B)).

Definition glob_conseq (Γ Δ : @Ensemble (BPropF V)) :=
  forall M,
    (forall A, (In _ Γ A) -> mforces M A) ->
    (forall w, (exists B, (In _ Δ B) /\ (wforces M w B))).

Lemma Persistence : forall A M w, wforces M w A ->
            (forall v, reachable w v -> wforces M v A).
Proof.
induction A ; intros ; try auto.
- simpl. pose ((@persist M) w0 v).
  pose (v0 H0 w). apply v1. auto.
- simpl. split. inversion H. apply IHA1 with (w:=w) ; auto.
  inversion H. apply IHA2 with (w:=w) ; auto.
- simpl. inversion H. left. apply IHA1 with (w:=w) ; auto.
  right. apply IHA2 with (w:=w) ; auto.
- simpl. intros. simpl in H. apply H with (v:=v0) ; auto.
  pose ((@reach_tran) _ _ _ _ H0 H1). auto.
- simpl. simpl in H. destruct H. destruct H. exists x. split.
  pose ((@reach_tran) _ _ _ _ H H0). auto. auto.
Qed.

(* This useful later on, in the proofs of soundness and completeness. *)

Lemma wforces_dec : forall A M w,
    (wforces M w A) \/ ((wforces M w A) -> False).
Proof.
intros. apply classic.
Qed.