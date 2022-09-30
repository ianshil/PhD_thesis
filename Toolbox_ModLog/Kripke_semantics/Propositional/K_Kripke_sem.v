Require Import Classical.
(* Used in the decidability of the forcing relation. *)

Require Import List.
Export ListNotations.

Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import K_Syntax.


    Class kmodel :=
      {
        nodes : Type ;
        reachable : nodes -> nodes -> Prop ;
        val : nodes ->V -> Prop ;
      }.

Fixpoint wforces (M : kmodel) w (A : MPropF) : Prop :=
      match A with
      | # p => val w p
      | Bot => False
      | A --> B => (wforces M w A) -> (wforces M w B)
      | Box A => forall v, reachable w v -> wforces M v A
      end.

Definition mforces M (A : MPropF) : Prop := forall w , wforces M w A.

Definition valid_form A := forall M, mforces M A.

Definition loc_conseq (Γ : Ensemble MPropF) (A : MPropF) :=
  forall M w, (forall B, (In _ Γ B) -> wforces M w B) -> (wforces M w A).

Definition glob_conseq (Γ : Ensemble MPropF) (A : MPropF) :=
  forall M, (forall B, (In _ Γ B) -> mforces M B) -> (mforces M A).
