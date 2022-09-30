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

Lemma sThm_irrel : forall A B Γ, sKH_prv (Γ, A --> (B --> A)).
Proof.
intros. apply sKH_extens_wKH. apply wThm_irrel.
Qed.

Lemma simp_Id_gen : forall A Γ, sKH_prv (Γ, A --> A).
Proof.
intros. apply sKH_extens_wKH. apply wimp_Id_gen.
Qed.

Lemma sImp_Box_power_le : forall (m n : nat) (A B : MPropF) Γ, (n <= m) ->
  sKH_prv (Γ, (Imp_Box_power n A B) --> (Imp_Box_power m A B)).
Proof.
intros.
pose (sKH_monot (Empty_set _, Imp_Box_power n A B --> Imp_Box_power m A B)).
apply s. apply sKH_extens_wKH. apply Imp_Box_power_le ; auto.
intro. intros. simpl in H0. inversion H0.
Qed.

Lemma sImp_Box_power_MP_deep : forall (n : nat) (A B C : MPropF) Γ,
  sKH_prv (Γ, (Imp_Box_power n A B) --> (Imp_Box_power n A (B --> C)) --> (Imp_Box_power n A C)).
Proof.
intros.
pose (sKH_monot (Empty_set _, (Imp_Box_power n A B) --> (Imp_Box_power n A (B --> C)) --> (Imp_Box_power n A C))).
apply s. apply sKH_extens_wKH. apply Imp_Box_power_MP_deep.
intro. intros. simpl in H. inversion H.
Qed.

Lemma sDistrib_Box_Imp_Box_power : forall (n : nat) (A B : MPropF) Γ,
  sKH_prv (Γ, (Box (Imp_Box_power n A B)) --> (Imp_Box_power n (Box A) (Box B))).
Proof.
intros.
pose (sKH_monot (Empty_set _, Box (Imp_Box_power n A B) --> Imp_Box_power n (Box A) (Box B))).
apply s. apply sKH_extens_wKH. apply Distrib_Box_Imp_Box_power.
intro. intros. simpl in H. inversion H.
Qed.

Theorem sKH_Detachment_Theorem : forall s,
           (sKH_prv s) ->
           (forall A B Γ, (fst s = Γ) ->
                          (snd s = A --> B) ->
                          sKH_prv (Union _ Γ (Singleton _ (A)), B)).
Proof.
intros s D. induction D.
(* Ids *)
* intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst.
  simpl. apply MPs with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A B);(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ids.
  apply IdRule_I. apply Union_introl. assumption. inversion H2. subst.
  apply Ids. apply IdRule_I. apply Union_intror. apply In_singleton. inversion H3.
(* Axs *)
* intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst. simpl.
  apply MPs with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A B);(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Axs.
  apply AxRule_I. assumption. inversion H2. subst. apply Ids. apply IdRule_I.
  apply Union_intror. apply In_singleton. inversion H3.
(* MPs *)
* intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. simpl.
  assert (J01: List.In (Γ0, A0 --> A --> B) [(Γ0, A0 --> A --> B); (Γ0, A0)]). apply in_eq.
  assert (J02: List.In (Γ0, A0) [(Γ0, A0 --> A --> B); (Γ0, A0)]). apply in_cons. apply in_eq.
  assert (J1: Γ0 = Γ0). reflexivity.
  assert (J2: A0 --> A --> B = A0 --> A --> B). reflexivity.
  pose (H0 (Γ0, A0 --> A --> B) J01 A0 (Imp A B) Γ0 J1 J2).
  assert (sKH_prv (Γ0, A --> B)).
  assert (J3: (forall A1 : MPropF, fst (Union _ Γ0 (Singleton _ A0), A --> B) A1 ->
  sKH_prv (Γ0, A1))).
  intro. simpl. intro. inversion H2. subst. apply Ids.
  apply IdRule_I. assumption. subst. inversion H3. subst.
  apply H. apply in_cons. apply in_eq.
  pose (sKH_comp (Union _ Γ0 (Singleton _ A0), A --> B) s Γ0 J3). simpl in s0. assumption.
  apply MPs with (ps:=[(Union _ Γ0 (Singleton _ A), (Imp A B));(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MPs with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A0 (Imp A B));(Union _ Γ0 (Singleton _ A), A0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  assert (J4: Included _ (fst (Γ0, A0 --> A --> B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption.
  pose (H _ J01).
  pose (sKH_monot (Γ0, A0 --> A --> B) s0 (Union _ Γ0 (Singleton _ A)) J4). assumption.
  inversion H5. subst. pose (H _ J02).
  assert (J4: Included _ (fst (Γ0, A0 --> A --> B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption.
  pose (sKH_monot (Γ0, A0) s0 (Union _ Γ0 (Singleton _ A)) J4). simpl in s1.
  assumption. inversion H6. inversion H4. subst. apply Ids. apply IdRule_I. apply Union_intror. apply In_singleton.
  inversion H5.
(* sNec *)
* intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. inversion id2.
Qed.

Theorem sKH_Deduction_Theorem : forall s,
           (sKH_prv s) ->
           (forall A B Γ, (fst s = Union _ Γ (Singleton _ (A))) ->
                          (snd s = B) ->
                          (exists n, sKH_prv (Γ, (Imp_Box_power n A B)))).
Proof.
intros s D. induction D.
(* Ids *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. exists 0. inversion H0.
  + subst. apply MPs with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H2. subst.
    apply sThm_irrel. inversion H3. subst.
    apply Ids. apply IdRule_I. assumption. inversion H4.
  + subst. inversion H1. subst. apply simp_Id_gen.
(* Axs *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. exists 0.
  apply MPs with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply sThm_irrel. inversion H2. subst.
  apply Axs. apply AxRule_I. assumption. inversion H3.
(* MPs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J01: List.In (Union (MPropF) Γ (Singleton (MPropF) A), A0 --> B0) [(Union (MPropF) Γ (Singleton (MPropF) A), A0 --> B0); (Union (MPropF) Γ (Singleton (MPropF) A), A0)]).
  apply in_eq.
  assert (J02: List.In (Union (MPropF) Γ (Singleton (MPropF) A), A0) [(Union (MPropF) Γ (Singleton (MPropF) A), A0 --> B0); (Union (MPropF) Γ (Singleton (MPropF) A), A0)]).
  apply in_cons. apply in_eq.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 --> B0 = A0 --> B0). reflexivity.
  pose (H0 (Union (MPropF) Γ (Singleton (MPropF) A), A0 --> B0) J01 A (Imp A0 B0) Γ J1 J2).
  destruct e. subst.
  assert (J3: A0 = A0). reflexivity.
  pose (H0 (Union (MPropF) Γ (Singleton (MPropF) A), A0) J02 A A0 Γ J1 J3). destruct e.
  exists (max x x0).
  apply MPs with (ps:=[(Γ, (Imp_Box_power (Init.Nat.max x x0) A (A0 --> B0)) --> (Imp_Box_power (Init.Nat.max x x0) A B0));
  (Γ, (Imp_Box_power (Init.Nat.max x x0) A (A0 --> B0)))]). 2: apply MPRule_I.
  intros. inversion H4. subst.
  apply MPs with (ps:=[(Γ, (Imp_Box_power (Init.Nat.max x x0) A A0) --> (Imp_Box_power (Init.Nat.max x x0) A (A0 --> B0)) --> (Imp_Box_power (Init.Nat.max x x0) A B0));
  (Γ, (Imp_Box_power (Init.Nat.max x x0) A A0))]). 2: apply MPRule_I.
  intros. inversion H5. subst. apply sImp_Box_power_MP_deep. inversion H6.
  subst.
  apply MPs with (ps:=[(Γ, (Imp_Box_power x0 A A0) --> (Imp_Box_power (Init.Nat.max x x0) A A0));
  (Γ, Imp_Box_power x0 A A0)]). 2: apply MPRule_I.
  intros. inversion H7. subst. apply sImp_Box_power_le ; lia.
  inversion H8. subst. auto. inversion H9. inversion H7.
  inversion H5. subst.
  apply MPs with (ps:=[(Γ, (Imp_Box_power x A (A0 --> B0)) --> (Imp_Box_power (Init.Nat.max x x0) A (A0 --> B0)));
  (Γ, Imp_Box_power x A (A0 --> B0))]). 2: apply MPRule_I.
  intros. inversion H6. subst. apply sImp_Box_power_le ; lia.
  inversion H7. subst. auto. inversion H8. inversion H6.
(* sNec *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J01: List.In (Union (MPropF) Γ (Singleton (MPropF) A), A0) [(Union (MPropF) Γ (Singleton (MPropF) A), A0)]).
  apply in_eq.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 = A0). reflexivity.
  pose (H0 (Union (MPropF) Γ (Singleton (MPropF) A), A0) J01 A A0 Γ J1 J2). destruct e.
  exists (S x). simpl.
  apply MPs with (ps:=[(Γ, (Imp_Box_power x (Box A) (Box A0)) --> A --> (Imp_Box_power x (Box A) (Box A0)));
  (Γ, Imp_Box_power x (Box A) (Box A0))]). 2: apply MPRule_I.
  intros. inversion H3. subst. apply Axs. apply AxRule_I. apply MA2_I.
  exists ((Imp_Box_power x (Box A) (Box A0))). exists A. auto. inversion H4 ; subst.
  2: inversion H5.
  apply MPs with (ps:=[(Γ, (Box (Imp_Box_power x A A0)) --> (Imp_Box_power x (Box A) (Box A0)));
  (Γ, Box (Imp_Box_power x A A0))]). 2: apply MPRule_I.
  intros. inversion H5. subst. apply sDistrib_Box_Imp_Box_power.
  inversion H6 ; subst. 2: inversion H7.
  apply sNec with (ps:=[(Γ, Imp_Box_power x A A0)]).
  2: apply sNecRule_I. intros. inversion H7. 2: inversion H8.
  subst. auto.
Qed.

Theorem sKH_Boxed_Detachment_Theorem : forall n A B Γ,
      (sKH_prv (Γ, (Imp_Box_power n A B))) ->
      (sKH_prv (Union _ Γ (Singleton _ (A)), B)).
Proof.
induction n.
- intros. simpl in H.
  apply sKH_Detachment_Theorem with (s:=(Γ, A --> B)) ; auto.
- intros. simpl in H.
  assert (J1: sKH_prv (Union MPropF Γ (Singleton MPropF A), Imp_Box_power n (Box A) B)).
  apply MPs with (ps:=[(Union MPropF Γ (Singleton MPropF A), A --> Imp_Box_power n (Box A) B);
  (Union MPropF Γ (Singleton MPropF A), A)]). 2: apply MPRule_I.
  intros. inversion H0. subst.
  apply sKH_monot with (Γ1:=Union MPropF Γ (Singleton MPropF A)) in H.
  apply H ; auto. simpl ; intro ; intro. apply Union_introl ; auto. inversion H1.
  2: inversion H2. subst. apply Ids. apply IdRule_I. apply Union_intror. apply In_singleton.
  pose (IHn (Box A) B (Union MPropF Γ (Singleton MPropF A)) J1).
  pose (sKH_comp (Union MPropF (Union MPropF Γ (Singleton MPropF A)) (Singleton MPropF (Box A)), B)
  s (Union MPropF Γ (Singleton MPropF A))). apply s0.
  simpl. intros. clear s0. inversion H0. subst. inversion H1.
  subst. apply Ids. apply IdRule_I. apply Union_introl ; auto.
  subst. inversion H2. subst.
  apply Ids. apply IdRule_I. apply Union_intror ; auto.
  subst. inversion H1. subst.
  apply sNec with (ps:=[(Union MPropF Γ (Singleton MPropF A), A)]).
  2: apply sNecRule_I. intros. inversion H2. 2: inversion H3. subst.
  apply Ids. apply IdRule_I. apply Union_intror. apply In_singleton.
Qed.


Theorem sKH_Boxed_Detachment_Deduction_Theorem : forall A B Γ,
      (sKH_prv (Union _ Γ (Singleton _ (A)), B)) <->
      (exists n, sKH_prv (Γ, (Imp_Box_power n A B))).
Proof.
intros. split ; intro.
apply sKH_Deduction_Theorem with (s:=(Union MPropF Γ (Singleton MPropF A), B)) ; auto.
destruct H. apply sKH_Boxed_Detachment_Theorem with (n:=x). auto.
Qed.
