Require Import List.
Export ListNotations.

Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import BiInt_extens_interactions.
Require Import wBIH_meta_interactions.

Lemma sThm_irrel : forall A B Γ, sBIH_rules (Γ, A → (B → A)).
Proof.
intros. apply sBIH_extens_wBIH. apply wThm_irrel.
Qed.

Lemma simp_Id_gen : forall A Γ, sBIH_rules (Γ, A → A).
Proof.
intros. apply sBIH_extens_wBIH. apply wimp_Id_gen.
Qed.

Lemma scomm_And_obj : forall A B Γ, (sBIH_rules (Γ, And A B → And B A)).
Proof.
intros. apply sBIH_extens_wBIH. apply comm_And_obj.
Qed.

Lemma sContr_Bot : forall A Γ, sBIH_rules (Γ, And A (Neg A) → (Bot V)).
Proof.
intros. apply sBIH_extens_wBIH. apply wContr_Bot.
Qed.

Lemma sEFQ : forall A Γ, sBIH_rules (Γ, (Bot V) → A).
Proof.
intros. apply sBIH_extens_wBIH. apply wEFQ.
Qed.

Lemma smonotR_Or : forall A B Γ, (sBIH_rules (Γ, A → B)) ->
    (forall C, sBIH_rules (Γ, (Or A C) → (Or B C))).
Proof.
intros A B Γ D C.
apply MPs with (ps:=[(Γ, (C → Or B C) → (Or A C → Or B C));(Γ,(C → Or B C))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (A → Or B C) → (C → Or B C) → (Or A C → Or B C));(Γ,(A → Or B C))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists A. exists C.
exists (Or B C). auto. inversion H1. subst.
apply MPs with (ps:=[(Γ, (B → Or B C) → (A → Or B C));(Γ,((B → Or B C)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, (A → B) → (B → Or B C) → (A → Or B C));(Γ,(A → B))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Axs.
apply AxRule_I. apply RA1_I. exists A. exists B. exists (Or B C). auto.
inversion H4. subst. assumption. inversion H5. inversion H3. subst. apply Axs.
apply AxRule_I. apply RA2_I. exists B. exists C.
auto. inversion H4. inversion H2. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA3_I.
exists B. exists C. auto. inversion H1.
Qed.

Lemma smonotL_Or : forall A B Γ,
    (sBIH_rules (Γ, A → B)) ->
    (forall C, sBIH_rules (Γ, (Or C A) → (Or C B))).
Proof.
intros A B Γ D C.
apply MPs with (ps:=[(Γ, (A → Or C B) → ((Or C A) → (Or C B)));(Γ,(A → Or C B))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (C → Or C B) → (A → Or C B) → ((Or C A) → (Or C B)));(Γ,(C → Or C B))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists C. exists A.
exists (Or C B). auto. inversion H1. subst. apply Axs.
apply AxRule_I. apply RA2_I. exists C. exists B.
auto. inversion H2. inversion H0. subst.
apply MPs with (ps:=[(Γ, (B → Or C B) → (A → Or C B));(Γ,((B → Or C B)))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply MPs with (ps:=[(Γ, (A → B) → (B → Or C B) → (A → Or C B));(Γ,(A → B))]).
2: apply MPRule_I. intros. inversion H2. subst. apply Axs.
apply AxRule_I. apply RA1_I. exists A. exists B. exists (Or C B). auto.
inversion H3. subst. assumption. inversion H4. inversion H2. subst. apply Axs.
apply AxRule_I. apply RA3_I. exists C. exists B.
auto. inversion H3. inversion H1.
Qed.

Lemma scomm_Or_obj : forall A B Γ, (sBIH_rules (Γ, Or A B → Or B A)).
Proof.
intros. apply sBIH_extens_wBIH. apply comm_Or_obj.
Qed.

Lemma scomm_Or : forall A B Γ,
    (sBIH_rules (Γ, Or A B)) ->
    (sBIH_rules (Γ, Or B A)).
Proof.
intros A B Γ D.
apply MPs with (ps:=[(Γ, Or A B → Or B A);(Γ, Or A B)]).
2: apply MPRule_I. intros. inversion H. subst.
apply scomm_Or_obj. inversion H0. subst. assumption.
inversion H1.
Qed.

Lemma smonot_Or2 : forall A B Γ,
    (sBIH_rules (Γ, A → B)) ->
    (forall C, sBIH_rules (Γ, (Or A C) → (Or C B))).
Proof.
intros A B Γ D C.
apply MPs with (ps:=[(Γ, (C → Or C B) → (Or A C → Or C B));(Γ, C → Or C B)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (A → Or C B) → (C → Or C B) → (Or A C → Or C B));(Γ, A → Or C B)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Axs.
apply AxRule_I. apply RA4_I. exists A. exists C. exists (Or C B). auto.
inversion H1. subst.
apply MPs with (ps:=[(Γ, (B → Or C B) → (A → Or C B));(Γ, B → Or C B)]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, (A → B) → (B → Or C B) → (A → Or C B));(Γ, A → B)]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists B. exists (Or C B).
auto. inversion H4. subst. assumption. inversion H5. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists C. exists B. auto.
inversion H4. inversion H2. inversion H0. subst. apply Axs. apply AxRule_I.
apply RA2_I. exists C. exists B. auto. inversion H1.
Qed.

Lemma sabsorp_Or1 : forall A Γ,
    (sBIH_rules (Γ, Or A (Bot V))) ->
    (sBIH_rules (Γ, A)).
Proof.
intros A Γ D.
apply MPs with (ps:=[(Γ, Imp (Or A (Bot V)) A);(Γ, Or A (Bot V))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (Bot V → A) → (Or A (Bot V) → A));(Γ, (Bot V → A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, (A → A) → (Bot V → A) → (Or A (Bot V) → A));(Γ, A → A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists A. exists (Bot V).
exists A. auto. inversion H2. subst. apply simp_Id_gen.
inversion H3. inversion H1. subst. apply sEFQ. inversion H2.
inversion H0. subst. assumption. inversion H1.
Qed.

Theorem sdual_residuation_gen : forall A B C Γ,
  (sBIH_rules (Γ, (Excl A B) → C) ->
      sBIH_rules (Γ, A → (Or B C))) *
  (sBIH_rules (Γ, A → (Or B C)) ->
      sBIH_rules (Γ, (Excl A B) → C)).
Proof.
intros A B C Γ. split.
- intro D. pose (@smonot_Or2 (Excl A B) C Γ D B).
  apply MPs with (ps:=[(Γ, (Or (Excl A B) B → Or B C) → (A → Or B C));(Γ,Or (Excl A B) B → Or B C)]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MPs with (ps:=[(Γ, (A → Or (Excl A B) B) → (Or (Excl A B) B → Or B C) → (A → Or B C));(Γ,(A → Or (Excl A B) B))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists A. exists (Or (Excl A B) B). exists (Or B C). auto.
  inversion H1. subst.
  apply MPs with (ps:=[(Γ, (Or B (Excl A B) → Or (Excl A B) B) → (A → Or (Excl A B) B));(Γ,(Or B (Excl A B) → Or (Excl A B) B))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MPs with (ps:=[(Γ, (A → Or B (Excl A B)) → (Or B (Excl A B) → Or (Excl A B) B) → (A → Or (Excl A B) B));(Γ,(A → Or B (Excl A B)))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists A. exists (Or B (Excl A B)). exists (Or (Excl A B) B).
  auto. inversion H4. subst.
  apply Axs. apply AxRule_I. apply RA11_I. exists A. exists B. auto. inversion H5.
  inversion H3. subst. apply scomm_Or_obj. inversion H4. inversion H2.
  inversion H0. subst. assumption. inversion H1.
- intro D. apply MPs with (ps:=[(Γ, ((Or C (Excl A (Or B C))) → C) → (Excl A B → C));(Γ, (Or C (Excl A (Or B C))) → C)]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MPs with (ps:=[(Γ, (Excl A B → (Or C (Excl A (Or B C)))) → ((Or C (Excl A (Or B C))) → C) → (Excl A B → C));(Γ, Excl A B → (Or C (Excl A (Or B C))))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Axs. apply AxRule_I. apply RA1_I.
  exists (Excl A B). exists (Or C (Excl A (Or B C))). exists C. auto. inversion H1. subst.
  apply MPs with (ps:=[(Γ, ((Or C (Excl (Excl A B) C)) → Or C (Excl A (Or B C))) → (Excl A B → Or C (Excl A (Or B C))));(Γ, ((Or C (Excl (Excl A B) C)) → Or C (Excl A (Or B C))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MPs with (ps:=[(Γ, (Excl A B → (Or C (Excl (Excl A B) C)))→ ((Or C (Excl (Excl A B) C)) → Or C (Excl A (Or B C))) → (Excl A B → Or C (Excl A (Or B C))));
  (Γ, (Excl A B → (Or C (Excl (Excl A B) C))))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (Excl A B). exists (Or C (Excl (Excl A B) C)).
  exists (Or C (Excl A (Or B C))). auto. inversion H4. subst.
  apply Axs. apply AxRule_I. apply RA11_I. exists (Excl A B). exists C. auto. inversion H5.
  inversion H3. subst. apply smonotL_Or. apply Axs. apply AxRule_I. apply RA13_I.
  exists A. exists B. exists C. auto. inversion H4. inversion H2. inversion H0. subst.
  apply MPs with (ps:=[(Γ, (Or C (Bot _) → C) → (Or C (Excl A (Or B C)) → C));
  (Γ, (Or C (Bot _) → C))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply MPs with (ps:=[(Γ, (Or C (Excl A (Or B C)) → Or C (Bot _)) → (Or C (Bot _) → C) → (Or C (Excl A (Or B C)) → C));
  (Γ, (Or C (Excl A (Or B C)) → Or C (Bot _)))]). 2: apply MPRule_I. intros. inversion H2. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (Or C (Excl A (Or B C))).
  exists (Or C (Bot V)). exists C. auto. inversion H3. subst. apply smonotL_Or.
  apply MPs with (ps:=[(Γ, ((And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))) → Bot V) → (Excl A (Or B C) → Bot V));
  (Γ, ((And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))) → Bot V))]). 2: apply MPRule_I. intros. inversion H4. subst.
  apply MPs with (ps:=[(Γ, (Excl A (Or B C) → (And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C))))) → ((And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))) → Bot V) → (Excl A (Or B C) → Bot V));
  (Γ, (Excl A (Or B C) → (And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C))))))]). 2: apply MPRule_I. intros. inversion H5. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (Excl A (Or B C)).
  exists (And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))). exists (Bot V). auto. inversion H6.
  subst.
  apply MPs with (ps:=[(Γ, (Excl A (Or B C) → (Neg (wNeg (A → Or B C)))) → (Excl A (Or B C) → And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))));
  (Γ, (Excl A (Or B C) → (Neg (wNeg (A → Or B C)))))]). 2: apply MPRule_I. intros. inversion H7. subst.
  apply MPs with (ps:=[(Γ, (Excl A (Or B C) → (wNeg (A → Or B C))) → (Excl A (Or B C) → (Neg (wNeg (A → Or B C)))) → (Excl A (Or B C) → And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))));
  (Γ, (Excl A (Or B C) → (wNeg (A → Or B C))))]). 2: apply MPRule_I. intros. inversion H8. subst.
  apply Axs. apply AxRule_I. apply RA7_I. exists (Excl A (Or B C)).
  exists (wNeg (A → Or B C)). exists (Neg (wNeg (A → Or B C))). auto. inversion H9. subst.
  apply Axs. apply AxRule_I. apply RA12_I. exists A. exists (Or B C).
  auto. inversion H10. inversion H8. inversion H9. subst.
  apply MPs with (ps:=[(Γ, (Neg (wNeg (A → Or B C))) → (Excl A (Or B C) → Neg (wNeg (A → Or B C))));
  (Γ, (Neg (wNeg (A → Or B C))))]). 2: apply MPRule_I. intros. inversion H9. subst.
  apply sThm_irrel. inversion H11. subst. apply DNs with (ps:=[(Γ, A → Or B C)]).
  2: apply DNsRule_I. intros. inversion H12. subst. assumption. inversion H13. inversion H12.
  inversion H9. inversion H7. inversion H5. subst. apply sContr_Bot. inversion H6.
  inversion H4. inversion H2. subst.
  apply MPs with (ps:=[(Γ, (Bot V → C) → (Or C (Bot V) → C));(Γ, (Bot V → C))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MPs with (ps:=[(Γ, (C → C) → (Bot V → C) → (Or C (Bot V) → C));(Γ, (C → C))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Axs.
  apply AxRule_I. apply RA4_I. exists C. exists (Bot V). exists C. auto.
  inversion H5. subst. apply simp_Id_gen. inversion H6. inversion H4. subst. apply sEFQ.
  inversion H5. inversion H3. inversion H1.
Qed.

Theorem sdual_residuation : forall A B C,
  (sBIH_rules (Empty_set _, (Excl A B) → C) ->
      sBIH_rules (Empty_set _, A → (Or B C))) *
  (sBIH_rules (Empty_set _, A → (Or B C)) ->
      sBIH_rules (Empty_set _, (Excl A B) → C)).
Proof.
intros. apply sdual_residuation_gen with (Γ:=Empty_set _).
Qed.

Theorem spair_dual_residuation_gen : forall A B C Γ,
  (spair_derrec (Γ, Singleton _ ((Excl A B) → C)) ->
      spair_derrec (Γ, Singleton _ (A → (Or B C)))) *
  (spair_derrec (Γ, Singleton _ (A → (Or B C))) ->
      spair_derrec (Γ, Singleton _ ((Excl A B) → C))).
Proof.
intros A B C Γ. split.
- intro. exists [(A → Or B C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. simpl. inversion H0. subst. apply In_singleton. inversion H1. inversion H1.
  * destruct H. destruct H. destruct H0. pose (sdual_residuation_gen A B C Γ). destruct p. clear s0. simpl.
    simpl in s. simpl in H1. simpl in H0. destruct x.
    + simpl in H1. apply MPs with (ps:=[(Γ, Bot V → Or (A → Or B C) (Bot V));(Γ, Bot V)]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Axs.
      apply AxRule_I. apply RA3_I. exists (A → Or B C). exists (Bot V). auto.
      inversion H3. subst. assumption. inversion H4.
    + assert (x=nil). inversion H. subst. assert (b = (Excl A B → C)). pose (H0 b).
      assert (List.In b (b :: x)). apply in_eq. apply s0 in H2. inversion H2. reflexivity.
      subst. destruct x. reflexivity. exfalso. apply H4. pose (H0 b).
      assert (List.In b (Excl A B → C :: b :: x)). apply in_cons. apply in_eq.
      apply s0 in H2. inversion H2. subst. apply in_eq. subst. simpl in H1. assert (b= Excl A B → C).
      pose (H0 b). assert (List.In b [b]). apply in_eq. apply s0 in H2. inversion H2. auto.
      subst. apply sabsorp_Or1 in H1. apply s in H1.
      apply MPs with (ps:=[(Γ, (A → Or B C) → (Or (A → Or B C) (Bot V)));(Γ, (A → Or B C))]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Axs. apply AxRule_I. apply RA2_I.
      exists (A → Or B C). exists (Bot V). auto. inversion H3. subst. assumption. inversion H4.
- intro. exists [(Excl A B → C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. simpl. inversion H0. subst. apply In_singleton. inversion H1. inversion H1.
  * destruct H. destruct H. destruct H0. pose (sdual_residuation_gen A B C Γ). destruct p. clear s. simpl.
    simpl in H1. simpl in s0. simpl in H0. destruct x.
    + simpl in H1. apply MPs with (ps:=[(Γ, Bot V → Or (Excl A B → C) (Bot V));(Γ, Bot V)]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Axs.
      apply AxRule_I. apply RA3_I. exists (Excl A B → C). exists (Bot V). auto.
      inversion H3. subst. assumption. inversion H4.
    + assert (x=nil). inversion H. subst. assert (b = (A → Or B C)). pose (H0 b).
      assert (List.In b (b :: x)). apply in_eq. apply s in H2. inversion H2. reflexivity.
      subst. destruct x. reflexivity. exfalso. apply H4. pose (H0 b).
      assert (List.In b (A → Or B C :: b :: x)). apply in_cons. apply in_eq.
      apply s in H2. inversion H2. subst. apply in_eq. subst. simpl in H1. assert (b= A → Or B C).
      pose (H0 b). assert (List.In b [b]). apply in_eq. apply s in H2. inversion H2. auto.
      subst. apply sabsorp_Or1 in H1. apply s0 in H1.
      apply MPs with (ps:=[(Γ, (Excl A B → C) → (Or (Excl A B → C) (Bot V)));(Γ, (Excl A B → C))]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Axs. apply AxRule_I. apply RA2_I.
      exists (Excl A B → C). exists (Bot V). auto. inversion H3. subst. assumption. inversion H4.
Qed.

Theorem sBIH_Detachment_Theorem : forall s,
           (sBIH_rules s) ->
           (forall A B Γ, (fst s = Γ) ->
                          (snd s = A → B) ->
                          sBIH_rules (Union _ Γ (Singleton _ (A)), B)).
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
  assert (J01: List.In (Γ0, A0 → A → B) [(Γ0, A0 → A → B); (Γ0, A0)]). apply in_eq.
  assert (J02: List.In (Γ0, A0) [(Γ0, A0 → A → B); (Γ0, A0)]). apply in_cons. apply in_eq.
  assert (J1: Γ0 = Γ0). reflexivity.
  assert (J2: A0 → A → B = A0 → A → B). reflexivity.
  pose (H0 (Γ0, A0 → A → B) J01 A0 (Imp A B) Γ0 J1 J2).
  assert (sBIH_rules (Γ0, A → B)).
  assert (J3: (forall A1 : BPropF V, fst (Union _ Γ0 (Singleton _ A0), A → B) A1 ->
  sBIH_rules (Γ0, A1))).
  intro. simpl. intro. inversion H2. subst. apply Ids.
  apply IdRule_I. assumption. subst. inversion H3. subst.
  apply H. apply in_cons. apply in_eq.
  pose (sBIH_comp (Union _ Γ0 (Singleton _ A0), A → B) s Γ0 J3). simpl in s0. assumption.
  apply MPs with (ps:=[(Union _ Γ0 (Singleton _ A), (Imp A B));(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MPs with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A0 (Imp A B));(Union _ Γ0 (Singleton _ A), A0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  assert (J4: Included _ (fst (Γ0, A0 → A → B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption.
  pose (H _ J01).
  pose (sBIH_monot (Γ0, A0 → A → B) s0 (Union _ Γ0 (Singleton _ A)) J4). assumption.
  inversion H5. subst. pose (H _ J02).
  assert (J4: Included _ (fst (Γ0, A0 → A → B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption.
  pose (sBIH_monot (Γ0, A0) s0 (Union _ Γ0 (Singleton _ A)) J4). simpl in s1.
  assumption. inversion H6. inversion H4. subst. apply Ids. apply IdRule_I. apply Union_intror. apply In_singleton.
  inversion H5.
(* DNs *)
* intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. inversion id2. subst. simpl.
  remember (Union (BPropF V) Γ0 (Singleton (BPropF V)  (wNeg A0))) as Γ.
  assert (J01: List.In (Γ0, A0) [(Γ0, A0)]). apply in_eq. apply H in J01.
  apply MPs with (ps:=[(Γ, (And (wNeg A0) (Neg (wNeg A0))) → Bot _); (Γ, And (wNeg A0) (Neg (wNeg A0)))]).
  2: apply MPRule_I. intros. inversion H2. rewrite <- H3. apply sContr_Bot. inversion H3.
  rewrite <- H4.
  apply MPs with (ps:=[(Γ,(Top V →  (And (wNeg A0) (Neg (wNeg A0)))));(Γ, Top V)]).
  2: apply MPRule_I. intros. inversion H5. rewrite <- H6.
  apply MPs with (ps:=[(Γ,(Top V → (Neg (wNeg A0))) →(Top V →  (And (wNeg A0) (Neg (wNeg A0)))));(Γ, Top V → (Neg (wNeg A0)))]).
  2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
  apply MPs with (ps:=[(Γ,(Top V → (wNeg A0)) → (Top V → (Neg (wNeg A0))) → (Top V → (And (wNeg A0) (Neg (wNeg A0)))));(Γ, Top V → (wNeg A0))]).
  2: apply MPRule_I. intros. inversion H9. rewrite <- H10. apply Axs. apply AxRule_I.
  apply RA7_I. exists (Top V). exists (wNeg A0). exists (Neg (wNeg A0)). auto. inversion H10. 2: inversion H11.
  rewrite <- H11.
  apply MPs with (ps:=[(Γ, wNeg A0 → Top V → wNeg A0);(Γ, wNeg A0)]). intros. 2: apply MPRule_I.
  inversion H12. rewrite <- H13. apply sThm_irrel. inversion H13. 2: inversion H14. rewrite <- H14.
  apply Ids. apply IdRule_I. subst. apply Union_intror. apply In_singleton.
  inversion H8. rewrite <- H9.
  apply MPs with (ps:=[(Γ, Neg (wNeg A0) → Top V → Neg (wNeg A0));(Γ, Neg (wNeg A0))]). intros. 2: apply MPRule_I.
  inversion H10. rewrite <- H11. apply sThm_irrel. inversion H11. 2: inversion H12. rewrite <- H12.
  apply DNs with (ps:=[(Γ, A0)]). intros. 2: apply DNsRule_I. inversion H13. subst.
  pose (sBIH_monot _ J01). apply s. simpl. intro. intros. apply Union_introl. auto. inversion H14.
  inversion H9. inversion H6. subst. apply sBIH_extens_wBIH. apply wTop. inversion H7. inversion H4.
Qed.

Theorem gen_sBIH_Detachment_Theorem : forall A B Γ,
  spair_derrec (Γ, Singleton _ (A → B)) ->
      spair_derrec (Union _ Γ (Singleton _ (A)), Singleton _ (B)).
Proof.
intros A B Γ spair. unfold spair_derrec. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H.
subst. simpl. apply In_singleton. inversion H0. simpl.
apply MPs with (ps:=[ (Union _ Γ (Singleton _ A), Imp B (Or B (Bot V))); (Union _ Γ (Singleton _ A), B)]).
2: apply MPRule_I. intros. inversion H. subst. apply Axs. apply AxRule_I.
apply RA2_I. exists B. exists (Bot V). auto. inversion H0. subst.
destruct spair. destruct H1. destruct H2. simpl in H3. simpl in H2. destruct x.
apply MPs with (ps:=[(Union _ Γ (Singleton _ A), Imp (Bot V) B);(Union _ Γ (Singleton _ A), (Bot V))]).
2: apply MPRule_I. intros. inversion H4. subst. apply sEFQ. inversion H5.
assert (J1: Included _ (fst (Γ, Bot V)) (Union _ Γ (Singleton _ A))). intro. intro. apply Union_introl.
assumption.
pose (sBIH_monot (Γ , Bot V) H3 (Union _ Γ (Singleton _ A)) J1). simpl in s. subst. assumption.
inversion H6.
destruct x. simpl in H3. assert (b=A → B). pose (H2 b). assert (List.In b [b]). apply in_eq.
apply s in H4. inversion H4. reflexivity. subst. apply sabsorp_Or1 in H3.
assert (J1: Γ = Γ). reflexivity.
assert (J2: A → B = A → B). reflexivity.
pose (sBIH_Detachment_Theorem (Γ, A → B) H3 A B Γ J1 J2). assumption.
exfalso. simpl in H3. inversion H1. apply H6. subst. pose (H2 b).
assert (List.In b (b :: b0 :: x)). apply in_eq. pose (s H4). inversion s0. subst.
pose (H2 b0). assert (List.In b0 (A → B :: b0 :: x)). apply in_cons. apply in_eq.
pose (s1 H5). inversion s2. subst. apply in_eq. inversion H1.
Qed.

Lemma sDN_to_form : forall A Γ, (sBIH_rules (Γ, Neg (wNeg A)→ A)).
Proof.
intros A Γ. apply sBIH_extens_wBIH. apply wDN_to_form.
Qed.

Lemma sT_for_DN : forall A n m Γ, (le m n) -> (sBIH_rules (Γ, (DN_form n A) → (DN_form m A))).
Proof.
intros. apply sBIH_extens_wBIH. apply wT_for_DN. assumption.
Qed.

Lemma sExcl_mon : forall A B C,
  (sBIH_rules (Empty_set _, A → B)) ->
  (sBIH_rules (Empty_set _, (Excl A C) → (Excl B C))).
Proof.
intros. apply sdual_residuation.
apply MPs with (ps:=[(Empty_set _, (B → Or C (Excl B C)) → (A → Or C (Excl B C)));
(Empty_set _, (B → Or C (Excl B C)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Empty_set _, (A → B) → (B → Or C (Excl B C)) → (A → Or C (Excl B C)));
(Empty_set _, (A → B))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (Or C (Excl B C)). auto. inversion H2. subst. assumption. inversion H3.
inversion H1. subst.
apply Axs. apply AxRule_I. apply RA11_I. exists B. exists C. auto. inversion H2.
Qed.

Lemma smon_Excl : forall A B C,
  (sBIH_rules (Empty_set _, A → B)) ->
  (sBIH_rules (Empty_set _, (Excl C B) → (Excl C A))).
Proof.
intros. apply sdual_residuation.
apply MPs with (ps:=[(Empty_set _, (Or A (Excl C A) → Or B (Excl C A)) → (C → Or B (Excl C A)));
(Empty_set _, (Or A (Excl C A) → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Empty_set _, (C → Or A (Excl C A)) → (Or A (Excl C A) → Or B (Excl C A)) → (C → Or B (Excl C A)));
(Empty_set _, C → Or A (Excl C A))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists C. exists (Or A (Excl C A)).
exists (Or B (Excl C A)). auto. inversion H2. subst.
apply Axs. apply AxRule_I. apply RA11_I. exists C. exists A.
auto. inversion H3. inversion H1. subst.
apply MPs with (ps:=[(Empty_set _, ((Excl C A) → Or B (Excl C A)) → (Or A (Excl C A) → Or B (Excl C A)));
(Empty_set _, ((Excl C A) → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Empty_set _, (A → Or B (Excl C A)) → ((Excl C A) → Or B (Excl C A)) → (Or A (Excl C A) → Or B (Excl C A)));
(Empty_set _, (A → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists A. exists (Excl C A).
exists (Or B (Excl C A)). auto. inversion H4. subst.
apply MPs with (ps:=[(Empty_set _, (B → Or B (Excl C A)) → (A → Or B (Excl C A)));
(Empty_set _, (B → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Empty_set _, (A → B) → (B → Or B (Excl C A)) → (A → Or B (Excl C A)));
(Empty_set _, (A → B))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (Or B (Excl C A)). auto. inversion H7. subst. assumption. inversion H8.
inversion H6. subst.
apply Axs. apply AxRule_I. apply RA2_I. exists B. exists (Excl C A). auto.
inversion H7. inversion H5. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists B. exists (Excl C A). auto.
inversion H4. inversion H2.
Qed.

Lemma sOr_Neg : forall A B C Γ,
  (sBIH_rules (Γ, A → (Or B C))) ->
  (sBIH_rules (Γ, (And (Neg B) A) → C)).
Proof.
intros.
apply MPs with (ps:=[(Γ, ((And (Neg B) (Or B C)) → C) → (And (Neg B) A → C));(Γ, And (Neg B) (Or B C) → C)]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, ((And (Neg B) A) → (And (Neg B) (Or B C))) → ((And (Neg B) (Or B C)) → C) → (And (Neg B) A → C));
(Γ, ((And (Neg B) A) → (And (Neg B) (Or B C))))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists (And (Neg B) A). exists (And (Neg B) (Or B C)).
exists C. auto. inversion H2. subst.
apply MPs with (ps:=[(Γ, (And (Neg B) A → (Or B C)) → (And (Neg B) A → And (Neg B) (Or B C)));
(Γ, (And (Neg B) A → (Or B C)))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply MPs with (ps:=[(Γ, (And (Neg B) A → (Neg B)) → (And (Neg B) A → (Or B C)) → (And (Neg B) A → And (Neg B) (Or B C)));
(Γ, (And (Neg B) A → (Neg B)))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Axs. apply AxRule_I. apply RA7_I. exists (And (Neg B) A). exists (Neg B).
exists (Or B C). auto. inversion H5. subst.
apply Axs. apply AxRule_I. apply RA5_I. exists (Neg B). exists A. auto.
inversion H6. inversion H4. subst.
apply MPs with (ps:=[(Γ, (A → Or B C) → (And (Neg B) A → Or B C));
(Γ, (A → Or B C))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Γ, (And (Neg B) A → A) → (A → Or B C) → (And (Neg B) A → Or B C));
(Γ, (And (Neg B) A → A))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists (And (Neg B) A). exists A.
exists (Or B C). auto. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA6_I. exists (Neg B). exists A. auto.
inversion H8. inversion H6. subst. assumption. inversion H7. inversion H5. inversion H3. inversion H1. subst.
apply MPs with (ps:=[(Γ, (And (Or B C) (Neg B) → C) → (And (Neg B) (Or B C) → C));
(Γ, (And (Or B C) (Neg B) → C))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, (And (Neg B) (Or B C) → And (Or B C) (Neg B)) → (And (Or B C) (Neg B) → C) → (And (Neg B) (Or B C) → C));
(Γ, And (Neg B) (Or B C) → And (Or B C) (Neg B))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists (And (Neg B) (Or B C)). exists (And (Or B C) (Neg B)).
exists C. auto. inversion H4. subst.
apply MPs with (ps:=[(Γ, (And (Neg B) (Or B C) → (Neg B)) → (And (Neg B) (Or B C) → And (Or B C) (Neg B)));
(Γ, (And (Neg B) (Or B C) → (Neg B)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Γ, (And (Neg B) (Or B C) → (Or B C)) → (And (Neg B) (Or B C) → (Neg B)) → (And (Neg B) (Or B C) → And (Or B C) (Neg B)));
(Γ, (And (Neg B) (Or B C) → (Or B C)))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA7_I. exists (And (Neg B) (Or B C)). exists (Or B C).
exists (Neg B). auto. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA6_I. exists (Neg B). exists (Or B C).
auto. inversion H8. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA5_I. exists (Neg B). exists (Or B C).
auto. inversion H7. inversion H5. inversion H3. subst.
apply MPs with (ps:=[(Γ, ((Or B C) → (Neg B) → C) → (And (Or B C) (Neg B) → C));
(Γ, ((Or B C) → (Neg B) → C))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Axs. apply AxRule_I. apply RA8_I. exists (Or B C). exists (Neg B). exists C.
auto. inversion H5. subst.
apply MPs with (ps:=[(Γ, (C → Neg B → C) → (Or B C → Neg B → C));
(Γ, (C → Neg B → C))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply MPs with (ps:=[(Γ, (B → Neg B → C) → (C → Neg B → C) → (Or B C → Neg B → C));
(Γ, (B → Neg B → C))]).
2: apply MPRule_I. intros. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (Neg B → C). auto. inversion H8. subst.
apply MPs with (ps:=[(Γ, ((And B (Neg B)) → C) → (B → Neg B → C));
(Γ, ((And B (Neg B)) → C))]).
2: apply MPRule_I. intros. inversion H9. subst.
apply Axs. apply AxRule_I. apply RA9_I. exists B. exists (Neg B). exists C.
auto. inversion H10. subst.
apply MPs with (ps:=[(Γ, (Bot V → C) → (And B (Neg B) → C));
(Γ, (Bot V → C))]).
2: apply MPRule_I. intros. inversion H11. subst.
apply MPs with (ps:=[(Γ, (And B (Neg B) → Bot V) → (Bot V → C) → (And B (Neg B) → C));
(Γ, (And B (Neg B) → Bot V))]).
2: apply MPRule_I. intros. inversion H12. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists (And B (Neg B)). exists (Bot V).
exists (C). auto. inversion H13. subst. apply sContr_Bot. inversion H14. inversion H12. subst.
apply sEFQ. inversion H13. inversion H11. inversion H9. inversion H7. subst.
apply sThm_irrel. inversion H8. inversion H6. inversion H4. inversion H2.
Qed.

Lemma swNeg_Top : forall A B Γ,
  (sBIH_rules (Γ, ((wNeg A) → B))) ->
  (sBIH_rules (Γ, (Excl (Top _) A) → B)).
Proof.
intros A B Γ D. apply MPs with (ps:=[(Γ, (wNeg A → B) → (Excl (Top V) A → B));
(Γ, (wNeg A → B))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (Excl (Top V) A → wNeg A) → (wNeg A → B) → Excl (Top V) A → B);
(Γ, (Excl (Top V) A → wNeg A))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I.
apply RA1_I. exists (Excl (Top V) A). exists (wNeg A). exists B. auto.
inversion H1. subst. apply simp_Id_gen.
inversion H2. inversion H0. subst. auto. inversion H1.
Qed.

Lemma sTop_wNeg : forall A B Γ,
  (sBIH_rules (Γ, (Excl (Top _) A) → B)) ->
  (sBIH_rules (Γ, ((wNeg A) → B))).
Proof.
intros A B Γ D. apply MPs with (ps:=[(Γ, (Excl (Top V) A → B) → (wNeg A → B));
(Γ, (Excl (Top V) A → B))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (wNeg A → Excl (Top V) A) → (Excl (Top V) A → B) → wNeg A → B);
(Γ, (wNeg A → Excl (Top V) A))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists (wNeg A). exists (Excl (Top V) A). exists B. auto.
inversion H1. subst. apply simp_Id_gen.
inversion H2. inversion H0. subst. assumption. inversion H1.
Qed.

Lemma Top_wNeg_cons : forall A B Γ,
  (sBIH_rules (Γ, A → (Excl (Top _) B))) ->
  (sBIH_rules (Γ, A → (wNeg B))).
Proof.
intros. apply MPs with (ps:=[(Γ, (Excl (Top V) B → wNeg B) → (A → wNeg B));
(Γ, (Excl (Top V) B → wNeg B))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, (A → Excl (Top V) B) → (Excl (Top V) B → wNeg B) → (A → wNeg B));
(Γ, (A → Excl (Top V) B))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists (Excl (Top V) B). exists (wNeg B). auto.
inversion H2. subst. assumption. inversion H3. inversion H1. subst. 2: inversion H2.
apply simp_Id_gen.
Qed.

Lemma sOr_imp_assoc : forall A B C D Γ,
  (sBIH_rules (Γ, A → (Or (Or B C) D))) ->
  (sBIH_rules (Γ, A → (Or B (Or C D)))).
Proof.
intros.
apply MPs with (ps:=[(Γ, (Or (Or B C) D → Or B (Or C D)) → (A → Or B (Or C D)));
(Γ, (Or (Or B C) D → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, (A → Or (Or B C) D) → (Or (Or B C) D → Or B (Or C D)) → (A → Or B (Or C D)));
(Γ, (A → Or (Or B C) D))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists (Or (Or B C) D).
exists (Or B (Or C D)). auto. inversion H2. subst.
assumption. inversion H3. inversion H1. subst.
apply MPs with (ps:=[(Γ, (D → Or B (Or C D)) → (Or (Or B C) D → Or B (Or C D)));
(Γ, (D → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, ((Or B C) → Or B (Or C D)) → (D → Or B (Or C D)) → (Or (Or B C) D → Or B (Or C D)));
(Γ, ((Or B C) → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists (Or B C).
exists D. exists (Or B (Or C D)). auto. inversion H4. subst.
apply MPs with (ps:=[(Γ, (C → Or B (Or C D)) → (Or B C → Or B (Or C D)));
(Γ, C → Or B (Or C D))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Γ, (B → Or B (Or C D)) → (C → Or B (Or C D)) → (Or B C → Or B (Or C D)));
(Γ, B → Or B (Or C D))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (Or B (Or C D)). auto. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA2_I. exists B. exists (Or C D). auto. inversion H8.
inversion H6. subst.
apply MPs with (ps:=[(Γ, ((Or C D) → Or B (Or C D)) → (C → Or B (Or C D)));
(Γ, (Or C D) → Or B (Or C D))]). 2: apply MPRule_I. intros. inversion H7. subst.
apply MPs with (ps:=[(Γ, (C → (Or C D)) → ((Or C D) → Or B (Or C D)) → (C → Or B (Or C D)));
(Γ, (C → (Or C D)))]). 2: apply MPRule_I. intros. inversion H8. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists C. exists (Or C D).
exists (Or B (Or C D)). auto. inversion H9. subst.
apply Axs. apply AxRule_I. apply RA2_I. exists C. exists D. auto. inversion H10.
inversion H8. subst. apply Axs. apply AxRule_I.
apply RA3_I. exists B. exists (Or C D). auto. inversion H9. inversion H7. inversion H5. inversion H3. subst.
apply MPs with (ps:=[(Γ, ((Or C D) → Or B (Or C D)) → (D → Or B (Or C D)));
(Γ, ((Or C D) → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply MPs with (ps:=[(Γ, (D → (Or C D)) → ((Or C D) → Or B (Or C D)) → (D → Or B (Or C D)));
(Γ, (D → (Or C D)))]). 2: apply MPRule_I. intros. inversion H5. subst. apply Axs. apply AxRule_I. apply RA1_I. exists D. exists (Or C D).
exists (Or B (Or C D)). auto. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists C. exists D. auto. inversion H7.
inversion H5. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists B. exists (Or C D). auto.
inversion H6. inversion H4. inversion H2.
Qed.

Lemma sClaim1 : forall A B Γ,
    (sBIH_rules (Γ, (Neg (Excl A B)) → ((wNeg B) → (wNeg A)))).
Proof.
intros A B Γ. apply sBIH_extens_wBIH. apply wClaim1.
Qed.

Lemma sDN_dist_imp : forall A B Γ,
    (sBIH_rules (Γ, (Neg (wNeg (A → B))) → ((Neg (wNeg A)) → (Neg (wNeg B))))).
Proof.
intros A B Γ. apply sBIH_extens_wBIH. apply wDN_dist_imp.
Qed.

Theorem sBIH_Deduction_Theorem : forall s,
           (sBIH_rules s) ->
           (forall A B Γ, (fst s = Union _ Γ (Singleton _ (A))) ->
                          (snd s = B) ->
                          (exists n, sBIH_rules (Γ, (DN_form n A) → B))).
Proof.
intros s D. induction D.
(* Ids *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. exists 0. inversion H0.
  + subst. apply MPs with (ps:=[(Γ, A0 → A → A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H2. subst.
    apply sThm_irrel. inversion H3. subst.
    apply Ids. apply IdRule_I. assumption. inversion H4.
  + subst. inversion H1. subst. apply simp_Id_gen.
(* Axs *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. exists 0.
  apply MPs with (ps:=[(Γ, A0 → A → A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply sThm_irrel. inversion H2. subst.
  apply Axs. apply AxRule_I. assumption. inversion H3.
(* MPs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J01: List.In (Union (BPropF V) Γ (Singleton (BPropF V) A), A0 → B0) [(Union (BPropF V) Γ (Singleton (BPropF V) A), A0 → B0); (Union (BPropF V) Γ (Singleton (BPropF V) A), A0)]).
  apply in_eq.
  assert (J02: List.In (Union (BPropF V) Γ (Singleton (BPropF V) A), A0) [(Union (BPropF V) Γ (Singleton (BPropF V) A), A0 → B0); (Union (BPropF V) Γ (Singleton (BPropF V) A), A0)]).
  apply in_cons. apply in_eq.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 → B0 = A0 → B0). reflexivity.
  pose (H0 (Union (BPropF V) Γ (Singleton (BPropF V) A), A0 → B0) J01 A (Imp A0 B0) Γ J1 J2).
  destruct e. subst.
  assert (J3: A0 = A0). reflexivity.
  pose (H0 (Union (BPropF V) Γ (Singleton (BPropF V) A), A0) J02 A A0 Γ J1 J3). destruct e.
  exists (max x x0).
  apply MPs with (ps:=[(Γ, (And (DN_form (Init.Nat.max x x0) A) A0 → B0) → ((DN_form (Init.Nat.max x x0) A) → B0));(Γ, And (DN_form (Init.Nat.max x x0) A) A0 → B0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  apply MPs with (ps:=[(Γ, ((DN_form (Init.Nat.max x x0) A) → And (DN_form (Init.Nat.max x x0) A) A0) → (And (DN_form (Init.Nat.max x x0) A) A0 → B0) → ((DN_form (Init.Nat.max x x0) A) → B0));(Γ, (DN_form (Init.Nat.max x x0) A) → And (DN_form (Init.Nat.max x x0) A) A0)]).
  2: apply MPRule_I. intros. inversion H5. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists (DN_form (Init.Nat.max x x0) A). exists (And (DN_form (Init.Nat.max x x0) A) A0). exists B0. auto.
  inversion H6. subst.
  apply MPs with (ps:=[(Γ, ((DN_form (Init.Nat.max x x0) A) → A0) → ((DN_form (Init.Nat.max x x0) A) → And (DN_form (Init.Nat.max x x0) A) A0));(Γ, (DN_form (Init.Nat.max x x0) A) → A0)]).
  2: apply MPRule_I. intros. inversion H7. subst.
  apply MPs with (ps:=[(Γ, ((DN_form (Init.Nat.max x x0) A) → (DN_form (Init.Nat.max x x0) A)) → ((DN_form (Init.Nat.max x x0) A) → A0) → ((DN_form (Init.Nat.max x x0) A) → And (DN_form (Init.Nat.max x x0) A) A0));
  (Γ, (DN_form (Init.Nat.max x x0) A) → (DN_form (Init.Nat.max x x0) A))]).
  2: apply MPRule_I. intros. inversion H8. subst. apply Axs.
  apply AxRule_I. apply RA7_I. exists (DN_form (Init.Nat.max x x0) A). exists (DN_form (Init.Nat.max x x0) A). exists A0. auto.
  inversion H9. subst. apply simp_Id_gen. inversion H10. inversion H8. subst. 2: inversion H9.
  apply MPs with (ps:=[(Γ, (DN_form x0 A → A0) → (DN_form (Init.Nat.max x x0) A → A0));
  (Γ, DN_form x0 A → A0)]).
  2: apply MPRule_I. intros. inversion H9. subst.
  apply MPs with (ps:=[(Γ, (DN_form (Init.Nat.max x x0) A → DN_form x0 A) → (DN_form x0 A → A0) → (DN_form (Init.Nat.max x x0) A → A0));
  (Γ, DN_form (Init.Nat.max x x0) A → DN_form x0 A)]).
  2: apply MPRule_I. intros. inversion H10. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists (DN_form (Init.Nat.max x x0) A). exists (DN_form x0 A).
  exists A0. auto. inversion H11. subst. apply sT_for_DN. lia. inversion H12.
  inversion H10. subst. assumption. inversion H11. inversion H7. inversion H5. subst.
  apply MPs with (ps:=[(Γ, (DN_form (Init.Nat.max x x0) A → A0 → B0) → (And (DN_form (Init.Nat.max x x0) A) A0 → B0));
  (Γ, (DN_form (Init.Nat.max x x0) A → A0 → B0))]). 2: apply MPRule_I.
  intros. inversion H6. subst. apply Axs. apply AxRule_I.
  apply RA8_I. exists (DN_form (Init.Nat.max x x0) A). exists A0. exists B0.
  auto. subst. inversion H7. subst.
  apply MPs with (ps:=[(Γ, (DN_form x A → A0 → B0) → (DN_form (Init.Nat.max x x0) A → A0 → B0));
  (Γ, DN_form x A → A0 → B0)]). 2: apply MPRule_I. intros. inversion H8. subst.
  apply MPs with (ps:=[(Γ, (DN_form (Init.Nat.max x x0) A → DN_form x A) → (DN_form x A → A0 → B0) → (DN_form (Init.Nat.max x x0) A → A0 → B0));
  (Γ, DN_form (Init.Nat.max x x0) A → DN_form x A)]). 2: apply MPRule_I. intros. inversion H9. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (DN_form (Init.Nat.max x x0) A).
  exists (DN_form x A). exists (A0 → B0). auto. subst. inversion H10. subst.
  apply sT_for_DN. lia. inversion H11. inversion H9. subst. assumption.
  inversion H10. inversion H8. inversion H6.
(* DNs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J01: List.In (Union (BPropF V) Γ (Singleton (BPropF V) A), A0) [(Union (BPropF V) Γ (Singleton (BPropF V) A), A0)]).
  apply in_eq.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 = A0). reflexivity.
  pose (H0 (Union (BPropF V) Γ (Singleton (BPropF V) A), A0) J01 A A0 Γ J1 J2). destruct e.
  assert (DNsRule [(Γ, DN_form x A → A0)] (Γ, Neg (wNeg (DN_form x A → A0)))).
  apply DNsRule_I.
  assert (J3: (forall prem : Ensemble (BPropF V) * BPropF V, List.In prem [(Γ, DN_form x A → A0)] ->
  sBIH_rules prem)). intros. inversion H4. subst. 2: inversion H5. assumption.
  pose (@DNs (Γ, Neg (wNeg (DN_form x A → A0))) [(Γ, DN_form x A → A0)] J3 H3).
  pose (sDN_dist_imp (DN_form x A) A0 Γ). exists (S x). simpl.
  apply MPs with (ps:=[(Γ, Neg (wNeg (DN_form x A → A0)) → Neg (wNeg (DN_form x A)) → Neg (wNeg A0));
  (Γ, Neg (wNeg (DN_form x A → A0)))]). 2: apply MPRule_I. intros. inversion H4. subst. 2: inversion H5.
  assumption. subst. assumption. inversion H6.
Qed.

Theorem gen_sBIH_Deduction_Theorem : forall A B Γ,
  spair_derrec (Union _ Γ (Singleton _ (A)), Singleton _ (B)) ->
      (exists n, spair_derrec (Γ, Singleton _ ((DN_form n A) → B))).
Proof.
intros A B Γ spair. unfold spair_derrec. simpl. destruct spair.
destruct H. destruct H0. simpl in H1. simpl in H0. destruct x.
- simpl in H1.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: Bot V = Bot V). reflexivity.
  pose (sBIH_Deduction_Theorem (Union _ Γ (Singleton _ A), Bot V) H1 A (Bot V) Γ J1 J2).
  destruct e. exists x. exists [(DN_form x A → B)]. repeat split. apply NoDup_cons.
  auto. apply NoDup_nil. intros. inversion H3. subst. apply In_singleton.
  subst. inversion H4. simpl.
  apply MPs with (ps:=[(Γ, Imp (DN_form x A → B) (Or (DN_form x A → B) (Bot V))); (Γ, (DN_form x A → B))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Axs. apply AxRule_I. apply RA2_I.
  exists (DN_form x A → B). exists (Bot V). auto. inversion H4. subst.
  apply MPs with (ps:=[(Γ, (Bot V → B) → (DN_form x A → B));(Γ, Bot V → B)]).
  2: apply MPRule_I. intros. inversion H5. subst.
  apply MPs with (ps:=[(Γ, (DN_form x A → Bot V) → (Bot V → B) → (DN_form x A → B));(Γ, DN_form x A → Bot V)]).
  2: apply MPRule_I. intros. inversion H6. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (DN_form x A). exists (Bot V). exists B.
  auto. inversion H7. subst. assumption. inversion H8. inversion H6. subst. apply sEFQ. inversion H7. inversion H5.
- simpl in H1. destruct x. simpl in H1. assert (b=B). pose (H0 b). assert (List.In b [b]). apply in_eq.
  apply s in H2. inversion H2. reflexivity. subst. apply sabsorp_Or1 in H1.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: B = B). reflexivity.
  pose (sBIH_Deduction_Theorem (Union _ Γ (Singleton _ A), B) H1 A B Γ J1 J2). destruct e.
  exists x. exists [(DN_form x A → B)]. repeat split. apply NoDup_cons.
  auto. apply NoDup_nil. intros. inversion H3. subst. apply In_singleton.
  subst. inversion H4. simpl.
  apply MPs with (ps:=[(Γ, Imp (DN_form x A → B) (Or (DN_form x A → B) (Bot V))); (Γ, (DN_form x A → B))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Axs. apply AxRule_I. apply RA2_I.
  exists (DN_form x A → B). exists (Bot V). auto. inversion H4. subst.
  assumption. inversion H5.
  exfalso. simpl in H0. inversion H. apply H4. subst. pose (H0 b).
  assert (List.In b (b :: b0 :: x)). apply in_eq. pose (s H2). inversion s0. subst.
  pose (H0 b0). assert (List.In b0 (b :: b0 :: x)). apply in_cons. apply in_eq.
  pose (s1 H3). inversion s2. subst. apply in_eq.
Qed.



