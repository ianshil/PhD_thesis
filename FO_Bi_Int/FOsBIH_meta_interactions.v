Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_logics.
Require Import FO_BiInt_extens_interactions.
Require Import FOwBIH_meta_interactions.

Section sMeta.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Lemma sThm_irrel : forall A B Γ, FOsBIH_rules (Γ, A --> (B --> A)).
Proof.
intros. apply FOsBIH_extens_FOwBIH. apply wThm_irrel.
Qed.

Lemma simp_Id_gen : forall A Γ, FOsBIH_rules (Γ, A --> A).
Proof.
intros. apply FOsBIH_extens_FOwBIH. apply wimp_Id_gen.
Qed.

Lemma scomm_And_obj : forall A B Γ, (FOsBIH_rules (Γ, A ∧ B --> B ∧ A)).
Proof.
intros. apply FOsBIH_extens_FOwBIH. apply comm_And_obj.
Qed.

Lemma sContr_Bot : forall A Γ, FOsBIH_rules (Γ, A ∧ (¬ A) --> (⊥)).
Proof.
intros. apply FOsBIH_extens_FOwBIH. apply wContr_Bot.
Qed.

Lemma sEFQ : forall A Γ, FOsBIH_rules (Γ, (⊥) --> A).
Proof.
intros. apply FOsBIH_extens_FOwBIH. apply wEFQ.
Qed.

Lemma smonotR_Or : forall A B Γ, (FOsBIH_rules (Γ, A --> B)) ->
    (forall C, FOsBIH_rules (Γ, (A ∨ C) --> (B ∨ C))).
Proof.
intros A B Γ D C.
apply MPs with (ps:=[(Γ, (C --> B ∨ C) --> (A ∨ C --> B ∨ C));(Γ,(C --> B ∨ C))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (A --> B ∨ C) --> (C --> B ∨ C) --> (A ∨ C --> B ∨ C));(Γ,(A --> B ∨ C))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists A. exists C.
exists (B ∨ C). auto. inversion H1. subst.
apply MPs with (ps:=[(Γ, (B --> B ∨ C) --> (A --> B ∨ C));(Γ,((B --> B ∨ C)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, (A --> B) --> (B --> B ∨ C) --> (A --> B ∨ C));(Γ,(A --> B))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Axs.
apply AxRule_I. apply RA1_I. exists A. exists B. exists (B ∨ C). auto.
inversion H4. subst. assumption. inversion H5. inversion H3. subst. apply Axs.
apply AxRule_I. apply RA2_I. exists B. exists C.
auto. inversion H4. inversion H2. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA3_I.
exists B. exists C. auto. inversion H1.
Qed.

Lemma smonotL_Or : forall A B Γ,
    (FOsBIH_rules (Γ, A --> B)) ->
    (forall C, FOsBIH_rules (Γ, (C ∨ A) --> (C ∨ B))).
Proof.
intros A B Γ D C.
apply MPs with (ps:=[(Γ, (A --> C ∨ B) --> ((C ∨ A) --> (C ∨ B)));(Γ,(A --> C ∨ B))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (C --> C ∨ B) --> (A --> C ∨ B) --> ((C ∨ A) --> (C ∨ B)));(Γ,(C --> C ∨ B))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists C. exists A.
exists (C ∨ B). auto. inversion H1. subst. apply Axs.
apply AxRule_I. apply RA2_I. exists C. exists B.
auto. inversion H2. inversion H0. subst.
apply MPs with (ps:=[(Γ, (B --> C ∨ B) --> (A --> C ∨ B));(Γ,((B --> C ∨ B)))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply MPs with (ps:=[(Γ, (A --> B) --> (B --> C ∨ B) --> (A --> C ∨ B));(Γ,(A --> B))]).
2: apply MPRule_I. intros. inversion H2. subst. apply Axs.
apply AxRule_I. apply RA1_I. exists A. exists B. exists (C ∨ B). auto.
inversion H3. subst. assumption. inversion H4. inversion H2. subst. apply Axs.
apply AxRule_I. apply RA3_I. exists C. exists B.
auto. inversion H3. inversion H1.
Qed.

Lemma scomm_Or_obj : forall A B Γ, (FOsBIH_rules (Γ, A ∨ B --> B ∨ A)).
Proof.
intros. apply FOsBIH_extens_FOwBIH. apply comm_Or_obj.
Qed.

Lemma scomm_Or : forall A B Γ,
    (FOsBIH_rules (Γ, A ∨ B)) ->
    (FOsBIH_rules (Γ, B ∨ A)).
Proof.
intros A B Γ D.
apply MPs with (ps:=[(Γ, A ∨ B --> B ∨ A);(Γ, A ∨ B)]).
2: apply MPRule_I. intros. inversion H. subst.
apply scomm_Or_obj. inversion H0. subst. assumption.
inversion H1.
Qed.

Lemma smonot_Or2 : forall A B Γ,
    (FOsBIH_rules (Γ, A --> B)) ->
    (forall C, FOsBIH_rules (Γ, (A ∨ C) --> (C ∨ B))).
Proof.
intros A B Γ D C.
apply MPs with (ps:=[(Γ, (C --> C ∨ B) --> (A ∨ C --> C ∨ B));(Γ, C --> C ∨ B)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (A --> C ∨ B) --> (C --> C ∨ B) --> (A ∨ C --> C ∨ B));(Γ, A --> C ∨ B)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Axs.
apply AxRule_I. apply RA4_I. exists A. exists C. exists (C ∨ B). auto.
inversion H1. subst.
apply MPs with (ps:=[(Γ, (B --> C ∨ B) --> (A --> C ∨ B));(Γ, B --> C ∨ B)]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, (A --> B) --> (B --> C ∨ B) --> (A --> C ∨ B));(Γ, A --> B)]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists B. exists (C ∨ B).
auto. inversion H4. subst. assumption. inversion H5. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists C. exists B. auto.
inversion H4. inversion H2. inversion H0. subst. apply Axs. apply AxRule_I.
apply RA2_I. exists C. exists B. auto. inversion H1.
Qed.

Lemma sabsorp_Or1 : forall A Γ,
    (FOsBIH_rules (Γ, A ∨ (⊥))) ->
    (FOsBIH_rules (Γ, A)).
Proof.
intros A Γ D.
apply MPs with (ps:=[(Γ, (A ∨ ⊥) --> A);(Γ, A ∨ (⊥))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, (⊥ --> A) --> (A ∨ (⊥) --> A));(Γ, (⊥ --> A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, (A --> A) --> (⊥ --> A) --> (A ∨ (⊥) --> A));(Γ, A --> A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists A. exists (⊥).
exists A. auto. inversion H2. subst. apply simp_Id_gen.
inversion H3. inversion H1. subst. apply sEFQ. inversion H2.
inversion H0. subst. assumption. inversion H1.
Qed.

Theorem sdual_residuation_gen : forall A B C Γ,
  (FOsBIH_rules (Γ, (A --< B) --> C) ->
      FOsBIH_rules (Γ, A --> (B ∨ C))) *
  (FOsBIH_rules (Γ, A --> (B ∨ C)) ->
      FOsBIH_rules (Γ, (A --< B) --> C)).
Proof.
intros A B C Γ. split.
- intro D. pose (@smonot_Or2 (A --< B) C Γ D B).
  apply MPs with (ps:=[(Γ, ((A --< B) ∨ B --> B ∨ C) --> (A --> B ∨ C));(Γ,(A --< B) ∨ B --> B ∨ C)]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MPs with (ps:=[(Γ, (A --> (A --< B) ∨ B) --> ((A --< B) ∨ B --> B ∨ C) --> (A --> B ∨ C));(Γ,(A --> (A --< B) ∨ B))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists A. exists ((A --< B) ∨ B). exists (B ∨ C). auto.
  inversion H1. subst.
  apply MPs with (ps:=[(Γ, (B ∨ (A --< B) --> (A --< B) ∨ B) --> (A --> (A --< B) ∨ B));(Γ,(B ∨ (A --< B) --> (A --< B) ∨ B))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MPs with (ps:=[(Γ, (A --> B ∨ (A --< B)) --> (B ∨ (A --< B) --> (A --< B) ∨ B) --> (A --> (A --< B) ∨ B));(Γ,(A --> B ∨ (A --< B)))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists A. exists (B ∨ (A --< B)). exists ((A --< B) ∨ B).
  auto. inversion H4. subst.
  apply Axs. apply AxRule_I. apply RA11_I. exists A. exists B. auto. inversion H5.
  inversion H3. subst. apply scomm_Or_obj. inversion H4. inversion H2.
  inversion H0. subst. assumption. inversion H1.
- intro D. apply MPs with (ps:=[(Γ, ((C ∨ (A --< (B ∨ C))) --> C) --> ((A --< B) --> C));(Γ, (C ∨ (A --< (B ∨ C))) --> C)]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MPs with (ps:=[(Γ, ((A --< B) --> (C ∨ (A --< (B ∨ C)))) --> ((C ∨ (A --< (B ∨ C))) --> C) --> ((A --< B) --> C));(Γ, (A --< B) --> (C ∨ (A --< (B ∨ C))))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Axs. apply AxRule_I. apply RA1_I.
  exists (A --< B). exists (C ∨ (A --< (B ∨ C))). exists C. auto. inversion H1. subst.
  apply MPs with (ps:=[(Γ, ((C ∨ ((A --< B) --< C)) --> C ∨ (A --< (B ∨ C))) --> ((A --< B) --> C ∨ (A --< (B ∨ C))));(Γ, ((C ∨ ((A --< B) --< C)) --> C ∨ (A --< (B ∨ C))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MPs with (ps:=[(Γ, ((A --< B) --> (C ∨ ((A --< B) --< C)))--> ((C ∨ ((A --< B) --< C)) --> C ∨ (A --< (B ∨ C))) --> ((A --< B) --> C ∨ (A --< (B ∨ C))));
  (Γ, ((A --< B) --> (C ∨ ((A --< B) --< C))))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (A --< B). exists (C ∨ ((A --< B) --< C)).
  exists (C ∨ (A --< (B ∨ C))). auto. inversion H4. subst.
  apply Axs. apply AxRule_I. apply RA11_I. exists (A --< B). exists C. auto. inversion H5.
  inversion H3. subst. apply smonotL_Or. apply Axs. apply AxRule_I. apply RA13_I.
  exists A. exists B. exists C. auto. inversion H4. inversion H2. inversion H0. subst.
  apply MPs with (ps:=[(Γ, (C ∨ (⊥) --> C) --> (C ∨ (A --< (B ∨ C)) --> C));
  (Γ, (C ∨ (⊥) --> C))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply MPs with (ps:=[(Γ, (C ∨ (A --< (B ∨ C)) --> C ∨ (⊥)) --> (C ∨ (⊥) --> C) --> (C ∨ (A --< (B ∨ C)) --> C));
  (Γ, (C ∨ (A --< (B ∨ C)) --> C ∨ (⊥)))]). 2: apply MPRule_I. intros. inversion H2. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (C ∨ (A --< (B ∨ C))).
  exists (C ∨ (⊥)). exists C. auto. inversion H3. subst. apply smonotL_Or.
  apply MPs with (ps:=[(Γ, (((∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> B ∨ C)))) --> ⊥) --> ((A --< (B ∨ C)) --> ⊥));
  (Γ, ((∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> (B ∨ C)))) --> ⊥))]). 2: apply MPRule_I. intros. inversion H4. subst.
  apply MPs with (ps:=[(Γ, ((A --< (B ∨ C)) --> ((∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> B ∨ C))))) --> (((∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> B ∨ C)))) --> ⊥) --> ((A --< (B ∨ C)) --> ⊥));
  (Γ, ((A --< (B ∨ C)) --> ((∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> B ∨ C))))))]). 2: apply MPRule_I. intros. inversion H5. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (A --< (B ∨ C)).
  exists ((∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> B ∨ C)))). exists (⊥). auto. inversion H6.
  subst.
  apply MPs with (ps:=[(Γ, ((A --< (B ∨ C)) --> (¬ (∞ (A --> B ∨ C)))) --> ((A --< (B ∨ C)) --> (∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> B ∨ C)))));
  (Γ, ((A --< (B ∨ C)) --> (¬ (∞ (A --> B ∨ C)))))]). 2: apply MPRule_I. intros. inversion H7. subst.
  apply MPs with (ps:=[(Γ, ((A --< (B ∨ C)) --> (∞ (A --> B ∨ C))) --> ((A --< (B ∨ C)) --> (¬ (∞ (A --> B ∨ C)))) --> ((A --< (B ∨ C)) --> (∞ (A --> B ∨ C)) ∧ (¬ (∞ (A --> B ∨ C)))));
  (Γ, ((A --< (B ∨ C)) --> (∞ (A --> B ∨ C))))]). 2: apply MPRule_I. intros. inversion H8. subst.
  apply Axs. apply AxRule_I. apply RA7_I. exists (A --< (B ∨ C)).
  exists (∞ (A --> B ∨ C)). exists (¬ (∞ (A --> B ∨ C))). auto. inversion H9. subst.
  apply Axs. apply AxRule_I. apply RA12_I. exists A. exists (B ∨ C).
  auto. inversion H10. inversion H8. inversion H9. subst.
  apply MPs with (ps:=[(Γ, (¬ (∞ (A --> B ∨ C))) --> ((A --< (B ∨ C)) --> ¬ (∞ (A --> B ∨ C))));
  (Γ, (¬ (∞ (A --> B ∨ C))))]). 2: apply MPRule_I. intros. inversion H9. subst.
  apply sThm_irrel. inversion H11. subst. apply DNs with (ps:=[(Γ, A --> B ∨ C)]).
  2: apply DNsRule_I. intros. inversion H12. subst. assumption. inversion H13. inversion H12.
  inversion H9. inversion H7. inversion H5. subst. apply sContr_Bot. inversion H6.
  inversion H4. inversion H2. subst.
  apply MPs with (ps:=[(Γ, (⊥ --> C) --> (C ∨ (⊥) --> C));(Γ, (⊥ --> C))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MPs with (ps:=[(Γ, (C --> C) --> (⊥ --> C) --> (C ∨ (⊥) --> C));(Γ, (C --> C))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Axs.
  apply AxRule_I. apply RA4_I. exists C. exists (⊥). exists C. auto.
  inversion H5. subst. apply simp_Id_gen. inversion H6. inversion H4. subst. apply sEFQ.
  inversion H5. inversion H3. inversion H1.
Qed.

Theorem sdual_residuation : forall A B C,
  (FOsBIH_rules ((Empty_set form), (A --< B) --> C) ->
      FOsBIH_rules (Empty_set _, A --> ((B ∨ C)))) *
  (FOsBIH_rules (Empty_set _, A --> ((B ∨ C))) ->
      FOsBIH_rules (Empty_set _, (A --< B) --> C)).
Proof.
intros A B C. apply sdual_residuation_gen.
Qed.

Theorem FOsBIH_Detachment_Theorem : forall s,
           (FOsBIH_rules s) ->
           (forall A B Γ, (fst s = Γ) ->
                          (snd s = A --> B) ->
                          FOsBIH_rules  (Union _ Γ (Singleton _ A), B)).
Proof.
intros s D. induction D.
(* Ids *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst.
  simpl. apply MPs with (ps:=[(Union form Γ0 (Singleton form A), A --> B);(Union form Γ0 (Singleton form A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ids.
  apply IdRule_I. apply Union_introl ; auto. inversion H2. subst.
  apply Ids. apply IdRule_I. 2: inversion H3. apply Union_intror. apply In_singleton.
(* Axs *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst. simpl.
  apply MPs with (ps:=[(Union form Γ0 (Singleton form A), A --> B);(Union form Γ0 (Singleton form A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Axs.
  apply AxRule_I. assumption. inversion H2. subst. apply Ids. apply IdRule_I.
  apply Union_intror. apply In_singleton. inversion H3.
(* MPs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. simpl.
  assert (J01: List.In (Γ0, A0 --> A --> B) ((Γ0, A0 --> A --> B) :: (Γ0, A0) :: nil)). apply in_eq.
  assert (J1: Γ0 = Γ0). reflexivity.
  assert (J2: A0 --> A --> B = A0 --> A --> B). reflexivity.
  pose (H0 (Γ0, A0 --> A --> B) J01 A0 (A --> B) Γ0 J1 J2).
  assert (FOsBIH_rules (Γ0, A --> B)).
  assert (J02: List.In (Γ0, A0) ((Γ0, A0 --> A --> B) :: (Γ0, A0) :: nil)). apply in_cons. apply in_eq.
  pose (H (Γ0, A0) J02).
  apply MPs with (ps:=[(Γ0, A0 --> A --> B); (Γ0, A0)]) ; auto.
  assert (J3: (forall A1 : form, In _ (fst (Union form Γ0 (Singleton form A0), A --> B)) A1 -> FOsBIH_rules (Γ0, A1))).
  intro. simpl. intro. inversion H3. apply Ids. apply IdRule_I. auto. subst.
  inversion H4. subst. apply H. apply in_cons ; apply in_eq.
  pose (FOsBIH_comp (Union form Γ0 (Singleton form A0), A --> B) f Γ0 J3). simpl in f0.
  apply MPs with (ps:=[(Union form Γ0 (Singleton form A), A --> B);(Union form Γ0 (Singleton form A), A)]). 2: apply MPRule_I.
  intros. inversion H3.
  pose (FOsBIH_monot (Γ0, A --> B) f0 (Union form Γ0 (Singleton form A))). simpl in f1. subst.
  apply f1. intro. intro. apply Union_introl. auto.
  inversion H4. subst. 2: inversion H5. apply Ids. apply IdRule_I. apply Union_intror. apply In_singleton.
(* DNs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. inversion id2. subst. simpl.
  assert (J01: List.In (Γ0, A0) ((Γ0, A0) :: nil)). apply in_eq. apply H in J01. remember (Union form Γ0 (Singleton form (∞ A0))) as Γ.
  apply MPs with (ps:=[(Γ, ((∞ A0) ∧ (¬ (∞ A0))) --> ⊥); (Γ, (∞ A0) ∧ (¬ (∞ A0)))]).
  2: apply MPRule_I. intros. inversion H2. rewrite <- H3. apply sContr_Bot. inversion H3.
  rewrite <- H4.
  apply MPs with (ps:=[(Γ,(⊤ -->  ((∞ A0) ∧ (¬ (∞ A0)))));(Γ, ⊤)]).
  2: apply MPRule_I. intros. inversion H5. rewrite <- H6.
  apply MPs with (ps:=[(Γ,(⊤ --> (¬ (∞ A0))) -->(⊤ -->  ((∞ A0) ∧ (¬ (∞ A0)))));(Γ, ⊤ --> (¬ (∞ A0)))]).
  2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
  apply MPs with (ps:=[(Γ,(⊤ --> (∞ A0)) --> (⊤ --> (¬ (∞ A0))) --> (⊤ --> ((∞ A0) ∧ (¬ (∞ A0)))));(Γ, ⊤ --> (∞ A0))]).
  2: apply MPRule_I. intros. inversion H9. rewrite <- H10. apply Axs. apply AxRule_I.
  apply RA7_I. exists (⊤). exists (∞ A0). exists (¬ (∞ A0)). auto. inversion H10. 2: inversion H11.
  rewrite <- H11.
  apply MPs with (ps:=[(Γ, ∞ A0 --> ⊤ --> ∞ A0);(Γ, ∞ A0)]). intros. 2: apply MPRule_I.
  inversion H12. rewrite <- H13. apply sThm_irrel. inversion H13. 2: inversion H14. rewrite <- H14.
  apply Ids. apply IdRule_I. subst. apply Union_intror. apply In_singleton.
  inversion H8. rewrite <- H9.
  apply MPs with (ps:=[(Γ, ¬ (∞ A0) --> ⊤ --> ¬ (∞ A0));(Γ, ¬ (∞ A0))]). intros. 2: apply MPRule_I.
  inversion H10. rewrite <- H11. apply sThm_irrel. inversion H11. 2: inversion H12. rewrite <- H12.
  apply DNs with (ps:=[(Γ, A0)]). 2: apply DNsRule_I. intros. inversion H13. subst.
  pose (FOsBIH_monot _ J01). simpl in f. pose (f (Union form Γ0 (Singleton _ (∞ A0)))). simpl in f0.
  apply f0. intro ; intro. apply Union_introl ; auto. inversion H14.
  inversion H9. inversion H6. subst. apply FOsBIH_extens_FOwBIH. apply wTop. inversion H7. inversion H4.
(* Gens *)
- intros A B Γ id1 id2. inversion H1. subst. simpl. inversion id2.
(* ECs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl. inversion id2. subst.
  assert (J01: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B, A0 --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B, A0 --> B[↑]) :: nil)). apply in_eq.
  apply H in J01. apply MPs with (ps:=[(Union form Γ0 (Singleton form (∃ A0)), (∃ A0) --> B);(Union form Γ0 (Singleton form (∃ A0)), ∃ A0)]). 2: apply MPRule_I.
  intros. inversion H2. subst. assert (FOsBIH_rules (Γ0, (∃ A0) --> B)).
  apply ECs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B, A0 --> B[↑])]). 2: apply ECRule_I. intros.
  inversion H3. subst. auto. inversion H4.
  pose (FOsBIH_monot (Γ0, (∃ A0) --> B) H3 (Union form Γ0 (Singleton form (∃ A0)))). simpl in f. apply f.
  intro. intro. apply Union_introl ; auto.
  inversion H3. subst. 2: inversion H4. apply Ids. apply IdRule_I.
  apply Union_intror ; apply In_singleton.
Qed.

Theorem gen_FOsBIH_Detachment_Theorem : forall A B Γ,
  spair_der (Γ, Singleton _ (A --> B)) ->
      spair_der (Union form Γ (Singleton form A),  Singleton _ B).
Proof.
intros A B Γ spair. unfold spair_der. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. simpl. apply In_singleton. inversion H0.
apply MPs with (ps:=[ (Union form Γ (Singleton form A), B --> (B ∨ ⊥)); (Union form Γ (Singleton form A), B)]).
2: apply MPRule_I. intros. inversion H. subst. apply Axs. apply AxRule_I. apply RA2_I.
exists B. exists (⊥). auto. inversion H0. subst. 2: inversion H1.
destruct spair. destruct H1. destruct H2. simpl in H3. destruct x.
apply MPs with (ps:=[(Union form Γ (Singleton form A), ⊥ --> B);(Union form Γ (Singleton form A), ⊥)]).
2: apply MPRule_I. intros. inversion H4. subst. apply sEFQ. inversion H5. subst. 2: inversion H6.
simpl in H3. apply FOsBIH_monot with (Γ1:= Union form Γ (Singleton form A)) in H3. simpl in H3. auto.
simpl. intro. intro. apply Union_introl ; auto.
destruct x. simpl in H3. assert (f=A --> B). pose (H2 f). assert (List.In f (f :: nil)). apply in_eq.
apply i in H4. inversion H4. auto. subst. apply sabsorp_Or1 in H3.
assert (J1: Γ = Γ). reflexivity.
assert (J2: A --> B = A --> B). reflexivity.
pose (FOsBIH_Detachment_Theorem (Γ, A --> B) H3 A B Γ J1 J2). assumption.
exfalso. simpl in H1. inversion H1. apply H6. subst. pose (H2 f).
assert (List.In f (f :: f0 :: x)). apply in_eq. pose (i H4). inversion i0. subst.
pose (H2 f0). assert (List.In f0 (A --> B :: f0 :: x)). apply in_cons. apply in_eq.
pose (i1 H5). inversion i2. subst. apply in_eq.
Qed.

Lemma sDN_to_form : forall A Γ, (FOsBIH_rules (Γ, ¬ (∞ A)--> A)).
Proof.
intros A Γ. apply FOsBIH_extens_FOwBIH. apply wDN_to_form.
Qed.

Lemma sT_for_DN : forall A n m Γ, (le m n) -> (FOsBIH_rules (Γ, (DN_form n A) --> (DN_form m A))).
Proof.
intros. apply FOsBIH_extens_FOwBIH. apply wT_for_DN. assumption.
Qed.

Lemma sExcl_mon : forall A B C,
  (FOsBIH_rules (Empty_set _, A --> B)) ->
  (FOsBIH_rules (Empty_set _, (A --< C) --> (B --< C))).
Proof.
intros. apply sdual_residuation.
apply MPs with (ps:=[(Empty_set _, (B --> C ∨ (B --< C)) --> (A --> C ∨ (B --< C)));
(Empty_set _, (B --> C ∨ (B --< C)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Empty_set _, (A --> B) --> (B --> C ∨ (B --< C)) --> (A --> C ∨ (B --< C)));
(Empty_set _, (A --> B))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (C ∨ (B --< C)). auto. inversion H2. subst. assumption. inversion H3.
inversion H1. subst.
apply Axs. apply AxRule_I. apply RA11_I. exists B. exists C. auto. inversion H2.
Qed.

Lemma smon_Excl : forall A B C,
  (FOsBIH_rules (Empty_set _, A --> B)) ->
  (FOsBIH_rules (Empty_set _, (C --< B) --> (C --< A))).
Proof.
intros. apply sdual_residuation.
apply MPs with (ps:=[(Empty_set _, (A ∨ (C --< A) --> B ∨ (C --< A)) --> (C --> B ∨ (C --< A)));
(Empty_set _, (A ∨ (C --< A) --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Empty_set _, (C --> A ∨ (C --< A)) --> (A ∨ (C --< A) --> B ∨ (C --< A)) --> (C --> B ∨ (C --< A)));
(Empty_set _, C --> A ∨ (C --< A))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists C. exists (A ∨ (C --< A)).
exists (B ∨ (C --< A)). auto. inversion H2. subst.
apply Axs. apply AxRule_I. apply RA11_I. exists C. exists A.
auto. inversion H3. inversion H1. subst.
apply MPs with (ps:=[(Empty_set _, ((C --< A) --> B ∨ (C --< A)) --> (A ∨ (C --< A) --> B ∨ (C --< A)));
(Empty_set _, ((C --< A) --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Empty_set _, (A --> B ∨ (C --< A)) --> ((C --< A) --> B ∨ (C --< A)) --> (A ∨ (C --< A) --> B ∨ (C --< A)));
(Empty_set _, (A --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists A. exists (C --< A).
exists (B ∨ (C --< A)). auto. inversion H4. subst.
apply MPs with (ps:=[(Empty_set _, (B --> B ∨ (C --< A)) --> (A --> B ∨ (C --< A)));
(Empty_set _, (B --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Empty_set _, (A --> B) --> (B --> B ∨ (C --< A)) --> (A --> B ∨ (C --< A)));
(Empty_set _, (A --> B))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (B ∨ (C --< A)). auto. inversion H7. subst. assumption. inversion H8.
inversion H6. subst.
apply Axs. apply AxRule_I. apply RA2_I. exists B. exists (C --< A). auto.
inversion H7. inversion H5. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists B. exists (C --< A). auto.
inversion H4. inversion H2.
Qed.

Lemma sOr_Neg : forall A B C Γ,
  (FOsBIH_rules (Γ, A --> (B ∨ C))) ->
  (FOsBIH_rules (Γ, ((¬ B) ∧ A) --> C)).
Proof.
intros.
apply MPs with (ps:=[(Γ, (((¬ B) ∧ (B ∨ C)) --> C) --> ((¬ B) ∧ A --> C));(Γ, (¬ B) ∧ (B ∨ C) --> C)]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, (((¬ B) ∧ A) --> ((¬ B) ∧ (B ∨ C))) --> (((¬ B) ∧ (B ∨ C)) --> C) --> ((¬ B) ∧ A --> C));
(Γ, (((¬ B) ∧ A) --> ((¬ B) ∧ (B ∨ C))))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists ((¬ B) ∧ A). exists ((¬ B) ∧ (B ∨ C)).
exists C. auto. inversion H2. subst.
apply MPs with (ps:=[(Γ, ((¬ B) ∧ A --> (B ∨ C)) --> ((¬ B) ∧ A --> (¬ B) ∧ (B ∨ C)));
(Γ, ((¬ B) ∧ A --> (B ∨ C)))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply MPs with (ps:=[(Γ, ((¬ B) ∧ A --> (¬ B)) --> ((¬ B) ∧ A --> (B ∨ C)) --> ((¬ B) ∧ A --> (¬ B) ∧ (B ∨ C)));
(Γ, ((¬ B) ∧ A --> (¬ B)))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Axs. apply AxRule_I. apply RA7_I. exists ((¬ B) ∧ A). exists (¬ B).
exists (B ∨ C). auto. inversion H5. subst.
apply Axs. apply AxRule_I. apply RA5_I. exists (¬ B). exists A. auto.
inversion H6. inversion H4. subst.
apply MPs with (ps:=[(Γ, (A --> B ∨ C) --> ((¬ B) ∧ A --> B ∨ C));
(Γ, (A --> B ∨ C))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Γ, ((¬ B) ∧ A --> A) --> (A --> B ∨ C) --> ((¬ B) ∧ A --> B ∨ C));
(Γ, ((¬ B) ∧ A --> A))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists ((¬ B) ∧ A). exists A.
exists (B ∨ C). auto. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA6_I. exists (¬ B). exists A. auto.
inversion H8. inversion H6. subst. assumption. inversion H7. inversion H5. inversion H3. inversion H1. subst.
apply MPs with (ps:=[(Γ, ((B ∨ C) ∧ (¬ B) --> C) --> ((¬ B) ∧ (B ∨ C) --> C));
(Γ, ((B ∨ C) ∧ (¬ B) --> C))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, ((¬ B) ∧ (B ∨ C) --> (B ∨ C) ∧ (¬ B)) --> ((B ∨ C) ∧ (¬ B) --> C) --> ((¬ B) ∧ (B ∨ C) --> C));
(Γ, (¬ B) ∧ (B ∨ C) --> (B ∨ C) ∧ (¬ B))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists ((¬ B) ∧ (B ∨ C)). exists ((B ∨ C) ∧ (¬ B)).
exists C. auto. inversion H4. subst.
apply MPs with (ps:=[(Γ, ((¬ B) ∧ (B ∨ C) --> (¬ B)) --> ((¬ B) ∧ (B ∨ C) --> (B ∨ C) ∧ (¬ B)));
(Γ, ((¬ B) ∧ (B ∨ C) --> (¬ B)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Γ, ((¬ B) ∧ (B ∨ C) --> (B ∨ C)) --> ((¬ B) ∧ (B ∨ C) --> (¬ B)) --> ((¬ B) ∧ (B ∨ C) --> (B ∨ C) ∧ (¬ B)));
(Γ, ((¬ B) ∧ (B ∨ C) --> (B ∨ C)))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA7_I. exists ((¬ B) ∧ (B ∨ C)). exists (B ∨ C).
exists (¬ B). auto. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA6_I. exists (¬ B). exists (B ∨ C).
auto. inversion H8. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA5_I. exists (¬ B). exists (B ∨ C).
auto. inversion H7. inversion H5. inversion H3. subst.
apply MPs with (ps:=[(Γ, ((B ∨ C) --> (¬ B) --> C) --> ((B ∨ C) ∧ (¬ B) --> C));
(Γ, ((B ∨ C) --> (¬ B) --> C))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Axs. apply AxRule_I. apply RA8_I. exists (B ∨ C). exists (¬ B). exists C.
auto. inversion H5. subst.
apply MPs with (ps:=[(Γ, (C --> ¬ B --> C) --> (B ∨ C --> ¬ B --> C));
(Γ, (C --> ¬ B --> C))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply MPs with (ps:=[(Γ, (B --> ¬ B --> C) --> (C --> ¬ B --> C) --> (B ∨ C --> ¬ B --> C));
(Γ, (B --> ¬ B --> C))]).
2: apply MPRule_I. intros. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (¬ B --> C). auto. inversion H8. subst.
apply MPs with (ps:=[(Γ, ((B ∧ (¬ B)) --> C) --> (B --> ¬ B --> C));
(Γ, ((B ∧ (¬ B)) --> C))]).
2: apply MPRule_I. intros. inversion H9. subst.
apply Axs. apply AxRule_I. apply RA9_I. exists B. exists (¬ B). exists C.
auto. inversion H10. subst.
apply MPs with (ps:=[(Γ, (⊥ --> C) --> (B ∧ (¬ B) --> C));
(Γ, (⊥ --> C))]).
2: apply MPRule_I. intros. inversion H11. subst.
apply MPs with (ps:=[(Γ, (B ∧ (¬ B) --> ⊥) --> (⊥ --> C) --> (B ∧ (¬ B) --> C));
(Γ, (B ∧ (¬ B) --> ⊥))]).
2: apply MPRule_I. intros. inversion H12. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists (B ∧ (¬ B)). exists (⊥).
exists (C). auto. inversion H13. subst. apply sContr_Bot. inversion H14. inversion H12. subst.
apply sEFQ. inversion H13. inversion H11. inversion H9. inversion H7. subst.
apply sThm_irrel. inversion H8. inversion H6. inversion H4. inversion H2.
Qed.

Lemma swNeg_Top : forall A B Γ,
  (FOsBIH_rules (Γ, ((∞ A) --> B))) ->
  (FOsBIH_rules (Γ, (⊤ --< A) --> B)).
Proof.
intros A B Γ D. apply MPs with (ps:=[(Γ, (∞ A --> B) --> ((⊤ --< A) --> B));
(Γ, (∞ A --> B))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, ((⊤ --< A) --> ∞ A) --> (∞ A --> B) --> (⊤ --< A) --> B);
(Γ, ((⊤ --< A) --> ∞ A))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I.
apply RA1_I. exists (⊤ --< A). exists (∞ A). exists B. auto.
inversion H1. subst. apply simp_Id_gen.
inversion H2. inversion H0. subst. auto. inversion H1.
Qed.

Lemma sTop_wNeg : forall A B Γ,
  (FOsBIH_rules (Γ, (⊤ --< A) --> B)) ->
  (FOsBIH_rules (Γ, ((∞ A) --> B))).
Proof.
intros A B Γ D. apply MPs with (ps:=[(Γ, ((⊤ --< A) --> B) --> ((∞ A) --> B));
(Γ, ((⊤ --< A) --> B))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MPs with (ps:=[(Γ, ((∞ A) --> ⊤ --< A) --> ((⊤ --< A) --> B) --> (∞ A) --> B);
(Γ, ((∞ A) --> ⊤ --< A))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists (∞ A). exists (⊤ --< A). exists B. auto.
inversion H1. subst. apply simp_Id_gen.
inversion H2. inversion H0. subst. assumption. inversion H1.
Qed.

Lemma Top_wNeg_cons : forall A B Γ,
  (FOsBIH_rules (Γ, A --> (⊤ --< B))) ->
  (FOsBIH_rules (Γ, A --> (∞ B))).
Proof.
intros. apply MPs with (ps:=[(Γ, ((⊤ --< B) --> ∞ B) --> (A --> ∞ B));
(Γ, ((⊤ --< B) --> ∞ B))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, (A --> ⊤ --< B) --> ((⊤ --< B) --> ∞ B) --> (A --> ∞ B));
(Γ, (A --> ⊤ --< B))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists (⊤ --< B). exists (∞ B). auto.
inversion H2. subst. assumption. inversion H3. inversion H1. subst. 2: inversion H2.
apply simp_Id_gen.
Qed.

Lemma sOr_imp_assoc : forall A B C D Γ,
  (FOsBIH_rules (Γ, A --> ((B ∨ C) ∨ D))) ->
  (FOsBIH_rules (Γ, A --> (B ∨ (C ∨ D)))).
Proof.
intros.
apply MPs with (ps:=[(Γ, ((B ∨ C) ∨ D --> B ∨ (C ∨ D)) --> (A --> B ∨ (C ∨ D)));
(Γ, ((B ∨ C) ∨ D --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MPs with (ps:=[(Γ, (A --> (B ∨ C) ∨ D) --> ((B ∨ C) ∨ D --> B ∨ (C ∨ D)) --> (A --> B ∨ (C ∨ D)));
(Γ, (A --> (B ∨ C) ∨ D))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists A. exists ((B ∨ C) ∨ D).
exists (B ∨ (C ∨ D)). auto. inversion H2. subst.
assumption. inversion H3. inversion H1. subst.
apply MPs with (ps:=[(Γ, (D --> B ∨ (C ∨ D)) --> ((B ∨ C) ∨ D --> B ∨ (C ∨ D)));
(Γ, (D --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MPs with (ps:=[(Γ, ((B ∨ C) --> B ∨ (C ∨ D)) --> (D --> B ∨ (C ∨ D)) --> ((B ∨ C) ∨ D --> B ∨ (C ∨ D)));
(Γ, ((B ∨ C) --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists (B ∨ C).
exists D. exists (B ∨ (C ∨ D)). auto. inversion H4. subst.
apply MPs with (ps:=[(Γ, (C --> B ∨ (C ∨ D)) --> (B ∨ C --> B ∨ (C ∨ D)));
(Γ, C --> B ∨ (C ∨ D))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply MPs with (ps:=[(Γ, (B --> B ∨ (C ∨ D)) --> (C --> B ∨ (C ∨ D)) --> (B ∨ C --> B ∨ (C ∨ D)));
(Γ, B --> B ∨ (C ∨ D))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (B ∨ (C ∨ D)). auto. inversion H7. subst.
apply Axs. apply AxRule_I. apply RA2_I. exists B. exists (C ∨ D). auto. inversion H8.
inversion H6. subst.
apply MPs with (ps:=[(Γ, ((C ∨ D) --> B ∨ (C ∨ D)) --> (C --> B ∨ (C ∨ D)));
(Γ, (C ∨ D) --> B ∨ (C ∨ D))]). 2: apply MPRule_I. intros. inversion H7. subst.
apply MPs with (ps:=[(Γ, (C --> (C ∨ D)) --> ((C ∨ D) --> B ∨ (C ∨ D)) --> (C --> B ∨ (C ∨ D)));
(Γ, (C --> (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H8. subst.
apply Axs. apply AxRule_I. apply RA1_I. exists C. exists (C ∨ D).
exists (B ∨ (C ∨ D)). auto. inversion H9. subst.
apply Axs. apply AxRule_I. apply RA2_I. exists C. exists D. auto. inversion H10.
inversion H8. subst. apply Axs. apply AxRule_I.
apply RA3_I. exists B. exists (C ∨ D). auto. inversion H9. inversion H7. inversion H5. inversion H3. subst.
apply MPs with (ps:=[(Γ, ((C ∨ D) --> B ∨ (C ∨ D)) --> (D --> B ∨ (C ∨ D)));
(Γ, ((C ∨ D) --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply MPs with (ps:=[(Γ, (D --> (C ∨ D)) --> ((C ∨ D) --> B ∨ (C ∨ D)) --> (D --> B ∨ (C ∨ D)));
(Γ, (D --> (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H5. subst. apply Axs. apply AxRule_I. apply RA1_I. exists D. exists (C ∨ D).
exists (B ∨ (C ∨ D)). auto. inversion H6. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists C. exists D. auto. inversion H7.
inversion H5. subst.
apply Axs. apply AxRule_I. apply RA3_I. exists B. exists (C ∨ D). auto.
inversion H6. inversion H4. inversion H2.
Qed.

Lemma sClaim1 : forall A B Γ,
    (FOsBIH_rules (Γ, (¬ (A --< B)) --> ((∞ B) --> (∞ A)))).
Proof.
intros A B Γ. apply FOsBIH_extens_FOwBIH. apply wClaim1.
Qed.

Lemma sDN_dist_imp : forall A B Γ,
    (FOsBIH_rules (Γ, (¬ (∞ (A --> B))) --> ((¬ (∞ A)) --> (¬ (∞ B))))).
Proof.
intros A B Γ. apply FOsBIH_extens_FOwBIH. apply wDN_dist_imp.
Qed.

Lemma DN_dist_up : forall n A, (DN_form n A)[↑] = DN_form n A[↑].
Proof.
induction n.
- intros. simpl ; auto.
- intros. simpl. pose (IHn A). rewrite e. auto.
Qed.

Theorem FOsBIH_Deduction_Theorem : forall s,
           (FOsBIH_rules s) ->
           (forall A B Γ, (fst s = Union _ Γ (Singleton _ A)) ->
                          (snd s = B) ->
                          (exists n, FOsBIH_rules (Γ, (DN_form n A) --> B))).
Proof.
intros s D. induction D.
(* Ids *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. exists 0. inversion H0.
  + subst. apply MPs with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H2. subst.
    apply sThm_irrel. inversion H3. subst. apply Ids. apply IdRule_I. assumption. inversion H4.
  + subst. simpl. inversion H1. apply simp_Id_gen.
(* Axs *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. exists 0.
  apply MPs with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply sThm_irrel. inversion H2. subst. apply Axs. apply AxRule_I. assumption. inversion H3.
(* MPs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J01: List.In   (Union _ Γ (Singleton _ A), A0 --> B0) ((Union _ Γ (Singleton _ A), A0 --> B0) :: (Union _ Γ (Singleton _ A), A0) :: nil)). apply in_eq.
  assert (J02: List.In (Union _ Γ (Singleton _ A), A0) ((Union _ Γ (Singleton _ A), A0 --> B0) :: (Union _ Γ (Singleton _ A), A0) :: nil)). apply in_cons. apply in_eq.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 --> B0 = A0 --> B0). reflexivity.
  pose (H0 (Union _ Γ (Singleton _ A), A0 --> B0) J01 A (A0 --> B0) Γ J1 J2).
  destruct e. subst.
  assert (J3: A0 = A0). reflexivity.
  pose (H0 (Union _ Γ (Singleton _ A), A0) J02 A A0 Γ J1 J3). destruct e.
  exists (max x x0).
  apply MPs with (ps:=[(Γ, ((DN_form (Init.Nat.max x x0) A) ∧ A0 --> B0) --> ((DN_form (Init.Nat.max x x0) A) --> B0));(Γ, (DN_form (Init.Nat.max x x0) A) ∧ A0 --> B0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  apply MPs with (ps:=[(Γ, ((DN_form (Init.Nat.max x x0) A) --> (DN_form (Init.Nat.max x x0) A) ∧ A0) --> ((DN_form (Init.Nat.max x x0) A) ∧ A0 --> B0) --> ((DN_form (Init.Nat.max x x0) A) --> B0));(Γ, (DN_form (Init.Nat.max x x0) A) --> (DN_form (Init.Nat.max x x0) A) ∧ A0)]).
  2: apply MPRule_I. intros. inversion H5. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists (DN_form (Init.Nat.max x x0) A). exists ((DN_form (Init.Nat.max x x0) A) ∧ A0). exists B0. auto.
  inversion H6. subst.
  apply MPs with (ps:=[(Γ, ((DN_form (Init.Nat.max x x0) A) --> A0) --> ((DN_form (Init.Nat.max x x0) A) --> (DN_form (Init.Nat.max x x0) A) ∧ A0));(Γ, (DN_form (Init.Nat.max x x0) A) --> A0)]).
  2: apply MPRule_I. intros. inversion H7. subst.
  apply MPs with (ps:=[(Γ, ((DN_form (Init.Nat.max x x0) A) --> (DN_form (Init.Nat.max x x0) A)) --> ((DN_form (Init.Nat.max x x0) A) --> A0) --> ((DN_form (Init.Nat.max x x0) A) --> (DN_form (Init.Nat.max x x0) A) ∧ A0));
  (Γ, (DN_form (Init.Nat.max x x0) A) --> (DN_form (Init.Nat.max x x0) A))]).
  2: apply MPRule_I. intros. inversion H8. subst. apply Axs.
  apply AxRule_I. apply RA7_I. exists (DN_form (Init.Nat.max x x0) A). exists (DN_form (Init.Nat.max x x0) A). exists A0. auto.
  inversion H9. subst. apply simp_Id_gen. inversion H10. inversion H8. subst. 2: inversion H9.
  apply MPs with (ps:=[(Γ, (DN_form x0 A --> A0) --> (DN_form (Init.Nat.max x x0) A --> A0));
  (Γ, DN_form x0 A --> A0)]).
  2: apply MPRule_I. intros. inversion H9. subst.
  apply MPs with (ps:=[(Γ, (DN_form (Init.Nat.max x x0) A --> DN_form x0 A) --> (DN_form x0 A --> A0) --> (DN_form (Init.Nat.max x x0) A --> A0));
  (Γ, DN_form (Init.Nat.max x x0) A --> DN_form x0 A)]).
  2: apply MPRule_I. intros. inversion H10. subst. apply Axs.
  apply AxRule_I. apply RA1_I. exists (DN_form (Init.Nat.max x x0) A). exists (DN_form x0 A).
  exists A0. auto. inversion H11. subst. apply sT_for_DN. lia. inversion H12.
  inversion H10. subst. assumption. inversion H11. inversion H7. inversion H5. subst.
  apply MPs with (ps:=[(Γ, (DN_form (Init.Nat.max x x0) A --> A0 --> B0) --> ((DN_form (Init.Nat.max x x0) A) ∧ A0 --> B0));
  (Γ, (DN_form (Init.Nat.max x x0) A --> A0 --> B0))]). 2: apply MPRule_I.
  intros. inversion H6. subst. apply Axs. apply AxRule_I.
  apply RA8_I. exists (DN_form (Init.Nat.max x x0) A). exists A0. exists B0.
  auto. subst. inversion H7. subst.
  apply MPs with (ps:=[(Γ, (DN_form x A --> A0 --> B0) --> (DN_form (Init.Nat.max x x0) A --> A0 --> B0));
  (Γ, DN_form x A --> A0 --> B0)]). 2: apply MPRule_I. intros. inversion H8. subst.
  apply MPs with (ps:=[(Γ, (DN_form (Init.Nat.max x x0) A --> DN_form x A) --> (DN_form x A --> A0 --> B0) --> (DN_form (Init.Nat.max x x0) A --> A0 --> B0));
  (Γ, DN_form (Init.Nat.max x x0) A --> DN_form x A)]). 2: apply MPRule_I. intros. inversion H9. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (DN_form (Init.Nat.max x x0) A).
  exists (DN_form x A). exists (A0 --> B0). auto. subst. inversion H10. subst.
  apply sT_for_DN. lia. inversion H11. inversion H9. subst. assumption.
  inversion H10. inversion H8. inversion H6.
(* DNs *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J01: List.In (Union _ Γ (Singleton _ A), A0) ((Union _ Γ (Singleton _ A), A0) :: nil)). apply in_eq.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 = A0). reflexivity.
  pose (H0 (Union _ Γ (Singleton _ A), A0) J01 A A0 Γ J1 J2). destruct e.
  assert (DNsRule ((Γ, (DN_form x A) --> A0) :: nil) (Γ, ¬ (∞ (DN_form x A --> A0)))).
  apply DNsRule_I.
  assert (J3: (forall prem, List.In prem ((Γ, DN_form x A --> A0) :: nil) ->
  FOsBIH_rules prem)). intros. inversion H4. subst. 2: inversion H5. assumption.
  pose (DNs J3 H3).
  pose (sDN_dist_imp (DN_form x A) A0 Γ). exists (S x). simpl.
  apply MPs with (ps:=[(Γ, ¬ (∞ (DN_form x A --> A0)) --> ¬ (∞ (DN_form x A)) --> ¬ (∞ A0));
  (Γ, ¬ (∞ (DN_form x A --> A0)))]). 2: apply MPRule_I. intros. inversion H4. subst. 2: inversion H5.
  assumption. subst. assumption. inversion H6.
(* Gen *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: FOsBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form (Union form Γ (Singleton form A)) B, A0)). apply H. apply in_eq.
  assert (exists n : nat, FOsBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, DN_form n (subst_form ↑ A) --> A0)).
  apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form (Union form Γ (Singleton form A)) B, A0)) ; auto. apply in_eq.
  simpl. apply Extensionality_Ensembles. split ; intro ; intro. destruct H2. destruct H2. subst. inversion H3. subst. apply Union_introl.
  exists x0. split ; auto. subst. inversion H2. apply Union_intror. apply In_singleton. destruct H2. destruct H2. destruct H2. subst.
  exists x0. split ; auto. apply Union_introl ; auto. inversion H2. exists A. split ; auto. apply Union_intror ; apply In_singleton.
  destruct H2. exists x.
  apply MPs with (ps:=[(Γ, (∀ ((DN_form x A)[↑] --> A0)) --> (DN_form x A --> (∀ A0)));(Γ, ∀ ((DN_form x A)[↑] --> A0))]). 2: apply MPRule_I.
  intros. inversion H3. subst. apply Axs. apply AxRule_I. apply RA17_I. exists (DN_form x A). exists A0. auto. inversion H4.
  subst. 2: inversion H5. apply Gens with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (DN_form x A)[↑] --> A0)]). 2: apply GenRule_I.
  intros. inversion H5. 2: inversion H6. subst. auto. simpl. rewrite DN_dist_up. auto.
(* EC *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: FOsBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form (Union form Γ (Singleton form A)) B, A0 --> B0[↑])). apply H. apply in_eq.
  assert (exists n : nat, FOsBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, DN_form n A[↑] --> A0 --> B0[↑])).
  apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form (Union form Γ (Singleton form A)) B, A0 --> B0[↑])) ; auto. apply in_eq.
  apply Extensionality_Ensembles. split ; intro ; intro. destruct H2. destruct H2. subst. inversion H3. subst. apply Union_introl.
  exists x0. split ; auto. subst. inversion H2. apply Union_intror. apply In_singleton. destruct H2. destruct H2. destruct H2. subst.
  exists x0. split ; auto. apply Union_introl ; auto. inversion H2. exists A. split ; auto. apply Union_intror ; apply In_singleton.
  destruct H2. exists x.
  apply MPs with (ps:=[(Γ, ((DN_form x A ∧ (∃ A0)) --> B0) --> (DN_form x A --> (∃ A0) --> B0));(Γ, (DN_form x A ∧ (∃ A0)) --> B0)]). 2: apply MPRule_I.
  intros. inversion H3. subst. apply Axs. apply AxRule_I. apply RA9_I. exists (DN_form x A). exists (∃ A0). exists B0. auto. inversion H4.
  subst. 2: inversion H5.
  apply MPs with (ps:=[(Γ, (((∃ A0) ∧ DN_form x A) --> B0) --> (((DN_form x A) ∧ (∃ A0)) --> B0));(Γ, (∃ A0) ∧ (DN_form x A) --> B0)]). 2: apply MPRule_I.
  intros. inversion H5. subst.
  apply MPs with (ps:=[(Γ, (((DN_form x A) ∧ (∃ A0)) --> ((∃ A0) ∧ DN_form x A)) --> (((∃ A0) ∧ DN_form x A) --> B0) --> (((DN_form x A) ∧ (∃ A0)) --> B0));(Γ, (DN_form x A ∧ (∃ A0)) --> ((∃ A0) ∧ DN_form x A))]). 2: apply MPRule_I.
  intros. inversion H6. subst. apply Axs. apply AxRule_I. apply RA1_I. exists ((DN_form x A) ∧ (∃ A0)). exists ((∃ A0) ∧ DN_form x A). exists B0.
  auto. inversion H7. 2: inversion H8. subst. apply FOsBIH_extens_FOwBIH. apply comm_And_obj. inversion H6. 2: inversion H7. subst.
  apply MPs with (ps:=[(Γ, ((∃ A0) --> (DN_form x A) --> B0) --> ((∃ A0) ∧ (DN_form x A) --> B0));(Γ, (∃ A0) --> (DN_form x A) --> B0)]). 2: apply MPRule_I.
  intros. inversion H7. subst. apply Axs. apply AxRule_I. apply RA8_I. exists (∃ A0). exists (DN_form x A). exists B0. auto. inversion H8.
  2: inversion H9. subst. apply ECs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A0 --> ((DN_form x A) --> B0)[↑])]). 2: apply ECRule_I.
  intros. inversion H9. 2: inversion H10. subst. simpl.
  apply MPs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, ((A0 ∧ DN_form x A[↑]) --> B0[↑]) --> A0 --> (DN_form x A)[↑] --> B0[↑]);(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (A0 ∧ DN_form x A[↑]) --> B0[↑])]).
  2: apply MPRule_I. intros. inversion H10. subst. apply Axs. apply AxRule_I. apply RA9_I. exists A0. exists (DN_form x A[↑]). exists B0[↑]. rewrite DN_dist_up. auto.
  inversion H11. subst. 2: inversion H12.
  apply MPs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (DN_form x A[↑] ∧ A0 --> B0[↑]) --> (A0 ∧ DN_form x A[↑] --> B0[↑]));(fun x : form => exists B : form, x = B[↑] /\ In form Γ B,  DN_form x A[↑] ∧ A0 --> B0[↑])]).
  2: apply MPRule_I. intros. inversion H12. subst.
  apply MPs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, ((A0 ∧ DN_form x A[↑] ) --> (DN_form x A[↑] ∧ A0)) --> (DN_form x A[↑] ∧ A0 --> B0[↑]) --> (A0 ∧ DN_form x A[↑] --> B0[↑]));(fun x : form => exists B : form, x = B[↑] /\ In form Γ B,  (A0 ∧ DN_form x A[↑] ) --> (DN_form x A[↑] ∧ A0))]).
  2: apply MPRule_I. intros. inversion H13. subst. apply Axs. apply AxRule_I. apply RA1_I. exists (A0 ∧ DN_form x A[↑]).
  exists (DN_form x A[↑] ∧ A0). exists B0[↑]. auto. inversion H14. 2: inversion H15. subst. apply FOsBIH_extens_FOwBIH. apply comm_And_obj.
  inversion H13. 2: inversion H14. subst.
  apply MPs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (DN_form x A[↑] --> A0 --> B0[↑]) --> (DN_form x A[↑] ∧ A0 --> B0[↑]));(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, DN_form x A[↑] --> A0 --> B0[↑])]).
  2: apply MPRule_I. intros. inversion H14. subst. apply Axs. apply AxRule_I. apply RA8_I. exists (DN_form x A[↑]).
  exists A0. exists B0[↑]. auto. inversion H15. 2: inversion H16. subst. auto.
Qed.

Theorem gen_FOsBIH_Deduction_Theorem : forall A B Γ,
  spair_der (Union _ Γ (Singleton _ A), Singleton _ B) ->
      (exists n, spair_der (Γ, Singleton _ ((DN_form n A) --> B))).
Proof.
intros A B Γ spair. unfold spair_der. simpl. destruct spair.
destruct H. destruct H0. simpl in H1. simpl in H0. destruct x.
- simpl in H1.
  assert (J1: Union form Γ (Singleton form A) = Union form Γ (Singleton form A)). reflexivity.
  assert (J2: ⊥ = ⊥). reflexivity.
  pose (FOsBIH_Deduction_Theorem (Union _ Γ (Singleton _ A), ⊥) H1 A (⊥) Γ J1 J2).
  destruct e. exists x. exists [(DN_form x A --> B)]. repeat split. apply NoDup_cons.
  auto. apply NoDup_nil. intros. inversion H3 ; subst. apply In_singleton. inversion H4.
  apply MPs with (ps:=[(Γ, (DN_form x A --> B) --> ((DN_form x A --> B) ∨ (⊥))); (Γ, (DN_form x A --> B))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Axs. apply AxRule_I. apply RA2_I.
  exists (DN_form x A --> B). exists (⊥). auto. inversion H4. subst.
  apply MPs with (ps:=[(Γ, (⊥ --> B) --> (DN_form x A --> B));(Γ, ⊥ --> B)]).
  2: apply MPRule_I. intros. inversion H5. subst.
  apply MPs with (ps:=[(Γ, (DN_form x A --> ⊥) --> (⊥ --> B) --> (DN_form x A --> B));(Γ, DN_form x A --> ⊥)]).
  2: apply MPRule_I. intros. inversion H6. subst.
  apply Axs. apply AxRule_I. apply RA1_I. exists (DN_form x A). exists (⊥). exists B.
  auto. inversion H7. subst. assumption. inversion H8. inversion H6. subst. apply sEFQ. inversion H7. inversion H5.
- simpl in H1. destruct x. simpl in H1. assert (f=B). pose (H0 f). assert (List.In f (f :: nil)). apply in_eq.
  apply i in H2. inversion H2 ; auto. subst. apply sabsorp_Or1 in H1.
  assert (J1: Union form Γ (Singleton form A) = Union form Γ (Singleton form A)). reflexivity.
  assert (J2: B = B). reflexivity.
  pose (FOsBIH_Deduction_Theorem (Union _ Γ (Singleton _ A), B) H1 A B Γ J1 J2). destruct e.
  exists x. exists [(DN_form x A --> B)]. repeat split. apply NoDup_cons.
  auto. apply NoDup_nil. intros. inversion H3 ; subst. apply In_singleton. inversion H4.
  apply MPs with (ps:=[(Γ, (DN_form x A --> B) --> ((DN_form x A --> B) ∨ (⊥))); (Γ, (DN_form x A --> B))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Axs. apply AxRule_I. apply RA2_I.
  exists (DN_form x A --> B). exists (⊥). auto. inversion H4. subst.
  assumption. inversion H5.
  exfalso. simpl in H0. inversion H. apply H4. subst. pose (H0 f).
  assert (List.In f (f :: f0 :: x)). apply in_eq. pose (i H2). inversion i0. subst.
  pose (H0 f0). assert (List.In f0 (f :: f0 :: x)). apply in_cons. apply in_eq.
  pose (i1 H3). inversion i2. subst. apply in_eq.
Qed.

Lemma Closure_DN_strong : forall Γ A, FOsBIH_rules (Γ, A) -> forall n, FOsBIH_rules (Γ, DN_form n A).
Proof.
intros. induction n.
- simpl. auto.
- simpl. apply DNs with (ps:=[(Γ, DN_form n A)]).
  2: apply DNsRule_I. intros. inversion H0. subst. 2: inversion H1.
  auto.
Qed.

Theorem gen_FOsBIH_Double_Negated_Detachment_Theorem : forall A B Γ,
  (exists n, spair_der (Γ, Singleton _ ((DN_form n A) --> B))) ->
      spair_der (Union _ Γ (Singleton _ (A)), Singleton _ (B)).
Proof.
intros A B Γ spair. unfold spair_der. simpl. destruct spair.
destruct H. destruct H. destruct H0. simpl in H1. simpl in H0.
assert (x0 = [] \/ x0 = [DN_form x A --> B]).
{ destruct x0 ; subst ; simpl. auto. destruct x0 ; subst ; simpl ; auto. right. pose (H0 f).
  destruct i ; auto. simpl ; auto. exfalso. inversion H. inversion H5.
  apply H4. simpl. left. subst. pose (H0 f). destruct i ; auto. simpl ; auto.
  pose (H0 f0). destruct i ; auto. simpl ; auto. }
destruct H2.
- subst. simpl in H1. exists []. repeat split ; auto. intros. inversion H2. simpl.
  apply FOsBIH_monot with (Γ1:=Union _ Γ (Singleton _ A)) in H1 ; auto.
  intro. simpl. intros. apply Union_introl. auto.
- subst. simpl in H1. exists [B]. repeat split ; auto. apply NoDup_cons ; auto. apply NoDup_nil.
  intros. inversion H2. subst. apply In_singleton. inversion H3. simpl.
  apply sabsorp_Or1 in H1.
  apply MPs with (ps:=[(Union _ Γ (Singleton _ A), B --> (B ∨ ⊥));(Union _ Γ (Singleton _ A), B)]).
  2: apply MPRule_I. intros. inversion H2. subst. apply Axs. apply AxRule_I. apply RA2_I. exists B.
  exists ⊥. auto. inversion H3 ; subst. 2: inversion H4.
  apply MPs with (ps:=[(Union _ Γ (Singleton _ A), DN_form x A --> B);(Union _ Γ (Singleton _ A), DN_form x A)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  apply FOsBIH_monot with (Γ1:=Union _ Γ (Singleton _ A)) in H1 ; auto.
  intro. intros. apply Union_introl ; auto. inversion H5. subst. 2: inversion H6.
  apply Closure_DN_strong. apply Ids. apply IdRule_I. apply Union_intror. apply In_singleton.
Qed.

End sMeta.

