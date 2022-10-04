Require Import List.
Export ListNotations.

Require Import genT.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import BiInt_extens_interactions.
Require Import BiInt_remove_list.
Require Import wBIH_meta_interactions.


(* Some proof-theoretical results about list_disj. They are helpful in the manipulation
    of prime theories. *)

Lemma Id_list_disj : forall Γ l0 l1,
  wBIH_rules (Γ, list_disj l0 → list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- simpl. apply wEFQ.
- simpl. apply wmonotL_Or. apply IHl0.
Qed.

Lemma list_disj_app : forall l0 Γ A l1,
  wBIH_rules (Γ, A → list_disj (l0 ++ l1)) -> wBIH_rules (Γ, A → (Or (list_disj l0) (list_disj l1))).
Proof.
induction l0.
- simpl. intros.
  apply MP with (ps:=[(Γ, ((list_disj l1) → (Or (Bot V) (list_disj l1))) → (A → (Or (Bot V) (list_disj l1))));(Γ, (list_disj l1) → (Or (Bot V) (list_disj l1)))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → (list_disj l1)) → ((list_disj l1) → (Or (Bot V) (list_disj l1))) → (A → (Or (Bot V) (list_disj l1))));(Γ,A → (list_disj l1))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists (list_disj l1). exists ((Or (Bot V) (list_disj l1))). auto. inversion H2.
  2: inversion H3. subst. assumption. inversion H1. 2: inversion H2. subst. apply Ax.
  apply AxRule_I. apply RA3_I. exists (Bot V). exists (list_disj l1). auto.
- simpl. intros.
  apply MP with (ps:=[(Γ, ((Or a (list_disj (l0 ++ l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))) → (A → ((Or (Or a (list_disj l0))) (list_disj l1))));
  (Γ,  ((Or a (list_disj (l0 ++ l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → (Or a (list_disj (l0 ++ l1)))) → ((Or a (list_disj (l0 ++ l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))) → (A → ((Or (Or a (list_disj l0))) (list_disj l1))));
  (Γ,  A → (Or a (list_disj (l0 ++ l1))))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists ((Or a (list_disj (l0 ++ l1)))). exists (((Or (Or a (list_disj l0))) (list_disj l1))).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst.
  apply MP with (ps:=[(Γ, ((Or a (Or (list_disj l0) (list_disj l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))) → ((Or a (list_disj (l0 ++ l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))));
  (Γ, ((Or a (Or (list_disj l0) (list_disj l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, ((Or a (list_disj (l0 ++ l1))) → (Or a (Or (list_disj l0) (list_disj l1)))) → ((Or a (Or (list_disj l0) (list_disj l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))) → ((Or a (list_disj (l0 ++ l1))) → ((Or (Or a (list_disj l0))) (list_disj l1))));
  (Γ, ((Or a (list_disj (l0 ++ l1))) → (Or a (Or (list_disj l0) (list_disj l1)))))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists ((Or a (list_disj (l0 ++ l1)))). exists ((Or a (Or (list_disj l0) (list_disj l1)))).
  exists (((Or (Or a (list_disj l0))) (list_disj l1))). auto. inversion H4. 2: inversion H5.
  subst. apply wmonotL_Or. apply IHl0. apply wimp_Id_gen. inversion H3. 2: inversion H4. subst.
  remember (list_disj l0) as E. remember (list_disj l1) as F.
  apply MP with (ps:=[(Γ, ((Or E F) → (Or (Or a E) F)) → ((Or a (Or E F)) → (Or (Or a E) F)));
  (Γ, ((Or E F) → (Or (Or a E) F)))]). 2: apply MPRule_I. intros. inversion H4. rewrite <- H5.
  apply MP with (ps:=[(Γ, (a → (Or (Or a E) F)) → ((Or E F) → (Or (Or a E) F)) → ((Or a (Or E F)) → (Or (Or a E) F)));
  (Γ, (a → (Or (Or a E) F)))]). 2: apply MPRule_I. intros. inversion H6. rewrite <- H7.
  apply Ax. apply AxRule_I. apply RA4_I. exists a. exists (Or E F). exists ((Or (Or a E) F)).
  auto. inversion H7. 2: inversion H8. rewrite <- H8.
  apply MP with (ps:=[(Γ, ((Or a E) → (Or (Or a E) F)) → (a → (Or (Or a E) F)));(Γ, ((Or a E) → (Or (Or a E) F)))]).
  2: apply MPRule_I. intros. inversion H9. rewrite <- H10.
  apply MP with (ps:=[(Γ, (a → (Or a E)) → ((Or a E) → (Or (Or a E) F)) → (a → (Or (Or a E) F)));(Γ, a → (Or a E))]).
  2: apply MPRule_I. intros. inversion H11. rewrite <- H12. apply Ax. apply AxRule_I.
  apply RA1_I. exists a. exists (Or a E). exists ((Or (Or a E) F)). auto.
  inversion H12. 2: inversion H13. rewrite <- H13. apply Ax. apply AxRule_I. apply RA2_I.
  exists a. exists E. auto. inversion H10. 2: inversion H11. rewrite <- H11. apply Ax.
  apply AxRule_I. apply RA2_I. exists (Or a E). exists F. auto. inversion H5. 2: inversion H6.
  rewrite <- H6. apply wmonotR_Or. apply Ax. apply AxRule_I. apply RA3_I. exists a. exists E. auto.
Qed.

Lemma list_disj_app0 : forall l0 Γ A l1,
  wBIH_rules (Γ, A → (Or (list_disj l0) (list_disj l1))) -> wBIH_rules (Γ, A → list_disj (l0 ++ l1)).
Proof.
induction l0.
- simpl. intros.
  apply MP with (ps:=[(Γ, ((Or (Bot V) (list_disj l1)) → list_disj l1) → (A → list_disj l1));
  (Γ, (Or (Bot V) (list_disj l1)) → list_disj l1)]). 2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → (Or (Bot V) (list_disj l1))) → ((Or (Bot V) (list_disj l1)) → list_disj l1) → (A → list_disj l1));
  (Γ, A → (Or (Bot V) (list_disj l1)))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists A. exists ((Or (Bot V) (list_disj l1))).
  exists (list_disj l1). auto. inversion H2. 2: inversion H3. subst. auto. inversion H1.
  2: inversion H2. subst.
  apply MP with (ps:=[(Γ, ((list_disj l1) → list_disj l1) → ((Or (Bot V) (list_disj l1)) → list_disj l1));
  (Γ, (list_disj l1) → list_disj l1)]). 2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, ((Bot V) → list_disj l1) → ((list_disj l1) → list_disj l1) → ((Or (Bot V) (list_disj l1)) → list_disj l1));
  (Γ, (Bot V) → list_disj l1)]). 2: apply MPRule_I. intros. inversion H3. subst.
  apply Ax. apply AxRule_I. apply RA4_I. exists (Bot V). exists (list_disj l1).
  exists (list_disj l1). auto. inversion H4. 2: inversion H5. subst. apply wEFQ.
  inversion H3. 2: inversion H4. subst. apply wimp_Id_gen.
- simpl. intros.
  apply MP with (ps:=[(Γ, (((Or (Or a (list_disj l0))) (list_disj l1)) → (Or a (list_disj (l0 ++ l1)))) → (A → (Or a (list_disj (l0 ++ l1)))));
  (Γ, (((Or (Or a (list_disj l0))) (list_disj l1)) → (Or a (list_disj (l0 ++ l1)))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → ((Or (Or a (list_disj l0))) (list_disj l1))) → (((Or (Or a (list_disj l0))) (list_disj l1)) → (Or a (list_disj (l0 ++ l1)))) → (A → (Or a (list_disj (l0 ++ l1)))));
  (Γ,  A → ((Or (Or a (list_disj l0))) (list_disj l1)))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists (((Or (Or a (list_disj l0))) (list_disj l1))). exists ((Or a (list_disj (l0 ++ l1)))).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst.
  apply MP with (ps:=[(Γ, ((Or a (Or (list_disj l0) (list_disj l1))) → (Or a (list_disj (l0 ++ l1)))) → (((Or (Or a (list_disj l0))) (list_disj l1)) → (Or a (list_disj (l0 ++ l1)))));
  (Γ, ((Or a (Or (list_disj l0) (list_disj l1))) → (Or a (list_disj (l0 ++ l1)))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (((Or (Or a (list_disj l0))) (list_disj l1)) → (Or a (Or (list_disj l0) (list_disj l1)))) → ((Or a (Or (list_disj l0) (list_disj l1))) → (Or a (list_disj (l0 ++ l1)))) → (((Or (Or a (list_disj l0))) (list_disj l1)) → (Or a (list_disj (l0 ++ l1)))));
  (Γ, (((Or (Or a (list_disj l0))) (list_disj l1)) → (Or a (Or (list_disj l0) (list_disj l1)))))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists (((Or (Or a (list_disj l0))) (list_disj l1))).
  exists ((Or a (Or (list_disj l0) (list_disj l1)))). exists ((Or a (list_disj (l0 ++ l1)))).
  auto. inversion H4. 2: inversion H5.
  subst. remember (list_disj l0) as E. remember (list_disj l1) as F.
  apply MP with (ps:=[(Γ, (F → (Or a (Or E F))) → ((Or (Or a E) F) → (Or a (Or E F))));
  (Γ, F → (Or a (Or E F)))]). 2: apply MPRule_I. intros. inversion H5. rewrite <- H6.
  apply MP with (ps:=[(Γ, ((Or a E) → (Or a (Or E F))) → (F → (Or a (Or E F))) → ((Or (Or a E) F) → (Or a (Or E F))));
  (Γ, ((Or a E) → (Or a (Or E F))))]). 2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
  apply Ax. apply AxRule_I. apply RA4_I. exists (Or a E). exists F. exists ((Or a (Or E F))).
  auto. inversion H8. 2: inversion H9. rewrite <- H9. apply wmonotL_Or. apply Ax.
  apply AxRule_I. apply RA2_I. exists E. exists F. auto. inversion H6. 2: inversion H7.
  rewrite <- H7.
  apply MP with (ps:=[(Γ, ((Or E F) → (Or a (Or E F))) → (F → (Or a (Or E F))));(Γ, ((Or E F) → (Or a (Or E F))))]).
  2: apply MPRule_I. intros. inversion H8. rewrite <- H9.
  apply MP with (ps:=[(Γ, (F → (Or E F)) → ((Or E F) → (Or a (Or E F))) → (F → (Or a (Or E F))));(Γ, F → (Or E F))]).
  2: apply MPRule_I. intros. inversion H10. rewrite <- H11. apply Ax. apply AxRule_I.
  apply RA1_I. exists F. exists (Or E F). exists ((Or a (Or E F))). auto.
  inversion H11. 2: inversion H12. rewrite <- H12. apply Ax. apply AxRule_I. apply RA3_I.
  exists E. exists F. auto. inversion H9. 2: inversion H10. rewrite <- H10. apply Ax.
  apply AxRule_I. apply RA3_I. exists a. exists (Or E F). auto. inversion H3. 2: inversion H4.
  rewrite <- H4. apply wmonotL_Or. apply IHl0. apply wimp_Id_gen.
Qed.


Notation "A ∨ B" := (Or A B) (at level 13, right associativity) : My_scope.

Lemma list_disj_remove_app : forall l0 l1 Γ A,
wBIH_rules (Γ, list_disj (l0 ++ remove_list l0 l1) → (Or A (list_disj (l0 ++ remove eq_dec_form A (remove_list l0 l1))))).
Proof.
induction l0.
- simpl. intros. apply remove_disj.
- simpl. intros.
  apply MP with (ps:=[(Γ, (a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  → A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) → (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))));
  (Γ,a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  → A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1))))))]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Γ, (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) → (a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  → A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) → (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))));
  (Γ,(a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA1_I.
  exists (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))).
  exists (a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))).
  exists (A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))). auto.
  inversion H1. 2: inversion H2. subst.
  { simpl. apply wmonotL_Or. clear H1. clear H0. clear H.
    remember (remove eq_dec_form a (remove_list l0 l1)) as E.
    apply MP with (ps:=[(Γ, (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E))) → A ∨ (list_disj (l0 ++ remove eq_dec_form A E))) → (list_disj (l0 ++ E) → A ∨ (list_disj (l0 ++ remove eq_dec_form A E))));
    (Γ, (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E))) → A ∨ (list_disj (l0 ++ remove eq_dec_form A E))))]).
    2: apply MPRule_I. intros. inversion H. rewrite <- H0.
    apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) → A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))) → (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E))) → A ∨ (list_disj (l0 ++ remove eq_dec_form A E))) → (list_disj (l0 ++ E) → A ∨ (list_disj (l0 ++ remove eq_dec_form A E))));
    (Γ, (list_disj (l0 ++ E) → A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))))]).
    2: apply MPRule_I. intros. inversion H1. rewrite <- H2. apply Ax. apply AxRule_I.
    apply RA1_I. exists (list_disj (l0 ++ E)). exists (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))).
    exists (A ∨ (list_disj (l0 ++ remove eq_dec_form A E))). auto. inversion H2. rewrite <- H3.
    { simpl. apply MP with (ps:=[(Γ, (((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) → A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))) → (list_disj (l0 ++ E) → A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))));
    (Γ, (((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) → A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))))]).
    2: apply MPRule_I. intros. inversion H4. rewrite <- H5.
    apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) → ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E))))) → (((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) → A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))) → (list_disj (l0 ++ E) → A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))));
    (Γ, (list_disj (l0 ++ E) → ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E))))))]).
    2: apply MPRule_I. intros. inversion H6. rewrite <- H7. apply Ax. apply AxRule_I. apply RA1_I.
    exists (list_disj (l0 ++ E)). exists ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))).
    exists (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))). auto.
    inversion H7. 2: inversion H8. rewrite <- H8.
    { remember ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) as F.
      apply MP with (ps:=[(Γ, (((list_disj l0) ∨ (list_disj E)) → F) → (list_disj (l0 ++ E) → F));
      (Γ, (((list_disj l0) ∨ (list_disj E)) → F))]). 2: apply MPRule_I. intros.
      inversion H9. rewrite <- H10.
      apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) → ((list_disj l0) ∨ (list_disj E))) → (((list_disj l0) ∨ (list_disj E)) → F) → (list_disj (l0 ++ E) → F));
      (Γ, list_disj (l0 ++ E) → ((list_disj l0) ∨ (list_disj E)))]). 2: apply MPRule_I. intros.
      inversion H11. rewrite <- H12. apply Ax. apply AxRule_I. apply RA1_I.
      exists (list_disj (l0 ++ E)). exists ((list_disj l0) ∨ (list_disj E)). exists F. auto.
      inversion H12. 2: inversion H13. rewrite <- H13. apply list_disj_app. apply wimp_Id_gen.
      inversion H10. 2: inversion H11. rewrite <- H11. clear H11. clear H10.
      clear H9. clear H8. clear H7. clear H6. clear H5. clear H0. clear H4.
      clear H3. clear H2. clear H1. clear H. rewrite HeqF. apply wmonotL_Or.
      apply remove_disj. }
    inversion H5. 2: inversion H6. rewrite <- H6. remember (list_disj l0) as D.
    remember (list_disj (remove eq_dec_form A E)) as F.
    apply MP with (ps:=[(Γ, (A ∨ F → A ∨ (D ∨ F)) → (D ∨ (A ∨ F) → A ∨ (D ∨ F)));(Γ, (A ∨ F) → A ∨ (D ∨ F))]).
    2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
    apply MP with (ps:=[(Γ, (D → A ∨ (D ∨ F)) → (A ∨ F → A ∨ (D ∨ F)) → (D ∨ (A ∨ F) → A ∨ (D ∨ F)));(Γ, D → A ∨ (D ∨ F))]).
    2: apply MPRule_I. intros. inversion H9. rewrite <- H10. apply Ax. apply AxRule_I.
    apply RA4_I. exists D. exists (A ∨ F). exists (A ∨ (D ∨ F)). auto. inversion H10. 2: inversion H11.
    rewrite <- H11.
    apply MP with (ps:=[(Γ, ((D ∨ F) → A ∨ (D ∨ F)) → (D → A ∨ (D ∨ F)));(Γ, ((D ∨ F) → A ∨ (D ∨ F)))]).
    2: apply MPRule_I. intros. inversion H12. rewrite <- H13.
    apply MP with (ps:=[(Γ, (D → (D ∨ F)) → ((D ∨ F) → A ∨ (D ∨ F)) → (D → A ∨ (D ∨ F)));(Γ, D → (D ∨ F))]).
    2: apply MPRule_I. intros. inversion H14. rewrite <- H15. apply Ax. apply AxRule_I.
    apply RA1_I. exists D. exists (D ∨ F). exists (A ∨ (D ∨ F)). auto. inversion H15.
    rewrite <- H16. apply Ax. apply AxRule_I. apply RA2_I. exists D. exists F. auto.
    inversion H16. inversion H13. rewrite <- H14. apply Ax. apply AxRule_I. apply RA3_I.
    exists A. exists (D ∨ F). auto. inversion H14. inversion H8. rewrite <- H9.
    apply wmonotL_Or. apply Ax. apply AxRule_I. apply RA3_I. exists D. exists F. auto.
    inversion H9. }
    inversion H3. inversion H0. 2: inversion H1. rewrite <- H1. apply wmonotL_Or. apply list_disj_app0.
    apply wimp_Id_gen. }
  inversion H0. 2: inversion H1. subst.
  remember ((list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1))))) as E.
  apply MP with (ps:=[(Γ, ((A ∨ E) → A ∨ (Or a E)) → (a ∨ (A ∨ E) → A ∨ (Or a E)));
  (Γ, ((A ∨ E) → A ∨ (Or a E)))]). 2: apply MPRule_I. intros. inversion H1. rewrite <- H2.
  apply MP with (ps:=[(Γ, (a → A ∨ (Or a E)) → ((A ∨ E) → A ∨ (Or a E)) → (a ∨ (A ∨ E) → A ∨ (Or a E)));
  (Γ, (a → A ∨ (Or a E)))]). 2: apply MPRule_I. intros. inversion H3. rewrite <- H4. clear H4.
  clear H2. apply Ax. apply AxRule_I. apply RA4_I. exists a. exists (A ∨ E).
  exists (A ∨ (Or a E)). auto. inversion H4. 2: inversion H5. rewrite <- H5.
  apply MP with (ps:=[(Γ, ((Or a E) → A ∨ (Or a E)) → (a → A ∨ (Or a E))); (Γ, ((Or a E) → A ∨ (Or a E)))]).
  2: apply MPRule_I. intros. inversion H6. rewrite <- H7.
  apply MP with (ps:=[(Γ, (a → (Or a E)) → ((Or a E) → A ∨ (Or a E)) → (a → A ∨ (Or a E))); (Γ, a → (Or a E))]).
  2: apply MPRule_I. intros. inversion H8. rewrite <- H9. apply Ax. apply AxRule_I. apply RA1_I.
  exists a. exists (Or a E). exists (A ∨ (Or a E)). auto. inversion H9.
  rewrite <- H10. 2: inversion H10. apply Ax. apply AxRule_I. apply RA2_I.
  exists a. exists E. auto. inversion H7. 2: inversion H8. rewrite <- H8.
  apply Ax. apply AxRule_I. apply RA3_I. exists A. exists (Or a E). auto.
  inversion H2. rewrite <- H3. apply wmonotL_Or. apply Ax. apply AxRule_I.
  apply RA3_I. exists a. exists E. auto. inversion H3.
Qed.

Lemma Id_list_disj_remove : forall Γ l0 l1,
  wBIH_rules (Γ, list_disj l1 → list_disj (l0 ++ remove_list l0 l1)).
Proof.
induction l0.
- intros. simpl. apply wimp_Id_gen.
- simpl. intros.
  apply MP with (ps:=[(Γ, (list_disj (l0 ++ remove_list l0 l1) → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (list_disj l1 → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, list_disj (l0 ++ remove_list l0 l1) → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1))))]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Γ, (list_disj l1 → list_disj (l0 ++ remove_list l0 l1)) → (list_disj (l0 ++ remove_list l0 l1) → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (list_disj l1 → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ,list_disj l1 → list_disj (l0 ++ remove_list l0 l1))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists (list_disj l1). exists (list_disj (l0 ++ remove_list l0 l1)).
  exists (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))). auto.
  inversion H1. 2: inversion H2. subst. apply IHl0. inversion H0. subst.
  clear H. clear H0. apply list_disj_remove_app. inversion H1.
Qed.

Lemma der_list_disj_remove1 : forall Γ A l0 l1,
    (wBIH_rules (Γ, A → list_disj l0)) ->
    (wBIH_rules (Γ, A → list_disj (l0 ++ remove_list l0 l1))).
Proof.
intros Γ A. induction l0.
- simpl. intros.
  apply MP with (ps:=[(Γ, ((Bot V) → list_disj l1) → (A → list_disj l1));
  (Γ, (Bot V) → list_disj l1)]). 2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → (Bot V)) → ((Bot V) → list_disj l1) → (A → list_disj l1));
  (Γ, A → (Bot V))]). 2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists (Bot V). exists (list_disj l1).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst. apply wEFQ.
- intros. subst. simpl. simpl in H.
  apply MP with (ps:=[(Γ, (a ∨ (list_disj l0) → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (A → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, (a ∨ (list_disj l0) → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → a ∨ (list_disj l0)) → (a ∨ (list_disj l0) → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (A → a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, A → a ∨ (list_disj l0))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (Or a (list_disj l0)).
  exists (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))). auto.
  inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst. clear H0. clear H1. apply wmonotL_Or. apply Id_list_disj.
Qed.

Lemma der_list_disj_remove2 : forall Γ A l0 l1,
    (wBIH_rules (Γ, A → list_disj l1)) ->
    (wBIH_rules (Γ, A → list_disj (l0 ++ remove_list l0 l1))).
Proof.
intros.
apply MP with (ps:=[(Γ, (list_disj l1 → (list_disj (l0 ++ (remove_list l0 l1)))) → (A → (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, (list_disj l1 → (list_disj (l0 ++ (remove_list l0 l1)))))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A → list_disj l1) → (list_disj l1 → (list_disj (l0 ++ (remove_list l0 l1)))) → (A → (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, A → list_disj l1)]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists A. exists (list_disj l1). exists (list_disj (l0 ++ (remove_list l0 l1))).
auto. inversion H2. 2 : inversion H3. subst. auto. inversion H1. subst. 2: inversion H2.
clear H0. clear H1.
apply MP with (ps:=[(Γ, ((list_disj (l0 ++ (remove_list l0 l1))) → (list_disj (l0 ++ (remove_list l0 l1)))) → (list_disj l1 → (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, (list_disj (l0 ++ (remove_list l0 l1))) → (list_disj (l0 ++ (remove_list l0 l1))))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (list_disj l1 → (list_disj (l0 ++ (remove_list l0 l1)))) → ((list_disj (l0 ++ (remove_list l0 l1))) → (list_disj (l0 ++ (remove_list l0 l1)))) → (list_disj l1 → (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, (list_disj l1 → (list_disj (l0 ++ (remove_list l0 l1)))))]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
exists (list_disj l1). exists ((list_disj (l0 ++ (remove_list l0 l1)))).
exists (list_disj (l0 ++ (remove_list l0 l1))). auto. inversion H2.
2: inversion H3. subst. clear H1. clear H2. clear H0. apply Id_list_disj_remove.
inversion H1. 2: inversion H2. subst. clear H0. clear H1. apply wimp_Id_gen.
Qed.

Lemma absorp_Or2 : forall A Γ,
    (wBIH_rules (Γ, (Bot V) ∨ A)) ->
    (wBIH_rules (Γ, A)).
Proof.
intros A Γ D.
apply MP with (ps:=[(Γ, ((Bot V) ∨ A)→ A);(Γ, (Bot V) ∨ A)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A→ A)→ (((Bot V) ∨ A)→ A));(Γ, (A→ A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, ((Bot V)→ A)→ (A→ A)→ (((Bot V) ∨ A)→ A));(Γ, (Bot V)→ A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists (Bot V). exists A.
exists A. auto. inversion H2. subst. apply wEFQ. inversion H1. inversion H3.
inversion H3. inversion H1. subst. apply wimp_Id_gen. inversion H2.
inversion H0. subst. assumption. inversion H1.
Qed.

Lemma der_list_disj_bot : forall l Γ,
  wBIH_rules (Γ, list_disj l) -> wBIH_rules (Γ, list_disj (remove eq_dec_form (Bot V) l)).
Proof.
induction l.
- simpl. intros ; auto.
- intros. simpl in H. simpl. destruct (eq_dec_form (Bot V) a).
  + subst. apply IHl. apply absorp_Or2 ; auto.
  + simpl. apply MP with (ps:=[(Γ, (a ∨ list_disj l) → (a ∨ list_disj (remove eq_dec_form (Bot V) l)));(Γ, a ∨ list_disj l)]).
     intros. 2: apply MPRule_I. inversion H0. subst.
     apply MP with (ps:=[(Γ, (list_disj l → a ∨ list_disj (remove eq_dec_form (Bot V) l)) → ((a ∨ list_disj l) → (a ∨ list_disj (remove eq_dec_form (Bot V) l))));
     (Γ, list_disj l → a ∨ list_disj (remove eq_dec_form (Bot V) l))]).
     intros. 2: apply MPRule_I. inversion H1. subst.
     apply MP with (ps:=[(Γ, (a → a ∨ list_disj (remove eq_dec_form (Bot V) l)) → (list_disj l → a ∨ list_disj (remove eq_dec_form (Bot V) l)) → ((a ∨ list_disj l) → (a ∨ list_disj (remove eq_dec_form (Bot V) l))));
     (Γ, a → a ∨ list_disj (remove eq_dec_form (Bot V) l))]).
     intros. 2: apply MPRule_I. inversion H2. subst. apply Ax. apply AxRule_I. apply RA4_I.
     exists a. exists (list_disj l). exists (a ∨ list_disj (remove eq_dec_form (Bot V) l)). auto. inversion H3 ; subst.
     2: inversion H4. apply Ax. apply AxRule_I. apply RA2_I. exists a. exists (list_disj (remove eq_dec_form (Bot V) l)). auto.
     inversion H2 ; subst. 2: inversion H3.
     apply MP with (ps:=[(Γ, (list_disj (remove eq_dec_form (Bot V) l) → a ∨ list_disj (remove eq_dec_form (Bot V) l)) → (list_disj l → a ∨ list_disj (remove eq_dec_form (Bot V) l)));
     (Γ, (list_disj (remove eq_dec_form (Bot V) l) → a ∨ list_disj (remove eq_dec_form (Bot V) l)))]). 2: apply MPRule_I.
     intros. inversion H3. subst.
     apply MP with (ps:=[(Γ, (list_disj l → list_disj (remove eq_dec_form (Bot V) l)) → (list_disj (remove eq_dec_form (Bot V) l) → a ∨ list_disj (remove eq_dec_form (Bot V) l)) → (list_disj l → a ∨ list_disj (remove eq_dec_form (Bot V) l)));
     (Γ, list_disj l → list_disj (remove eq_dec_form (Bot V) l))]). 2: apply MPRule_I.
     intros. inversion H4. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (list_disj l).
     exists (list_disj (remove eq_dec_form (Bot V) l)). exists (a ∨ list_disj (remove eq_dec_form (Bot V) l)). auto.
     inversion H5. subst. apply wBIH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (list_disj l)), list_disj (remove eq_dec_form (Bot V) l))) ; auto.
     apply IHl. apply Id. apply IdRule_I. apply Union_intror. apply In_singleton. inversion H6.
     inversion H4. subst. 2: inversion H5. apply Ax. apply AxRule_I. apply RA3_I. exists a.
     exists (list_disj (remove eq_dec_form (Bot V) l)). auto. inversion H1. subst. 2: inversion H2. auto.
Qed.

Lemma list_disj_remove__ : forall l Γ A,
  wBIH_rules (Γ, list_disj l) -> wBIH_rules (Γ, A ∨ list_disj (remove eq_dec_form A l)).
Proof.
intros. pose (remove_disj l A Γ).
apply wBIH_Detachment_Theorem with (A:= list_disj l) (B:=A ∨ list_disj (remove eq_dec_form A l)) (Γ:=Γ) in w ; auto.
pose (wBIH_comp _ w Γ). apply w0. intros. simpl in H0. inversion H0 ; subst.
apply Id. apply IdRule_I. auto. inversion H1. subst. auto.
Qed.

Lemma list_disj_In0 : forall l Γ A,
  List.In A l ->
  wBIH_rules (Γ, A → list_disj l).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  * subst. simpl. apply Ax. apply AxRule_I. apply RA2_I. exists A. exists (list_disj l). auto.
  * simpl. apply MP with (ps:=[(Γ, (list_disj l → a ∨ list_disj l) → (A → a ∨ list_disj l));(Γ, (list_disj l → a ∨ list_disj l))]).
    2: apply MPRule_I. intros. inversion H1. subst.
    apply MP with (ps:=[(Γ, (A → list_disj l) → (list_disj l → a ∨ list_disj l) → (A → a ∨ list_disj l));(Γ, (A → list_disj l))]).
    2: apply MPRule_I. intros. inversion H2. subst.
    apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (list_disj l). exists (a ∨ list_disj l). auto. inversion H3.
    subst. 2: inversion H4. apply IHl ; auto. inversion H2. subst. apply Ax. apply AxRule_I. apply RA3_I. exists a. exists (list_disj l). auto.
    inversion H3.
Qed.

Lemma list_disj_In : forall l Γ A,
  List.In A l ->
  wBIH_rules (Γ, A ∨ list_disj l) ->
  wBIH_rules (Γ,list_disj l).
Proof.
induction l.
- simpl. intros. inversion H.
- intros. simpl. simpl in H0.
  apply MP with (ps:=[(Γ, (A ∨ (a ∨ list_disj l)) → (a ∨ list_disj l));(Γ, A ∨ (a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H1. 2: inversion H2 ; subst ; auto. 2: inversion H3. subst.
  apply MP with (ps:=[(Γ, ((a ∨ list_disj l) → (a ∨ list_disj l)) → ((A ∨ (a ∨ list_disj l)) → (a ∨ list_disj l)));(Γ, (a ∨ list_disj l) → (a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (A → (a ∨ list_disj l)) → ((a ∨ list_disj l) → (a ∨ list_disj l)) → ((A ∨ (a ∨ list_disj l)) → (a ∨ list_disj l)));(Γ, A → (a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA4_I. exists A. exists (a ∨ list_disj l ). exists (a ∨ list_disj l ). auto.
  inversion H4. subst. 2: inversion H5.
  inversion H. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A. exists (list_disj l). auto.
  apply MP with (ps:=[(Γ, (list_disj l → a ∨ list_disj l) → (A → a ∨ list_disj l));(Γ, (list_disj l → a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H6. subst.
  apply MP with (ps:=[(Γ, (A → list_disj l) → (list_disj l → a ∨ list_disj l) → (A → a ∨ list_disj l));(Γ, (A → list_disj l))]).
  2: apply MPRule_I. intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA1_I. exists A.
  exists (list_disj l). exists (a ∨ list_disj l). auto. inversion H8. subst. apply list_disj_In0 ; auto. inversion H9.
  inversion H7. subst. apply Ax. apply AxRule_I. apply RA3_I. exists a. exists (list_disj l). auto. inversion H8.
  inversion H3. subst. 2: inversion H4. apply wimp_Id_gen.
Qed.


(* ------------------------------------------------------------------------------------------------------ *)

(* Some proof-theoretical results about list_conj. *)

Fixpoint list_conj (l : list _) : BPropF V :=
match l with
 | nil => Top V
 | h :: t => And h (list_conj t)
end.

Notation "A ∧ B" := (And A B) (at level 13, right associativity) : My_scope.

Lemma list_conj_in_list : forall Γ l A,
  List.In A l ->
  wBIH_rules (Γ, (list_conj l) → A).
Proof.
induction l.
- intros. inversion H.
- intros. simpl. inversion H. subst. apply Ax. apply AxRule_I. apply RA5_I.
  exists A. exists (list_conj l). auto. apply IHl in H0.
  apply MP with (ps:=[(Γ, (list_conj l → A) → (a ∧ list_conj l → A));(Γ, list_conj l → A)]).
  2: apply MPRule_I. intros. inversion H1. subst.
  apply MP with (ps:=[(Γ, (a ∧ list_conj l → list_conj l) → (list_conj l → A) → (a ∧ list_conj l → A));(Γ, a ∧ list_conj l → list_conj l)]).
  2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists (a ∧ list_conj l). exists (list_conj l). exists A. auto. inversion H3. subst.
  apply Ax. apply AxRule_I. apply RA6_I. exists a. exists (list_conj l). auto. inversion H4.
  inversion H2. subst. auto. inversion H3.
Qed.

Lemma finite_context_list_conj : forall Γ A,
  wBIH_rules (Γ, A) ->
  (forall l, (forall A : _, (Γ A -> List.In A l) * (List.In A l -> Γ A)) ->
  wBIH_rules (Singleton _ (list_conj l), A)).
Proof.
intros. pose (wBIH_comp _ H (Singleton _ (list_conj l))). apply w. intros. clear w.
simpl in H1.
apply MP with (ps:=[(Singleton _ (list_conj l), (list_conj l) → A0);(Singleton _ (list_conj l), list_conj l)]).
2: apply MPRule_I. intros. inversion H2. subst. apply list_conj_in_list. apply H0. auto.
inversion H3. subst. 2: inversion H4. apply Id. apply IdRule_I. apply In_singleton.
Qed.

Lemma der_list_conj_finite_context : forall l (Γ : Ensemble _),
  (forall B : _, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  wBIH_rules (Γ, list_conj l).
Proof.
induction l ; intros.
- simpl. apply wTop.
- simpl. destruct (In_dec l a).
  + assert (forall B : _, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
     intros. split ; intro. apply H in H0. inversion H0. subst. auto. auto.
     apply H. apply in_cons ; auto. pose (IHl Γ H0).
     apply MP with (ps:=[(Γ, list_conj l → (a ∧ list_conj l));(Γ, list_conj l)]). 2: apply MPRule_I.
     intros. inversion H1. subst.
     apply MP with (ps:=[(Γ, (list_conj l → list_conj l) → (list_conj l → (a ∧ list_conj l)));(Γ, list_conj l → list_conj l)]). 2: apply MPRule_I.
     intros. inversion H2. subst.
     apply MP with (ps:=[(Γ, (list_conj l → a) → (list_conj l → list_conj l) → (list_conj l → (a ∧ list_conj l)));(Γ, list_conj l → a)]). 2: apply MPRule_I.
     intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA7_I. exists (list_conj l). exists a. exists (list_conj l). auto.
     inversion H4. 2: inversion H5. subst. apply MP with (ps:=[(Γ, a → list_conj l → a);(Γ, a)]).
     2: apply MPRule_I. intros. inversion H5. subst. apply wThm_irrel. inversion H6. subst. apply Id.
     apply IdRule_I. apply H. apply in_eq. inversion H7. inversion H3. subst. apply wimp_Id_gen. inversion H4.
     inversion H2 ; subst ; auto. inversion H3.
  + assert (J1: (forall B : _, ((fun x : _ => In _ Γ x /\ x <> a) B -> List.In B l) * (List.In B l -> (fun x : _ => In _ Γ x /\ x <> a) B))).
     intros. split ; intro. destruct H0. apply H in H0. inversion H0. subst. exfalso. apply H1 ; auto. auto.
     split. apply H. apply in_cons ; auto. intro. subst. auto.
     pose (IHl (fun x => In _ Γ x /\ x <> a) J1).
     apply MP with (ps:=[(Γ, list_conj l → (a ∧ list_conj l));(Γ, list_conj l)]). 2: apply MPRule_I.
     intros. inversion H0. subst.
     apply MP with (ps:=[(Γ, (list_conj l → list_conj l) → (list_conj l → (a ∧ list_conj l)));(Γ, list_conj l → list_conj l)]). 2: apply MPRule_I.
     intros. inversion H1. subst.
     apply MP with (ps:=[(Γ, (list_conj l → a) → (list_conj l → list_conj l) → (list_conj l → (a ∧ list_conj l)));(Γ, list_conj l → a)]). 2: apply MPRule_I.
     intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA7_I. exists (list_conj l). exists a. exists (list_conj l). auto.
     inversion H3. 2: inversion H4. subst. apply MP with (ps:=[(Γ, a → list_conj l → a);(Γ, a)]).
     2: apply MPRule_I. intros. inversion H4. subst. apply wThm_irrel. inversion H5. subst. apply Id.
     apply IdRule_I. apply H. apply in_eq. inversion H6. inversion H2. subst. apply wimp_Id_gen. inversion H3.
     inversion H1 ; subst ; auto. 2: inversion H2. apply wBIH_monot with (Γ1:=Γ) in w. apply w. simpl. intro. intros.
     inversion H2. auto.
Qed.

Lemma list_conj_finite_context : forall l (Γ : Ensemble _) A,
  (forall B : _, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  wBIH_rules (Singleton _ (list_conj l), A) ->
  wBIH_rules (Γ, A).
Proof.
intros.
assert (wBIH_rules (Singleton _ (list_conj l), list_conj l)). apply Id. apply IdRule_I. apply In_singleton.
assert (forall A : _, In _ (fst (Singleton _ (list_conj l), list_conj l)) A -> wBIH_rules (Γ, A)).
intros. simpl in H2. inversion H2. subst. apply der_list_conj_finite_context ; auto.
pose (wBIH_comp (Singleton _ (list_conj l), A) H0 Γ H2). simpl in w. auto.
Qed.

(* Dual MP *)

Theorem dual_MP : forall A B Δ,
  wpair_derrec (Singleton _ (Excl A B), Δ) ->
  wpair_derrec (Singleton _ B, Δ) ->
      wpair_derrec (Singleton _ A, Δ).
Proof.
intros. destruct H. destruct H0. destruct H. destruct H1. destruct H0. destruct H3. simpl in H1.
simpl in H2. simpl in H3. simpl in H4. unfold wpair_derrec. exists (x ++ remove_list x x0). repeat split.
apply add_remove_list_preserve_NoDup ; auto. intros. simpl. apply in_app_or in H5. destruct H5.
apply H1 ; auto. apply In_remove_list_In_list in H5. apply H3 ; auto. simpl.
assert (wBIH_rules (Singleton _ (Excl A B), list_disj (x ++ remove_list x x0))).
assert (Singleton _ (Excl A B) = Union _ (Empty_set _) (Singleton _ (Excl A B))).
apply Extensionality_Ensembles. split ; intro ; intro. apply Union_intror ; auto.
inversion H5. inversion H6. auto. rewrite H5. clear H5.
apply wBIH_Detachment_Theorem with (s:=(Empty_set _, Imp (Excl A B) (list_disj (x ++ remove_list x x0)))) ; auto.
apply der_list_disj_remove1. apply wBIH_Deduction_Theorem with (s:=( Union _ (Empty_set _) (Singleton _ (Excl A B)),list_disj x)) ; auto.
assert (Union _ (Empty_set _) (Singleton _ (Excl A B)) = Singleton _ (Excl A B)).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H5. inversion H6. auto.
apply Union_intror ; auto. rewrite H5. clear H5. auto.
assert (wBIH_rules (Singleton _ B, list_disj (x ++ remove_list x x0))).
assert (Singleton _ B = Union _ (Empty_set _) (Singleton _ B)).
apply Extensionality_Ensembles. split ; intro ; intro. apply Union_intror ; auto.
inversion H6. inversion H7. auto. rewrite H6. clear H6.
apply wBIH_Detachment_Theorem with (s:=(Empty_set _, B → list_disj (x ++ remove_list x x0))) ; auto.
apply der_list_disj_remove2. apply wBIH_Deduction_Theorem with (s:=( Union _ (Empty_set _) (Singleton _ B),list_disj x0)) ; auto.
assert (Union _ (Empty_set _) (Singleton _ B) = Singleton _ B).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H6. inversion H7. auto.
apply Union_intror ; auto. rewrite H6. clear H6. auto.
assert (Singleton _ A = Union _ (Empty_set _) (Singleton _ A)). apply Extensionality_Ensembles.
split ; intro ; intro. apply Union_intror ; auto. inversion H7. subst. inversion H8. subst. auto.
rewrite H7. clear H7.
apply wBIH_Detachment_Theorem with (s:=(Empty_set _, A → list_disj (x ++ remove_list x x0))) ; auto.
apply MP with (ps:=[(Empty_set _, ((B ∨ (Excl A B)) → list_disj (x ++ remove_list x x0)) → (A → list_disj (x ++ remove_list x x0)));
(Empty_set _, ((B ∨ (Excl A B)) → list_disj (x ++ remove_list x x0)))]). 2: apply MPRule_I.
intros. inversion H7 ; subst.
apply MP with (ps:=[(Empty_set _, (A → (B ∨ (Excl A B))) → ((B ∨ (Excl A B)) → list_disj (x ++ remove_list x x0)) → (A → list_disj (x ++ remove_list x x0)));
(Empty_set _, A → (B ∨ (Excl A B)))]). 2: apply MPRule_I.
intros. inversion H8 ; subst. apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (B ∨ (Excl A B)).
exists (list_disj (x ++ remove_list x x0)). auto. inversion H9 ; subst. 2: inversion H10. apply Ax.
apply AxRule_I. apply RA11_I. exists A. exists B ; auto. inversion H8. subst. 2: inversion H9.
apply MP with (ps:=[(Empty_set _, ((Excl A B) → list_disj (x ++ remove_list x x0)) → ((B ∨ (Excl A B)) → list_disj (x ++ remove_list x x0)));
(Empty_set _, (Excl A B) → list_disj (x ++ remove_list x x0))]). 2: apply MPRule_I.
intros. inversion H9. subst.
apply MP with (ps:=[(Empty_set _, (B → list_disj (x ++ remove_list x x0)) → ((Excl A B) → list_disj (x ++ remove_list x x0)) → ((B ∨ (Excl A B)) → list_disj (x ++ remove_list x x0)));
(Empty_set _, B → list_disj (x ++ remove_list x x0))]). 2: apply MPRule_I.
intros. inversion H10. subst. apply Ax. apply AxRule_I. apply RA4_I. exists B. exists (Excl A B).
exists (list_disj (x ++ remove_list x x0)). auto. inversion H11 ; subst. 2: inversion H12.
apply wBIH_Deduction_Theorem with (s:=(Union _ (Empty_set _) (Singleton _ B), list_disj (x ++ remove_list x x0))) ; auto.
assert (Union _ (Empty_set _) (Singleton _ B) = Singleton _ B).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H12. inversion H13. auto.
apply Union_intror ; auto. rewrite H12 ; auto. inversion H10. 2: inversion H11. subst.
apply wBIH_Deduction_Theorem with (s:=(Union _ (Empty_set _) (Singleton _ (Excl A B)), list_disj (x ++ remove_list x x0))) ; auto.
assert (Union _ (Empty_set _) (Singleton _ (Excl A B)) = Singleton _ (Excl A B)).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H11. inversion H12. auto.
apply Union_intror ; auto. rewrite H11 ; auto.
Qed.


