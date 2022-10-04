Require Import Classical.
(* Used in various places:
    - existence of a derivation in the axiomatic system for a sequent
      (should be decidable as Bi-Int is, but this would require extra work)
    - some set-theoretic arguments (maybe they can be constructivised *)

Require Import FunctionalExtensionality.

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_logics.
Require Import FO_BiInt_extens_interactions.
Require Import FOwBIH_meta_interactions.
Require Import FOsBIH_meta_interactions.
Require Import FO_BiInt_Kripke_sem.
Require Import FO_BiInt_Lindenbaum_lem.
Require Import FO_BiInt_strong_induction.
(* Require Import ListEnumerabilityFacts.
Require Import Set_FO_Bi_Int_enum. *)

Section wcompleteness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(* Hypothesis from Lindenbaum lemma *)

Variable encode0 : form -> nat.
Hypothesis encode0_inj : forall A B, (encode0 A = encode0 B) -> A = B.

(* Existential All Complete Underivable (EACU) pairs and their properties. *)

Definition ExAllCompNotDer (s: prod (@Ensemble form) (Ensemble form)) : Prop :=
  witness_Ex (fst s) /\ witness_All (snd s) /\ complete (fst s, snd s) /\ (wpair_der (fst s, snd s) -> False).

Lemma clos_deriv : forall (Γ Δ : @Ensemble form), ExAllCompNotDer (Γ, Δ) ->
                                (forall A, wpair_der (Γ, Singleton _ A) -> (In _ Γ A)).
Proof.
intros. destruct H. destruct H1. destruct H2. simpl in H2. simpl in H3. pose (H2 A). simpl in o. destruct o.
auto. exfalso. apply H3. destruct H0. destruct H0. destruct H5. exists [A]. repeat split ; auto.
apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H7. subst ; auto.
inversion H8. simpl.
destruct x.
- simpl in H6. apply MP with (ps:=[(Γ, ⊥ --> (A ∨ ⊥));(Γ, ⊥)]).
  2: apply MPRule_I. intros. inversion H7. subst. apply wEFQ. inversion H8.
  subst. 2: inversion H9. auto.
- destruct x. simpl in H6. assert (J1: List.In f (f :: nil)). apply in_eq.
  pose (H5 _ J1). simpl in i. inversion i. subst. auto.
  exfalso. assert (J1: List.In f (f :: f0 :: x)). apply in_eq. pose (H5 _ J1). simpl in i. inversion i. subst.
  assert (J2: List.In f0 (f :: f0 :: x)). apply in_cons ; apply in_eq.
  pose (H5 _ J2). inversion i0. subst. inversion H0. subst. apply H9. apply in_eq.
Qed.

Lemma primeness : forall (Γ Δ : @Ensemble form), ExAllCompNotDer (Γ, Δ) ->
                                (forall A B, (In _ Γ (A ∨ B))  -> ((In _ Γ A) \/ (In _ Γ B))).
Proof.
intros. destruct H. destruct H1. destruct H2. simpl in H2. simpl in H3. pose (H2 A). pose (H2 B).
destruct o ; destruct o0 ; auto. simpl in H4. simpl in H5. exfalso. apply H3.
destruct (eq_dec_form A B). subst. exists [B].
repeat split. apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H6.
subst. auto. inversion H7. simpl.
intros. auto. apply MP with (ps:=[(Γ, B --> (B ∨ ⊥));(Γ, B)]).
2: apply MPRule_I. intros. inversion H6. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists B. exists ⊥. auto. inversion H7. 2: inversion H8. subst.
apply MP with (ps:=[(Γ,(B ∨ B) --> B);(Γ,(B ∨ B))]). 2: apply MPRule_I.
intros. inversion H8. subst.
apply MP with (ps:=[(Γ,(B --> B) --> (B ∨ B) --> B);(Γ,(B --> B))]). 2: apply MPRule_I.
intros. inversion H9. subst.
apply MP with (ps:=[(Γ,(B --> B) --> (B --> B) --> (B ∨ B) --> B);(Γ,(B --> B))]). 2: apply MPRule_I.
intros. inversion H10. subst. apply Ax. apply AxRule_I. apply RA4_I.
exists B. exists B. exists B. auto. inversion H11. 2: inversion H12.
subst. apply wimp_Id_gen. inversion H10. 2: inversion H11. subst. apply wimp_Id_gen.
inversion H9. subst. 2: inversion H10. apply Id. apply IdRule_I. auto.
exists (A :: [B]). repeat split. apply NoDup_cons. intro. inversion H6. auto.
inversion H7. apply NoDup_cons ; auto ; apply NoDup_nil. intros.
simpl. inversion H6. subst. auto. inversion H7. intros.
simpl. inversion H6. subst. auto. inversion H7.
subst. auto. inversion H10. inversion H8. simpl.
apply MP with (ps:=[(Γ, (A ∨ B) --> (A ∨ (B ∨ ⊥)));(Γ, A ∨ B)]).
2: apply MPRule_I. intros. inversion H6. subst.
apply MP with (ps:=[(Γ,(B --> A ∨ (B ∨ ⊥)) --> (A ∨ B --> A ∨ (B ∨ ⊥)));
(Γ, (B --> A ∨ (B ∨ ⊥)))]). 2: apply MPRule_I. intros. inversion H7. subst.
apply MP with (ps:=[(Γ,(A --> A ∨ (B ∨ ⊥)) --> (B --> A ∨ (B ∨ ⊥)) --> (A ∨ B --> A ∨ (B ∨ ⊥)));
(Γ, (A --> A ∨ (B ∨ ⊥)))]). 2: apply MPRule_I. intros. inversion H8. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists B. exists (A ∨ (B ∨ ⊥)).
auto. inversion H9. subst. 2: inversion H10. apply Ax. apply AxRule_I.
apply RA2_I. exists A. exists (B ∨ ⊥). auto. inversion H8. 2: inversion H9.
subst.
apply MP with (ps:=[(Γ, ((B ∨ ⊥) --> A ∨ (B ∨ ⊥)) --> (B --> A ∨ (B ∨ ⊥)));
(Γ, ((B ∨ ⊥) --> A ∨ (B ∨ ⊥)))]). 2: apply MPRule_I. intros.
inversion H9. subst.
apply MP with (ps:=[(Γ, (B --> (B ∨ ⊥)) --> ((B ∨ ⊥) --> A ∨ (B ∨ ⊥)) --> (B --> A ∨ (B ∨ ⊥)));
(Γ, (B --> (B ∨ ⊥)))]). 2: apply MPRule_I. intros.
inversion H10. subst. apply Ax. apply AxRule_I. apply RA1_I. exists B.
exists (B ∨ ⊥). exists (A ∨ (B ∨ ⊥)). auto. inversion H11. subst.
2: inversion H12. apply Ax. apply AxRule_I. apply RA2_I. exists B. exists ⊥. auto.
inversion H10. 2: inversion H11. subst. apply Ax. apply AxRule_I. apply RA3_I.
exists A. exists (B ∨ ⊥). auto. inversion H7. subst. 2: inversion H8.
apply Id. apply IdRule_I. auto.
Qed.

Lemma cp_Bot_R : forall (Γ Δ : @Ensemble form), ExAllCompNotDer (Γ, Δ) -> (In _ Δ ⊥).
Proof.
intros. destruct H. destruct H0. destruct H1. simpl in H1. simpl in H2. pose (H1 ⊥). destruct o ; auto.
simpl in H3. exfalso. apply H2. exists []. repeat split. apply NoDup_nil.
intros. inversion H4. subst. auto. simpl. apply Id. apply IdRule_I. auto.
Qed.

Lemma cp_Henkin : forall (Γ Δ : @Ensemble form), ExAllCompNotDer (Γ, Δ) ->
                                (forall A,  (forall t, In _ Γ A[t..]) -> (In _ Γ (∀ A))).
Proof.
intros. destruct H. destruct H1. destruct H2. destruct (classic (In form Γ (∀ A))) ; auto.
pose (H2 (∀ A)). destruct o ; auto. simpl in H5. apply H1 in H5. simpl in H5. destruct H5.
exfalso. apply H3. exists [A[x..]]. repeat split ; auto. apply NoDup_cons. intro.
inversion H6. apply NoDup_nil. intros. inversion H6 ; subst. 2: inversion H7.
simpl ; auto. simpl.
apply MP with (ps:=[(Γ, A[x..] --> (A[x..] ∨ ⊥));(Γ, A[x..])]).
2: apply MPRule_I. intros. inversion H6. subst. apply Ax.
apply AxRule_I. apply RA2_I. exists A[x..]. exists ⊥ ; auto.
inversion H7. subst. 2: inversion H8. apply Id. apply IdRule_I. apply H0 ; auto.
Qed.

Lemma cp_dual_Henkin : forall (Γ Δ : @Ensemble form), ExAllCompNotDer (Γ, Δ) ->
                                (forall A,  (forall t, In _ Δ A[t..]) -> (In _ Δ (∃ A))).
Proof.
intros. destruct H. destruct H1. destruct H2. destruct (classic (In form Δ (∃ A))) ; auto.
pose (H2 (∃ A)). destruct o ; auto. simpl in H5. apply H in H5. simpl in H5. destruct H5.
exfalso. apply H3.
exists [A[x..]]. repeat split ; auto. apply NoDup_cons. intro.
inversion H6. apply NoDup_nil. intros. inversion H6 ; subst. 2: inversion H7.
simpl ; auto. simpl.
apply MP with (ps:=[(Γ, A[x..] --> (A[x..] ∨ ⊥));(Γ, A[x..])]).
2: apply MPRule_I. intros. inversion H6. subst. apply Ax.
apply AxRule_I. apply RA2_I. exists A[x..]. exists ⊥ ; auto.
inversion H7. subst. 2: inversion H8. apply Id. apply IdRule_I. auto.
Qed.






(* Canonical model construction *)


Definition Canon_worlds : Type :=
  {x : prod (@Ensemble form) (@Ensemble form) | ExAllCompNotDer x}.

Definition Canon_relation (P0 P1 : Canon_worlds) : Prop :=
  Included _ (fst (proj1_sig P0)) (fst (proj1_sig P1)).

Instance universal_interp : interp term :=
    {| i_func := func  |}.

Lemma universal_interp_eval rho (t : term) : eval rho t = t `[rho].
Proof.
induction t using term_ind. auto. simpl. f_equal.
Qed.

Lemma universal_interp_eval0 n (t : Vector.t term n): (Vector.map (eval var) t) = t.
Proof.
pose (Vector.map_id term n t). assert (eval var = (fun x : term => x)).
{ apply functional_extensionality. intros. pose (universal_interp_eval var x).
   Search var. rewrite subst_term_var in e0. auto. } rewrite H. auto.
Qed.

Program Instance Canon_model : kmodel term :=
      {|
        nodes := Canon_worlds ;
        reachable := Canon_relation ;
        k_interp := universal_interp ;
        k_P := fun C P v => In _ (fst (proj1_sig C)) (atom P v)
      |}.

Lemma truth_lemma : forall n A (cp : Canon_worlds),
  (size A = n) ->
  (ksat cp var A) <-> (In _ (fst (proj1_sig cp)) A).
Proof.
pose (strong_induction (fun x => forall (A : form) (cp : Canon_worlds), size A = x -> var ⊩( cp) A <-> In form (fst (proj1_sig cp)) A)
). apply i. clear i. intros n IH A cp eqsize. subst.
destruct A ; destruct cp ; simpl ; try simpl in H ; auto.
(* ⊥ *)
- split ; intro.
  * inversion H.
  * destruct x. simpl in H. unfold ExAllCompNotDer in e. simpl in e. destruct e. destruct H1.
    destruct H2. apply H3. unfold wpair_der. simpl. exists []. repeat split. apply NoDup_nil.
    intros. inversion H4. subst. simpl. apply Id. apply IdRule_I. simpl. auto.
(* ⊤ *)
- split ; intro ; auto. pose (classic (In form (fst x) ⊤)). destruct o. auto.
  exfalso. destruct x. simpl in H0. unfold ExAllCompNotDer in e. simpl in e.
  clear H. destruct e. destruct H1. destruct H2. apply H3. unfold wpair_der.
  exists [⊤]. repeat split. apply NoDup_cons. auto. apply NoDup_nil.
  intros. inversion H4. subst. simpl. unfold complete in H2. simpl in H2.
  pose (H2 ⊤). destruct o ; auto. exfalso ; auto. inversion H5.
  simpl. apply MP with (ps:=[(e0, ⊤ --> (⊤ ∨ ⊥)); (e0, ⊤)]).
  intros. inversion H4. subst. apply Ax. apply AxRule_I. apply RA2_I.
  exists ⊤. exists ⊥. auto. inversion H5. subst.
  apply MP with (ps:=[(e0, (⊤ --> ⊤) --> ⊤); (e0, ⊤ --> ⊤)]).
  intros. inversion H6. subst. apply Ax. apply AxRule_I. apply RA15_I.
  exists (⊤ --> ⊤). auto. inversion H7. subst. apply wimp_Id_gen. inversion H8.
  apply MPRule_I. inversion H6. apply MPRule_I.
(* atom *)
- split ; intro.
  * destruct x. simpl. simpl in H. rewrite universal_interp_eval0 in H. auto.
  * rewrite universal_interp_eval0. auto.
(* Binary connectives *)
- destruct x. simpl. destruct b.
(* A1 ∧ A2 *)
  * split ; intro.
    + destruct H. pose (IH (size A1)). apply i in H ; simpl ; try lia ; auto.
        simpl in H. pose (IH (size A2)). apply i0 in H0 ; simpl ; try lia ; auto. simpl in H0. clear i. clear i0.
        apply clos_deriv with (Δ:=e1) ; auto. destruct (eq_dec_form A1 A2).
        { subst. exists [A2 ∧ A2]. repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
          intros. inversion H1. simpl. subst. apply In_singleton. inversion H2. simpl.
          apply MP with (ps:=[(e0, (A2 ∧ A2) --> (A2 ∧ A2) ∨ ⊥);(e0, (A2 ∧ A2))]).
          2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (A2 ∧ A2).
          exists ⊥. auto. inversion H2. subst.
          apply MP with (ps:=[(e0, (A2 --> (A2 ∧ A2)));(e0, A2)]).
          2: apply MPRule_I. intros. inversion H3. subst.
          apply MP with (ps:=[(e0, (A2 --> A2) --> (A2 --> (A2 ∧ A2)));(e0, (A2 --> A2))]).
          2: apply MPRule_I. intros. inversion H4. subst.
          apply MP with (ps:=[(e0, (A2 --> A2) --> (A2 --> A2) --> (A2 --> (A2 ∧ A2)));(e0, (A2 --> A2))]).
          2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
          apply RA7_I. exists A2. exists A2. exists A2. auto. inversion H6. subst. apply wimp_Id_gen.
          inversion H7. inversion H5. subst. apply wimp_Id_gen. inversion H6. inversion H4. subst.
          apply Id. apply IdRule_I. auto. inversion H5. inversion H3. }
       { exists [A1 ∧ A2]. repeat split.
          apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H1. subst. apply In_singleton.
          inversion H2. simpl.
          apply MP with (ps:=[(e0, (A1 ∧ A2) --> (A1 ∧ A2 ∨ ⊥));(e0, A1 ∧ A2)]).
          2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (A1 ∧ A2).
          exists ⊥. auto. inversion H2. subst. 2: inversion H3.
          apply MP with (ps:=[(e0, A1 --> (A1 ∧ A2));(e0, A1)]).
          2: apply MPRule_I. intros. inversion H3. subst.
          apply MP with (ps:=[(e0, (A1 --> A2) --> (A1 --> (A1 ∧ A2)));(e0, (A1 --> A2))]).
          2: apply MPRule_I. intros. inversion H4. subst.
          apply MP with (ps:=[(e0, (A1 --> A1) --> (A1 --> A2) --> (A1 --> (A1 ∧ A2)));(e0, (A1 --> A1))]).
          2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
          apply RA7_I. exists A1. exists A1. exists A2. auto. inversion H6.
          subst. 2: inversion H7. apply wimp_Id_gen. inversion H5. subst. 2: inversion H6.
          apply MP with (ps:=[(e0, A2 --> (A1 --> A2));(e0, A2)]).
          2: apply MPRule_I. intros. inversion H6. subst. apply wThm_irrel.
          inversion H7. subst. 2: inversion H8. apply Id. apply IdRule_I. auto.
          inversion H4. subst. apply Id. apply IdRule_I. auto. inversion H5. }
    + split. pose (IH (size A1)). apply i ; simpl ; try lia ; auto. clear i. apply clos_deriv with (Δ:=e1) ; auto.
        exists [A1]. repeat split.
        apply NoDup_cons ; auto ; apply NoDup_nil. intros. simpl. inversion H0. subst. apply In_singleton. inversion H1.
        simpl.
        apply MP with (ps:=[(e0, A1 --> (A1 ∨ ⊥));(e0, A1)]).
        2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA2_I.
        exists A1. exists ⊥. auto. inversion H1. subst.
        apply MP with (ps:=[(e0, (A1 ∧ A2) --> A1);(e0, (A1 ∧ A2))]).
        2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
        apply RA5_I. exists A1. exists A2. auto. inversion H3. 2: inversion H4.
        subst. apply Id. apply IdRule_I. auto. inversion H2.
       pose (IH (size A2)). apply i ; simpl ; try lia ; auto. clear i. apply clos_deriv with (Δ:=e1) ; auto.
        exists [A2]. repeat split.
        apply NoDup_cons ; auto ; apply NoDup_nil. intros. simpl. inversion H0. subst. apply In_singleton. inversion H1.
        simpl.
        apply MP with (ps:=[(e0, A2 --> (A2 ∨ ⊥));(e0, A2)]).
        2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA2_I.
        exists A2. exists ⊥. auto. inversion H1. subst.
        apply MP with (ps:=[(e0, (A1 ∧ A2) --> A2);(e0, (A1 ∧ A2))]).
        2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
        apply RA6_I. exists A1. exists A2. auto. inversion H3. 2: inversion H4.
        subst. apply Id. apply IdRule_I. auto. inversion H2.
(* A1 ∨ A2 *)
  * split ; intro.
    + destruct H. pose (IH (size A1)). apply i in H ; simpl ; try lia ; auto. clear i. apply clos_deriv with (Δ:=e1) ; auto.
        simpl in H. exists [A1 ∨ A2]. repeat split.
        apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H0. subst. apply In_singleton. inversion H1.
        simpl.
        apply MP with (ps:=[(e0, (A1 ∨ A2) --> (A1 ∨ A2) ∨ ⊥);(e0, (A1 ∨ A2))]).
        2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (A1 ∨ A2).
        exists ⊥. auto. inversion H1. subst.
        apply MP with (ps:=[(e0, A1 --> (A1 ∨ A2));(e0, A1)]).
        2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
        apply RA2_I. exists A1. exists A2. auto. inversion H3. 2: inversion H4.
        subst. apply Id. apply IdRule_I. auto. inversion H2.
        pose (IH (size A2)). apply i in H ; simpl ; try lia ; auto. clear i. apply clos_deriv with (Δ:=e1) ; auto. simpl in H.
        exists [A1 ∨ A2]. repeat split.
        apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H0. subst. apply In_singleton. inversion H1.
        simpl.
        apply MP with (ps:=[(e0, (A1 ∨ A2) --> (A1 ∨ A2) ∨ ⊥);(e0, (A1 ∨ A2))]).
        2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (A1 ∨ A2).
        exists ⊥. auto. inversion H1. subst.
        apply MP with (ps:=[(e0, A2 --> (A1 ∨ A2));(e0, A2)]).
        2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
        apply RA3_I. exists A1. exists A2. auto. inversion H3. 2: inversion H4.
        subst. apply Id. apply IdRule_I. auto. inversion H2.
    + apply primeness with (Δ:=e1) in H ; auto. destruct H. left.
       pose (IH (size A1)). apply i ; simpl ; try lia ; auto.
       right. pose (IH (size A2)). apply i ; simpl ; try lia ; auto.
(* A1 --> A2 *)
  * split ; intro.
      +  destruct (classic (In form e0 (A1 --> A2))).
          auto. exfalso. unfold ExAllCompNotDer in e. simpl in e. destruct e. destruct a. destruct a.
          assert (wpair_der (Union _ e0 (Singleton _ A1), Singleton _ A2) -> False).
          intro. apply H0. apply gen_FOwBIH_Deduction_Theorem in H1.
          { apply clos_deriv with (Δ:=e1). unfold ExAllCompNotDer ; auto. auto. }
          (* This is the first place where the proof does not go through, as explained in Subsection 9.10.3 of the dissertation. *)
          admit.
        + intros. destruct v. simpl. destruct x. simpl. pose (IH (size A1)). apply i in H1 ; simpl ; try lia ; auto. clear i.
          simpl in H1. unfold Canon_relation in H0. simpl in H0.
          apply H0 in H. unfold ExAllCompNotDer in e2. simpl in e2. destruct e2. destruct a. destruct a.
          pose (IH (size A2)). apply i ; simpl ; try lia ; auto. clear i.
          assert (wpair_der (e3, Singleton _ A2)). exists [A2]. repeat split.
          apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H2. subst. simpl. apply In_singleton. inversion H3.
          simpl.
          apply MP with (ps:=[(e3, A2 --> (A2 ∨ ⊥));(e3, A2)]). 2: apply MPRule_I.
          intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A2. exists ⊥.
          auto. inversion H3. subst. 2: inversion H4.
          apply MP with (ps:=[(e3, A1 --> A2);(e3, A1)]). 2: apply MPRule_I.
          intros. inversion H4. subst. apply Id. apply IdRule_I. auto.
          inversion H5. 2: inversion H6. subst. apply Id. apply IdRule_I. auto.
          apply clos_deriv with (Δ:=e4). unfold ExAllCompNotDer ; auto. auto.
(* A1 --< A2 *)
  * split ; intro.
   + destruct H. destruct H. destruct (classic (In form e0 (A1 --< A2))). auto.
      exfalso. destruct H0. assert (wpair_der (e0, Singleton _ (A1 --< A2)) -> False). intro. apply H1.
      apply clos_deriv with (Δ:=e1) ; auto.
      simpl in H0. assert (In form (fst (proj1_sig x)) (A2 ∨ (A1 --< A2))).
      apply clos_deriv with (Δ:=(snd (proj1_sig x))). unfold ExAllCompNotDer ; auto. simpl.
      destruct x. simpl. auto. exists [A2 ∨ (A1 --< A2)]. repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
      intros. simpl. inversion H4. subst. apply In_singleton. inversion H5. simpl.
      apply MP with (ps:=[(fst (proj1_sig x), (A2 ∨ (A1 --< A2)) --> (A2 ∨ (A1 --< A2)) ∨ ⊥);(fst (proj1_sig x), (A2 ∨ (A1 --< A2)))]). 2: apply MPRule_I.
      intros. inversion H4. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (A2 ∨ (A1 --< A2)). exists ⊥. auto.
      inversion H5. 2: inversion H6. subst.
      apply MP with (ps:=[(fst (proj1_sig x), A1 --> (A2 ∨ (A1 --< A2)));(fst (proj1_sig x), A1)]). 2: apply MPRule_I.
      intros. inversion H6. subst. apply Ax. apply AxRule_I. apply RA11_I. exists A1.
      exists A2. auto. inversion H7. 2: inversion H8. subst. apply Id. apply IdRule_I.
      apply IH with (k:=size A1) ; auto. simpl. lia.
      apply primeness with (Δ:=snd (proj1_sig x)) in H4. destruct H4 ; auto.
      apply H2. pose (IH (size A2)). apply i ; simpl ; try lia ; auto. destruct x. simpl in H4.  simpl. auto.
    + assert (wpair_der ((Singleton _ A1), Union _ e1 (Singleton _ A2)) -> False).
      intro. destruct H0. destruct H0. destruct H1. simpl in H2. simpl in H1. unfold ExAllCompNotDer in e. simpl in e.
      destruct e. destruct H4. destruct H5. pose (remove_disj x A2 (Singleton _ A1)).
      assert (FOwBIH_rules (Singleton _ A1, A2 ∨ (list_disj (remove eq_dec_form A2 x)))).
      apply MP with (ps:=[(Singleton _ A1, list_disj x --> A2 ∨
       (list_disj (remove eq_dec_form A2 x)));(Singleton _ A1, list_disj x)]).
      2: apply MPRule_I. intros. inversion H7. subst. auto. inversion H8. subst.
      auto. inversion H9. clear f. clear H2.
      assert (Singleton _ A1 = Union _ (Empty_set _) (Singleton _ A1)).
      apply Extensionality_Ensembles. split. intro. intros. inversion H2. subst.
      apply Union_intror. apply In_singleton. intro. intros. inversion H2.
      subst. inversion H8. inversion H8. subst. apply In_singleton. rewrite H2 in H7.
      assert (J1: Union _ (Empty_set _) (Singleton _ A1) =
      Union _ (Empty_set _) (Singleton _ A1)). auto.
      assert (J2: A2 ∨ (list_disj (remove eq_dec_form A2 x)) = A2 ∨ (list_disj (remove eq_dec_form A2 x))). auto.
      pose (FOwBIH_Deduction_Theorem (Union _ (Empty_set _) (Singleton _ A1),
      A2 ∨ (list_disj (remove eq_dec_form A2 x))) H7 A1 (A2 ∨ (list_disj (remove eq_dec_form A2 x)))
      (Empty_set _) J1 J2). apply wdual_residuation in f. clear J2. clear J1. clear H2. clear H5.
      apply H6. exists (remove eq_dec_form A2 x). repeat split. apply NoDup_remove.
      auto. intros. simpl. pose (H1 A). assert (List.In A x). apply In_remove with (B:= A2).
      auto. apply i in H5. inversion H5. subst. auto. subst. inversion H8.
      subst. exfalso. apply remove_In in H2. auto. simpl.
      apply MP with (ps:=[(e0, (A1 --< A2) --> list_disj (remove eq_dec_form A2 x));(e0, A1 --< A2)]).
      2: apply MPRule_I. intros. inversion H2. subst.
      pose (FOwBIH_monot (Empty_set _, (A1 --< A2) --> list_disj (remove eq_dec_form A2 x))
      f e0). apply f0. clear f0. simpl. intro. intros. inversion H5. inversion H5.
      subst. 2: inversion H8. clear H2. clear H5. apply Id. apply IdRule_I. auto.
       (* This is the second place where the proof does not go through, as explained in Subsection 9.10.3 of the dissertation. *)
       admit.
(* Quantifiers *)
- destruct q.
  (* Universal *)
  * split ; intros.
    + destruct x. simpl. pose (cp_Henkin _ _ e A). apply i. intros. pose (H t). unfold ExAllCompNotDer in e. simpl in e.
       destruct e. destruct a. destruct a.
       assert (J1: size A[t..] < size (∀ A)). simpl. rewrite subst_size. lia.
       assert (J2: size A[t..] = size A[t..]). auto.
       pose (IH _ J1 A[t..] (exist (fun x : Ensemble form * Ensemble form => ExAllCompNotDer x) (e0, e1)  (conj w (conj w0 (conj c f)))) J2).
       simpl in i0. apply i0. clear i0. clear J1. clear J2. apply ksat_comp. apply ksat_ext with (rho:= t..) ; auto.
       intros. unfold funcomp. unfold scons. destruct x. pose (subst_term_var t). auto. simpl. auto.
    + destruct x. pose (@exist (prod (Ensemble form) (Ensemble form)) ExAllCompNotDer (e0,e1) e).
       assert (In form (fst (proj1_sig s)) A[j..]).
       { pose (clos_deriv _ _ e A[j..]). simpl. simpl in H. apply i. exists [A[j..]].
          repeat split ; simpl. apply NoDup_cons ; auto ; apply NoDup_nil.
          intros. destruct H0 ; auto. subst ; auto. apply In_singleton. inversion H0.
          apply MP with (ps:=[(e0, A[j..] --> A[j..] ∨ ⊥);(e0, A[j..])]). 2: apply MPRule_I.
          intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A[j..].
          exists ⊥. auto. inversion H1. subst. 2: inversion H2.
          apply MP with (ps:=[(e0, (∀ A) --> A[j..]);(e0, ∀ A)]). 2: apply MPRule_I.
          intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA18_I. exists A. exists j. auto.
          inversion H3. 2: inversion H4. subst. apply Id. apply IdRule_I. auto. }
       assert (J1: size A[j..] < size (∀ A) ). simpl. rewrite subst_size. lia.
       assert (J2: size A[j..] = size A[j..]). auto.
       pose (IH _ J1 A[j..] (exist (fun x : Ensemble form * Ensemble form => ExAllCompNotDer x) (e0, e1) e) J2).
       simpl in i. apply i in H0. apply ksat_comp in H0. apply ksat_ext with (rho:= j..) in H0 ; auto.
       intros. destruct x ; auto. simpl. unfold funcomp. simpl. pose (subst_term_var j). auto.
  (* Existential *)
  * split ; intros.
    + destruct x. simpl. destruct H.
       assert (J1: size A[x..] < size (∃ A)). simpl. rewrite subst_size. lia.
       assert (J2: size A[x..] = size A[x..]). auto.
       pose (IH _ J1 A[x..] (exist (fun x : Ensemble form * Ensemble form => ExAllCompNotDer x) (e0, e1) e) J2).
       simpl in i. apply ksat_ext with (rho:= (x.. >> eval var)) in H ; auto.
       apply ksat_comp in H. apply i in H. pose (clos_deriv _ _ e (∃ A)). apply i0.
       exists [∃ A]. repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
       intros. inversion H0 ; auto. subst ; auto. simpl. apply In_singleton. inversion H1. simpl.
       apply MP with (ps:=[(e0, (∃ A) --> (∃ A) ∨ ⊥);(e0, ∃ A)]). 2: apply MPRule_I.
       intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (∃ A).
       exists ⊥. auto. inversion H1. subst. 2: inversion H2.
       apply MP with (ps:=[(e0, A[x..] --> (∃ A));(e0, A[x..])]). 2: apply MPRule_I.
       intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA19_I. exists A.
       exists x. auto. inversion H3. subst. 2: inversion H4. apply Id. apply IdRule_I. auto.
       intros. destruct x0 ; auto. unfold funcomp. simpl. pose (subst_term_var x). auto.
    + destruct x. simpl in H. apply NNPP. intro.
       assert (forall j : term, ~ (j.. ⊩( exist (fun x : Ensemble form * Ensemble form => ExAllCompNotDer x) (e0, e1) e) A)).
       intros. intro. apply H0. exists j ; auto.
       assert (J0: forall t : term, In form e1 A[t..]). intros.
       assert (J1: size A[t..] < size (∃ A)). simpl. rewrite subst_size. lia.
       assert (J2: size A[t..] = size A[t..]). auto.
       pose (IH _ J1 A[t..] (exist (fun x : Ensemble form * Ensemble form => ExAllCompNotDer x) (e0, e1) e) J2).
       simpl in i. unfold ExAllCompNotDer in e. simpl in e. destruct e. destruct a. destruct a.
       unfold complete in c. simpl in c. pose (c A[t..]). destruct o ; auto.
       apply i in H2. apply ksat_comp in H2. apply ksat_ext with (rho:= t..) in H2 ; auto. exfalso. apply (H1 t) ; auto.
       intros. destruct x ; auto. unfold funcomp. simpl. pose (subst_term_var t). auto.
       pose (cp_dual_Henkin _ _ e A J0). unfold ExAllCompNotDer in e. simpl in e. destruct e. destruct a. destruct a. simpl.
       apply f. exists [∃ A]. repeat split ; auto. apply NoDup_cons ; auto ; apply NoDup_nil.
       intros. inversion H2 ; auto. subst ; auto. inversion H3. simpl.
       apply MP with (ps:=[(e0, (∃ A) --> (∃ A) ∨ ⊥);(e0, ∃ A)]). 2: apply MPRule_I.
       intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (∃ A).
       exists ⊥. auto. inversion H3. subst. 2: inversion H4. apply Id. apply IdRule_I. auto.
Admitted.

Theorem closedwCounterCompleteness : forall (Γ Δ : @Ensemble form),
    (closed_S Γ) ->
    (closed_S Δ) ->
    (wpair_der (Γ, Δ) -> False) ->
    ((loc_conseq Γ Δ) -> False).
Proof.
intros Γ Δ ClΓ ClΔ WD.
apply Lindenbaum_lemma with (encode1:= encode0) in WD ; auto. destruct WD. destruct x. simpl in H. destruct H. destruct H0.
destruct H1. destruct H2. destruct H3. intro. unfold loc_conseq in H5.
assert (J1: ExAllCompNotDer (e,e0)). unfold ExAllCompNotDer ; auto.
pose (@exist (prod (Ensemble form) (Ensemble form)) ExAllCompNotDer (e,e0) J1).
pose (H5 _ Canon_model s var).
assert (forall A : form, In form Γ A -> var ⊩( s) A). intros. assert (J5: size A = size A). auto.
pose (truth_lemma (size A) A s J5). apply i. auto.
apply e1 in H6. destruct H6. destruct H6. assert (J5: size x = size x). auto.
pose (truth_lemma (size x) x s J5). apply i in H7. simpl in H7.
apply H4. exists [x]. repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
intros. inversion H8. simpl. subst ; auto. inversion H9. simpl.
apply MP with (ps:=[(e, x --> (x ∨ ⊥));(e, x)]). 2: apply MPRule_I.
intros. inversion H8. subst. apply Ax. apply AxRule_I. apply RA2_I. exists x. exists ⊥.
auto. inversion H9. subst. 2: inversion H10. apply Id. apply IdRule_I. auto.
Qed.

Theorem closedwCompleteness : forall (Γ Δ : @Ensemble form),
    (closed_S Γ) ->
    (closed_S Δ) ->
    (loc_conseq Γ Δ) ->
    (wpair_der (Γ, Δ)).
Proof.
intros Γ Δ ClΓ ClΔ LC. pose (closedwCounterCompleteness Γ Δ).
pose (classic (wpair_der (Γ, Δ))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.

Theorem wCounterCompleteness : forall (Γ Δ : @Ensemble form),
    (wpair_der (Γ, Δ) -> False) ->
    ((loc_conseq Γ Δ) -> False).
Proof.
(* We do not have this result. *)
Admitted.

Theorem wCompleteness : forall (Γ Δ : @Ensemble form),
    (loc_conseq Γ Δ) ->
    (wpair_der (Γ, Δ)).
Proof.
intros Γ Δ LC. pose (wCounterCompleteness Γ Δ).
pose (classic (wpair_der (Γ, Δ))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.

End wcompleteness.
