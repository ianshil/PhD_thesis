Require Import Classical.
(* Used in various places:
    - existence of a derivation in the axiomatic system for a sequent
      (should be decidable as Bi-Int is, but this would require extra work)
    - some set-theoretic arguments (maybe they can be constructivised *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import BiInt_extens_interactions.
Require Import wBIH_meta_interactions.
Require Import sBIH_meta_interactions.
Require Import BiInt_Kripke_sem.
Require Import BiInt_Lindenbaum_lem.

Definition CompNotDer (s: prod (@Ensemble (BPropF V)) (@Ensemble (BPropF V))) : Prop :=
  (complete (fst s, snd s) /\ (wpair_derrec (fst s, snd s) -> False)).

Lemma clos_deriv : forall (Γ Δ : @Ensemble (BPropF V)), CompNotDer (Γ, Δ) ->
                                (forall A, wBIH_rules (Γ, A) -> (In _ Γ A)).
Proof.
intros. destruct H. simpl in H. simpl in H1. pose (H A). destruct o.
auto. simpl in H2. exfalso. apply H1. exists [A]. repeat split.
apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H3. subst.
auto. inversion H4. simpl. apply MP with (ps:=[(Γ, Imp A (Or A (Bot V)));(Γ, A)]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists A. exists (Bot V). auto. inversion H4. subst. 2: inversion H5.
assumption.
Qed.

Lemma primeness : forall (Γ Δ : @Ensemble (BPropF V)), CompNotDer (Γ, Δ) ->
                                (forall A B, (In _ Γ (Or A B))  -> ((In _ Γ A) \/ (In _ Γ B))).
Proof.
intros. destruct H. simpl in H. simpl in H1. pose (H A). pose (H B).
destruct o ; destruct o0 ; auto. simpl in H2. simpl in H3. exfalso. apply H1.
destruct (eq_dec_form A B). subst. exists [B].
repeat split. apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H4.
subst. auto. inversion H5. simpl. apply MP with (ps:=[(Γ, Imp B (Or B (Bot V)));(Γ, B)]).
2: apply MPRule_I. intros. inversion H4. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists B. exists (Bot V). auto. inversion H5. 2: inversion H6. subst.
apply MP with (ps:=[(Γ,(Or B B) → B);(Γ,(Or B B))]). 2: apply MPRule_I.
intros. inversion H6. subst.
apply MP with (ps:=[(Γ,(B → B) → (Or B B) → B);(Γ,(B → B))]). 2: apply MPRule_I.
intros. inversion H7. subst.
apply MP with (ps:=[(Γ,(B → B) → (B → B) → (Or B B) → B);(Γ,(B → B))]). 2: apply MPRule_I.
intros. inversion H8. subst. apply Ax. apply AxRule_I. apply RA4_I.
exists B. exists B. exists B. auto. inversion H9. 2: inversion H10.
subst. apply wimp_Id_gen. inversion H8. 2: inversion H9. subst. apply wimp_Id_gen.
inversion H7. subst. 2: inversion H8. apply Id. apply IdRule_I. auto.
exists (A :: [B]). repeat split. apply NoDup_cons. intro. inversion H4. auto.
inversion H5. apply NoDup_cons ; auto ; apply NoDup_nil. intros.
simpl. inversion H4. subst. auto. inversion H5. subst. auto. inversion H6.
simpl. apply MP with (ps:=[(Γ, Imp (Or A B) (Or A (Or B (Bot V))));(Γ, Or A B)]).
2: apply MPRule_I. intros. inversion H4. subst.
apply MP with (ps:=[(Γ,(B → Or A (Or B (Bot V))) → (Or A B → Or A (Or B (Bot V))));
(Γ, (B → Or A (Or B (Bot V))))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ,(A → Or A (Or B (Bot V))) → (B → Or A (Or B (Bot V))) → (Or A B → Or A (Or B (Bot V))));
(Γ, (A → Or A (Or B (Bot V))))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists B. exists (Or A (Or B (Bot V))).
auto. inversion H7. subst. 2: inversion H8. apply Ax. apply AxRule_I.
apply RA2_I. exists A. exists (Or B (Bot V)). auto. inversion H6. 2: inversion H7.
subst.
apply MP with (ps:=[(Γ, ((Or B (Bot V)) → Or A (Or B (Bot V))) → (B → Or A (Or B (Bot V))));
(Γ, ((Or B (Bot V)) → Or A (Or B (Bot V))))]). 2: apply MPRule_I. intros.
inversion H7. subst.
apply MP with (ps:=[(Γ, (B → (Or B (Bot V))) → ((Or B (Bot V)) → Or A (Or B (Bot V))) → (B → Or A (Or B (Bot V))));
(Γ, (B → (Or B (Bot V))))]). 2: apply MPRule_I. intros.
inversion H8. subst. apply Ax. apply AxRule_I. apply RA1_I. exists B.
exists (Or B (Bot V)). exists (Or A (Or B (Bot V))). auto. inversion H9. subst.
2: inversion H10. apply Ax. apply AxRule_I. apply RA2_I. exists B. exists (Bot V). auto.
inversion H8. 2: inversion H9. subst. apply Ax. apply AxRule_I. apply RA3_I.
exists A. exists (Or B (Bot V)). auto. inversion H5. subst. 2: inversion H6.
apply Id. apply IdRule_I. auto.
Qed.

Lemma cp_Bot_R : forall (Γ Δ : @Ensemble (BPropF V)), CompNotDer (Γ, Δ) -> (In _ Δ (Bot V)).
Proof.
intros. destruct H. simpl in H. simpl in H0. pose (H (Bot V)). destruct o ; auto.
simpl in H1. exfalso. apply H0. exists []. repeat split. apply NoDup_nil.
intros. inversion H2. simpl. apply Id. apply IdRule_I. auto.
Qed.

Definition Canon_worlds : Type :=
  {x : prod (@Ensemble (BPropF V)) (@Ensemble (BPropF V)) | CompNotDer x}.

Definition Canon_rel (P0 P1 : Canon_worlds) : Prop :=
  Included _ (fst (proj1_sig P0)) (fst (proj1_sig P1)).

Definition Canon_val (P : Canon_worlds) (q : V) : Prop :=
  In _ (fst (proj1_sig P)) (# q).

Lemma C_R_refl u : Canon_rel u u.
Proof.
unfold Canon_rel. intro. auto.
Qed.

Lemma C_R_trans u v w: Canon_rel u v -> Canon_rel v w -> Canon_rel u w.
Proof.
intros. unfold Canon_rel.
intro. intros. unfold Canon_rel in H0. unfold Canon_rel in H.
apply H0. apply H. auto.
Qed.

Lemma C_val_persist : forall u v, Canon_rel u v -> forall p, Canon_val u p -> Canon_val v p.
Proof.
intros.
unfold Canon_val in H0. unfold Canon_rel in H.
unfold Canon_val. apply H. auto.
Qed.

Instance CM : model :=
      {|
        nodes := Canon_worlds ;
        reachable := Canon_rel ;
        val := Canon_val ;

        reach_refl := C_R_refl ;
        reach_tran := C_R_trans ;

        persist := C_val_persist;
      |}.

Lemma truth_lemma : forall A (cp : Canon_worlds),
  (wforces CM cp A) <-> (In _ (fst (proj1_sig cp)) A).
Proof.
induction A ; intro ; split ; intros ; destruct cp ; simpl ; try simpl in H ; auto.
(* Bot V *)
- inversion H.
- destruct x. simpl in H. unfold CompNotDer in c. destruct c. simpl in H1. apply H1.
  unfold wpair_derrec. simpl. exists []. repeat split. apply NoDup_nil. intros.
  inversion H2. simpl. apply Id. apply IdRule_I. auto.
(* Top V *)
- pose (classic (In (BPropF V) (fst x) (Top V))). destruct o. auto.
  exfalso. destruct x. simpl in H0. simpl in c. unfold CompNotDer in c.
  clear H. destruct c. simpl in H. simpl in H1. apply H1. unfold wpair_derrec.
  exists [Top V]. repeat split. apply NoDup_cons. auto. apply NoDup_nil.
  intros. inversion H2. subst. simpl. unfold complete in H. simpl in H. clear H2.
  pose (H (Top V)). destruct o. exfalso. apply H0. auto. auto. inversion H3.
  simpl. apply MP with (ps:=[(e, Imp (Top V) (Or (Top V) (Bot V))); (e, (Top V))]).
  intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I.
  exists (Top V). exists (Bot V). auto. inversion H3. subst.
  apply MP with (ps:=[(e, Imp (Imp (Top V) (Top V)) (Top V)); (e, Imp (Top V) (Top V))]).
  intros. inversion H4. subst. apply Ax. apply AxRule_I. apply RA15_I.
  exists (Top V → Top V). auto. inversion H5. subst. apply wimp_Id_gen. inversion H6.
  apply MPRule_I. inversion H4. apply MPRule_I.
(* And A1 A2 *)
- destruct H. apply IHA1 in H. simpl in H. apply IHA2 in H0. simpl in H0.
  apply clos_deriv with (Δ:=snd x). auto.
  apply MP with (ps:=[(fst x, A1 → (And A1 A2));(fst x, A1)]).
  2: apply MPRule_I. intros. inversion H1. subst.
  apply MP with (ps:=[(fst x, (A1 → A2) → (A1 → (And A1 A2)));(fst x, (A1 → A2))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(fst x, (A1 → A1) → (A1 → A2) → (A1 → (And A1 A2)));(fst x, (A1 → A1))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply RA7_I. exists A1. exists A1. exists A2. auto. inversion H4.
  subst. 2: inversion H5. apply wimp_Id_gen. inversion H3. subst. 2: inversion H4.
  apply MP with (ps:=[(fst x, A2 → (A1 → A2));(fst x, A2)]).
  2: apply MPRule_I. intros. inversion H4. subst. apply wThm_irrel.
  inversion H5. subst. 2: inversion H6. apply Id. apply IdRule_I. assumption.
  inversion H2. subst. apply Id. apply IdRule_I. assumption. inversion H3.
- split. apply IHA1. simpl. apply clos_deriv with (Δ:=snd x) ; auto.
  apply MP with (ps:=[(fst x, Imp (And A1 A2) A1);(fst x, (And A1 A2))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA5_I. exists A1. exists A2. auto. inversion H1. 2: inversion H2.
  subst. apply Id. apply IdRule_I ; auto.
  apply IHA2. simpl. apply clos_deriv with (Δ:=snd x) ; auto.
  apply MP with (ps:=[(fst x, Imp (And A1 A2) A2);(fst x, (And A1 A2))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA6_I. exists A1. exists A2. auto. inversion H1. 2: inversion H2.
  subst. apply Id. apply IdRule_I ; auto.
(* Or A1 A2 *)
- destruct H.
  apply IHA1 in H. simpl in H. apply clos_deriv with (Δ:=snd x) ; auto.
  apply MP with (ps:=[(fst x, Imp A1 (Or A1 A2));(fst x, A1)]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA2_I. exists A1. exists A2. auto. inversion H1. 2: inversion H2.
  subst. apply Id. apply IdRule_I ; auto.
  apply IHA2 in H. simpl in H. apply clos_deriv with (Δ:=snd x) ; auto.
  apply MP with (ps:=[(fst x, Imp A2 (Or A1 A2));(fst x, A2)]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA3_I. exists A1. exists A2. auto. inversion H1. 2: inversion H2.
  subst. apply Id. apply IdRule_I ; auto.
- apply primeness with (Δ:=snd x) in H ; auto. destruct H. left. apply IHA1 ; auto.
  right. apply IHA2 ; auto.
(* Imp A1 A2 *)
- destruct x. simpl. destruct (classic (In (BPropF V) e (A1 → A2))).
  auto. exfalso. unfold CompNotDer in c. simpl in c. destruct c.
  assert (wpair_derrec (Union _ e (Singleton _ A1), Singleton _ A2) -> False).
  intro. apply gen_wBIH_Deduction_Theorem in H1. apply H0.
  { apply clos_deriv with (Δ:=e0). unfold CompNotDer ; auto. destruct H1.
    destruct H1. destruct H2. destruct x. simpl in H3. simpl in H2.
    apply MP with (ps:=[(e, Imp (Bot V) (A1 → A2));(e, Bot V)]). 2: apply MPRule_I.
    intros. inversion H4. subst. apply wEFQ. inversion H5. 2: inversion H6. subst.
    assumption. inversion H1. subst. pose (H2 b). assert (List.In b (b :: x)). apply in_eq.
    apply s in H4. inversion H4. subst. destruct x. simpl in H3.
    apply absorp_Or1 in H3. auto. pose (H2 b). assert (List.In b (A1 → A2 :: b :: x)).
    apply in_cons. apply in_eq. apply s0 in H5. inversion H5. subst. inversion H1.
    subst. exfalso. apply H10. apply in_eq. }
  apply Lindenbaum_lemma in H1. destruct H1. destruct H1.
  destruct H1. destruct H2. destruct H3.
  assert (J1: complete (fst (x, x0), snd (x, x0)) /\ (wpair_derrec (fst (x, x0), snd (x, x0)) -> False)). auto.
  pose (@exist (prod (Ensemble (BPropF V)) (Ensemble (BPropF V))) CompNotDer (x,x0) J1).
  pose (H s).
  assert (J2: Canon_rel (exist (fun x : Ensemble (BPropF V) * Ensemble (BPropF V) =>
  CompNotDer x) (e, e0) (conj c f)) s). unfold Canon_rel. simpl.
  intro. intros. apply H1. apply Union_introl. auto. apply w in J2.
  apply IHA2 in J2. simpl in J2.
  apply H4. exists [A2]. repeat split. apply NoDup_cons. auto. apply NoDup_nil.
  intros. inversion H5. subst. simpl. apply H2. apply In_singleton. inversion H6.
  simpl. apply MP with (ps:=[(x, Imp A2 (Or A2 (Bot V)));(x, A2)]). 2: apply MPRule_I.
  intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A2. exists (Bot V).
  auto. inversion H6. 2: inversion H7. subst. apply Id. apply IdRule_I. auto.
  apply IHA1. simpl. apply H1. apply Union_intror. apply In_singleton.
- intros. destruct x. simpl in H. destruct v. simpl. destruct x. simpl.
  apply IHA1 in H1. simpl in H1. unfold Canon_rel in H0. simpl in H0.
  apply H0 in H. unfold CompNotDer in c0. destruct c0. simpl in f. simpl in c0.
  apply IHA2. simpl.
  assert (wpair_derrec (e1, Singleton _ A2)). exists [A2]. repeat split.
  apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H2. subst. apply In_singleton.
  inversion H3. simpl.
  apply MP with (ps:=[(e1, Imp A2 (Or A2 (Bot V)));(e1, A2)]). 2: apply MPRule_I.
  intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A2. exists (Bot V).
  auto. inversion H3. subst.
  apply MP with (ps:=[(e1, Imp A1 A2);(e1, A1)]). 2: apply MPRule_I.
  intros. inversion H4. subst. apply Id. apply IdRule_I. auto.
  inversion H5. 2: inversion H6. subst. apply Id. apply IdRule_I. auto.
  inversion H4.
  apply clos_deriv with (Δ:=e2). unfold CompNotDer ; auto. destruct H2. destruct H2.
  destruct H3. destruct x. simpl in H4. apply MP with (ps:=[(e1, Imp (Bot V) A2);(e1, Bot V)]).
  2: apply MPRule_I. intros. inversion H5. subst. apply wEFQ. inversion H6. 2: inversion H7.
  subst. auto. inversion H2. subst. pose (H3 b). assert (List.In b (b :: x)).
  apply in_eq. apply s in H5. inversion H5. subst. destruct x. simpl in H4.
  apply absorp_Or1 in H4. auto. exfalso. pose (H3 b0). assert (List.In b0 (b :: b0 :: x)).
  apply in_cons. apply in_eq. apply s0 in H6. inversion H6. subst. apply H7. apply in_eq.
(* Excl A1 A2 *)
- destruct H. destruct H. destruct H0. apply IHA1 in H0.
  assert (In (BPropF V) (fst (proj1_sig x0)) (Or A2 (Excl A1 A2))).
  apply clos_deriv with (Δ:=(snd (proj1_sig x0))). unfold CompNotDer ; auto.
  destruct x0. simpl. auto. destruct x0. simpl.
  apply MP with (ps:=[(fst x0, Imp A1 (Or A2 (Excl A1 A2)));(fst x0, A1)]). 2: apply MPRule_I.
  intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA11_I. exists A1.
  exists A2. auto. inversion H3. 2: inversion H4. subst. apply Id. apply IdRule_I.
  auto. apply primeness with (Δ:=snd (proj1_sig x0)) in H2. destruct H2 ; auto. exfalso.
  apply H1. apply IHA2 ; auto. destruct x0. simpl in H2. auto.
- assert (wpair_derrec ((Singleton _ A1), Union _ (snd x) (Singleton _ A2)) -> False).
  intro. destruct H0. destruct H0. destruct H1. simpl in H2. simpl in H1.
  destruct x. simpl in H. simpl in H1. destruct c. simpl in H3. simpl in H4.
  pose (remove_disj x0 A2 (Singleton (BPropF V) A1)).
  assert (wBIH_rules (Singleton (BPropF V) A1, Or A2 (list_disj (remove eq_dec_form A2 x0)))).
  apply MP with (ps:=[(Singleton (BPropF V) A1, list_disj x0 → Or A2
   (list_disj (remove eq_dec_form A2 x0)));(Singleton (BPropF V) A1, list_disj x0)]).
  2: apply MPRule_I. intros. inversion H5. subst. auto. inversion H6. subst.
  auto. inversion H7. clear w. clear H2.
  assert (Singleton (BPropF V) A1 = Union _ (Empty_set _) (Singleton (BPropF V) A1)).
  apply Extensionality_Ensembles. split. intro. intros. inversion H2. subst.
  apply Union_intror. apply In_singleton. intro. intros. inversion H2.
  subst. inversion H6. inversion H6. subst. apply In_singleton. rewrite H2 in H5.
  assert (J1: Union (BPropF V) (Empty_set (BPropF V)) (Singleton (BPropF V) A1) =
  Union (BPropF V) (Empty_set (BPropF V)) (Singleton (BPropF V) A1)). auto.
  assert (J2: Or A2 (list_disj (remove eq_dec_form A2 x0)) = Or A2 (list_disj (remove eq_dec_form A2 x0))). auto.
  pose (wBIH_Deduction_Theorem (Union (BPropF V) (Empty_set (BPropF V)) (Singleton (BPropF V) A1),
  Or A2 (list_disj (remove eq_dec_form A2 x0))) H5 A1 (Or A2 (list_disj (remove eq_dec_form A2 x0)))
  (Empty_set _) J1 J2). apply wdual_residuation in w. clear J2. clear J1. clear H2.
  clear H5.
  apply H4. exists (remove eq_dec_form A2 x0). repeat split. apply NoDup_remove.
  auto. intros. simpl. pose (H1 A). assert (List.In A x0). apply In_remove with (B:= A2).
  auto. apply u in H5. inversion H5. subst. auto. subst. inversion H6.
  subst. exfalso. apply remove_In in H2. auto. simpl.
  apply MP with (ps:=[(e, Excl A1 A2 → list_disj (remove eq_dec_form A2 x0));(e, Excl A1 A2)]).
  2: apply MPRule_I. intros. inversion H2. subst.
  pose (wBIH_monot (Empty_set (BPropF V), Excl A1 A2 → list_disj (remove eq_dec_form A2 x0))
  w e). apply w0. clear w0. simpl. intro. intros. inversion H5. inversion H5.
  subst. 2: inversion H6. clear H2. clear H5. apply Id. apply IdRule_I. auto.
  apply Lindenbaum_lemma in H0. destruct H0. destruct H0. destruct H0.
  destruct H1. destruct H2.
  assert (J1: CompNotDer (x0, x1)). unfold CompNotDer. auto.
  pose (@exist (prod (Ensemble (BPropF V)) (Ensemble (BPropF V))) CompNotDer (x0,x1) J1).
  exists s. unfold Canon_rel. simpl. split. destruct x. simpl.
  intro. intros. destruct c. simpl in H5. pose (H5 x). destruct o.
  simpl in H7. auto. simpl in H7. exfalso. pose (H1 x). simpl in i.
  assert (In (BPropF V) (Union (BPropF V) e0 (Singleton (BPropF V) A2)) x).
  apply Union_introl. auto. apply i in H8. apply H3. exists [x].
  repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
  intros. inversion H9. subst. simpl. auto. inversion H10.
  simpl. apply MP with (ps:=[(x0, Imp x (Or x (Bot V))); (x0, x)]).
  2: apply MPRule_I. intros. inversion H9. subst.
  apply Ax. apply AxRule_I. apply RA2_I. exists x. exists (Bot V). auto.
  inversion H10. 2: inversion H11. subst. apply Id. apply IdRule_I.
  auto. split. apply IHA1. simpl. apply H0. apply In_singleton.
  intro. apply IHA2 in H4. simpl in H4. apply H3. exists [A2].
  repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
  intros. inversion H5. subst. simpl. apply H1. apply Union_intror.
  apply In_singleton. inversion H6. simpl.
  apply MP with (ps:=[(x0, Imp A2 (Or A2 (Bot V)));(x0, A2)]). 2: apply MPRule_I.
  intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A2.
  exists (Bot V). auto. inversion H6. 2: inversion H7. subst. clear H5.
  clear H6. apply Id. apply IdRule_I. auto.
Qed.

Theorem wCounterCompleteness : forall (Γ Δ : @Ensemble (BPropF V)),
    (wpair_derrec (Γ, Δ) -> False) -> ((loc_conseq Γ Δ) -> False).
Proof.
intros Γ Δ WD.
apply Lindenbaum_lemma in WD. destruct WD. destruct H. destruct H. destruct H0.
destruct H1. intro. unfold loc_conseq in H3.
assert (J1: complete (fst (x, x0), snd (x, x0)) /\ (wpair_derrec (fst (x, x0), snd (x, x0)) -> False)). auto.
pose (@exist (prod (Ensemble (BPropF V)) (Ensemble (BPropF V))) CompNotDer (x,x0) J1).
pose (H3 CM s).
assert ((forall A : BPropF V, In (BPropF V) Γ A -> wforces CM s A)). intros. apply truth_lemma. auto.
apply e in H4. destruct H4. destruct H4. apply truth_lemma in H5. simpl in H5.
apply H2. exists [x1]. repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
intros. inversion H6. simpl. subst. apply H0 ; auto. inversion H7. simpl.
apply MP with (ps:=[(x, Imp x1 (Or x1 (Bot V)));(x, x1)]). 2: apply MPRule_I.
intros. inversion H6. subst. apply Ax. apply AxRule_I. apply RA2_I. exists x1. exists (Bot V).
auto. inversion H7. subst. 2: inversion H8. apply Id. apply IdRule_I. auto.
Qed.

Theorem wCompleteness : forall (Γ Δ : @Ensemble (BPropF V)),
    (loc_conseq Γ Δ) -> wpair_derrec (Γ, Δ).
Proof.
intros Γ Δ LC. pose (wCounterCompleteness Γ Δ).
pose (classic (wpair_derrec (Γ, Δ))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.
