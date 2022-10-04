Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Ensembles.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.

Section Logics.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(* Variable substituitions preserve provability. *)

Lemma subst_Ax : forall A f, (BIAxioms A) -> (BIAxioms A[f]).
Proof.
intros A f Ax. revert f. induction Ax ; intro f.
- destruct H. destruct H. destruct H. subst. apply RA1_I.
  exists (x[f]). exists (x0[f]). exists (x1[f]). unfold RA1. reflexivity.
- destruct H. destruct H. subst. apply RA2_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. destruct H. subst. apply RA3_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA4_I.
  exists (x[f]). exists (x0[f]). exists (x1[f]). reflexivity.
- destruct H. destruct H. subst. apply RA5_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. destruct H. subst. apply RA6_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA7_I.
  exists (x[f]). exists (x0[f]). exists (x1[f]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA8_I.
  exists (x[f]). exists (x0[f]). exists (x1[f]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA9_I.
  exists (x[f]). exists (x0[f]). exists (x1[f]). reflexivity.
- destruct H. destruct H. subst. apply RA10_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. destruct H. subst. apply RA11_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. destruct H. subst. apply RA12_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA13_I.
  exists (x[f]). exists (x0[f]). exists (x1[f]). reflexivity.
- destruct H. destruct H. subst. apply RA14_I.
  exists (x[f]). exists (x0[f]). reflexivity.
- destruct H. subst. apply RA15_I. exists (x[f]). reflexivity.
- destruct H. subst. apply RA16_I. exists (x[f]). reflexivity.
- destruct H. destruct H. subst. apply RA17_I.
  unfold RA17. simpl. exists (x[f]). exists (x0[up f]).
  rewrite up_form. reflexivity.
- destruct H. destruct H. subst. apply RA18_I.
  unfold RA18. simpl. exists (x[up f]).
  assert (exists t, x[x0..][f] = x[up f][t..]).
  { rewrite subst_comp. unfold funcomp. 
     exists (subst_term f x0).
    rewrite subst_comp. unfold funcomp. apply subst_ext. intros.
    induction n. simpl. auto. simpl. unfold funcomp. rewrite subst_term_comp.
    rewrite subst_term_id. auto. auto. }
  destruct H. exists x1. rewrite H. auto.
- destruct H. destruct H. subst. apply RA19_I.
  unfold RA19. simpl. exists (x[up f]).
  assert (exists t, x[x0..][f] = x[up f][t..]).
  { rewrite subst_comp. unfold funcomp. 
     exists (subst_term f x0).
    rewrite subst_comp. unfold funcomp. apply subst_ext. intros.
    induction n. simpl. auto. simpl. unfold funcomp. rewrite subst_term_comp.
    rewrite subst_term_id. auto. auto. }
  destruct H. exists x1. rewrite H. auto.
Qed.

Theorem FOwBIH_subst : forall s f, FOwBIH_rules s ->
    FOwBIH_rules (fun x : form => exists B : form, x = B[f] /\ In form (fst s) B, (snd s)[f]).
Proof.
intros s f D. revert f. induction D ; intro f.
(* Id *)
- inversion H. subst. apply Id. apply IdRule_I. simpl. exists A. auto.
(* Ax *)
- inversion H. subst. apply Ax. apply AxRule_I. simpl. apply subst_Ax. auto.
(* MP *)
- inversion H1. subst. simpl. apply MP with (ps:=[(fun x : form => exists B : form, x = B[f] /\ In form Γ B, (A --> B)[f]); (fun x : form => exists B : form, x = B[f] /\ In form Γ B, A[f])]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1). apply f0. inversion H3. subst.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). apply f0. inversion H4. simpl. apply MPRule_I.
(* DNw *)
- inversion H1. subst. simpl. apply DNw with (ps:=[(Empty_set _ , A[f])]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply DNwRule_I.
  assert (J1: List.In (Empty_set form, A) ((Empty_set form, A) :: nil)). apply in_eq.
  pose (H0 (Empty_set _, A) J1 f). simpl in f0.
  assert ((fun x : form => exists B : form, x = B[f] /\ In form (Empty_set form) B) = Empty_set _).
  apply Extensionality_Ensembles. split. intro. intros. inversion H3. destruct H4. inversion H5.
  intro. intros. inversion H3. rewrite H3 in f0 ; auto.
(* Gen *)
- inversion H1. subst. simpl.
  apply Gen with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f] /\ In form Γ B) C), A[up f])]).
  2: apply GenRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B), A) (((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil))). apply in_eq.
  pose (@H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1). simpl in f0.
  pose (f0 (up f)).
  assert ((fun x : form => exists B : form, x = B[up f] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B : form, x0 = B[f] /\ In form Γ B) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f]. split. apply up_form. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite up_form. auto. exists x ; split ; auto. rewrite <- H3 ; auto.
(* EC *)
- inversion H1. subst. simpl.
  apply EC with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f] /\ In form Γ B) C), A[up f] --> B[f][↑])]).
  2: apply ECRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (@H0 _ J1). simpl in f0. pose (f0 (up f)).
  assert ((fun x : form => exists B : form, x = B[up f] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[f] /\ In form Γ B0) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f]. split. apply up_form. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite up_form. auto. exists x ; split ; auto.  rewrite up_form in f1. rewrite <- H3 ; auto.
Qed.

Theorem FOsBIH_subst : forall s f, FOsBIH_rules s -> FOsBIH_rules (fun x : form => exists B : form, x = B[f] /\ In form (fst s) B, (snd s)[f]).
Proof.
intros s f D. revert f. induction D ; intro f.
(* Ids *)
- inversion H. subst. apply Ids. apply IdRule_I. simpl. exists A. auto.
(* Axs *)
- inversion H. subst. apply Axs. apply AxRule_I. simpl. apply subst_Ax. auto.
(* MPs *)
- inversion H1. subst. simpl. apply MPs with (ps:=[(fun x : form => exists B : form, x = B[f] /\ In form Γ B, (A --> B)[f]); (fun x : form => exists B : form, x = B[f] /\ In form Γ B, A[f])]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1). apply f0. inversion H3. subst.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). apply f0. inversion H4. simpl. apply MPRule_I.
(* DNs *)
- inversion H1. subst. simpl. apply DNs with (ps:=[(fun x : form => exists B : form, x = B[f] /\ In form Γ B, A[f])]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply DNsRule_I.
  apply H0 with (prem:=(Γ, A)). apply in_eq.
(* Gens *)
- inversion H1. subst. simpl.
  apply Gens with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f] /\ In form Γ B) C), A[up f])]).
  2: apply GenRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B), A) (((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil))). apply in_eq.
  pose (@H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1). simpl in f0.
  pose (f0 (up f)).
  assert ((fun x : form => exists B : form, x = B[up f] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B : form, x0 = B[f] /\ In form Γ B) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f]. split. apply up_form. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite up_form. auto. exists x ; split ; auto. rewrite <- H3 ; auto.
(* ECs *)
- inversion H1. subst. simpl.
  apply ECs with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f] /\ In form Γ B) C), A[up f] --> B[f][↑])]).
  2: apply ECRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (@H0 _ J1). simpl in f0. pose (f0 (up f)).
  assert ((fun x : form => exists B : form, x = B[up f] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[f] /\ In form Γ B0) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f]. split. apply up_form. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite up_form. auto. exists x ; split ; auto.  rewrite up_form in f1. rewrite <- H3 ; auto.
Qed.

(* Monotonicity holds. *)

Theorem FOwBIH_monot : forall s,
          (FOwBIH_rules s) ->
          (forall Γ1, Included _ (fst s) Γ1 -> (FOwBIH_rules (Γ1, (snd s)))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ1 incl. inversion H. subst. apply Id. apply IdRule_I. simpl. apply incl ; auto.
(* Ax *)
- intros Γ1 incl. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ1 incl. inversion H1. subst. simpl. apply MP with (ps:=[(Γ1, A --> B); (Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1 Γ1). apply f ; auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 Γ1). apply f ; auto. inversion H4. apply MPRule_I.
(* DNw *)
- intros Γ1 incl. inversion H1. subst. simpl. apply DNw with (ps:=[(Empty_set _ , A)]).
  intros. inversion H2. subst. auto. inversion H3. apply DNwRule_I.
(* Gen *)
- intros Γ1 incl. inversion H1. subst. simpl. simpl in incl. apply Gen with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B, A)]).
  2: apply GenRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1 (fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B)). apply f.
  intro. simpl. intro. inversion H3. destruct H4 ; subst. unfold In. exists x0 ; split ; auto. apply incl ; auto.
(* EC *)
- intros Γ1 incl. inversion H1. subst. simpl. apply EC with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B, A --> B[↑])]).
  2: apply ECRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) J1 (fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B)). apply f.
  intro. simpl. intro. inversion H3. destruct H4 ; subst. unfold In. exists x0 ; split ; auto. apply incl ; auto.
Qed.

Theorem FOsBIH_monot : forall s,
          (FOsBIH_rules s) ->
          (forall Γ1, Included _ (fst s) Γ1 -> (FOsBIH_rules (Γ1, (snd s)))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros Γ1 incl. inversion H. subst. apply Ids. apply IdRule_I. simpl. apply incl ; auto.
(* Axs *)
- intros Γ1 incl. inversion H. subst. apply Axs. apply AxRule_I. assumption.
(* MPs *)
- intros Γ1 incl. inversion H1. subst. simpl. apply MPs with (ps:=[(Γ1, A --> B); (Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1 Γ1). apply f ; auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 Γ1). apply f ; auto. inversion H4. apply MPRule_I.
(* DNs *)
- intros Γ1 incl. inversion H1. subst. simpl. apply DNs with (ps:=[(Γ1 , A)]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply DNsRule_I.
  apply H0 with (prem:=(Γ, A)). apply in_eq. auto.
(* Gens *)
- intros Γ1 incl. inversion H1. subst. simpl. simpl in incl. apply Gens with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B, A)]).
  2: apply GenRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1 (fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B)). apply f.
  intro. simpl. intro. inversion H3. destruct H4 ; subst. unfold In. exists x0 ; split ; auto. apply incl ; auto.
(* ECs *)
- intros Γ1 incl. inversion H1. subst. simpl. apply ECs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B, A --> B[↑])]).
  2: apply ECRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) J1 (fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B)). apply f.
  intro. simpl. intro. inversion H3. destruct H4 ; subst. unfold In. exists x0 ; split ; auto. apply incl ; auto.
Qed.

(* Compositionality holds. *)

Theorem FOwBIH_comp : forall s,
          (FOwBIH_rules s) ->
          (forall Γ,  (forall A, (In _ (fst s) A) -> FOwBIH_rules (Γ, A)) ->
          FOwBIH_rules (Γ, (snd s))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ derall. inversion H. subst. pose (derall A). apply f. auto.
(* Ax *)
- intros Γ derall. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ derall. inversion H1. subst. apply MP with (ps:=[(Γ, A --> B); (Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A --> B) ((Γ0, A --> B) :: (Γ0, A) :: nil)). apply in_eq.
  pose (H0 (Γ0, A --> B) J1 Γ). apply f. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ0, A) ((Γ0, A --> B) :: (Γ0, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ0, A) J2 Γ). apply f. auto. inversion H4. apply MPRule_I.
(* DNw *)
- intros Γ derall. inversion H1. subst. simpl. apply DNw with (ps:=[(Empty_set _, A)]).
  intros. inversion H2. subst. auto. inversion H3. apply DNwRule_I.
(* Gen *)
- intros Γ derall. inversion H1. subst. simpl. apply Gen with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A)]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply GenRule_I.
  apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B, A)). apply in_eq. simpl. intros. simpl in derall.
  inversion H3. destruct H4. subst. pose (derall x). apply f in H5.
  apply FOwBIH_subst with (f:=↑) (s:=(Γ, x)) ; auto.
(* EC *)
- intros Γ derall. inversion H1. subst. simpl. apply EC with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑])]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply ECRule_I.
  apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B, A --> B[↑])). apply in_eq. simpl. intros. simpl in derall.
  inversion H3. destruct H4. subst. pose (derall x). apply f in H5.
  apply FOwBIH_subst with (f:=↑) (s:=(Γ, x)) ; auto.
Qed.

Theorem FOsBIH_comp : forall s,
          (FOsBIH_rules s) ->
          (forall Γ,  (forall A, (In _ (fst s) A) -> FOsBIH_rules (Γ, A)) ->
          FOsBIH_rules (Γ, (snd s))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros Γ derall. inversion H. subst. pose (derall A). apply f. auto.
(* Axs *)
- intros Γ derall. inversion H. subst. apply Axs. apply AxRule_I. assumption.
(* MPs *)
- intros Γ derall. inversion H1. subst. apply MPs with (ps:=[(Γ, A --> B); (Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A --> B) ((Γ0, A --> B) :: (Γ0, A) :: nil)). apply in_eq.
  pose (H0 (Γ0, A --> B) J1 Γ). apply f. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ0, A) ((Γ0, A --> B) :: (Γ0, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ0, A) J2 Γ). apply f. auto. inversion H4. apply MPRule_I.
(* DNs *)
- intros Γ derall. inversion H1. subst. simpl. apply DNs with (ps:=[(Γ, A)]).
  intros. inversion H2. subst. auto. 2: inversion H3. 2: apply DNsRule_I.
  pose (H0 (Γ0, A)). apply f. apply in_eq. intros. simpl in H3. apply derall. auto.
(* Gens *)
- intros Γ derall. inversion H1. subst. simpl. apply Gens with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A)]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply GenRule_I.
  apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B, A)). apply in_eq. simpl. intros. simpl in derall.
  inversion H3. destruct H4. subst. pose (derall x). apply f in H5.
  apply FOsBIH_subst with (f:=↑) (s:=(Γ, x)) ; auto.
(* ECs *)
- intros Γ derall. inversion H1. subst. simpl. apply ECs with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑])]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply ECRule_I.
  apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B, A --> B[↑])). apply in_eq. simpl. intros. simpl in derall.
  inversion H3. destruct H4. subst. pose (derall x). apply f in H5.
  apply FOsBIH_subst with (f:=↑) (s:=(Γ, x)) ; auto.
Qed.

(* Atom substitution preserves provability. *)

(* Strong version *)

Lemma atom_subst_Ax : forall A f, (atom_subst_respects_strong f) -> (BIAxioms A) -> (BIAxioms A[f /atom]).
Proof.
intros A f resp Ax. revert resp. revert f. induction Ax ; intros f resp.
- destruct H. destruct H. destruct H. subst. apply RA1_I.
  exists (x[f /atom ] ). exists (x0[f /atom ] ). exists (x1[f /atom ]). unfold RA1. reflexivity.
- destruct H. destruct H. subst. apply RA2_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA3_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA4_I.
  exists (x[f /atom]). exists (x0[f /atom]). exists (x1[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA5_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA6_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA7_I.
  exists (x[f /atom]). exists (x0[f /atom]). exists (x1[f /atom]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA8_I.
  exists (x[f /atom]). exists (x0[f /atom]). exists (x1[f /atom]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA9_I.
  exists (x[f /atom]). exists (x0[f /atom]). exists (x1[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA10_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA11_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA12_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA13_I.
  exists (x[f /atom]). exists (x0[f /atom]). exists (x1[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA14_I.
  exists (x[f /atom]). exists (x0[f /atom]). reflexivity.
- destruct H. subst. apply RA15_I. exists (x[f /atom]). reflexivity.
- destruct H. subst. apply RA16_I. exists (x[f /atom]). reflexivity.
- destruct H. destruct H. subst. apply RA17_I.
  unfold RA17. simpl. exists (x[f /atom]). exists (x0[f /atom ]).
  repeat rewrite atom_subst_comp_strong ; auto.
- destruct H. destruct H. subst. apply RA18_I.
  unfold RA18. simpl. exists (x[f /atom ]). exists x0.
  rewrite atom_subst_comp_strong ; auto.
- destruct H. destruct H. subst. apply RA19_I.
  unfold RA19. simpl. exists (x[f /atom ]). exists x0.
  rewrite atom_subst_comp_strong ; auto.
Qed.

Theorem FOwBIH_struct : forall s f,
  (atom_subst_respects_strong f) ->
  (FOwBIH_rules s) ->
  FOwBIH_rules (fun x : form => exists B : form, x = B[ f /atom] /\ In form (fst s) B, (snd s)[ f /atom]).
Proof.
intros s f resp D. revert resp. revert f. induction D ; intros f resp.
(* Id *)
- inversion H. subst. apply Id. apply IdRule_I. simpl. exists A. auto.
(* Ax *)
- inversion H. subst. apply Ax. apply AxRule_I. simpl. apply atom_subst_Ax ; auto.
(* MP *)
- inversion H1. subst. simpl. apply MP with (ps:=[(fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B, (A --> B)[f /atom]); (fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B, A[f /atom])]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1). apply f0 ; auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). apply f0 ; auto. inversion H4. simpl. apply MPRule_I.
(* DNw *)
- inversion H1. subst. simpl. apply DNw with (ps:=[(Empty_set _ , A[f /atom])]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply DNwRule_I.
  assert (J1: List.In (Empty_set form, A) ((Empty_set form, A) :: nil)). apply in_eq.
  pose (H0 (Empty_set _, A) J1 f). simpl in f.
  assert ((fun x : form => exists B : form, x = B[f /atom] /\ In form (Empty_set form) B) = Empty_set _).
  apply Extensionality_Ensembles. split. intro. intros. inversion H3. destruct H4. inversion H5.
  intro. intros. inversion H3. simpl in f0. rewrite H3 in f0 ; auto.
(* Gen *)
- inversion H1. subst. simpl.
  apply Gen with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B) C), A[f /atom])]).
  2: apply GenRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B), A) (((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil))). apply in_eq.
  pose (@H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1). simpl in f0.
  pose (f0 f resp).
  assert ((fun x : form => exists B : form, x = B[f /atom ] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B : form, x0 = B[f /atom] /\ In form Γ B) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f /atom]. split. rewrite atom_subst_comp_strong ; auto. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite atom_subst_comp_strong ; auto. exists x ; split ; auto. rewrite <- H3 ; auto.
(* EC *)
- inversion H1. subst. simpl.
  apply EC with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B) C), A[f /atom] --> B[f /atom][↑])]).
  2: apply ECRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (@H0 _ J1). simpl in f0. pose (f0 f resp).
  assert ((fun x : form => exists B : form, x = B[f /atom] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[f /atom] /\ In form Γ B0) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f /atom]. split. rewrite atom_subst_comp_strong ; auto. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite atom_subst_comp_strong ; auto. exists x ; split ; auto. rewrite <- H3. rewrite <- atom_subst_comp_strong in f1 ; auto.
Qed.

Theorem FOsBIH_struct : forall s f,
  (atom_subst_respects_strong f) ->
  (FOsBIH_rules s) ->
  FOsBIH_rules (fun x : form => exists B : form, x = B[ f /atom] /\ In form (fst s) B, (snd s)[ f /atom]).
Proof.
intros s f resp D. revert resp. revert f. induction D ; intros f resp.
(* Ids *)
- inversion H. subst. apply Ids. apply IdRule_I. simpl. exists A. auto.
(* Axs *)
- inversion H. subst. apply Axs. apply AxRule_I. simpl. apply atom_subst_Ax ; auto.
(* MPs *)
- inversion H1. subst. simpl. apply MPs with (ps:=[(fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B, (A --> B)[f /atom]); (fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B, A[f /atom])]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1). apply f0 ; auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). apply f0 ; auto. inversion H4. simpl. apply MPRule_I.
(* DNs *)
- inversion H1. subst. simpl. apply DNs with (ps:=[(fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B, A[f /atom])]).
  intros. inversion H2. subst. 2: inversion H3. 2: apply DNsRule_I.
  apply H0 with (prem:=(Γ, A)) ; auto. apply in_eq.
(* Gens *)
- inversion H1. subst. simpl.
  apply Gens with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B) C), A[f /atom])]).
  2: apply GenRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B), A) (((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil))). apply in_eq.
  pose (@H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1). simpl in f0.
  pose (f0 f resp).
  assert ((fun x : form => exists B : form, x = B[f /atom ] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B : form, x0 = B[f /atom] /\ In form Γ B) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f /atom]. split. rewrite atom_subst_comp_strong ; auto. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite atom_subst_comp_strong ; auto. exists x ; split ; auto. rewrite <- H3 ; auto.
(* EC *)
- inversion H1. subst. simpl.
  apply ECs with (ps:=[((fun x : form => exists C : form, x = C[↑] /\ In _ (fun x : form => exists B : form, x = B[f /atom] /\ In form Γ B) C), A[f /atom] --> B[f /atom][↑])]).
  2: apply ECRule_I. intros. inversion H2. 2: inversion H3. subst.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (@H0 _ J1). simpl in f0. pose (f0 f resp).
  assert ((fun x : form => exists B : form, x = B[f /atom] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[↑] /\ In form Γ B0) B) =
  (fun x : form => exists C : form, x = C[↑] /\ In form (fun x0 : form => exists B0 : form, x0 = B0[f /atom] /\ In form Γ B0) C)).
  apply Extensionality_Ensembles. split ; intro ; intro. inversion H3. destruct H4. inversion H5. destruct H6.
  subst. unfold In. exists x1[f /atom]. split. rewrite atom_subst_comp_strong ; auto. exists x1. split ; auto. inversion H3.
  destruct H4. subst. inversion H5. destruct H4. subst. unfold In. exists x[↑]. split.
  rewrite atom_subst_comp_strong ; auto. exists x ; split ; auto. rewrite <- H3.
  rewrite <- atom_subst_comp_strong in f1 ; auto.
Qed.

(* They are finite logics. *)

Lemma List_Reverse_arrow : forall l0 Γ0 Γ1,
  (Included form Γ0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B)) ->
  (forall A : form, (Γ0 A -> List.In A l0) * (List.In A l0 -> Γ0 A)) ->
      (exists l1, (map (subst_form ↑) l1 = l0) /\ (forall y, List.In y l1 -> In _ Γ1 y)).
Proof.
induction l0 ; intros.
- exists []. split ; auto. intros. inversion H1.
- destruct (In_dec eq_dec_form a l0).
  + assert (J1: forall A : form, (Γ0 A -> List.In A l0) * (List.In A l0 -> Γ0 A)).
     intros. split ; intro. apply H0 in H1. inversion H1. subst. auto. auto.
     apply H0. apply in_cons. auto.
     pose (IHl0 Γ0 Γ1 H J1). destruct e. destruct H1. subst. pose (H0 a).
     destruct p. assert (List.In a (a :: map (subst_form ↑) x)). apply in_eq.
     apply γ in H1. apply H in H1. unfold In in H1. destruct H1. destruct H1. subst.
     exists (x0 :: x). simpl. split ; auto. intros. destruct H1 ; subst ; auto.
  + assert (J1: Included form (fun x : form => x <> a /\ In form Γ0 x)
     (fun x : form => exists B : form, x = B[↑] /\ In form Γ1 B)).
     intro. intros. unfold In in H1. destruct H1. apply H in H2. auto.
     assert (J2: (forall A : form, ((fun x : form => x <> a /\ In form Γ0 x) A -> List.In A l0) *
     (List.In A l0 -> (fun x : form => x <> a /\ In form Γ0 x) A))).
     intros. split. intro. destruct H1. apply H0 in H2. inversion H2. exfalso ; auto. auto.
     intros. split. intro. subst. auto. assert (List.In A (a :: l0)). apply in_cons ; auto.
     apply H0 in H2. auto.
     pose (IHl0 (fun x => x <> a /\ In _ Γ0 x) Γ1 J1 J2). destruct e. destruct H1. subst.
     pose (H0 a). destruct p. assert (List.In a (a :: map (subst_form ↑) x)). apply in_eq.
     apply γ in H1. apply H in H1. unfold In in H1. destruct H1. destruct H1. subst.
     exists (x0 :: x). simpl. split ; auto. intros. destruct H1 ; subst ; auto.
Qed.

Theorem FOwBIH_finite : forall s,
          (FOwBIH_rules s) ->
          (exists (Γ : Ensemble _), prod (Included _ Γ (fst s))
                                     (prod (FOwBIH_rules (Γ, snd s))
                                     (exists (l : list form), (forall A, ((Γ A) -> List.In A l) * (List.In A l -> (Γ A)))))).
Proof.
intros s D0. induction D0.
(* Id *)
- inversion H. subst. simpl. exists (fun x => x = A).
  repeat split. intro. intro. unfold In. inversion H1. assumption.
  apply Id. apply IdRule_I. auto. unfold In ; auto.
  exists [A]. intro. split. intro. subst. apply in_eq. intro. inversion H1.
  subst. auto. inversion H2.
(* Ax *)
- inversion H. subst. simpl. exists (Empty_set _).
  repeat split. intro. intro. unfold In. inversion H1.
  apply Ax. apply AxRule_I. auto.
  exists []. intro. split. intro. subst. inversion H1. intro. inversion H1.
(* MP *)
- inversion H1. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1). destruct e. destruct H2. destruct p. destruct e.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). destruct e. destruct H3. destruct p. destruct e.
  exists (Union _ x x1). repeat split. intro. intro. simpl. inversion H4.
  subst. apply i. assumption. apply i0. assumption. simpl.
  apply MP with (ps:=[(Union _ x x1, A --> B); (Union _ x x1, A)]).
  intros. inversion H4. subst.
  assert (J3: Included _ (fst (x, A --> B)) (Union _ x x1)). intro. simpl. intro.
  apply Union_introl. assumption. pose (@FOwBIH_monot (x, A --> B) f (Union _ x x1) J3). assumption.
  inversion H5. subst. assert (J4: Included _ (fst (x1, A)) (Union _ x x1)). intro. simpl. intro.
  apply Union_intror. assumption. pose (@FOwBIH_monot (x1, A) f0 (Union _ x x1) J4). assumption.
  inversion H6. apply MPRule_I.
  exists (x0 ++ x2). intro. split. intro. inversion H4. subst. pose (H2 A0).
  destruct p. apply in_or_app. apply i1 in H5. auto. subst. pose (H3 A0).
  destruct p. apply i1 in H5. apply in_or_app. auto. intro. apply in_app_or in H4.
  destruct H4. apply Union_introl. apply H2. assumption. apply Union_intror.
  apply H3. assumption.
(* DNw *)
- inversion H1. subst. exists (Empty_set _). repeat split.
  intro. intro. simpl. inversion H2. apply DNw with (ps:=[(Empty_set _, A)]).
  assumption. apply DNwRule_I. exists []. intro. split. intro. inversion H2.
  intro. inversion H2.
(* Gen *)
- inversion H1. subst. simpl.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1). destruct e. destruct H2. destruct p. destruct e.
  simpl in i. simpl in f.
  assert (exists x1, (map (subst_form ↑) x1 = x0) /\ (forall y, List.In y x1 -> In _ Γ y)).
  pose (List_Reverse_arrow x0 x Γ). apply e ; auto.
  destruct H3. destruct H3.
  exists (fun y => List.In y x1). repeat split. intro. intro. unfold In in H5. apply H4 ; auto.
  apply Gen with (ps:=[((fun z => exists C, z = C[↑] /\ In form (fun y : form => List.In y x1) C), A)]).
  intros. 2: apply GenRule_I. inversion H5. subst. 2: inversion H6.
  assert ((fun z : form => exists C : form, z = C[↑] /\ In form (fun y : form => List.In y x1) C) = x).
  apply Extensionality_Ensembles. split ; intro ; intro.
  inversion H3. destruct H6. subst. unfold In in H7. apply H2.
  apply in_map_iff. exists x2 ; split ; auto. unfold In. apply H2 in H3. apply in_map_iff in H3.
  destruct H3. destruct H3 ; subst. exists x2. split ; auto.
  rewrite H3. auto. exists x1. intros ; auto.
(* EC *)
- inversion H1. subst. simpl.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) J1). destruct e. destruct H2. destruct p. destruct e.
  simpl in i. simpl in f.
  assert (exists x1, (map (subst_form ↑) x1 = x0) /\ (forall y, List.In y x1 -> In _ Γ y)).
  pose (List_Reverse_arrow x0 x Γ). apply e ; auto.
  destruct H3. destruct H3.
  exists (fun y => List.In y x1). repeat split. intro. intro. unfold In in H5. apply H4 ; auto.
  apply EC with (ps:=[((fun z => exists C, z = C[↑] /\ In form (fun y : form => List.In y x1) C), A --> B[↑])]).
  intros. 2: apply ECRule_I. inversion H5. subst. 2: inversion H6.
  assert ((fun z : form => exists C : form, z = C[↑] /\ In form (fun y : form => List.In y x1) C) = x).
  apply Extensionality_Ensembles. split ; intro ; intro.
  inversion H3. destruct H6. subst. unfold In in H7. apply H2.
  apply in_map_iff. exists x2 ; split ; auto. unfold In. apply H2 in H3. apply in_map_iff in H3.
  destruct H3. destruct H3 ; subst. exists x2. split ; auto.
  rewrite H3. auto. exists x1. intros ; auto.
Qed.

Theorem FOsBIH_finite : forall s,
          (FOsBIH_rules s) ->
          (exists (Γ : Ensemble _), prod (Included _ Γ (fst s))
                                     (prod (FOsBIH_rules (Γ, snd s))
                                     (exists (l : list form), (forall A, ((Γ A) -> List.In A l) * (List.In A l -> (Γ A)))))).
Proof.
intros s D0. induction D0.
(* Ids *)
- inversion H. subst. simpl. exists (fun x => x = A).
  repeat split. intro. intro. unfold In. inversion H1. assumption.
  apply Ids. apply IdRule_I. auto. unfold In ; auto.
  exists [A]. intro. split. intro. subst. apply in_eq. intro. inversion H1.
  subst. auto. inversion H2.
(* Axs *)
- inversion H. subst. simpl. exists (Empty_set _).
  repeat split. intro. intro. unfold In. inversion H1.
  apply Axs. apply AxRule_I. auto.
  exists []. intro. split. intro. subst. inversion H1. intro. inversion H1.
(* MPs *)
- inversion H1. subst. assert (J1: List.In (Γ, A --> B) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A --> B) J1). destruct e. destruct H2. destruct p. destruct e.
  assert (J2: List.In (Γ, A) ((Γ, A --> B) :: (Γ, A) :: nil)). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). destruct e. destruct H3. destruct p. destruct e.
  exists (Union _ x x1). repeat split. intro. intro. simpl. inversion H4.
  subst. apply i. assumption. apply i0. assumption. simpl.
  apply MPs with (ps:=[(Union _ x x1, A --> B); (Union _ x x1, A)]).
  intros. inversion H4. subst.
  assert (J3: Included _ (fst (x, A --> B)) (Union _ x x1)). intro. simpl. intro.
  apply Union_introl. assumption. pose (@FOsBIH_monot (x, A --> B) f (Union _ x x1) J3). assumption.
  inversion H5. subst. assert (J4: Included _ (fst (x1, A)) (Union _ x x1)). intro. simpl. intro.
  apply Union_intror. assumption. pose (@FOsBIH_monot (x1, A) f0 (Union _ x x1) J4). assumption.
  inversion H6. apply MPRule_I.
  exists (x0 ++ x2). intro. split. intro. inversion H4. subst. pose (H2 A0).
  destruct p. apply in_or_app. apply i1 in H5. auto. subst. pose (H3 A0).
  destruct p. apply i1 in H5. apply in_or_app. auto. intro. apply in_app_or in H4.
  destruct H4. apply Union_introl. apply H2. assumption. apply Union_intror.
  apply H3. assumption.
(* DNs *)
- inversion H1. subst. simpl. assert (J1: List.In (Γ, A) ((Γ, A) :: nil)). apply in_eq.
  pose (H0 (Γ, A) J1). destruct e. destruct H2. destruct p. destruct e.
  exists x. repeat split. intro. intro. simpl. apply i. assumption.
  simpl in f. apply DNs with (ps:=[(x, A)]). 2: apply DNsRule_I. intros.
  inversion H3. subst. 2: inversion H4. auto. exists x0. intro. split ; intro ;
  apply H2 ; auto.
(* Gens *)
- inversion H1. subst. simpl.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A) J1). destruct e. destruct H2. destruct p. destruct e.
  simpl in i. simpl in f.
  assert (exists x1, (map (subst_form ↑) x1 = x0) /\ (forall y, List.In y x1 -> In _ Γ y)).
  pose (List_Reverse_arrow x0 x Γ). apply e ; auto.
  destruct H3. destruct H3.
  exists (fun y => List.In y x1). repeat split. intro. intro. unfold In in H5. apply H4 ; auto.
  apply Gens with (ps:=[((fun z => exists C, z = C[↑] /\ In form (fun y : form => List.In y x1) C), A)]).
  intros. 2: apply GenRule_I. inversion H5. subst. 2: inversion H6.
  assert ((fun z : form => exists C : form, z = C[↑] /\ In form (fun y : form => List.In y x1) C) = x).
  apply Extensionality_Ensembles. split ; intro ; intro.
  inversion H3. destruct H6. subst. unfold In in H7. apply H2.
  apply in_map_iff. exists x2 ; split ; auto. unfold In. apply H2 in H3. apply in_map_iff in H3.
  destruct H3. destruct H3 ; subst. exists x2. split ; auto.
  rewrite H3. auto. exists x1. intros ; auto.
(* ECs *)
- inversion H1. subst. simpl.
  assert (J1: List.In (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) ((fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) :: nil)). apply in_eq.
  pose (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑]) J1). destruct e. destruct H2. destruct p. destruct e.
  simpl in i. simpl in f.
  assert (exists x1, (map (subst_form ↑) x1 = x0) /\ (forall y, List.In y x1 -> In _ Γ y)).
  pose (List_Reverse_arrow x0 x Γ). apply e ; auto.
  destruct H3. destruct H3.
  exists (fun y => List.In y x1). repeat split. intro. intro. unfold In in H5. apply H4 ; auto.
  apply ECs with (ps:=[((fun z => exists C, z = C[↑] /\ In form (fun y : form => List.In y x1) C), A --> B[↑])]).
  intros. 2: apply ECRule_I. inversion H5. subst. 2: inversion H6.
  assert ((fun z : form => exists C : form, z = C[↑] /\ In form (fun y : form => List.In y x1) C) = x).
  apply Extensionality_Ensembles. split ; intro ; intro.
  inversion H3. destruct H6. subst. unfold In in H7. apply H2.
  apply in_map_iff. exists x2 ; split ; auto. unfold In. apply H2 in H3. apply in_map_iff in H3.
  destruct H3. destruct H3 ; subst. exists x2. split ; auto.
  rewrite H3. auto. exists x1. intros ; auto.
Qed.

End Logics.
