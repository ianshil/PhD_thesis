Require Import List.
Export ListNotations.

Require Import PeanoNat.

Require Import Ensembles.
Require Import BiInt_GHC.

Lemma subst_Ax : forall A f, (BIAxioms A) -> (BIAxioms (subst f A)).
Proof.
intros A f Ax. induction Ax.
- destruct H. destruct H. destruct H. subst. apply RA1_I.
  exists (subst f x). exists (subst f x0). exists (subst f x1). unfold RA1. reflexivity.
- destruct H. destruct H. subst. apply RA2_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. subst. apply RA3_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA4_I.
  exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
- destruct H. destruct H. subst. apply RA5_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. subst. apply RA6_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA7_I.
  exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA8_I.
  exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA9_I.
  exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
- destruct H. destruct H. subst. apply RA10_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. subst. apply RA11_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. subst. apply RA12_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. destruct H. subst. apply RA13_I.
  exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
- destruct H. destruct H. subst. apply RA14_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. subst. apply RA15_I.
  exists (subst f x). reflexivity.
- destruct H. subst. apply RA16_I.
  exists (subst f x). reflexivity.
Qed.

Theorem wBIH_monot : forall s,
          (wBIH_rules s) ->
          (forall Γ1, (Included _ (fst s) Γ1) ->
          (wBIH_rules (Γ1, (snd s)))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ1 incl. inversion H. subst. apply Id. apply IdRule_I. simpl. apply incl.
  assumption.
(* Ax *)
- intros Γ1 incl. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ1 incl. inversion H1. subst. simpl. apply MP with (ps:=[(Γ1, A → B); (Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A → B) [(Γ, A → B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A → B) J1 Γ1). apply w. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A → B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 Γ1). apply w. auto. inversion H4. apply MPRule_I.
(* DNw *)
- intros Γ1 incl. inversion H1. subst. simpl. apply DNw with (ps:=[(Empty_set _, A)]).
  intros. inversion H2. subst. auto. inversion H3. apply DNwRule_I.
Qed.

Theorem sBIH_monot : forall s,
          (sBIH_rules s) ->
          (forall Γ1, (Included _ (fst s) Γ1) ->
          (sBIH_rules (Γ1, (snd s)))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros Γ1 incl. inversion H. subst. apply Ids. apply IdRule_I. simpl. apply incl.
  assumption.
(* Axs *)
- intros Γ1 incl. inversion H. subst. apply Axs. apply AxRule_I. assumption.
(* MPs *)
- intros Γ1 incl. inversion H1. subst. simpl. apply MPs with (ps:=[(Γ1, A → B); (Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A → B) [(Γ, A → B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A → B) J1 Γ1). apply s. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A → B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 Γ1). apply s. auto. inversion H4. apply MPRule_I.
(* DNs *)
- intros Γ1 incl. inversion H1. subst. simpl. apply DNs with (ps:=[(Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A) [(Γ, A)]). apply in_eq.
  pose (H0 (Γ, A) J1 Γ1). apply s. simpl. auto. inversion H3. apply DNsRule_I.
Qed.

Theorem wBIH_comp : forall s,
          (wBIH_rules s) ->
          (forall Γ,  (forall A, ((fst s) A) -> wBIH_rules (Γ, A)) ->
          wBIH_rules (Γ, (snd s))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ derall. inversion H. subst. pose (derall A). apply w. auto.
(* Ax *)
- intros Γ derall. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ derall. inversion H1. subst. apply MP with (ps:=[(Γ, A → B); (Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A → B) [(Γ0, A → B); (Γ0, A)]). apply in_eq.
  pose (H0 (Γ0, A → B) J1 Γ). apply w. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ0, A) [(Γ0, A → B); (Γ0, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ0, A) J2 Γ). apply w. auto. inversion H4. apply MPRule_I.
(* DNw *)
- intros Γ derall. inversion H1. subst. simpl. apply DNw with (ps:=[(Empty_set _, A)]).
  intros. inversion H2. subst. auto. inversion H3. apply DNwRule_I.
Qed.

Theorem sBIH_comp : forall s,
          (sBIH_rules s) ->
          (forall Γ,  (forall A, ((fst s) A) -> sBIH_rules (Γ, A)) ->
          sBIH_rules (Γ, (snd s))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros Γ derall. inversion H. subst. pose (derall A). apply s. auto.
(* Axs *)
- intros Γ derall. inversion H. subst. apply Axs. apply AxRule_I. assumption.
(* MPs *)
- intros Γ derall. inversion H1. subst. apply MPs with (ps:=[(Γ, A → B); (Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A → B) [(Γ0, A → B); (Γ0, A)]). apply in_eq.
  pose (H0 (Γ0, A → B) J1 Γ). apply s. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ0, A) [(Γ0, A → B); (Γ0, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ0, A) J2 Γ). apply s. auto. inversion H4. apply MPRule_I.
(* DNs *)
- intros Γ derall. inversion H1. subst. simpl. apply DNs with (ps:=[(Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A) [(Γ0, A)]). apply in_eq.
  pose (H0 (Γ0, A) J1 Γ). apply s. simpl. auto. inversion H3. apply DNsRule_I.
Qed.

Theorem wBIH_struct : forall s,
          (wBIH_rules s) ->
          (forall (f : V -> (BPropF V)),
          (wBIH_rules ((fun y => (exists A, prod ((fst s) A) (y = (subst f A)))), (subst f (snd s))))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros f. inversion H. subst. simpl. apply Id. apply IdRule_I.
  exists A. auto.
(* Ax *)
- intros f. inversion H. subst. apply Ax. apply AxRule_I. 
  apply subst_Ax with (f:=f). assumption.
(* MP *)
- intros f. inversion H1. subst. apply MP with (ps:=[((fun y : BPropF V =>
  exists A0 : BPropF V, prod (Γ A0) (y = subst f A0)), (subst f A) → (subst f B)); ((fun y : BPropF V =>
  exists A0 : BPropF V, prod (Γ A0) (y = subst f A0)), (subst f A))]). simpl.
  intros. inversion H2. subst. assert (J1: List.In (Γ, A → B) [(Γ, A → B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A → B) J1 f). apply w. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A → B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 f). apply w. auto. inversion H4. apply MPRule_I.
(* DNw *)
- intros f. inversion H1. subst. apply DNw with (ps:=[(Empty_set _, (subst f A))]).
  intros. inversion H2. subst. assert (J1: List.In (Empty_set (BPropF V), A) [(Empty_set (BPropF V), A)]). apply in_eq.
  pose (H0 (Empty_set (BPropF V), A) J1 f). simpl in w.
  assert ((fun y : BPropF V => exists A : BPropF V,
  prod (Empty_set _ A) (y = subst f A)) = Empty_set _).
  { apply Extensionality_Ensembles. split. intro. intro. inversion H3. destruct H4.
    inversion e. intro. intro. inversion H3. } rewrite H3 in w. apply w. simpl. auto.
  inversion H3. apply DNwRule_I.
Qed.

Theorem sBIH_struct : forall s,
          (sBIH_rules s) ->
          (forall (f : V -> (BPropF V)),
          (sBIH_rules ((fun y => (exists A, prod ((fst s) A) (y = (subst f A)))), (subst f (snd s))))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros f. inversion H. subst. simpl. apply Ids. apply IdRule_I.
  exists A. auto.
(* Axs *)
- intros f. inversion H. subst. apply Axs. apply AxRule_I.
  apply subst_Ax with (f:=f). assumption.
(* MPs *)
- intros f. inversion H1. subst. apply MPs with (ps:=[((fun y : BPropF V =>
  exists A0 : BPropF V, prod (Γ A0) (y = subst f A0)), (subst f A) → (subst f B)); ((fun y : BPropF V =>
  exists A0 : BPropF V, prod (Γ A0) (y = subst f A0)), (subst f A))]). simpl.
  intros. inversion H2. subst. assert (J1: List.In (Γ, A → B) [(Γ, A → B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A → B) J1 f). apply s. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A → B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 f). apply s. auto. inversion H4. apply MPRule_I.
(* DNs *)
- intros f. inversion H1. subst. simpl. apply DNs with (ps:=[((fun y : BPropF V => exists A0 : BPropF V,
  (prod (Γ A0) (y = subst f A0))), (subst f A))]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A) [(Γ, A)]). apply in_eq.
  pose (H0 (Γ, A) J1 f). simpl in s. apply s. inversion H3. apply DNsRule_I.
Qed.

Theorem wBIH_finite : forall s,
          (wBIH_rules s) ->
          (exists (Γ : Ensemble _), prod (Included _ Γ (fst s))
                                     (prod (wBIH_rules (Γ, snd s))
                                     (exists (l : list (BPropF V)), (forall A, ((Γ A) -> List.In A l) * (List.In A l -> (Γ A)))))).
Proof.
intros s D0. induction D0.
(* Id *)
- inversion H. subst. simpl. exists (fun x => x = A).
  repeat split. intro. intro. unfold In. inversion H1. assumption.
  apply Id. apply IdRule_I. auto.
  exists [A]. intro. split. intro. subst. apply in_eq. intro. inversion H1.
  subst. auto. inversion H2.
(* Ax *)
- inversion H. subst. simpl. exists (Empty_set _).
  repeat split. intro. intro. unfold In. inversion H1.
  apply Ax. apply AxRule_I. auto.
  exists []. intro. split. intro. subst. inversion H1. intro. inversion H1.
(* MP *)
- inversion H1. subst. assert (J1: List.In (Γ, A → B) [(Γ, A → B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A → B) J1). destruct e. destruct H2. destruct p. destruct e.
  assert (J2: List.In (Γ, A) [(Γ, A → B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). destruct e. destruct H3. destruct p. destruct e.
  exists (Union _ x x1). repeat split. intro. intro. simpl. inversion H4.
  subst. apply i. assumption. apply i0. assumption. simpl.
  apply MP with (ps:=[(Union _ x x1, A → B); (Union _ x x1, A)]).
  intros. inversion H4. subst.
  assert (J3: Included _ (fst (x, A → B)) (Union _ x x1)). intro. simpl. intro.
  apply Union_introl. assumption. pose (@wBIH_monot (x, A → B) w (Union _ x x1) J3). assumption.
  inversion H5. subst. assert (J4: Included _ (fst (x1, A)) (Union _ x x1)). intro. simpl. intro.
  apply Union_intror. assumption. pose (@wBIH_monot (x1, A) w0 (Union _ x x1) J4). assumption.
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
Qed.

Theorem sBIH_finite : forall s,
          (sBIH_rules s) ->
          (exists (Γ : Ensemble _), prod (Included _ Γ (fst s))
                                     (prod (sBIH_rules (Γ, snd s))
                                     (exists (l : list (BPropF V)), (forall A, ((Γ A) -> List.In A l) * (List.In A l -> (Γ A)))))).
Proof.
intros s D0. induction D0.
(* Ids *)
- inversion H. subst. simpl. exists (fun x => x = A).
  repeat split. intro. intro. unfold In. inversion H1. assumption.
  apply Ids. apply IdRule_I. auto.
  exists [A]. intro. split. intro. subst. apply in_eq. intro. inversion H1.
  subst. auto. inversion H2.
(* Axs *)
- inversion H. subst. simpl. exists (Empty_set _).
  repeat split. intro. intro. unfold In. inversion H1.
  apply Axs. apply AxRule_I. auto.
  exists []. intro. split. intro. subst. inversion H1. intro. inversion H1.
(* MPs *)
- inversion H1. subst. assert (J1: List.In (Γ, A → B) [(Γ, A → B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A → B) J1). destruct e. destruct H2. destruct p. destruct e.
  assert (J2: List.In (Γ, A) [(Γ, A → B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). destruct e. destruct H3. destruct p. destruct e.
  exists (Union _ x x1). repeat split. intro. intro. simpl. inversion H4.
  subst. apply i. assumption. apply i0. assumption. simpl.
  apply MPs with (ps:=[(Union _ x x1, A → B); (Union _ x x1, A)]).
  intros. inversion H4. subst.
  assert (J3: Included _ (fst (x, A → B)) (Union _ x x1)). intro. simpl. intro.
  apply Union_introl. assumption. pose (@sBIH_monot (x, A → B) s (Union _ x x1) J3). assumption.
  inversion H5. subst. assert (J4: Included _ (fst (x1, A)) (Union _ x x1)). intro. simpl. intro.
  apply Union_intror. assumption. pose (@sBIH_monot (x1, A) s0 (Union _ x x1) J4). assumption.
  inversion H6. apply MPRule_I.
  exists (x0 ++ x2). intro. split. intro. inversion H4. subst. pose (H2 A0).
  destruct p. apply in_or_app. apply i1 in H5. auto. subst. pose (H3 A0).
  destruct p. apply i1 in H5. apply in_or_app. auto. intro. apply in_app_or in H4.
  destruct H4. apply Union_introl. apply H2. assumption. apply Union_intror.
  apply H3. assumption.
(* DNs *)
- inversion H1. subst. assert (J1: List.In (Γ, A) [(Γ, A)]). apply in_eq.
  pose (H0 (Γ, A) J1). destruct e. destruct H2. destruct p. destruct e.
  exists x. repeat split. assumption.
  apply DNs with (ps:=[(x, A)]). intro. intro. simpl. inversion H3. subst.
  auto. inversion H4. apply DNsRule_I. exists x0. intro. split. intro. apply H2 ; assumption.
  intro. apply H2 ; assumption.
Qed.
