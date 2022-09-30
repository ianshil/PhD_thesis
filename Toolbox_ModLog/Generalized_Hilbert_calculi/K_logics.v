Require Import List.
Export ListNotations.

Require Import PeanoNat.

Require Import Ensembles.
Require Import K_Syntax.
Require Import K_GHC.

Lemma subst_Ax : forall A f, (KAxioms A) -> (KAxioms (subst f A)).
Proof.
intros A f Ax. induction Ax.
- destruct H. destruct H. destruct H. subst. apply MA1_I.
  exists (subst f x). exists (subst f x0). exists (subst f x1). reflexivity.
- destruct H. destruct H. subst. apply MA2_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. destruct H. subst. apply MA3_I.
  exists (subst f x). exists (subst f x0). reflexivity.
- destruct H. subst. apply MA4_I. exists (subst f x). reflexivity.
- destruct H. destruct H. subst. apply MA5_I.
  exists (subst f x). exists (subst f x0). reflexivity.
Qed.

Theorem wKH_monot : forall s,
          (wKH_prv s) ->
          (forall Γ1, (Included _ (fst s) Γ1) ->
          (wKH_prv (Γ1, (snd s)))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ1 incl. inversion H. subst. apply Id. apply IdRule_I. simpl. apply incl.
  assumption.
(* Ax *)
- intros Γ1 incl. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ1 incl. inversion H1. subst. simpl. apply MP with (ps:=[(Γ1, A --> B); (Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1 Γ1). apply w. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 Γ1). apply w. auto. inversion H4. apply MPRule_I.
(* wNec *)
- intros Γ1 incl. inversion H1. subst. simpl. apply wNec with (ps:=[(Empty_set _, A)]).
  intros. inversion H2. subst. auto. inversion H3. apply wNecRule_I.
Qed.

Theorem sKH_monot : forall s,
          (sKH_prv s) ->
          (forall Γ1, (Included _ (fst s) Γ1) ->
          (sKH_prv (Γ1, (snd s)))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros Γ1 incl. inversion H. subst. apply Ids. apply IdRule_I. simpl. apply incl.
  assumption.
(* Axs *)
- intros Γ1 incl. inversion H. subst. apply Axs. apply AxRule_I. assumption.
(* MPs *)
- intros Γ1 incl. inversion H1. subst. simpl. apply MPs with (ps:=[(Γ1, A --> B); (Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1 Γ1). apply s. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 Γ1). apply s. auto. inversion H4. apply MPRule_I.
(* sNec *)
- intros Γ1 incl. inversion H1. subst. simpl. apply sNec with (ps:=[(Γ1, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A) [(Γ, A)]). apply in_eq.
  pose (H0 (Γ, A) J1 Γ1). apply s. simpl. auto. inversion H3. apply sNecRule_I.
Qed.

Theorem wKH_comp : forall s,
          (wKH_prv s) ->
          (forall Γ,  (forall A, ((fst s) A) -> wKH_prv (Γ, A)) ->
          wKH_prv (Γ, (snd s))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros Γ derall. inversion H. subst. pose (derall A). apply w. auto.
(* Ax *)
- intros Γ derall. inversion H. subst. apply Ax. apply AxRule_I. assumption.
(* MP *)
- intros Γ derall. inversion H1. subst. apply MP with (ps:=[(Γ, A --> B); (Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A --> B) [(Γ0, A --> B); (Γ0, A)]). apply in_eq.
  pose (H0 (Γ0, A --> B) J1 Γ). apply w. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ0, A) [(Γ0, A --> B); (Γ0, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ0, A) J2 Γ). apply w. auto. inversion H4. apply MPRule_I.
(* wNec *)
- intros Γ derall. inversion H1. subst. simpl. apply wNec with (ps:=[(Empty_set _, A)]).
  intros. inversion H2. subst. auto. inversion H3. apply wNecRule_I.
Qed.

Theorem sKH_comp : forall s,
          (sKH_prv s) ->
          (forall Γ,  (forall A, ((fst s) A) -> sKH_prv (Γ, A)) ->
          sKH_prv (Γ, (snd s))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros Γ derall. inversion H. subst. pose (derall A). apply s. auto.
(* Axs *)
- intros Γ derall. inversion H. subst. apply Axs. apply AxRule_I. assumption.
(* MPs *)
- intros Γ derall. inversion H1. subst. apply MPs with (ps:=[(Γ, A --> B); (Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A --> B) [(Γ0, A --> B); (Γ0, A)]). apply in_eq.
  pose (H0 (Γ0, A --> B) J1 Γ). apply s. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ0, A) [(Γ0, A --> B); (Γ0, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ0, A) J2 Γ). apply s. auto. inversion H4. apply MPRule_I.
(* sNec *)
- intros Γ derall. inversion H1. subst. simpl. apply sNec with (ps:=[(Γ, A)]).
  intros. inversion H2. subst. assert (J1: List.In (Γ0, A) [(Γ0, A)]). apply in_eq.
  pose (H0 (Γ0, A) J1 Γ). apply s. simpl. auto. inversion H3. apply sNecRule_I.
Qed.

Theorem wKH_struct : forall s,
          (wKH_prv s) ->
          (forall (f : V -> MPropF),
          (wKH_prv ((fun y => (exists A, prod ((fst s) A) (y = (subst f A)))), (subst f (snd s))))).
Proof.
intros s D0. induction D0.
(* Id *)
- intros f. inversion H. subst. simpl. apply Id. apply IdRule_I.
  exists A. auto.
(* Ax *)
- intros f. inversion H. subst. apply Ax. apply AxRule_I. 
  apply subst_Ax with (f:=f). assumption.
(* MP *)
- intros f. inversion H1. subst. apply MP with (ps:=[((fun y : MPropF =>
  exists A0 : MPropF, prod (Γ A0) (y = subst f A0)), (subst f A) --> (subst f B)); ((fun y : MPropF =>
  exists A0 : MPropF, prod (Γ A0) (y = subst f A0)), (subst f A))]). simpl.
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1 f). apply w. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 f). apply w. auto. inversion H4. apply MPRule_I.
(* wNec *)
- intros f. inversion H1. subst. apply wNec with (ps:=[(Empty_set _, (subst f A))]).
  intros. inversion H2. subst. assert (J1: List.In (Empty_set MPropF, A) [(Empty_set MPropF, A)]). apply in_eq.
  pose (H0 (Empty_set MPropF, A) J1 f). simpl in w.
  assert ((fun y : MPropF => exists A : MPropF,
  prod (Empty_set _ A) (y = subst f A)) = Empty_set _).
  { apply Extensionality_Ensembles. split. intro. intro. inversion H3. destruct H4.
    inversion e. intro. intro. inversion H3. } rewrite H3 in w. apply w. simpl. auto.
  inversion H3. apply wNecRule_I.
Qed.

Theorem sKH_struct : forall s,
          (sKH_prv s) ->
          (forall (f : V -> MPropF),
          (sKH_prv ((fun y => (exists A, prod ((fst s) A) (y = (subst f A)))), (subst f (snd s))))).
Proof.
intros s D0. induction D0.
(* Ids *)
- intros f. inversion H. subst. simpl. apply Ids. apply IdRule_I.
  exists A. auto.
(* Axs *)
- intros f. inversion H. subst. apply Axs. apply AxRule_I.
  apply subst_Ax with (f:=f). assumption.
(* MPs *)
- intros f. inversion H1. subst. apply MPs with (ps:=[((fun y : MPropF =>
  exists A0 : MPropF, prod (Γ A0) (y = subst f A0)), (subst f A) --> (subst f B)); ((fun y : MPropF =>
  exists A0 : MPropF, prod (Γ A0) (y = subst f A0)), (subst f A))]). simpl.
  intros. inversion H2. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1 f). apply s. simpl. auto. inversion H3. subst.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2 f). apply s. auto. inversion H4. apply MPRule_I.
(* sNec *)
- intros f. inversion H1. subst. simpl. apply sNec with (ps:=[((fun y : MPropF => exists A0 : MPropF,
  (prod (Γ A0) (y = subst f A0))), (subst f A))]).
  intros. inversion H2. subst. assert (J1: List.In (Γ, A) [(Γ, A)]). apply in_eq.
  pose (H0 (Γ, A) J1 f). simpl in s. apply s. inversion H3. apply sNecRule_I.
Qed.

Theorem wKH_finite : forall s,
          (wKH_prv s) ->
          (exists (Γ : Ensemble _), prod (Included _ Γ (fst s))
                                     (prod (wKH_prv (Γ, snd s))
                                     (exists (l : list MPropF), (forall A, ((Γ A) -> List.In A l) * (List.In A l -> (Γ A)))))).
Proof.
intros s D0. induction D0.
(* Id *)
- inversion H. subst. simpl. exists (fun x => x = A).
  repeat split. intro. intro. unfold In. inversion H1. assumption.
  apply Id. apply IdRule_I. auto. unfold In. auto.
  exists [A]. intro. split. intro. subst. apply in_eq. intro. inversion H1.
  subst. auto. inversion H2.
(* Ax *)
- inversion H. subst. simpl. exists (Empty_set _).
  repeat split. intro. intro. unfold In. inversion H1.
  apply Ax. apply AxRule_I. auto.
  exists []. intro. split. intro. subst. inversion H1. intro. inversion H1.
(* MP *)
- inversion H1. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1). destruct e. destruct H2. destruct p. destruct e.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). destruct e. destruct H3. destruct p. destruct e.
  exists (Union _ x x1). repeat split. intro. intro. simpl. inversion H4.
  subst. apply i. assumption. apply i0. assumption. simpl.
  apply MP with (ps:=[(Union _ x x1, A --> B); (Union _ x x1, A)]).
  intros. inversion H4. subst.
  assert (J3: Included _ (fst (x, A --> B)) (Union _ x x1)). intro. simpl. intro.
  apply Union_introl. assumption. pose (@wKH_monot (x, A --> B) w (Union _ x x1) J3). assumption.
  inversion H5. subst. assert (J4: Included _ (fst (x1, A)) (Union _ x x1)). intro. simpl. intro.
  apply Union_intror. assumption. pose (@wKH_monot (x1, A) w0 (Union _ x x1) J4). assumption.
  inversion H6. apply MPRule_I.
  exists (x0 ++ x2). intro. split. intro. inversion H4. subst. pose (H2 A0).
  destruct p. apply in_or_app. apply i1 in H5. auto. subst. pose (H3 A0).
  destruct p. apply i1 in H5. apply in_or_app. auto. intro. apply in_app_or in H4.
  destruct H4. apply Union_introl. apply H2. assumption. apply Union_intror.
  apply H3. assumption.
(* wNec *)
- inversion H1. subst. exists (Empty_set _). repeat split.
  intro. intro. simpl. inversion H2. apply wNec with (ps:=[(Empty_set _, A)]).
  assumption. apply wNecRule_I. exists []. intro. split. intro. inversion H2.
  intro. inversion H2.
Qed.

Theorem sKH_finite : forall s,
          (sKH_prv s) ->
          (exists Γ, prod (Included _ Γ (fst s))
                                     (prod (sKH_prv (Γ, snd s))
                                     (exists l, (forall A, ((Γ A) -> List.In A l) * (List.In A l -> (Γ A)))))).
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
- inversion H1. subst. assert (J1: List.In (Γ, A --> B) [(Γ, A --> B); (Γ, A)]). apply in_eq.
  pose (H0 (Γ, A --> B) J1). destruct e. destruct H2. destruct p. destruct e.
  assert (J2: List.In (Γ, A) [(Γ, A --> B); (Γ, A)]). apply in_cons. apply in_eq.
  pose (H0 (Γ, A) J2). destruct e. destruct H3. destruct p. destruct e.
  exists (Union _ x x1). repeat split. intro. intro. simpl. inversion H4.
  subst. apply i. assumption. apply i0. assumption. simpl.
  apply MPs with (ps:=[(Union _ x x1, A --> B); (Union _ x x1, A)]).
  intros. inversion H4. subst.
  assert (J3: Included _ (fst (x, A --> B)) (Union _ x x1)). intro. simpl. intro.
  apply Union_introl. assumption. pose (@sKH_monot (x, A --> B) s (Union _ x x1) J3). assumption.
  inversion H5. subst. assert (J4: Included _ (fst (x1, A)) (Union _ x x1)). intro. simpl. intro.
  apply Union_intror. assumption. pose (@sKH_monot (x1, A) s0 (Union _ x x1) J4). assumption.
  inversion H6. apply MPRule_I.
  exists (x0 ++ x2). intro. split. intro. inversion H4. subst. pose (H2 A0).
  destruct p. apply in_or_app. apply i1 in H5. auto. subst. pose (H3 A0).
  destruct p. apply i1 in H5. apply in_or_app. auto. intro. apply in_app_or in H4.
  destruct H4. apply Union_introl. apply H2. assumption. apply Union_intror.
  apply H3. assumption.
(* sNec *)
- inversion H1. subst. assert (J1: List.In (Γ, A) [(Γ, A)]). apply in_eq.
  pose (H0 (Γ, A) J1). destruct e. destruct H2. destruct p. destruct e.
  exists x. repeat split. assumption.
  apply sNec with (ps:=[(x, A)]). intro. intro. simpl. inversion H3. subst.
  auto. inversion H4. apply sNecRule_I. exists x0. intro. split. intro. apply H2 ; assumption.
  intro. apply H2 ; assumption.
Qed.
