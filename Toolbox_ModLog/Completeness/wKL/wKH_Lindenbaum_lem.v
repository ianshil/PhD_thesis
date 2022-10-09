Require Import Classical.

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Ensembles.
Require Import K_Syntax.
Require Import K_GHC.
Require Import K_logics.
Require Import K_extens_interactions.
Require Import K_wKH_meta_interactions.
Require Import K_strong_induction.




(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Encoding of formulas. *)

Parameter encode0 : MPropF -> nat.

Hypothesis encode0_inj : forall A B, (encode0 A = encode0 B) -> A = B.

Definition encode : MPropF -> nat := fun x => S (encode0 x).

Lemma encode_no_0 : forall A, (encode A = 0) -> False.
Proof.
intros. unfold encode in H. lia.
Qed.

Lemma encode_inj : forall A B, (encode A = encode B) -> A = B.
Proof.
intros. unfold encode in H. inversion H.
apply encode0_inj  ; auto.
Qed.

Lemma decoding_inh :
  {g : nat -> option (MPropF) | (forall A, g (encode A) = Some A) /\
                                  (forall n, (((exists A, encode A = n) -> False) -> g n = None)) }.
Proof.
apply constructive_definite_description.
assert (H : forall n, exists! op,
  (forall A : MPropF, encode A = n -> op = Some A) /\
  (((exists A : MPropF, encode A = n) -> False) -> op = None)).
{ intro n.
  destruct (classic (exists A, encode A = n)).
  destruct H. exists (Some x). unfold unique. repeat split. intros.
  subst. simpl. apply encode_inj in H0. subst ; auto.
  intro. exfalso. apply H0. exists x. auto.
  intros. destruct H0. pose (H0 x). firstorder.
  exists None. unfold unique. repeat split. intros.
  exfalso. apply H. exists A. auto. intros. destruct H0. apply H1 in H.
  auto. }
exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
split.
- split.
  + intros A.
    destruct (constructive_definite_description _ _).
    simpl. destruct a. apply H0 ; auto.
  + intros n.
    now destruct (constructive_definite_description _ _).
- intros g' [H1 H2].
  apply functional_extensionality.
  intros n.
  destruct (constructive_definite_description _ _) as [x e].
  simpl. destruct e. destruct (classic (exists A, encode A = n)).
  + clear H3. destruct H4. subst. rewrite H1. apply H0 ; auto.
  + pose (H3 H4). rewrite e. pose (H2 n). symmetry. rewrite e0. auto.
     auto.
Qed.


Definition decoding : nat -> option (MPropF) := proj1_sig decoding_inh.

Lemma encode_decode_Id : forall A, decoding (encode A) = Some A.
Proof.
intro. unfold decoding. destruct decoding_inh. destruct a. auto.
Qed.



(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Random lemmas. *)

Lemma eq_dec_nat : forall (n m : nat), {n = m} + {n <> m}.
Proof.
induction n.
- destruct m.
  * auto.
  * auto.
- intro m. destruct m.
  * auto.
  * destruct IHn with (m:=m).
    + left. lia.
    + right. lia.
Qed.


(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* How we build the Lindenbaum extension. *)

Definition choice_form Γ A B : Ensemble (MPropF) :=
fun x => (In _ Γ x) \/
  (((wKH_prv (Union _ Γ (Singleton _ B), A) -> False) -> x = B) /\
  (wKH_prv (Union _ Γ (Singleton _ B), A) -> x = (B --> Bot))).

(* For any natural number, check if it is the encoding of a formula, then pick either the
    formula or its negation. *)

Definition choice_code Γ A n : Ensemble MPropF :=
match decoding n with
| None => Γ
| Some B => choice_form Γ A B
end.

Fixpoint Lindf (Γ : Ensemble MPropF) A (n : nat) : Ensemble MPropF :=
match n with
| 0 => Γ
| S m => choice_code (Lindf Γ A m) A (S m)
end.

Definition Lind Γ A : Ensemble MPropF := fun x => (exists n, In _ (Lindf Γ A n) x).


(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Properties of our Lind. *)




(* A Lindf is an extension of the initial set. *)

Lemma Lindf_extens : forall n Γ A x,
    In (MPropF) Γ x -> In _ (Lindf Γ A n) x.
Proof.
induction n.
- simpl. auto.
- simpl. intros. pose (IHn Γ A x H). unfold choice_code.
  destruct (decoding (S n)) ; auto.
  unfold In. unfold choice_form. auto.
Qed.

Lemma Lindf_extens_le : forall m n Γ A x,
    In _ (Lindf Γ A n) x -> (le n m) -> In _ (Lindf Γ A m) x.
Proof.
induction m.
- intros. simpl. inversion H0. subst. simpl in H. auto.
- intros. inversion H0 ; subst ; auto. simpl. unfold In.
  apply IHm in H ; auto. unfold choice_code.
  destruct (decoding (S m)) ; auto.
  unfold choice_form. unfold In. auto.
Qed.

Lemma Lind_extens : forall Γ A x,
    In (MPropF) Γ x -> In (MPropF) (Lind Γ A) x.
Proof.
intros. unfold Lind. unfold In. exists 0. auto.
Qed.

(* Each step of the construction preserves unprovability. *)

Lemma Unprv_Lindf : forall n Γ A, (wKH_prv (Γ, A) -> False) ->
  (wKH_prv (Lindf Γ A n, A) -> False).
Proof.
induction n ; intros.
- simpl in H0. auto.
- simpl in H0. apply IHn with (Γ:=Γ) (A:=A) ; auto. unfold choice_code in H0.
  destruct (decoding (S n)) ; auto.
  pose (IHn _ _ H).
  unfold choice_form in H0.
  destruct (classic (wKH_prv (Union MPropF (Lindf Γ A n) (Singleton MPropF m), A))).
  + assert (choice_form (Lindf Γ A n) A m =
     Union _ (Lindf Γ A n) (Singleton _ (m --> Bot))).
     { apply Extensionality_Ensembles. split ; intro ; intros.
        inversion H2. apply Union_introl ; auto. destruct H3.
        unfold choice_form in H3. pose (H4 H1). rewrite e.
        apply Union_intror ; apply In_singleton.
        unfold In. inversion H2 ; auto. subst. unfold choice_form ; auto. subst.
        inversion H3. subst.  unfold choice_form.
        right. split. intros. exfalso ; auto. auto. }
    unfold choice_form in H2. rewrite H2 in H0. clear H2.
    apply MP with (ps:=[(Lindf Γ A n, (m --> A) --> A);(Lindf Γ A n, m -->A)]).
    2: apply MPRule_I. intros. inversion H2. subst.
    apply MP with (ps:=[(Lindf Γ A n, ((m --> Bot) --> A) --> (m --> A) --> A);(Lindf Γ A n, (m --> Bot) --> A)]).
    2: apply MPRule_I. intros. inversion H3. subst.
    apply All_cases_LEM. inversion H4. subst. 2: inversion H5.
    apply wKH_Deduction_Theorem with
    (s:=(Union MPropF (Lindf Γ A n) (Singleton MPropF (m --> Bot)), A)) ; auto.
    inversion H3. 2: inversion H4. subst.
    apply wKH_Deduction_Theorem with
    (s:=(Union MPropF (Lindf Γ A n) (Singleton MPropF m), A)) ; auto.
  + assert (choice_form (Lindf Γ A n) A m =
     Union _ (Lindf Γ A n) (Singleton _ m)).
     { apply Extensionality_Ensembles. split ; intro ; intros.
        inversion H2. apply Union_introl ; auto. destruct H3.
        unfold choice_form in H3. pose (H3 H1). rewrite e.
        apply Union_intror ; apply In_singleton.
        unfold In. inversion H2 ; auto. subst. unfold choice_form. auto.
        subst. inversion H3 ; subst. right. split. auto. intros. exfalso ; auto. }
    unfold choice_form in H2. rewrite H2 in H0. clear H2. exfalso. apply H1. auto.
Qed.

(* A Lindf extension preserves deducibility. *)

Lemma der_Lindf_m_Lindf_le : forall n m Γ A B,
  (wKH_prv (Lindf Γ A n, B)) -> (le n m) ->
    (wKH_prv (Lindf Γ A m, B)).
Proof.
intros.
pose (wKH_monot (Lindf Γ A n, B) H (Lindf Γ A m)).
simpl in w. apply w. intro. intros. apply Lindf_extens_le with (n:=n) ; auto.
Qed.

Lemma der_Lindf_Lindf : forall s, (wKH_prv s) ->
 (forall Γ A B, (Lind Γ A = fst s) ->
                      (B = snd s) ->
                      (exists n, (wKH_prv (Lindf Γ A n, B)))).
Proof.
intros s D. induction D ; intros.
- inversion H. subst. simpl in H0. subst. simpl. unfold Lind in H2. destruct H2.
  exists x. apply Id. apply IdRule_I. auto.
- inversion H. subst. simpl in H0. subst. simpl. exists 0. apply Ax. apply AxRule_I.
  auto.
- inversion H1. subst. simpl in H2. subst.
  assert (J1: List.In (Lind Γ A, A0 --> B0) [(Lind Γ A, A0 --> B0); (Lind Γ A, A0)]).
  apply in_eq. pose (H (Lind Γ A, A0 --> B0) J1).
  assert (J2: List.In (Lind Γ A, A0) [(Lind Γ A, A0 --> B0); (Lind Γ A, A0)]).
  apply in_cons. apply in_eq. pose (H (Lind Γ A, A0) J2).
  assert (J3: Lind Γ A = Lind Γ A). auto.
  assert (J4: A0 --> B0 = A0 --> B0). auto.
  pose (H0 (Lind Γ A, A0 --> B0) J1 Γ A (A0 --> B0) J3 J4). destruct e. clear J4.
  clear w. clear J1.
  assert (J5: A0 = A0). auto.
  pose (H0 (Lind Γ A, A0) J2 Γ A A0 J3 J5). destruct e. clear J5.
  clear J3. clear w0. clear J2.
  exists (max x x0). simpl.
  apply MP with (ps:=[(Lindf Γ A (Init.Nat.max x x0), A0 --> B0);(Lindf Γ A (Init.Nat.max x x0), A0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  pose (der_Lindf_m_Lindf_le x (Init.Nat.max x x0) _ _ _ H2). apply w.
  lia. inversion H5. 2: inversion H6. subst. clear H4. clear H5.
  pose (der_Lindf_m_Lindf_le x0 (Init.Nat.max x x0) _ _ _ H3). apply w. lia.
- subst. inversion H1. subst. simpl in H2. subst.
  assert (J1: List.In (Empty_set (MPropF), A0) [(Empty_set (MPropF), A0)]). apply in_eq.
  pose (H (Empty_set (MPropF), A0) J1). simpl. exists 0. apply wNec with (ps:=[(Empty_set (MPropF), A0)]).
  2: apply wNecRule_I. intros. inversion H2. subst. auto. inversion H3.
Qed.

(* A Lind extension is unprovable *)

Lemma Unprv_Lind : forall Γ A, (wKH_prv (Γ, A) -> False) ->
  (wKH_prv (Lind Γ A , A) -> False).
Proof.
intros.
assert (J1: Lind Γ A = Lind Γ A). auto.
assert (J2: A = A). auto.
pose (der_Lindf_Lindf (Lind Γ A, A) H0 Γ A A J1 J2). destruct e.
pose (Unprv_Lindf x Γ A H H1). auto.
Qed.

(* A Lind extension is maximal. *)

Lemma maximality_Lind_extens : forall Γ A, (wKH_prv (Γ, A) -> False) ->
  (forall B, (In _ (Lind Γ A) B) \/ (In _ (Lind Γ A) (B --> Bot))).
Proof.
intros.
assert (In MPropF (Lindf Γ A (encode B)) B \/ In MPropF (Lindf Γ A (encode B)) (B --> Bot)).
  { simpl. unfold choice_code. remember (decoding (S (encode0 B))) as k.
    pose (encode_decode_Id B) ; auto. unfold encode in e.
    rewrite e in Heqk. subst.
    assert (J1: wKH_prv (Lindf Γ A (encode0 B), A) -> False).
    apply Unprv_Lindf ; auto. unfold choice_form. simpl.
    destruct (classic (wKH_prv (Union MPropF (Lindf Γ A (encode0 B)) (Singleton MPropF B), A))).
    + right. unfold In. right. split ; intros. exfalso. auto. auto.
    + left. unfold In. right. split ; intros ; auto. exfalso ; auto. }
destruct H0. left. exists (encode B). auto. right. exists (encode B). auto.
Qed.


(* A Lind extension is closed under derivation. *)

Lemma closeder_Lind_extens : forall Γ A, (wKH_prv (Γ, A) -> False) ->
  (forall B, wKH_prv (Lind Γ A, B) -> (In _ (Lind Γ A) B)).
Proof.
intros. destruct (maximality_Lind_extens _ _ H B) ; auto.
exfalso. apply Unprv_Lind with (Γ:=Γ) (A:=A) ; auto.
apply MP with (ps:=[(Lind Γ A, Bot --> A);(Lind Γ A, Bot)]).
2: apply MPRule_I. intros. inversion H2. subst. apply Ax.
apply AxRule_I. apply MA4_I. exists A. auto. inversion H3.
subst. 2: inversion H4.
apply MP with (ps:=[(Lind Γ A, B --> Bot);(Lind Γ A, B)]).
2: apply MPRule_I. intros. inversion H4 ; subst ; auto.
apply Id. apply IdRule_I. auto. inversion H5. subst. 2: inversion H6.
auto.
Qed.

(* A Lind extension is consistent. *)

Lemma Consist_Lindf : forall n Γ A, (wKH_prv (Γ, A) -> False) ->
  (wKH_prv (Lindf Γ A n, Bot) -> False).
Proof.
intros. pose (Unprv_Lindf n Γ A H). apply f.
apply MP with (ps:=[(Lindf Γ A n, Bot --> A);(Lindf Γ A n, Bot)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply MA4_I. exists A. auto.
inversion H2. 2: inversion H3. subst. auto.
Qed.

Lemma Consist_Lind : forall Γ A, (wKH_prv (Γ, A) -> False) ->
  (wKH_prv (Lind Γ A, Bot) -> False).
Proof.
intros. apply closeder_Lind_extens in H0 ; auto. unfold Lind in H0.
unfold In in H0. destruct H0. apply Consist_Lindf with (Γ:=Γ) (A:=A) (n:=x) ; auto.
apply Id. apply IdRule_I. auto.
Qed.

Lemma Consist_Lindf0 : forall Γ A, (wKH_prv (Γ, A) -> False) ->
  (wKH_prv (Lind Γ A, Bot) -> False).
Proof.
intros. apply Unprv_Lind in H ; auto.
apply MP with (ps:=[(Lind Γ A, Bot --> A);(Lind Γ A, Bot)]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
apply AxRule_I. apply MA4_I. exists A. auto. inversion H2.
2: inversion H3. subst. auto.
Qed.

Lemma Lindenbaum_lemma : forall Γ A,
    (wKH_prv (Γ, A) -> False) ->
    (exists Γm, Included _ Γ Γm /\
                   (forall B, (Γm B) \/ (Γm (B --> Bot))) /\
                   (wKH_prv (Γm, A) -> False)).
Proof.
intros Γ A notder.
exists (Lind Γ A). repeat split.
- intro. apply Lind_extens.
- intro. apply maximality_Lind_extens ; auto.
- apply Unprv_Lind ; auto.
Qed.





