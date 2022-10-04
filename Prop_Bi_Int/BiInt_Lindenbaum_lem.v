Require Import Classical.
(* Used in various places:
    - existence of a derivation in the axiomatic system for a sequent
      (should be decidable as Bi-Int is, but this would require extra work)
    - existence of a formula for which a number is an encoding (if I write
      down the function I might be able to extract it)
    - some set-theoretic arguments (maybe they can be constructivised) *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Ensembles.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import BiInt_extens_interactions.
Require Import wBIH_meta_interactions.
Require Import BiInt_remove_list.




(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Encoding of formulas. *)

Parameter encode0 : BPropF V -> nat.

Hypothesis encode0_inj : forall A B n, (encode0 A = n) -> (encode0 B = n) -> A = B.

Definition encode : BPropF V -> nat := fun x => S (encode0 x).

Lemma encode_no_0 : forall A, (encode A = 0) -> False.
Proof.
intros. unfold encode in H. lia.
Qed.

Lemma encode_inj : forall A B n, (encode A = n) -> (encode B = n) -> A = B.
Proof.
intros. unfold encode in H. unfold encode in H0.
destruct n. exfalso. lia. inversion H. inversion H0. subst.
apply encode0_inj with (n:=encode0 A) ; auto.
Qed.

Lemma decoding_inh :
  {g : nat -> option (BPropF V) | (forall A, g (encode A) = Some A) /\
                                  (forall n, (forall (E : {A : _ | encode A = n}), (g n = Some (proj1_sig E))) /\
                                             (((exists A, encode A = n) -> False) -> g n = None)) }.
Proof.
apply constructive_definite_description.
assert (H : forall n, exists! op, (forall E : {A : BPropF V | encode A = n},
    op = Some (proj1_sig E)) /\ (((exists A : BPropF V, encode A = n) -> False) ->
    op = None)).
{ intro n. 
  destruct (classic (exists A, encode A = n)).
  destruct H. exists (Some x). unfold unique. repeat split. intros.
  subst. simpl. destruct E. simpl. pose (encode_inj x x0 (encode x)).
  assert (encode x = encode x). auto. pose (e0 H). pose (e1 e). rewrite e2. auto.
  intro. exfalso. apply H0. exists x. auto. intros. destruct H0.
  assert ({A : BPropF V | encode A = n}). exists x. auto. pose (H0 H2).
  destruct H2. simpl in e. rewrite <- e0 in H. pose (encode_inj x x0 (encode x)).
  assert (encode x = encode x). auto. pose (e1 H2). symmetry in H. pose (e2 H).
  rewrite <- e3 in e. auto. exists None. unfold unique. repeat split. intros.
  exfalso. apply H. destruct E. exists x. auto. intros. destruct H0. apply H1 in H.
  auto. }
exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
split.
- split.
  + intros A.
    destruct (constructive_definite_description _ _).
    simpl. destruct a. assert ({A0 : BPropF V | encode A0 = encode A}). exists A. auto.
    pose (H0 H2). destruct H2. simpl in e. pose (encode_inj x0 A (encode x0)).
    assert (encode x0 = encode x0). auto. pose (e1 H2). assert (encode x0 = encode A).
    auto. symmetry in H3. pose (e2 H3). rewrite <- e3. auto.
  + intros n.
    now destruct (constructive_definite_description _ _).
- intros g' [H1 H2].
  apply functional_extensionality.
  intros n.
  destruct (constructive_definite_description _ _) as [x e].
  simpl. destruct e. destruct (classic (exists A, encode A = n)).
  + clear H3. destruct H4. assert ({A : BPropF V | encode A = n}). exists x0. auto.
    pose (H0 H4). pose (H2 n). destruct a. pose (H5 H4). destruct H4. simpl in e0.
    simpl in e. rewrite e. rewrite e0. auto.
  + pose (H3 H4). rewrite e. pose (H2 n). destruct a. pose (H6 H4). rewrite e0. auto.
Qed.

Definition decoding : nat -> option (BPropF V) := proj1_sig decoding_inh.

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

Lemma nat_remove_le_length : forall l (n : nat), length (remove eq_dec_nat n l) <= length l.
Proof.
induction l.
- intros. simpl. reflexivity.
- intros. simpl. destruct (eq_dec_nat n a).
  * subst. apply le_S. apply IHl.
  * simpl. apply le_n_S. apply IHl.
Qed.

Lemma nat_remove_In_smaller_length : forall (l : list nat) (n : nat),
       List.In n l -> length (remove eq_dec_nat n l) < length l.
Proof.
induction l.
- intros. inversion H.
- intros. simpl. destruct (eq_dec_nat n a).
  * subst. unfold lt. apply le_n_S. apply nat_remove_le_length.
  * simpl. apply Lt.lt_n_S. apply IHl. inversion H. subst. exfalso. apply n0. auto.
    assumption.
Qed.

Lemma max_of_list : forall (l : list nat), ((l = []) -> False) -> (exists n, (List.In n l) /\
            (forall m, List.In m l -> m <= n)).
Proof.
induction l.
- simpl. intros. exfalso. apply H. auto.
- intros. destruct l.
  * exists a. split. apply in_eq. intros. inversion H0. subst. auto. inversion H1.
  * assert (n :: l = [] -> False). intro. inversion H0. apply IHl in H0.
    destruct H0. destruct H0. inversion H0.
    + subst. exists (Nat.max a x). split. pose (Nat.max_dec a x).
      destruct s. rewrite e. apply in_eq. rewrite e. apply in_cons. apply in_eq.
      intros. inversion H2. lia. pose (H1 m). apply l0 in H3. lia.
    + exists (Nat.max a x). split. pose (Nat.max_dec a x).
      destruct s. rewrite e. apply in_eq. rewrite e. apply in_cons. apply in_cons. auto.
      intros. inversion H3. lia. pose (H1 m). apply l0 in H4. lia.
Qed.

Lemma always_add_a_nat : forall (l : list nat), (NoDup l) -> (exists n, (NoDup (n :: l))).
Proof.
intros. destruct l.
- exists 0. apply NoDup_cons ; auto ; apply NoDup_nil.
- assert (J1: (n :: l = [] -> False) ). intro. inversion H0.
  pose (max_of_list (n :: l) J1). destruct e. destruct H0. exists (S x).
  apply NoDup_cons. intro. apply H1 in H2. lia. auto.
Qed.

Lemma no_list_all_nat : (exists (l : list nat), (NoDup l) /\ (forall (n : nat), List.In n l)) -> False.
Proof.
intros. destruct H. destruct H. pose (always_add_a_nat x H). destruct e.
assert (incl (x0 :: x) x). intro. intros. inversion H2. subst. pose (H0 a). auto.
auto. pose (@NoDup_incl_length nat (x0 :: x) x H1 H2). simpl in l. lia.
Qed.

Lemma list_all_pred_nat : forall n, exists l, (NoDup l) /\ (forall m, (m <= n) <-> List.In m l).
Proof.
induction n. exists [0]. split. apply NoDup_cons ; auto ; apply NoDup_nil.
intros. split ; intro. inversion H. subst. apply in_eq.
inversion H. subst. auto. inversion H0. destruct IHn. destruct H. exists ((S n) :: x).
intros. split. apply NoDup_cons. intro. apply H0 in H1. lia. auto.
split ; intros. inversion H1. subst. apply in_eq. subst. apply in_cons.
apply H0. auto. inversion H1. subst. auto. apply H0 in H2. lia.
Qed.


(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Multiple disjunctions lemmas. *)

Fixpoint mult_disj (n : nat) (A : BPropF V) : BPropF V :=
match n with
  | 0 => A
  | S m => Or A (mult_disj m A)
  end.

Lemma der_mult_disj_Bot : forall n Γ A,
  wBIH_rules (Γ, Or A (mult_disj n (Bot V))) -> wBIH_rules (Γ, A).
Proof.
induction n.
- simpl. intros. apply absorp_Or1. auto.
- simpl. intros.
  apply MP with (ps:=[(Γ, Imp (Or A (Or (Bot V) (mult_disj n (Bot V)))) A);(Γ, Or A (Or (Bot V) (mult_disj n (Bot V))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, ((Or (Bot V) (mult_disj n (Bot V))) → A) → (Or A (Or (Bot V) (mult_disj n (Bot V))) → A));(Γ, ((Or (Bot V) (mult_disj n (Bot V))) → A))]).
  2: apply MPRule_I. intros. inversion H1. subst.
  apply MP with (ps:=[(Γ, (A → A) → ((Or (Bot V) (mult_disj n (Bot V))) → A) → (Or A (Or (Bot V) (mult_disj n (Bot V))) → A));(Γ, A → A)]).
  2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
  apply RA4_I. exists A. exists (Or (Bot V) (mult_disj n (Bot V))). exists A. auto.
  inversion H3. 2: inversion H4. subst. apply wimp_Id_gen. inversion H2. 2: inversion H3.
  subst.
  apply MP with (ps:=[(Γ, ((Bot V) → A) → (Or (Bot V) (mult_disj n (Bot V)) → A));
  (Γ, (Bot V) → A)]). 2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(Γ, (Or (Bot V) (mult_disj n (Bot V)) → (Bot V)) → ((Bot V) → A) → (Or (Bot V) (mult_disj n (Bot V)) → A));
  (Γ, Or (Bot V) (mult_disj n (Bot V)) → (Bot V))]). 2: apply MPRule_I. intros. inversion H4. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (Or (Bot V) (mult_disj n (Bot V))).
  exists (Bot V). exists A. auto. inversion H5. 2: inversion H6. subst.
  clear H4. clear H5. clear H3. clear H1. clear H2. clear H0.
  apply wBIH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (Or (Bot V) (mult_disj n (Bot V)))), Bot V)) ; auto.
  apply IHn. apply Id. apply IdRule_I. apply Union_intror. apply In_singleton.
  inversion H4. 2: inversion H5. subst. apply wEFQ.
  inversion H1. 2: inversion H2. subst. auto.
Qed.

Lemma mult_disj_Id : forall x y, (mult_disj x (Bot V) = mult_disj y (Bot V)) -> x = y.
Proof.
induction x.
- intros. simpl in H. destruct y. auto. simpl in H. destruct y. simpl in H. inversion H.
  inversion H.
- induction y.
  * intros. simpl in H. inversion H.
  * intros. simpl in H. inversion H. apply IHx in H1. auto.
Qed.

Lemma too_many_disj00 : forall (n : nat) A B,
((exists (m k : nat), (m <= n) /\ (decoding m = Some (Or A (Or B (mult_disj k (Bot V)))))) -> False)
\/
  (exists (m max : nat), (decoding m = Some (Or A (Or B (mult_disj max (Bot V)))) /\ (m <= n))
  /\
  (forall (o p : nat), ((decoding p = Some (Or A (Or B (mult_disj o (Bot V)))) /\ (p <= n)) ->
        o <= max))).
Proof.
induction n.
- intros. remember (decoding 0) as u. destruct u.
  + destruct (classic (exists g, b = (Or A (Or B (mult_disj g (Bot V)))))).
    * destruct H. right. exists 0. exists x. repeat split ; auto.
      subst. auto. intros. destruct H0. inversion H1. subst. clear H1.
      rewrite H0 in Hequ. inversion Hequ. apply mult_disj_Id in H1. lia.
    * left. intro. destruct H0. destruct H0. destruct H0. inversion H0. subst.
      apply H. exists x0. rewrite <- Hequ in H1. inversion H1. auto.
  + left. intro. destruct H. destruct H. destruct H. inversion H. subst.
    rewrite <- Hequ in H0. inversion H0.
- intros. remember (decoding (S n)) as u. destruct u.
  + destruct (classic (exists g, b = (Or A (Or B (mult_disj g (Bot V)))))).
    * destruct H. subst. right. pose (IHn A B). destruct o.
      { clear IHn. exists (S n). exists x. repeat split ; auto.
        intros. destruct H0. inversion H1. subst. rewrite <- Hequ in H0.
        inversion H0. apply mult_disj_Id in H3. lia. subst. exfalso.
        apply H. exists p. exists o. split ; auto. }
      { clear IHn. destruct H. destruct H. destruct H. destruct H.
        pose (Nat.max_dec x1 x). destruct s.
        - exists x0. exists x1. repeat split ; auto. intros. destruct H2.
          inversion H3. subst. rewrite <- Hequ in H2. inversion H2. subst.
          apply mult_disj_Id in H5. lia. subst. apply H0 with (p:=p).
          split ; auto.
        - exists (S n). exists x. repeat split ; auto. intros. destruct H2.
          inversion H3. subst. rewrite <- Hequ in H2. inversion H2.
          apply mult_disj_Id in H5. lia. subst. pose (H0 o p). destruct l.
          split ; auto. lia. lia. }
    * pose (IHn A B). destruct o.
      { left. intro. clear IHn. destruct H1. destruct H1. destruct H1. subst.
        inversion H1. subst. rewrite <- Hequ in H2. inversion H2. apply H.
        exists x0. auto. subst. apply H0. exists x. exists x0. split ; auto. }
      { right. clear IHn. destruct H0. destruct H0. destruct H0. destruct H0.
        exists x. exists x0. repeat split ; auto. intros. destruct H3. inversion H4.
        subst. rewrite <- Hequ in H3. inversion H3. exfalso. apply H. exists o ; auto.
        subst. apply H1 with (p:=p). split ; auto. }
  + pose (IHn A B). destruct o.
    * clear IHn. left. intro. destruct H0. destruct H0. destruct H0. subst.
      inversion H0. subst. rewrite <- Hequ in H1. inversion H1.
      subst. apply H. exists x. exists x0. split ; auto.
    * clear IHn. destruct H. destruct H. destruct H. destruct H.
      right. exists x. exists x0. repeat split ; auto.
      intros. destruct H2. inversion H3. subst. rewrite <- Hequ in H2.
      inversion H2. subst. apply H0 with (p:=p). auto.
Qed.

Lemma too_many_disj0 : forall (n : nat) A B,
 (exists (m k : nat), (decoding (S m) = Some (Or A (Or B (mult_disj k (Bot V)))) /\ (n <= m))).
Proof.
intros.
pose (too_many_disj00 n A B). destruct o.
- exists (pred (encode (Or A (Or B (mult_disj 0 (Bot V)))))). exists 0.
  split.
  assert ((S (Init.Nat.pred (encode (Or A (Or B (Bot V)))))) =
  encode (Or A (Or B (Bot V)))). remember (encode (Or A (Or B (Bot V)))) as u. destruct u.
  exfalso. apply encode_no_0 with (A:=(Or A (Or B (mult_disj 0 (Bot V))))). auto.
  auto. simpl (mult_disj 0 (Bot V)). rewrite H0. apply encode_decode_Id.
  destruct (Nat.le_decidable n (Init.Nat.pred (encode (Or A (Or B (Bot V)))))) ; auto.
  exfalso. assert (Init.Nat.pred (encode (Or A (Or B (Bot V)))) < n). lia.
  apply H. exists (encode (Or A (Or B (Bot V)))). exists 0. simpl.
  split ; auto. apply encode_decode_Id.
- destruct H. destruct H. destruct H. destruct H.
  exists (Init.Nat.pred (encode (Or A (Or B (mult_disj (S x0) (Bot V)))))).
  exists (S x0). split.
  assert ((S (Init.Nat.pred (encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V)))))))) =
  (encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V))))))).
  remember (encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V)))))) as u. destruct u ; auto.
  symmetry in Hequ. apply encode_no_0 in Hequ. inversion Hequ.
  simpl (mult_disj (S x0) (Bot V)). rewrite H2. apply encode_decode_Id.
  destruct (Nat.le_decidable n (Init.Nat.pred (encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V)))))))) ; auto.
  assert ((encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V)))))) <= n). lia.
  clear H2. pose (H0 (S x0) (encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V))))))).
  assert (decoding (encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V)))))) = Some (Or A (Or B (mult_disj (S x0) (Bot V)))) /\
  encode (Or A (Or B (Or (Bot V) (mult_disj x0 (Bot V))))) <= n). split.
  simpl. apply encode_decode_Id. lia. apply l in H2. exfalso. lia.
Qed.

Lemma too_many_disj10 :forall (n : nat) A,
((exists (m k : nat), (m <= n) /\ (decoding m = Some (Or A (mult_disj k (Bot V))))) -> False)
\/
  (exists (m max : nat), (decoding m = Some (Or A (mult_disj max (Bot V))) /\ (m <= n))
  /\
  (forall (o p : nat), ((decoding p = Some (Or A (mult_disj o (Bot V))) /\ (p <= n)) ->
        o <= max))).
Proof.
induction n.
- intros. remember (decoding 0) as u. destruct u.
  + destruct (classic (exists g, b = (Or A (mult_disj g (Bot V))))).
    * destruct H. right. exists 0. exists x. repeat split ; auto.
      subst. auto. intros. destruct H0. inversion H1. subst. clear H1.
      rewrite H0 in Hequ. inversion Hequ. apply mult_disj_Id in H1. lia.
    * left. intro. destruct H0. destruct H0. destruct H0. inversion H0. subst.
      apply H. exists x0. rewrite <- Hequ in H1. inversion H1. auto.
  + left. intro. destruct H. destruct H. destruct H. inversion H. subst.
    rewrite <- Hequ in H0. inversion H0.
- intros. remember (decoding (S n)) as u. destruct u.
  + destruct (classic (exists g, b = (Or A (mult_disj g (Bot V))))).
    * destruct H. subst. right. pose (IHn A). destruct o.
      { clear IHn. exists (S n). exists x. repeat split ; auto.
        intros. destruct H0. inversion H1. subst. rewrite <- Hequ in H0.
        inversion H0. apply mult_disj_Id in H3. lia. subst. exfalso.
        apply H. exists p. exists o. split ; auto. }
      { clear IHn. destruct H. destruct H. destruct H. destruct H.
        pose (Nat.max_dec x1 x). destruct s.
        - exists x0. exists x1. repeat split ; auto. intros. destruct H2.
          inversion H3. subst. rewrite <- Hequ in H2. inversion H2. subst.
          apply mult_disj_Id in H5. lia. subst. apply H0 with (p:=p).
          split ; auto.
        - exists (S n). exists x. repeat split ; auto. intros. destruct H2.
          inversion H3. subst. rewrite <- Hequ in H2. inversion H2.
          apply mult_disj_Id in H5. lia. subst. pose (H0 o p). destruct l.
          split ; auto. lia. lia. }
    * pose (IHn A). destruct o.
      { left. intro. clear IHn. destruct H1. destruct H1. destruct H1. subst.
        inversion H1. subst. rewrite <- Hequ in H2. inversion H2. apply H.
        exists x0. auto. subst. apply H0. exists x. exists x0. split ; auto. }
      { right. clear IHn. destruct H0. destruct H0. destruct H0. destruct H0.
        exists x. exists x0. repeat split ; auto. intros. destruct H3. inversion H4.
        subst. rewrite <- Hequ in H3. inversion H3. exfalso. apply H. exists o ; auto.
        subst. apply H1 with (p:=p). split ; auto. }
  + pose (IHn A). destruct o.
    * clear IHn. left. intro. destruct H0. destruct H0. destruct H0. subst.
      inversion H0. subst. rewrite <- Hequ in H1. inversion H1.
      subst. apply H. exists x. exists x0. split ; auto.
    * clear IHn. destruct H. destruct H. destruct H. destruct H.
      right. exists x. exists x0. repeat split ; auto.
      intros. destruct H2. inversion H3. subst. rewrite <- Hequ in H2.
      inversion H2. subst. apply H0 with (p:=p). auto.
Qed.

Lemma too_many_disj1 : forall (n : nat) A,
 (exists (m k : nat), (decoding (S m) = Some (Or A (mult_disj k (Bot V))) /\ (n <= m))).
Proof.
intros.
pose (too_many_disj10 n A). destruct o.
- exists (pred (encode (Or A (mult_disj 0 (Bot V))))). exists 0.
  split.
  assert ((S (Init.Nat.pred (encode (Or A (Bot V))))) =
  encode (Or A (Bot V))). remember (encode (Or A (Bot V))) as u. destruct u.
  exfalso. apply encode_no_0 with (A:=(Or A (mult_disj 0 (Bot V)))). auto.
  auto. simpl ((mult_disj 0 (Bot V))). rewrite H0. apply encode_decode_Id.
  destruct (Nat.le_decidable n (Init.Nat.pred (encode (Or A (Bot V))))) ; auto.
  exfalso. assert (Init.Nat.pred (encode (Or A (Bot V))) < n). lia.
  apply H. exists (encode (Or A (Bot V))). exists 0. simpl.
  split ; auto. apply encode_decode_Id.
- destruct H. destruct H. destruct H. destruct H.
  exists (Init.Nat.pred (encode (Or A (mult_disj (S x0) (Bot V))))).
  exists (S x0). split.
  assert ((S (Init.Nat.pred (encode (Or A (Or (Bot V) (mult_disj x0 (Bot V))))))) =
  (encode (Or A (Or (Bot V) (mult_disj x0 (Bot V)))))).
  remember (encode (Or A (Or (Bot V) (mult_disj x0 (Bot V))))) as u. destruct u ; auto.
  symmetry in Hequ. apply encode_no_0 in Hequ. inversion Hequ.
  simpl (mult_disj (S x0) (Bot V)). rewrite H2. apply encode_decode_Id.
  destruct (Nat.le_decidable n (Init.Nat.pred (encode (Or A (Or (Bot V) (mult_disj x0 (Bot V))))))) ; auto.
  assert ((encode (Or A (Or (Bot V) (mult_disj x0 (Bot V))))) <= n). lia.
  clear H2. pose (H0 (S x0) (encode (Or A (Or (Bot V) (mult_disj x0 (Bot V)))))).
  assert (decoding (encode (Or A (Or (Bot V) (mult_disj x0 (Bot V))))) = Some (Or A (mult_disj (S x0) (Bot V))) /\
  encode (Or A (Or (Bot V) (mult_disj x0 (Bot V)))) <= n). split.
  simpl. apply encode_decode_Id. lia. apply l in H2. exfalso. lia.
Qed.





(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* List of disjunctions. *)

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
  apply MP with (ps:=[(Γ, ((list_disj l1) → Or (Bot V) (list_disj l1)) → (A → Or (Bot V) (list_disj l1)));(Γ, (list_disj l1) → Or (Bot V) (list_disj l1))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → (list_disj l1)) → ((list_disj l1) → Or (Bot V) (list_disj l1)) → (A → Or (Bot V) (list_disj l1)));(Γ,A → (list_disj l1))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists (list_disj l1). exists (Or (Bot V) (list_disj l1)). auto. inversion H2.
  2: inversion H3. subst. assumption. inversion H1. 2: inversion H2. subst. apply Ax.
  apply AxRule_I. apply RA3_I. exists (Bot V). exists (list_disj l1). auto.
- simpl. intros.
  apply MP with (ps:=[(Γ, (Or a (list_disj (l0 ++ l1)) → Or (Or a (list_disj l0)) (list_disj l1)) → (A → Or (Or a (list_disj l0)) (list_disj l1)));
  (Γ,  (Or a (list_disj (l0 ++ l1)) → Or (Or a (list_disj l0)) (list_disj l1)))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → Or a (list_disj (l0 ++ l1))) → (Or a (list_disj (l0 ++ l1)) → Or (Or a (list_disj l0)) (list_disj l1)) → (A → Or (Or a (list_disj l0)) (list_disj l1)));
  (Γ,  A → Or a (list_disj (l0 ++ l1)))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists (Or a (list_disj (l0 ++ l1))). exists (Or (Or a (list_disj l0)) (list_disj l1)).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst.
  apply MP with (ps:=[(Γ, (Or a (Or (list_disj l0) (list_disj l1)) → Or (Or a (list_disj l0)) (list_disj l1)) → (Or a (list_disj (l0 ++ l1)) → Or (Or a (list_disj l0)) (list_disj l1)));
  (Γ, (Or a (Or (list_disj l0) (list_disj l1)) → Or (Or a (list_disj l0)) (list_disj l1)))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (Or a (list_disj (l0 ++ l1)) → Or a (Or (list_disj l0) (list_disj l1))) → (Or a (Or (list_disj l0) (list_disj l1)) → Or (Or a (list_disj l0)) (list_disj l1)) → (Or a (list_disj (l0 ++ l1)) → Or (Or a (list_disj l0)) (list_disj l1)));
  (Γ, (Or a (list_disj (l0 ++ l1)) → Or a (Or (list_disj l0) (list_disj l1))))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists (Or a (list_disj (l0 ++ l1))). exists (Or a (Or (list_disj l0) (list_disj l1))).
  exists (Or (Or a (list_disj l0)) (list_disj l1)). auto. inversion H4. 2: inversion H5.
  subst. apply wmonotL_Or. apply IHl0. apply wimp_Id_gen. inversion H3. 2: inversion H4. subst.
  remember (list_disj l0) as E. remember (list_disj l1) as F.
  apply MP with (ps:=[(Γ, ((Or E F) → Or (Or a E) F) → (Or a (Or E F) → Or (Or a E) F));
  (Γ, ((Or E F) → Or (Or a E) F))]). 2: apply MPRule_I. intros. inversion H4. rewrite <- H5.
  apply MP with (ps:=[(Γ, (a → Or (Or a E) F) → ((Or E F) → Or (Or a E) F) → (Or a (Or E F) → Or (Or a E) F));
  (Γ, (a → Or (Or a E) F))]). 2: apply MPRule_I. intros. inversion H6. rewrite <- H7.
  apply Ax. apply AxRule_I. apply RA4_I. exists a. exists (Or E F). exists (Or (Or a E) F).
  auto. inversion H7. 2: inversion H8. rewrite <- H8.
  apply MP with (ps:=[(Γ, ((Or a E) → Or (Or a E) F) → (a → Or (Or a E) F));(Γ, ((Or a E) → Or (Or a E) F))]).
  2: apply MPRule_I. intros. inversion H9. rewrite <- H10.
  apply MP with (ps:=[(Γ, (a → (Or a E)) → ((Or a E) → Or (Or a E) F) → (a → Or (Or a E) F));(Γ, a → (Or a E))]).
  2: apply MPRule_I. intros. inversion H11. rewrite <- H12. apply Ax. apply AxRule_I.
  apply RA1_I. exists a. exists (Or a E). exists (Or (Or a E) F). auto.
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
  apply MP with (ps:=[(Γ, (Or (Bot V) (list_disj l1) → list_disj l1) → (A → list_disj l1));
  (Γ, Or (Bot V) (list_disj l1) → list_disj l1)]). 2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → Or (Bot V) (list_disj l1)) → (Or (Bot V) (list_disj l1) → list_disj l1) → (A → list_disj l1));
  (Γ, A → Or (Bot V) (list_disj l1))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (Or (Bot V) (list_disj l1)).
  exists (list_disj l1). auto. inversion H2. 2: inversion H3. subst. auto. inversion H1.
  2: inversion H2. subst.
  apply MP with (ps:=[(Γ, ((list_disj l1) → list_disj l1) → (Or (Bot V) (list_disj l1) → list_disj l1));
  (Γ, (list_disj l1) → list_disj l1)]). 2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (Bot V → list_disj l1) → ((list_disj l1) → list_disj l1) → (Or (Bot V) (list_disj l1) → list_disj l1));
  (Γ, Bot V → list_disj l1)]). 2: apply MPRule_I. intros. inversion H3. subst.
  apply Ax. apply AxRule_I. apply RA4_I. exists (Bot V). exists (list_disj l1).
  exists (list_disj l1). auto. inversion H4. 2: inversion H5. subst. apply wEFQ.
  inversion H3. 2: inversion H4. subst. apply wimp_Id_gen.
- simpl. intros.
  apply MP with (ps:=[(Γ, (Or (Or a (list_disj l0)) (list_disj l1) → Or a (list_disj (l0 ++ l1))) → (A → Or a (list_disj (l0 ++ l1))));
  (Γ, (Or (Or a (list_disj l0)) (list_disj l1) → Or a (list_disj (l0 ++ l1))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → Or (Or a (list_disj l0)) (list_disj l1)) → (Or (Or a (list_disj l0)) (list_disj l1) → Or a (list_disj (l0 ++ l1))) → (A → Or a (list_disj (l0 ++ l1))));
  (Γ,  A → Or (Or a (list_disj l0)) (list_disj l1))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists (Or (Or a (list_disj l0)) (list_disj l1)). exists (Or a (list_disj (l0 ++ l1))).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst.
  apply MP with (ps:=[(Γ, (Or a (Or (list_disj l0) (list_disj l1)) → Or a (list_disj (l0 ++ l1))) → (Or (Or a (list_disj l0)) (list_disj l1) → Or a (list_disj (l0 ++ l1))));
  (Γ, (Or a (Or (list_disj l0) (list_disj l1)) → Or a (list_disj (l0 ++ l1))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (Or (Or a (list_disj l0)) (list_disj l1) → Or a (Or (list_disj l0) (list_disj l1))) → (Or a (Or (list_disj l0) (list_disj l1)) → Or a (list_disj (l0 ++ l1))) → (Or (Or a (list_disj l0)) (list_disj l1) → Or a (list_disj (l0 ++ l1))));
  (Γ, (Or (Or a (list_disj l0)) (list_disj l1) → Or a (Or (list_disj l0) (list_disj l1))))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists (Or (Or a (list_disj l0)) (list_disj l1)).
  exists (Or a (Or (list_disj l0) (list_disj l1))). exists (Or a (list_disj (l0 ++ l1))).
  auto. inversion H4. 2: inversion H5.
  subst. remember (list_disj l0) as E. remember (list_disj l1) as F.
  apply MP with (ps:=[(Γ, (F → Or a (Or E F)) → (Or (Or a E) F → Or a (Or E F)));
  (Γ, F → Or a (Or E F))]). 2: apply MPRule_I. intros. inversion H5. rewrite <- H6.
  apply MP with (ps:=[(Γ, ((Or a E) → Or a (Or E F)) → (F → Or a (Or E F)) → (Or (Or a E) F → Or a (Or E F)));
  (Γ, ((Or a E) → Or a (Or E F)))]). 2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
  apply Ax. apply AxRule_I. apply RA4_I. exists (Or a E). exists F. exists (Or a (Or E F)).
  auto. inversion H8. 2: inversion H9. rewrite <- H9. apply wmonotL_Or. apply Ax.
  apply AxRule_I. apply RA2_I. exists E. exists F. auto. inversion H6. 2: inversion H7.
  rewrite <- H7.
  apply MP with (ps:=[(Γ, ((Or E F) → Or a (Or E F)) → (F → Or a (Or E F)));(Γ, ((Or E F) → Or a (Or E F)))]).
  2: apply MPRule_I. intros. inversion H8. rewrite <- H9.
  apply MP with (ps:=[(Γ, (F → (Or E F)) → ((Or E F) → Or a (Or E F)) → (F → Or a (Or E F)));(Γ, F → (Or E F))]).
  2: apply MPRule_I. intros. inversion H10. rewrite <- H11. apply Ax. apply AxRule_I.
  apply RA1_I. exists F. exists (Or E F). exists (Or a (Or E F)). auto.
  inversion H11. 2: inversion H12. rewrite <- H12. apply Ax. apply AxRule_I. apply RA3_I.
  exists E. exists F. auto. inversion H9. 2: inversion H10. rewrite <- H10. apply Ax.
  apply AxRule_I. apply RA3_I. exists a. exists (Or E F). auto. inversion H3. 2: inversion H4.
  rewrite <- H4. apply wmonotL_Or. apply IHl0. apply wimp_Id_gen.
Qed.

Lemma list_disj_remove_app : forall l0 l1 Γ A,
wBIH_rules (Γ, list_disj (l0 ++ remove_list l0 l1) → Or A (list_disj (l0 ++ remove eq_dec_form A (remove_list l0 l1)))).
Proof.
induction l0.
- simpl. intros. apply remove_disj.
- simpl. intros.
  apply MP with (ps:=[(Γ, (Or a (Or A (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  → Or A (Or a (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) → (Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → Or A (Or a (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))));
  (Γ,Or a (Or A (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  → Or A (Or a (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1))))))]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Γ, (Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → Or a (Or A (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) → (Or a (Or A (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  → Or A (Or a (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) → (Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → Or A (Or a (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))));
  (Γ,(Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  → Or a (Or A (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA1_I.
  exists (Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))).
  exists (Or a (Or A (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))).
  exists (Or A (Or a (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))). auto.
  inversion H1. 2: inversion H2. subst.
  { simpl. apply wmonotL_Or. clear H1. clear H0. clear H.
    remember (remove eq_dec_form a (remove_list l0 l1)) as E.
    apply MP with (ps:=[(Γ, (Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E))) → Or A (list_disj (l0 ++ remove eq_dec_form A E))) → (list_disj (l0 ++ E) → Or A (list_disj (l0 ++ remove eq_dec_form A E))));
    (Γ, (Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E))) → Or A (list_disj (l0 ++ remove eq_dec_form A E))))]).
    2: apply MPRule_I. intros. inversion H. rewrite <- H0.
    apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) → Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))) → (Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E))) → Or A (list_disj (l0 ++ remove eq_dec_form A E))) → (list_disj (l0 ++ E) → Or A (list_disj (l0 ++ remove eq_dec_form A E))));
    (Γ, (list_disj (l0 ++ E) → Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))))]).
    2: apply MPRule_I. intros. inversion H1. rewrite <- H2. apply Ax. apply AxRule_I.
    apply RA1_I. exists (list_disj (l0 ++ E)). exists (Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))).
    exists (Or A (list_disj (l0 ++ remove eq_dec_form A E))). auto. inversion H2. rewrite <- H3.
    { simpl. apply MP with (ps:=[(Γ, ((Or (list_disj l0) (Or A (list_disj (remove eq_dec_form A E)))) → Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))) → (list_disj (l0 ++ E) → Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))));
    (Γ, ((Or (list_disj l0) (Or A (list_disj (remove eq_dec_form A E)))) → Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))))]).
    2: apply MPRule_I. intros. inversion H4. rewrite <- H5.
    apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) → (Or (list_disj l0) (Or A (list_disj (remove eq_dec_form A E))))) → ((Or (list_disj l0) (Or A (list_disj (remove eq_dec_form A E)))) → Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))) → (list_disj (l0 ++ E) → Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))));
    (Γ, (list_disj (l0 ++ E) → (Or (list_disj l0) (Or A (list_disj (remove eq_dec_form A E))))))]).
    2: apply MPRule_I. intros. inversion H6. rewrite <- H7. apply Ax. apply AxRule_I. apply RA1_I.
    exists (list_disj (l0 ++ E)). exists (Or (list_disj l0) (Or A (list_disj (remove eq_dec_form A E)))).
    exists (Or A (Or (list_disj l0) (list_disj (remove eq_dec_form A E)))). auto.
    inversion H7. 2: inversion H8. rewrite <- H8.
    { remember (Or (list_disj l0) (Or A (list_disj (remove eq_dec_form A E)))) as F.
      apply MP with (ps:=[(Γ, ((Or (list_disj l0) (list_disj E)) → F) → (list_disj (l0 ++ E) → F));
      (Γ, ((Or (list_disj l0) (list_disj E)) → F))]). 2: apply MPRule_I. intros.
      inversion H9. rewrite <- H10.
      apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) → (Or (list_disj l0) (list_disj E))) → ((Or (list_disj l0) (list_disj E)) → F) → (list_disj (l0 ++ E) → F));
      (Γ, list_disj (l0 ++ E) → (Or (list_disj l0) (list_disj E)))]). 2: apply MPRule_I. intros.
      inversion H11. rewrite <- H12. apply Ax. apply AxRule_I. apply RA1_I.
      exists (list_disj (l0 ++ E)). exists (Or (list_disj l0) (list_disj E)). exists F. auto.
      inversion H12. 2: inversion H13. rewrite <- H13. apply list_disj_app. apply wimp_Id_gen.
      inversion H10. 2: inversion H11. rewrite <- H11. clear H11. clear H10.
      clear H9. clear H8. clear H7. clear H6. clear H5. clear H0. clear H4.
      clear H3. clear H2. clear H1. clear H. rewrite HeqF. apply wmonotL_Or.
      apply remove_disj. }
    inversion H5. 2: inversion H6. rewrite <- H6. remember (list_disj l0) as D.
    remember (list_disj (remove eq_dec_form A E)) as F.
    apply MP with (ps:=[(Γ, (Or A F → Or A (Or D F)) → (Or D (Or A F) → Or A (Or D F)));(Γ, (Or A F) → Or A (Or D F))]).
    2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
    apply MP with (ps:=[(Γ, (D → Or A (Or D F)) → (Or A F → Or A (Or D F)) → (Or D (Or A F) → Or A (Or D F)));(Γ, D → Or A (Or D F))]).
    2: apply MPRule_I. intros. inversion H9. rewrite <- H10. apply Ax. apply AxRule_I.
    apply RA4_I. exists D. exists (Or A F). exists (Or A (Or D F)). auto. inversion H10. 2: inversion H11.
    rewrite <- H11.
    apply MP with (ps:=[(Γ, ((Or D F) → Or A (Or D F)) → (D → Or A (Or D F)));(Γ, ((Or D F) → Or A (Or D F)))]).
    2: apply MPRule_I. intros. inversion H12. rewrite <- H13.
    apply MP with (ps:=[(Γ, (D → (Or D F)) → ((Or D F) → Or A (Or D F)) → (D → Or A (Or D F)));(Γ, D → (Or D F))]).
    2: apply MPRule_I. intros. inversion H14. rewrite <- H15. apply Ax. apply AxRule_I.
    apply RA1_I. exists D. exists (Or D F). exists (Or A (Or D F)). auto. inversion H15.
    rewrite <- H16. apply Ax. apply AxRule_I. apply RA2_I. exists D. exists F. auto.
    inversion H16. inversion H13. rewrite <- H14. apply Ax. apply AxRule_I. apply RA3_I.
    exists A. exists (Or D F). auto. inversion H14. inversion H8. rewrite <- H9.
    apply wmonotL_Or. apply Ax. apply AxRule_I. apply RA3_I. exists D. exists F. auto.
    inversion H9. }
    inversion H3. inversion H0. 2: inversion H1. rewrite <- H1. apply wmonotL_Or. apply list_disj_app0.
    apply wimp_Id_gen. }
  inversion H0. 2: inversion H1. subst.
  remember ((list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1))))) as E.
  apply MP with (ps:=[(Γ, ((Or A E) → Or A (Or a E)) → (Or a (Or A E) → Or A (Or a E)));
  (Γ, ((Or A E) → Or A (Or a E)))]). 2: apply MPRule_I. intros. inversion H1. rewrite <- H2.
  apply MP with (ps:=[(Γ, (a → Or A (Or a E)) → ((Or A E) → Or A (Or a E)) → (Or a (Or A E) → Or A (Or a E)));
  (Γ, (a → Or A (Or a E)))]). 2: apply MPRule_I. intros. inversion H3. rewrite <- H4. clear H4.
  clear H2. apply Ax. apply AxRule_I. apply RA4_I. exists a. exists (Or A E).
  exists (Or A (Or a E)). auto. inversion H4. 2: inversion H5. rewrite <- H5.
  apply MP with (ps:=[(Γ, ((Or a E) → Or A (Or a E)) → (a → Or A (Or a E))); (Γ, ((Or a E) → Or A (Or a E)))]).
  2: apply MPRule_I. intros. inversion H6. rewrite <- H7.
  apply MP with (ps:=[(Γ, (a → (Or a E)) → ((Or a E) → Or A (Or a E)) → (a → Or A (Or a E))); (Γ, a → (Or a E))]).
  2: apply MPRule_I. intros. inversion H8. rewrite <- H9. apply Ax. apply AxRule_I. apply RA1_I.
  exists a. exists (Or a E). exists (Or A (Or a E)). auto. inversion H9.
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
  apply MP with (ps:=[(Γ, (list_disj (l0 ++ remove_list l0 l1) → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (list_disj l1 → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, list_disj (l0 ++ remove_list l0 l1) → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1))))]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Γ, (list_disj l1 → list_disj (l0 ++ remove_list l0 l1)) → (list_disj (l0 ++ remove_list l0 l1) → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (list_disj l1 → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ,list_disj l1 → list_disj (l0 ++ remove_list l0 l1))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists (list_disj l1). exists (list_disj (l0 ++ remove_list l0 l1)).
  exists (Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))). auto.
  inversion H1. 2: inversion H2. subst. apply IHl0. inversion H0. subst.
  clear H. clear H0. apply list_disj_remove_app. inversion H1.
Qed.

Lemma der_list_disj_remove1 : forall Γ A l0 l1,
    (wBIH_rules (Γ, A → list_disj l0)) ->
    (wBIH_rules (Γ, A → list_disj (l0 ++ remove_list l0 l1))).
Proof.
intros Γ A. induction l0.
- simpl. intros.
  apply MP with (ps:=[(Γ, (Bot V → list_disj l1) → (A → list_disj l1));
  (Γ, Bot V → list_disj l1)]). 2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → Bot V) → (Bot V → list_disj l1) → (A → list_disj l1));
  (Γ, A → Bot V)]). 2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists (Bot V). exists (list_disj l1).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst. apply wEFQ.
- intros. subst. simpl. simpl in H.
  apply MP with (ps:=[(Γ, (Or a (list_disj l0) → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (A → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, (Or a (list_disj l0) → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A → Or a (list_disj l0)) → (Or a (list_disj l0) → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) → (A → Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, A → Or a (list_disj l0))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (Or a (list_disj l0)).
  exists (Or a (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))). auto.
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


(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* How we build prime pairs. *)

Definition choice_form (Γ Δ : @Ensemble (BPropF V)) (A1 A2 : BPropF V)
  (DerDisj : wpair_derrec (Γ, Singleton _ (Or A1 A2))) : Ensemble (BPropF V) :=
fun x => (In _ Γ x) \/
  (((wpair_derrec (Union _ Γ (Singleton _ A1), Δ) -> False) -> x = A1) /\
  (((wpair_derrec (Union _ Γ (Singleton _ A1), Δ) -> False) -> False) -> x = A2)).

(* For any natural number, check if it is the encoding of a formula, and if it is and this
   formula happens to be a disjunction and derivable from the set, then pick one of the disjuncts. *)

Definition choice_code (Γ Δ : @Ensemble (BPropF V)) (n :nat) : @Ensemble (BPropF V) :=
match decoding n with
| None => Γ
| Some A => match A with
            | Or A1 A2 => fun x => (In _ Γ x) \/
                (exists (DerDisj : wpair_derrec (Γ, Singleton _ (Or A1 A2))), In _ (choice_form Γ Δ A1 A2 DerDisj) x)
            | _ => Γ
            end
end.

Fixpoint nprime_theory (Γ Δ : @Ensemble (BPropF V)) (n : nat) : @Ensemble (BPropF V) :=
match n with
| 0 => Γ
| S m => choice_code (nprime_theory Γ Δ m) Δ (S m)
end.

Definition prime_theory (Γ Δ : @Ensemble (BPropF V)) : @Ensemble (BPropF V) :=
  fun x => (exists n, In _ (nprime_theory Γ Δ n) x).


(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Properties of our prime pairs. *)




(* A prime pair is an extension of the initial pair. *)

Lemma nprime_theory_extens : forall n (Γ Δ: @Ensemble (BPropF V)) x,
    In (BPropF V) Γ x -> In (BPropF V) (nprime_theory Γ Δ n) x.
Proof.
induction n.
- simpl. auto.
- simpl. intros. pose (IHn Γ Δ x H). unfold choice_code.
  destruct (decoding (S n)).
  + destruct b ; auto.
    * unfold In. left. auto.
  + auto.
Qed.

Lemma nprime_theory_extens_le : forall m n (Γ Δ: @Ensemble (BPropF V)) x,
    In (BPropF V) (nprime_theory Γ Δ n) x -> (le n m) -> In (BPropF V) (nprime_theory Γ Δ m) x.
Proof.
induction m.
- intros. simpl. inversion H0. subst. simpl in H. auto.
- intros. inversion H0.
  + subst. auto.
  + subst. simpl. unfold In. apply IHm in H ; auto. unfold choice_code.
    destruct (decoding (S m)).
    * destruct b ; auto.
    * auto.
Qed.

Lemma prime_theory_extens : forall (Γ Δ: @Ensemble (BPropF V)) x,
    In (BPropF V) Γ x -> In (BPropF V) (prime_theory Γ Δ) x.
Proof.
intros. unfold prime_theory. unfold In. exists 0. auto.
Qed.

(* Each step of the construction preserves unprovability. *)

Lemma Under_nprime_theory : forall n (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  (wpair_derrec (nprime_theory Γ Δ n, Δ) -> False).
Proof.
induction n ; intros.
- simpl in H0. auto.
- simpl in H0. apply IHn with (Γ:=Γ) (Δ:=Δ) ; auto. unfold choice_code in H0.
  destruct (decoding (S n)).
  + destruct b ; auto. destruct H0. simpl in H0. destruct H0. destruct H1.
    destruct (classic (wpair_derrec (nprime_theory Γ Δ n, Singleton (BPropF V) (Or b1 b2)))).
    * assert ((fun x : BPropF V => In (BPropF V) (nprime_theory Γ Δ n) x \/ (exists
      DerDisj : wpair_derrec (nprime_theory Γ Δ n, Singleton (BPropF V) (Or b1 b2)),
      In (BPropF V) (choice_form (nprime_theory Γ Δ n) Δ b1 b2 DerDisj) x)) =
      (fun x : BPropF V => In (BPropF V) (nprime_theory Γ Δ n) x \/
      In (BPropF V) (choice_form (nprime_theory Γ Δ n) Δ b1 b2 H3) x)).
      { apply Extensionality_Ensembles. split. intro. intros. inversion H4.
        unfold In. auto. destruct H5. unfold In. auto. intro. intros.
        inversion H4. unfold In. auto. unfold In. right. exists H3. auto. }
      rewrite H4 in H2. clear H4. unfold choice_form in H2.
      destruct (classic (wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ n) (Singleton (BPropF V) b1), Δ) ->
      False)).
      { assert ((fun x : BPropF V => In (BPropF V) (nprime_theory Γ Δ n) x \/
        In (BPropF V) (fun x0 : BPropF V => In (BPropF V) (nprime_theory Γ Δ n)
        x0 \/ ((wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ n) (Singleton (BPropF V) b1), Δ) ->
        False) -> x0 = b1) /\ (((wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ n)
        (Singleton (BPropF V) b1), Δ) -> False) -> False) -> x0 = b2)) x) =
        Union _ (nprime_theory Γ Δ n) (Singleton _ b1)).
        { apply Extensionality_Ensembles. split. intro. intros. inversion H5. apply Union_introl. auto.
          inversion H6. apply Union_introl. auto. destruct H7. apply H7 in H4. rewrite H4.
          apply Union_intror. apply In_singleton. intro. intros. inversion H5. subst.
          unfold In. auto. subst. inversion H6. subst. unfold In. right. right.
          split ; auto. intro. exfalso. auto. }
        rewrite H5 in H2. clear H5. exfalso. apply H4. exists x. repeat split ; auto. }
      { assert ((fun x : BPropF V => In (BPropF V) (nprime_theory Γ Δ n) x \/
        In (BPropF V) (fun x0 : BPropF V => In (BPropF V) (nprime_theory Γ Δ n)
        x0 \/ ((wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ n) (Singleton (BPropF V) b1), Δ) ->
        False) -> x0 = b1) /\ (((wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ n)
        (Singleton (BPropF V) b1), Δ) -> False) -> False) -> x0 = b2)) x) =
        Union _ (nprime_theory Γ Δ n) (Singleton _ b2)).
        { apply Extensionality_Ensembles. split. intro. intros. inversion H5. apply Union_introl. auto.
          inversion H6. apply Union_introl. auto. destruct H7. apply H8 in H4. rewrite H4.
          apply Union_intror. apply In_singleton. intro. intros. inversion H5. subst.
          unfold In. auto. subst. inversion H6. subst. unfold In. right. right.
          split ; auto. intro. exfalso. auto. }
        rewrite H5 in H2. clear H5. assert (wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ n)
        (Singleton (BPropF V) b1), Δ)). destruct (classic (wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ n)
        (Singleton (BPropF V) b1), Δ))). auto. exfalso. apply H4. auto. clear H4.
        destruct H5. simpl in H4. destruct H4. destruct H5.
        exists (x0 ++ (remove_list x0 x)). repeat split. Search remove_list. apply add_remove_list_preserve_NoDup.
        auto. auto. intros. simpl. apply in_app_or in H7. destruct H7.
        apply H5. auto. apply In_remove_list_In_list in H7. apply H1. auto.
        simpl. apply MP with (ps:=[(nprime_theory Γ Δ n, Imp (Or b1 b2) (list_disj (x0 ++ remove_list x0 x)));
        (nprime_theory Γ Δ n, (Or b1 b2))]). 2: apply MPRule_I. intros. inversion H7. subst.
        apply MP with (ps:=[(nprime_theory Γ Δ n, (b2 → (list_disj (x0 ++ remove_list x0 x))) → (Or b1 b2 → (list_disj (x0 ++ remove_list x0 x))));
        (nprime_theory Γ Δ n, (b2 → (list_disj (x0 ++ remove_list x0 x))))]). 2: apply MPRule_I. intros. inversion H8. subst.
        apply MP with (ps:=[(nprime_theory Γ Δ n, (b1 → (list_disj (x0 ++ remove_list x0 x))) → (b2 → (list_disj (x0 ++ remove_list x0 x))) → (Or b1 b2 → (list_disj (x0 ++ remove_list x0 x))));
        (nprime_theory Γ Δ n, (b1 → (list_disj (x0 ++ remove_list x0 x))))]). 2: apply MPRule_I. intros. inversion H9. subst.
        apply Ax. apply AxRule_I. apply RA4_I. exists b1. exists b2. exists (list_disj (x0 ++ remove_list x0 x)).
        auto. inversion H10. 2: inversion H11. subst.
        { simpl. apply der_list_disj_remove1.
          pose (wBIH_Deduction_Theorem ((Union (BPropF V) (nprime_theory Γ Δ n) (Singleton (BPropF V) b1), list_disj x0))
          H6 b1 (list_disj x0) (nprime_theory Γ Δ n)). apply w ; auto. }
        inversion H9. 2: inversion H10. subst.
        { simpl. apply der_list_disj_remove2.
          pose (wBIH_Deduction_Theorem ((Union (BPropF V) (nprime_theory Γ Δ n) (Singleton (BPropF V) b2), list_disj x))
          H2 b2 (list_disj x) (nprime_theory Γ Δ n)). apply w ; auto. }
        inversion H8. 2: inversion H9. subst. destruct H3. simpl in H3. destruct H3.
        destruct H9. destruct x1. apply MP with (ps:=[(nprime_theory Γ Δ n, Imp (Bot V) (Or b1 b2));
        (nprime_theory Γ Δ n, Bot V)]). 2: apply MPRule_I. intros. inversion H11. subst.
        apply wEFQ. inversion H12. 2: inversion H13. subst. simpl in H10. auto.
        destruct x1. simpl in H10. apply absorp_Or1 in H10. assert (List.In b [b]). apply in_eq. pose (H9 b H11).
        inversion s. subst. auto. exfalso. inversion H3. subst. apply H13.
        assert (List.In b0 (b :: b0 :: x1)). apply in_cons. apply in_eq. pose (H9 b0 H11).
        inversion s. subst. assert (List.In b (b :: Or b1 b2 :: x1)). apply in_eq. pose (H9 b H12).
        inversion s0. subst. apply in_eq. }
    * assert ((fun x : BPropF V => In (BPropF V) (nprime_theory Γ Δ n) x \/ (exists
      DerDisj : wpair_derrec (nprime_theory Γ Δ n, Singleton (BPropF V) (Or b1 b2)),
      In (BPropF V) (choice_form (nprime_theory Γ Δ n) Δ b1 b2 DerDisj) x))= (nprime_theory Γ Δ n)).
      { apply Extensionality_Ensembles. split. intro. intros. inversion H4. auto. destruct H5.
        exfalso. apply H3. auto. intro. intros. unfold In. auto. }
      rewrite H4 in H2. clear H4. exists x. repeat split ; auto.
  + auto.
Qed.

(* A prime pair preserves derivability. *)

Lemma der_nprime_theory_mprime_theory_le : forall n m (Γ Δ: @Ensemble (BPropF V)) A,
  (wBIH_rules (nprime_theory Γ Δ n, A)) -> (le n m) ->
    (wBIH_rules (nprime_theory Γ Δ m, A)).
Proof.
intros.
pose (wBIH_monot (nprime_theory Γ Δ n, A) H (nprime_theory Γ Δ m)).
simpl in w. apply w. intro. intros. apply nprime_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma der_prime_theory_nprime_theory : forall s, (wBIH_rules s) ->
 (forall (Γ Δ: @Ensemble (BPropF V)) A, (prime_theory Γ Δ = fst s) ->
                                        (A = snd s) ->
                                        (exists n, (wBIH_rules (nprime_theory Γ Δ n, A)))).
Proof.
intros s D. induction D ; intros.
- inversion H. subst. simpl in H0. subst. simpl. unfold prime_theory in H2. destruct H2.
  exists x. apply Id. apply IdRule_I. auto.
- inversion H. subst. simpl in H0. subst. simpl. exists 0. apply Ax. apply AxRule_I.
  auto.
- inversion H1. subst. simpl in H2. subst.
  assert (J1: List.In (prime_theory Γ Δ, A0 → B) [(prime_theory Γ Δ, A0 → B); (prime_theory Γ Δ, A0)]).
  apply in_eq. pose (H (prime_theory Γ Δ, A0 → B) J1).
  assert (J2: List.In (prime_theory Γ Δ, A0) [(prime_theory Γ Δ, A0 → B); (prime_theory Γ Δ, A0)]).
  apply in_cons. apply in_eq. pose (H (prime_theory Γ Δ, A0) J2).
  assert (J3: prime_theory Γ Δ = prime_theory Γ Δ). auto.
  assert (J4: A0 → B = A0 → B). auto.
  pose (H0 (prime_theory Γ Δ, A0 → B) J1 Γ Δ (A0 → B) J3 J4). destruct e. clear J4.
  clear w. clear J1.
  assert (J5: A0 = A0). auto.
  pose (H0 (prime_theory Γ Δ, A0) J2 Γ Δ A0 J3 J5). destruct e. clear J5.
  clear J3. clear w0. clear J2.
  exists (max x x0). simpl.
  apply MP with (ps:=[(nprime_theory Γ Δ (Init.Nat.max x x0), A0 → B);(nprime_theory Γ Δ (Init.Nat.max x x0), A0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  pose (der_nprime_theory_mprime_theory_le x (Init.Nat.max x x0) _ _ _ H2). apply w.
  lia. inversion H5. 2: inversion H6. subst. clear H4. clear H5.
    pose (der_nprime_theory_mprime_theory_le x0 (Init.Nat.max x x0) _ _ _ H3). apply w. lia.
- subst. inversion H1. subst. simpl in H2. subst.
  assert (J1: List.In (Empty_set (BPropF V), A) [(Empty_set (BPropF V), A)]). apply in_eq.
  pose (H (Empty_set (BPropF V), A) J1). simpl. exists 0. apply DNw with (ps:=[(Empty_set (BPropF V), A)]).
  2: apply DNwRule_I. intros. inversion H2. subst. auto. inversion H3.
Qed.

(* A prime pair is prime. *)

Lemma primeness_fst_Lind_pair0 : forall (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  (forall A1 A2, (wBIH_rules (prime_theory Γ Δ, Or A1 A2)) -> ((In _ (prime_theory Γ Δ) A1) \/ (In _ (prime_theory Γ Δ) A2))).
Proof.
intros.

(* There is a n s.t. (nprime_theory Γ Δ n) derives the disjunction. *)
assert (J1: prime_theory Γ Δ = prime_theory Γ Δ). auto.
assert (J2: Or A1 A2 = Or A1 A2). auto.
pose (der_prime_theory_nprime_theory (prime_theory Γ Δ, Or A1 A2) H0 Γ Δ (Or A1 A2) J1 J2).
destruct e.

(* There must be m and l s.t.  n < m and (S m) is the encoding of (Or A1 (Or A2 (Bot V x l)))
   and the latter is derived by (nprime_theory Γ Δ m). *)
assert (exists l m, (decoding (S m) = Some (Or A1 (Or A2 (mult_disj l (Bot V))))) /\
(x <= m)).
{ pose (too_many_disj0 x A1 A2). destruct e. destruct H2. exists x1.
  exists x0. auto. }
destruct H2. destruct H2. destruct H2.
assert (J3: wBIH_rules (nprime_theory Γ Δ x1, Or A1 (Or A2 (mult_disj x0 (Bot V))))).
apply wBIH_monot with (Γ1:=nprime_theory Γ Δ x1) in H1. remember (nprime_theory Γ Δ x1) as C.
apply MP with (ps:=[(C, Imp (Or A1 A2) (Or A1 (Or A2 (mult_disj x0 (Bot V)))));
(C, (Or A1 A2))]). 2: apply MPRule_I. intros. inversion H4. rewrite <- H5.
apply MP with (ps:=[(C, (A2 → (Or A1 (Or A2 (mult_disj x0 (Bot V))))) → (Or A1 A2 → Or A1 (Or A2 (mult_disj x0 (Bot V)))));
(C, A2 → (Or A1 (Or A2 (mult_disj x0 (Bot V)))))]). 2: apply MPRule_I. intros. inversion H6. rewrite <- H7.
apply MP with (ps:=[(C, (A1 → (Or A1 (Or A2 (mult_disj x0 (Bot V))))) → (A2 → (Or A1 (Or A2 (mult_disj x0 (Bot V))))) → (Or A1 A2 → Or A1 (Or A2 (mult_disj x0 (Bot V)))));
(C, A1 → (Or A1 (Or A2 (mult_disj x0 (Bot V)))))]). 2: apply MPRule_I. intros. inversion H8. rewrite <- H9.
apply Ax. apply AxRule_I. apply RA4_I. exists A1. exists A2.
exists (Or A1 (Or A2 (mult_disj x0 (Bot V)))). auto. inversion H9. 2: inversion H10.
rewrite <- H10. apply Ax. apply AxRule_I. apply RA2_I. exists A1. exists (Or A2 (mult_disj x0 (Bot V))).
auto. inversion H7. 2: inversion H8. rewrite <- H8. remember (mult_disj x0 (Bot V)) as E.
apply MP with (ps:=[(C, ((Or A2 E) → Or A1 (Or A2 E)) → (A2 → Or A1 (Or A2 E)));
(C, (Or A2 E) → Or A1 (Or A2 E))]). 2: apply MPRule_I. intros. inversion H9. rewrite <- H10.
apply MP with (ps:=[(C, (A2 → (Or A2 E)) → ((Or A2 E) → Or A1 (Or A2 E)) → (A2 → Or A1 (Or A2 E)));
(C, A2 → (Or A2 E))]). 2: apply MPRule_I. intros. inversion H11. rewrite <- H12.
apply Ax. apply AxRule_I. apply RA1_I. exists A2. exists (Or A2 E).
exists (Or A1 (Or A2 E)). auto. inversion H12. 2: inversion H13. rewrite <- H13.
apply Ax. apply AxRule_I. apply RA2_I. exists A2. exists E. auto. inversion H10.
2: inversion H11. rewrite <- H11. apply Ax. apply AxRule_I. apply RA3_I.
exists A1. exists (Or A2 E). auto. inversion H5. 2: inversion H6. rewrite <- H6.
auto.
intro. intros. simpl in H4. apply nprime_theory_extens_le with (n:=x) ; auto.

(* Then (nprime_theory Γ Δ (S (m))) must take A1 or (Or A2 (Bot V x l)). *)
assert (In (BPropF V) (nprime_theory Γ Δ (S x1)) A1 \/
((wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ x1) (Singleton (BPropF V) A1), Δ))
  /\ (In (BPropF V) (nprime_theory Γ Δ (S x1)) (Or A2 (mult_disj x0 (Bot V)))))).
simpl. unfold choice_code. rewrite H2.
unfold choice_form. simpl.
assert (J4: wpair_derrec (nprime_theory Γ Δ x1, Singleton (BPropF V) (Or A1 (Or A2 (mult_disj x0 (Bot V)))))).
exists [(Or A1 (Or A2 (mult_disj x0 (Bot V))))]. repeat split.
apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H4. subst. simpl.
apply In_singleton. simpl. inversion H5. simpl.
apply MP with (ps:=[(nprime_theory Γ Δ x1, Imp (Or A1 (Or A2 (mult_disj x0 (Bot V)))) (Or (Or A1 (Or A2 (mult_disj x0 (Bot V)))) (Bot V)));
(nprime_theory Γ Δ x1, (Or A1 (Or A2 (mult_disj x0 (Bot V)))))]). 2: apply MPRule_I.
intros. inversion H4. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (Or A1 (Or A2 (mult_disj x0 (Bot V)))).
exists (Bot V). auto. inversion H5. subst. 2: inversion H6. auto.
destruct (classic (wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ x1) (Singleton (BPropF V) A1), Δ) -> False)).
left. unfold In. right. exists J4.
right. split. intro. auto. intros. exfalso. apply H5. auto.
right. unfold In. split.
destruct (classic (wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ x1) (Singleton (BPropF V) A1), Δ))) ; auto.
exfalso. auto.
auto. right. exists J4. right. split. intro. exfalso. auto.
intro. auto. destruct H4.


(* If it takes A1, then we are done as A1 is in (prime_theory Γ Δ). *)
left. unfold prime_theory. unfold In. exists (S x1) ; auto.

(* If it takes (Or A2 (Bot V x l)) we need more work. *)
right. destruct H4.

(* Note that (nprime_theory Γ Δ (S x1)) derives A2. *)
assert (wBIH_rules (nprime_theory Γ Δ (S x1), A2)).
apply der_mult_disj_Bot with (n:= x0). apply Id. apply IdRule_I. auto.

(* There is a k and o s.t. S (x1) < k and (S k) is the encoding for (Or A2 (mult_disj o (Bot V))). *)
assert (exists k o, (decoding (S k) = Some (Or A2 (mult_disj o (Bot V)))) /\
((S x1) <= k)). apply too_many_disj1.
destruct H7. destruct H7. destruct H7.

(* Then (nprime_theory Γ Δ (S k)) derives (Or A2 (mult_disj o Bot V)) as it derives A2. *)
assert (J4: wpair_derrec (nprime_theory Γ Δ x2, Singleton (BPropF V)  (Or A2 (mult_disj x3 (Bot V))))).
exists [(Or A2 (mult_disj x3 (Bot V)))]. repeat split.
apply NoDup_cons ; auto ; apply NoDup_nil. intros. inversion H9. subst. simpl.
apply In_singleton. simpl. inversion H10. simpl.
apply MP with (ps:=[(nprime_theory Γ Δ x2, Imp (Or A2 (mult_disj x3 (Bot V))) (Or (Or A2 (mult_disj x3 (Bot V))) (Bot V)));
(nprime_theory Γ Δ x2, (Or A2 (mult_disj x3 (Bot V))))]). 2: apply MPRule_I.
intros. inversion H9. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (Or A2 (mult_disj x3 (Bot V))).
exists (Bot V). auto. inversion H10. subst. 2: inversion H11.
apply wBIH_monot with (Γ1:=nprime_theory Γ Δ x2) in H6. simpl in H6.
apply MP with (ps:=[(nprime_theory Γ Δ x2, Imp A2 (Or A2 (mult_disj x3 (Bot V))));
(nprime_theory Γ Δ x2, A2)]). 2: apply MPRule_I. intros. inversion H11. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists A2. exists (mult_disj x3 (Bot V)). auto.
inversion H12. 2: inversion H13. subst. auto. intro. intros.
apply nprime_theory_extens_le with (n:=(S x1)) ; auto ; lia.

(* So this theory has to take A2 and then we are done as A2 is in prime_theory Γ Δ. *)
assert (In (BPropF V) (nprime_theory Γ Δ (S x2)) A2).
simpl. unfold choice_code. rewrite H7. unfold choice_form. simpl. unfold In. right. exists J4.
right. split. intro. auto. intros. exfalso.
apply Under_nprime_theory with (n:=x2) (Γ:=Γ) (Δ:=Δ) ; auto.
destruct H4. simpl in H4. destruct H4. destruct H10.
destruct (classic (wpair_derrec (Union (BPropF V) (nprime_theory Γ Δ x2) (Singleton (BPropF V) A2), Δ))).
destruct H12. simpl in H12. destruct H12. destruct H13.
exists (x4 ++ (remove_list x4 x5)). repeat split.
apply add_remove_list_preserve_NoDup ; auto. intros.
simpl. apply in_app_or in H15. destruct H15. apply H10. auto.
apply In_remove_list_In_list in H15. apply H13. auto. simpl.
remember (list_disj (x4 ++ remove_list x4 x5)) as E.
apply MP with (ps:=[(nprime_theory Γ Δ x2, Imp (Or A1 A2) E);
(nprime_theory Γ Δ x2, (Or A1 A2))]). 2: apply MPRule_I. intros. inversion H15.
rewrite <- H16.
apply MP with (ps:=[(nprime_theory Γ Δ x2, (A2 → E) → (Or A1 A2 → E));
(nprime_theory Γ Δ x2, (A2 → E))]). 2: apply MPRule_I. intros. inversion H17.
rewrite <- H18.
apply MP with (ps:=[(nprime_theory Γ Δ x2, (A1 → E) → (A2 → E) → (Or A1 A2 → E));
(nprime_theory Γ Δ x2, (A1 → E))]). 2: apply MPRule_I. intros. inversion H19.
rewrite <- H20. apply Ax. apply AxRule_I. apply RA4_I. exists A1. exists A2.
exists E. auto. inversion H20. 2: inversion H21. rewrite <- H21. subst.
apply der_list_disj_remove1.
apply wBIH_Deduction_Theorem with (s:=(Union (BPropF V) (nprime_theory Γ Δ x2) (Singleton (BPropF V) A1), list_disj x4)) ; auto.
apply wBIH_monot with (Γ1:=Union (BPropF V) (nprime_theory Γ Δ x2) (Singleton (BPropF V) A1)) in H11 ; auto ; simpl.
intro. intros. inversion H16. subst. auto. subst. apply Union_introl.
apply nprime_theory_extens_le with (n:=x1) ; auto ; lia.
subst. inversion H18. subst. apply Union_intror. apply In_singleton.
inversion H18. subst. clear H18. clear H17. clear H15.
apply der_list_disj_remove2.
apply wBIH_Deduction_Theorem with (s:=(Union (BPropF V) (nprime_theory Γ Δ x2) (Singleton (BPropF V) A2), list_disj x5)) ; auto.
inversion H19. inversion H16. rewrite <- H17.
apply wBIH_monot with (Γ1:=nprime_theory Γ Δ x2) in H1. simpl in H1. auto.
simpl. intro. intros. apply nprime_theory_extens_le with (n:=x) ; auto ; lia.
inversion H17.
exfalso. auto.

unfold prime_theory. unfold In. exists (S x2) ; auto.
Qed.

Lemma primeness_fst_Lind_pair : forall (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  (forall A1 A2, In _ (prime_theory Γ Δ) (Or A1 A2) -> ((In _ (prime_theory Γ Δ) A1) \/ (In _ (prime_theory Γ Δ) A2))).
Proof.
intros. apply primeness_fst_Lind_pair0 ; auto. apply Id. apply IdRule_I. auto.
Qed.

Lemma list_primeness_fst_Lind_pair : forall (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  (forall x, In _ (prime_theory Γ Δ) (list_disj x) -> ((In _ (prime_theory Γ Δ) (Bot V)) \/ (exists A, List.In A x /\ (In _ (prime_theory Γ Δ) A)))).
Proof.
intros. induction x.
- simpl in H0. left. auto.
- simpl. simpl in H0. apply primeness_fst_Lind_pair in H0. destruct H0. right.
  exists a. auto. 2: auto. apply IHx in H0. destruct H0. left. auto.
  right. destruct H0. destruct H0. clear IHx. exists x0. auto.
Qed.


(* A prime pair is closed under derivation. *)

Lemma closeder_fst_Lind_pair : forall (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  (forall A, wBIH_rules (prime_theory Γ Δ, A) -> (In _ (prime_theory Γ Δ) A)).
Proof.
intros. assert (wBIH_rules (prime_theory Γ Δ, (Or A A))).
apply MP with (ps:=[(prime_theory Γ Δ, Imp A (Or A A));(prime_theory Γ Δ, A)]). 2: apply MPRule_I.
intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A. exists A. auto.
inversion H2. 2: inversion H3. subst. clear H1. auto.
apply primeness_fst_Lind_pair0 in H1 ; auto. destruct H1 ; auto.
Qed.

(* A prime pair is complete. *)

Lemma Complete_Lind_pair : forall (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  complete (prime_theory Γ Δ, fun x : BPropF V => wBIH_rules (prime_theory Γ Δ, x) -> False).
Proof.
intros. intro. simpl. destruct (classic (prime_theory Γ Δ A)) ; auto. right. intro.
apply H0. apply closeder_fst_Lind_pair ; auto.
Qed.

(* A prime pair is consistent. *)

Lemma Consist_nprime_theory : forall n (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  (wBIH_rules (nprime_theory Γ Δ n, Bot V) -> False).
Proof.
intros. pose (Under_nprime_theory n Γ Δ H).
apply f. exists []. repeat split ; auto. apply NoDup_nil.
intros. inversion H1.
Qed.

Lemma Consist_prime_theory : forall (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  (wBIH_rules (prime_theory Γ Δ, Bot V) -> False).
Proof.
intros. apply closeder_fst_Lind_pair in H0 ; auto. unfold prime_theory in H0.
unfold In in H0. destruct H0. apply Consist_nprime_theory with (Γ:=Γ) (Δ:=Δ) (n:=x) ; auto.
apply Id. apply IdRule_I. auto.
Qed.

(* A prime pair is unprovable. *)

Lemma Under_Lind_pair : forall (Γ Δ: @Ensemble (BPropF V)), (wpair_derrec (Γ, Δ) -> False) ->
  wpair_derrec (prime_theory Γ Δ, fun x : BPropF V => wBIH_rules (prime_theory Γ Δ, x) -> False) ->
   False.
Proof.
intros. destruct H0. destruct H0. destruct H1. simpl in H1. simpl in H2.
apply closeder_fst_Lind_pair in H2. 2: auto.
pose (list_primeness_fst_Lind_pair Γ Δ H x H2). destruct o.
- assert (wBIH_rules (prime_theory Γ Δ, Bot V)). apply Id.
  apply IdRule_I. auto. apply Consist_prime_theory in H4. auto. auto.
- destruct H3. destruct H3. pose (H1 x0). apply f in H3. auto. apply Id.
  apply IdRule_I. auto.
Qed.

(* The RHS of a prime pair is the complement of the LHS and is an extension of the RHS of the init. *)

Lemma Compl_prime_theory_extens : forall (Γ Δ: @Ensemble (BPropF V)) x,
     (wpair_derrec (Γ, Δ) -> False) -> In (BPropF V) Δ x -> In (BPropF V) (Complement _ (prime_theory Γ Δ)) x.
Proof.
intros. destruct (classic (In (BPropF V) (Complement (BPropF V) (prime_theory Γ Δ)) x)) ; auto.
exfalso. unfold Complement in H1. assert (In (BPropF V) (prime_theory Γ Δ) x).
destruct (classic (In (BPropF V) (prime_theory Γ Δ) x)) ; auto. exfalso. apply H1.
unfold In. auto.
assert (exists n, wpair_derrec (nprime_theory Γ Δ n, Δ)).
{ unfold prime_theory in H2. inversion H2. exists x0.
  exists [x].
  simpl. repeat split. apply NoDup_cons ; auto ; apply NoDup_nil.
  intros. inversion H4. subst. auto. inversion H5.
  apply MP with (ps:=[(nprime_theory Γ Δ x0, Imp x (Or x (Bot V)));(nprime_theory Γ Δ x0, x)]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Ax. apply AxRule_I.
  apply RA2_I. exists x. exists (Bot V). auto. inversion H5.
  subst. 2: inversion H6. apply Id. apply IdRule_I. auto. }
destruct H3.
apply Under_nprime_theory with (n:=x0) in H ; auto.
Qed.

Lemma Lindenbaum_lemma : forall (Γ Δ: @Ensemble (BPropF V)),
    (wpair_derrec (Γ, Δ) -> False) ->
    (exists Γm Δm, Included _ Γ Γm /\
                   Included _ Δ Δm /\
                   complete (Γm, Δm) /\
                   (wpair_derrec (Γm, Δm) -> False)).
Proof.
intros Γ Δ notder.
exists (prime_theory Γ Δ). exists (fun x => (wBIH_rules ((prime_theory Γ Δ), x) -> False)).
repeat split.
- intro. apply prime_theory_extens.
- intro. intro. unfold In. intro. pose (Compl_prime_theory_extens _ _ x notder H).
  unfold Complement in i. unfold In in i. apply closeder_fst_Lind_pair in H0. apply i. auto. auto.
- apply Complete_Lind_pair ; auto.
- apply Under_Lind_pair ; auto.
Qed.





