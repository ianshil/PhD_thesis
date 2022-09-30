Require Import List.
Require Import ListDec.
Export ListNotations.

Require Import genT.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import K_Syntax.
Require Import K_GHC.
Require Import K_logics.
Require Import K_extens_interactions.

Lemma wThm_irrel : forall A B Γ, wKH_prv (Γ, A --> (B --> A)).
Proof.
intros A B Γ. apply Ax. apply AxRule_I. apply MA2_I. exists A. exists B. auto.
Qed.

Lemma wimp_Id_gen : forall A Γ, wKH_prv (Γ, A --> A).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, (((A --> A) --> A) --> A)  --> (A --> A));(Γ, (((A --> A) --> A) --> A))]).
2: apply MPRule_I. intros. inversion H ; subst.
apply MP with (ps:=[(Γ, (A --> ((A --> A) --> A)) --> (((A --> A) --> A) --> A) --> (A --> A));(Γ, (A --> ((A --> A) --> A)))]).
2: apply MPRule_I. intros. inversion H0 ; subst.
apply Ax. apply AxRule_I. apply MA1_I. exists A.
exists ((A --> A) --> A). exists A. auto. inversion H1. 2: inversion H2. subst.
apply Ax. apply AxRule_I. apply MA2_I. exists A.
exists (A --> A). auto. inversion H0. subst. 2: inversion H1.
apply Ax. apply AxRule_I. apply MA3_I. exists A. exists A. auto.
Qed.

Lemma Help8 : forall A B C D Γ,
  wKH_prv (Γ, (((A --> B) --> (C --> B)) --> D) --> ((C --> A) --> D)).
Proof.
intros.
apply MP with (ps:=[(Γ, ((C --> A) --> (A --> B) --> (C --> B)) --> ((((A --> B) --> (C --> B)) --> D) --> (C --> A) --> D));
(Γ, ((C --> A) --> (A --> B) --> (C --> B)))]).
2: apply MPRule_I. intros.
inversion H ; subst. apply Ax. apply AxRule_I. apply MA1_I.
exists (C --> A). exists ((A --> B) --> C --> B). exists D. auto.
inversion H0. subst. apply Ax. apply AxRule_I. apply MA1_I. exists C. exists A.
exists B. auto. inversion H1.
Qed.

Lemma Help10 : forall A B C Γ,
  wKH_prv (Γ, ((A --> B) --> C) --> (B --> C)).
Proof.
intros.
apply MP with (ps:=[(Γ, (B --> (A --> B)) --> ((A --> B) --> C) --> (B --> C));
(Γ, B --> (A --> B))]).
2: apply MPRule_I. intros.
inversion H ; subst. apply Ax. apply AxRule_I. apply MA1_I. exists B. exists (A --> B).
exists C. auto.
inversion H0. subst. apply Ax. apply AxRule_I. apply MA2_I. exists B. exists A ; auto.
inversion H1.
Qed.

Lemma Help33 : forall A B C D Γ,
  wKH_prv (Γ, (A --> (D --> C)) --> ((B --> D) --> (A --> (B --> C)))).
Proof.
intros.
apply MP with (ps:=[(Γ, ((((D --> C) --> (B --> C)) --> (A --> (B --> C)))--> ((B --> D) --> (A --> (B --> C)))) --> ((A --> (D --> C)) --> ((B --> D) --> (A --> (B --> C)))));
(Γ, (((D --> C) --> (B --> C)) --> (A --> (B --> C)))--> ((B --> D) --> (A --> (B --> C))))]).
2: apply MPRule_I. intros.
inversion H ; subst. apply Help8.
inversion H0. subst. apply Help8.
inversion H1.
Qed.

Lemma Contr_imp : forall A B Γ,
  wKH_prv (Γ, (A --> A --> B) --> (A --> B)).
Proof.
intros.
apply MP with (ps:=[(Γ, ((((A --> B) --> B)  --> (A --> B)) --> (A --> B)) --> ((A --> A --> B) --> (A --> B)));
(Γ, (((A --> B) --> B)  --> (A --> B)) --> (A --> B))]).
2: apply MPRule_I. intros. inversion H. subst. apply Help8.
inversion H0. subst. 2: inversion H1. apply Ax. apply AxRule_I.
apply MA3_I. exists (A --> B). exists B. auto.
Qed.

Lemma Help105 : forall A B Γ,
  wKH_prv (Γ, ((A --> B) --> A) -->  ((A --> B) --> B)).
Proof.
intros.
apply MP with (ps:=[(Γ, (((A --> B) --> (A --> B) --> B) --> ((A --> B) --> B)) --> ((A --> B) --> A) -->  ((A --> B) --> B));
(Γ, ((A --> B) --> (A --> B) --> B) --> ((A --> B) --> B))]).
2: apply MPRule_I. intros. inversion H. subst.
apply Help8. inversion H0. 2: inversion H1. subst. apply Contr_imp.
Qed.

Lemma Help316 : forall A B Γ,
  wKH_prv (Γ, A --> (A --> B) --> B).
Proof.
intros.
apply MP with (ps:=[(Γ, (((A --> B) --> A) --> ((A --> B) --> B)) --> (A --> (A --> B) --> B));
(Γ, ((A --> B) --> A) --> ((A --> B) --> B))]).
 2: apply MPRule_I. intros. inversion H. subst.
apply Help10. inversion H0. subst. apply Help105.
inversion H1.
Qed.

Lemma Swap_imp : forall A B C Γ,
  wKH_prv (Γ, (A --> B --> C) --> (B --> A --> C)).
Proof.
intros.
apply MP with (ps:=[(Γ, (B --> (B --> C) --> C) --> ((A --> B --> C) --> B --> A --> C));
(Γ, B --> (B --> C) --> C)]).
2: apply MPRule_I. intros. inversion H.
subst. apply Help33. inversion H0. subst. apply Help316.
inversion H1.
Qed.

Lemma MetaSwap_imp : forall A B C Γ,
  wKH_prv (Γ, A --> B --> C) ->
  wKH_prv (Γ, B --> A --> C).
Proof.
intros.
apply MP with (ps:=[(Γ, (A --> B --> C) --> (B --> A --> C));
(Γ, A --> B --> C)]).
2: apply MPRule_I. intros. inversion H0.
subst. apply Swap_imp. inversion H1. subst. auto.
inversion H2.
Qed.

Lemma Trans_imp : forall A B C Γ,
  wKH_prv (Γ, (A --> B --> C) --> (A --> B) --> A --> C).
Proof.
intros.
apply MP with (ps:=[(Γ, ((B --> A --> C) --> (A --> B) --> A --> C) --> ((A --> B --> C) --> (A --> B) --> A --> C));
(Γ, (B --> A --> C) --> (A --> B) --> A --> C)]). 2: apply MPRule_I.
intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((A --> B --> C) --> (B --> A --> C)) --> ((B --> A --> C) --> (A --> B) --> A --> C) --> ((A --> B --> C) --> (A --> B) --> A --> C));
(Γ, (A --> B --> C) --> (B --> A --> C))]). 2: apply MPRule_I.
intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply MA1_I. exists (A --> B --> C).
exists (B --> A --> C). exists ((A --> B) --> A --> C). auto. inversion H1.
2: inversion H2. subst. apply Swap_imp. inversion H0.
subst.
apply MP with (ps:=[(Γ, ((A --> B) --> ((B --> A --> C) --> A --> C)) --> ((B --> A --> C) --> (A --> B) --> A --> C));
(Γ, ((A --> B) --> ((B --> A --> C) --> A --> C)))]). 2: apply MPRule_I.
intros. inversion H1. subst. apply Swap_imp.
inversion H2. subst. 2: inversion H3.
apply MP with (ps:=[(Γ,  (((B --> A --> C) --> (A --> A --> C)) --> ((B --> A --> C) --> A --> C))--> ((A --> B) --> (B --> A --> C) --> A --> C));
(Γ, (((B --> A --> C) --> (A --> A --> C)) --> ((B --> A --> C) --> A --> C)))]). 2: apply MPRule_I.
intros. inversion H3. subst.
apply MP with (ps:=[(Γ,  ((A --> B) --> ((B --> A --> C) --> (A --> A --> C))) --> (((B --> A --> C) --> (A --> A --> C)) --> ((B --> A --> C) --> A --> C)) --> ((A --> B) --> (B --> A --> C) --> A --> C));
(Γ, ((A --> B) --> ((B --> A --> C) --> (A --> A --> C))))]). 2: apply MPRule_I.
intros. inversion H4. subst. apply Ax. apply AxRule_I.
apply MA1_I. exists (A --> B). exists (((B --> A --> C) --> (A --> A --> C))).
exists ((B --> A --> C) --> (A --> C)). auto. inversion H5 ; subst.
2: inversion H6. apply Ax. apply AxRule_I. apply MA1_I.
exists A. exists B. exists (A --> C). auto. inversion H4. subst.
2: inversion H5. 2: inversion H1.
apply MP with (ps:=[(Γ, ((A --> A --> C) --> (A --> C)) --> ((B --> A --> C) --> A --> A --> C) --> (B --> A --> C) --> A --> C);
(Γ, ((A --> A --> C) --> (A --> C)))]). 2: apply MPRule_I. intros. inversion H5.
subst.
apply MP with (ps:=[(Γ, (((B --> A --> C) --> A --> A --> C) --> ((A --> A --> C) --> A --> C) --> (B --> A --> C) --> A --> C) --> (((A --> A --> C) --> A --> C) --> ((B --> A --> C) --> A --> A --> C) --> (B --> A --> C) --> A --> C));
(Γ, ((B --> A --> C) --> A --> A --> C) --> ((A --> A --> C) --> A --> C) --> (B --> A --> C) --> A --> C)]).
2: apply MPRule_I. intros. inversion H6. subst. apply Swap_imp. inversion H7.
subst. 2: inversion H8. apply Ax. apply AxRule_I. apply MA1_I.
exists (B --> A --> C). exists (A --> A --> C). exists (A --> C). auto.
inversion H6. 2: inversion H7. subst. apply Contr_imp.
Qed.

Theorem wKH_Detachment_Theorem : forall s,
           (wKH_prv s) ->
           (forall A B Γ, (fst s = Γ) ->
                          (snd s = A --> B) ->
                          wKH_prv  (Union _ Γ (Singleton _ (A)), B)).
Proof.
intros s D. induction D.
(* Id *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst.
  simpl. apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A B);(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Id.
  apply IdRule_I. apply Union_introl. assumption. inversion H2. subst.
  apply Id. apply IdRule_I. apply Union_intror. apply In_singleton. inversion H3.
(* Ax *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst. simpl.
  apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A B);(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
  apply AxRule_I. assumption. inversion H2. subst. apply Id. apply IdRule_I.
  apply Union_intror. apply In_singleton. inversion H3.
(* MP *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. simpl.
  assert (J01: List.In (Γ0, A0 --> A --> B) [(Γ0, A0 --> A --> B); (Γ0, A0)]). apply in_eq.
  assert (J1: Γ0 = Γ0). reflexivity.
  assert (J2: A0 --> A --> B = A0 --> A --> B). reflexivity.
  pose (H0 (Γ0, A0 --> A --> B) J01 A0 (Imp A B) Γ0 J1 J2).
  assert (wKH_prv (Γ0, A --> B)).
  assert (J3: (forall A1 : MPropF, fst (Union _ Γ0 (Singleton _ A0), A --> B) A1 ->
  wKH_prv (Γ0, A1))).
  intro. simpl. intro. inversion H2. subst. apply Id.
  apply IdRule_I. assumption. subst. inversion H3. subst.
  assert (J02: List.In (Γ0, A1) [(Γ0, A1 --> A --> B); (Γ0, A1)]). apply in_cons. apply in_eq.
  pose (H (Γ0, A1) J02). assumption.
  pose (wKH_comp (Union _ Γ0 (Singleton _ A0), A --> B) w Γ0 J3). simpl in w0. assumption.
  apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), (Imp A B));(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A0 (Imp A B));(Union _ Γ0 (Singleton _ A), A0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  assert (J4: Included _ (fst (Γ0, A0 --> A --> B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption. pose (H (Γ0, A0 --> A --> B) J01).
  pose (wKH_monot (Γ0, A0 --> A --> B) w0 (Union _ Γ0 (Singleton _ A)) J4). assumption.
  inversion H5. subst.
  assert (J4: Included _ (fst (Γ0, A0 --> A --> B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption.
  pose (wKH_monot (Γ0, A0)). apply w0. apply H. apply in_cons. apply in_eq.
  auto. inversion H6. inversion H4. subst. apply Id. apply IdRule_I. apply Union_intror.
  apply In_singleton. inversion H5.
(* wNec *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. inversion id2.
Qed.

Theorem wKH_Deduction_Theorem : forall s,
           (wKH_prv s) ->
           (forall A B Γ, (fst s = Union _ Γ (Singleton _ (A))) ->
                          (snd s = B) ->
                          wKH_prv (Γ, A --> B)).
Proof.
intros s D. induction D.
(* Id *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. inversion H0.
  + subst. apply MP with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H2. subst.
    apply wThm_irrel. inversion H3. subst. apply Id. apply IdRule_I. assumption.
    inversion H4.
  + subst. inversion H1. subst. apply wimp_Id_gen.
(* Ax *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl.
  apply MP with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply wThm_irrel. inversion H2. subst.
  apply Ax. apply AxRule_I. assumption. inversion H3.
(* MP *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 --> B0 = A0 --> B0). reflexivity.
  assert (J20: List.In (Union (MPropF) Γ (Singleton (MPropF) A), A0 --> B0) [(Union (MPropF) Γ (Singleton (MPropF) A), A0 --> B0); (Union (MPropF) Γ (Singleton (MPropF) A), A0)]).
  apply in_eq.
  pose (H0 (Union (MPropF) Γ (Singleton (MPropF) A),  A0 --> B0) J20
  A (Imp A0 B0) Γ J1 J2).
  assert (J3: A0 = A0). reflexivity.
  apply MP with (ps:=[(Γ, (A --> A0) --> (A --> B0));(Γ, A --> A0)]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (A --> (A0 --> B0)) --> (A --> A0) --> (A --> B0));(Γ, A --> (A0 --> B0))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply Trans_imp. inversion H4. subst. auto. inversion H5. inversion H3.
  subst.
  assert (J30: List.In (Union (MPropF) Γ (Singleton (MPropF) A), A0) [(Union (MPropF) Γ (Singleton (MPropF) A), A0 --> B0); (Union (MPropF) Γ (Singleton (MPropF) A), A0)]).
  apply in_cons. apply in_eq. assert (J40: A0 = A0). reflexivity.
  pose (H0 (Union (MPropF) Γ (Singleton (MPropF) A), A0) J30
  A A0 Γ J1 J40). auto. inversion H4.
(* wNec *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: wKH_prv (Empty_set _, Box A0)).
  apply wNec with (ps:=[(Empty_set _, A0)]). 2: apply wNecRule_I. assumption.
  assert (J2: Included _ (fst (Empty_set _, Box A0)) Γ). intro. intro. inversion H2.
  pose (wKH_monot (Empty_set _, Box A0) J1 Γ J2). simpl in w.
  apply MP with (ps:=[(Γ, (Box A0) --> A --> (Box A0)); (Γ, Box A0)]).
  2: apply MPRule_I. intros. inversion H2. subst. apply wThm_irrel.
  inversion H3. subst. 2: inversion H4. assumption.
Qed.

Theorem wKH_Detachment_Deduction_Theorem : forall A B Γ,
      wKH_prv (Union _ Γ (Singleton _ (A)), B) <-> wKH_prv (Γ, A --> B).
Proof.
intros. split ; intro.
apply wKH_Deduction_Theorem with (s:=(Union MPropF Γ (Singleton MPropF A), B)) ; auto.
apply wKH_Detachment_Theorem with (s:=(Γ, A --> B)) ; auto.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)

(* Some results about remove. *)

Lemma In_remove : forall (A : MPropF) B (l : list (MPropF)), List.In A (remove eq_dec_form B l) -> List.In A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in H. destruct (eq_dec_form B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : MPropF) B (l : list (MPropF)), InT A (remove eq_dec_form B l) -> InT A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in H. destruct (eq_dec_form B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (MPropF)), NoDup l -> NoDup (remove eq_dec_form A l).
Proof.
intro A. induction l.
- intro. simpl. apply NoDup_nil.
- intro H. simpl. destruct (eq_dec_form A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.


(* To help for the results about sKH. *)

Lemma eq_dec_nat : forall (n m : nat), (n = m) + (n <> m).
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

Lemma thm_irrel_Imp_Box_power : forall (n : nat) (A B : MPropF),
  wKH_prv (Empty_set _, B --> (Imp_Box_power n A B)).
Proof.
induction n ; intros ; simpl.
- apply wThm_irrel.
- pose (wKH_Deduction_Theorem (Singleton _ B,  A --> Imp_Box_power n (Box A) B)).
  apply w ; auto. 2: simpl. clear w.
  pose (wKH_Deduction_Theorem (Union _ (Singleton _ B) (Singleton _ A),  Imp_Box_power n (Box A) B)).
  apply w ; auto. clear w. remember (Union MPropF (Singleton MPropF B) (Singleton MPropF A)) as X.
  apply MP with (ps:=[(X, B --> Imp_Box_power n (Box A) B);(X, B)]).
  2: apply MPRule_I. intros. inversion H. rewrite <- H0.
  pose (wKH_monot (Empty_set _, B --> Imp_Box_power n (Box A) B)). apply w ; auto.
  intro. simpl ; intro. inversion H1. inversion H0. subst. 2: inversion H1.
  apply Id. apply IdRule_I. apply Union_introl. apply In_singleton.
  apply Extensionality_Ensembles. split ; intro ; intros. apply Union_intror ; auto.
  inversion H. inversion H0. auto.
Qed.

Lemma Imp_Box_power_le : forall (n m: nat) (A B : MPropF), (n <= m) ->
  wKH_prv (Empty_set _, (Imp_Box_power n A B) --> (Imp_Box_power m A B)).
Proof.
induction n.
- simpl. destruct m.
  + simpl. intros. apply wimp_Id_gen.
  + intros. simpl. assert (J1: 0 <= m). lia.
     pose (wKH_Deduction_Theorem (Singleton _ (A --> B),  A --> Imp_Box_power m (Box A) B)).
     apply w ; auto. 2: simpl. clear w.
     pose (wKH_Deduction_Theorem (Union _ (Singleton _ (A --> B)) (Singleton _ A),  Imp_Box_power m (Box A) B)).
     apply w ; auto. clear w. remember (Union MPropF (Singleton MPropF (A --> B)) (Singleton MPropF A)) as X.
     apply MP with (ps:=[(X, B --> Imp_Box_power m (Box A) B);(X, B)]).
     2: apply MPRule_I. intros. inversion H0. rewrite <- H1.
     pose (wKH_monot (Empty_set _, B --> Imp_Box_power m (Box A) B)). apply w.
     apply thm_irrel_Imp_Box_power. intro. intros. inversion H2. inversion H1.
     rewrite <- H2. 2: inversion H2.
     apply MP with (ps:=[(X, A --> B);(X, A)]). 2: apply MPRule_I.
     intros. inversion H3. subst. apply Id. apply IdRule_I. apply Union_introl.
     apply In_singleton. inversion H4. subst. 2: inversion H5. apply Id.
     apply IdRule_I. apply Union_intror. apply In_singleton.
     apply Extensionality_Ensembles. split ; intro ; intros. apply Union_intror. auto.
     inversion H0. subst. inversion H1. auto.
- simpl. destruct m.
  + intros. inversion H.
  + intros. simpl.
     pose (wKH_Deduction_Theorem (Singleton _ (A --> Imp_Box_power n (Box A) B),  A --> Imp_Box_power m (Box A) B)).
     apply w ; auto. 2: simpl. clear w.
     pose (wKH_Deduction_Theorem (Union _ (Singleton _ (A --> Imp_Box_power n (Box A) B)) (Singleton _ A),  Imp_Box_power m (Box A) B)).
     apply w ; auto. clear w. remember (Union MPropF (Singleton MPropF (A --> Imp_Box_power n (Box A) B)) (Singleton MPropF A)) as X.
     apply MP with (ps:=[(X, Imp_Box_power n (Box A) B --> Imp_Box_power m (Box A) B);(X, Imp_Box_power n (Box A) B)]).
     2: apply MPRule_I. intros. inversion H0. rewrite <- H1.
     pose (wKH_monot (Empty_set _, Imp_Box_power n (Box A) B --> Imp_Box_power m (Box A) B)). apply w. clear w.
     apply IHn ; lia. intro. intros. inversion H2. inversion H1.
     rewrite <- H2. 2: inversion H2.
     apply MP with (ps:=[(X, A --> Imp_Box_power n (Box A) B);(X, A)]). 2: apply MPRule_I.
     intros. inversion H3. subst. apply Id. apply IdRule_I. apply Union_introl.
     apply In_singleton. inversion H4. subst. 2: inversion H5. apply Id.
     apply IdRule_I. apply Union_intror. apply In_singleton.
     apply Extensionality_Ensembles. split ; intro ; intros. apply Union_intror. auto.
     inversion H0. subst. inversion H1. auto.
Qed.

Lemma Imp_Box_power_MP_deep : forall (n : nat) (A B C : MPropF),
  wKH_prv (Empty_set _, (Imp_Box_power n A B) --> (Imp_Box_power n A (B --> C)) --> (Imp_Box_power n A C)).
Proof.
induction n.
- intros. simpl.
  pose (wKH_Deduction_Theorem (Singleton _ (A --> B),  (A --> B --> C) --> A --> C)).
  apply w ; auto. 2: simpl. clear w.
  pose (wKH_Deduction_Theorem (Union _ (Singleton _ (A --> B)) (Singleton _ (A --> B --> C)),  A --> C)).
  apply w ; auto. clear w.
  pose (wKH_Deduction_Theorem (Union _ (Union _ (Singleton _ (A --> B)) (Singleton _ (A --> B --> C))) (Singleton _ A),  C)).
  apply w ; auto. clear w. remember (Union MPropF (Union MPropF (Singleton MPropF (A --> B)) (Singleton MPropF (A --> B --> C))) (Singleton MPropF A)) as X.
  apply MP with (ps:=[(X, B --> C);(X, B)]). 2: apply MPRule_I.
  intros. inversion H. rewrite <- H0.
  apply MP with (ps:=[(X, A --> B --> C);(X, A)]). 2: apply MPRule_I.
  intros. inversion H1. rewrite <- H2. apply Id. apply IdRule_I.
  subst. apply Union_introl. apply Union_intror. apply In_singleton.
  inversion H2. rewrite <- H3. apply Id. apply IdRule_I. subst.
  apply Union_intror. apply In_singleton. inversion H3. inversion H0.
  rewrite <- H1. apply MP with (ps:=[(X, A --> B);(X, A)]).
  intros. 2: apply MPRule_I. inversion H2. rewrite <- H3. apply Id.
  apply IdRule_I. subst. apply Union_introl. apply Union_introl. apply In_singleton.
  inversion H3. rewrite <- H4. apply Id. apply IdRule_I. subst. apply Union_intror.
  apply In_singleton. inversion H4. inversion H1. apply Extensionality_Ensembles.
  split. intro. intros. inversion H. subst. apply Union_intror. apply In_singleton.
  intro. intros. inversion H. subst. inversion H0. subst. auto.
- intros. simpl.
  pose (wKH_Deduction_Theorem (Singleton _ (A --> Imp_Box_power n (Box A) B),  (A --> (Imp_Box_power n (Box A) (B --> C))) --> A --> Imp_Box_power n (Box A) C)).
  apply w ; auto. 2: simpl. clear w.
  pose (wKH_Deduction_Theorem (Union _ (Singleton _ (A --> Imp_Box_power n (Box A) B)) (Singleton _ (A --> (Imp_Box_power n (Box A) (B --> C)))),  A --> Imp_Box_power n (Box A) C)).
  apply w ; auto. clear w.
  pose (wKH_Deduction_Theorem (Union _ (Union _ (Singleton _ (A --> Imp_Box_power n (Box A) B)) (Singleton _ (A --> (Imp_Box_power n (Box A) (B --> C))))) (Singleton _ A),  Imp_Box_power n (Box A) C)).
  apply w ; auto. clear w. remember (Union MPropF (Union MPropF (Singleton MPropF (A --> Imp_Box_power n (Box A) B)) (Singleton MPropF (A --> (Imp_Box_power n (Box A) (B --> C))))) (Singleton MPropF A)) as X.
  apply MP with (ps:=[(X, (Imp_Box_power n (Box A) (B --> C)) --> Imp_Box_power n (Box A) C);
  (X, (Imp_Box_power n (Box A) (B --> C)))]). 2: apply MPRule_I.
  intros. inversion H. rewrite <- H0.
  apply MP with (ps:=[(X, (Imp_Box_power n (Box A) B) --> (Imp_Box_power n (Box A) (B --> C) --> Imp_Box_power n (Box A) C));(X, Imp_Box_power n (Box A) B)]). 2: apply MPRule_I.
  intros. inversion H1. rewrite <- H2.
  pose (wKH_monot ((Empty_set _, Imp_Box_power n (Box A) B --> Imp_Box_power n (Box A) (B --> C) --> Imp_Box_power n (Box A) C))).
  apply w. apply IHn. intro. simpl. intros. inversion H3.
  inversion H2. rewrite <- H3.
  apply MP with (ps:=[(X, A --> Imp_Box_power n (Box A) B);(X, A)]). 2: apply MPRule_I.
  intros. inversion H4. rewrite <- H5. apply Id. apply IdRule_I.
  subst. apply Union_introl. apply Union_introl. apply In_singleton.
  inversion H5. rewrite <- H6. subst. apply Id. apply IdRule_I.
  apply Union_intror. apply In_singleton. inversion H6. inversion H3.
  inversion H0. rewrite <- H1.
  apply MP with (ps:=[(X, A --> Imp_Box_power n (Box A) (B --> C));(X, A)]). 2: apply MPRule_I.
  intros. inversion H2. rewrite <- H3. subst. apply Id. apply IdRule_I. apply Union_introl.
  apply Union_intror. apply In_singleton. inversion H3. subst. apply Id. apply IdRule_I.
  apply Union_intror. apply In_singleton. inversion H4. inversion H1.
  apply Extensionality_Ensembles. split. intro. intros. inversion H. subst.
  apply Union_intror. apply In_singleton. intro. intros. inversion H. subst. inversion H0. subst. auto.
Qed.

Lemma Distrib_Box_Imp_Box_power : forall (n : nat) (A B : MPropF) Γ,
  wKH_prv (Γ, (Box (Imp_Box_power n A B)) --> (Imp_Box_power n (Box A) (Box B))).
Proof.
induction n ; intros ; cbn.
- apply Ax. apply AxRule_I. apply MA5_I. exists A. exists B. auto.
- pose (wKH_Deduction_Theorem (Union _ Γ (Singleton _ (Box (A --> Imp_Box_power n (Box A) B))), Box A --> Imp_Box_power n (Box (Box A)) (Box B))).
  apply w ; auto. clear w.
  pose (wKH_Deduction_Theorem (Union _ (Union _ Γ (Singleton _ (Box (A --> Imp_Box_power n (Box A) B)))) (Singleton _ (Box A)), Imp_Box_power n (Box (Box A)) (Box B))).
  apply w ; auto. clear w. remember (Union MPropF (Union MPropF Γ (Singleton MPropF (Box (A --> Imp_Box_power n (Box A) B)))) (Singleton MPropF (Box A))) as X.
  apply MP with (ps:=[(X, Box (Imp_Box_power n (Box A) B) --> Imp_Box_power n (Box (Box A)) (Box B));(X, Box (Imp_Box_power n (Box A) B))]).
  2: apply MPRule_I. intros. inversion H. rewrite <- H0.
  pose (wKH_monot (Γ, Box (Imp_Box_power n (Box A) B) --> Imp_Box_power n (Box (Box A)) (Box B))).
  apply w ; cbn ; auto. clear w. subst. intro. intros. apply Union_introl. apply Union_introl. auto.
  inversion H0. rewrite <- H1. 2: inversion H1.
  apply MP with (ps:=[(X, Box A --> Box (Imp_Box_power n (Box A) B));(X, Box A)]).
  2: apply MPRule_I. intros. inversion H2. rewrite <- H3.
  apply MP with (ps:=[(X, Box (A --> Imp_Box_power n (Box A) B) --> Box A --> Box (Imp_Box_power n (Box A) B));(X, Box (A --> Imp_Box_power n (Box A) B))]).
  2: apply MPRule_I. intros. inversion H4. rewrite <- H5. apply Ax. apply AxRule_I.
  apply MA5_I. exists A. exists (Imp_Box_power n (Box A) B). auto. inversion H5.
  rewrite <- H6. apply Id. subst. apply IdRule_I. apply Union_introl. apply Union_intror.
  apply In_singleton. inversion H6. inversion H3. subst. apply Id. apply IdRule_I.
  apply Union_intror. apply In_singleton. inversion H4.
Qed.

(* To help for the completeness of wKH. *)

Lemma NegNeg_elim : forall Γ A, wKH_prv (Γ, (A --> Bot) --> Bot) ->
    wKH_prv (Γ, A).
Proof.
intros.
apply MP with (ps:=[(Γ, ((A --> Bot) --> A) --> A);(Γ, (A --> Bot) --> A)]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply MA3_I. exists A. exists Bot. auto.
inversion H1. subst. 2: inversion H2.
apply wKH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (A --> Bot)), A)) ; auto.
apply MP with (ps:=[(Union MPropF Γ (Singleton MPropF (A --> Bot)), Bot --> A);
(Union MPropF Γ (Singleton MPropF (A --> Bot)), Bot)]).
2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
apply MA4_I. exists A ; auto. inversion H3. subst. 2: inversion H4.
apply wKH_Detachment_Theorem with (s:=(Γ, (A --> Bot) --> Bot)) ; auto.
Qed.

(* To help for the Lindenbaum lemma. *)

Lemma Explosion : forall Γ A B,
  wKH_prv (Γ, (B --> Bot) --> (B --> A)).
Proof.
intros.
apply wKH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (B --> Bot)),  B --> A)) ; auto.
apply wKH_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ (B --> Bot))) (Singleton _ B), A)) ; auto.
remember (Union MPropF (Union MPropF Γ (Singleton MPropF (B --> Bot))) (Singleton MPropF B)) as X.
apply MP with (ps:=[(X, Bot --> A);(X, Bot)]). 2: apply MPRule_I.
intros. inversion H. subst. apply Ax. apply AxRule_I. apply MA4_I. exists A ; auto.
inversion H0. 2: inversion H1. rewrite <- H1.
apply MP with (ps:=[(X, B --> Bot);(X, B)]). 2: apply MPRule_I.
intros. inversion H2. subst. apply Id. apply IdRule_I. apply Union_introl.
apply Union_intror. apply In_singleton. inversion H3. subst.
apply Id. apply IdRule_I. apply Union_intror. apply In_singleton. inversion H4.
Qed.

Lemma All_cases_LEM : forall Γ A B,
  wKH_prv (Γ, ((B --> Bot) --> A) --> (B --> A) --> A).
Proof.
intros.
apply wKH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ ((B --> Bot) --> A)),  (B --> A) --> A)) ; auto.
apply wKH_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ ((B --> Bot) --> A))) (Singleton _ (B --> A)), A)) ; auto.
remember (Union MPropF (Union MPropF Γ (Singleton MPropF ((B --> Bot) --> A))) (Singleton MPropF (B --> A))) as X.
apply NegNeg_elim.
apply wKH_Deduction_Theorem with (s:=(Union _ X (Singleton _ (A --> Bot)), Bot)) ; auto.
remember (Union MPropF X (Singleton MPropF (A --> Bot))) as X0.
apply MP with (ps:=[(X0, A --> Bot);(X0, A)]). 2: apply MPRule_I.
intros. inversion H. rewrite <- H0. apply Id. apply IdRule_I. subst.
apply Union_intror. apply In_singleton. inversion H0. 2: inversion H1.
rewrite <- H1.
apply MP with (ps:=[(X0, (B --> Bot) --> A);(X0, B --> Bot)]). 2: apply MPRule_I.
intros. inversion H2. rewrite <- H3. apply Id. apply IdRule_I. subst.
apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
inversion H3. rewrite <- H4. 2: inversion H4.
apply wKH_Deduction_Theorem with (s:=(Union _ X0 (Singleton _ B), Bot)) ; auto.
apply MP with (ps:=[(Union MPropF X0 (Singleton MPropF B), A --> Bot);
(Union MPropF X0 (Singleton MPropF B), A)]). 2: apply MPRule_I.
intros. inversion H5. rewrite <- H6. apply Id. subst. apply IdRule_I.
apply Union_introl. apply Union_intror. apply In_singleton.
inversion H6. 2: inversion H7. rewrite <- H7.
apply MP with (ps:=[(Union MPropF X0 (Singleton MPropF B), B --> A);
(Union MPropF X0 (Singleton MPropF B), B)]). 2: apply MPRule_I.
intros. inversion H8. rewrite <- H9. apply Id. apply IdRule_I. subst.
apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
inversion H9. subst. apply Id. apply IdRule_I. apply Union_intror. apply In_singleton.
inversion H10.
Qed.



(* Finitarise, shift all formulas on the right, apply wNec, distribute Box,
    shift all boxed formulas on the left. *)

Lemma Imp_list_Imp : forall l Γ A B,
    wKH_prv (Γ, list_Imp (A --> B) l) <->
    wKH_prv (Γ, A --> list_Imp B l).
Proof.
induction l ; simpl ; intros.
- split ; intro ; auto.
- split ; intro.
  * apply wKH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ A), a --> list_Imp B l)) ; auto.
    apply wKH_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ A)) (Singleton _ a), list_Imp B l)) ; auto.
    assert (Union MPropF (Union MPropF Γ (Singleton MPropF A)) (Singleton MPropF a) =
    Union MPropF (Union MPropF Γ (Singleton MPropF a)) (Singleton MPropF A)).
    apply Extensionality_Ensembles. split ; intro ; intros. inversion H0. subst.
    inversion H1. subst. apply Union_introl. apply Union_introl  ; auto. subst.
    inversion H2. subst. apply Union_intror. apply In_singleton. subst. apply Union_introl.
    apply Union_intror. auto. inversion H0. subst. inversion H1. subst. apply Union_introl.
    apply Union_introl. auto. subst. apply Union_intror. auto. subst.
    apply Union_introl. apply Union_intror. auto. rewrite H0.
    apply wKH_Detachment_Theorem with (s:=(Union MPropF Γ (Singleton MPropF a),
    A --> list_Imp B l)) ; auto. apply IHl.
    apply wKH_Detachment_Theorem with (s:=(Γ, a --> list_Imp (A --> B) l)) ; auto.
  * apply wKH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ a), list_Imp (A --> B) l)) ; auto.
    apply IHl.
    apply wKH_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ a)) (Singleton _ A), list_Imp B l)) ; auto.
    assert (Union MPropF (Union MPropF Γ (Singleton MPropF A)) (Singleton MPropF a) =
    Union MPropF (Union MPropF Γ (Singleton MPropF a)) (Singleton MPropF A)).
    apply Extensionality_Ensembles. split ; intro ; intros. inversion H0. subst.
    inversion H1. subst. apply Union_introl. apply Union_introl  ; auto. subst.
    inversion H2. subst. apply Union_intror. apply In_singleton. subst. apply Union_introl.
    apply Union_intror. auto. inversion H0. subst. inversion H1. subst. apply Union_introl.
    apply Union_introl. auto. subst. apply Union_intror. auto. subst.
    apply Union_introl. apply Union_intror. auto. rewrite <- H0. clear H0.
    apply wKH_Detachment_Theorem with (s:=(Union MPropF Γ (Singleton MPropF A),
    a --> list_Imp B l)) ; auto.
    apply wKH_Detachment_Theorem with (s:=(Γ, A --> a --> list_Imp B l)) ; auto.
Qed.

Lemma wKH_Imp_list_Detachment_Deduction_Theorem : forall l (Γ: Ensemble MPropF) A,
    (forall B : MPropF, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
    ((wKH_prv (Γ, A)) <-> (wKH_prv (Empty_set _, list_Imp A l))).
Proof.
induction l ; simpl ; intros.
- split ; intro.
  * assert (Γ = Empty_set MPropF). apply Extensionality_Ensembles.
    split ; intro ; intros. apply H in H1. exfalso ; auto. inversion H1.
    rewrite H1 in H0 ; auto.
  * assert (Γ = Empty_set MPropF). apply Extensionality_Ensembles.
    split ; intro ; intros. apply H in H1. exfalso ; auto. inversion H1.
    rewrite H1 ; auto.
- split ; intro.
  * assert (decidable_eq MPropF). unfold decidable_eq. intros.
    destruct (eq_dec_form x y). subst. unfold Decidable.decidable. auto.
    unfold Decidable.decidable. auto.
    pose (In_decidable H1 a l). destruct d.
    + assert (J0: forall B : MPropF, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
       intros. split ; intro. pose (H B). destruct p. apply o in H3. destruct H3.
       subst. auto. auto. apply H. auto.
       pose (IHl Γ A J0). apply i in H0.
       apply MP with (ps:=[(Empty_set MPropF, (list_Imp A l) --> (a --> list_Imp A l));
       (Empty_set MPropF, list_Imp A l)]).
       2: apply MPRule_I. intros. inversion H3. subst.
       apply Ax. apply AxRule_I. apply MA2_I. exists (list_Imp A l).
       exists a. auto. inversion H4. subst. 2: inversion H5. auto.
    + assert (J0: forall B : MPropF,
       ((fun y : MPropF => In MPropF Γ y /\ y <> a) B -> List.In B l) *
       (List.In B l -> (fun y : MPropF => In MPropF Γ y /\ y <> a) B)).
       intros. split ; intro. destruct H3. pose (H B). destruct p.
       apply o in H3. destruct H3 ; subst. exfalso. apply H4 ; auto.
       auto. split ; auto. apply H ; auto. intro. subst. auto.
       pose (IHl (fun y => (In _ Γ y) /\ (y <> a)) (a --> A) J0).
       destruct i. apply Imp_list_Imp. apply H3.
       apply wKH_Deduction_Theorem with (s:=(Γ, A)) ; simpl ; auto.
       apply Extensionality_Ensembles. split ; intro ; intros. unfold In.
       destruct (eq_dec_form a x). subst. apply Union_intror. apply In_singleton.
       apply Union_introl. unfold In. split ; auto. inversion H5. subst.
       inversion H6. auto. subst. inversion H6. subst. apply H. auto.
  * assert (decidable_eq MPropF). unfold decidable_eq. intros.
    destruct (eq_dec_form x y). subst. unfold Decidable.decidable. auto.
    unfold Decidable.decidable. auto.
    pose (In_decidable H1 a l). destruct d.
    + assert (J0: forall B : MPropF, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
       intros. split ; intro. pose (H B). destruct p. apply o in H3. destruct H3.
       subst. auto. auto. apply H. auto.
       apply Imp_list_Imp in H0.
       pose (IHl Γ (a --> A)).
       apply MP with (ps:=[(Γ, a --> A);(Γ, a)]).
       2: apply MPRule_I. intros. inversion H3. subst. apply i. intros.
       split ; intros. pose (H B). destruct p. apply o in H4. destruct H4 ; subst.
       auto. auto. apply H. auto. auto. inversion H4 ; subst.
       apply Id. apply IdRule_I. apply H. auto. inversion H5.
    + assert (J0: forall B : MPropF,
       ((fun y : MPropF => In MPropF Γ y /\ y <> a) B -> List.In B l) *
       (List.In B l -> (fun y : MPropF => In MPropF Γ y /\ y <> a) B)).
       intros. split ; intro. destruct H3. pose (H B). destruct p.
       apply o in H3. destruct H3 ; subst. exfalso. apply H4 ; auto.
       auto. split ; auto. apply H ; auto. intro. subst. auto.
       pose (IHl (fun y => (In _ Γ y) /\ (y <> a)) (a --> A) J0).
       destruct i. apply Imp_list_Imp in H0. apply H4 in H0.
       pose (wKH_Detachment_Theorem (fun y : MPropF => In MPropF Γ y /\ y <> a, a --> A)
       H0 a A (fun y : MPropF => In MPropF Γ y /\ y <> a)). simpl in w.
       assert (Γ = Union MPropF (fun y : MPropF => In MPropF Γ y /\ y <> a)
       (Singleton MPropF a)).
       apply Extensionality_Ensembles. split ; intro ; intros. unfold In.
       destruct (eq_dec_form a x). subst. apply Union_intror. apply In_singleton.
       apply Union_introl. unfold In. split ; auto. inversion H5. subst.
       inversion H6. auto. subst. inversion H6. subst. apply H. auto.
       rewrite H5. apply w ; auto.
Qed.

Lemma K_list_Imp : forall l Γ A,
wKH_rules (Γ, Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)).
Proof.
induction l ; simpl ; intros.
- apply wimp_Id_gen.
- apply wKH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (Box (a --> list_Imp A l))),  Box a --> list_Imp (Box A) (Box_list l))) ; auto.
  apply wKH_Deduction_Theorem with (s:=(Union _ (Union _ Γ (Singleton _ (Box (a --> list_Imp A l)))) (Singleton _ (Box a)),  list_Imp (Box A) (Box_list l))) ; auto.
  remember (Union MPropF (Union MPropF Γ (Singleton MPropF (Box (a --> list_Imp A l)))) (Singleton MPropF (Box a))) as X.
  apply MP with (ps:=[(X, Box (list_Imp A l) --> list_Imp (Box A) (Box_list l));(X,Box (list_Imp A l))]).
  2: apply MPRule_I. intros. inversion H. rewrite <- H0. auto.
  inversion H0. 2: inversion H1. rewrite <- H1.
  apply MP with (ps:=[(X, Box a --> Box (list_Imp A l));(X, Box a)]).
  2: apply MPRule_I. intros. inversion H2. rewrite <- H3.
  apply MP with (ps:=[(X, Box (a --> list_Imp A l) --> (Box a --> Box (list_Imp A l)));(X, Box (a --> list_Imp A l))]).
  2: apply MPRule_I. intros. inversion H4. rewrite <- H5. apply Ax.
  apply AxRule_I. apply MA5_I. exists a. exists (list_Imp A l). auto.
  inversion H5. subst. apply Id. apply IdRule_I. apply Union_introl.
  apply Union_intror. apply In_singleton. inversion H6.
  inversion H3. subst. apply Id. apply IdRule_I. apply Union_intror.
  apply In_singleton. inversion H4.
Qed.

Lemma Box_distrib_list_Imp : forall l A,
    wKH_prv (Empty_set MPropF, list_Imp A l) ->
    wKH_prv (Empty_set MPropF, list_Imp (Box A) (Box_list l)).
Proof.
induction l ; simpl ; intros.
- apply wNec with (ps:=[(Empty_set MPropF, A)]).
  2: apply wNecRule_I. intros. inversion H0 ; subst ; auto.
  inversion H1.
- apply MP with (ps:=[(Empty_set MPropF, (Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)) --> (Box a --> list_Imp (Box A) (Box_list l)));
  (Empty_set MPropF, Box (list_Imp A l) --> list_Imp (Box A) (Box_list l))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Empty_set MPropF, (Box a --> Box (list_Imp A l)) --> ((Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)) --> (Box a --> list_Imp (Box A) (Box_list l))));
  (Empty_set MPropF, Box a --> Box (list_Imp A l))]).
  2: apply MPRule_I. intros. inversion H1. subst.
  apply Ax. apply AxRule_I. apply MA1_I. exists (Box a).
  exists (Box (list_Imp A l)). exists (list_Imp (Box A) (Box_list l)). auto.
  inversion H2 ; subst. 2: inversion H3.
  apply MP with (ps:=[(Empty_set MPropF, Box (a --> (list_Imp A l)) --> (Box a --> Box (list_Imp A l)));
  (Empty_set MPropF, Box (a --> (list_Imp A l)))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply Ax. apply AxRule_I. apply MA5_I. exists a. exists (list_Imp A l).
  auto. inversion H4. subst. 2: inversion H5.
  apply wNec with (ps:=[(Empty_set MPropF, a --> list_Imp A l)]).
  2: apply wNecRule_I. intros. inversion H5 ; subst. 2: inversion H6.
  auto. inversion H1 ; subst. 2: inversion H2. apply K_list_Imp.
Qed.

Lemma In_list_In_Box_list : forall l A,
    List.In A l -> List.In (Box A) (Box_list l).
Proof.
induction l ; intros ; simpl.
- inversion H.
- inversion H ;  subst ; auto.
Qed.

Lemma In_Box_list_In_list : forall l A,
     List.In A (Box_list l) -> (exists B, List.In B l /\ A = Box B).
Proof.
induction l ; simpl ; intros.
- inversion H.
- destruct H ; subst. exists a. split ; auto. apply IHl in H.
  destruct H. destruct H. subst. exists x ; auto.
Qed.

Lemma K_rule : forall Γ A, wKH_prv (Γ, A) ->
    wKH_prv ((fun x => (exists B, In _ Γ B /\ x = Box B)), Box A).
Proof.
intros. apply wKH_finite in H. simpl in H. destruct H. destruct H. destruct p.
destruct e.
pose (wKH_monot (fun x1 : MPropF => exists B : MPropF, List.In B x0 /\ x1 = Box B, Box A)).
apply w0 ; simpl ; auto. clear w0.
pose (wKH_Imp_list_Detachment_Deduction_Theorem x0 x A H).
apply i0 in w. clear i0.
apply Box_distrib_list_Imp in w.
remember (fun y => exists B : MPropF, List.In B x0 /\ y = Box B) as Boxed_x.
pose (wKH_Imp_list_Detachment_Deduction_Theorem (Box_list x0) Boxed_x  (Box A)).
apply i0 in w ; auto. intros. split ; intro. subst. destruct H1. destruct H1. subst.
simpl. apply In_list_In_Box_list ; auto. subst. apply In_Box_list_In_list in H1.
auto. intro. intros. inversion H0. destruct H1. subst. unfold In.
exists x2 ; split ; auto. apply i. apply H ; auto.
Qed.

