Require Import K_Syntax.
Require Import wKS_calc.
Require Import List.
Export ListNotations.

Require Import genT.
Require Import ddT.
Require Import gen_tacs.
Require Import existsT.
Require Import univ_gen_ext.
Require Import dd_fc.
Require Import PeanoNat.
Require Import Lia.
Require Import wKS_remove_list.
Require Import wKS_list_lems.
Require Import List_lemmasT.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

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

Lemma NoDup_incl_lengthT : forall (l l' : list MPropF), NoDup l -> incl l l' ->
          ((length l < length l') + (length l = length l')).
Proof.
induction l.
- intros. destruct l'.
  * right. auto.
  * left. simpl. lia.
- induction l' ; intros.
  * exfalso. assert (In a (a :: l)). apply in_eq. pose (H0 a H1). inversion i.
  * simpl. destruct (eq_dec_form a a0).
    + subst. assert (NoDup l). inversion H. assumption. assert (incl l l').
      unfold incl. intros. assert (In a (a0 :: l)). apply in_cons. assumption.
      apply H0 in H3. inversion H3. subst. exfalso. inversion H. apply H6. assumption. assumption.
      pose (IHl _ H1 H2). destruct s. left. lia. right. lia.
    + destruct (In_dec l a0).
      { destruct (In_dec l' a0).
        - assert (NoDup l). inversion H. assumption. assert (incl l l'). unfold incl.
          intros. assert (In a1 (a :: l)). apply in_cons. assumption. apply H0 in H3.
          inversion H3. subst. assumption. assumption. pose (IHl _ H1 H2). destruct s.
          left. lia. right. lia.
        - assert (NoDup l). inversion H. assumption. assert (incl l (a0 :: l')).
          unfold incl. intros. assert (In a1 (a :: l)). apply in_cons. assumption.
          apply H0 in H3. assumption. assert (In a l'). assert (In a (a :: l)).
          apply in_eq. apply H0 in H3. inversion H3. subst. exfalso. apply n. reflexivity.
          assumption. apply in_split in H3. destruct (eq_dec_nat (length l) (length l')).
          * subst. right. auto.
          * left. destruct H3. destruct H3. subst.
            rewrite app_length. simpl. assert (incl l (a0 :: x ++ x0)). unfold incl.
            intros. assert (In a1 (a :: l)). apply in_cons. assumption. apply H0 in H4.
            inversion H4. subst. apply in_eq. apply in_app_or in H5. destruct H5.
            apply in_cons. apply in_or_app. auto. inversion H5. subst. exfalso. inversion H.
            apply H8. assumption. apply in_cons. apply in_or_app. auto.
            rewrite app_length in n0. simpl in n0.
            pose (IHl _ H1 H3). destruct s. 
            + simpl in l0. rewrite app_length in l0. lia.
            + exfalso. apply n0. simpl in e. rewrite app_length in e. lia.  }
      { assert (incl l l'). unfold incl. intros. assert (In a1 (a :: l)). apply in_cons. assumption.
        apply H0 in H2. inversion H2. subst. exfalso. apply f. assumption. assumption.
        assert (NoDup l). inversion H. assumption. pose (IHl _ H2 H1). destruct s.
        - left. lia.
        - right. lia. }
Qed.


(* First, let us define the first part of our measure. This number is simply
   the number of implication symbols in a sequent.

   To define it, we need to define the number of implications in a formula. *)

Fixpoint n_imp_subformF (A : MPropF) : nat :=
match A with
 | # P => 0
 | Bot => 0
 | Imp B C => 1 + (n_imp_subformF B) + (n_imp_subformF C)
 | Box B => (n_imp_subformF B)
end.

(* With this definition in hand, we can then straightforwardly define the number
   of implications in a list of formulae. *)

Fixpoint n_imp_subformLF (l : list MPropF) : nat :=
match l with
  | [] => 0
  | h :: t => (n_imp_subformF h) + (n_imp_subformLF t)
end.

(* Then the definition we were initially looking for can be reached: *)

Definition n_imp_subformS (s : Seq) : nat :=
    (n_imp_subformLF (fst s)) + (n_imp_subformLF (snd s)).

(* It is clear that n_imp_subformS counts the occurrences of implications in a
   sequent s. As a consequence, if that number is 0 we know for sure that the
   rules for implication on the left or right cannot be applied upwards on s.
   This is the meaning of the lemma n_imp_subformS_is_0. 

   But first we need a preliminary lemma which claims that if an implication is
   in a list, then n_imp_subformLF of that list is higher than one.*)

Lemma In_n_imp_subformLF_is_non_0 (l : list MPropF) :
    forall A B, (In (Imp A B) l) -> (le 1 (n_imp_subformLF l)).
Proof.
intros A B Hin. induction l.
- inversion Hin.
- inversion Hin.
  * subst. simpl. apply Le.le_n_S. apply le_0_n.
  * pose (IHl H). simpl. destruct l0.
    + rewrite Nat.add_1_r. apply Le.le_n_S. apply le_0_n.
    + rewrite <- plus_n_Sm. apply Le.le_n_S. apply le_0_n.
Qed.

Theorem n_imp_subformS_is_0 (s : Seq) :
    (n_imp_subformS s) = 0 -> (existsT2 ps, (ImpRRule ps s) + (ImpLRule ps s)) -> False.
Proof.
intros is0 RA. destruct RA. destruct s0.
- inversion i. subst. unfold n_imp_subformS in is0. simpl in is0.
  assert (n_imp_subformLF (Δ0 ++ A --> B :: Δ1) = 0). lia.
  assert (In (A --> B) (Δ0 ++ A --> B :: Δ1)). apply in_or_app. right. apply in_eq.
  pose (In_n_imp_subformLF_is_non_0 (Δ0 ++ A --> B :: Δ1) A B H0). lia.
- inversion i. subst.
  assert (In (A --> B) (Γ0 ++ A --> B :: Γ1)). apply in_or_app. right. apply in_eq.
  pose (In_n_imp_subformLF_is_non_0 (Γ0 ++ A --> B :: Γ1) A B H). unfold n_imp_subformS in is0.
  simpl in is0. assert (n_imp_subformLF (Δ0 ++ Δ1) = 0). lia. lia.
Qed.

Lemma n_imp_subformLF_dist_app : forall l1 l2, n_imp_subformLF (l1 ++ l2) =
                                               plus (n_imp_subformLF l1) (n_imp_subformLF l2).
Proof.
induction l1.
- intros. auto.
- intros. simpl. rewrite IHl1. lia.
Qed.

Lemma n_imp_nobox_gen_ext : forall l1 l2, nobox_gen_ext l1 l2 ->
                                               (n_imp_subformLF l1 <= n_imp_subformLF l2).
Proof.
intros. induction X.
- simpl. lia.
- simpl. lia.
- simpl. lia.
Qed.

Lemma n_imp_unboxed : forall l, (n_imp_subformLF (unboxed_list l) <= n_imp_subformLF l).
Proof.
induction l.
- simpl. lia.
- simpl. destruct a ; simpl ; lia.
Qed.


(* Second, let us define the second part of our measure. This number is simply
   the number of box symbols in a sequent.

   To define it, we need to define the number of boxes in a formula. *)

Fixpoint n_box_subformF (A : MPropF) : nat :=
match A with
 | # P => 0
 | Bot => 0
 | Imp B C => (n_box_subformF B) + (n_box_subformF C)
 | Box B => 1 + (n_box_subformF B)
end.

(* With this definition in hand, we can then straightforwardly define the number
   of boxes in a list of formulae. *)

Fixpoint n_box_subformLF (l : list MPropF) : nat :=
match l with
  | [] => 0
  | h :: t => (n_box_subformF h) + (n_box_subformLF t)
end.

(* The the definition we were initially looking for can be reached: *)

Definition n_box_subformS (s : Seq) : nat :=
    (n_box_subformLF (fst s)) + (n_box_subformLF (snd s)).

(* We prove some lemmas about these notions. *)

Lemma In_n_box_subformLF_is_non_0 (l : list MPropF) :
    forall A, (In (Box A) l) -> (le 1 (n_box_subformLF l)).
Proof.
intros A Hin. induction l.
- inversion Hin.
- inversion Hin.
  * subst. simpl. apply Le.le_n_S. apply le_0_n.
  * pose (IHl H). simpl. destruct l0.
    + rewrite Nat.add_1_r. apply Le.le_n_S. apply le_0_n.
    + rewrite <- plus_n_Sm. apply Le.le_n_S. apply le_0_n.
Qed.

Theorem n_box_subformS_is_0 (s : Seq) :
    (n_box_subformS s) = 0 -> (existsT2 ps, (wKRRule ps s)) -> False.
Proof.
intros is0 RA. destruct RA. inversion w. subst. unfold n_box_subformS in is0.
simpl in is0.
assert (n_box_subformLF (Δ0 ++ Box A :: Δ1) = 0). lia.
assert (In (Box A) (Δ0 ++ Box A :: Δ1)). apply in_or_app. right. apply in_eq.
pose (In_n_box_subformLF_is_non_0 (Δ0 ++ Box A :: Δ1) A H1). lia.
Qed.

Lemma n_box_subformLF_dist_app : forall l1 l2, n_box_subformLF (l1 ++ l2) =
                                               plus (n_box_subformLF l1) (n_box_subformLF l2).
Proof.
induction l1.
- intros. auto.
- intros. simpl. rewrite IHl1. lia.
Qed.

Lemma n_box_nobox_gen_ext : forall l1 l2, nobox_gen_ext l1 l2 ->
                                               (n_box_subformLF l1 <= n_box_subformLF l2).
Proof.
intros. induction X.
- simpl. lia.
- simpl. lia.
- simpl. lia.
Qed.

Lemma n_box_unboxed : forall l, (n_box_subformLF (unboxed_list l) <= n_box_subformLF l).
Proof.
induction l.
- simpl. lia.
- simpl. destruct a ; simpl ; lia.
Qed.


(* We can consequently define our measure on sequents: *)

Definition term_meas (s : Seq) : nat :=
  (n_imp_subformS s) + (n_box_subformS s).




(* Third, we need to prove that if no wKS rule is applicable to a sequent s,
   then its derivations have a height equal to 0. *)

Theorem no_wKS_rule_applic : forall s, (forall ps, (wKS_rules ps s) -> False) ->
                                 forall (D : wKS_drv s), derrec_height D = 0.
Proof.
intros s noRA D. induction D.
- auto.
- exfalso. apply noRA with (ps:=ps). assumption.
Qed.