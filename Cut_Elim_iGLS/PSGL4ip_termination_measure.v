Require Import GL4ip_PSGL4ip_calcs.
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
Require Import GL4ip_PSGL4ip_remove_list.
Require Import GL4ip_PSGL4ip_list_lems.
Require Import GL4ip_PSGL4ip_dec.
Require Import List_lemmasT.
Require Import DLW_WO_list_nat.
Require Import Wellfounded.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Definition proj1_sigT2 {A : Type} (P : A -> Type) (e:sigT P) := match e with
                                    | existT _ a b => a
                                    end.

Definition proj2_sigT2 {A : Type} (P : A -> Type) (e : sigT P) :=
  match e return (P (proj1_sigT2 e)) with
  | existT _ a b => b
  end.

Hypothesis eq_dec_propvar : forall x y : V, {x = y}+{x <> y}.

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

Lemma dec_le : forall (n m : nat), (n <= m) + (m <= n).
Proof.
induction n.
- destruct m ; auto. left. lia.
- destruct m ; auto. right ; lia. pose (IHn m). destruct s. left ; lia. right ; lia.
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








(*------------------------------------------------------------------------------------------------------------------------------------------*)








(* First, we define a On/Off measure which checks if the sequent is an instance
    of an identity. If so, it is given 0. If not, it is given 1. This will help show that
    in BoxImpLRule, the measure of the left premise decreases: either it becomes
    an axiom (then decreases, as we cannot apply rule on axioms), or the number
    of usable boxes decreases too (Box A is now appearing as a block ; if it already did
    then the left premise would necessarily be an axiom). *)

Inductive init_switch_ind (s : list MPropF * (MPropF)) (n : nat) : Type :=
 | init : ((IdRule [] s) + (BotLRule [] s)) -> (n = 0) -> init_switch_ind s n
 | notinit : (((IdRule [] s) + (BotLRule [] s)) -> False) -> (n = 1) -> init_switch_ind s n.

Lemma dec_nat_init_switch_ind : forall (s : list MPropF * (MPropF)),
  existsT2 n, (init_switch_ind s n) * ((n = 0) + (n =1)).
Proof.
intro s. destruct (dec_init_rules s).
- exists 0. split ; try apply init ; auto.
- exists 1. split ; try apply notinit ; auto.
Qed.

Definition init_switch (s: list MPropF * (MPropF)) : nat := proj1_sigT2 (dec_nat_init_switch_ind s).

Lemma init_switch_0_or_1 : forall (s : list MPropF * (MPropF)),
 ( init_switch s = 0) + (init_switch s = 1).
Proof.
intro s. unfold init_switch. destruct (dec_nat_init_switch_ind s) ; destruct p.
destruct s0 ; subst ; auto ; simpl.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)








(* I might need to change some things as I used sequents which were pairs of multisets before
    while now I have only one formula on the right. Keep that in mind. *)


(* Second, we intend to define the notion of usable boxed formulae in a sequent. We also
   prove that if this measure is 0 then no GLR rule can be applied to this sequent.

   In the next definitions our aim is to define the list of all boxed subformulae (not
   occurrences) of all the formulae in a sequent. *)

Fixpoint subform_boxesF (A : MPropF) : list MPropF :=
match A with
 | # P => nil
 | Bot => nil
 | And B C => (subform_boxesF B) ++ (remove_list (subform_boxesF B) (subform_boxesF C))
 | Or B C => (subform_boxesF B) ++ (remove_list (subform_boxesF B) (subform_boxesF C))
 | Imp B C => (subform_boxesF B) ++ (remove_list (subform_boxesF B) (subform_boxesF C))
 | Box B => (Box B) :: (subform_boxesF B)
end.

Fixpoint subform_boxesLF (l : list MPropF) : list MPropF :=
match l with
  | nil => nil
  | h :: t => (subform_boxesF h) ++ (remove_list (subform_boxesF h) (subform_boxesLF t))
end.

Definition subform_boxesS (s : Seq) : list MPropF :=
  (subform_boxesLF (fst s)) ++ (remove_list (subform_boxesLF (fst s)) (subform_boxesF (snd s))).

Lemma In_subform_boxesF_box : forall (A B : MPropF), In A (subform_boxesF B) -> is_boxedT A.
Proof.
unfold is_boxedT. intros A B. generalize dependent A. induction B ; intros.
- simpl in H. destruct H.
- simpl in H. destruct H.
- simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. assumption.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. assumption.
- simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. assumption.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. assumption.
- simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. assumption.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. assumption.
- simpl in H. destruct H. exists B. auto. apply IHB in H. assumption.
Qed.

Lemma In_subform_boxesLF_box : forall (A : MPropF) l, In A (subform_boxesLF l) -> is_boxedT A.
Proof.
unfold is_boxedT. intros A l. generalize dependent A. induction l ; intros.
- simpl in H. destruct H.
- simpl in H. apply in_app_or in H. destruct H. apply In_subform_boxesF_box in H. assumption.
  apply In_remove_list_In_list in H. apply IHl. assumption.
Qed.

(* Then next lemmas help us reach our goal. *)

Fixpoint length_form (a: MPropF) : nat :=
match a with
  | # v => 1
  | Bot => 1
  | And a0 a1 => S (length_form a0 + length_form a1)
  | Or a0 a1 => S (length_form a0 + length_form a1)
  | Imp a0 a1 => S (length_form a0 + length_form a1)
  | Box a0 => S (length_form a0)
end.

Lemma S_le_False : forall (n : nat), S n <= n -> False.
Proof.
induction n.
- intro. inversion H.
- intro. apply Le.le_S_n in H. apply IHn. assumption.
Qed.

Lemma in_subform_boxesF_smaller_length_form : forall (A B : MPropF), In A (subform_boxesF B) ->
                (length_form A <= length_form B).
Proof.
intros A B. generalize dependent A. induction B; intros .
- simpl. inversion H.
- simpl. inversion H.
- simpl. simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. lia.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. lia.
- simpl. simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. lia.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. lia.
- simpl. simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. lia.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. lia.
- simpl in H. destruct H. subst. auto. apply IHB in H. simpl. apply le_S. assumption.
Qed.

Lemma contradic_subform_boxesF: forall A l, (l = (subform_boxesF A)) -> (In (Box A) l)  -> False.
Proof.
intros. subst. pose (in_subform_boxesF_smaller_length_form (Box A) A H0).
inversion l.
- apply eq_S_F in H1. assumption.
- simpl in l. apply S_le_False in l. assumption.
Qed.

Lemma NoDup_subform_boxesF : forall A, NoDup (subform_boxesF A).
Proof.
induction A.
- simpl. apply NoDup_nil.
- simpl. apply NoDup_nil.
- simpl. apply add_remove_list_preserve_NoDup. apply IHA1. apply IHA2.
- simpl. apply add_remove_list_preserve_NoDup. apply IHA1. apply IHA2.
- simpl. apply add_remove_list_preserve_NoDup. apply IHA1. apply IHA2.
- simpl. apply NoDup_cons. intro. apply contradic_subform_boxesF in H. assumption.
  reflexivity. apply IHA.
Qed.

Lemma subform_boxesLF_dist_app : forall l1 l2,
        (subform_boxesLF (l1 ++ l2)) =
        (subform_boxesLF l1) ++ (remove_list (subform_boxesLF l1) (subform_boxesLF l2)).
Proof.
induction l1.
- intros l2. simpl. reflexivity.
- intros l2. simpl. rewrite IHl1. repeat rewrite <- app_assoc.
  assert (E: remove_list (subform_boxesF a) (subform_boxesLF l1 ++
             remove_list (subform_boxesLF l1) (subform_boxesLF l2)) =
             remove_list (subform_boxesF a) (subform_boxesLF l1) ++
             remove_list (subform_boxesF a ++ remove_list (subform_boxesF a)
             (subform_boxesLF l1)) (subform_boxesLF l2)).
  { rewrite app_remove_list. rewrite redund_remove_list. rewrite <- remove_list_dist_app. reflexivity. }
  rewrite E. reflexivity.
Qed.

Lemma NoDup_subform_boxesLF : forall l, NoDup (subform_boxesLF l).
Proof.
induction l.
- intros. simpl. apply NoDup_nil.
- intros. simpl. apply add_remove_list_preserve_NoDup. apply NoDup_subform_boxesF.
  apply IHl.
Qed.

Lemma NoDup_subform_boxesS : forall s, NoDup (subform_boxesS s).
Proof.
intro s. unfold subform_boxesS. apply add_remove_list_preserve_NoDup.
apply NoDup_subform_boxesLF. apply NoDup_subform_boxesF.
Qed.

Lemma univ_gen_ext_incl_subform_boxes : forall l1 l2 P, (univ_gen_ext P l1 l2) ->
                                          incl (subform_boxesLF l1) (subform_boxesLF l2).
Proof.
intros. induction X.
- unfold incl. intros. auto.
- unfold incl. intros. simpl in H. simpl. apply in_app_or in H. destruct H.
  * apply in_or_app. left. assumption.
  * apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
    apply in_or_app. right. apply not_removed_remove_list. apply IHX. assumption.
    assumption.
- unfold incl. intros. simpl. destruct (In_dec (subform_boxesF x) a).
  * apply in_or_app. left. assumption.
  * apply in_or_app. right. apply not_removed_remove_list. apply IHX. assumption.
    assumption.
Qed.

Lemma XBoxed_list_same_subform_boxes : forall l,
          incl (subform_boxesLF (XBoxed_list l)) (subform_boxesLF l) /\
          incl (subform_boxesLF l) (subform_boxesLF (XBoxed_list l)).
Proof.
induction l.
- split.
  * unfold incl. intros. simpl in H. inversion H.
  * unfold incl. intros. simpl in H. inversion H.
- split.
  * unfold incl. intros. simpl. simpl in H. apply in_app_or in H. destruct H.
    apply in_or_app. left. destruct a ; simpl in H ; try contradiction.
    simpl. assumption. simpl. assumption. simpl. assumption. simpl. right. assumption. apply In_remove_list_In_list in H.
    apply in_app_or in H. destruct H. apply in_or_app. left. assumption. apply in_or_app.
    right. apply In_remove_list_In_list_not_In_remove_list in H. destruct H. destruct IHl.
    apply H1 in H. apply not_removed_remove_list ; assumption.
  * destruct IHl. unfold incl. intros. simpl in H1. apply in_app_or in H1. destruct H1.
    destruct a ; simpl in H1 ; try contradiction.
    apply in_app_or in H1. destruct H1.
    simpl. apply in_or_app. left. apply in_or_app. left. assumption. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. simpl. apply in_or_app.
    left. apply in_or_app. right. apply not_removed_remove_list ; assumption.
    apply in_app_or in H1. destruct H1.
    simpl. apply in_or_app. left. apply in_or_app. left. assumption. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. simpl. apply in_or_app.
    left. apply in_or_app. right. apply not_removed_remove_list ; assumption.
    apply in_app_or in H1. destruct H1.
    simpl. apply in_or_app. left. apply in_or_app. left. assumption. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. simpl. apply in_or_app.
    left. apply in_or_app. right. apply not_removed_remove_list ; assumption. destruct H1.
    subst. simpl. apply in_or_app. right. apply not_removed_remove_list. apply in_eq.
    intros. apply contradic_subform_boxesF in H1. assumption. auto. simpl. apply in_or_app.
    left. assumption. simpl. apply in_or_app. right. rewrite remove_list_dist_app.
    apply in_or_app. right. apply not_removed_remove_list. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. apply H0 in H1.
    apply not_removed_remove_list ; assumption. intro. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. destruct a ; simpl ; try assumption.
    simpl (unBox_formula (a1 ∧ a2)) in H2. firstorder. simpl (unBox_formula (a1 ∨ a2)) in H2. firstorder.
    simpl (unBox_formula (a1 → a2)) in H2. firstorder. simpl (unBox_formula (Box a)) in H2.
    apply H3. simpl. right. assumption.
Qed.

Lemma In_incl_subform_boxes : forall l A, In A l ->
                  (forall B, In B (subform_boxesF A) -> In B (subform_boxesLF l)).
Proof.
induction l.
- intros. inversion H.
- intros. simpl. inversion H.
  * subst. apply in_or_app. left. assumption.
  * pose (IHl A H1). destruct (In_dec (subform_boxesF a) B).
    + apply in_or_app. left. assumption.
    + apply in_or_app. right. apply not_removed_remove_list. apply i. assumption.
      assumption.
Qed.




(* Now we can define the notion of usable boxed formulae: it is a positive one such that
   it does not appear as a top formula in the LHS of the sequent. To do so, we need to
   define the list of such formulae: *)

Fixpoint top_boxes (l : list MPropF) : list MPropF :=
match l with
  | nil => nil
  | h :: t => match h with
                | Box A => (Box A) :: top_boxes t
                | _ => top_boxes t
              end
end.

Lemma top_boxes_distr_app : forall (l1 l2 : list MPropF),
      top_boxes (l1 ++ l2) = (top_boxes l1) ++ (top_boxes l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l. simpl. reflexivity.
- intro l2. simpl. destruct a ; try apply IHl1.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma top_boxes_incl_list : forall l, incl (top_boxes l) l.
Proof.
induction l.
- simpl. unfold incl. intros. inversion H.
- unfold incl. intros. destruct a.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. destruct H.
    + subst. apply in_eq.
    + apply in_cons. apply IHl. assumption.
Qed.

Lemma in_top_boxes : forall l A, (In A (top_boxes l)) -> (existsT2 B l1 l2, (A = Box B) * (l = l1 ++ A :: l2)).
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. destruct a.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([# v] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([⊥] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([a1 ∧ a2] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([a1 ∨ a2] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([a1 → a2] ++ x0). exists x1. auto.
  * simpl (top_boxes (Box a :: l)) in H. destruct (eq_dec_form (Box a) A).
    + subst. exists a. exists []. exists l. auto.
    + subst. assert (H0 : In A (top_boxes l)). inversion H. exfalso. apply n. assumption.
      assumption. apply IHl in H0. destruct H0. destruct s. destruct s. destruct p.
      subst. exists x. exists ([Box a] ++ x0). exists x1. auto.
Qed.

Lemma box_in_top_boxes : forall l1 l2 A, existsT2 l3 l4, top_boxes (l1 ++ Box A :: l2) = l3 ++ Box A :: l4.
Proof.
intros. exists (top_boxes l1). exists (top_boxes l2). rewrite top_boxes_distr_app. auto.
Qed.

Lemma box_preserv_top_boxes : forall l1 l2 l3 A, top_boxes l1 = l2 ++ Box A :: l3 ->
                                existsT2 l4 l5, l1 = l4 ++ Box A :: l5.
Proof.
induction l1.
- intros. simpl in H. destruct l2 ; inversion H.
- induction l2.
  * intros. rewrite app_nil_l in H. destruct a.
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([# v] ++ x).
      exists x0. subst. auto.
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([⊥] ++ x).
      exists x0. subst. auto.
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 ∧ a2] ++ x).
      exists x0. subst. auto.
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 ∨ a2] ++ x).
      exists x0. subst. auto.
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 → a2] ++ x).
      exists x0. subst. auto.
    + inversion H. exists []. exists l1. auto.
  * intros. destruct a.
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([# v] ++ x).
      exists x0. subst. auto.
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([⊥] ++ x).
      exists x0. subst. auto.
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 ∧ a2] ++ x).
      exists x0. subst. auto.
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 ∨ a2] ++ x).
      exists x0. subst. auto.
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 → a2] ++ x).
      exists x0. subst. auto.
    + inversion H. apply IHl1 in H2. destruct H2. destruct s. subst. exists (Box a :: x). exists x0. auto.
Qed.

Lemma removed_box_exists : forall l1 l2 l3 A,
    (remove_list (top_boxes l1) (top_boxes (l2 ++ Box A :: l3))) = nil ->
    (existsT2 l4 l5, l1 = l4 ++ Box A :: l5).
Proof.
intros. pose (box_in_top_boxes l2 l3 A). repeat destruct s. rewrite e in H.
remember (top_boxes l1) as l. apply remove_list_in_nil in H. destruct H.
destruct s. subst. apply box_preserv_top_boxes in e0. assumption.
Qed.

Lemma is_box_in_top_boxes : forall l A, In A l -> is_boxedT A -> In A (top_boxes l).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  * subst. inversion X. subst. simpl. left. reflexivity.
  * pose (IHl A H0 X). destruct a ; simpl ; try assumption.
    right. assumption.
Qed.







(*  Some more 'macro' lemmas dealing with subform_boxes and top_boxes. *)

Lemma RHS_top_box_is_subformLF : forall (s : Seq) (A : MPropF),
        (In A (top_boxes [snd s])) -> (In A (subform_boxesLF [snd s])).
Proof.
intros s A H. apply in_top_boxes in H. destruct H. repeat destruct s0. destruct p. subst. rewrite e0.
rewrite subform_boxesLF_dist_app. apply in_or_app. pose (In_dec (subform_boxesLF x0) (Box x)).
destruct s0.
- left. assumption.
- right. apply not_removed_remove_list.
  * simpl. left. reflexivity.
  * assumption.
Qed.

Lemma RHS_top_box_is_subform : forall s A, (In A (top_boxes [snd s])) -> (In A (subform_boxesS s)).
Proof.
intros s A H. unfold subform_boxesS. apply RHS_top_box_is_subformLF in H.
apply remove_list_is_in with (l2:=subform_boxesLF (fst s)) in H. simpl in H.
rewrite remove_list_of_nil in H. rewrite app_nil_r in H. assumption.
Qed.







(* Finally, we can define the list of usable boxed formulae. The length of that list is
   the first component of our measure. *)

Definition usable_boxes (s :Seq) : list MPropF :=
   remove_list (top_boxes (fst s)) (subform_boxesS s).

(* We can show that our notion of usable box effectively captures what it is intended to:
   an upper bound on how many GLR rules can be applied to a sequent. To check this, we can
   show that if the number of usable boxes is effectively 0 then no GLR is applicable. This
   is the content of the lemma length_usable_boxes_is_0. *)

Lemma no_RHS_box_no_GLR (s : Seq) :
    (is_boxedT (snd s) -> False) -> (existsT2 ps, GLRRule ps s) -> False.
Proof.
intros notbox RA. destruct RA. inversion g. subst. simpl in notbox.
apply notbox. exists A ; auto.
Qed.

Lemma all_RHS_boxes_are_LHS_boxes_no_GLR (s : Seq) :
    (IdRule [] s -> False) ->  (* This line makes sure that we do PS: no IdB can happen. *)
    (remove_list (top_boxes (fst s)) (top_boxes [snd s])) = nil ->
    (existsT2 ps, GLRRule ps s) -> False.
Proof.
intros noId isnil RA. destruct RA. inversion g. subst. simpl in isnil.
apply noId.
pose (removed_box_exists Γ [] [] A). simpl in s. apply s in isnil. destruct isnil. destruct s0.
subst. apply IdRule_I.
Qed.

Lemma no_usable_boxes_all_RHS_are_LHS (s : Seq) :
    length (usable_boxes s) = 0 -> (remove_list (top_boxes (fst s)) (top_boxes [snd s])) = nil.
Proof.
intro is0. remember (usable_boxes s) as l. destruct l.
- unfold usable_boxes in Heql. symmetry in Heql. rewrite remove_list_is_nil in Heql.
  rewrite remove_list_is_nil. intros. apply RHS_top_box_is_subform in H. apply Heql. assumption.
- inversion is0.
Qed.

Theorem length_usable_boxes_is_0 (s : Seq) :
    length (usable_boxes s) = 0 ->
    (IdRule [] s -> False) ->
    (existsT2 ps, GLRRule ps s) -> False.
Proof.
intros H0 H1. pose (no_usable_boxes_all_RHS_are_LHS s H0).
pose (all_RHS_boxes_are_LHS_boxes_no_GLR H1 e). assumption.
Qed.

Lemma NoDup_usable_boxes : forall s, NoDup (usable_boxes s).
Proof.
intro s. unfold usable_boxes. destruct s. simpl. unfold subform_boxesS.
simpl. pose (NoDup_subform_boxesLF l). pose (NoDup_subform_boxesF m).
pose (add_remove_list_preserve_NoDup n n0). apply remove_list_preserv_NoDup.
assumption.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)








(* Third, let us define a the third part of our measure. It is the ordered list of numbers of
    of occurrences of formulae of all complexity from the maximal complexity of a sequent
    to 0. *)

Inductive weight_test_ind (n : nat) (A : MPropF) (m : nat) : Type :=
  | testpos : (n = weight_form A) -> (m = 1) -> weight_test_ind n A m
  | testneg : (n <> weight_form A) -> (m = 0) -> weight_test_ind n A m.

Lemma dec_weight_test : forall n A,
  existsT2 m, (weight_test_ind n A m) * ((m = 1) + (m = 0)).
Proof.
intros. destruct (eq_dec_nat n (weight_form A)).
- subst. exists 1. split ; auto. apply testpos ; auto.
- exists 0 ; split ; auto. apply testneg ; auto.
Qed.

Definition weight_test n A : nat := proj1_sigT2 ( dec_weight_test n A).

Lemma weight_test_0_or_1 : forall n A,
 (weight_test n A = 0) + (weight_test n A = 1).
Proof.
intros. unfold weight_test. destruct (dec_weight_test n A) ; destruct p ; destruct s ; auto.
Qed.

Fixpoint occ_weight_list (n : nat) (l : list MPropF) : nat :=
match l with
  | nil => 0
  | h :: t => (weight_test n h) + (occ_weight_list n t)
end.

Fixpoint list_occ_weight_list (n : nat) (l : list MPropF): list nat :=
match n with
  | 0 => nil
  | S m => (occ_weight_list (S m) l) :: (list_occ_weight_list m l)
end.

Lemma max_weight_list : forall l, existsT2 n, (forall B, InT B l -> weight_form B <= n) *
                (forall m, (forall B, InT B l -> weight_form B <= m) -> n <= m).
Proof.
induction l.
- simpl. exists 0. split ; auto. intros. inversion H. intros. lia.
- destruct IHl. destruct p. destruct (dec_le x (weight_form a)).
  * exists (weight_form a). split. intros. inversion H ; subst ; auto.
    pose (l0 B H1). lia. intros. apply H. apply InT_eq.
  * exists x. split. intros. inversion H ; subst ; auto. intros. apply l1. intros.
    apply H. apply InT_cons ; auto.
Qed.

Definition seq_list_occ_weight (s : list MPropF * (MPropF)) : list nat :=
          list_occ_weight_list (proj1_sigT2 (max_weight_list (fst s ++ [snd s]))) (fst s ++ [snd s]).








(*------------------------------------------------------------------------------------------------------------------------------------------*)








(* Use Dominique's work, which provides the correct induction principle (essentially formalises
    Shortlex). *)


(* We can thus define the triple which is the measure on sequents we were looking for. *)

Definition less_than3 (s0 s1 : list MPropF * (MPropF)) : Prop :=
     @lex (list nat) (less_than lt) [[init_switch s0];[length (usable_boxes s0)];(seq_list_occ_weight s0)]
                              [[init_switch s1];[length (usable_boxes s1)];(seq_list_occ_weight s1)].

Notation "s0 '<3' s1" := (less_than3 s0 s1) (at level 70).

Fact less_than3_inv l m : l <3 m ->  (init_switch l <  init_switch m) \/
                                                       ((init_switch l = init_switch m) /\ (length (usable_boxes l) < length (usable_boxes m))) \/
                                                       ((init_switch l = init_switch m) /\ (length (usable_boxes l) = length (usable_boxes m)) /\ (less_than lt (seq_list_occ_weight l) (seq_list_occ_weight m))).
Proof.
inversion 1; subst.
- right. inversion H1 ; subst.
  + right. repeat split ; auto. apply lex_cons_inv in H2. destruct H2.
     destruct H0.  apply lex_cons_inv in H2. inversion H2. destruct H0 ; auto.
  + left. split ; auto. apply less_than_inv in H7. destruct H7. simpl in H0. exfalso.
     lia. apply lex_cons_inv in H0. destruct H0. destruct H0. apply lex_cons_inv in H2. inversion H2.
     destruct H0 ; auto.
- left. apply less_than_inv in H5. destruct H5. simpl in H0. exfalso ; lia.
  apply lex_cons_inv in H0. destruct H0. destruct H0. apply lex_cons_inv in H1. inversion H1.
  destruct H0 ; auto.
Qed.


Theorem less_than3_wf : well_founded less_than3.
Proof.
unfold less_than3.
apply wf_inverse_image.
pose (@less_than_wf nat lt Nat.lt_wf_0).
pose (@lex_wf (list nat) (less_than lt) w).
auto.
Qed.


Corollary less_than3_rect (P : (list MPropF * (MPropF)) -> Type)
(HP : forall s, (forall s1, init_switch s1 < init_switch s -> P s1) ->
    (forall s1, (init_switch s1 = init_switch s) -> (length (usable_boxes s1) < length (usable_boxes s)) -> P s1) ->
    (forall s1,  (init_switch s1 = init_switch s) -> (length (usable_boxes s1) = length (usable_boxes s)) -> less_than lt (seq_list_occ_weight s1) (seq_list_occ_weight s) -> P s1) -> P s) s : P s.
Proof.
  induction s as [ s IHs ] using (well_founded_induction_type less_than3_wf).
  apply HP; intros; apply IHs.
  + unfold less_than3. apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto.
  + unfold less_than3. rewrite H. apply lex_skip. apply lex_cons ; auto.
     apply less_than_eq. apply lex_cons ; auto.
  + unfold less_than3. rewrite H. apply lex_skip. rewrite H0. apply lex_skip. apply lex_cons ; auto.
Qed.

Lemma decT_lt : forall m n, (m < n) + ((m < n) -> False).
Proof.
induction m.
- destruct n. right. intro. inversion H. left. lia.
- destruct n. right. intro. inversion H. pose (IHm n). destruct s. left. lia. right. intro. apply f. lia.
Qed.

Theorem less_than3_strong_inductionT:
forall P : (list MPropF * (MPropF)) -> Type,
(forall s0 : list MPropF * (MPropF), (forall s1 : list MPropF * (MPropF), ((s1 <3 s0) -> P s1)) -> P s0) ->
forall s : list MPropF * (MPropF), P s.
Proof.
intros P sIH.
assert (J: (forall s : list MPropF * (MPropF),
    (forall s1, init_switch s1 < init_switch s -> P s1) ->
    (forall s1, (init_switch s1 = init_switch s) -> (length (usable_boxes s1) < length (usable_boxes s)) -> P s1) ->
    (forall s1,  (init_switch s1 = init_switch s) -> (length (usable_boxes s1) = length (usable_boxes s)) -> less_than lt (seq_list_occ_weight s1) (seq_list_occ_weight s) -> P s1) -> P s)).
{ intros. apply sIH. intros. apply less_than3_inv in H. destruct (decT_lt (init_switch s1) (init_switch s)).
   apply X ; auto. assert (init_switch s1 = init_switch s /\ length (usable_boxes s1) < length (usable_boxes s) \/
    init_switch s1 = init_switch s /\
    length (usable_boxes s1) = length (usable_boxes s) /\ less_than lt (seq_list_occ_weight s1) (seq_list_occ_weight s)).
   destruct H ; auto. exfalso ; auto. clear H. destruct (decT_lt (length (usable_boxes s1)) (length (usable_boxes s))).
   apply X0 ; auto. destruct H0 ; destruct H ; auto.
   assert (init_switch s1 = init_switch s /\
     length (usable_boxes s1) = length (usable_boxes s) /\ less_than lt (seq_list_occ_weight s1) (seq_list_occ_weight s)).
   destruct H0 ; auto. destruct H ; auto. exfalso ; auto. clear H0. apply X1. destruct H ; auto. destruct H ; destruct H0 ; auto.
   destruct H. destruct H0 ; auto. }
pose (@less_than3_rect P J) ; auto.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)





(* Useful lemmas *)

Lemma length_max : forall n l, length (list_occ_weight_list n l) = n.
Proof.
induction n.
- intros. simpl ; auto.
- intros. simpl. pose (IHn l). lia.
Qed.

Lemma max_less_length : forall l1 l2 n m, n < m -> length (list_occ_weight_list n l1) < length (list_occ_weight_list m l2).
Proof.
intros. pose (length_max n l1). rewrite e. pose (length_max m l2). rewrite e0. auto.
Qed.

Lemma occ_weight_list_app_distrib : forall n l1 l2, occ_weight_list n (l1 ++ l2) = Nat.add (occ_weight_list n l1) (occ_weight_list n l2).
Proof.
intro n. induction l1.
- simpl. intros. auto.
- simpl. simpl in IHl1. intros. rewrite IHl1. lia.
Qed.

Lemma bigger_than_max_weight_0 : forall l n, ((proj1_sigT2 (max_weight_list l)) < n) -> (occ_weight_list n l = 0).
Proof.
induction l.
- intros. simpl. auto.
- intros. simpl. destruct (eq_dec_nat n (weight_form a)).
  + subst. exfalso. destruct (max_weight_list (a :: l)). simpl in H. destruct p.
     assert (InT a (a :: l)). apply InT_eq. pose (l0 a H0). lia.
  + assert (weight_test n a = 0). unfold weight_test. destruct (dec_weight_test n a). destruct p.
     destruct s. subst. inversion w. subst. exfalso. apply n0. auto. inversion H1. subst. inversion w. inversion H1.
     subst. simpl. auto. rewrite H0. simpl. apply IHl. destruct (max_weight_list (a :: l)). simpl in H.
     destruct p. destruct (max_weight_list l). destruct p. simpl in IHl. simpl.
     assert (x0 <= x). apply l3. intros. apply l0. apply InT_cons ; auto. lia.
Qed.

Lemma is_max_weight_bigger_0 : forall l, (0 < proj1_sigT2 (max_weight_list l)) -> (0 < occ_weight_list (proj1_sigT2 (max_weight_list l)) l).
Proof.
induction l.
- intros. exfalso. destruct (max_weight_list []). simpl in H. destruct p. assert (x <= 0).
  apply l0. intros. inversion H0. lia.
- intros. simpl. destruct (max_weight_list (a :: l)). simpl. simpl in H. destruct p.
  destruct (eq_dec_nat x (weight_form a)).
  + subst. unfold weight_test. destruct (dec_weight_test (weight_form a) a). destruct p.
     destruct s. subst. simpl. lia. subst. simpl. inversion w. inversion H1. exfalso. apply H0 ; auto.
  + assert (weight_test x a = 0). unfold weight_test. destruct (dec_weight_test x a). destruct p.
     destruct s. subst. inversion w. subst. exfalso. apply n. auto. inversion H1. subst. simpl. auto.
     rewrite H0. simpl.
     assert (x = (proj1_sigT2 (max_weight_list l))).
     { assert ((proj1_sigT2 (max_weight_list l)) <= x). destruct (max_weight_list l). simpl. simpl in IHl. destruct p.
       apply l3. intros. apply l0. apply InT_cons ; auto.
       assert (x <= (proj1_sigT2 (max_weight_list l))). assert (InT a (a :: l)). apply InT_eq. pose (l0 a H2).
       inversion l2. subst. exfalso. apply n ; auto. subst.
       assert (S m <= Nat.max (weight_form a) (proj1_sigT2 (max_weight_list l))). apply l1.
       intros. inversion H4. subst. lia. subst.
       assert (weight_form B <= (proj1_sigT2 (max_weight_list l))).
       destruct (max_weight_list l). subst. simpl. simpl in H1. simpl in IHl. destruct p. apply l3 ; auto.
       lia. lia. lia. }
     rewrite H1. apply IHl. lia.
Qed.

Lemma list_occ_weight_list_swap : forall l0 l1 l2 n, (list_occ_weight_list n (l0 ++ l1 ++ l2)) = (list_occ_weight_list n (l1 ++ l0 ++ l2)).
Proof.
induction n.
- intros. simpl ; auto.
- intros. simpl. rewrite IHn. repeat rewrite occ_weight_list_app_distrib.
  assert ((occ_weight_list (S n) l0 + (occ_weight_list (S n) l1 + occ_weight_list (S n) l2))%nat =
  (occ_weight_list (S n) l1 + (occ_weight_list (S n) l0 + occ_weight_list (S n) l2))%nat). lia. rewrite H. auto.
Qed.

Lemma list_occ_weight_list_headlist : forall  l0 l1 l2 x, (lex lt (list_occ_weight_list x l0) (list_occ_weight_list x l1)) ->
                                    (lex lt (list_occ_weight_list x (l0 ++ l2)) (list_occ_weight_list x (l1 ++ l2))).
Proof.
intros. generalize dependent l2. generalize dependent l1. generalize dependent l0.
induction x.
- simpl. intros. inversion H.
- intros. inversion H.
  * subst. apply IHx with (l2:=l2) in H1. simpl.
    destruct (dec_le (occ_weight_list (S x) (l0 ++ l2)) (occ_weight_list (S x) (l1 ++ l2))).
    + inversion l. rewrite H2. apply lex_skip ; auto. repeat rewrite occ_weight_list_app_distrib.
       rewrite occ_weight_list_app_distrib in H2. rewrite occ_weight_list_app_distrib in H0. apply lex_cons.
       repeat rewrite length_max ; auto. lia.
    + repeat rewrite occ_weight_list_app_distrib in l. repeat rewrite occ_weight_list_app_distrib. inversion l.
       rewrite H2. apply lex_skip ; auto. exfalso. lia.
  * subst. simpl. repeat rewrite occ_weight_list_app_distrib. apply lex_cons. repeat rewrite length_max ; auto. lia.
Qed.

Lemma lex_same_length : forall l0 l1, lex lt l0 l1 -> (length l0 = length l1).
Proof.
intros. induction H.
- simpl. rewrite IHlex. auto.
- simpl. auto.
Qed.

Lemma list_occ_weight_list_relevant : forall  x l0 l1, (Nat.max (proj1_sigT2 (max_weight_list l0)) (proj1_sigT2 (max_weight_list l1)) <= x) ->
         (less_than lt (list_occ_weight_list (proj1_sigT2 (max_weight_list l0)) l0) (list_occ_weight_list (proj1_sigT2 (max_weight_list l1)) l1)) ->
         (lex lt (list_occ_weight_list x l0) (list_occ_weight_list x l1)).
Proof.
induction x.
- intros. simpl. exfalso. destruct l0. destruct l1. destruct (max_weight_list []). simpl in H. simpl in H0.
  destruct p. assert (x <= 0). apply l0. intros. inversion H1. inversion H1. subst. simpl in H0. inversion H0.
  inversion H2. subst. inversion H2. destruct (max_weight_list []). simpl in H. simpl in H0.
  destruct p. assert (x <= 0). apply l0. intros. inversion H1. inversion H1. subst. simpl in H0.
  destruct (max_weight_list (m :: l1)). simpl in H. simpl in H0. destruct p.
  assert (InT m (m :: l1)). apply InT_eq. pose (l2 m H2). destruct m ; simpl in l4 ; lia.
  destruct (max_weight_list (m :: l0)). simpl in H. simpl in H0. destruct p.
  assert (InT m (m :: l0)). apply InT_eq. pose (l m H1). destruct m ; simpl in l3 ; lia.
- intros. simpl. inversion H0.
  * subst. repeat rewrite length_max in H1. inversion H.
    + assert (proj1_sigT2 (max_weight_list l1) = S x). lia. rewrite H3. rewrite <- H2. apply lex_cons.
       repeat rewrite length_max ; auto.
       pose (bigger_than_max_weight_0 _ H1). rewrite e.
       apply is_max_weight_bigger_0. lia.
    + subst. pose (IHx _ _ H3 H0). assert (proj1_sigT2 (max_weight_list l0) < S x). lia.
       pose (bigger_than_max_weight_0 _ H2). rewrite e. assert (proj1_sigT2 (max_weight_list l1) < S x). lia.
       pose (bigger_than_max_weight_0 _ H4). rewrite e0. apply lex_skip ; auto.
  * subst. inversion H.
    + simpl. assert ((proj1_sigT2 (max_weight_list l1) = S x) * (proj1_sigT2 (max_weight_list l0) = S x)).
       { pose (lex_same_length H1). pose (length_max (proj1_sigT2 (max_weight_list l0)) l0). rewrite <- e0.
          pose (length_max (proj1_sigT2 (max_weight_list l1)) l1). rewrite <- e1. split ; lia. }
       destruct H2. inversion H1.
       { destruct (max_weight_list l0). simpl. simpl in H2. simpl in e0. rewrite e0 in H2. simpl in H2. inversion H2.
         simpl in H3.  rewrite H3. rewrite <- H7. destruct (max_weight_list l1). simpl. simpl in H4. simpl in e.
         rewrite e in H4. simpl in H4. inversion H4. simpl in H3. rewrite <- H9. apply lex_skip.
         rewrite <- H10. rewrite <- H8. auto. }
       { destruct (max_weight_list l0). simpl. simpl in H2. simpl in e0. rewrite e0 in H2. simpl in H2. inversion H2.
         simpl in H3.  rewrite H3. rewrite <- H8. destruct (max_weight_list l1). simpl. simpl in H4. simpl in e.
         rewrite e in H4. simpl in H4. inversion H4. simpl in H3. rewrite <- H10. apply lex_cons ; auto.
         repeat rewrite length_max ; auto. }
    + subst. pose (IHx _ _ H3 H0). assert (proj1_sigT2 (max_weight_list l0) < S x). lia.
       pose (bigger_than_max_weight_0 _ H2). rewrite e. assert (proj1_sigT2 (max_weight_list l1) < S x). lia.
       pose (bigger_than_max_weight_0 _ H4). rewrite e0. apply lex_skip ; auto.
Qed.









(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* We show that in a PSGL4ip rule application, the premises are smaller than the conclusion
    according to the order <3. *)








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* GLR rule *)


Lemma GLR_applic_more_top_boxes : forall prem concl, GLRRule [prem] concl ->
                                                     (IdRule [] concl -> False) ->
                                    incl (top_boxes (fst concl)) (top_boxes (fst prem)).
Proof.
intros prem concl RA noIdB. inversion RA. subst. simpl. rewrite top_boxes_distr_app.
simpl. unfold incl. intros. apply in_or_app. left. assert (In a Γ). apply in_top_boxes in H.
destruct H. repeat destruct s. destruct p. subst. apply in_or_app. right. apply in_eq.
assert (InT a Γ). apply in_splitT in H1. destruct H1. destruct s. rewrite e.
apply InT_or_app. right. apply InT_eq. pose (InT_univ_gen_ext H2 X). destruct s.
exfalso. apply f. apply in_top_boxes in H. destruct H. repeat destruct s.
destruct p. exists x. assumption. apply top_boxes_incl_list in H.
pose (list_preserv_XBoxed_list BΓ). pose (InT_In i). apply i0 in i1.
apply is_box_in_top_boxes. apply i0. apply InT_In. assumption.
apply H0. apply InT_In. assumption.
Qed.



Lemma GLR_applic_le_subform_boxes : forall prem concl, GLRRule [prem] concl ->
                                                        (IdRule [] concl -> False) ->
                        (length (subform_boxesS prem) <= length (subform_boxesS concl) /\
                         forall B, (In B (subform_boxesS prem)) -> (In B (subform_boxesS concl))).
Proof.
intros prem concl RA noIdB. inversion RA. subst. split.
- apply NoDup_incl_length.
  * apply NoDup_subform_boxesS.
  * intro. intros. unfold subform_boxesS in H. unfold subform_boxesS. simpl. simpl in H.
    repeat rewrite app_length.  repeat rewrite app_length in H. repeat rewrite remove_list_of_nil.
    repeat rewrite remove_list_of_nil in H. apply in_app_or in H.
    destruct H. rewrite subform_boxesLF_dist_app in H. apply in_app_or in H. destruct H.
    apply in_or_app. left. apply univ_gen_ext_incl_subform_boxes in X. apply X. pose (XBoxed_list_same_subform_boxes BΓ).
    destruct a0. apply H1. assumption. apply In_remove_list_In_list in H.
    apply remove_list_is_in. simpl in H. destruct H. subst ; apply in_eq.
    apply in_app_or in H. destruct H. apply in_cons ; auto. apply In_remove_In_list in H.
    apply In_remove_list_In_list in H. inversion H. apply remove_list_is_in. apply In_remove_list_In_list in H.
    apply in_cons ; auto.
- intro. intros. unfold subform_boxesS in H. unfold subform_boxesS. simpl. simpl in H.
  repeat rewrite app_length.  repeat rewrite app_length in H. repeat rewrite remove_list_of_nil.
  repeat rewrite remove_list_of_nil in H. apply in_app_or in H.
  destruct H. rewrite subform_boxesLF_dist_app in H. apply in_app_or in H. destruct H.
  apply in_or_app. left. apply univ_gen_ext_incl_subform_boxes in X. apply X. pose (XBoxed_list_same_subform_boxes BΓ).
  destruct a. apply H1. assumption. apply In_remove_list_In_list in H.
  apply remove_list_is_in. simpl in H. destruct H. subst ; apply in_eq.
  apply in_app_or in H. destruct H. apply in_cons ; auto. apply In_remove_In_list in H.
  apply In_remove_list_In_list in H. inversion H. apply remove_list_is_in. apply In_remove_list_In_list in H.
  apply in_cons ; auto.
Qed.

Theorem GLR_applic_less_usable_boxes : forall prem concl, GLRRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                         length (usable_boxes prem) < length (usable_boxes concl).
Proof.
intros prem concl RA noIdB. inversion RA. unfold usable_boxes. simpl.
apply remove_list_incr_decr.
- apply NoDup_subform_boxesS.
- apply NoDup_subform_boxesS.
- exists (Box A). repeat split. simpl. rewrite top_boxes_distr_app. apply in_or_app. right. simpl.
  left. reflexivity. unfold subform_boxesS. simpl.
  destruct (In_dec (subform_boxesLF Γ) (Box A)). apply in_or_app. left. assumption.
  apply in_or_app. right. apply not_removed_remove_list ; auto. apply in_eq.
  intro. apply noIdB. subst. pose (in_top_boxes Γ (Box A) H2). repeat destruct s.
  destruct p. subst. apply IdRule_I.
- intro A0. pose (@GLR_applic_more_top_boxes prem concl). subst. pose (i RA). pose (i0 noIdB).
  apply i1.
- intro A0. subst. pose (GLR_applic_le_subform_boxes RA noIdB). destruct a. apply H1.
Qed.

Theorem PSGLR_less_than3 : forall prem concl, GLRRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          prem <3 concl.
Proof.
intros.
destruct (dec_init_rules prem).
- unfold less_than3. apply lex_cons ; auto.
  assert (init_switch concl = 1). unfold init_switch. destruct (dec_nat_init_switch_ind concl). destruct p. destruct s0.
  subst. simpl. 2: auto. exfalso. inversion i. firstorder. inversion H2. rewrite H1.
  assert (init_switch prem = 0). unfold init_switch. destruct (dec_nat_init_switch_ind prem). destruct p. destruct s0 ; auto.
  subst. simpl. exfalso. inversion i. inversion H3. firstorder. rewrite H2. apply less_than_eq. apply lex_cons ; auto.
- unfold less_than3.
  assert (init_switch concl = 1). unfold init_switch. destruct (dec_nat_init_switch_ind concl). destruct p. destruct s.
  subst. simpl. 2: auto. exfalso. inversion i. firstorder. inversion H2. rewrite H1.
  assert (init_switch prem = 1). unfold init_switch. destruct (dec_nat_init_switch_ind prem). destruct p. destruct s ; auto.
  subst. simpl. exfalso. inversion i. firstorder. inversion H3. rewrite H2.
  apply lex_skip. apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. apply GLR_applic_less_usable_boxes ; auto.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* AndR rule *)

Lemma PSAndR_leq_init_switch : forall prem1 prem2 concl, AndRRule [prem1; prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                ((init_switch prem1 <= init_switch concl) * (init_switch prem2 <= init_switch concl)).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem1). pose (init_switch_0_or_1 prem2).
destruct s. unfold init_switch in e. rewrite e. destruct s0. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e0. rewrite e0. split ; lia. destruct s0.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
Qed.

Lemma PSAndR_same_usable_boxes : forall prem1 prem2 concl, AndRRule [prem1; prem2] concl ->
                ((length (usable_boxes prem1) <= length (usable_boxes concl)) * (length (usable_boxes prem2) <= length (usable_boxes concl))).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. split.
- apply remove_list_incr_decr2 ; try apply NoDup_subform_boxesS. intro. intros.
  unfold subform_boxesS. simpl. unfold subform_boxesS in H0. simpl in H0.
  apply in_app_or in H0. destruct H0. apply in_or_app ; auto. apply remove_list_is_in.
  apply In_remove_list_In_list in H0. apply in_or_app ; auto.
- apply remove_list_incr_decr2 ; try apply NoDup_subform_boxesS. intro. intros.
  unfold subform_boxesS. simpl. unfold subform_boxesS in H0. simpl in H0.
  apply in_app_or in H0. destruct H0. apply in_or_app ; auto. apply remove_list_is_in.
  apply In_remove_list_In_list in H0. apply remove_list_is_in ; auto.
Qed.

Lemma PSAndR_less_weight : forall prem1 prem2 concl, AndRRule [prem1; prem2] concl ->
                ((lex (less_than lt) [seq_list_occ_weight prem1] [seq_list_occ_weight concl]) *
                 (lex (less_than lt) [seq_list_occ_weight prem2] [seq_list_occ_weight concl])).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl. destruct (max_weight_list (Γ ++ [A ∧ B])). simpl.
destruct p. split.
- destruct (max_weight_list (Γ ++ [A])). simpl. destruct p. assert (x0 <= x).
  apply l2. intros. apply InT_app_or in H0. destruct H0. apply l. apply InT_or_app ; auto.
  inversion i ; subst. assert (InT (B0 ∧ B) (Γ ++ [B0 ∧ B])). apply InT_or_app ; right ; apply InT_eq.
  pose (l _ H0). simpl in l3. lia. inversion H1. inversion H0 ; subst. 
  { apply lex_cons ; auto. apply less_than_eq.
     assert (Γ ++ [A] = Γ ++ [A] ++ []). auto. rewrite H1. clear H1.
     assert (Γ ++ [A ∧ B] = Γ ++ [A ∧ B] ++ []). auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ [A ∧ B] []).
     rewrite e. repeat rewrite app_nil_r. apply list_occ_weight_list_headlist.
     apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [A]). destruct p. simpl. destruct (max_weight_list [A ∧ B]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; right ; apply InT_eq. subst. inversion H3. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; right ; apply InT_eq. subst. inversion H4. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [A]). destruct p. simpl. destruct (max_weight_list [A ∧ B]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= weight_form A).
       { apply l4. intros. inversion H1. subst. 2: inversion H3. auto. }
       assert (weight_form (A ∧ B) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. lia. }
  { apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
- destruct (max_weight_list (Γ ++ [B])). simpl. destruct p. assert (x0 <= x).
  apply l2. intros. apply InT_app_or in H0. destruct H0. apply l. apply InT_or_app ; auto.
  inversion i ; subst. assert (InT (A ∧ B0) (Γ ++ [A ∧ B0])). apply InT_or_app ; right ; apply InT_eq.
  pose (l _ H0). simpl in l3. lia. inversion H1. inversion H0 ; subst.
  { apply lex_cons ; auto. apply less_than_eq.
     assert (Γ ++ [B] = Γ ++ [B] ++ []). auto. rewrite H1. clear H1.
     assert (Γ ++ [A ∧ B] = Γ ++ [A ∧ B] ++ []). auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ [A ∧ B] []).
     rewrite e. repeat rewrite app_nil_r. apply list_occ_weight_list_headlist.
     apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [A ∧ B]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; right ; apply InT_eq. subst. inversion H3. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; right ; apply InT_eq. subst. inversion H4. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [A ∧ B]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= weight_form B).
       { apply l4. intros. inversion H1. subst. 2: inversion H3. auto. }
       assert (weight_form (A ∧ B) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. lia. }
  { apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSAndR_less_than3 : forall prem1 prem2 concl, AndRRule [prem1;prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          ((prem1 <3 concl) * (prem2 <3 concl)).
Proof.
intros. split.
- unfold less_than3. pose (PSAndR_leq_init_switch H H0 H1). destruct p. inversion l.
  * subst. apply lex_skip. pose (PSAndR_same_usable_boxes H). destruct p. inversion l1.
    + rewrite H4. apply lex_skip. pose (PSAndR_less_weight H). destruct p. auto.
    + apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
- unfold less_than3. pose (PSAndR_leq_init_switch H H0 H1). destruct p. inversion l0.
  * subst. apply lex_skip. pose (PSAndR_same_usable_boxes H). destruct p. inversion l2.
    + rewrite H4. apply lex_skip. pose (PSAndR_less_weight H). destruct p. auto.
    + apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* AndL rule *)

Lemma PSAndL_leq_init_switch : forall prem concl, AndLRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSAndL_leq_usable_boxes : forall prem concl, AndLRule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app.
assert (subform_boxesS (Γ0 ++ A :: B :: Γ1, C) = subform_boxesS (Γ0 ++ A ∧ B  :: Γ1, C)).
unfold subform_boxesS. simpl.
assert (subform_boxesLF (Γ0 ++ A :: B :: Γ1)= subform_boxesLF (Γ0 ++ A ∧ B  :: Γ1)).
{ repeat rewrite subform_boxesLF_dist_app. simpl. repeat rewrite <- app_assoc. 
  repeat rewrite app_remove_list. rewrite redund_remove_list. rewrite <- remove_list_dist_app. auto. }
rewrite H0. auto. rewrite H0. apply remove_list_incr_decr3.
intro. intros. apply in_or_app. apply in_app_or in H1 ; destruct H1 ; auto.
simpl in H1. right. assert (A :: B :: Γ1 = (A :: [B]) ++ Γ1). auto. rewrite H2.
rewrite top_boxes_distr_app. apply in_or_app ; auto.
Qed.

Lemma PSAndL_less_weight : forall prem concl, AndLRule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl.  simpl. destruct (max_weight_list ((Γ0 ++ A ∧ B :: Γ1) ++ [C])).
destruct p. destruct (max_weight_list ((Γ0 ++ A :: B :: Γ1) ++ [C])). simpl. destruct p.
assert (x0 <= x).
{ apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
  destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
  assert (InT (B0 ∧ B) ((Γ0 ++ B0 ∧ B :: Γ1) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H0). simpl in l3. lia. subst. inversion H1. subst.
  assert (InT (A ∧ B0) ((Γ0 ++ A ∧ B0 :: Γ1) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H0). simpl in l3. lia. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons ; auto. inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
inversion H0 ; subst.
{ apply lex_cons ; auto. apply less_than_eq.
   assert ((Γ0 ++ A :: B :: Γ1) ++ [C] = Γ0 ++ (A :: [B]) ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
   assert ((Γ0 ++ A ∧ B :: Γ1) ++ [C] = Γ0 ++ [A ∧ B] ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
   rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ0 [A ∧ B] (Γ1 ++ [C])).
   rewrite e. clear e. apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
   - destruct (max_weight_list [A; B]). destruct p. simpl. destruct (max_weight_list [A ∧ B]). destruct p. simpl.
     assert (x0 <= x).
     { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
        subst. inversion H3. 2: inversion H4. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_cons.
        apply InT_eq. }
     assert (x1 <= x).
     { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left ; apply InT_or_app ; right ; apply InT_eq. inversion H4. }
     lia.
   - apply less_than_lt. destruct (max_weight_list [A;B]). destruct p. simpl. destruct (max_weight_list [A ∧ B]). destruct p. simpl.
     apply max_less_length.
     assert (x0 <= Nat.max (weight_form A) (weight_form B)).
     { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. subst ; lia. inversion H4. }
     assert (weight_form (A ∧ B) <= x1).
     { apply l5. apply InT_eq. }
     simpl in H2. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSAndL_less_than3 : forall prem concl, AndLRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSAndL_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSAndL_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSAndL_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* OrR1 rule *)

Lemma PSOrR1_leq_init_switch : forall prem concl, OrR1Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSOrR1_leq_usable_boxes : forall prem concl, OrR1Rule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. apply remove_list_incr_decr2.
1-2: apply NoDup_subform_boxesS. intro. intros.
unfold subform_boxesS. simpl. unfold subform_boxesS in H0. simpl in H0.
apply in_app_or in H0. destruct H0. apply in_or_app ; auto. apply remove_list_is_in.
apply In_remove_list_In_list in H0. apply in_or_app ; auto.
Qed.

Lemma PSOrR1_less_weight : forall prem concl, OrR1Rule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl. destruct (max_weight_list (Γ ++ [A ∨ B])). simpl.
destruct p. destruct (max_weight_list (Γ ++ [A])). simpl. destruct p. assert (x0 <= x).
apply l2. intros. apply InT_app_or in H0. destruct H0. apply l. apply InT_or_app ; auto.
inversion i ; subst. assert (InT (B0 ∨ B) (Γ ++ [B0 ∨ B])). apply InT_or_app ; right ; apply InT_eq.
pose (l _ H0). simpl in l3. lia. inversion H1. inversion H0 ; subst.
  { apply lex_cons ; auto. apply less_than_eq.
     assert (Γ ++ [A] = Γ ++ [A] ++ []). auto. rewrite H1. clear H1.
     assert (Γ ++ [A ∨ B] = Γ ++ [A ∨ B] ++ []). auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ [A ∨ B] []).
     rewrite e. repeat rewrite app_nil_r. apply list_occ_weight_list_headlist.
     apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [A]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; right ; apply InT_eq. subst. inversion H3. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; right ; apply InT_eq. subst. inversion H4. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [A]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= weight_form A).
       { apply l4. intros. inversion H1. subst. 2: inversion H3. auto. }
       assert (weight_form (A ∨ B) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSOrR1_less_than3 : forall prem concl, OrR1Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSOrR1_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSOrR1_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSOrR1_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* OrR2 rule *)

Lemma PSOrR2_leq_init_switch : forall prem concl, OrR2Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSOrR2_leq_usable_boxes : forall prem concl, OrR2Rule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. apply remove_list_incr_decr2.
1-2: apply NoDup_subform_boxesS. intro. intros.
unfold subform_boxesS. simpl. unfold subform_boxesS in H0. simpl in H0.
apply in_app_or in H0. destruct H0. apply in_or_app ; auto. apply remove_list_is_in.
apply In_remove_list_In_list in H0. apply remove_list_is_in ; auto.
Qed.

Lemma PSOrR2_less_weight : forall prem concl, OrR2Rule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl. destruct (max_weight_list (Γ ++ [A ∨ B])). simpl.
destruct p. destruct (max_weight_list (Γ ++ [B])). simpl. destruct p. assert (x0 <= x).
apply l2. intros. apply InT_app_or in H0. destruct H0. apply l. apply InT_or_app ; auto.
inversion i ; subst. assert (InT (A ∨ B0) (Γ ++ [A ∨ B0])). apply InT_or_app ; right ; apply InT_eq.
pose (l _ H0). simpl in l3. lia. inversion H1. inversion H0 ; subst.
  { apply lex_cons ; auto. apply less_than_eq.
     assert (Γ ++ [B] = Γ ++ [B] ++ []). auto. rewrite H1. clear H1.
     assert (Γ ++ [A ∨ B] = Γ ++ [A ∨ B] ++ []). auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ [A ∨ B] []).
     rewrite e. repeat rewrite app_nil_r. apply list_occ_weight_list_headlist.
     apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; right ; apply InT_eq. subst. inversion H3. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; right ; apply InT_eq. subst. inversion H4. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= weight_form B).
       { apply l4. intros. inversion H1. subst. 2: inversion H3. auto. }
       assert (weight_form (A ∨ B) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSOrR2_less_than3 : forall prem concl, OrR2Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSOrR2_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSOrR2_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSOrR2_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* OrL rule *)

Lemma PSOrL_leq_init_switch : forall prem1 prem2 concl, OrLRule [prem1;prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          ((init_switch prem1 <= init_switch concl) * (init_switch prem2 <= init_switch concl)).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem1). pose (init_switch_0_or_1 prem2).
destruct s. unfold init_switch in e. rewrite e. destruct s0. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e0. rewrite e0. split ; lia. destruct s0.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
Qed.

Lemma PSOrL_leq_usable_boxes : forall prem1 prem2 concl, OrLRule [prem1;prem2] concl ->
                ((length (usable_boxes prem1) <= length (usable_boxes concl)) * (length (usable_boxes prem2) <= length (usable_boxes concl))).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app.
split.
- simpl (top_boxes (A ∨ B :: Γ1)).
  assert (length (remove_list (top_boxes Γ0 ++ top_boxes (A :: Γ1)) (subform_boxesS (Γ0 ++ A ∨ B :: Γ1, C))) <=
  length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ A ∨ B :: Γ1, C)))).
  { apply remove_list_incr_decr3. intro. intros. apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
    apply in_or_app ; right. simpl. destruct A ; auto. apply in_cons ; auto. }
  assert (length (remove_list (top_boxes Γ0 ++ top_boxes (A :: Γ1)) (subform_boxesS (Γ0 ++ A :: Γ1, C))) <=
  length (remove_list (top_boxes Γ0 ++ top_boxes (A :: Γ1)) (subform_boxesS (Γ0 ++ A ∨ B :: Γ1, C)))).
  { apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
    simpl. intro. apply in_app_or in H1 ; destruct H1. apply in_or_app ; left.
    repeat rewrite subform_boxesLF_dist_app ; repeat rewrite subform_boxesLF_dist_app in H1 ;
    apply in_app_or in H1 ; destruct H1 ; [ apply in_or_app ; auto | apply remove_list_is_in ;
    apply In_remove_list_In_list in H1 ; simpl in H1 ; apply in_app_or in H1 ; destruct H1 ].
    simpl. apply in_or_app ; left. apply in_or_app ; auto. apply In_remove_list_In_list in H1.
    simpl. apply remove_list_is_in ; auto. apply In_remove_list_In_list in H1.
    apply remove_list_is_in ; auto. }
  lia.
- simpl (top_boxes (A ∨ B :: Γ1)).
  assert (length (remove_list (top_boxes Γ0 ++ top_boxes (B :: Γ1)) (subform_boxesS (Γ0 ++ A ∨ B :: Γ1, C))) <=
  length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ A ∨ B :: Γ1, C)))).
  { apply remove_list_incr_decr3. intro. intros. apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
    apply in_or_app ; right. simpl. destruct B ; auto. apply in_cons ; auto. }
  assert (length (remove_list (top_boxes Γ0 ++ top_boxes (B :: Γ1)) (subform_boxesS (Γ0 ++ B :: Γ1, C))) <=
  length (remove_list (top_boxes Γ0 ++ top_boxes (B :: Γ1)) (subform_boxesS (Γ0 ++ A ∨ B :: Γ1, C)))).
  { apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
    simpl. intro. apply in_app_or in H1 ; destruct H1. apply in_or_app ; left.
    repeat rewrite subform_boxesLF_dist_app ; repeat rewrite subform_boxesLF_dist_app in H1 ;
    apply in_app_or in H1 ; destruct H1 ; [ apply in_or_app ; auto | apply remove_list_is_in ;
    apply In_remove_list_In_list in H1 ; simpl in H1 ; apply in_app_or in H1 ; destruct H1 ].
    simpl. apply in_or_app ; left. apply remove_list_is_in ; auto. apply In_remove_list_In_list in H1.
    simpl. apply remove_list_is_in ; auto. apply In_remove_list_In_list in H1.
    apply remove_list_is_in ; auto. }
  lia.
Qed.

Lemma PSOrL_less_weight : forall prem1 prem2 concl, OrLRule [prem1;prem2] concl ->
                ((lex (less_than lt) [seq_list_occ_weight prem1] [seq_list_occ_weight concl]) *
                 (lex (less_than lt) [seq_list_occ_weight prem2] [seq_list_occ_weight concl])).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl. destruct (max_weight_list ((Γ0 ++ A ∨ B :: Γ1) ++ [C])).
destruct p. simpl. split.
- destruct (max_weight_list ((Γ0 ++ A :: Γ1) ++ [C])). simpl. destruct p.
  assert (x0 <= x).
  { apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
    destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
    assert (InT (B0 ∨ B) ((Γ0 ++ B0 ∨ B :: Γ1) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_eq. pose (l _ H0). simpl in l3. lia. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_cons ; auto. inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
  inversion H0 ; subst.
  { apply lex_cons ; auto. apply less_than_eq.
     assert ((Γ0 ++ A :: Γ1) ++ [C] = Γ0 ++ [A] ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     assert ((Γ0 ++ A ∨ B :: Γ1) ++ [C] = Γ0 ++ [A ∨ B] ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ0 [A ∨ B] (Γ1 ++ [C])).
     rewrite e. clear e. apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [A]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
          inversion H3. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left ; apply InT_or_app ; right ; apply InT_eq. inversion H4. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [A]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= weight_form A).
       { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. }
       assert (weight_form (A ∨ B) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. lia. }
  { apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
- destruct (max_weight_list ((Γ0 ++ B :: Γ1) ++ [C])). simpl. destruct p.
  assert (x0 <= x).
  { apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
    destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
    assert (InT (A ∨ B0) ((Γ0 ++ A ∨ B0 :: Γ1) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_eq. pose (l _ H0). simpl in l3. lia. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_cons ; auto. inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
  inversion H0 ; subst.
  { apply lex_cons ; auto. apply less_than_eq.
     assert ((Γ0 ++ B :: Γ1) ++ [C] = Γ0 ++ [B] ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     assert ((Γ0 ++ A ∨ B :: Γ1) ++ [C] = Γ0 ++ [A ∨ B] ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ0 [A ∨ B] (Γ1 ++ [C])).
     rewrite e. clear e. apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
          inversion H3. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left ; apply InT_or_app ; right ; apply InT_eq. inversion H4. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [A ∨ B]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= weight_form B).
       { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. }
       assert (weight_form (A ∨ B) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. lia. }
  { apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSOrL_less_than3 : forall prem1 prem2 concl, OrLRule [prem1;prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          ((prem1 <3 concl) * (prem2 <3 concl)).
Proof.
intros. unfold less_than3. pose (PSOrL_leq_init_switch H H0 H1). destruct p. split.
- inversion l.
  * subst. apply lex_skip. pose (PSOrL_leq_usable_boxes H). destruct p. inversion l1.
    + rewrite H4. apply lex_skip. pose (PSOrL_less_weight H). destruct p ; auto.
    + apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
- inversion l0.
  * subst. apply lex_skip. pose (PSOrL_leq_usable_boxes H). destruct p. inversion l2.
    + rewrite H4. apply lex_skip. pose (PSOrL_less_weight H). destruct p ; auto.
    + apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* ImpR rule *)

Lemma PSImpR_leq_init_switch : forall prem concl, ImpRRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSImpR_leq_usable_boxes : forall prem concl, ImpRRule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app.
assert (length (remove_list (top_boxes Γ0 ++ top_boxes (A :: Γ1)) (subform_boxesS (Γ0 ++ Γ1, A → B))) <=
length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ Γ1, A → B)))).
{ apply remove_list_incr_decr3. intro. intros. apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
  apply in_or_app ; right. simpl. destruct A ; auto. apply in_cons ; auto. }
assert (length (remove_list (top_boxes Γ0 ++ top_boxes (A :: Γ1)) (subform_boxesS (Γ0 ++ A :: Γ1, B))) <=
length (remove_list (top_boxes Γ0 ++ top_boxes (A :: Γ1)) (subform_boxesS (Γ0 ++ Γ1, A → B)))).
{ apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
  simpl. intro. apply in_app_or in H1 ; destruct H1. repeat rewrite subform_boxesLF_dist_app.
  repeat rewrite subform_boxesLF_dist_app in H1. apply in_app_or in H1. destruct H1.
  apply in_or_app ; left. apply in_or_app ; auto. apply In_remove_list_In_list in H1. simpl in H1.
  apply in_app_or in H1. destruct H1. apply remove_list_is_in. apply in_or_app ; auto.
  apply In_remove_list_In_list in H1. apply in_or_app ; left. apply remove_list_is_in ; auto.
  apply In_remove_list_In_list in H1. apply remove_list_is_in. apply remove_list_is_in ; auto. }
lia.
Qed.

Lemma PSImpR_less_weight : forall prem concl, ImpRRule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl.
destruct (max_weight_list ((Γ0 ++ Γ1) ++ [A → B])). simpl.
destruct p. destruct (max_weight_list ((Γ0 ++ A :: Γ1) ++ [B])). simpl. destruct p.
assert (x0 <= x).
{ apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
  destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
  assert (InT (B0 → B) ((Γ0 ++ Γ1) ++ [B0 → B])). apply InT_or_app ; right. apply InT_eq.
  pose (l _ H0). simpl in l3. lia. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; auto.
  inversion i. 2: inversion H1. subst.
  assert (InT (A → B0) ((Γ0 ++ Γ1) ++ [A → B0])). apply InT_or_app ; right. apply InT_eq.
  pose (l _ H0). simpl in l3. lia. }
inversion H0 ; subst.
{ apply lex_cons ; auto. apply less_than_eq.
   assert ((Γ0 ++ A :: Γ1) ++ [B] = (Γ0 ++ A :: Γ1) ++ [B] ++ []). repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
   rewrite list_occ_weight_list_swap.
   assert ([B] ++ (Γ0 ++ A :: Γ1) ++ [] =(B :: Γ0) ++ [A] ++ Γ1). repeat rewrite <- app_assoc ; simpl ; rewrite app_nil_r ; auto. rewrite H1. clear H1.
   rewrite list_occ_weight_list_swap. assert ([A] ++ (B :: Γ0) ++ Γ1 = (A :: [B]) ++ Γ0 ++ Γ1). auto. rewrite H1. clear H1.
   assert ((Γ0 ++ Γ1) ++ [A → B] = (Γ0 ++ Γ1) ++ [A → B] ++ []). rewrite app_nil_r ; auto. rewrite H1. clear H1.
   pose (list_occ_weight_list_swap (Γ0 ++ Γ1) [A → B] []).
   rewrite e. clear e. rewrite app_nil_r. apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
   - destruct (max_weight_list [A; B]). destruct p. simpl. destruct (max_weight_list [A → B]). destruct p. simpl.
     assert (x0 <= x).
     { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
        subst. inversion H3. 2: inversion H4. subst. apply l1. apply InT_or_app ; right. apply InT_eq. }
     assert (x1 <= x).
     { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; right ;  apply InT_eq. inversion H4. }
     lia.
   - apply less_than_lt. destruct (max_weight_list [A;B]). destruct p. simpl. destruct (max_weight_list [A → B]). destruct p. simpl.
     apply max_less_length.
     assert (x0 <= Nat.max (weight_form A) (weight_form B)).
     { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. subst ; lia. inversion H4. }
     assert (weight_form (A → B) <= x1).
     { apply l5. apply InT_eq. }
     simpl in H2. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSImpR_less_than3 : forall prem concl, ImpRRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSImpR_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSImpR_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSImpR_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* AtomImpL1 rule *)

Lemma PSAtomImpL1_leq_init_switch : forall prem concl, AtomImpL1Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSAtomImpL1_leq_usable_boxes : forall prem concl, AtomImpL1Rule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app. simpl.
assert (subform_boxesS (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) = subform_boxesS (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C)).
unfold subform_boxesS. simpl.
assert (subform_boxesLF (Γ0 ++ # P :: Γ1 ++ A :: Γ2)= subform_boxesLF (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2)).
{ repeat rewrite subform_boxesLF_dist_app. simpl. repeat rewrite subform_boxesLF_dist_app. simpl. auto. }
rewrite H0. auto. rewrite H0. apply remove_list_incr_decr3.
intro. intros. apply in_or_app. apply in_app_or in H1 ; destruct H1 ; auto.
repeat rewrite top_boxes_distr_app. repeat rewrite top_boxes_distr_app in H1.
simpl in H1. right. apply in_app_or in H1. destruct H1. apply in_or_app ; auto.
apply in_or_app ; right. destruct A ; simpl ; auto.
Qed.

Lemma PSAtomImpL1_less_weight : forall prem concl, AtomImpL1Rule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl.
destruct (max_weight_list ((Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2) ++ [C])). simpl.
destruct p. destruct (max_weight_list ((Γ0 ++ # P :: Γ1 ++ A :: Γ2) ++ [C])). simpl. destruct p.
assert (x0 <= x).
{ apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
  destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
  assert (InT (# P → A) ((Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons. apply InT_or_app ; right ; apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia. subst.
  apply InT_app_or in H1. destruct H1. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons. apply InT_or_app ; auto. inversion i0. subst.
  assert (InT (# P → B) ((Γ0 ++ # P :: Γ1 ++ # P → B :: Γ2) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons ; apply InT_or_app ; right ; apply InT_eq. pose (l _ H0). simpl in l3. lia.
  subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons ; apply InT_or_app ; right ; apply InT_cons ; auto.
  inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
inversion H0 ; subst.
{ apply lex_cons ; auto. apply less_than_eq.
  assert ((Γ0 ++ # P :: Γ1 ++ A :: Γ2) ++ [C] = Γ0 ++ [# P] ++ Γ1 ++ A :: Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  rewrite list_occ_weight_list_swap.
  assert ([# P] ++ Γ0 ++ Γ1 ++ A :: Γ2 ++ [C] = (# P :: Γ0 ++ Γ1) ++ [A] ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  rewrite list_occ_weight_list_swap.
  assert ([A] ++ (# P :: Γ0 ++ Γ1) ++ Γ2 ++ [C] = (A :: [# P]) ++ Γ0 ++ Γ1 ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  assert ((Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2) ++ [C] = Γ0 ++ [# P] ++ Γ1 ++ # P → A :: Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  pose (list_occ_weight_list_swap Γ0 [# P] (Γ1 ++ # P → A :: Γ2 ++ [C])). rewrite e. clear e.
  assert ([# P] ++ Γ0 ++ Γ1 ++ # P → A :: Γ2 ++ [C] = (# P :: Γ0 ++ Γ1) ++ [# P → A] ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  pose (list_occ_weight_list_swap (# P :: Γ0 ++ Γ1) [# P → A] (Γ2 ++ [C])). rewrite e. clear e.
  assert ([# P → A] ++ (# P :: Γ0 ++ Γ1) ++ Γ2 ++ [C] = (# P → A :: [# P]) ++ Γ0 ++ Γ1 ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
  - destruct (max_weight_list [A; # P]). destruct p. simpl. destruct (max_weight_list [# P → A;# P]). destruct p. simpl.
    assert (x0 <= x).
    { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left.
       apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
       subst. inversion H3. 2: inversion H4. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq. }
    assert (x1 <= x).
    { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left.
       apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
       subst. inversion H4. 2: inversion H5. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq. }
    lia.
  - apply less_than_lt. destruct (max_weight_list [A;# P]). destruct p. simpl. destruct (max_weight_list [# P → A;# P]). destruct p. simpl.
    apply max_less_length.
    assert (x0 <= Nat.max (weight_form A) (weight_form # P)).
    { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. subst ; lia. inversion H4. }
    simpl in H1. assert (weight_form (# P → A) <= x1).
    { apply l5. apply InT_eq. }
    simpl in H2. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSAtomImpL1_less_than3 : forall prem concl, AtomImpL1Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSAtomImpL1_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSAtomImpL1_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSAtomImpL1_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* AtomImpL2 rule *)


Lemma PSAtomImpL2_leq_init_switch : forall prem concl, AtomImpL2Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSAtomImpL2_leq_usable_boxes : forall prem concl, AtomImpL2Rule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app. simpl.
assert (subform_boxesS (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) = subform_boxesS (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C)).
unfold subform_boxesS. simpl.
assert (subform_boxesLF (Γ0 ++ A :: Γ1 ++ # P :: Γ2)= subform_boxesLF (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2)).
{ repeat rewrite subform_boxesLF_dist_app. simpl. repeat rewrite subform_boxesLF_dist_app. simpl. auto. }
rewrite H0. auto. rewrite H0. apply remove_list_incr_decr3.
intro. intros. apply in_or_app. apply in_app_or in H1 ; destruct H1 ; auto.
repeat rewrite top_boxes_distr_app. repeat rewrite top_boxes_distr_app in H1.
simpl in H1. right. apply in_app_or in H1. destruct H1.
destruct A ; simpl. 1-5: apply in_or_app ; auto. right. apply in_or_app ; auto.
destruct A ; simpl. 1-5: apply in_or_app ; auto. right. apply in_or_app ; auto.
Qed.

Lemma PSAtomImpL2_less_weight : forall prem concl, AtomImpL2Rule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl.
destruct (max_weight_list ((Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2) ++ [C])). simpl.
destruct p. destruct (max_weight_list ((Γ0 ++ A :: Γ1 ++ # P :: Γ2) ++ [C])). simpl. destruct p.
assert (x0 <= x).
{ apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
  destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
  assert (InT (# P → B) ((Γ0 ++ # P → B :: Γ1 ++ # P :: Γ2) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia. subst.
  apply InT_app_or in H1. destruct H1. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons. apply InT_or_app ; auto. inversion i0. subst.
  assert (InT (# P → A) ((Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia.
  subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons ; apply InT_or_app ; right ; apply InT_cons ; auto.
  inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
inversion H0 ; subst.
{ apply lex_cons ; auto. apply less_than_eq.
  assert ((Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2) ++ [C] = Γ0 ++ [# P → A] ++ Γ1 ++ # P :: Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  rewrite list_occ_weight_list_swap.
  assert ([# P → A] ++ Γ0 ++ Γ1 ++ # P :: Γ2 ++ [C] = (# P → A :: Γ0 ++ Γ1) ++ [# P] ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  rewrite list_occ_weight_list_swap.
  assert ([# P] ++ (# P → A :: Γ0 ++ Γ1) ++ Γ2 ++ [C] = (# P :: [# P → A]) ++ Γ0 ++ Γ1 ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  assert ((Γ0 ++ A :: Γ1 ++ # P :: Γ2) ++ [C] = Γ0 ++ [A] ++ Γ1 ++ # P :: Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  pose (list_occ_weight_list_swap Γ0 [A] (Γ1 ++ # P :: Γ2 ++ [C])). rewrite e. clear e.
  assert ([A] ++ Γ0 ++ Γ1 ++ # P :: Γ2 ++ [C] = (A :: Γ0 ++ Γ1) ++ [# P] ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  pose (list_occ_weight_list_swap (A :: Γ0 ++ Γ1) [# P] (Γ2 ++ [C])). rewrite e. clear e.
  assert ([# P] ++ (A :: Γ0 ++ Γ1) ++ Γ2 ++ [C] = (# P :: [A]) ++ Γ0 ++ Γ1 ++ Γ2 ++ [C]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
  - destruct (max_weight_list [# P;  A]). destruct p. simpl. destruct (max_weight_list [# P  ;# P → A]). destruct p. simpl.
    assert (x0 <= x).
    { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left.
       apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
       subst. inversion H3. 2: inversion H4. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq. }
    assert (x1 <= x).
    { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left.
       apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
       subst. inversion H4. 2: inversion H5. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq. }
    lia.
  - apply less_than_lt. destruct (max_weight_list [# P;A]). destruct p. simpl. destruct (max_weight_list [# P;# P → A]). destruct p. simpl.
    apply max_less_length.
    assert (x0 <= Nat.max (weight_form # P) (weight_form A)).
    { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. subst ; lia. inversion H4. }
    assert (weight_form (# P → A) <= x1).
    { apply l5. apply InT_cons. apply InT_eq. }
    simpl in H2. simpl in H1. destruct A ; simpl in H1 ; simpl in H2 ; lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSAtomImpL2_less_than3 : forall prem concl, AtomImpL2Rule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSAtomImpL2_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSAtomImpL2_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSAtomImpL2_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* AndImpL rule *)

Lemma PSAndImpL_leq_init_switch : forall prem concl, AndImpLRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSAndImpL_leq_usable_boxes : forall prem concl, AndImpLRule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app.
assert (length (remove_list (top_boxes Γ0 ++ top_boxes (A → B → C :: Γ1)) (subform_boxesS (Γ0 ++ (A ∧ B) → C :: Γ1, D))) <=
length (remove_list (top_boxes Γ0 ++ top_boxes ((A ∧ B) → C :: Γ1)) (subform_boxesS (Γ0 ++ (A ∧ B) → C :: Γ1, D)))).
{ apply remove_list_incr_decr3. intro. intros. apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
  apply in_or_app ; right. simpl. simpl in H0. auto. }
assert (length (remove_list (top_boxes Γ0 ++ top_boxes (A → B → C :: Γ1)) (subform_boxesS (Γ0 ++ A → B → C :: Γ1, D))) <=
length (remove_list (top_boxes Γ0 ++ top_boxes (A → B → C :: Γ1)) (subform_boxesS (Γ0 ++ (A ∧ B) → C :: Γ1, D)))).
{ apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
  simpl. intro. apply in_app_or in H1 ; destruct H1. repeat rewrite subform_boxesLF_dist_app.
  repeat rewrite subform_boxesLF_dist_app in H1. apply in_app_or in H1. destruct H1.
  apply in_or_app ; left. apply in_or_app ; auto. apply In_remove_list_In_list in H1. simpl in H1.
  apply in_app_or in H1. destruct H1. apply in_app_or in H1. destruct H1. apply in_or_app. left.
  apply remove_list_is_in. simpl. apply in_or_app. left. apply in_or_app. left. apply in_or_app ; auto.
  apply In_remove_list_In_list in H1. apply in_app_or in H1. destruct H1.
  apply in_or_app ; left. apply remove_list_is_in. simpl. apply in_or_app ; left.
  apply in_or_app ; left. apply remove_list_is_in ; auto.
  apply In_remove_list_In_list in H1. apply in_or_app ; left. apply remove_list_is_in. simpl.
  apply in_or_app ; left. apply remove_list_is_in ; auto. apply In_remove_list_In_list in H1.
  apply in_or_app ; left. apply remove_list_is_in. simpl.
  apply remove_list_is_in ; auto. apply In_remove_list_In_list in H1.
  apply remove_list_is_in ; auto. }
lia.
Qed.

Lemma PSAndImpL_less_weight : forall prem concl, AndImpLRule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl.
destruct (max_weight_list ((Γ0 ++ (A ∧ B) → C :: Γ1) ++ [D])). simpl.
destruct p. destruct (max_weight_list ((Γ0 ++ A → B → C :: Γ1) ++ [D])). simpl. destruct p.
assert (x0 <= x).
{ apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
  destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
  assert (InT ((A ∧ B) → C) ((Γ0 ++ (A ∧ B) → C :: Γ1) ++ [D])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia. subst.
  apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons ; auto.
  inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
inversion H0 ; subst.
{ apply lex_cons ; auto. apply less_than_eq.
   assert ((Γ0 ++ A → B → C :: Γ1) ++ [D] = Γ0 ++ [A → B → C] ++ (Γ1 ++ [D])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
   assert ((Γ0 ++ (A ∧ B) → C :: Γ1) ++ [D] = Γ0 ++ [(A ∧ B) → C] ++ (Γ1 ++ [D])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
   rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ0 [(A ∧ B) → C] (Γ1 ++ [D])).
   rewrite e. clear e. apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
   - destruct (max_weight_list [A → B → C]). destruct p. simpl. destruct (max_weight_list [(A ∧ B) → C]). destruct p. simpl.
     assert (x0 <= x).
     { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
        inversion H3. }
     assert (x1 <= x).
     { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left ; apply InT_or_app ; right ; apply InT_eq. inversion H4. }
     lia.
   - apply less_than_lt. destruct (max_weight_list [A → B → C]). destruct p. simpl. destruct (max_weight_list [(A ∧ B) → C]). destruct p. simpl.
     apply max_less_length.
     assert (x0 <= weight_form (A → B → C)).
     { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. }
     assert (weight_form ((A ∧ B) → C) <= x1).
     { apply l5. apply InT_eq. }
     simpl in H2. simpl in H1. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSAndImpL_less_than3 : forall prem concl, AndImpLRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSAndImpL_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSAndImpL_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSAndImpL_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.








(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* OrImpL rule *)

Lemma PSOrImpL_leq_init_switch : forall prem concl, OrImpLRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (init_switch prem <= init_switch concl).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem). destruct s. unfold init_switch in e. rewrite e. auto.
unfold init_switch in e. rewrite e. lia.
Qed.

Lemma PSOrImpL_leq_usable_boxes : forall prem concl, OrImpLRule [prem] concl ->
                (length (usable_boxes prem) <= length (usable_boxes concl)).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app. simpl.
repeat rewrite top_boxes_distr_app. simpl.
apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
simpl. intro. apply in_app_or in H0 ; destruct H0. repeat rewrite subform_boxesLF_dist_app.
repeat rewrite subform_boxesLF_dist_app in H0. apply in_app_or in H0. destruct H0.
apply in_or_app ; left. apply in_or_app ; auto. apply In_remove_list_In_list in H0. simpl in H0.
apply in_app_or in H0. destruct H0. apply in_app_or in H0. destruct H0. apply in_or_app. left.
apply remove_list_is_in. simpl. apply in_or_app. left. apply in_or_app. left. apply in_or_app ; auto.
apply In_remove_list_In_list in H0.
apply in_or_app ; left. apply remove_list_is_in. simpl. apply in_or_app ; left. apply remove_list_is_in ; auto.
apply In_remove_list_In_list in H0. apply in_or_app ; left. repeat rewrite subform_boxesLF_dist_app in H0.
apply in_app_or in H0. destruct H0. apply remove_list_is_in. simpl.
apply remove_list_is_in. repeat rewrite subform_boxesLF_dist_app. apply in_or_app ; auto.
apply In_remove_list_In_list in H0. simpl in H0. apply in_app_or in H0.
destruct H0. apply in_app_or in H0. destruct H0. apply remove_list_is_in. simpl.
apply in_or_app ; left. apply in_or_app ; left. apply remove_list_is_in ; auto.
apply In_remove_list_In_list in H0.
apply remove_list_is_in. simpl. apply in_or_app ; left. apply remove_list_is_in ; auto.
apply In_remove_list_In_list in H0. apply remove_list_is_in. simpl.
apply remove_list_is_in. repeat rewrite subform_boxesLF_dist_app.
apply remove_list_is_in ; auto. apply In_remove_list_In_list in H0.
apply remove_list_is_in ; auto.
Qed.

Lemma PSOrImpL_less_weight : forall prem concl, OrImpLRule [prem] concl ->
                (lex (less_than lt) [seq_list_occ_weight prem] [seq_list_occ_weight concl]).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl.
destruct (max_weight_list ((Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2) ++ [D])). simpl.
destruct p. destruct (max_weight_list ((Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2) ++ [D])). simpl. destruct p.
assert (x0 <= x).
{ apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
  destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
  assert (InT ((A ∨ B) → C) ((Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2) ++ [D])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia. subst.
  apply InT_app_or in H1. destruct H1. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons. apply InT_or_app ; auto. inversion i0. subst.
  assert (InT ((A ∨ B) → C) ((Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2) ++ [D])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia.
  subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons ; apply InT_or_app ; auto.
  inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
inversion H0 ; subst.
{ apply lex_cons ; auto. apply less_than_eq.
  assert ((Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2) ++ [D] = Γ0 ++ [(A ∨ B) → C] ++ Γ1 ++ Γ2 ++ [D]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  rewrite list_occ_weight_list_swap.
  assert ((Γ0 ++ A → C  :: Γ1 ++ B → C :: Γ2) ++ [D] = Γ0 ++ [A→ C] ++ Γ1 ++ B → C :: Γ2 ++ [D]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  pose (list_occ_weight_list_swap Γ0 [A→ C] (Γ1 ++ B → C :: Γ2 ++ [D])). rewrite e. clear e.
  assert ([A→ C] ++ Γ0 ++ Γ1 ++ B → C :: Γ2 ++ [D] = (A→ C :: Γ0 ++ Γ1) ++ [B → C] ++ Γ2 ++ [D]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  pose (list_occ_weight_list_swap (A→ C :: Γ0 ++ Γ1) [B → C] (Γ2 ++ [D])). rewrite e. clear e.
  assert ([B → C] ++ (A→ C :: Γ0 ++ Γ1) ++ Γ2 ++ [D] = (B → C :: [A→ C]) ++ Γ0 ++ Γ1 ++ Γ2 ++ [D]).
  repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H1. clear H1.
  apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
  - destruct (max_weight_list [B → C; A→ C ]). destruct p. simpl. destruct (max_weight_list [(A ∨ B) → C]). destruct p. simpl.
    assert (x0 <= x).
    { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left.
       apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
       subst. inversion H3. 2: inversion H4. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq. }
    assert (x1 <= x).
    { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left.
       apply InT_or_app ; right ; apply InT_eq. inversion H4. }
    lia.
  - apply less_than_lt. destruct (max_weight_list [B → C;A→ C ]). destruct p. simpl. destruct (max_weight_list [(A ∨ B) → C ]). destruct p. simpl.
    apply max_less_length.
    assert (x0 <= Nat.max (weight_form (B → C)) (weight_form (A→ C))).
    { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. subst ; lia. inversion H4. }
    assert (weight_form ((A ∨ B) → C) <= x1).
    { apply l5. apply InT_eq. }
    simpl in H2. simpl in H1. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSOrImpL_less_than3 : forall prem concl, OrImpLRule [prem] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          (prem <3 concl).
Proof.
intros. unfold less_than3. pose (PSOrImpL_leq_init_switch H H0 H1). inversion l.
- subst. apply lex_skip. pose (PSOrImpL_leq_usable_boxes H). inversion l0.
  * rewrite H4. apply lex_skip. pose (PSOrImpL_less_weight H). auto.
  * apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
- apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.









(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* ImpImpL rule *)

Lemma PSImpImpL_leq_init_switch : forall prem1 prem2 concl, ImpImpLRule [prem1;prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          ((init_switch prem1 <= init_switch concl) * (init_switch prem2 <= init_switch concl)).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H2 ; auto. inversion H3.
subst. simpl. pose (init_switch_0_or_1 prem1). pose (init_switch_0_or_1 prem2).
destruct s. unfold init_switch in e. rewrite e. destruct s0. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e0. rewrite e0. split ; lia. destruct s0.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
Qed.

Lemma PSImpImpL_leq_usable_boxes : forall prem1 prem2 concl, ImpImpLRule [prem1;prem2] concl ->
                ((length (usable_boxes prem1) <= length (usable_boxes concl)) * (length (usable_boxes prem2) <= length (usable_boxes concl))).
Proof.
intros. inversion H. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app.
split.
- simpl (top_boxes (B → C :: Γ1)). simpl (top_boxes ((A → B) → C :: Γ1)).
  apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
  simpl. intro. apply in_app_or in H0 ; destruct H0. apply in_or_app ; left.
  repeat rewrite subform_boxesLF_dist_app ; repeat rewrite subform_boxesLF_dist_app in H0 ;
  apply in_app_or in H0 ; destruct H0 ; [ apply in_or_app ; auto | apply remove_list_is_in ;
  apply In_remove_list_In_list in H0 ; simpl in H0 ; apply in_app_or in H0 ; destruct H0 ].
  apply in_app_or in H0. destruct H0.
  simpl. apply in_or_app ; left. apply in_or_app ; left. apply remove_list_is_in ; auto.
  apply In_remove_list_In_list in H0. simpl. apply in_or_app ; left. apply remove_list_is_in ; auto.
  apply In_remove_list_In_list in H0. simpl. apply remove_list_is_in ; auto.
  apply In_remove_list_In_list in H0. apply in_app_or in H0. destruct H0.
  apply in_or_app ; left.  repeat rewrite subform_boxesLF_dist_app. apply remove_list_is_in.
  simpl. apply in_or_app ; left. apply in_or_app ; left. apply in_or_app ; auto.
  apply In_remove_list_In_list in H0.
  apply in_or_app ; left.  repeat rewrite subform_boxesLF_dist_app. apply remove_list_is_in.
  simpl. apply in_or_app ; left. apply in_or_app ; left. apply remove_list_is_in ; auto.
- simpl (top_boxes ((A → B) → C :: Γ1)).
  assert (length (remove_list (top_boxes Γ0 ++ top_boxes (C :: Γ1)) (subform_boxesS (Γ0 ++ (A → B) → C :: Γ1, D))) <=
  length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ (A → B) → C :: Γ1, D)))).
  { apply remove_list_incr_decr3. intro. intros. apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
    apply in_or_app ; right. simpl. destruct C ; auto. apply in_cons ; auto. }
  assert (length (remove_list (top_boxes Γ0 ++ top_boxes (C :: Γ1)) (subform_boxesS (Γ0 ++ C :: Γ1, D))) <=
  length (remove_list (top_boxes Γ0 ++ top_boxes (C :: Γ1)) (subform_boxesS (Γ0 ++ (A → B) → C :: Γ1, D)))).
  { apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
    simpl. intro. apply in_app_or in H1 ; destruct H1. apply in_or_app ; left.
    repeat rewrite subform_boxesLF_dist_app ; repeat rewrite subform_boxesLF_dist_app in H1 ;
    apply in_app_or in H1 ; destruct H1 ; [ apply in_or_app ; auto | apply remove_list_is_in ;
    apply In_remove_list_In_list in H1 ; simpl in H1 ; apply in_app_or in H1 ; destruct H1 ].
    simpl. apply in_or_app ; left. apply remove_list_is_in ; auto. apply In_remove_list_In_list in H1.
    simpl. apply remove_list_is_in ; auto. apply In_remove_list_In_list in H1.
    apply remove_list_is_in ; auto. }
  lia.
Qed.

Lemma PSImpImpL_less_weight : forall prem1 prem2 concl, ImpImpLRule [prem1;prem2] concl ->
                ((lex (less_than lt) [seq_list_occ_weight prem1] [seq_list_occ_weight concl]) *
                 (lex (less_than lt) [seq_list_occ_weight prem2] [seq_list_occ_weight concl])).
Proof.
intros. inversion H. subst. unfold seq_list_occ_weight. simpl. destruct (max_weight_list ((Γ0 ++ (A → B) → C :: Γ1) ++ [D])).
destruct p. simpl. split.
- destruct (max_weight_list ((Γ0 ++ B → C :: Γ1) ++ [A → B])). simpl. destruct p.
  assert (x0 <= x).
  { apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
    destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
    assert (InT ((A → B) → C) ((Γ0 ++ (A → B) → C :: Γ1) ++ [D])). apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_cons ; auto. inversion i. 2: inversion H1. subst.
    assert (InT ((A → B) → C) ((Γ0 ++ (A → B) → C :: Γ1) ++ [D])). apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_eq. pose (l _ H0). simpl in l3. simpl. lia. }
  inversion H0 ; subst.
  { apply lex_cons ; auto. apply less_than_eq.
     assert ((Γ0 ++ B → C :: Γ1) ++ [A → B] = (Γ0 ++ B → C :: Γ1) ++ [A → B] ++ []). repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap.
     assert ([A → B] ++ (Γ0 ++ B → C :: Γ1) ++ [] =(A → B :: Γ0) ++ [B → C] ++ Γ1). repeat rewrite <- app_assoc ; simpl ; rewrite app_nil_r ; auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. assert ([B → C] ++ (A → B :: Γ0) ++ Γ1 = (B → C :: [A → B]) ++ Γ0 ++ Γ1). auto. rewrite H1. clear H1.
     assert ((Γ0 ++ (A → B) → C :: Γ1) ++ [D] = (Γ0 ++ (A → B) → C :: Γ1) ++ [D] ++ []). rewrite app_nil_r ; auto. rewrite H1. clear H1.
     pose (list_occ_weight_list_swap (Γ0 ++ (A → B) → C :: Γ1) [D] []).
     rewrite e. clear e. rewrite app_nil_r.
     assert ([D] ++ Γ0 ++ (A → B) → C :: Γ1 = (D :: Γ0) ++ [(A → B) → C] ++ Γ1). repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     pose (list_occ_weight_list_swap (D :: Γ0) [(A → B) → C] Γ1). rewrite e. clear e.
     assert ([(A → B) → C] ++ (D :: Γ0) ++ Γ1 = [(A → B) → C;D] ++ Γ0 ++ Γ1). auto. rewrite H1. clear H1.
     apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [B → C; A → B]). destruct p. simpl. destruct (max_weight_list [(A → B) → C; D]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
          subst. inversion H3. 2: inversion H4. subst. apply l1. apply InT_or_app ; right. apply InT_eq. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left ; apply InT_or_app ; right ; apply InT_eq. inversion H4.
          subst. apply l. apply InT_or_app ; right ; apply InT_eq. inversion H7. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [B → C; A → B]). destruct p. simpl. destruct (max_weight_list [(A → B) → C; D]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= Nat.max (weight_form (B → C)) (weight_form (A → B))).
       { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. subst ; lia. inversion H4. }
       assert (weight_form ((A → B) → C) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. simpl in H1. lia. }
  { apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
- destruct (max_weight_list ((Γ0 ++ C :: Γ1) ++ [D])). simpl. destruct p.
  assert (x0 <= x).
  { apply l2. intros. apply InT_app_or in H0. destruct H0. apply InT_app_or in i.
    destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
    assert (InT ((A → B) → B0) ((Γ0 ++ (A → B) → B0 :: Γ1) ++ [D])). apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_eq. pose (l _ H0). simpl in l3. lia. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
    apply InT_cons ; auto. inversion i. 2: inversion H1. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
  inversion H0 ; subst.
  { apply lex_cons ; auto. apply less_than_eq.
     assert ((Γ0 ++ C :: Γ1) ++ [D] = Γ0 ++ [C] ++ (Γ1 ++ [D])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     assert ((Γ0 ++ (A → B) → C :: Γ1) ++ [D] = Γ0 ++ [(A → B) → C] ++ (Γ1 ++ [D])). rewrite <- app_assoc ; simpl ; auto. rewrite H1. clear H1.
     rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ0 [(A → B) → C] (Γ1 ++ [D])).
     rewrite e. clear e. apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
     - destruct (max_weight_list [C]). destruct p. simpl. destruct (max_weight_list [(A → B) → C]). destruct p. simpl.
       assert (x0 <= x).
       { apply l4. intros. inversion H1. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
          inversion H3. }
       assert (x1 <= x).
       { apply l6. intros. inversion H2. subst. apply l. apply InT_or_app ; left ; apply InT_or_app ; right ; apply InT_eq. inversion H4. }
       lia.
     - apply less_than_lt. destruct (max_weight_list [C]). destruct p. simpl. destruct (max_weight_list [(A → B) → C]). destruct p. simpl.
       apply max_less_length.
       assert (x0 <= weight_form C).
       { apply l4. intros. inversion H1. subst. lia. subst. inversion H3. }
       assert (weight_form ((A → B) → C) <= x1).
       { apply l5. apply InT_eq. }
       simpl in H2. lia. }
  { apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSImpImpL_less_than3 : forall prem1 prem2 concl, ImpImpLRule [prem1;prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          ((prem1 <3 concl) * (prem2 <3 concl)).
Proof.
intros. unfold less_than3. pose (PSImpImpL_leq_init_switch H H0 H1). destruct p. split.
- inversion l.
  * subst. apply lex_skip. pose (PSImpImpL_leq_usable_boxes H). destruct p. inversion l1.
    + rewrite H4. apply lex_skip. pose (PSImpImpL_less_weight H). destruct p ; auto.
    + apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
- inversion l0.
  * subst. apply lex_skip. pose (PSImpImpL_leq_usable_boxes H). destruct p. inversion l2.
    + rewrite H4. apply lex_skip. pose (PSImpImpL_less_weight H). destruct p ; auto.
    + apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.









(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* BoxImpL rule *)

Lemma PSBoxImpL_leq_init_switch : forall prem1 prem2 concl, BoxImpLRule [prem1;prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          ((init_switch prem1 <= init_switch concl) * (init_switch prem2 <= init_switch concl)).
Proof.
intros.
unfold init_switch.
destruct (dec_nat_init_switch_ind concl).
destruct p. destruct s. subst. exfalso. inversion i. destruct H1 ; auto. inversion H2.
subst. simpl. pose (init_switch_0_or_1 prem1). pose (init_switch_0_or_1 prem2).
destruct s. unfold init_switch in e. rewrite e. destruct s0. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e0. rewrite e0. split ; lia. destruct s0.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
unfold init_switch in e. rewrite e. unfold init_switch in e0. rewrite e0. split ; lia.
Qed.

Lemma BoxImpL_applic_le_subform_boxes : forall prem1 prem2 concl, BoxImpLRule [prem1;prem2] concl ->
                                                        (IdRule [] concl -> False) ->
                         forall B, (In B (subform_boxesS prem1)) -> (In B (subform_boxesS concl)).
Proof.
intros prem1 prem2 concl RA noId. inversion RA. subst.
intro. intros. unfold subform_boxesS in H. unfold subform_boxesS. simpl. simpl in H. apply in_app_or in H.
destruct H. rewrite subform_boxesLF_dist_app in H. apply in_app_or in H. destruct H.
apply in_or_app. left. apply univ_gen_ext_incl_subform_boxes in X.
pose (XBoxed_list_same_subform_boxes BΓ).
destruct a. apply H0 in H. clear H0. clear H1.
apply X in H. rewrite subform_boxesLF_dist_app in H. apply in_app_or in H. 
rewrite subform_boxesLF_dist_app. destruct H. apply in_or_app ; auto.
apply In_remove_list_In_list in H. apply remove_list_is_in.
simpl. destruct (eq_dec_form B0 (Box A)) ; auto. right.
destruct (In_dec (subform_boxesF A ++ remove eq_dec_form (Box A) (remove_list (subform_boxesF A) (subform_boxesF B))) B0).
apply in_or_app ; auto. apply in_or_app ; right. apply in_not_touched_remove ; auto.
apply not_removed_remove_list ; auto. apply In_remove_list_In_list in H. simpl in H. destruct H. subst.
apply in_or_app ; left. rewrite subform_boxesLF_dist_app. apply remove_list_is_in.
simpl ; auto. apply in_app_or in H. destruct H.
apply in_or_app ; left. rewrite subform_boxesLF_dist_app. apply remove_list_is_in.
simpl. right. apply in_or_app ; left ; apply in_or_app ; auto. apply In_remove_In_list in H.
rewrite remove_list_of_nil in H. inversion H.
apply In_remove_list_In_list in H. apply in_or_app ; left.  rewrite subform_boxesLF_dist_app. apply remove_list_is_in.
simpl. right. apply in_or_app ; left ; apply in_or_app ; auto.
Qed.

Lemma PSBoxImpL_prem1_le_usable_boxes : forall prem1 prem2 concl, BoxImpLRule [prem1;prem2] concl ->
                                                (IdRule [] concl -> False) ->
                                                (BotLRule [] concl -> False) ->
                                                (init_switch prem1 = init_switch concl) ->
                                                (length (usable_boxes prem1) < length (usable_boxes concl)).
Proof.
intros. inversion X. subst. unfold usable_boxes. simpl.
apply remove_list_incr_decr. 1-2: apply NoDup_subform_boxesS.
- exists (Box A). repeat split. rewrite top_boxes_distr_app. apply in_or_app. right. simpl ; auto.
  unfold subform_boxesS. simpl. apply in_or_app ; left.
  repeat rewrite subform_boxesLF_dist_app. apply remove_list_is_in. simpl ; auto.
  intro. rewrite top_boxes_distr_app in H2. simpl in H2.
  rewrite <- top_boxes_distr_app in H2. pose (in_top_boxes _ _ H2).
  repeat destruct s. destruct p. inversion e. subst. clear e.
  assert (exists x2 x3, (x2 ++ Box x :: x3) = BΓ).
  { rewrite e0 in X0. apply univ_gen_ext_splitR in X0. destruct X0. destruct s.
    repeat destruct p. subst. inversion u0. subst. exists x2. exists l ; auto. subst.
    exfalso ; apply H6 ; exists x ; auto. }
  destruct H3. destruct H3. rewrite <- H3 in H1.
  rewrite XBox_app_distrib in H1. simpl in H1.
  unfold init_switch in H1.
  destruct (dec_nat_init_switch_ind ((XBoxed_list x2 ++ x :: Box x :: XBoxed_list x3) ++ [Box x], x)).
  destruct p. simpl in H1. destruct s. subst. destruct (dec_nat_init_switch_ind (Γ0 ++ Box x → B :: Γ1, C)).
  destruct p. simpl in H1. subst. destruct s. inversion i0. destruct H1 ; auto. inversion H3.
  inversion e. subst. inversion i. inversion H4. apply H3. left. repeat rewrite <- app_assoc. simpl. constructor.
- intro A0. repeat rewrite top_boxes_distr_app.
  simpl. intro. apply in_or_app. left. rewrite <- top_boxes_distr_app in H2.
  assert (In A0 (Γ0 ++ Γ1)). apply in_top_boxes in H2.
  destruct H2. repeat destruct s. destruct p. subst. rewrite e0. apply in_or_app. right. apply in_eq.
  assert (InT A0 (Γ0 ++ Γ1)). apply in_splitT in H3. destruct H3. destruct s. rewrite e.
  apply InT_or_app. right. apply InT_eq. pose (InT_univ_gen_ext H4 X0). destruct s.
  exfalso. apply f. apply in_top_boxes in H2. destruct H2. repeat destruct s.
  destruct p. exists x. assumption. apply top_boxes_incl_list in H2.
  pose (list_preserv_XBoxed_list BΓ). pose (InT_In i). apply i0 in i1.
  apply is_box_in_top_boxes. apply i0. apply InT_In. assumption.
  apply H5. apply InT_In. assumption.
- intro A0. pose (BoxImpL_applic_le_subform_boxes X H). intros. apply i. auto.
Qed.

Lemma PSBoxImpL_prem2_leq_usable_boxes : forall prem1 prem2 concl, BoxImpLRule [prem1;prem2] concl ->
                (length (usable_boxes prem2) <= length (usable_boxes concl)).
Proof.
intros. inversion X. subst. unfold usable_boxes. simpl. repeat rewrite top_boxes_distr_app.
simpl (top_boxes (Box A → B :: Γ1)).
assert (length (remove_list (top_boxes Γ0 ++ top_boxes (B :: Γ1)) (subform_boxesS (Γ0 ++ Box A → B :: Γ1, C))) <=
length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ Box A → B :: Γ1, C)))).
{ apply remove_list_incr_decr3. intro. intros. apply in_app_or in H ; destruct H. apply in_or_app ; auto.
  apply in_or_app ; right. simpl. destruct B ; auto. apply in_cons ; auto. }
assert (length (remove_list (top_boxes Γ0 ++ top_boxes (B :: Γ1)) (subform_boxesS (Γ0 ++ B :: Γ1, C))) <=
length (remove_list (top_boxes Γ0 ++ top_boxes (B :: Γ1)) (subform_boxesS (Γ0 ++ Box A → B :: Γ1, C)))).
{ apply remove_list_incr_decr2. 1-2: apply NoDup_subform_boxesS. intro. unfold subform_boxesS.
  simpl. intro. apply in_app_or in H0 ; destruct H0. apply in_or_app ; left.
  repeat rewrite subform_boxesLF_dist_app ; repeat rewrite subform_boxesLF_dist_app in H0 ;
  apply in_app_or in H0 ; destruct H0 ; [ apply in_or_app ; auto | apply remove_list_is_in ;
  apply In_remove_list_In_list in H0 ; simpl in H0 ; apply in_app_or in H0 ; destruct H0 ].
  simpl. destruct (eq_dec_form a (Box A)). auto. right. apply in_or_app ; left.
  destruct (In_dec (subform_boxesF A) a). apply in_or_app ; auto. apply in_or_app ; right.
  apply in_not_touched_remove ; auto. apply not_removed_remove_list ; auto.
  apply In_remove_list_In_list in H0. apply remove_list_is_in. auto.
  apply In_remove_list_In_list in H0. apply remove_list_is_in ; auto. }
lia.
Qed.

Lemma PSBoxImpL_prem2_less_weight : forall prem1 prem2 concl, BoxImpLRule [prem1;prem2] concl ->
                 (lex (less_than lt) [seq_list_occ_weight prem2] [seq_list_occ_weight concl]).
Proof.
intros. inversion X. subst. unfold seq_list_occ_weight. simpl. destruct (max_weight_list ((Γ0 ++ Box A → B :: Γ1) ++ [C])).
destruct p. simpl. destruct (max_weight_list ((Γ0 ++ B :: Γ1) ++ [C])). simpl. destruct p.
assert (x0 <= x).
{ apply l2. intros. apply InT_app_or in H. destruct H. apply InT_app_or in i.
  destruct i. apply l. apply InT_or_app ; left. apply InT_or_app ; auto. inversion i. subst.
  assert (InT (Box A → B0) ((Γ0 ++Box A → B0 :: Γ1) ++ [C])). apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_eq. pose (l _ H). simpl in l3. lia. subst. apply l. apply InT_or_app ; left. apply InT_or_app ; right.
  apply InT_cons ; auto. inversion i. 2: inversion H0. subst. apply l. apply InT_or_app ; right ; apply InT_eq. }
inversion H ; subst.
{ apply lex_cons ; auto. apply less_than_eq.
   assert ((Γ0 ++ B :: Γ1) ++ [C] = Γ0 ++ [B] ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H0. clear H0.
   assert ((Γ0 ++ Box A → B :: Γ1) ++ [C] = Γ0 ++ [Box A → B] ++ (Γ1 ++ [C])). rewrite <- app_assoc ; simpl ; auto. rewrite H0. clear H0.
   rewrite list_occ_weight_list_swap. pose (list_occ_weight_list_swap Γ0 [Box A → B] (Γ1 ++ [C])).
   rewrite e. clear e. apply list_occ_weight_list_headlist. apply list_occ_weight_list_relevant.
   - destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [Box A → B]). destruct p. simpl.
     assert (x0 <= x).
     { apply l4. intros. inversion H0. subst. apply l1. apply InT_or_app ; left. apply InT_or_app ; right ; apply InT_eq.
        inversion H3. }
     assert (x1 <= x).
     { apply l6. intros. inversion H1. subst. apply l. apply InT_or_app ; left ; apply InT_or_app ; right ; apply InT_eq. inversion H4. }
     lia.
   - apply less_than_lt. destruct (max_weight_list [B]). destruct p. simpl. destruct (max_weight_list [Box A → B]). destruct p. simpl.
     apply max_less_length.
     assert (x0 <= weight_form B).
     { apply l4. intros. inversion H0. subst. lia. subst. inversion H3. }
     assert (weight_form (Box A → B) <= x1).
     { apply l5. apply InT_eq. }
     simpl in H1. lia. }
{ apply lex_cons ; auto. apply less_than_lt. repeat rewrite length_max ; lia. }
Qed.

Theorem PSBoxImpL_less_than3 : forall prem1 prem2 concl, BoxImpLRule [prem1;prem2] concl ->
                                                          (IdRule [] concl -> False) ->
                                                          (BotLRule [] concl -> False) ->
                                                          ((prem1 <3 concl) * (prem2 <3 concl)).
Proof.
intros. unfold less_than3. pose (PSBoxImpL_leq_init_switch X H H0). destruct p. split.
- inversion l.
  * subst. apply lex_skip. pose (PSBoxImpL_prem1_le_usable_boxes X H H0 H2).
     apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
- inversion l0.
  * subst. apply lex_skip. pose (PSBoxImpL_prem2_leq_usable_boxes X). inversion l1.
    + rewrite H3. apply lex_skip. pose (PSBoxImpL_prem2_less_weight X) ; auto.
    + apply lex_cons ; auto. apply less_than_eq. apply lex_cons ; auto. lia.
  * apply lex_cons. auto. apply less_than_eq. apply lex_cons ; auto. lia.
Qed.









(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* All rules. *)



Theorem PSGL4ip_less_than3 : forall prems concl, PSGL4ip_rules prems concl ->
                                                    (forall prem, InT prem prems -> prem <3 concl).
Proof.
intros. inversion X ; subst.
1-2: inversion H0 ; subst ; inversion H.
1-11: inversion H2 ; subst.
inversion H ; subst. apply PSAndR_less_than3 with (prem2:=(Γ, B)) ; auto.
inversion H4 ; subst. apply PSAndR_less_than3 with (prem1:=(Γ, A)) ; auto. inversion H5.
inversion H ; subst. apply PSAndL_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSOrR1_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSOrR2_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSOrL_less_than3 with (prem2:=(Γ0 ++ B :: Γ1, C)) ; auto.
inversion H4 ; subst. apply PSOrL_less_than3 with (prem1:=(Γ0 ++ A :: Γ1, C)) ; auto. inversion H5.
inversion H ; subst. apply PSImpR_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSAtomImpL1_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSAtomImpL2_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSAndImpL_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSOrImpL_less_than3 ; auto. inversion H4.
inversion H ; subst. apply PSImpImpL_less_than3 with (prem2:=(Γ0 ++ C :: Γ1, D)) ; auto.
inversion H4 ; subst. apply PSImpImpL_less_than3 with (prem1:=(Γ0 ++ B → C :: Γ1, A → B)) ; auto. inversion H5.
1-2: inversion X0 ; subst.
inversion H ; subst. apply PSBoxImpL_less_than3 with (prem2:=(Γ0 ++ B :: Γ1, C)) ; auto.
inversion H4 ; subst. apply PSBoxImpL_less_than3 with (prem1:=(XBoxed_list BΓ ++ [Box A], A)) ; auto. inversion H5.
inversion H ; subst. apply PSGLR_less_than3 ; auto. inversion H4.
Qed.




