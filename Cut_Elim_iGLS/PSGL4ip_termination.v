Require Import GL4ip_PSGL4ip_calcs.
Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.
Require Import univ_gen_ext.
Require Import GL4ip_PSGL4ip_list_lems.
Require Import dd_fc.
Require Import PeanoNat.
Require Import Coq.Init.Nat.
Require Import strong_inductionT.
Require Import PSGL4ip_termination_measure.
Require Import GL4ip_PSGL4ip_remove_list.
Require Import GL4ip_PSGL4ip_dec.
Require Import Lia.

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

Lemma In_InT : forall (A : MPropF) l, In A l -> InT A l.
Proof.
intros. apply in_splitT in H. destruct H. destruct s. subst. apply InT_or_app. right.
apply InT_eq.
Qed.

Lemma In_InT_pair : forall (A : MPropF) (n : nat) l, In (A, n) l -> InT (A, n) l.
Proof.
induction l.
- intro. inversion H.
- intro. assert ({(A, n) = a} + {(A, n) <> a}). destruct a.
  destruct (eq_dec_form A m). subst. destruct (eq_dec_nat n n0). subst. auto.
  right. intro. apply n1. inversion H0. auto. right. intro. inversion H0.
  auto. destruct H0. subst. apply InT_eq. apply InT_cons. apply IHl.
  inversion H. exfalso. auto. assumption.
Qed.

Lemma dec_le : forall n m, (n <= m) + ((n <= m) -> False).
Proof.
induction n.
- intro m. left. apply le_0_n.
- intro m. pose (IHn m). destruct s.
  * destruct (eq_dec_nat n m). subst. right. intro. lia. left. lia.
  * right. intro. apply f. lia.
Qed.

Lemma InT_map_iff : forall {A B : Type} (f : A -> B) (l : list A) (y : B),
       (InT y (map f l) -> (existsT2 x : A, (f x = y) * InT x l)) *
       ((existsT2 x : A, (f x = y) * InT x l) -> InT y (map f l)).
Proof.
induction l.
- intros. simpl. split. intro. inversion X. intro. destruct X. destruct p. inversion i.
- simpl. intros. split.
  * intro. inversion X.
    + subst. exists a. split ; [ reflexivity | apply InT_eq].
    + subst. pose (IHl y). destruct p. apply s in X0. destruct X0. destruct p. exists x.
      split. assumption. apply InT_cons. assumption.
  * intro. pose (IHl y). destruct p. clear s. pose (proj2_sigT2 X).
    destruct p. inversion i0. subst. rewrite <- e. rewrite <- H0. apply InT_eq.
    subst. assert (existsT2 x : A, (f x = y) * InT x l). exists (proj1_sigT2 X).
    split ; assumption. apply i in X1. apply InT_cons. assumption.
Qed.

Lemma le_False_lt : forall n m, ((n <= m) -> False) -> (m < n).
Proof.
induction n.
- intros. exfalso. apply H. apply le_0_n.
- induction m.
  * intros. lia.
  * intros. apply Lt.lt_n_S. apply IHn. intro. apply H. apply Le.le_n_S. assumption.
Qed.

Lemma top_boxes_nobox_gen_ext : forall l, nobox_gen_ext (top_boxes l) l.
Proof.
induction l.
- simpl. apply univ_gen_ext_nil.
- destruct a ; simpl.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_cons. assumption.
Qed.

Lemma nobox_gen_ext_top_boxes_identity : forall l0 l1, nobox_gen_ext l0 l1 ->
                                                       is_Boxed_list l0 ->
                                                       (l0 = top_boxes l1).
Proof.
intros l0 l1 X. induction X.
- intros. reflexivity.
- intro. simpl. destruct x.
  * exfalso. pose (H (# v)). assert (In # v (# v :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (⊥)). assert (In (⊥) (⊥ :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (x1 ∧ x2)). assert (In (x1 ∧ x2) (x1 ∧ x2 :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (x1 ∨ x2)). assert (In (x1 ∨ x2) (x1 ∨ x2 :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (x1 → x2)). assert (In (x1 → x2) (x1 → x2 :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * assert (l = top_boxes le). apply IHX. intro. intros. apply H. apply in_cons. assumption.
    rewrite H0. reflexivity.
- simpl. destruct x.
  * apply IHX.
  * apply IHX.
  * apply IHX.
  * apply IHX.
  * apply IHX.
  * exfalso. apply p. exists x. reflexivity.
Qed.

Fixpoint flatten_list {A : Type} (l : list (list A)) : list A :=
  match l with
  | [ ] => [ ]
  | h :: t => h ++ (flatten_list t)
  end
.

Lemma InT_flatten_list_InT_elem {A : Type} : forall (l : list (list A)) b,
        InT b (flatten_list l) -> (existsT2 bs, (InT b bs) * (InT bs l)).
Proof.
induction l.
- intros. simpl in X. inversion X.
- intros. simpl in X. apply InT_app_or in X. destruct X.
  * exists a. split ; [assumption | apply InT_eq].
  * pose (IHl b). apply s in i. destruct i. destruct p. exists x. split ; [assumption | apply InT_cons ; assumption].
Qed.

Lemma redundant_flatten_list : forall ls (s : Seq), map (fun z : list (MPropF) * (MPropF) => [z;s]) ls =
flatten_list (map (fun y : list (MPropF) * (MPropF) => [[y;s]]) ls).
Proof.
induction ls.
- intros. simpl. reflexivity.
- simpl. intros. rewrite IHls. reflexivity.
Qed.

Lemma InT_trans_flatten_list {A : Type} : forall (l : list (list A)) bs b,
        (InT b bs) -> (InT bs l) -> (InT b (flatten_list l)).
Proof.
induction l.
- intros. inversion X0.
- intros. inversion X0.
  * subst. simpl. apply InT_or_app. auto.
  * subst. simpl. apply InT_or_app. right. pose (IHl bs b X X1) ; assumption.
Qed.

(* In this file we prove that each sequent Γ |- Δ has a derivation (not proof) D in
   PSGL4ip of maximal height: all derivations in PSGL4ip of this sequent must have an
   inferior or equal height to that of D.

   This result can be understood as claiming that the proof search defined by PSGL4ip
   terminates. *)

(* The next lemma claims that for each sequent s there is a derivation of that sequent. *)

Lemma der_s_inhabited : forall s, inhabited (derrec PSGL4ip_rules (fun _ => True) s).
Proof.
intros s.
pose (@dpI ((list (MPropF)) *(MPropF) ) PSGL4ip_rules (fun _ : ((list (MPropF)) *(MPropF)) => True) s).
assert (H: (fun _ : ((list (MPropF)) *(MPropF) ) => True) s). apply I. apply d in H. apply inhabits. assumption.
Qed.

(* The next definition deals with the property of being a derivation D0 of maximal height
   for the sequent s. *)

Definition is_mhd (s: Seq) (D0 : derrec (PSGL4ip_rules) (fun _ => True) s): Prop :=
      forall (D1 : derrec (PSGL4ip_rules) (fun _ => True) s), derrec_height D1 <= derrec_height D0.


(* The next lemma says that given a list and an element, there are only finitely many
   ways to insert this element in a list. *)

Lemma list_of_splits : forall (l : list (MPropF)), existsT2 listSplits,
                            forall l1 l2, ((l1 ++ l2 = l) <-> In (l1, l2) listSplits).
Proof.
induction l.
- exists [([],[])]. intros. destruct l1. split ; intro. simpl in H. rewrite H. apply in_eq.
  simpl in H. destruct H. inversion H. reflexivity. inversion H. split ; intro.
  simpl in H. inversion H. simpl. inversion H. inversion H0. inversion H0.
- destruct IHl. exists ([([], a :: l)] ++ (map (fun y => (a :: (fst y), snd y)) x)).
  intros. split ; intro.
  * apply in_or_app. destruct l1. simpl. left. left. simpl in H. rewrite H.
    reflexivity. simpl in H. inversion H. subst. right. pose (i l1 l2). destruct i0.
    assert (l1 ++ l2 = l1 ++ l2). reflexivity. apply H0 in H2.
    pose (in_map (fun y : list (MPropF) * list (MPropF) => (a :: fst y, snd y)) x (l1, l2) H2).
    simpl in i. assumption.
  * simpl in H. destruct H. inversion H. simpl. reflexivity. rewrite in_map_iff in H.
    destruct H. destruct H. inversion H. subst. simpl. pose (i (fst x0) (snd x0)).
    destruct i0. assert ((fst x0, snd x0) = x0). destruct x0. simpl. reflexivity.
    rewrite H3 in H2. apply H2 in H0. rewrite H0. reflexivity.
Qed.

Definition listInserts l (A : MPropF) := map (fun y => (fst y) ++ A :: (snd y)) (proj1_sigT2 (list_of_splits l)).

(* The next two lemmas make sure that the definition listInserts indeed captures the intended
   list. *)

Lemma listInserts_In : forall l (A: MPropF) l1 l2, ((l1 ++ l2 = l) -> In (l1 ++ A :: l2) (listInserts l A)).
Proof.
intros. unfold listInserts. assert (In (l1, l2) (proj1_sigT2 (list_of_splits l))). destruct (list_of_splits l).
simpl. pose (i l1 l2). apply i0. assumption.
pose (in_map (fun y : list (MPropF) * list (MPropF) => fst y ++ A :: snd y) (proj1_sigT2 (list_of_splits l)) (l1, l2) H0).
simpl in i. assumption.
Qed.

Lemma listInserts_InT : forall l (A: MPropF) l1 l2, ((l1 ++ l2 = l) -> InT (l1 ++ A :: l2) (listInserts l A)).
Proof.
intros. unfold listInserts. assert (InT (l1, l2) (proj1_sigT2 (list_of_splits l))). destruct (list_of_splits l). apply In_InT_seqs.
simpl. pose (i l1 l2). apply i0. assumption.
pose (InT_map (fun y : list (MPropF) * list (MPropF) => fst y ++ A :: snd y) H0).
simpl in i. assumption.
Qed.

Lemma In_listInserts : forall l (A: MPropF) l0, In l0 (listInserts l A) ->
                            (exists l1 l2, prod (l1 ++ l2 = l) (l1 ++ A :: l2 = l0)).
Proof.
intros. unfold listInserts in H. destruct (list_of_splits l). simpl in H. rewrite in_map_iff in H.
destruct H. destruct H. subst. exists (fst x0). exists (snd x0). split. apply i.
destruct x0. simpl. assumption. reflexivity.
Qed.

Lemma InT_listInserts : forall l (A: MPropF) l0, InT l0 (listInserts l A) ->
                            (existsT2 l1 l2, prod (l1 ++ l2 = l) (l1 ++ A :: l2 = l0)).
Proof.
intros. unfold listInserts in H. destruct (list_of_splits l). simpl in H. apply InT_map_iff in H.
destruct H. subst. exists (fst x0). exists (snd x0). split. apply i.
destruct x0. destruct p. simpl. apply InT_In ; auto. destruct p. subst. reflexivity.
Qed.

(* The definitions below allow you to create the list of all sequents given two lists and a
   formula to insert in one of them. *)

Definition listInsertsL_Seqs (Γ : list (MPropF)) (A C : MPropF) := map (fun y => (y, C)) (listInserts Γ A).

Fixpoint remove_nth (n: nat) (A : MPropF) l:=
    match n with
      | 0 => l
      | 1 => match l with
               | [] => []
               | B::tl => if (eq_dec_form A B) then tl else B:: tl
             end
      | S m => match l with
                 | [] => []
                 | B::tl => B::(remove_nth m A tl)
               end
      end.

Fixpoint nth_split (n : nat) (l : list (MPropF)) : (list (MPropF) * list (MPropF)) :=
    match n with
      | 0 => ([], l)
      | 1 => match l with
               | [] => ([], [])
               | B::tl => ([B] , tl)
             end
      | S m => match l with
                 | [] => ([], [])
                 | B::tl => (B :: (fst (nth_split m tl)), snd (nth_split m tl))
               end
      end.

Lemma nth_split_length : forall (l0 l1 : list (MPropF)), (nth_split (length l0) (l0 ++ l1)) = (l0, l1).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. pose (IHl0 l1). simpl (length (a :: l0)). simpl ((a :: l0) ++ l1).
  simpl. destruct l0.
  * simpl. reflexivity.
  * assert (match length (m :: l0) with
| 0 => ([a], (m :: l0) ++ l1)
| S _ =>
    (a :: fst (nth_split (length (m :: l0)) ((m :: l0) ++ l1)),
    snd (nth_split (length (m :: l0)) ((m :: l0) ++ l1)))
end = (a :: fst (nth_split (length (m :: l0)) ((m :: l0) ++ l1)),
    snd (nth_split (length (m :: l0)) ((m :: l0) ++ l1)))). reflexivity. rewrite H.
clear H. rewrite e. simpl. reflexivity.
Qed.

Lemma effective_remove_nth : forall A l0 l1, ((remove_nth (S (length l0)) A (l0 ++ A :: l1)) = l0 ++ l1).
Proof.
induction l0.
- intros. simpl. destruct (eq_dec_form A A). reflexivity. exfalso. auto.
- intros. simpl (S (length (a :: l0))). repeat rewrite <- app_assoc. simpl ((a :: l0) ++ A :: l1).
  pose (IHl0 l1). simpl ((a :: l0) ++ l1). rewrite <- e. simpl. reflexivity.
Qed.

Lemma nth_split_idL : forall (l0 l1 : list (MPropF)), l0 = fst (nth_split (length l0) (l0 ++ l1)).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. simpl (length (a :: l0)). pose (IHl0 l1). assert (fst (nth_split (S (length l0)) ((a :: l0) ++ l1)) =
  a :: fst (nth_split (length l0) (l0 ++ l1))). simpl. destruct l0. simpl. reflexivity.
  simpl. reflexivity. rewrite H. rewrite <- e. reflexivity.
Qed.

Lemma nth_split_idR : forall (l0 l1 : list (MPropF)), l1 = snd (nth_split (length l0) (l0 ++ l1)).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. simpl (length (a :: l0)). pose (IHl0 l1). rewrite e. destruct l0.
  * simpl. reflexivity.
  * simpl (length (m :: l0)). simpl (S (S (length l0))).
    simpl (length (m :: l0)) in e. rewrite <- e.
    assert ((S (S (length l0))) = (length (a :: m :: l0))). simpl. reflexivity.
    rewrite H. rewrite nth_split_length. simpl. reflexivity.
Qed.

Lemma nth_split_length_id : forall (l0 l1 : list (MPropF)) n, (length l0 = n) ->
                                (fst (nth_split n (l0 ++ l1)) = l0 /\
                                snd (nth_split n (l0 ++ l1)) = l1).
Proof.
induction l0.
- intros. simpl. split. simpl in H. subst. simpl. reflexivity. simpl in H. subst. simpl. reflexivity.
- intros. simpl in H. subst. split.
  * assert (J1:length l0 = length l0). reflexivity. pose (@IHl0 l1 (length l0) J1).
    destruct a0. simpl. destruct l0. simpl. reflexivity. simpl. rewrite <- H.
    simpl. reflexivity.
  * assert (J1:length l0 = length l0). reflexivity. pose (@IHl0 l1 (length l0) J1).
    destruct a0. rewrite <- H0. simpl ((a :: l0) ++ snd (nth_split (length l0) (l0 ++ l1))).
    assert ((nth_split (S (length l0)) (a :: l0 ++ snd (nth_split (length l0) (l0 ++ l1))) =
    (a :: l0 ,snd (nth_split (length l0) (l0 ++ l1))))).
    pose (nth_split_length (a :: l0) (snd (nth_split (length l0) (l0 ++ l1)))). apply e.
    rewrite H1. simpl. reflexivity.
Qed.





(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* And rules *)

(* Let's start with AndR *)

Definition prems_And_R (s : Seq) : list (list (Seq)) :=
match (snd s) with
  | And A B => [[(fst s, A);(fst s, B)]]
  | _ => nil
end.

Lemma finite_AndR_premises_of_S : forall (s : Seq), existsT2 listAndRprems,
              (forall prems, ((AndRRule prems s) -> (InT prems listAndRprems)) *
                             ((InT prems listAndRprems) -> (AndRRule prems s))).
Proof.
intro s.
exists (prems_And_R s). intros. split ; intros. inversion H. subst. unfold prems_And_R.
simpl. apply InT_eq. unfold prems_And_R in H. destruct s. simpl in H.
destruct m. 1-2: inversion H. 2-4: inversion H. inversion H. subst. apply AndRRule_I.
inversion H1.
Qed.



(* And now AndL *)

Fixpoint top_ands (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | And A B => (And A B) :: top_ands t
                | _ => top_ands t
              end
end.

Fixpoint pos_top_ands (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | And A B => (And A B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_ands t))
                | _ => (map (fun y => (fst y, S  (snd y))) (pos_top_ands t))
              end
end.

Fixpoint prems_And_L (l : list ((MPropF) * nat)) (s : Seq) : list (Seq) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_And_L t s
      | S m => match C with
           | And A B => ((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ A :: B :: (snd (nth_split m (remove_nth (S m) C (fst s)))) , snd s)
                                :: (prems_And_L t s)
           | _ => prems_And_L t s
           end
      end
end.

Lemma In_pos_top_ands_0_False : forall l (A : MPropF), In (A, 0) (pos_top_ands l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-2: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2-4: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_ands_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_ands l) -> 
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ands_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ands_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. inversion H.
    + inversion H1. subst. exists []. exists l. repeat split. simpl.
      destruct (eq_dec_form (a1 ∧ a2) (a1 ∧ a2)). reflexivity. exfalso. auto.
    + subst. apply InT_map_iff in H1. destruct H1. destruct p.
      destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
      apply InT_In in i. apply In_pos_top_ands_0_False in i. assumption.
      apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
      subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
      rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
      assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
      assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
      rewrite H1. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
      rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
      assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
      rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ands_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ands_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 → a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ands_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma Good_pos_in_pos_top_ands : forall A B Γ0 Γ1,
              In (And A B, S (length Γ0)) (pos_top_ands (Γ0 ++ And A B :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  1-2: simpl ; apply InT_In ; apply InT_map_iff ; exists (And A B, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (And A B, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. right. apply InT_In. apply InT_map_iff. exists (And A B, S (length Γ0)).
  split. simpl. reflexivity. apply In_InT_pair. apply IHΓ0.
Qed.

Lemma AndL_help01 : forall prem s l, InT prem (prems_And_L l s) ->
                  (existsT2 n A B Γ0 Γ1 C,
                        (In (And A B, S n) l) *
                        (prem = (Γ0 ++ A :: B :: Γ1, C)) *
                        (C = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (And A B) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (And A B) (fst s)))))).
Proof.
intros prem s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). destruct a. destruct m0.
  1-2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  2-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
     exists x2. exists x3. exists x4. repeat split ; try auto. apply in_cons. assumption.
  + inversion H.
    { simpl in H1. simpl in H0. simpl (fst (l, m)) in IHl0. simpl (snd (l, m)) in IHl0.
      exists n. exists m0_1. exists m0_2.
      exists (fst (nth_split n match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form (m0_1 ∧ m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n (m0_1 ∧ m0_2) tl
                    end
           end)).
      exists (snd (nth_split n match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form (m0_1 ∧ m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n (m0_1 ∧ m0_2) tl
                    end
           end)). exists m. repeat split ; auto. apply in_eq. }
    { pose (IHl0 H1). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. repeat split ; try auto. apply in_cons. assumption. }
Qed.

Lemma AndL_help1 : forall prem s, InT prem (prems_And_L (pos_top_ands (fst s)) s) -> AndLRule [prem] s.
Proof.
intros. pose (@AndL_help01 _ _ _ H). repeat destruct s0. destruct s.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)).
simpl (fst (l, m)) in H. simpl (snd (l, m)). simpl (snd (l, m)) in H.
apply In_pos_top_ands_split_l in i.
destruct i. destruct s. repeat destruct p.
subst. rewrite <- e. rewrite <- e0. apply AndLRule_I.
Qed.

Lemma AndL_help002 : forall Γ0 Γ1 l C A B,
           InT (Γ0 ++ A :: B :: Γ1, C) (prems_And_L ((A ∧ B, S (length Γ0)) :: l) (Γ0 ++ A ∧ B :: Γ1, C)).
Proof.
intros. unfold prems_And_L.
simpl (fst (Γ0 ++ A ∧ B :: Γ1, C)). simpl (snd (Γ0 ++ A ∧ B :: Γ1, C)).
repeat rewrite effective_remove_nth. pose (nth_split_idL Γ0 Γ1).
rewrite <- e. pose (nth_split_idR Γ0 Γ1). rewrite <- e0. apply InT_eq.
Qed.

Lemma AndL_help02 : forall Γ0 Γ1 C A B l n,
            AndLRule [(Γ0 ++ A :: B :: Γ1, C)] (Γ0 ++ (And A B) :: Γ1, C) ->
            (length Γ0 = n) ->
            (In ((And A B), S n) l) ->
            InT (Γ0 ++ A :: B :: Γ1, C) (prems_And_L l (Γ0 ++ (And A B) :: Γ1, C)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  1-2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  * apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. apply AndL_help002.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
       pose (IHl (length Γ0) H J1 H3). simpl. destruct n0 ; auto. apply InT_cons ; auto.
Qed.

Lemma AndL_help2 : forall prem s, AndLRule [prem] s -> InT prem (prems_And_L (pos_top_ands (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@AndL_help02 Γ0 Γ1 C A B (pos_top_ands (Γ0 ++ (And A B) :: Γ1)) (length Γ0)). apply i ; try assumption ; auto.
apply Good_pos_in_pos_top_ands.
Qed.

Lemma finite_AndL_premises_of_S : forall (s : Seq), existsT2 listAndLprems,
              (forall prems, ((AndLRule prems s) -> (InT prems listAndLprems)) *
                             ((InT prems listAndLprems) -> (AndLRule prems s))).
Proof.
intros. destruct s.
exists (map (fun y => [y]) (prems_And_L (pos_top_ands l) (l,m))).
intros. split ; intro.
- inversion H. subst.
  pose (AndL_help2 H). apply InT_map_iff. exists (Γ0 ++ A :: B :: Γ1, m) ; split ; auto.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply AndL_help1. simpl. assumption.
Qed.


(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* Or rules *)

(* Let's start with OrR1 *)

Definition prems_Or_R1 (s : Seq) : list (list (Seq)) :=
match (snd s) with
  | Or A B => [[(fst s, A)]]
  | _ => nil
end.

Lemma finite_OrR1_premises_of_S : forall (s : Seq), existsT2 listOrR1prems,
              (forall prems, ((OrR1Rule prems s) -> (InT prems listOrR1prems)) *
                             ((InT prems listOrR1prems) -> (OrR1Rule prems s))).
Proof.
intros. exists (prems_Or_R1 s). intros. split ; intro.
inversion H. subst. unfold prems_Or_R1. simpl. apply InT_eq.
unfold prems_Or_R1 in H. destruct s. destruct m ; inversion H. 2: inversion H1.
subst. apply OrR1Rule_I.
Qed.

(* And OrR2 *)

Definition prems_Or_R2 (s : Seq) : list (list (Seq)) :=
match (snd s) with
  | Or A B => [[(fst s, B)]]
  | _ => nil
end.

Lemma finite_OrR2_premises_of_S : forall (s : Seq), existsT2 listOrR2prems,
              (forall prems, ((OrR2Rule prems s) -> (InT prems listOrR2prems)) *
                             ((InT prems listOrR2prems) -> (OrR2Rule prems s))).
Proof.
intros. exists (prems_Or_R2 s). intros. split ; intro.
inversion H. subst. unfold prems_Or_R2. simpl. apply InT_eq.
unfold prems_Or_R2 in H. destruct s. destruct m ; inversion H. 2: inversion H1.
subst. apply OrR2Rule_I.
Qed.



(* And now OrL *)

Fixpoint top_ors (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Or A B => (Or A B) :: top_ors t
                | _ => top_ors t
              end
end.

Fixpoint pos_top_ors (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Or A B => (Or A B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_ors t))
                | _ => (map (fun y => (fst y, S  (snd y))) (pos_top_ors t))
              end
end.

Fixpoint prems_Or_L (l : list ((MPropF) * nat)) (s : Seq) : list (list (Seq)) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_Or_L t s
      | S m => match C with
           | Or A B => [((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ A :: (snd (nth_split m (remove_nth (S m) C (fst s)))) , snd s);
                               ((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ B :: (snd (nth_split m (remove_nth (S m) C (fst s)))) , snd s)]
                                :: (prems_Or_L t s)
           | _ => prems_Or_L t s
           end
      end
end.

Lemma In_pos_top_ors_0_False : forall l (A : MPropF), In (A, 0) (pos_top_ors l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-3: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2-3: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_ors_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_ors l) -> 
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ors_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ors_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ors_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. inversion H.
    + inversion H1. subst. exists []. exists l. repeat split. simpl.
      destruct (eq_dec_form (a1 ∨ a2) (a1 ∨ a2)). reflexivity. exfalso. auto.
    + subst. apply InT_map_iff in H1. destruct H1. destruct p.
      destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
      apply InT_In in i. apply In_pos_top_ors_0_False in i. assumption.
      apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
      subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
      rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
      assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
      assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
      rewrite H1. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
      rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
      assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
      rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ors_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 → a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_ors_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma Good_pos_in_pos_top_ors : forall A B Γ0 Γ1,
              In (Or A B, S (length Γ0)) (pos_top_ors (Γ0 ++ Or A B :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  1-3: simpl ; apply InT_In ; apply InT_map_iff ; exists (Or A B, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2-3: simpl ; apply InT_In ; apply InT_map_iff ; exists (Or A B, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. right. apply InT_In. apply InT_map_iff. exists (Or A B, S (length Γ0)).
  split. simpl. reflexivity. apply In_InT_pair. apply IHΓ0.
Qed.

Lemma OrL_help01 : forall prems s l, InT prems (prems_Or_L l s) ->
                  (existsT2 n prem1 prem2 A B Γ0 Γ1 C,
                        (prems = [prem1; prem2]) *
                        (In ((Or A B), S n) l) *
                        (prem1 = (Γ0 ++ A :: Γ1, C)) *
                        (prem2 = (Γ0 ++ B :: Γ1, C)) *
                        (C = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Or A B) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Or A B) (fst s)))))).
Proof.
intros prems s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). simpl (snd (l, m)). destruct a. destruct m0.
  1-3: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
      exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  2-3: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
      exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
    exists x2. exists x3. exists x4. exists x5. exists x6. repeat split ; try auto. apply in_cons. assumption.
  + inversion H.

    { simpl in H1. simpl in H0. simpl (fst (l, m)) in IHl0. simpl (snd (l, m)) in IHl0.
      exists n.
      exists (fst
         (nth_split n
            match n with
            | 0 => match l with
                   | [] => []
                   | B :: tl => if eq_dec_form (m0_1 ∨ m0_2) B then tl else B :: tl
                   end
            | S _ => match l with
                     | [] => []
                     | B :: tl => B :: remove_nth n (m0_1 ∨ m0_2) tl
                     end
            end) ++
       m0_1
       :: snd
            (nth_split n
               match n with
               | 0 => match l with
                      | [] => []
                      | B :: tl => if eq_dec_form (m0_1 ∨ m0_2) B then tl else B :: tl
                      end
               | S _ => match l with
                        | [] => []
                        | B :: tl => B :: remove_nth n (m0_1 ∨ m0_2) tl
                        end
               end), m).
      exists (fst
        (nth_split n
           match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form (m0_1 ∨ m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n (m0_1 ∨ m0_2) tl
                    end
           end) ++
      m0_2
      :: snd
           (nth_split n
              match n with
              | 0 => match l with
                     | [] => []
                     | B :: tl => if eq_dec_form (m0_1 ∨ m0_2) B then tl else B :: tl
                     end
              | S _ => match l with
                       | [] => []
                       | B :: tl => B :: remove_nth n (m0_1 ∨ m0_2) tl
                       end
              end), m).  exists m0_1. exists m0_2. exists (fst (nth_split n (remove_nth (S n) (m0_1 ∨ m0_2) l))).
           exists (snd (nth_split n (remove_nth (S n) (m0_1 ∨ m0_2) l))). exists m. repeat split ; auto. apply in_eq. }
    { pose (IHl0 H1). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. repeat split ; try auto. apply in_cons. assumption. }
Qed.

Lemma OrL_help1 : forall prems s, InT prems (prems_Or_L (pos_top_ors (fst s)) s) ->
                                         OrLRule prems s.
Proof.
intros. pose (@OrL_help01 _ _ _ H). repeat destruct s0. destruct s. simpl in H.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)). simpl (snd (l, m)). simpl (snd (l, m)) in H.
simpl (fst (l, m)) in H. apply In_pos_top_ors_split_l in i.
destruct i. destruct s. repeat destruct p.
subst. rewrite <- e. rewrite <- e0. apply OrLRule_I.
Qed.

Lemma OrL_help002 : forall Γ0 Γ1 l C A B,
           InT [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)] (prems_Or_L ((A ∨ B, S (length Γ0)) :: l) (Γ0 ++ A ∨ B :: Γ1, C)).
Proof.
intros. unfold prems_Or_L.
simpl (fst (Γ0 ++ A ∨ B :: Γ1, C)). simpl (snd (Γ0 ++ A ∨ B :: Γ1, C)).
repeat rewrite effective_remove_nth. pose (nth_split_idL Γ0 Γ1).
rewrite <- e. pose (nth_split_idR Γ0 Γ1). rewrite <- e0. apply InT_eq.
Qed.

Lemma OrL_help02 : forall Γ0 Γ1 C A B l n,
            OrLRule [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ A ∨ B :: Γ1, C) ->
            (length Γ0 = n) ->
            (In ((A ∨ B), S n) l) ->
            InT [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)] (prems_Or_L l (Γ0 ++ A ∨ B :: Γ1, C)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  1-3: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; try simpl ; destruct n0 ; assumption ; assumption.
  2-3: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; try simpl ; destruct n0 ; assumption ; assumption.
  apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. pose (OrL_help002 Γ0 Γ1 l C A B) ; auto.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
      pose (IHl (length Γ0) H J1 H3). simpl. destruct n0. assumption. apply InT_cons. auto.
Qed.

Lemma OrL_help2 : forall prems s, OrLRule prems s -> InT prems (prems_Or_L (pos_top_ors (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@OrL_help02 Γ0 Γ1 C A B (pos_top_ors (Γ0 ++ (Or A B) :: Γ1)) (length Γ0)). apply i ; try assumption.
reflexivity. apply Good_pos_in_pos_top_ors.
Qed.

Lemma finite_OrL_premises_of_S : forall (s : Seq), existsT2 listOrLprems,
              (forall prems, ((OrLRule prems s) -> (InT prems listOrLprems)) *
                             ((InT prems listOrLprems) -> (OrLRule prems s))).
Proof.
intros. destruct s.
exists (prems_Or_L (pos_top_ors l) (l,m)).
intros. split ; intro.
- inversion H. subst. pose (OrL_help2 H) ; auto.
- apply OrL_help1. simpl. assumption.
Qed.





(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* ImpR rule *)

Fixpoint top_imps (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => (Imp A B) :: top_imps t
                | _ => top_imps t
              end
end.

Fixpoint pos_top_imps (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => (Imp A B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_imps t))
                | _ => (map (fun y => (fst y, S  (snd y))) (pos_top_imps t))
              end
end.

Definition prems_Imp_R (s : Seq) :=
match (snd s) with
  | Imp A B => listInsertsL_Seqs (fst s) A B
  | _ => nil
end.

Lemma ImpR_help1 : forall prem s, InT prem (prems_Imp_R s) -> ImpRRule [prem] s.
Proof.
intros. destruct s. destruct m ; simpl in H. 1-4: inversion H. 2: inversion H.
subst. unfold prems_Imp_R in H. simpl in H. unfold listInsertsL_Seqs in H.
apply InT_map_iff in H. destruct H. destruct p. subst. unfold listInserts in i.
apply InT_map_iff in i. destruct i. destruct p ; subst.
destruct (list_of_splits l). pose (i0 (fst x0) (snd x0)). simpl in i.
assert (In (fst x0, snd x0) x). destruct x0. simpl. apply InT_In ; auto.
apply i1 in H. rewrite <- H. apply ImpRRule_I.
Qed.

Lemma ImpR_help2 : forall prem s, ImpRRule [prem] s -> InT prem (prems_Imp_R s).
Proof.
intros. inversion H. subst. unfold prems_Imp_R. simpl. unfold listInsertsL_Seqs.
apply InT_map_iff. exists (Γ0 ++ A :: Γ1). split ; auto. unfold listInserts.
apply InT_map_iff. exists (Γ0,Γ1). simpl ; split ; auto.  destruct (list_of_splits (Γ0 ++ Γ1)).
simpl. pose (i Γ0 Γ1). apply In_InT_seqs. apply i0. reflexivity.
Qed.

Lemma finite_ImpR_premises_of_S : forall (s : Seq), existsT2 listImpRprems,
              (forall prems, ((ImpRRule prems s) -> (InT prems listImpRprems)) *
                             ((InT prems listImpRprems) -> (ImpRRule prems s))).
Proof.
intro s. destruct s.
exists (map (fun y => [y]) (prems_Imp_R (l,m))).
intros. split ; intro.
- inversion H. subst. apply InT_map_iff.
  exists (Γ0 ++ A :: Γ1, B). split. reflexivity.
  pose (@ImpR_help2 (Γ0 ++ A :: Γ1, B) (Γ0 ++ Γ1, A → B)). simpl in i. apply i.
  assumption.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply ImpR_help1. simpl. assumption.
Qed.





(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* AtomImpL1 rule. *)

Fixpoint top_atomimps (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | # P => (Imp # P B) :: top_atomimps t
                                   | _ => top_atomimps t
                                   end
                | _ => top_atomimps t
              end
end.

Fixpoint pos_top_atomimps (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | # P => (Imp # P B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_atomimps t))
                                   | _ => (map (fun y => (fst y, S (snd y))) (pos_top_atomimps t))
                                   end
                | _ => (map (fun y => (fst y, S (snd y))) (pos_top_atomimps t))
              end
end.

Fixpoint top_atoms (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                 | # P => # P :: top_atoms t
                 | _ => top_atoms t
                 end
end.

Fixpoint pos_top_atoms (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                 | # P => (# P, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_atoms t))
                 | _ => (map (fun y => (fst y, S (snd y))) (pos_top_atoms t))
                 end
end.

Inductive eqb_ind (P Q : V) (b : bool): Type :=
 | equalb : P = Q -> b = true -> (eqb_ind P Q b)
 | diffb : P <> Q -> b = false -> (eqb_ind P Q b).

Lemma dec_eqb_ind : forall P Q,
  existsT2 b, (eqb_ind P Q b).
Proof.
intros. destruct (eq_dec_propvar P Q).
- exists true. apply equalb ; auto.
- exists false. apply diffb ; auto.
Qed.

Definition eqb_prop (P Q : V) : bool := proj1_sigT2 (dec_eqb_ind P Q).

Lemma eqb_prop_eq : forall P0 P1, ((P0 = P1) -> (eqb_prop P0 P1 = true)) * ((eqb_prop P0 P1 = true) -> (P0 = P1)).
Proof.
unfold eqb_prop.
intros. destruct dec_eqb_ind. inversion e. subst. split. intros. auto. auto. subst.
split ; intro ; auto. simpl in H0. inversion H0.
Qed.

Definition all_pos_top_atoms_atomimps (l : list (MPropF)) : list (list ((MPropF * nat) * (MPropF * nat))) :=
                        map (fun x => (map (fun y => (x,y)) (pos_top_atomimps l))) (pos_top_atoms l).


Definition pair_atom_same_antec (p : ((MPropF * nat) * (MPropF * nat))) : bool :=
match (fst (fst p)) with
  | # P0 => match (fst (snd p)) with
      | Imp A B => match A with
                           | # P1 => eqb_prop P0 P1
                           | _ => false
                           end
      | _ => false
      end
  | _ => false
end.

Definition pos_atomimps_is_left_atoms (l : list (MPropF)) :=
          filter (fun (x : ((MPropF * nat) * (MPropF * nat))) => andb (ltb (snd (fst x)) (snd (snd x))) (pair_atom_same_antec x))
          (concat (all_pos_top_atoms_atomimps l)).

Definition pos_top_atomimps_L1 l := map (fun x => snd x) (pos_atomimps_is_left_atoms l).

Fixpoint prems_AtomImp_L1 (l : list ((MPropF) * nat)) (s : Seq) : list (Seq) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_AtomImp_L1 t s
      | S m => match C with
           | Imp A B => match A with
                               | # P => ((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ B :: (snd (nth_split m (remove_nth (S m) C (fst s)))), snd s)
                                             :: (prems_AtomImp_L1 t s)
                               | _ => prems_AtomImp_L1 t s
                               end
           | _ => prems_AtomImp_L1 t s
           end
      end
end.

Lemma In_pos_top_atoms_0_False : forall l (A : MPropF), In (A, 0) (pos_top_atoms l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1: simpl in H ;  destruct H ; [ inversion H | simpl ; apply in_map_iff in H ; destruct H ; 
    destruct H ; destruct x ; simpl in H ; inversion H].
    1-5: apply in_map_iff in H ; destruct H ; destruct H ; destruct x ; simpl in H ; inversion H.
Qed.

Lemma In_pos_top_atomimps_0_False : forall l (A : MPropF), In (A, 0) (pos_top_atomimps l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-4: apply in_map_iff in H ; destruct H ; destruct H ; destruct x ; simpl in H ; inversion H.
    2: apply in_map_iff in H ; destruct H ; destruct H ; destruct x ; simpl in H ; inversion H.
    destruct a1.
    2-6: apply in_map_iff in H ; destruct H ; destruct H ; destruct x ; simpl in H ; inversion H.
    simpl in H. destruct H. inversion H. apply in_map_iff in H. destruct H. destruct x. simpl in H. destruct H.
    inversion H.
Qed.

Lemma In_pos_top_atomimps_L1_0_False : forall l (A : MPropF), In (A, 0) (pos_top_atomimps_L1 l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-4: simpl in H ;  apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; simpl in e ; subst ; unfold pos_atomimps_is_left_atoms in i ;
    apply InT_In in i ; apply filter_In in i ; destruct i ; simpl in H0 ; apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H ; destruct H ; subst ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; inversion H ; subst ; clear H ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; destruct x ; simpl in H ; inversion H.
    2: simpl in H ;  apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; simpl in e ; subst ; unfold pos_atomimps_is_left_atoms in i ;
    apply InT_In in i ; apply filter_In in i ; destruct i ; simpl in H0 ; apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H ; destruct H ; subst ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; inversion H ; subst ; clear H ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; destruct x ; simpl in H ; inversion H.
    destruct a1.
    2-6: simpl in H ;  apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; simpl in e ; subst ; unfold pos_atomimps_is_left_atoms in i ;
    apply InT_In in i ; apply filter_In in i ; destruct i ; simpl in H0 ; apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H ; destruct H ; subst ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; inversion H ; subst ; clear H ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; destruct x ; simpl in H ; inversion H.
    apply In_InT_pair in H ; apply InT_map_iff in H. destruct H. destruct x. destruct p0.
    destruct p1. simpl in p. destruct p. inversion e. subst. unfold pos_atomimps_is_left_atoms in i.
     apply InT_In in i ; apply filter_In in i ; destruct i. simpl in H0. apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H. destruct H. subst. destruct x0.
    apply in_map_iff in H1. destruct H1. destruct H. inversion H. subst. inversion H1.
    inversion H3. apply in_map_iff in H3. destruct H3. destruct H3. inversion H3.
Qed.

Lemma filter_InT : forall [A : Type] (f : A -> bool) (x : A) (l : list A), (InT x (filter f l) -> ((InT x l) * (f x = true))) *
                                                                                                       ( ((InT x l) * (f x = true)) -> InT x (filter f l)).
Proof.
intros A f x. induction l.
- simpl. split ; intro. inversion X. destruct X. auto.
- split. destruct IHl. intros. simpl in X. remember (f a) as c. destruct c. inversion X. subst. split ; auto. apply InT_eq.
  subst. apply p in X0. destruct X0. split ; auto. apply InT_cons ; auto. apply p in X. destruct X.
  split ; auto. apply InT_cons ; auto.
  intros. destruct X. destruct IHl. inversion i. subst. simpl. destruct (f x). apply InT_eq.
  inversion e. subst. simpl. destruct (f a). apply InT_cons. apply i0. split ; auto.
  apply i0 ; split ; auto.
Qed.

Lemma InT_concat: forall [A : Type] (l : list (list A)) (y : A), (InT y (concat l) -> (existsT2 x : list A, (InT x l) * (InT y x))) *
                                                                                            ((existsT2 x : list A, (InT x l) * (InT y x)) -> InT y (concat l) ).
Proof.
intro A. induction l.
- intros. simpl. split ; intro. inversion X. destruct X. destruct p. inversion i.
- intros. simpl. split ; intro. apply InT_app_or in X. destruct X. exists a. split ; auto. apply InT_eq.
  pose (IHl y). destruct p. apply s in i. destruct i. destruct p. exists x. split ; auto. apply InT_cons ; auto.
  destruct X. destruct p. inversion i. subst. apply InT_or_app. auto. subst. apply InT_or_app.
  right. apply IHl. exists x. split ; auto.
Qed.

Lemma In_pos_top_atomimps_split_l :forall l (A : MPropF) n, In (A, S n) (pos_top_atomimps l) ->
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. destruct a1.
    + inversion H. inversion H1 ; subst. exists []. exists l. repeat split ; auto. simpl.
       destruct (eq_dec_form (# v → a2) (# v → a2)) ; auto. exfalso. apply n ; auto.
       subst. apply InT_map_iff in H1. destruct H1. destruct p.
      destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
      apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
      apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
      subst. exists (# v → a2 :: x). exists x0. repeat split.
      rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
      assert (fst (# v → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      # v → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
      assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
      rewrite H1. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idL (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
      rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
      assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
      rewrite H0. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idR (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
    + apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (⊥ → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        ⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∧ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∨ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 → a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (Box a1 → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (Box a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        Box a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (Box a1 → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((Box a1 → a2 :: x ++ A :: x0) = ((Box a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (Box a1 → a2 :: x) x0). simpl (length (Box a1 → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (Box a1 → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((Box a1 → a2 :: x ++ A :: x0) = ((Box a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (Box a1 → a2 :: x) x0). simpl (length (Box a1 → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atomimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma In_pos_top_atomimps_L1_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_atomimps_L1 l) ->
          existsT2 l0 l1 l2 P, (l = l0 ++ # P :: l1 ++ A :: l2) *
                          (length (l0 ++ # P :: l1) = n) *
                          ( l0 ++ # P :: l1 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l2 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. unfold pos_top_atomimps_L1 in H. apply In_InT_pair in H.
  apply InT_map_iff in H. destruct H. destruct p. destruct x. destruct p. destruct p0. simpl in e.
  inversion e. subst. unfold pos_atomimps_is_left_atoms in i. apply filter_InT in i. clear e.
  destruct i. simpl in e. assert (n0 <? S n = true). apply andb_prop in e. destruct e.
  auto. apply Nat.ltb_lt in H. apply InT_concat in i. destruct i. destruct p.
  unfold all_pos_top_atoms_atomimps in i. apply InT_map_iff in i. destruct i.
  destruct x0. destruct p. subst. apply InT_map_iff in i0. destruct i0.
  destruct x. destruct p. inversion e0. subst. destruct a.
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. destruct n. exfalso. inversion H. subst. apply InT_In in i.
     apply In_pos_top_atoms_0_False in i. auto. lia. inversion i.
     - { inversion H1. subst. destruct A.
       1-4: exfalso ; apply andb_prop in e ; destruct e ; unfold pair_atom_same_antec in H2 ; simpl in H2 ; inversion H2.
       2: exfalso ; apply andb_prop in e ; destruct e ; unfold pair_atom_same_antec in H2 ; simpl in H2 ; inversion H2.
       assert (A1 = # v). apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H2. simpl in H2.
       destruct A1. 2-6: exfalso ; inversion H2. apply eqb_prop_eq in H2. subst. auto. subst.
       pose (InT_In i0). exists []. apply In_pos_top_atomimps_split_l in i1. destruct i1.
       repeat destruct s. repeat destruct p ; subst. exists x. exists x0. exists v.
       repeat split ; auto. assert (S (length x) = length (# v :: x)). auto. rewrite H0.
       assert (# v :: x ++ # v → A2 :: x0 = (# v :: x) ++ # v → A2 :: x0). auto.
       rewrite H2. rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
       assert (S (length x) = length (# v :: x)). auto. rewrite H0.
       assert (# v :: x ++ # v → A2 :: x0 = (# v :: x) ++ # v → A2 :: x0). auto.
       rewrite H2. rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
     - subst. apply InT_map_iff in H1. destruct H1. destruct p. destruct x. simpl in e2. inversion e2. subst.
       assert (In (A, S n) (pos_top_atomimps_L1 l)).
       { unfold pos_top_atomimps_L1. apply in_map_iff. exists (m, n1, (A, S n)). simpl ; split ; auto.
         unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
         2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
         exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
         apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, S n).
         split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
         apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
         destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
         destruct A1. 2-6: inversion H1. auto. }
       apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
       exists (# v :: x). exists x0. exists x1. exists x2. repeat split ; auto.
       assert (length (# v :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
       simpl. auto. rewrite <- H0.
       assert (# v :: x ++ # x2 :: x0 ++ A :: x1 = (# v :: x ++ # x2 :: x0) ++ A :: x1).
       simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
       rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
       assert (length (# v :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
       simpl. auto. rewrite <- H0.
       assert (# v :: x ++ # x2 :: x0 ++ A :: x1 = (# v :: x ++ # x2 :: x0) ++ A :: x1).
       simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
       rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L1 l)).
     { unfold pos_top_atomimps_L1. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L1_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (⊥ :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (⊥ :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (⊥ :: x ++ # x2 :: x0 ++ A :: x1 = (⊥ :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (⊥ :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (⊥ :: x ++ # x2 :: x0 ++ A :: x1 = (⊥:: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L1 l)).
     { unfold pos_top_atomimps_L1. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L1_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (a1 ∧ a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (a1 ∧ a2 :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (a1 ∧ a2 :: x ++ # x2 :: x0 ++ A :: x1 = (a1 ∧ a2 :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (a1 ∧ a2 :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (a1 ∧ a2 :: x ++ # x2 :: x0 ++ A :: x1 = (a1 ∧ a2 :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L1 l)).
     { unfold pos_top_atomimps_L1. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L1_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (a1 ∨ a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (a1 ∨ a2 :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (a1 ∨ a2 :: x ++ # x2 :: x0 ++ A :: x1 = (a1 ∨ a2 :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (a1 ∨ a2 :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (a1 ∨ a2 :: x ++ # x2 :: x0 ++ A :: x1 = (a1 ∨ a2 :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. destruct n. exfalso. inversion H. subst. apply InT_In in i. apply In_pos_top_atoms_0_False in i. auto.
     subst. lia.
     assert (InT (A, S (S n)) (map (fun y : MPropF * nat => (fst y, S (snd y))) (pos_top_atomimps l))).
     { destruct a1. 2-6: auto. inversion i0. subst. inversion H1. auto. }
     apply InT_map_iff in H0. destruct H0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, S n) (pos_top_atomimps_L1 l)).
     { unfold pos_top_atomimps_L1. apply in_map_iff. exists (m, n1, (A, S n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, S n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (a1 → a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (a1 → a2 :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (a1 → a2 :: x ++ # x2 :: x0 ++ A :: x1 = (a1 → a2 :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (a1 → a2 :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (a1 → a2 :: x ++ # x2 :: x0 ++ A :: x1 = (a1 → a2 :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L1 l)).
     { unfold pos_top_atomimps_L1. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L1_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (Box a :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (Box a :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (Box a :: x ++ # x2 :: x0 ++ A :: x1 = (Box a :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (Box a :: x ++ # x2 :: x0) = S (length (x ++ # x2 :: x0))).
     simpl. auto. rewrite <- H0.
     assert (Box a :: x ++ # x2 :: x0 ++ A :: x1 = (Box a :: x ++ # x2 :: x0) ++ A :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
Qed.

Lemma Good_pos_in_pos_top_atomimps : forall A P Γ0 Γ1,
              In (Imp # P A, S (length Γ0)) (pos_top_atomimps (Γ0 ++ Imp # P A :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  1-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp # P A, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp # P A, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. destruct a1.
  simpl ; right ; apply InT_In ; apply InT_map_iff ; exists (Imp # P A, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  1-5: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp # P A, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
Qed.

Lemma Good_pos_in_pos_top_atoms : forall P Γ0 Γ1,
              In (# P, S (length Γ0)) (pos_top_atoms (Γ0 ++ # P :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  2-6: simpl ; apply InT_In ; apply InT_map_iff ; exists (# P, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. right. apply in_map_iff. exists (# P, S (length Γ0)). split ; auto.
Qed.

Lemma Good_pos_in_pos_top_atom_atomimps_L1 : forall A P Γ0 Γ1 Γ2,
              In (# P → A, S (length (Γ0 ++ # P :: Γ1))) (pos_top_atomimps_L1 (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2)).
Proof.
induction Γ0.
- intros. simpl. unfold pos_top_atomimps_L1. unfold pos_atomimps_is_left_atoms. apply in_map_iff.
  exists ((# P, 1),(# P → A, S (S (length Γ1)))). split. auto. apply filter_In. split. apply in_concat.
  exists (map (fun y : MPropF * nat => ((# P,1), y)) (pos_top_atomimps (# P :: Γ1 ++ # P → A :: Γ2))).
  split. unfold all_pos_top_atoms_atomimps. apply in_map_iff. exists (# P, 1) ; split ; auto.
  simpl. auto. apply in_map_iff. exists (# P → A, S (S (length Γ1))). split ; auto. simpl.
  apply in_map_iff. exists ((# P → A, S (length Γ1))). split ; simpl ; auto.
  apply Good_pos_in_pos_top_atomimps. simpl. unfold pair_atom_same_antec.
  simpl. apply eqb_prop_eq. auto.
- intros. simpl. pose (IHΓ0 Γ1 Γ2). unfold pos_top_atomimps_L1 in i. unfold pos_atomimps_is_left_atoms in i.
  apply in_map_iff in i. destruct i. destruct x. destruct p. destruct p0. simpl in H. destruct H. inversion H. subst.
  clear H. apply filter_In in H0. destruct H0. simpl in H0. apply in_concat in H. destruct H. destruct H.
  apply andb_prop in H0. destruct H0. apply Nat.ltb_lt in H0. unfold pair_atom_same_antec in H2. simpl in H2.
  destruct m. 2-6: exfalso ; inversion H2. apply eqb_prop_eq in H2. subst. unfold all_pos_top_atoms_atomimps in H.
  apply in_map_iff in H. destruct H. destruct H. subst. apply in_map_iff in H1. destruct H1. destruct x0. destruct x.
  destruct H. inversion H. subst. clear H. unfold pos_top_atomimps_L1.
  apply in_map_iff. exists ((#P, S n),(# P → A, S (S (length (Γ0 ++ # P :: Γ1))))). simpl. split ; auto.
  unfold pos_atomimps_is_left_atoms. apply filter_In. repeat split. 2: simpl ; auto.
  2: apply andb_true_intro. 2: split. 2: apply Nat.ltb_lt. 2: lia. 2: unfold pair_atom_same_antec.
  2: simpl ; apply eqb_prop_eq ; auto. apply in_concat.
  exists (map (fun y : MPropF * nat => ((# P, S n), y)) (pos_top_atomimps (a :: Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2))). split ; auto.
  unfold all_pos_top_atoms_atomimps. apply in_map_iff. exists (# P, S n). split ; auto.
  unfold pos_top_atoms. destruct a. 2-6:apply in_map_iff ; exists (# P, n) ; simpl ; split ; auto.
  apply in_cons. apply in_map_iff ; exists (# P, n) ; simpl ; split ; auto.
  apply in_map_iff. exists (# P → A, S (S (length (Γ0 ++ # P :: Γ1)))). split ; auto.
  simpl. destruct a.
  1-4: apply in_map_iff ; exists ((# P → A, S (length (Γ0 ++ # P :: Γ1)))) ; simpl ; split ; auto.
  2: apply in_map_iff ; exists ((# P → A, S (length (Γ0 ++ # P :: Γ1)))) ; simpl ; split ; auto.
  destruct a1. 2-6: apply in_map_iff ; exists ((# P → A, S (length (Γ0 ++ # P :: Γ1)))) ; simpl ; split ; auto.
  apply in_cons.  apply in_map_iff ; exists ((# P → A, S (length (Γ0 ++ # P :: Γ1)))) ; simpl ; split ; auto.
Qed.

Lemma AtomImpL1_help01 : forall prem s l, InT prem (prems_AtomImp_L1 l s) ->
                  (existsT2 n A P Γ0 Γ1 C,
                        (In (Imp # P A, S n) l) *
                        (prem = (Γ0 ++ A :: Γ1, C)) *
                        (C = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp # P A) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Imp # P A) (fst s)))))).
Proof.
intros prem s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). destruct a. destruct m0.
  1-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct m0_1.
  2-6: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
     exists x2. exists x3. exists x4. repeat split ; try auto. apply in_cons. assumption.
  + unfold prems_AtomImp_L1 in H. simpl (snd (l, m)). simpl (fst (l, m)).
     assert ((prem = ((fst (nth_split n (remove_nth (S n) (# v → m0_2) l)) ++
        m0_2 :: snd (nth_split n (remove_nth (S n) (# v → m0_2) (fst (l, m)))), m))) +
     InT prem ((fix prems_AtomImp_L1 (l : list (MPropF * nat)) (s : list (MPropF) * MPropF) {struct l} :
               list (list (MPropF) * MPropF) :=
             match l with
             | [] => []
             | (C, 0) :: t => prems_AtomImp_L1 t s
             | (C, S m) :: t =>
                 match C with
                 | # _ → B =>
                     (fst (nth_split m (remove_nth (S m) C (fst s))) ++ B :: snd (nth_split m (remove_nth (S m) C (fst s))), snd s)
                     :: prems_AtomImp_L1 t s
                 | _ => prems_AtomImp_L1 t s
                 end
             end) l0 (l, m))).
      inversion H ; auto. destruct H0.
    * subst. clear H. clear IHl0. exists n. exists m0_2. exists v. simpl (fst (l, m)).
      exists (fst (nth_split n (remove_nth (S n) (# v → m0_2) l))).
      exists (snd (nth_split n (remove_nth (S n) (# v → m0_2) l))). exists m. repeat split ; auto. apply in_eq.
    * apply IHl0 in i. destruct i. repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. repeat split ; try auto. apply in_cons. assumption.
Qed.

Lemma pos_top_atoms_insert : forall n Γ0 Γ1 m, InT (m, n) (pos_top_atoms (Γ0 ++ Γ1)) ->
                                                    n < S (length Γ0) ->
                                                    existsT2 Γ2 Γ3 : list (MPropF), Γ2 ++ m :: Γ3 = Γ0.
Proof.
induction n.
- intros. apply InT_In in H. apply In_pos_top_atoms_0_False in H. inversion H.
- intros. destruct Γ0.
  + simpl in H0. exfalso. lia.
  + simpl in H0. assert (n < S (length Γ0)). lia.
     destruct m0.
     * simpl in H. inversion H. subst. inversion H3. subst. exists []. exists Γ0. auto.
        subst. apply InT_map_iff in H3. destruct H3. destruct x. destruct p. simpl in e.
        inversion e. subst. pose (@IHn Γ0 Γ1 m i H1). repeat destruct s. rewrite <- e0.
        exists (# v :: x). exists x0. simpl ; auto.
     * simpl in H. apply InT_map_iff in H. destruct H. destruct x. destruct p. simpl in e.
        inversion e. subst. pose (@IHn Γ0 Γ1 m i H1). repeat destruct s. rewrite <- e0.
        exists (⊥ :: x). exists x0. simpl ; auto.
     * simpl in H. apply InT_map_iff in H. destruct H. destruct x. destruct p. simpl in e.
        inversion e. subst. pose (@IHn Γ0 Γ1 m i H1). repeat destruct s. rewrite <- e0.
        exists (m0_1 ∧ m0_2 :: x). exists x0. simpl ; auto.
     * simpl in H. apply InT_map_iff in H. destruct H. destruct x. destruct p. simpl in e.
        inversion e. subst. pose (@IHn Γ0 Γ1 m i H1). repeat destruct s. rewrite <- e0.
        exists (m0_1 ∨ m0_2 :: x). exists x0. simpl ; auto.
     * simpl in H. apply InT_map_iff in H. destruct H. destruct x. destruct p. simpl in e.
        inversion e. subst. pose (@IHn Γ0 Γ1 m i H1). repeat destruct s. rewrite <- e0.
        exists (m0_1 → m0_2 :: x). exists x0. simpl ; auto.
     * simpl in H. apply InT_map_iff in H. destruct H. destruct x. destruct p. simpl in e.
        inversion e. subst. pose (@IHn Γ0 Γ1 m i H1). repeat destruct s. rewrite <- e0.
        exists (Box m0 :: x). exists x0. simpl ; auto.
Qed.

Lemma exfalso_list_0 : forall l (A : MPropF), (A :: l = l) -> False.
Proof.
induction l.
- intros. inversion H.
- intros. inversion H. apply IHl in H2. auto.
Qed.

Lemma exfalso_list_1 : forall (l1 l0 : list (MPropF)), (l0 <> nil) -> (l0 ++ l1 = l1) -> False.
Proof.
induction l1.
- intros. rewrite app_nil_r in H0. subst. apply H ; auto.
- intros. destruct l0.
  * simpl in H0. apply H ; auto.
  * inversion H0. assert (l0 ++ [a] <> []). intro. destruct l0. simpl in H1. inversion H1. inversion H1.
    assert ((l0 ++ [a]) ++ l1 = l1). rewrite <- app_assoc ; auto.
    pose (IHl1 (l0 ++ [a]) H1 H4). auto.
Qed.

Lemma one_less_remove_split : forall n l0 l1 P B C,
    (fst (nth_split (S n) (remove_nth (S (S n)) (Imp (# P) C) (B :: l0))) ++ C :: (snd (nth_split (S n) (remove_nth (S (S n)) (Imp (# P) C) (B :: l0)))) = B :: l1) ->
    (fst (nth_split n (remove_nth (S n) (# P → C) l0)) ++ C :: snd (nth_split n (remove_nth (S n) (# P → C) l0)) = l1).
Proof.
induction n.
- intros. simpl. simpl in H. inversion H. destruct l0 ; auto.
- intros. simpl in H. inversion H. subst. simpl. auto.
Qed.


Lemma one_less_remove_split1 : forall n P0 P1 C A Γ0 Γ1 m,
    (fst (nth_split (S n) (remove_nth (S (S n)) (# P1 → C) ((m :: Γ0) ++ # P0 → A :: Γ1))) ++
    C :: snd (nth_split (S n) (remove_nth (S (S n)) (# P1 → C) ((m :: Γ0) ++ # P0 → A :: Γ1))) = (m :: Γ0) ++ A :: Γ1) ->
    (fst (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1))) ++
    C :: snd (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1))) = Γ0 ++ A :: Γ1).
Proof.
intros. apply one_less_remove_split with (B:=m). auto.
Qed.


Lemma remove_split_eq : forall P0 P1 A C n Γ0 Γ1,
((fst (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1)))) ++ C :: (snd (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1)))) =
Γ0 ++ A :: Γ1) ->
(A = C) * (P0 = P1) * (Γ0 = fst (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1)))) *
(Γ1 = snd (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1)))) * (length Γ0 = n).
Proof.
induction n.
- intros. simpl. destruct Γ0.
  * simpl. simpl in H. destruct (eq_dec_form (# P1 → C) (# P0 → A)).
    + inversion H ; inversion e ; auto ; repeat split ; auto.
    + inversion H ; subst. exfalso. apply exfalso_list_0 in H2 ; auto.
  * simpl. exfalso. simpl in H. inversion H. subst.
    destruct (eq_dec_form (# P1 → m) m). assert (weight_form (# P1 → m) = weight_form m).
    rewrite e. auto. simpl in H0. lia.
    assert (length (m :: Γ0 ++ # P0 → A :: Γ1) = length (Γ0 ++ A :: Γ1)). rewrite H2. auto.
    simpl in H0. repeat rewrite app_length in H0. simpl in H0. lia.
- intros. destruct Γ0.
  * simpl in H. destruct n. simpl in H. exfalso. inversion H. assert (weight_form (# P0 → A) = weight_form A).
    rewrite H1. auto. simpl in H0. lia. simpl in H. inversion H. subst. exfalso. assert (weight_form (# P0 → A) = weight_form A).
    rewrite H1. auto. simpl in H0. lia.
  * pose (IHn Γ0 Γ1). assert (fst (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1))) ++
    C :: snd (nth_split n (remove_nth (S n) (# P1 → C) (Γ0 ++ # P0 → A :: Γ1))) = Γ0 ++ A :: Γ1).
    apply one_less_remove_split1 in H. auto.
    apply p in H0. repeat destruct H0. repeat destruct p0. clear p. subst. repeat split ; auto.
    1-2 : assert (S (length Γ0) = length (m :: Γ0)) ; auto ; rewrite H0 ; rewrite effective_remove_nth.
    rewrite <- nth_split_idL ; auto. rewrite <- nth_split_idR ; auto.
Qed.


Lemma AtomImpL1_help0111 : forall A P l Γ0 Γ1 C,
      InT (Γ0 ++ A :: Γ1, C) (prems_AtomImp_L1 l (Γ0 ++ # P → A :: Γ1, C)) ->
      InT (# P → A, S (length Γ0)) l.
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. destruct a. destruct m.
  * apply InT_cons. apply IHl with (Γ1:=Γ1) (C:=C).
     unfold prems_AtomImp_L1 in H. destruct n ; auto.
  * apply InT_cons. apply IHl with (Γ1:=Γ1) (C:=C).
     unfold prems_AtomImp_L1 in H. destruct n ; auto.
  * apply InT_cons. apply IHl with (Γ1:=Γ1) (C:=C).
     unfold prems_AtomImp_L1 in H. destruct n ; auto.
  * apply InT_cons. apply IHl with (Γ1:=Γ1) (C:=C).
     unfold prems_AtomImp_L1 in H. destruct n ; auto.
  * simpl in H. destruct n ; auto. apply IHl in H. apply InT_cons ; auto.
    simpl in H. destruct m1 ; simpl in H. 2-6: apply IHl in H ; apply InT_cons ; auto.
    inversion H. 2: subst ; apply IHl in H1 ; apply InT_cons ; auto.
    subst. inversion H1. clear H1. clear H. apply remove_split_eq in H2.
    destruct H2. repeat destruct p. subst. apply InT_eq.
  * apply InT_cons. apply IHl with (Γ1:=Γ1) (C:=C).
     unfold prems_AtomImp_L1 in H. destruct n ; auto.
Qed.

Lemma AtomImpL1_help011 : forall A P Γ0 Γ1 C,
      InT (Γ0 ++ A :: Γ1, C) (prems_AtomImp_L1 (pos_top_atomimps_L1 (Γ0 ++ # P → A :: Γ1)) (Γ0 ++ # P → A :: Γ1, C)) ->
      (existsT2 Γ2 Γ3, Γ2 ++ # P :: Γ3 = Γ0).
Proof.
intros.
assert (InT (# P → A, S (length Γ0)) (pos_top_atomimps_L1 (Γ0 ++ # P → A :: Γ1))).
apply AtomImpL1_help0111 with (Γ1:=Γ1) (C:=C) ; auto.
unfold pos_top_atomimps_L1 in H0. unfold pos_atomimps_is_left_atoms in H0.
unfold all_pos_top_atoms_atomimps in H0. apply InT_map_iff in H0.
destruct H0. destruct x. simpl in p. destruct p. subst. destruct p0. apply filter_InT in i.
destruct i. simpl in e. assert (m = # P). symmetry in e ; apply Bool.andb_true_eq in e.
destruct e. unfold pair_atom_same_antec in H1. simpl in H1. destruct m ; simpl in H1 ; inversion H1.
symmetry in H3. apply eqb_prop_eq in H3. subst. auto. subst.
apply InT_concat in i. destruct i. destruct p.
apply InT_map_iff in i. destruct i. destruct p. subst. apply Bool.andb_true_iff in e.
destruct e. apply Nat.ltb_lt in H0. unfold pair_atom_same_antec in H1.
simpl in H1. apply InT_map_iff in i0. destruct i0. destruct p. inversion e.
subst. clear e. pose (@pos_top_atoms_insert n Γ0 (# P → A :: Γ1) (# P) i H0). assumption.
Qed.

Lemma AtomImpL1_help1 : forall prem s, InT prem (prems_AtomImp_L1 (pos_top_atomimps_L1 (fst s)) s) -> AtomImpL1Rule [prem] s.
Proof.
intros. destruct s. simpl in H. pose (@AtomImpL1_help01 _ _ _ H). repeat destruct s.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)).
simpl (fst (l, m)) in H. simpl (snd (l, m)). simpl (snd (l, m)) in H.
apply In_pos_top_atomimps_L1_split_l in i.
destruct i. repeat destruct s. repeat destruct p. rewrite <- e. simpl (fst (l, m)) in e0. rewrite <- e0.
subst. repeat rewrite <- app_assoc. simpl.
assert (x2 ++ # x5 :: x3 ++ # x1 → x0 :: x4 = (x2 ++ # x5 :: x3) ++ # x1 → x0 :: x4). repeat rewrite <- app_assoc ; auto.
rewrite H0 in H.
repeat rewrite effective_remove_nth in H. rewrite <- nth_split_idL in H. rewrite <- nth_split_idR in H.
apply AtomImpL1_help011 in H. destruct H. destruct s. rewrite <- e1 in H0. rewrite H0.
assert (x2 ++ # x5 :: x3 ++ x0 :: x4 = (x2 ++ # x5 :: x3) ++ x0 :: x4). repeat rewrite <- app_assoc ; auto.
rewrite <- e1 in H. rewrite H. repeat rewrite <- app_assoc. simpl. apply AtomImpL1Rule_I.
Qed.

Lemma AtomImpL1_help002 : forall Γ0 Γ1 Γ2 l C A P,
           InT (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) (prems_AtomImp_L1 ((Imp # P A, S (length (Γ0 ++ # P :: Γ1))) :: l) (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C)).
Proof.
intros. unfold prems_AtomImp_L1.
simpl (fst (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C)). simpl (fst (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C)).
simpl (snd (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C)).
assert (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2 = (Γ0 ++ # P :: Γ1) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; auto.
rewrite H.
repeat rewrite effective_remove_nth. pose (nth_split_idL (Γ0 ++ # P :: Γ1) Γ2).
rewrite <- e. pose (nth_split_idR (Γ0 ++ # P :: Γ1) Γ2). rewrite <- e0. repeat rewrite <- app_assoc. simpl. apply InT_eq.
Qed.

Lemma AtomImpL1_help02 : forall Γ0 Γ1 Γ2 A P C l n,
            AtomImpL1Rule [(Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)] (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C) ->
            (length (Γ0 ++ # P :: Γ1) = n) ->
            (In (# P → A, S n) l) ->
            InT (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) (prems_AtomImp_L1 l (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  1-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length (Γ0 ++ # P :: Γ1) = length (Γ0 ++ # P :: Γ1)) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length (Γ0 ++ # P :: Γ1) = length (Γ0 ++ # P :: Γ1)) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  destruct m1.
  2-6: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length (Γ0 ++ # P :: Γ1) = length (Γ0 ++ # P :: Γ1)) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. apply AtomImpL1_help002.
    + subst. assert (J1: (length (Γ0 ++ # P :: Γ1)) = (length (Γ0 ++ # P :: Γ1))). reflexivity. apply InT_In in H3.
       pose (IHl (length (Γ0 ++ # P :: Γ1)) H J1 H3). simpl. destruct n0 ; auto. apply InT_cons. auto.
Qed.

Lemma AtomImpL1_help2 : forall prem s, AtomImpL1Rule [prem] s -> InT prem (prems_AtomImp_L1 (pos_top_atomimps_L1 (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@AtomImpL1_help02 Γ0 Γ1 Γ2 A P C (pos_top_atomimps_L1 (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2)) (length (Γ0 ++ # P :: Γ1))).
apply i ; try assumption ; auto. apply Good_pos_in_pos_top_atom_atomimps_L1.
Qed.

Lemma finite_AtomImpL1_premises_of_S : forall (s : Seq), existsT2 listAtomImpL1prems,
              (forall prems, ((AtomImpL1Rule prems s) -> (InT prems listAtomImpL1prems)) *
                             ((InT prems listAtomImpL1prems) -> (AtomImpL1Rule prems s))).
Proof.
intros. destruct s.
exists (map (fun y => [y]) (prems_AtomImp_L1 (pos_top_atomimps_L1 l) (l,m))).
intros. split ; intro.
- inversion H. subst.
  pose (AtomImpL1_help2 H). apply InT_map_iff. exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, m) ; split ; auto.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply AtomImpL1_help1. simpl. assumption.
Qed.




(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* AtomImpL2 rule. *)

Definition pos_atomimps_is_right_atoms (l : list (MPropF)) :=
          filter (fun (x : ((MPropF * nat) * (MPropF * nat))) => andb (ltb (snd (snd x)) (snd (fst x))) (pair_atom_same_antec x))
          (concat (all_pos_top_atoms_atomimps l)).

Definition pos_top_atomimps_L2 l := map (fun x => snd x) (pos_atomimps_is_right_atoms l).

Fixpoint prems_AtomImp_L2 (l : list ((MPropF) * nat)) (s : Seq) : list (Seq) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_AtomImp_L2 t s
      | S m => match C with
           | Imp A B => match A with
                               | # P => ((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ B :: (snd (nth_split m (remove_nth (S m) C (fst s)))), snd s)
                                             :: (prems_AtomImp_L2 t s)
                               | _ => prems_AtomImp_L2 t s
                               end
           | _ => prems_AtomImp_L2 t s
           end
      end
end.

Lemma In_pos_top_atomimps_L2_0_False : forall l (A : MPropF), In (A, 0) (pos_top_atomimps_L2 l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-4: simpl in H ;  apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; simpl in e ; subst ; unfold pos_atomimps_is_left_atoms in i ;
    apply InT_In in i ; apply filter_In in i ; destruct i ; simpl in H0 ; apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H ; destruct H ; subst ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; inversion H ; subst ; clear H ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; destruct x ; simpl in H ; inversion H.
    2: simpl in H ;  apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; simpl in e ; subst ; unfold pos_atomimps_is_left_atoms in i ;
    apply InT_In in i ; apply filter_In in i ; destruct i ; simpl in H0 ; apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H ; destruct H ; subst ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; inversion H ; subst ; clear H ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; destruct x ; simpl in H ; inversion H.
    destruct a1.
    2-6: simpl in H ;  apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; simpl in e ; subst ; unfold pos_atomimps_is_left_atoms in i ;
    apply InT_In in i ; apply filter_In in i ; destruct i ; simpl in H0 ; apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H ; destruct H ; subst ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; inversion H ; subst ; clear H ;
    apply in_map_iff in H1 ; destruct H1 ; destruct H ; destruct x ; simpl in H ; inversion H.
    apply In_InT_pair in H ; apply InT_map_iff in H. destruct H. destruct x. destruct p0.
    destruct p1. simpl in p. destruct p. inversion e. subst. unfold pos_atomimps_is_left_atoms in i.
     apply InT_In in i ; apply filter_In in i ; destruct i. simpl in H0. apply in_concat in H ;
    destruct H ; destruct H ; unfold all_pos_top_atoms_atomimps in H ;
    apply in_map_iff in H ; destruct H. destruct H. subst. destruct x0.
    apply in_map_iff in H1. destruct H1. destruct H. inversion H. subst. inversion H1.
    inversion H3. apply in_map_iff in H3. destruct H3. destruct H3. inversion H3.
Qed.

Lemma In_pos_top_atoms_split_l :forall l (A : MPropF) n, In (A, S n) (pos_top_atoms l) ->
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. inversion H.
    + inversion H1 ; subst. exists []. exists l. repeat split ; auto. simpl.
       destruct (eq_dec_form (# v) (# v)) ; auto. exfalso. apply n ; auto.
    + subst. apply InT_map_iff in H1. destruct H1. destruct p.
      destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
      apply InT_In in i. apply In_pos_top_atoms_0_False in i. assumption.
      apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
      subst. exists (# v :: x). exists x0. repeat split.
      rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
      assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
      assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
      rewrite H1. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
      rewrite <- e2. reflexivity.
      rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
      assert (S (S (length x)) = S (length (# v:: x))). simpl. reflexivity.
      rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
      rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atoms_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atoms_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atoms_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atoms_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 → a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_atoms_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma In_pos_top_atomimps_L2_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_atomimps_L2 l) ->
          existsT2 l0 l1 l2 P, (l = l0 ++ A :: l1 ++ # P :: l2) *
                          (length l0 = n) *
                          ( l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 ++ # P :: l2 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. unfold pos_top_atomimps_L2 in H. apply In_InT_pair in H.
  apply InT_map_iff in H. destruct H. destruct p. destruct x. destruct p. destruct p0. simpl in e.
  inversion e. subst. unfold pos_atomimps_is_left_atoms in i. apply filter_InT in i. clear e.
  destruct i. simpl in e. assert (S n <? n0 = true). apply andb_prop in e. destruct e.
  auto. apply Nat.ltb_lt in H. apply InT_concat in i. destruct i. destruct p.
  unfold all_pos_top_atoms_atomimps in i. apply InT_map_iff in i. destruct i.
  destruct x0. destruct p. subst. apply InT_map_iff in i0. destruct i0.
  destruct x. destruct p. inversion e0. subst. destruct a.
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. inversion i.
     - inversion H1. subst. exfalso. lia.
     - subst. apply InT_map_iff in H1. destruct H1. destruct p. destruct x. simpl in e2. inversion e2. subst.
       destruct n. exfalso. apply InT_In in i0. apply In_pos_top_atomimps_0_False in i0. auto.
       assert (In (A, S n) (pos_top_atomimps_L2 l)).
       { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, S n)). simpl ; split ; auto.
         unfold pos_atomimps_is_right_atoms. apply filter_In. split. 2: simpl.
         2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
         exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
         apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, S n).
         split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
         apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
         destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
         destruct A1. 2-6: inversion H1. auto. }
       apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
       exists (# v :: x). exists x0. exists x1. exists x2. repeat split ; auto.
       assert (length (# v :: x) = S (length x)).
       simpl. auto. rewrite <- H0.
       assert (# v :: x ++ A :: x0 ++ # x2 :: x1 = (# v :: x) ++ A :: x0 ++ # x2 :: x1).
       simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
       rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
       assert (length (# v :: x) = S (length x)).
       simpl. auto. rewrite <- H0.
       assert (# v :: x ++ A :: x0 ++ # x2 :: x1 = (# v :: x) ++ A :: x0 ++ # x2 :: x1).
       simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
       rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L2 l)).
     { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (⊥ :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (⊥ :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (⊥ :: x ++ A :: x0 ++ # x2 :: x1 = (⊥ :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (⊥ :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (⊥ :: x ++ A :: x0 ++ # x2 :: x1 = (⊥ :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L2 l)).
     { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (a1 ∧ a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (a1 ∧ a2 :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (a1 ∧ a2 :: x ++ A :: x0 ++ # x2 :: x1 = (a1 ∧ a2 :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (a1 ∧ a2 :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (a1 ∧ a2 :: x ++ A :: x0 ++ # x2 :: x1 = (a1 ∧ a2 :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L2 l)).
     { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (a1 ∨ a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (a1 ∨ a2 :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (a1 ∨ a2 :: x ++ A :: x0 ++ # x2 :: x1 = (a1 ∨ a2 :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (a1 ∨ a2 :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (a1 ∨ a2 :: x ++ A :: x0 ++ # x2 :: x1 = (a1 ∨ a2 :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
  { simpl in i0. destruct a1.
     { inversion i0. inversion H1.
        - subst. exists []. simpl in i. apply InT_map_iff in i. destruct i. destruct x.
          simpl in p. destruct p. inversion e1 ; subst. destruct n. exfalso. apply InT_In in i. apply In_pos_top_atoms_0_False in i.
          auto. apply InT_In in i. apply In_pos_top_atoms_split_l in i. destruct i. repeat destruct s.
          repeat destruct p. subst. exists x. exists x0.
          assert (m = # v). apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H2. simpl in H2.
          destruct m. 2-6: exfalso ; inversion H2. apply eqb_prop_eq in H2. subst. auto. subst.
          exists v. repeat split ; auto. simpl. destruct (eq_dec_form (# v → a2) (# v → a2)).
          auto. exfalso. apply n. auto.
        - subst. simpl in i. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p. destruct p.
           inversion e1 ; subst.  apply InT_map_iff in H1. destruct H1. destruct p. destruct x. simpl in e2.
           inversion e2. subst.
            assert (In (A, n) (pos_top_atomimps_L2 l)).
             { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
               unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
               2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
               exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
               apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
               split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
               apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
               destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
               destruct A1. 2-6: inversion H1. auto. }
             destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
             apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
             exists (# v → a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
             assert (length (# v → a2 :: x) = S (length x)).
             simpl. auto. rewrite <- H0.
             assert (# v → a2 :: x ++ A :: x0 ++ # x2 :: x1 = (# v → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
             simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
             rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
             assert (length (# v → a2 :: x) = S (length x)).
             simpl. auto. rewrite <- H0.
             assert (# v → a2 :: x ++ A :: x0 ++ # x2 :: x1 = (# v → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
             simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
             rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
     { subst. simpl in i. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p. destruct p.
       inversion e1 ; subst. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e2.
       inversion e2. subst.
        assert (In (A, n) (pos_top_atomimps_L2 l)).
         { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
           unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
           2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
           exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
           apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
           split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
           apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
           destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
           destruct A1. 2-6: inversion H1. auto. }
         destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
         apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
         exists (⊥ → a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
         assert (length (⊥ → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert (⊥ → a2 :: x ++ A :: x0 ++ # x2 :: x1 = (⊥ → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
         assert (length (⊥ → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert (⊥ → a2 :: x ++ A :: x0 ++ # x2 :: x1 = (⊥ → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
     { subst. simpl in i. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p. destruct p.
       inversion e1 ; subst. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e2.
       inversion e2. subst.
        assert (In (A, n) (pos_top_atomimps_L2 l)).
         { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
           unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
           2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
           exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
           apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
           split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
           apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
           destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
           destruct A1. 2-6: inversion H1. auto. }
         destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
         apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
         exists ((a1_1 ∧ a1_2) → a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
         assert (length ((a1_1 ∧ a1_2) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
         assert (length ((a1_1 ∧ a1_2) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
     { subst. simpl in i. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p. destruct p.
       inversion e1 ; subst. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e2.
       inversion e2. subst.
        assert (In (A, n) (pos_top_atomimps_L2 l)).
         { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
           unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
           2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
           exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
           apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
           split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
           apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
           destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
           destruct A1. 2-6: inversion H1. auto. }
         destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
         apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
         exists ((a1_1 ∨ a1_2) → a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
         assert (length ((a1_1 ∨ a1_2) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
         assert (length ((a1_1 ∨ a1_2) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
     { subst. simpl in i. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p. destruct p.
       inversion e1 ; subst. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e2.
       inversion e2. subst.
        assert (In (A, n) (pos_top_atomimps_L2 l)).
         { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
           unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
           2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
           exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
           apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
           split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
           apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
           destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
           destruct A1. 2-6: inversion H1. auto. }
         destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
         apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
         exists ((a1_1 → a1_2) → a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
         assert (length ((a1_1 → a1_2) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((a1_1 → a1_2) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((a1_1 → a1_2) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
         assert (length ((a1_1 → a1_2) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((a1_1 → a1_2) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((a1_1 → a1_2) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
     { subst. simpl in i. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p. destruct p.
       inversion e1 ; subst. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e2.
       inversion e2. subst.
        assert (In (A, n) (pos_top_atomimps_L2 l)).
         { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
           unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
           2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
           exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
           apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
           split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
           apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
           destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
           destruct A1. 2-6: inversion H1. auto. }
         destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
         apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
         exists ((Box a1) → a2 :: x). exists x0. exists x1. exists x2. repeat split ; auto.
         assert (length ((Box a1) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((Box a1) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((Box a1) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
         assert (length ((Box a1) → a2 :: x) = S (length x)).
         simpl. auto. rewrite <- H0.
         assert ((Box a1) → a2 :: x ++ A :: x0 ++ # x2 :: x1 = ((Box a1) → a2 :: x) ++ A :: x0 ++ # x2 :: x1).
         simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
         rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. } }
  { simpl in i0. apply InT_map_iff in i0. destruct i0. destruct p. destruct x. simpl in e1.
     inversion e1. subst. simpl in i. apply InT_map_iff in i. destruct i. destruct x. simpl in p.
     destruct p. inversion e2. subst. clear e0. clear e2. clear e1.
     assert (In (A, n) (pos_top_atomimps_L2 l)).
     { unfold pos_top_atomimps_L2. apply in_map_iff. exists (m, n1, (A, n)). simpl ; split ; auto.
       unfold pos_atomimps_is_left_atoms. apply filter_In. split. 2: simpl.
       2: apply andb_true_intro ; split ; auto. 2: apply Nat.ltb_lt ; lia. apply in_concat.
       exists (map (fun y : MPropF * nat => ((m, n1), y)) (pos_top_atomimps l)). split ; auto.
       apply in_map_iff. exists (m, n1). split ; auto. apply InT_In ; auto. apply in_map_iff. exists (A, n).
       split ; auto. apply InT_In ; auto. unfold pair_atom_same_antec. simpl.
       apply andb_prop in e. destruct e. unfold pair_atom_same_antec in H1. simpl in H1.
       destruct m. 2-6: exfalso ; inversion H1. destruct A. 1-4: inversion H1. 2: inversion H1.
       destruct A1. 2-6: inversion H1. auto. }
     destruct n. exfalso. apply In_pos_top_atomimps_L2_0_False in H0. auto.
     apply IHl in H0. destruct H0. repeat destruct s. repeat destruct p. subst.
     exists (Box a :: x). exists x0. exists x1. exists x2. repeat split ; auto.
     assert (length (Box a :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (Box a :: x ++ A :: x0 ++ # x2 :: x1 = (Box a :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idL. auto.
     assert (length (Box a :: x) = S (length x)).
     simpl. auto. rewrite <- H0.
     assert (Box a :: x ++ A :: x0 ++ # x2 :: x1 = (Box a :: x) ++ A :: x0 ++ # x2 :: x1).
     simpl. repeat rewrite <- app_assoc ; auto. rewrite H1.
     rewrite effective_remove_nth. rewrite <- nth_split_idR. auto. }
Qed.

Lemma Good_pos_in_pos_top_atom_atomimps_L2 : forall A P Γ0 Γ1 Γ2,
              In (# P → A, S (length Γ0)) (pos_top_atomimps_L2 (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2)).
Proof.
induction Γ0.
- intros. simpl. unfold pos_top_atomimps_L2. unfold pos_atomimps_is_right_atoms. apply in_map_iff.
  exists ((# P, S (S (length Γ1))),(# P → A, 1)). split. auto. apply filter_In. split. apply in_concat.
  exists (map (fun y : MPropF * nat => ((# P, S (S (length Γ1))), y)) (pos_top_atomimps (# P → A :: Γ1 ++ # P :: Γ2))).
  split. unfold all_pos_top_atoms_atomimps. apply in_map_iff. exists (# P, S (S (length Γ1))) ; split ; auto.
  simpl. auto. apply in_map_iff. exists (# P, S (length Γ1)). split ; auto. apply Good_pos_in_pos_top_atoms.
  apply in_map_iff. exists (# P → A, 1). split ; simpl ; auto. unfold pair_atom_same_antec.
  simpl. apply eqb_prop_eq. auto.
- intros. simpl. pose (IHΓ0 Γ1 Γ2). unfold pos_top_atomimps_L2 in i. unfold pos_atomimps_is_right_atoms in i.
  apply in_map_iff in i. destruct i. destruct x. destruct p. destruct p0. simpl in H. destruct H. inversion H. subst.
  clear H. apply filter_In in H0. destruct H0. simpl in H0. apply in_concat in H. destruct H. destruct H.
  apply andb_prop in H0. destruct H0. apply Nat.ltb_lt in H0. unfold pair_atom_same_antec in H2. simpl in H2.
  destruct m. 2-6: exfalso ; inversion H2. apply eqb_prop_eq in H2. subst. unfold all_pos_top_atoms_atomimps in H.
  apply in_map_iff in H. destruct H. destruct H. subst. apply in_map_iff in H1. destruct H1. destruct x0. destruct x.
  destruct H. inversion H. subst. clear H. unfold pos_top_atomimps_L2.
  apply in_map_iff. exists ((#P, S n),(# P → A, S (S (length Γ0)))). simpl. split ; auto.
  unfold pos_atomimps_is_left_atoms. apply filter_In. repeat split. 2: simpl ; auto.
  2: apply andb_true_intro. 2: split. 2: apply Nat.ltb_lt. 2: lia. 2: unfold pair_atom_same_antec.
  2: simpl ; apply eqb_prop_eq ; auto. apply in_concat.
  exists (map (fun y : MPropF * nat => ((# P, S n), y)) (pos_top_atomimps (a :: Γ0 ++ # P → A:: Γ1 ++ # P :: Γ2))). split ; auto.
  unfold all_pos_top_atoms_atomimps. apply in_map_iff. exists (# P, S n). split ; auto.
  unfold pos_top_atoms. destruct a. 2-6:apply in_map_iff ; exists (# P, n) ; simpl ; split ; auto.
  apply in_cons. apply in_map_iff ; exists (# P, n) ; simpl ; split ; auto.
  apply in_map_iff. exists (# P → A, S (S (length Γ0))). split ; auto.
  simpl. destruct a.
  1-4: apply in_map_iff ; exists ((# P → A, S (length Γ0))) ; simpl ; split ; auto.
  2: apply in_map_iff ; exists ((# P → A, S (length Γ0))) ; simpl ; split ; auto.
  destruct a1. 2-6: apply in_map_iff ; exists ((# P → A, S (length Γ0))) ; simpl ; split ; auto.
  apply in_cons.  apply in_map_iff ; exists ((# P → A, S (length Γ0))) ; simpl ; split ; auto.
Qed.

Lemma AtomImpL2_help01 : forall prem s l, InT prem (prems_AtomImp_L2 l s) ->
                  (existsT2 n A P Γ0 Γ1 C,
                        (In (Imp # P A, S n) l) *
                        (prem = (Γ0 ++ A :: Γ1, C)) *
                        (C = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp # P A) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Imp # P A) (fst s)))))).
Proof.
intros prem s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). destruct a. destruct m0.
  1-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct m0_1.
  2-6: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
     exists x2. exists x3. exists x4. repeat split ; try auto. apply in_cons. assumption.
  + unfold prems_AtomImp_L2 in H. simpl (snd (l, m)). simpl (fst (l, m)).
     assert ((prem = ((fst (nth_split n (remove_nth (S n) (# v → m0_2) l)) ++
        m0_2 :: snd (nth_split n (remove_nth (S n) (# v → m0_2) (fst (l, m)))), m))) +
     InT prem ((fix prems_AtomImp_L2 (l : list (MPropF * nat)) (s : list (MPropF) * MPropF) {struct l} :
               list (list (MPropF) * MPropF) :=
             match l with
             | [] => []
             | (C, 0) :: t => prems_AtomImp_L2 t s
             | (C, S m) :: t =>
                 match C with
                 | # _ → B =>
                     (fst (nth_split m (remove_nth (S m) C (fst s))) ++ B :: snd (nth_split m (remove_nth (S m) C (fst s))), snd s)
                     :: prems_AtomImp_L2 t s
                 | _ => prems_AtomImp_L2 t s
                 end
             end) l0 (l, m))).
      inversion H ; auto. destruct H0.
    * subst. clear H. clear IHl0. exists n. exists m0_2. exists v. simpl (fst (l, m)).
      exists (fst (nth_split n (remove_nth (S n) (# v → m0_2) l))).
      exists (snd (nth_split n (remove_nth (S n) (# v → m0_2) l))). exists m. repeat split ; auto. apply in_eq.
    * apply IHl0 in i. destruct i. repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. repeat split ; try auto. apply in_cons. assumption.
Qed.

Lemma AtomImpL2_help0111 : forall A P l Γ0 Γ1 C,
      InT (Γ0 ++ A :: Γ1, C) (prems_AtomImp_L2 l (Γ0 ++ # P → A :: Γ1, C)) ->
      InT (# P → A, S (length Γ0)) l.
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. destruct a. destruct m.
  1-4: apply InT_cons ; apply IHl with (Γ1:=Γ1) (C:=C) ; unfold prems_AtomImp_L2 in H ; destruct n ; auto.
  2: apply InT_cons ; apply IHl with (Γ1:=Γ1) (C:=C) ; unfold prems_AtomImp_L2 in H ; destruct n ; auto.
  simpl in H. destruct n ; auto. apply IHl in H. apply InT_cons ; auto.
  simpl in H. destruct m1 ; simpl in H. 2-6: apply IHl in H ; apply InT_cons ; auto.
  inversion H. 2: subst ; apply IHl in H1 ; apply InT_cons ; auto.
  subst. inversion H1. clear H1. clear H. apply remove_split_eq in H2.
  destruct H2. repeat destruct p. subst. apply InT_eq.
Qed.

Lemma shift_pos_top_atoms : forall A n Γ0 Γ1, InT (A, n) (pos_top_atoms (Γ0 ++ Γ1)) -> (length Γ0 < n) ->
                                InT (A, (n - length Γ0)) (pos_top_atoms (Γ1)).
Proof.
induction n.
- intros. simpl. exfalso. lia.
- intros. destruct Γ0.
  * simpl. auto.
  * simpl in H0. simpl. simpl in H. destruct m.
    inversion H. inversion H2 ; subst. simpl. exfalso. lia. subst. apply InT_map_iff in H2.
    destruct H2. destruct p. destruct x. simpl in e. inversion e ; subst. apply IHn in i ; auto ; lia.
    1-5: apply InT_map_iff in H ; destruct H ; destruct p ; destruct x ; simpl in e ; inversion e ; subst ; apply IHn in i ; auto ; lia.
Qed.

Lemma AtomImpL2_help011 : forall A P Γ0 Γ1 C,
      InT (Γ0 ++ A :: Γ1, C) (prems_AtomImp_L2 (pos_top_atomimps_L2 (Γ0 ++ # P → A :: Γ1)) (Γ0 ++ # P → A :: Γ1, C)) ->
      (existsT2 Γ2 Γ3, Γ2 ++ # P :: Γ3 = Γ1).
Proof.
intros.
assert (InT (# P → A, S (length Γ0)) (pos_top_atomimps_L2 (Γ0 ++ # P → A :: Γ1))).
apply AtomImpL2_help0111 with (Γ1:=Γ1) (C:=C) ; auto.
unfold pos_top_atomimps_L2 in H0. unfold pos_atomimps_is_right_atoms in H0.
unfold all_pos_top_atoms_atomimps in H0. apply InT_map_iff in H0.
destruct H0. destruct x. simpl in p. destruct p. subst. destruct p0. apply filter_InT in i.
destruct i. simpl in e. assert (m = # P). symmetry in e ; apply Bool.andb_true_eq in e.
destruct e. unfold pair_atom_same_antec in H1. simpl in H1. destruct m ; simpl in H1 ; inversion H1.
symmetry in H3. apply eqb_prop_eq in H3. subst. auto. subst.
apply InT_concat in i. destruct i. destruct p.
apply InT_map_iff in i. destruct i. destruct p. subst. apply Bool.andb_true_iff in e.
destruct e. apply Nat.ltb_lt in H0. unfold pair_atom_same_antec in H1.
simpl in H1. apply InT_map_iff in i0. destruct i0. destruct p. inversion e.
subst. clear e. pose (@shift_pos_top_atoms (# P) n (Γ0 ++ [# P → A]) Γ1).
repeat rewrite <- app_assoc in i1. simpl in i1. pose (i1 i). rewrite app_length in i2. simpl in i2.
assert ((Nat.add (length Γ0) 1) = S (length Γ0)). lia. rewrite H2 in i2.
pose (i2 H0). Search pos_top_atoms.
assert (existsT2 m, S m = n - S (length Γ0)).
destruct (n - S (length Γ0)). exfalso. apply InT_In in i3. apply In_pos_top_atoms_0_False in i3. auto.
exists n0 ; auto. destruct H3. rewrite <- e in i3. apply InT_In in i3.
apply In_pos_top_atoms_split_l in i3. destruct i3. repeat destruct s.
repeat destruct p. subst. exists x0. exists x1. auto.
Qed.

Lemma AtomImpL2_help1 : forall prem s, InT prem (prems_AtomImp_L2 (pos_top_atomimps_L2 (fst s)) s) -> AtomImpL2Rule [prem] s.
Proof.
intros. destruct s. simpl in H. pose (@AtomImpL2_help01 _ _ _ H). repeat destruct s.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)).
simpl (fst (l, m)) in H. simpl (snd (l, m)). simpl (snd (l, m)) in H.
apply In_pos_top_atomimps_L2_split_l in i.
destruct i. repeat destruct s. repeat destruct p. rewrite <- e. simpl (fst (l, m)) in e0. rewrite <- e0.
subst. repeat rewrite <- app_assoc. simpl.
repeat rewrite effective_remove_nth in H. rewrite <- nth_split_idL in H. rewrite <- nth_split_idR in H.
apply AtomImpL2_help011 in H. destruct H. destruct s. rewrite <- e1. apply AtomImpL2Rule_I.
Qed.

Lemma AtomImpL2_help002 : forall Γ0 Γ1 Γ2 l C A P,
           InT (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) (prems_AtomImp_L2 ((Imp # P A, S (length Γ0)) :: l) (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C)).
Proof.
intros. unfold prems_AtomImp_L2.
simpl (fst (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C)). simpl (snd (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C)).
repeat rewrite effective_remove_nth. rewrite <- nth_split_idL. rewrite <- nth_split_idR. apply InT_eq.
Qed.

Lemma AtomImpL2_help02 : forall Γ0 Γ1 Γ2 A P C l n,
            AtomImpL2Rule [(Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)] (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C) ->
            (length Γ0 = n) ->
            (In (# P → A, S n) l) ->
            InT (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) (prems_AtomImp_L2 l (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  1-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  destruct m1.
  2-6: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. apply AtomImpL2_help002.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
       pose (IHl (length Γ0) H J1 H3). simpl. destruct n0 ; auto. apply InT_cons. auto.
Qed.

Lemma AtomImpL2_help2 : forall prem s, AtomImpL2Rule [prem] s -> InT prem (prems_AtomImp_L2 (pos_top_atomimps_L2 (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@AtomImpL2_help02 Γ0 Γ1 Γ2 A P C (pos_top_atomimps_L2 (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2)) (length Γ0)).
apply i ; try assumption ; auto. apply Good_pos_in_pos_top_atom_atomimps_L2.
Qed.

Lemma finite_AtomImpL2_premises_of_S : forall (s : Seq), existsT2 listAtomImpL2prems,
              (forall prems, ((AtomImpL2Rule prems s) -> (InT prems listAtomImpL2prems)) *
                             ((InT prems listAtomImpL2prems) -> (AtomImpL2Rule prems s))).
Proof.
intros. destruct s.
exists (map (fun y => [y]) (prems_AtomImp_L2 (pos_top_atomimps_L2 l) (l,m))).
intros. split ; intro.
- inversion H. subst.
  pose (AtomImpL2_help2 H). apply InT_map_iff. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, m) ; split ; auto.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply AtomImpL2_help1. simpl. assumption.
Qed.



(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* AndImpL rule. *)

Fixpoint top_andimps (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | And C D => (Imp (And C D) B) :: top_andimps t
                                   | _ => top_andimps t
                                   end
                | _ => top_andimps t
              end
end.

Fixpoint pos_top_andimps (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | And C D => (Imp (And C D) B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_andimps t))
                                   | _ => (map (fun y => (fst y, S (snd y))) (pos_top_andimps t))
                                   end
                | _ => (map (fun y => (fst y, S (snd y))) (pos_top_andimps t))
              end
end.

Fixpoint prems_AndImp_L (l : list ((MPropF) * nat)) (s : Seq) : list (Seq) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_AndImp_L t s
      | S m => match C with
           | Imp A B => match A with
                               | And D E => ((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ (Imp D (Imp E B)) :: (snd (nth_split m (remove_nth (S m) C (fst s)))) , snd s)
                                                      :: (prems_AndImp_L t s)
                               | _ => prems_AndImp_L t s
                               end
           | _ => prems_AndImp_L t s
           end
      end
end. 

Lemma In_pos_top_andimps_0_False : forall l (A : MPropF), In (A, 0) (pos_top_andimps l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-4: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    destruct a1.
    1-2: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2-4: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_andimps_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_andimps l) ->
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * destruct a1.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (# v → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (# v → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        # v → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (⊥ → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        ⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. inversion H.
      { inversion H1. subst. exists []. exists l. repeat split. simpl.
        destruct (eq_dec_form ((a1_1 ∧ a1_2) → a2) ((a1_1 ∧ a1_2) → a2)). reflexivity. exfalso. auto. }
      { subst. apply InT_map_iff in H1. destruct H1. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∧ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H1. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity. }
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∨ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 → a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (Box a1 → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (Box a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        Box a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (Box a1 → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((Box a1 → a2 :: x ++ A :: x0) = ((Box a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (Box a1 → a2 :: x) x0). simpl (length (Box a1 → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (Box a1 → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((Box a1 → a2 :: x ++ A :: x0) = ((Box a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (Box a1 → a2 :: x) x0). simpl (length (Box a1 → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_andimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma Good_pos_in_pos_top_andimps : forall A B C Γ0 Γ1,
              In (Imp (And A B) C, S (length Γ0)) (pos_top_andimps (Γ0 ++ Imp (And A B) C :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  1-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (And A B)C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (And A B) C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  destruct a1.
  1-2: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (And A B)C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (And A B)C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. right. apply InT_In. apply InT_map_iff. exists (Imp (And A B) C, S (length Γ0)).
  split. simpl. reflexivity. apply In_InT_pair. apply IHΓ0.
Qed.

Lemma AndImpL_help01 : forall prem s l, InT prem (prems_AndImp_L l s) ->
                  (existsT2 n A B D Γ0 Γ1 C,
                        (In (Imp (And A B) D, S n) l) *
                        (prem = (Γ0 ++ Imp A (Imp B D) :: Γ1, C)) *
                        (C = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp (And A B) D) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Imp (And A B) D) (fst s)))))).
Proof.
intros prem s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). destruct a. destruct m0.
  1-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; repeat split ; try auto ; apply in_cons ; assumption.
  2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct m0_1.
  1-2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; repeat split ; try auto ; apply in_cons ; assumption.
  2-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
     exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
  + inversion H.
    { simpl in H1. simpl in H0. simpl (fst (l, m)) in IHl0. simpl (snd (l, m)) in IHl0.
      exists n. exists m0_1_1. exists m0_1_2. exists m0_2.
      exists (fst (nth_split n match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form ((m0_1_1 ∧ m0_1_2) → m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n ((m0_1_1 ∧ m0_1_2) → m0_2) tl
                    end
           end)).
      exists (snd (nth_split n match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form ((m0_1_1 ∧ m0_1_2) → m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n ((m0_1_1 ∧ m0_1_2) → m0_2) tl
                    end
           end)). exists m. repeat split ; auto. apply in_eq. }
    { pose (IHl0 H1). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption. }
Qed.

Lemma AndImpL_help1 : forall prem s, InT prem (prems_AndImp_L (pos_top_andimps (fst s)) s) -> AndImpLRule [prem] s.
Proof.
intros. pose (@AndImpL_help01 _ _ _ H). repeat destruct s0. destruct s.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)).
simpl (fst (l, m)) in H. simpl (snd (l, m)). simpl (snd (l, m)) in H.
apply In_pos_top_andimps_split_l in i.
destruct i. destruct s. repeat destruct p.
subst. rewrite <- e. rewrite <- e0. apply AndImpLRule_I.
Qed.

Lemma AndImpL_help002 : forall Γ0 Γ1 l C A B D,
           InT (Γ0 ++ A → B → D :: Γ1, C) (prems_AndImp_L (((A ∧ B) → D, S (length Γ0)) :: l) (Γ0 ++ (A ∧ B) → D :: Γ1, C)).
Proof.
intros. unfold prems_AndImp_L.
simpl (fst (Γ0 ++ (A ∧ B) → D :: Γ1, C)). simpl (snd (Γ0 ++ (A ∧ B) → D :: Γ1, C)).
repeat rewrite effective_remove_nth. pose (nth_split_idL Γ0 Γ1).
rewrite <- e. pose (nth_split_idR Γ0 Γ1). rewrite <- e0. apply InT_eq.
Qed.

Lemma AndImpL_help02 : forall Γ0 Γ1 C A B D l n,
            AndImpLRule [(Γ0 ++ A → B → D :: Γ1, C)] (Γ0 ++ (And A B) → D :: Γ1, C) ->
            (length Γ0 = n) ->
            (In ((And A B) → D, S n) l) ->
            InT (Γ0 ++ A → B → D :: Γ1, C) (prems_AndImp_L l (Γ0 ++ (And A B) → D :: Γ1, C)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  1-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  destruct m1.
  1-2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. apply AndImpL_help002.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
       pose (IHl (length Γ0) H J1 H3). simpl. destruct n0 ; auto. apply InT_cons ; auto.
Qed.

Lemma AndImpL_help2 : forall prem s, AndImpLRule [prem] s -> InT prem (prems_AndImp_L (pos_top_andimps (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@AndImpL_help02 Γ0 Γ1 D A B C (pos_top_andimps (Γ0 ++ (And A B) → C :: Γ1)) (length Γ0)). apply i ; try assumption ; auto.
apply Good_pos_in_pos_top_andimps.
Qed.

Lemma finite_AndImpL_premises_of_S : forall (s : Seq), existsT2 listAndImpLprems,
              (forall prems, ((AndImpLRule prems s) -> (InT prems listAndImpLprems)) *
                             ((InT prems listAndImpLprems) -> (AndImpLRule prems s))).
Proof.
intros. destruct s.
exists (map (fun y => [y]) (prems_AndImp_L (pos_top_andimps l) (l,m))).
intros. split ; intro.
- inversion H. subst.
  pose (AndImpL_help2 H). apply InT_map_iff. exists (Γ0 ++ A → B → C :: Γ1, m) ; split ; auto.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply AndImpL_help1. simpl. assumption.
Qed.





(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* OrImpL rule. *)

Fixpoint top_orimps (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | Or C D => (Imp (Or C D) B) :: top_orimps t
                                   | _ => top_orimps t
                                   end
                | _ => top_orimps t
              end
end.

Fixpoint pos_top_orimps (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | Or C D => (Imp (Or C D) B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_orimps t))
                                   | _ => (map (fun y => (fst y, S (snd y))) (pos_top_orimps t))
                                   end
                | _ => (map (fun y => (fst y, S (snd y))) (pos_top_orimps t))
              end
end.

Fixpoint prems_OrImp_L (l : list ((MPropF) * nat)) (s : Seq) : list (Seq) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_OrImp_L t s
      | S m => match C with
           | Imp A B => match A with
                               | Or D E => (map (fun x => (((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ Imp D B :: x) , snd s))
                                                            (listInserts (snd (nth_split m (remove_nth (S m) C (fst s)))) (Imp E B)))
                                                   ++ (prems_OrImp_L t s)
                               | _ => prems_OrImp_L t s
                               end
           | _ => prems_OrImp_L t s
           end
      end
end.

Lemma In_pos_top_orimps_0_False : forall l (A : MPropF), In (A, 0) (pos_top_orimps l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-4: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    destruct a1.
    1-3: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2-3: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_orimps_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_orimps l) ->
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * destruct a1.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (# v → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (# v → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        # v → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (⊥ → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        ⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∧ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. inversion H.
      { inversion H1. subst. exists []. exists l. repeat split. simpl.
        destruct (eq_dec_form ((a1_1 ∨ a1_2) → a2) ((a1_1 ∨ a1_2) → a2)). reflexivity. exfalso. auto. }
      { subst. apply InT_map_iff in H1. destruct H1. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∨ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H1. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity. }
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 → a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (Box a1 → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (Box a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        Box a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (Box a1 → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((Box a1 → a2 :: x ++ A :: x0) = ((Box a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (Box a1 → a2 :: x) x0). simpl (length (Box a1 → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (Box a1 → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((Box a1 → a2 :: x ++ A :: x0) = ((Box a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (Box a1 → a2 :: x) x0). simpl (length (Box a1 → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_orimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma Good_pos_in_pos_top_orimps : forall A B C Γ0 Γ1,
              In (Imp (Or A B) C, S (length Γ0)) (pos_top_orimps (Γ0 ++ Imp (Or A B) C :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  1-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Or A B)C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Or A B) C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  destruct a1.
  1-3: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Or A B)C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2-3: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Or A B)C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. right. apply InT_In. apply InT_map_iff. exists (Imp (Or A B) C, S (length Γ0)).
  split. simpl. reflexivity. apply In_InT_pair. apply IHΓ0.
Qed.

Lemma OrImpL_help01 : forall prem s l, InT prem (prems_OrImp_L l s) ->
                  (existsT2 n A B D Γ0 Γ1 Γ2 C,
                        (In (Imp (Or A B) D, S n) l) *
                        (prem = (Γ0 ++ Imp A D :: Γ1 ++ Imp B D :: Γ2, C)) *
                        (C = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp (Or A B) D) (fst s))))) *
                        (Γ1 ++ Γ2 = (snd (nth_split n (remove_nth (S n) (Imp (Or A B) D) (fst s)))))).
Proof.
intros prem s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). destruct a. destruct m0.
  1-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct m0_1.
  1-3: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  2-3: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
     exists x2. exists x3. exists x4. exists x5. exists x6. repeat split ; try auto. apply in_cons. assumption.
  + unfold prems_OrImp_L in H. apply InT_app_or in H. destruct H.
     * apply InT_map_iff in i. destruct i. destruct p. subst. apply InT_listInserts in i. destruct i. destruct s.
       destruct p. subst. exists n. exists m0_1_1. exists m0_1_2. exists m0_2.
       exists (fst (nth_split n
          match n with
          | 0 => match l with
                 | [] => []
                 | B :: tl => if eq_dec_form ((m0_1_1 ∨ m0_1_2) → m0_2) B then tl else B :: tl
                 end
          | S _ => match l with
                   | [] => []
                   | B :: tl => B :: remove_nth n ((m0_1_1 ∨ m0_1_2) → m0_2) tl
                   end
          end)).
         exists x0. exists x1. exists m. repeat split ; auto. apply in_eq.
      * apply IHl0 in i. destruct i. repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
        exists x2. exists x3. exists x4. exists x5. exists x6. repeat split ; try auto. apply in_cons. assumption.
Qed.

Lemma OrImpL_help1 : forall prem s, InT prem (prems_OrImp_L (pos_top_orimps (fst s)) s) -> OrImpLRule [prem] s.
Proof.
intros. pose (@OrImpL_help01 _ _ _ H). repeat destruct s0. destruct s.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)).
simpl (fst (l, m)) in H. simpl (snd (l, m)). simpl (snd (l, m)) in H.
apply In_pos_top_orimps_split_l in i.
destruct i. destruct s. repeat destruct p. rewrite <- e1. rewrite e2. simpl (fst (l, m)) in e. rewrite <- e in e0.
rewrite e0. apply OrImpLRule_I.
Qed.

Lemma OrImpL_help002 : forall Γ0 Γ1 Γ2 l C A B D,
           InT (Γ0 ++ A → D :: Γ1 ++ B → D :: Γ2, C) (prems_OrImp_L (((A ∨ B) → D, S (length Γ0)) :: l) (Γ0 ++ (A ∨ B) → D :: Γ1 ++ Γ2, C)).
Proof.
intros. unfold prems_OrImp_L.
simpl (fst (Γ0 ++ (A ∨ B) → D :: Γ1 ++ Γ2, C)). simpl (snd (Γ0 ++ (A ∨ B) → D :: Γ1 ++ Γ2, C)).
repeat rewrite effective_remove_nth. pose (nth_split_idL Γ0 (Γ1 ++ Γ2)).
rewrite <- e. pose (nth_split_idR Γ0 (Γ1 ++ Γ2)). rewrite <- e0. apply InT_or_app. left.
apply InT_map_iff. exists (Γ1 ++ B → D :: Γ2). split. auto. apply listInserts_InT ; auto.
Qed.

Lemma OrImpL_help02 : forall Γ0 Γ1 Γ2 C A B D l n,
            OrImpLRule [(Γ0 ++ A → D :: Γ1 ++ B → D :: Γ2, C)] (Γ0 ++ (Or A B) → D :: Γ1 ++ Γ2, C) ->
            (length Γ0 = n) ->
            (In ((Or A B) → D, S n) l) ->
            InT (Γ0 ++ A → D :: Γ1 ++ B → D :: Γ2, C) (prems_OrImp_L l (Γ0 ++ (Or A B) → D :: Γ1 ++ Γ2, C)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  1-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  destruct m1.
  1-3: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2-3: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. apply OrImpL_help002.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
       pose (IHl (length Γ0) H J1 H3). simpl. destruct n0 ; auto. apply InT_or_app. auto.
Qed.

Lemma OrImpL_help2 : forall prem s, OrImpLRule [prem] s -> InT prem (prems_OrImp_L (pos_top_orimps (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@OrImpL_help02 Γ0 Γ1 Γ2 D A B C (pos_top_orimps (Γ0 ++ (Or A B) → C :: Γ1 ++ Γ2)) (length Γ0)). apply i ; try assumption ; auto.
apply Good_pos_in_pos_top_orimps.
Qed.

Lemma finite_OrImpL_premises_of_S : forall (s : Seq), existsT2 listOrImpLprems,
              (forall prems, ((OrImpLRule prems s) -> (InT prems listOrImpLprems)) *
                             ((InT prems listOrImpLprems) -> (OrImpLRule prems s))).
Proof.
intros. destruct s.
exists (map (fun y => [y]) (prems_OrImp_L (pos_top_orimps l) (l,m))).
intros. split ; intro.
- inversion H. subst.
  pose (OrImpL_help2 H). apply InT_map_iff. exists (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, m) ; split ; auto.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply OrImpL_help1. simpl. assumption.
Qed.




(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* ImpImpL rule. *)

Fixpoint top_impimps (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | Imp D E => (Imp (Imp D E) B) :: top_impimps t
                                   | _ => top_impimps t
                                   end
                | _ => top_impimps t
              end
end.

Fixpoint pos_top_impimps (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | Imp C D => (Imp (Imp C D) B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_impimps t))
                                   | _ => (map (fun y => (fst y, S (snd y))) (pos_top_impimps t))
                                   end
                | _ => (map (fun y => (fst y, S (snd y))) (pos_top_impimps t))
              end
end.

Fixpoint prems_ImpImp_L (l : list ((MPropF) * nat)) (s : Seq) : list (list (Seq)) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_ImpImp_L t s
      | S m => match C with
           | Imp A B => match A with
                               | Imp D E => [(((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ (Imp E B) :: (snd (nth_split m (remove_nth (S m) C (fst s))))), Imp D E);
                                                     (((fst (nth_split m (remove_nth (S m) C (fst s)))) ++ B :: (snd (nth_split m (remove_nth (S m) C (fst s))))), (snd s))]
                                                 :: (prems_ImpImp_L t s)
                               | _ => prems_ImpImp_L t s
                               end
           | _ => prems_ImpImp_L t s
           end
      end
end.

Lemma In_pos_top_impimps_0_False : forall l (A : MPropF), In (A, 0) (pos_top_impimps l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-4: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    destruct a1.
    1-4: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_impimps_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_impimps l) ->
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * destruct a1.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (# v → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (# v → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        # v → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (⊥ → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        ⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∧ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∨ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. inversion H.
      { inversion H1. subst. exists []. exists l. repeat split. simpl.
        destruct (eq_dec_form ((a1_1 → a1_2) → a2) ((a1_1 → a1_2) → a2)). reflexivity. exfalso. auto. }
      { subst. apply InT_map_iff in H1. destruct H1. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 → a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H1. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity. }
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((Box a1) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((Box a1) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (Box a1) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((Box a1) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((Box a1) → a2 :: x ++ A :: x0) = (((Box a1) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((Box a1) → a2 :: x) x0). simpl (length ((Box a1) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((Box a1) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((Box a1) → a2 :: x ++ A :: x0) = (((Box a1) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((Box a1) → a2 :: x) x0). simpl (length ((Box a1) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_impimps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma Good_pos_in_pos_top_impimps : forall A B C Γ0 Γ1,
              In (Imp (Imp A B) C, S (length Γ0)) (pos_top_impimps (Γ0 ++ Imp (Imp A B) C :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  1-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Imp A B) C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Imp A B) C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  destruct a1.
  1-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Imp A B) C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Imp A B) C, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. right. apply InT_In. apply InT_map_iff. exists (Imp (Imp A B) C, S (length Γ0)).
  split. simpl. reflexivity. apply In_InT_pair. apply IHΓ0.
Qed.

Lemma ImpImpL_help01 : forall prems s l, InT prems (prems_ImpImp_L l s) ->
                  (existsT2 n prem1 prem2 A B C Γ0 Γ1 D,
                        (prems = [prem1; prem2]) *
                        (In ((Imp (Imp A B) C), S n) l) *
                        (prem1 = (Γ0 ++ Imp B C :: Γ1, Imp A B)) *
                        (prem2 = (Γ0 ++ C :: Γ1, D)) *
                        (D = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp (Imp A B) C) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Imp (Imp A B) C) (fst s)))))).
Proof.
intros prems s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). destruct a. destruct m0.
  1-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; exists x7 ; repeat split ; try auto ; apply in_cons ; assumption.
  2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; exists x7 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct m0_1.
  1-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; exists x7 ; repeat split ; try auto ; apply in_cons ; assumption.
  2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; exists x7 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
     exists x2. exists x3. exists x4. exists x5. exists x6. exists x7. repeat split ; try auto. apply in_cons. assumption.
  + inversion H.
    { simpl in H1. simpl in H0. simpl (fst (l, m)) in IHl0. simpl (snd (l, m)) in IHl0.
      exists n. exists (fst
         (nth_split n
            match n with
            | 0 => match l with
                   | [] => []
                   | B :: tl => if eq_dec_form ((m0_1_1 → m0_1_2) → m0_2) B then tl else B :: tl
                   end
            | S _ => match l with
                     | [] => []
                     | B :: tl => B :: remove_nth n ((m0_1_1 → m0_1_2) → m0_2) tl
                     end
            end) ++
       m0_1_2 → m0_2
       :: snd
            (nth_split n
               match n with
               | 0 => match l with
                      | [] => []
                      | B :: tl => if eq_dec_form ((m0_1_1 → m0_1_2) → m0_2) B then tl else B :: tl
                      end
               | S _ => match l with
                        | [] => []
                        | B :: tl => B :: remove_nth n ((m0_1_1 → m0_1_2) → m0_2) tl
                        end
               end), m0_1_1 → m0_1_2).
      exists (fst
        (nth_split n
           match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form ((m0_1_1 → m0_1_2) → m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n ((m0_1_1 → m0_1_2) → m0_2) tl
                    end
           end) ++
      m0_2
      :: snd
           (nth_split n
              match n with
              | 0 => match l with
                     | [] => []
                     | B :: tl => if eq_dec_form ((m0_1_1 → m0_1_2) → m0_2) B then tl else B :: tl
                     end
              | S _ => match l with
                       | [] => []
                       | B :: tl => B :: remove_nth n ((m0_1_1 → m0_1_2) → m0_2) tl
                       end
              end), m).
      exists m0_1_1. exists m0_1_2. exists m0_2.
      exists (fst
         (nth_split n
            match n with
            | 0 => match l with
                   | [] => []
                   | B :: tl => if eq_dec_form ((m0_1_1 → m0_1_2) → m0_2) B then tl else B :: tl
                   end
            | S _ => match l with
                     | [] => []
                     | B :: tl => B :: remove_nth n ((m0_1_1 → m0_1_2) → m0_2) tl
                     end
            end)).
      exists (snd
            (nth_split n
               match n with
               | 0 => match l with
                      | [] => []
                      | B :: tl => if eq_dec_form ((m0_1_1 → m0_1_2) → m0_2) B then tl else B :: tl
                      end
               | S _ => match l with
                        | [] => []
                        | B :: tl => B :: remove_nth n ((m0_1_1 → m0_1_2) → m0_2) tl
                        end
               end)). exists m. repeat split ; auto. apply in_eq. }
    { pose (IHl0 H1). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7. repeat split ; try auto. apply in_cons. assumption. }
Qed.

Lemma ImpImpL_help1 : forall prems s, InT prems (prems_ImpImp_L (pos_top_impimps (fst s)) s) -> ImpImpLRule prems s.
Proof.
intros. pose (@ImpImpL_help01 _ _ _ H). repeat destruct s0. destruct s.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)).
simpl (fst (l, m)) in H. simpl (snd (l, m)). simpl (snd (l, m)) in H.
apply In_pos_top_impimps_split_l in i.
destruct i. destruct s. repeat destruct p.
subst. rewrite <- e. rewrite <- e0. apply ImpImpLRule_I.
Qed.

Lemma ImpImpL_help002 : forall Γ0 Γ1 l D A B C,
           InT [(Γ0 ++ B → C :: Γ1, A → B);(Γ0 ++ C :: Γ1, D)] (prems_ImpImp_L (((A →  B) → C, S (length Γ0)) :: l) (Γ0 ++ (A → B) → C :: Γ1, D)).
Proof.
intros. unfold prems_ImpImp_L.
simpl (fst (Γ0 ++ (A → B) → C :: Γ1, D)). simpl (snd (Γ0 ++ (A → B) → C :: Γ1, D)).
repeat rewrite effective_remove_nth. pose (nth_split_idL Γ0 Γ1).
rewrite <- e. pose (nth_split_idR Γ0 Γ1). rewrite <- e0. apply InT_eq.
Qed.

Lemma ImpImpL_help02 : forall Γ0 Γ1 D A B C l n,
            ImpImpLRule [(Γ0 ++ B → C :: Γ1, A → B);(Γ0 ++ C :: Γ1, D)] (Γ0 ++ (A → B) → C :: Γ1, D) ->
            (length Γ0 = n) ->
            (In ((A → B) → C, S n) l) ->
            InT [(Γ0 ++ B → C :: Γ1, A → B);(Γ0 ++ C :: Γ1, D)] (prems_ImpImp_L l (Γ0 ++ (A → B) → C :: Γ1, D)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  1-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  destruct m1.
  1-4: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  2: subst ; apply In_InT_pair in H1 ; inversion H1 ; subst ; inversion H2 ; subst ; apply InT_In in H2 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ H J1 H2) ; simpl ; destruct n0 ; assumption ; assumption.
  apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. apply ImpImpL_help002.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
       pose (IHl (length Γ0) H J1 H3). simpl. destruct n0 ; auto. apply InT_cons ; auto.
Qed.

Lemma ImpImpL_help2 : forall prems s, ImpImpLRule prems s -> InT prems (prems_ImpImp_L (pos_top_impimps (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@ImpImpL_help02 Γ0 Γ1 D A B C (pos_top_impimps (Γ0 ++ (A → B) → C :: Γ1)) (length Γ0)).
apply i ; try assumption ; auto.
apply Good_pos_in_pos_top_impimps.
Qed.

Lemma finite_ImpImpL_premises_of_S : forall (s : Seq), existsT2 listImpImpLprems,
              (forall prems, ((ImpImpLRule prems s) -> (InT prems listImpImpLprems)) *
                             ((InT prems listImpImpLprems) -> (ImpImpLRule prems s))).
Proof.
intros. destruct s.
exists (prems_ImpImp_L (pos_top_impimps l) (l,m)).
intros. split ; intro.
- inversion H. subst.
  pose (ImpImpL_help2 H). auto.
- apply ImpImpL_help1. simpl. assumption.
Qed.



(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* BoxImpL rule. *)

Fixpoint top_boximps (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | Box C => (Imp (Box C) B) :: top_boximps t
                                   | _ => top_boximps t
                                   end
                | _ => top_boximps t
              end
end.

Fixpoint pos_top_boximps (l : list (MPropF)) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => match A with
                                   | Box C => (Imp (Box C) B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_boximps t))
                                   | _ => (map (fun y => (fst y, S (snd y))) (pos_top_boximps t))
                                   end
                | _ => (map (fun y => (fst y, S (snd y))) (pos_top_boximps t))
              end
end.

Fixpoint prems_BoxImp_L (l : list ((MPropF) * nat)) (s : Seq) : list (list (Seq)) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_BoxImp_L t s
      | S m => match C with
           | Imp A B => match A with
                               | Box D => [((XBoxed_list (top_boxes (fst s))) ++ [Box D], D); (((fst (nth_split m (remove_nth (S m) C (fst s)))) ++
                                                 B :: (snd (nth_split m (remove_nth (S m) C (fst s))))), (snd s))]
                                                 :: (prems_BoxImp_L t s)
                               | _ => prems_BoxImp_L t s
                               end
           | _ => prems_BoxImp_L t s
           end
      end
end.

Lemma In_pos_top_boximps_0_False : forall l (A : MPropF), In (A, 0) (pos_top_boximps l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    1-4: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    2: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    destruct a1.
    1-5: simpl in H ; apply In_InT_pair in H ; apply InT_map_iff in H ; destruct H ;
    destruct p ; destruct x ; inversion e.
    simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_boximps_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_boximps l) ->
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ :: x ++ A :: x0) = ((⊥ :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ :: x) x0). simpl (length (⊥ :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∧ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∧ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∧ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∧ a2 :: x ++ A :: x0) = ((a1 ∧ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∧ a2 :: x) x0). simpl (length (a1 ∧ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (a1 ∨ a2 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 ∨ a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H0. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (a1 ∨ a2 :: x))). simpl. reflexivity.
    rewrite H. assert ((a1 ∨ a2 :: x ++ A :: x0) = ((a1 ∨ a2 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (a1 ∨ a2 :: x) x0). simpl (length (a1 ∨ a2 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * destruct a1.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (# v → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (# v → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        # v → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (# v → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((# v → a2 :: x ++ A :: x0) = ((# v → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (# v → a2 :: x) x0). simpl (length (# v → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists (⊥ → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        ⊥ → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (⊥ → a2 :: x))). simpl. reflexivity.
        rewrite H. assert ((⊥ → a2 :: x ++ A :: x0) = ((⊥ → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (⊥ → a2 :: x) x0). simpl (length (⊥ → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∧ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∧ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∧ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∧ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∧ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∧ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∧ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 ∨ a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 ∨ a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 ∨ a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 ∨ a1_2) → a2 :: x ++ A :: x0) = (((a1_1 ∨ a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 ∨ a1_2) → a2 :: x) x0). simpl (length ((a1_1 ∨ a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((a1_1 → a1_2) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (a1_1 → a1_2) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((a1_1 → a1_2) → a2 :: x))). simpl. reflexivity.
        rewrite H. assert (((a1_1 → a1_2) → a2 :: x ++ A :: x0) = (((a1_1 → a1_2) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR ((a1_1 → a1_2) → a2 :: x) x0). simpl (length ((a1_1 → a1_2) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
    + apply In_InT_pair in H. inversion H.
      { inversion H1. subst. exists []. exists l. repeat split. simpl.
        destruct (eq_dec_form ((Box a1) → a2) ((Box a1) → a2)). reflexivity. exfalso. auto. }
      { subst. apply InT_map_iff in H1. destruct H1. destruct p.
        destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
        subst. exists ((Box a1) → a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst ((Box a1) → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        (Box a1) → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length ((Box a1) → a2 :: x))). simpl. reflexivity.
        rewrite H1. assert (((Box a1) → a2 :: x ++ A :: x0) = (((Box a1) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL ((Box a1) → a2 :: x) x0). simpl (length ((Box a1) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length ((Box a1) → a2 :: x))). simpl. reflexivity.
        rewrite H0. assert (((Box a1) → a2 :: x ++ A :: x0) = (((Box a1) → a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idR ((Box a1) → a2 :: x) x0). simpl (length ((Box a1) → a2 :: x)) in e2.
        rewrite <- e2. reflexivity. }
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_boximps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma Good_pos_in_pos_top_boximps : forall A B Γ0 Γ1,
              In (Imp (Box A) B, S (length Γ0)) (pos_top_boximps (Γ0 ++ Imp (Box A) B :: Γ1)).
Proof.
induction Γ0.
- intros. simpl. auto.
- intros. destruct a.
  1-4: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Box A) B, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  2: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Box A) B, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  destruct a1.
  1-5: simpl ; apply InT_In ; apply InT_map_iff ; exists (Imp (Box A) B, S (length Γ0)) ;
  split ; simpl ; try reflexivity ; apply In_InT_pair ; apply IHΓ0.
  simpl. right. apply InT_In. apply InT_map_iff. exists (Imp (Box A) B, S (length Γ0)).
  split. simpl. reflexivity. apply In_InT_pair. apply IHΓ0.
Qed.

Lemma BoxImpL_help01 : forall prems s l, InT prems (prems_BoxImp_L l s) ->
                  (existsT2 n prem1 prem2 A B Γ0 Γ1 C,
                        (prems = [prem1; prem2]) *
                        (In ((Imp (Box A) B), S n) l) *
                        (prem1 = (XBoxed_list (top_boxes (fst s)) ++ [Box A], A)) *
                        (prem2 = (Γ0 ++ B :: Γ1, C)) *
                        (C = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp (Box A) B) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Imp (Box A) B) (fst s)))))).
Proof.
intros prems s. destruct s. induction l0 ; intros.
- simpl in H. inversion H.
- simpl (fst (l, m)). destruct a. destruct m0.
  1-4: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  2: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct m0_1.
  1-5: simpl in H ; destruct n ; pose (IHl0 H) ; repeat destruct s ; repeat destruct p ; exists x ; exists x0 ; exists x1 ;
  exists x2 ; exists x3 ; exists x4 ; exists x5 ; exists x6 ; repeat split ; try auto ; apply in_cons ; assumption.
  destruct n.
  + pose (IHl0 H). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
     exists x2. exists x3. exists x4. exists x5. exists x6. repeat split ; try auto. apply in_cons. assumption.
  + inversion H.
    { simpl in H1. simpl in H0. simpl (fst (l, m)) in IHl0. simpl (snd (l, m)) in IHl0.
      exists n. exists (XBoxed_list (top_boxes l) ++ [Box m0_1], m0_1).
      exists (fst
        (nth_split n
           match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form (Box m0_1 → m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n (Box m0_1 → m0_2) tl
                    end
           end) ++
      m0_2
      :: snd
           (nth_split n
              match n with
              | 0 => match l with
                     | [] => []
                     | B :: tl => if eq_dec_form (Box m0_1 → m0_2) B then tl else B :: tl
                     end
              | S _ => match l with
                       | [] => []
                       | B :: tl => B :: remove_nth n (Box m0_1 → m0_2) tl
                       end
              end), m).
      exists m0_1. exists m0_2.
      exists (fst
        (nth_split n
           match n with
           | 0 => match l with
                  | [] => []
                  | B :: tl => if eq_dec_form (Box m0_1 → m0_2) B then tl else B :: tl
                  end
           | S _ => match l with
                    | [] => []
                    | B :: tl => B :: remove_nth n (Box m0_1 → m0_2) tl
                    end
           end)).
      exists (snd
           (nth_split n
              match n with
              | 0 => match l with
                     | [] => []
                     | B :: tl => if eq_dec_form (Box m0_1 → m0_2) B then tl else B :: tl
                     end
              | S _ => match l with
                       | [] => []
                       | B :: tl => B :: remove_nth n (Box m0_1 → m0_2) tl
                       end
              end)). exists m. repeat split ; auto. apply in_eq. }
    { pose (IHl0 H1). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. repeat split ; try auto. apply in_cons. assumption. }
Qed.

Lemma BoxImpL_help1 : forall prems s, InT prems (prems_BoxImp_L (pos_top_boximps (fst s)) s) -> BoxImpLRule prems s.
Proof.
intros. pose (@BoxImpL_help01 _ _ _ H). repeat destruct s0. destruct s.
repeat destruct p. subst. simpl in i. simpl (fst (l, m)).
simpl (fst (l, m)) in H. simpl (snd (l, m)). simpl (snd (l, m)) in H.
apply In_pos_top_boximps_split_l in i.
destruct i. destruct s. repeat destruct p.
subst. rewrite <- e. rewrite <- e0. apply BoxImpLRule_I.
repeat rewrite top_boxes_distr_app. simpl. intro. intros.
rewrite <- top_boxes_distr_app in H0. apply in_top_boxes in H0. destruct H0. repeat destruct s.
destruct p. subst. exists x ; auto.
repeat rewrite top_boxes_distr_app. simpl.
rewrite <- top_boxes_distr_app. apply top_boxes_nobox_gen_ext.
Qed.

Lemma BoxImpL_help002 : forall Γ0 Γ1 l C A B,
           InT [(XBoxed_list (top_boxes (Γ0 ++ Γ1)) ++ [Box A], A);(Γ0 ++ B :: Γ1, C)] (prems_BoxImp_L (((Box A) → B, S (length Γ0)) :: l) (Γ0 ++ (Box A) → B :: Γ1, C)).
Proof.
intros. unfold prems_BoxImp_L.
simpl (fst (Γ0 ++ (Box A) → B :: Γ1, C)). simpl (snd (Γ0 ++ (Box A) → B :: Γ1, C)).
repeat rewrite effective_remove_nth. pose (nth_split_idL Γ0 Γ1).
rewrite <- e. pose (nth_split_idR Γ0 Γ1). rewrite <- e0.
repeat rewrite top_boxes_distr_app. simpl.
apply InT_eq.
Qed.

Lemma BoxImpL_help02 : forall Γ0 Γ1 C A B l n,
            BoxImpLRule [(XBoxed_list (top_boxes (Γ0 ++ Γ1)) ++ [Box A], A);(Γ0 ++ B :: Γ1, C)] (Γ0 ++ (Box A) → B :: Γ1, C) ->
            (length Γ0 = n) ->
            (In ((Box A) → B, S n) l) ->
            InT [(XBoxed_list (top_boxes (Γ0 ++ Γ1)) ++ [Box A], A);(Γ0 ++ B :: Γ1, C)] (prems_BoxImp_L l (Γ0 ++ (Box A) → B :: Γ1, C)).
Proof.
induction l ; intros.
- inversion H0.
- destruct a. destruct m.
  1-4: subst ; apply In_InT_pair in H0 ; inversion H0 ; subst ; inversion H1 ; subst ; apply InT_In in H1 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ X J1 H1) ; simpl ; destruct n0 ; assumption ; assumption.
  2: subst ; apply In_InT_pair in H0 ; inversion H0 ; subst ; inversion H1 ; subst ; apply InT_In in H1 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ X J1 H1) ; simpl ; destruct n0 ; assumption ; assumption.
  destruct m1.
  1-5: subst ; apply In_InT_pair in H0 ; inversion H0 ; subst ; inversion H1 ; subst ; apply InT_In in H1 ;
    assert (J1: length Γ0 = length Γ0) ; try reflexivity ; pose (IHl _ X J1 H1) ; simpl ; destruct n0 ; assumption ; assumption.
  apply In_InT_pair in H0. inversion H0.
    + subst. inversion H2. subst. apply BoxImpL_help002.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H2.
       pose (IHl (length Γ0) X J1 H2). simpl. destruct n0 ; auto. apply InT_cons ; auto.
Qed.

Lemma BoxImpL_help2 : forall prems s, BoxImpLRule prems s -> InT prems (prems_BoxImp_L (pos_top_boximps (fst s)) s).
Proof.
intros. inversion X. subst. simpl. assert (BΓ = top_boxes (Γ0 ++ Γ1)). apply nobox_gen_ext_top_boxes_identity ; auto.
rewrite H0 in X. rewrite  H0.
pose (@BoxImpL_help02 Γ0 Γ1 C A B (pos_top_boximps (Γ0 ++ (Box A) → B :: Γ1)) (length Γ0)).
apply i ; try assumption ; auto.
apply Good_pos_in_pos_top_boximps.
Qed.

Lemma finite_BoxImpL_premises_of_S : forall (s : Seq), existsT2 listBoxImpLprems,
              (forall prems, ((BoxImpLRule prems s) -> (InT prems listBoxImpLprems)) *
                             ((InT prems listBoxImpLprems) -> (BoxImpLRule prems s))).
Proof.
intros. destruct s.
exists (prems_BoxImp_L (pos_top_boximps l) (l,m)).
intros. split ; intro.
- inversion X. subst.
  pose (BoxImpL_help2 X). auto.
- apply BoxImpL_help1. simpl. assumption.
Qed.





(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* GLR rule. *)

Definition prems_Box_R (s : Seq) : list (Seq) :=
match snd s with
  | Box A => [((XBoxed_list (top_boxes (fst s))) ++ [Box A], A)]
  | _ => []
end.

Lemma GLR_help1 : forall prem s, InT prem (prems_Box_R s) ->
                                         GLRRule [prem] s.
Proof.
intros. destruct s. unfold prems_Box_R in H. simpl in H. destruct m.
1-6: inversion H. subst. 2: inversion H1. apply GLRRule_I.
2: apply top_boxes_nobox_gen_ext. intro.
intros. apply in_top_boxes in H0. destruct H0. repeat destruct s.
destruct p ; subst. exists x ; auto.
Qed.

Lemma nobox_gen_ext_id_top_boxes : forall Γ BΓ, is_Boxed_list BΓ -> nobox_gen_ext BΓ Γ -> BΓ = top_boxes Γ.
Proof.
induction Γ.
- intros. simpl. inversion X ; auto.
- intros. inversion X.
  * subst. destruct a ; simpl. 1-5: exfalso.
    + assert (In # v (# v :: l)). apply in_eq. pose (H _ H0). destruct e. inversion H1.
    + assert (In (⊥) ((⊥) :: l)). apply in_eq. pose (H _ H0). destruct e. inversion H1.
    + assert (In (a1 ∧ a2) ((a1 ∧ a2) :: l)). apply in_eq. pose (H _ H0). destruct e. inversion H1.
    + assert (In (a1 ∨ a2) ((a1 ∨ a2) :: l)). apply in_eq. pose (H _ H0). destruct e. inversion H1.
    + assert (In (a1 → a2) ((a1 → a2) :: l)). apply in_eq. pose (H _ H0). destruct e. inversion H1.
    + assert (is_Boxed_list l). intro. intros. apply H. apply in_cons ; auto. pose (IHΓ _ H0 X0). rewrite e. auto.
  * subst. destruct a. 1-5: simpl. 1-5: apply IHΓ ; auto. simpl. exfalso. apply H2. exists a. auto.
Qed.

Lemma GLR_help2 : forall prem s, GLRRule [prem] s ->
                      InT prem (prems_Box_R s).
Proof.
intros. inversion X. subst. simpl.
unfold prems_Box_R. simpl. assert (BΓ = top_boxes Γ).
apply nobox_gen_ext_id_top_boxes ; auto. rewrite H. apply InT_eq.
Qed.

Lemma finite_GLR_premises_of_S : forall (s : Seq), existsT2 listGLRprems,
              (forall prems, ((GLRRule prems s) -> (InT prems listGLRprems)) *
                             ((InT prems listGLRprems) -> (GLRRule prems s))).
Proof.
intros. destruct s.
exists (map (fun y => [y]) (prems_Box_R (l,m))).
intros. split ; intro.
- inversion X. subst. pose (GLR_help2 X). apply InT_map_iff. exists (XBoxed_list BΓ ++ [Box A], A) ; split ; auto.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply GLR_help1. simpl. assumption.
Qed.





(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* Initial rules. *)

Lemma finite_Id_premises_of_S : forall (s : Seq), existsT2 listIdprems,
              (forall prems, ((IdRule prems s) -> (InT prems listIdprems)) *
                             ((InT prems listIdprems) -> (IdRule prems s))).
Proof.
intros. destruct (dec_Id_rule s).
- exists [[]]. intros. split ; intro.
  * inversion H. subst. apply InT_eq.
  * inversion H. subst. assumption. inversion H1.
- exists []. intros. split ; intro.
  * inversion H. subst. exfalso. apply f. assumption.
  * inversion H.
Qed.

Lemma finite_BotL_premises_of_S : forall (s : Seq), existsT2 listBotLprems,
              (forall prems, ((BotLRule prems s) -> (InT prems listBotLprems)) *
                             ((InT prems listBotLprems) -> (BotLRule prems s))).
Proof.
intros. destruct (dec_BotL_rule s).
- exists [[]]. intros. split ; intro.
  * inversion H. subst. apply InT_eq.
  * inversion H. subst. assumption. inversion H1.
- exists []. intros. split ; intro.
  * inversion H. subst. exfalso. apply f. assumption.
  * inversion H.
Qed.





(*------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)





(* Now that we have the list of all premises of a sequent via all rules, we can combine
   them all to obtain the list of all potential premises via the PSGL4ip calculus. *)

Lemma finite_premises_of_S : forall (s : Seq), existsT2 listprems,
              (forall prems, ((PSGL4ip_rules prems s) -> (InT prems listprems)) *
                             ((InT prems listprems) -> (PSGL4ip_rules prems s))).
Proof.
intro s.
destruct (dec_PSGL4ip_rules s).
- exists []. intros. split. intro. exfalso. apply f. exists prems. assumption.
  intro. inversion H.
- destruct (dec_init_rules s).
  + exists [[]]. intros. split. intros. inversion X. 1-2: inversion H ; subst ; apply InT_eq.
     1-13: exfalso ; subst ; firstorder. intro. inversion H. subst. destruct s1. apply PSId.
      auto. apply PSBotL. auto. inversion H1.
  +  pose (finite_Id_premises_of_S s). destruct s1.
      pose (finite_BotL_premises_of_S s). destruct s1.
      pose (finite_AndR_premises_of_S s). destruct s1.
      pose (finite_AndL_premises_of_S s). destruct s1.
      pose (finite_OrR1_premises_of_S s). destruct s1.
      pose (finite_OrR2_premises_of_S s). destruct s1.
      pose (finite_OrL_premises_of_S s). destruct s1.
      pose (finite_ImpR_premises_of_S s). destruct s1.
      pose (finite_AtomImpL1_premises_of_S s). destruct s1.
      pose (finite_AtomImpL2_premises_of_S s). destruct s1.
      pose (finite_AndImpL_premises_of_S s). destruct s1.
      pose (finite_OrImpL_premises_of_S s). destruct s1.
      pose (finite_ImpImpL_premises_of_S s). destruct s1.
      pose (finite_BoxImpL_premises_of_S s). destruct s1.
      pose (finite_GLR_premises_of_S s). destruct s1.
      exists (x ++ x0 ++ x1 ++ x2 ++ x3 ++ x4 ++ x5 ++ x6 ++ x7 ++ x8 ++ x9 ++ x10 ++ x11 ++ x12 ++ x13).
      intros. split.
    * intros. inversion X ; subst. apply InT_or_app. left. apply p. auto.
       apply InT_or_app ; right ; apply InT_or_app ; left. apply p0. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; left. apply p1. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; left. apply p2. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; left. apply p3. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; left. apply p4. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; left. apply p5. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; left. apply p6. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; left. apply p7. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; left. apply p8. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; left. apply p9. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; left. apply p10. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; left. apply p11. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; left. apply p12. auto.
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_or_app ; right ;
       apply InT_or_app ; right ; apply InT_or_app ; right. apply p13. auto.
    *  intros. apply InT_app_or in H. destruct H. exfalso. apply p in i. inversion i. subst. auto.
       apply InT_app_or in i. destruct i. exfalso. apply p0 in i. inversion i. subst. auto.
       apply InT_app_or in i. destruct i. apply p1 in i ; apply PSAndR ; auto.
       apply InT_app_or in i. destruct i. apply p2 in i ; apply PSAndL ; auto.
       apply InT_app_or in i. destruct i. apply p3 in i ; apply PSOrR1 ; auto.
       apply InT_app_or in i. destruct i. apply p4 in i ; apply PSOrR2 ; auto.
       apply InT_app_or in i. destruct i. apply p5 in i ; apply PSOrL ; auto.
       apply InT_app_or in i. destruct i. apply p6 in i ; apply PSImpR ; auto.
       apply InT_app_or in i. destruct i. apply p7 in i ; apply PSAtomImpL1 ; auto.
       apply InT_app_or in i. destruct i. apply p8 in i ; apply PSAtomImpL2 ; auto.
       apply InT_app_or in i. destruct i. apply p9 in i ; apply PSAndImpL ; auto.
       apply InT_app_or in i. destruct i. apply p10 in i ; apply PSOrImpL ; auto.
       apply InT_app_or in i. destruct i. apply p11 in i ; apply PSImpImpL ; auto.
       apply InT_app_or in i. destruct i. apply p12 in i ; apply PSBoxImpL ; auto.
       apply p13 in i ; apply PSGLR ; auto.
Qed.

(* The next definitions "flattens" a list of lists of premises to a list of premises.*)

Definition list_of_premises (s : Seq) : list (Seq) :=
         flatten_list (proj1_sigT2 (finite_premises_of_S s)).

Lemma InT_list_of_premises_exists_prems : forall s prem, InT prem (list_of_premises s) ->
            existsT2 prems, (InT prem prems) * (PSGL4ip_rules prems s).
Proof.
intros. unfold list_of_premises in H.
apply InT_flatten_list_InT_elem in H. destruct H. destruct p.
exists x. split. auto.
destruct (finite_premises_of_S s). pose (p x). destruct p0. apply p0. assumption.
Qed.

Lemma exists_prems_InT_list_of_premises : forall s prem,
            (existsT2 prems, (InT prem prems) * (PSGL4ip_rules prems s)) ->
            InT prem (list_of_premises s).
Proof.
intros. destruct X. destruct p. unfold list_of_premises. destruct (finite_premises_of_S s).
pose (p0 x). destruct p1. apply InT_trans_flatten_list with (bs:=x). assumption. simpl. apply i0.
assumption.
Qed.

Lemma find_the_max_mhd : forall concl l
      (Prem_mhd : forall prems : list (Seq), PSGL4ip_rules prems concl ->
                  forall prem : Seq, InT prem prems ->
                  existsT2 Dprem : derrec PSGL4ip_rules (fun _ : Seq => True) prem,
                  is_mhd Dprem)
      (H1 : forall prem : Seq, InT prem l -> InT prem (list_of_premises concl))
      (H2 : forall (prem : Seq) (J : InT prem l), InT prem (proj1_sigT2
            (InT_list_of_premises_exists_prems concl (H1 prem J))))
      (H3 : forall (prem : Seq) (J : InT prem l), PSGL4ip_rules (proj1_sigT2
            (InT_list_of_premises_exists_prems concl (H1 prem J))) concl)
      (NotNil: l <> nil),

existsT2 prem, existsT2 (J0: InT prem l), forall prem' (J1: InT prem' l),
       (derrec_height (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1)))
        (H3 prem' J1)
        prem'
        (H2 prem' J1))))
       <=
       (derrec_height (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J0)))
        (H3 prem J0)
        prem
        (H2 prem J0)))).
Proof.
induction l ; intros.
- exfalso. apply NotNil. reflexivity.
- clear NotNil. destruct l.
  * exists a. assert (InT a [a]). apply InT_eq. exists H. intros. inversion J1. subst.
    destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' H))) (H3 prem' H) prem' (H2 prem' H)).
    destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) (H3 prem' J1) prem' (H2 prem' J1)).
    simpl. auto. inversion H4.
  * assert (H1' : forall prem : Seq, InT prem (s :: l) -> InT prem (list_of_premises concl)).
    { intros. apply H1. apply InT_cons. assumption. }
    assert (Prem_mhd' : forall prems : list (Seq), PSGL4ip_rules prems concl -> forall prem : Seq,
                        InT prem prems -> existsT2 Dprem : derrec PSGL4ip_rules (fun _ : Seq => True)
                        prem, is_mhd Dprem).
    { intros. apply Prem_mhd with (prems:= prems) ; try assumption. }
    assert (H2' : forall (prem : Seq) (J : InT prem (s :: l)), InT prem (proj1_sigT2
                  (InT_list_of_premises_exists_prems concl (H1' prem J)))).
    { intros. assert (InT prem (a :: s :: l)). apply InT_cons. assumption. pose (H2 _ H).
      destruct (InT_list_of_premises_exists_prems concl (H1' prem J)).
      simpl. destruct p. assumption. }
    assert (H3' : forall (prem : Seq) (J : InT prem (s :: l)), PSGL4ip_rules
                (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem J))) concl).
    { intros. destruct (InT_list_of_premises_exists_prems concl (H1' prem J)). simpl. destruct p.
      assumption. }
    assert (s :: l <> []). intro. inversion H.
    pose (IHl Prem_mhd' H1' H2' H3' H). destruct s0. destruct s0.
    (* I have a max in s :: l: so I simply need to compare it with a. *)
    assert (J2: InT a (a :: s :: l)). apply InT_eq.
    assert (J3: InT x (a :: s :: l)). apply InT_cons. assumption.
    (* The next assert decides on le between mhd of a and mhd of x. *)
    pose (dec_le
      (derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 a J2)))
      (H3 a J2) a (H2 a J2))))
      (derrec_height
       (proj1_sigT2
          (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0))) 
             (H3' x x0) x (H2' x x0))))).
    destruct s0.
    + exists x. exists J3. intros. inversion J1. subst.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) 
      (H3 prem' J1) prem' (H2 prem' J1)). simpl.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J2))) 
      (H3 prem' J2) prem' (H2 prem' J2)). simpl in l1. unfold is_mhd in i0.
      pose (i0 x1).
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x J3))) (H3 x J3) x (H2 x J3)).
      simpl.
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0))) 
      (H3' x x0) x (H2' x x0)). simpl in l1.
      unfold is_mhd in i1. pose (i1 x4). lia.
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0)))
      (H3' x x0) x (H2' x x0)). simpl in l0.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x J3))) (H3 x J3) x (H2 x J3)).
      simpl.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1)))). simpl.
      assert (derrec_height
     (proj1_sigT2
        (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' H4)))
           (H3' prem' H4) prem' (H2' prem' H4))) <= derrec_height x1).
      apply (l0 prem' H4). subst.
      unfold is_mhd in i0. pose (i0 x1).
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' H4)))
           (H3' prem' H4) prem' (H2' prem' H4)). simpl in H6. unfold is_mhd in i2. pose (i2 x3). lia.
    + exists a. exists J2. intros. apply le_False_lt in f.
      inversion J1.
      { subst. destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) 
        (H3 prem' J1) prem' (H2 prem' J1)). simpl.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J2))) 
        (H3 prem' J2) prem' (H2 prem' J2)).
        simpl. unfold is_mhd in i0. pose (i0 x1). lia. }
      { subst.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 a J2))) (H3 a J2) a (H2 a J2)).
        simpl.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) 
        (H3 prem' J1) prem' (H2 prem' J1)). simpl.
        destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0))) 
             (H3' x x0) x (H2' x x0)). simpl in l0.
        assert (derrec_height
       (proj1_sigT2
          (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' H4)))
             (H3' prem' H4) prem' (H2' prem' H4))) <= derrec_height x3). apply l0.
       destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' H4)))
             (H3' prem' H4) prem' (H2' prem' H4)). simpl in H0. simpl in f. unfold is_mhd in i2.
       pose (i2 x2). lia. }
Qed.

Lemma term_IH_help : forall concl,
     (existsT2 prems, (PSGL4ip_rules prems concl) * (prems <> [])) ->
     (forall prems, PSGL4ip_rules prems concl -> (forall prem, InT prem prems -> (existsT2 Dprem, @is_mhd prem Dprem)))
      ->
     (existsT2 Maxprems Maxprem DMaxprem, (PSGL4ip_rules Maxprems concl) * (@is_mhd Maxprem DMaxprem) * (InT Maxprem Maxprems) *
        (forall prems prem (Dprem : derrec (PSGL4ip_rules) (fun _ => True) prem), PSGL4ip_rules prems concl -> InT prem prems ->
            derrec_height Dprem <= derrec_height DMaxprem)).
Proof.
intros concl FAH Prem_mhd.
pose (list_of_premises concl).
assert (H1: forall prem, InT prem l -> InT prem (list_of_premises concl)).
intros. auto.
assert (H2: forall prem (J: InT prem l), InT prem (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J)))).
intros. destruct (InT_list_of_premises_exists_prems concl (H1 prem J)). destruct p. auto.
assert (H3: forall prem (J: InT prem l),
PSGL4ip_rules (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J))) concl).
intros. destruct (InT_list_of_premises_exists_prems concl (H1 prem J)). destruct p. auto.
assert (H4: forall prem (J: InT prem l), is_mhd (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J)))
        (H3 prem J)
        prem
        (H2 prem J)))).
intros. intro. destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J)))
(H3 prem J) prem (H2 prem J)). auto.
assert (l <> []). intro. destruct FAH. destruct p. destruct p.
- inversion i. subst. auto.
- inversion b. subst. auto.
- inversion a. subst. pose (@exists_prems_InT_list_of_premises (Γ, A ∧ B) (Γ, A)).
  assert (InT (Γ, A) (list_of_premises (Γ, A ∧ B))). apply i.
  exists [(Γ, A);(Γ, B)]. split. apply InT_eq. apply PSAndR ; assumption.
  assert (InT (Γ, A) l). auto. rewrite H in H5. inversion H5.
- inversion a. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ A ∧ B :: Γ1, C) (Γ0 ++ A :: B :: Γ1, C)).
  assert (InT (Γ0 ++ A :: B :: Γ1, C) (list_of_premises (Γ0 ++ A ∧ B :: Γ1, C))). apply i.
  exists [(Γ0 ++ A :: B :: Γ1, C)]. split. apply InT_eq. apply PSAndL ; assumption.
  assert (InT (Γ0 ++ A :: B :: Γ1, C) l). auto. rewrite H in H5. inversion H5.
- inversion o. subst. pose (@exists_prems_InT_list_of_premises (Γ, A ∨ B) (Γ, A)).
  assert (InT (Γ, A) (list_of_premises (Γ, A ∨ B))). apply i.
  exists [(Γ, A)]. split. apply InT_eq. apply PSOrR1 ; assumption.
  assert (InT (Γ, A) l). auto. rewrite H in H5. inversion H5.
- inversion o. subst. pose (@exists_prems_InT_list_of_premises (Γ, A ∨ B) (Γ, B)).
  assert (InT (Γ, B) (list_of_premises (Γ, A ∨ B))). apply i.
  exists [(Γ, B)]. split. apply InT_eq. apply PSOrR2 ; assumption.
  assert (InT (Γ, B) l). auto. rewrite H in H5. inversion H5.
- inversion o. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ A ∨ B :: Γ1, C) (Γ0 ++ A :: Γ1, C)).
  assert (InT (Γ0 ++ A :: Γ1, C) (list_of_premises (Γ0 ++ A ∨ B :: Γ1, C))). apply i.
  exists [(Γ0 ++ A :: Γ1, C);(Γ0 ++ B :: Γ1, C)]. split. apply InT_eq. apply PSOrL ; assumption.
  assert (InT (Γ0 ++ A :: Γ1, C) l). auto. rewrite H in H5. inversion H5.
- inversion i. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ Γ1, A → B) (Γ0 ++ A :: Γ1, B)).
  assert (InT(Γ0 ++ A :: Γ1, B) (list_of_premises (Γ0 ++ Γ1, A → B))). apply i0.
  exists [(Γ0 ++ A :: Γ1, B)]. split. apply InT_eq. apply PSImpR ; assumption.
  assert (InT (Γ0 ++ A :: Γ1, B) l). auto. rewrite H in H5. inversion H5.
- inversion a. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C) (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)).
  assert (InT (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) (list_of_premises (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C))). apply i.
  exists [(Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)]. split. apply InT_eq. apply PSAtomImpL1 ; assumption.
  assert (InT (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) l). auto. rewrite H in H5. inversion H5.
- inversion a. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C) (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)).
  assert (InT (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) (list_of_premises (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C))). apply i.
  exists [(Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)]. split. apply InT_eq. apply PSAtomImpL2 ; assumption.
  assert (InT (Γ0 ++  A :: Γ1 ++ # P :: Γ2, C) l). auto. rewrite H in H5. inversion H5.
- inversion a. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ (A ∧ B) → C :: Γ1, D) (Γ0 ++ A → B → C :: Γ1, D)).
  assert (InT (Γ0 ++ A → B → C :: Γ1, D) (list_of_premises (Γ0 ++ (A ∧ B) → C :: Γ1, D))). apply i.
  exists [(Γ0 ++ A → B → C :: Γ1, D)]. split. apply InT_eq. apply PSAndImpL ; assumption.
  assert (InT(Γ0 ++ A → B → C :: Γ1, D) l). auto. rewrite H in H5. inversion H5.
- inversion o. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
  assert (InT (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) (list_of_premises (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, D))). apply i.
  exists [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)]. split. apply InT_eq. apply PSOrImpL ; assumption.
  assert (InT (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) l). auto. rewrite H in H5. inversion H5.
- inversion i. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ (A → B) → C :: Γ1, D) (Γ0 ++ B → C :: Γ1, A → B)).
  assert (InT (Γ0 ++ B → C :: Γ1, A → B) (list_of_premises (Γ0 ++ (A → B) → C :: Γ1, D))). apply i0.
  exists [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)]. split. apply InT_eq. apply PSImpImpL ; assumption.
  assert (InT (Γ0 ++ B → C :: Γ1, A → B) l). auto. rewrite H in H5. inversion H5.
- inversion b. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ Box A → B :: Γ1, C) (XBoxed_list BΓ ++ [Box A], A)).
  assert (InT (XBoxed_list BΓ ++ [Box A], A) (list_of_premises (Γ0 ++ Box A → B :: Γ1, C))). apply i.
  exists [(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)]. split. apply InT_eq. apply PSBoxImpL ; assumption.
  assert (InT (XBoxed_list BΓ ++ [Box A], A) l). auto. rewrite H in H6. inversion H6.
- inversion g. subst. pose (@exists_prems_InT_list_of_premises (Γ, Box A) (XBoxed_list BΓ ++ [Box A], A)).
  assert (InT (XBoxed_list BΓ ++ [Box A], A) (list_of_premises (Γ, Box A))). apply i.
  exists [(XBoxed_list BΓ ++ [Box A], A)]. split. apply InT_eq. apply PSGLR ; assumption.
  assert (InT (XBoxed_list BΓ ++ [Box A], A) l). auto. rewrite H in H6. inversion H6.
- pose (find_the_max_mhd Prem_mhd H1 H2 H3 H).
  destruct s. destruct s. exists (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x x0))).
  exists x. exists (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x x0)))
  (H3 x x0) x (H2 x x0))). repeat split ; try apply H3 ; try apply H4 ; try apply H2.
  intros prems prem Dprem RA IsPrem.
  assert (J3: InT prem l).
  pose (@exists_prems_InT_list_of_premises concl prem). apply i. exists prems. auto.
  assert (E1: derrec_height Dprem <= derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2
  (InT_list_of_premises_exists_prems concl (H1 prem J3))) (H3 prem J3) prem (H2 prem J3)))).
  destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J3)))
  (H3 prem J3) prem (H2 prem J3)). auto.
  assert (E2: derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl
  (H1 prem J3))) (H3 prem J3) prem (H2 prem J3))) <=
  derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x x0)))
  (H3 x x0) x (H2 x x0)))). apply l0. lia.
Qed.

Lemma in_drs_concl_in_allT W rules prems ps (cn : W) (drs : dersrec rules prems ps)
  (dtn : derrec rules prems cn) : in_dersrec dtn drs -> InT cn ps.
Proof.
intro ind. induction ind. apply InT_eq.
apply InT_cons. assumption.
Qed.

Lemma dec_non_nil_prems: forall (concl : (Seq)), ((existsT2 prems, (PSGL4ip_rules prems concl) * (prems <> []))) +
                                       ((existsT2 prems, (PSGL4ip_rules prems concl) * (prems <> [])) -> False).
Proof.
intros. destruct (dec_init_rules concl).
- right. intros. destruct X. destruct p. inversion p ; subst ; auto.
  1-2: inversion H ; auto. 1-13: destruct s ; auto.
- destruct (dec_PSGL4ip_rules concl).
  + right. intros. apply f0. destruct X. exists x. destruct p ; auto.
  + left. destruct s. exists x. inversion p. 1-2: inversion H ; subst ; auto.
     1-11: subst ; inversion H1 ; subst ; split ; auto ; intro ; inversion H2.
     1-2: subst ; inversion X ; subst ; split ; auto ; intro ; inversion H2.
Qed.

(* The next theorem claims that every sequent s has a derivation DMax of maximal height. *)

Theorem PSGL4ip_termin_base : forall s, existsT2 (DMax : derrec (PSGL4ip_rules) (fun _ => True) s), (@is_mhd s DMax).
Proof.
(* Setting up the strong inductions on each. *)
pose (less_than3_strong_inductionT
    (fun x => (existsT2 DMax : derrec PSGL4ip_rules
    (fun _ : Seq => True) x, is_mhd DMax))).
apply s. clear s. intros s IH.

(* Now we can do the pen and paper proof. *)
assert (dersrecnil: dersrec (PSGL4ip_rules) (fun _ => True) nil).
apply dersrec_nil.
pose (dec_PSGL4ip_rules s). destruct s0.
- assert (forall ps : list (Seq), PSGL4ip_rules ps s -> False).
  intros. apply f. exists ps. assumption.
  pose (dpI PSGL4ip_rules (fun _ : Seq => True) s I).
  exists d. unfold is_mhd. intros. simpl. destruct D1. simpl. auto. exfalso. apply f. exists ps. auto.
- assert (forall prems, PSGL4ip_rules prems s -> (forall prem, InT prem prems ->
  (existsT2 Dprem, @is_mhd prem Dprem))).
  { intros. pose (PSGL4ip_less_than3 X H). apply IH. auto. }
    destruct (dec_non_nil_prems s).
    + pose (@term_IH_help s s1 X). repeat destruct s2. destruct p. destruct p. destruct p. inversion p.
      * inversion H. subst. inversion i.
      * inversion H. subst. inversion i.
      * inversion H1. subst. inversion i.
        { subst. pose (dpI PSGL4ip_rules (fun _ : Seq => True)(Γ, B) I).
           pose (dlCons d dersrecnil). pose (dlCons x1 d0).
           pose (@derI _ _ (fun _ : Seq => True) [(Γ, A); (Γ, B)] (Γ, A ∧ B) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H2). lia. } }
        {  subst. inversion H3 ; subst. 2: inversion H4. pose (dpI PSGL4ip_rules (fun _ : Seq => True) (Γ, A) I).
           pose (dlCons x1 dersrecnil). pose (dlCons d d0).
           pose (@derI _ _ (fun _ : Seq => True) [(Γ, A); (Γ, B)] (Γ, A ∧ B) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H2). lia. } }
      * inversion H1. subst. inversion i. 2: inversion H3. subst.
        subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: B :: Γ1, C)] (Γ0 ++ A ∧ B :: Γ1, C) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i. 2: inversion H3. subst.
        subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ, A)] (Γ, A ∨ B) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i. 2: inversion H3. subst.
        subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ, B)] (Γ, A ∨ B) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i.
        { subst. pose (dpI PSGL4ip_rules (fun _ : Seq => True) (Γ0 ++ B :: Γ1, C) I).
           pose (dlCons d dersrecnil). pose (dlCons x1 d0).
           pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ A ∨ B :: Γ1, C) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H2). lia. } }
        { subst. inversion H3 ; subst. 2: inversion H4. pose (dpI PSGL4ip_rules (fun _ : Seq => True) (Γ0 ++ A :: Γ1, C) I). 
           pose (dlCons x1 dersrecnil). pose (dlCons d d0).
           pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ A ∨ B :: Γ1, C) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H2). lia. } }
      * inversion H1. subst. inversion i. 2: inversion H3. subst.
        subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, B)] (Γ0 ++ Γ1, A → B) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i. 2: inversion H3. subst.
        subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)] (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i. 2: inversion H3. subst.
        subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)] (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i. 2: inversion H3. subst.
        subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A → B → C :: Γ1, D)] (Γ0 ++ (A ∧ B) → C :: Γ1, D) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i. 2: inversion H3. subst. subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)] (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, D) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H2). lia. }
      * inversion H1. subst. inversion i.
        { subst. pose (dpI PSGL4ip_rules (fun _ : Seq => True) (Γ0 ++ C :: Γ1, D) I). pose (dlCons d dersrecnil). pose (dlCons x1 d0).
           pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)] (Γ0 ++ (A → B) → C :: Γ1, D) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H2). lia. } }
        { subst. inversion H3 ; subst. 2: inversion H4. pose (dpI PSGL4ip_rules (fun _ : Seq => True) (Γ0 ++ B → C :: Γ1, A → B) I).
           pose (dlCons x1 dersrecnil). pose (dlCons d d0).
           pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)] (Γ0 ++ (A → B) → C :: Γ1, D) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H2). lia. } }
      * inversion X0. subst. inversion i.
        { subst. pose (dpI PSGL4ip_rules (fun _ : Seq => True) (Γ0 ++ B :: Γ1, C) I). pose (dlCons d dersrecnil). pose (dlCons x1 d0).
           pose (@derI _ _ (fun _ : Seq => True) [(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ Box A → B :: Γ1, C) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X2). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H1). lia. } }
        { subst. inversion H2 ; subst. 2: inversion H4. pose (dpI PSGL4ip_rules (fun _ : Seq => True) (XBoxed_list BΓ ++ [Box A], A) I).
           pose (dlCons x1 dersrecnil). pose (dlCons d d0).
           pose (@derI _ _ (fun _ : Seq => True) [(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ Box A → B :: Γ1, C) p d1).
           exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
           destruct D1.
           { simpl. lia. }
           { simpl.
             assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
             in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
             pose (in_drs_concl_in_allT X2). subst. pose (l ps p1 d4 p0 i1). assumption.
             pose (dersrec_height_le H1). lia. } }
      * inversion X0. subst. inversion i. 2: inversion H2. subst. pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(XBoxed_list BΓ ++ [Box A], A)] (Γ, Box A) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec PSGL4ip_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X2). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H1). lia. }
    + destruct s0. inversion p. 3-13: exfalso ; apply f ; exists ps ; split ; inversion H1 ; subst ; auto ; intro ; inversion H2.
       3-4: exfalso ; apply f ; exists ps ; split ; inversion X0 ; subst ; auto ; intro ; inversion H1.
      * inversion H. subst. pose (@derI _ _ (fun _ : Seq => True) [] (Γ0 ++ A :: Γ1, A) p dersrecnil).
        exists d. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl. destruct p0. 3-15: exfalso ; apply f ; exists ps ; split.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0) ; auto.
          - inversion b. subst. rewrite dersrec_height_nil with (ds:=d0) ; auto.
          - apply PSAndR ; auto.
          - intro ; subst ; inversion a.
          - apply PSAndL ; auto.
          - intro ; subst ; inversion a.
          - apply PSOrR1 ; auto.
          - intro ; subst ; inversion o.
          - apply PSOrR2 ; auto.
          - intro ; subst ; inversion o.
          - apply PSOrL ; auto.
          - intro ; subst ; inversion o.
          - apply PSImpR ; auto.
          - intro ; subst ; inversion i.
          - apply PSAtomImpL1 ; auto.
          - intro ; subst ; inversion a.
          - apply PSAtomImpL2 ; auto.
          - intro ; subst ; inversion a.
          - apply PSAndImpL ; auto.
          - intro ; subst ; inversion a.
          - apply PSOrImpL ; auto.
          - intro ; subst ; inversion o.
          - apply PSImpImpL ; auto.
          - intro ; subst ; inversion i.
          - apply PSBoxImpL ; auto.
          - intro ; subst ; inversion b.
          - apply PSGLR ; auto.
          - intro ; subst ; inversion g. }
      * inversion H. subst. pose (@derI _ _ (fun _ : Seq => True) [] (Γ0 ++ ⊥ :: Γ1, A) p dersrecnil).
        exists d. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil) ; auto.
        destruct D1.
        { simpl. lia. }
        { simpl. destruct p0. 3-15: exfalso ; apply f ; exists ps ; split.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0) ; auto.
          - inversion b. subst. rewrite dersrec_height_nil with (ds:=d0) ; auto.
          - apply PSAndR ; auto.
          - intro ; subst ; inversion a.
          - apply PSAndL ; auto.
          - intro ; subst ; inversion a.
          - apply PSOrR1 ; auto.
          - intro ; subst ; inversion o.
          - apply PSOrR2 ; auto.
          - intro ; subst ; inversion o.
          - apply PSOrL ; auto.
          - intro ; subst ; inversion o.
          - apply PSImpR ; auto.
          - intro ; subst ; inversion i.
          - apply PSAtomImpL1 ; auto.
          - intro ; subst ; inversion a.
          - apply PSAtomImpL2 ; auto.
          - intro ; subst ; inversion a.
          - apply PSAndImpL ; auto.
          - intro ; subst ; inversion a.
          - apply PSOrImpL ; auto.
          - intro ; subst ; inversion o.
          - apply PSImpImpL ; auto.
          - intro ; subst ; inversion i.
          - apply PSBoxImpL ; auto.
          - intro ; subst ; inversion b.
          - apply PSGLR ; auto.
          - intro ; subst ; inversion g. }
Qed.

Definition PSGL4ip_drv s := derrec PSGL4ip_rules (fun _ => True) s.

Theorem PSGL4ip_termin : forall s, existsT2 (DMax : PSGL4ip_drv s), (@is_mhd s DMax).
Proof.
intro s. pose (@PSGL4ip_termin_base s). apply s0 ; reflexivity.
Qed.

Theorem PSGL4ip_termin1 : forall (s : Seq), exists (DMax : derrec PSGL4ip_rules (fun _ => True) s), (is_mhd DMax).
Proof.
intro s.
pose (PSGL4ip_termin_base s).
destruct s0. exists x. assumption.
Qed.

Theorem PSGL4ip_termin2 : forall s, exists (DMax : derrec (PSGL4ip_rules) (fun _ => True) s), (is_mhd DMax).
Proof.
intro s. pose (@PSGL4ip_termin_base s). destruct s0. exists x. assumption.
Qed.

Theorem PSGL4ip_termin3 : forall (s : Seq), existsT2 (DMax : derrec PSGL4ip_rules (fun _ => True) s), (is_mhd DMax).
Proof.
intro s. pose (@PSGL4ip_termin_base s). apply s0 ; reflexivity.
Qed.

(* Now we can prove that the maximal height of derivations (mhd) for sequents
   decreases upwards in the applicability of the proofs. In other words, if a sequent s is the
   conclusion of an instance of a rule R of PSGL4ip with premises in ps, then for any element s0 of
   ps we have that (mhd s0) < (mhd s).

   To do so we first define mhd.*)

Definition mhd (s: Seq) : nat := derrec_height (proj1_sigT2 (@PSGL4ip_termin3 s)).

Lemma PSGL4ip_termin_der_is_mhd : forall s, (@is_mhd s (proj1_sigT2 (@PSGL4ip_termin3 s))).
Proof.
intro s. destruct PSGL4ip_termin3. auto.
Qed.

Theorem RA_mhd_decreases : forall prems concl, (PSGL4ip_rules prems concl) ->
                             (forall prem, (In prem prems) -> (mhd prem) < (mhd concl)).
Proof.
assert (dersrecnil: dersrec (PSGL4ip_rules) (fun _ => True) nil).
apply dersrec_nil.

intros. inversion X.
- inversion H0. subst. inversion H.
- inversion H0. subst. inversion H.
- inversion H2. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, A ∧ B))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, A))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, B))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(Γ, A); (Γ, B)] (Γ, A ∧ B) X d3).
    assert (E1: derrec_height d0 = mhd (Γ, A)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ, A ∧ B)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ, B)).
    unfold mhd. auto.
    assert (@is_mhd (Γ, A ∧ B) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H4 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
  * inversion H3. 2: inversion H4. subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, A ∧ B))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, A))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, B))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(Γ, A); (Γ, B)] (Γ, A ∧ B) X d3).
    assert (E1: derrec_height d0 = mhd (Γ, A)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ, A ∧ B)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ, B)).
    unfold mhd. auto.
    assert (@is_mhd (Γ, A ∧ B) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H5 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
- inversion H2. subst. inversion H. 2 : inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A ∧ B :: Γ1, C))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A :: B :: Γ1, C))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: B :: Γ1, C)] (Γ0 ++ A ∧ B :: Γ1, C) X d1).
  assert (E1: derrec_height d = mhd (Γ0 ++ A ∧ B :: Γ1, C)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ0 ++ A :: B :: Γ1, C)).
  unfold mhd. auto.
  assert (@is_mhd (Γ0 ++ A ∧ B :: Γ1, C) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H. 2 : inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, A ∨ B))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, A))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ, A)] (Γ, A ∨ B) X d1).
  assert (E1: derrec_height d = mhd (Γ, A ∨ B)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ, A)).
  unfold mhd. auto.
  assert (@is_mhd (Γ, A ∨ B) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H. 2 : inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, A ∨ B))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, B))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ, B)] (Γ, A ∨ B) X d1).
  assert (E1: derrec_height d = mhd (Γ, A ∨ B)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ, B)).
  unfold mhd. auto.
  assert (@is_mhd (Γ, A ∨ B) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A ∨ B :: Γ1, C))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A :: Γ1, C))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ B :: Γ1, C))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ A ∨ B :: Γ1, C) X d3).
    assert (E1: derrec_height d0 = mhd (Γ0 ++ A :: Γ1, C)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ A ∨ B :: Γ1, C)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ0 ++ B :: Γ1, C)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ A ∨ B :: Γ1, C) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H4 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
  * inversion H3. 2: inversion H4. subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A ∨ B :: Γ1, C))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A :: Γ1, C))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ B :: Γ1, C))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ A ∨ B :: Γ1, C) X d3).
    assert (E1: derrec_height d0 = mhd (Γ0 ++ A :: Γ1, C)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ A ∨ B :: Γ1, C)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ0 ++ B :: Γ1, C)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ A ∨ B :: Γ1, C) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H5 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
- inversion H2. subst. inversion H. 2 : inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ Γ1, A → B))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A :: Γ1, B))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, B)] (Γ0 ++ Γ1, A → B) X d1).
  assert (E1: derrec_height d = mhd (Γ0 ++ Γ1, A → B)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ0 ++ A :: Γ1, B)).
  unfold mhd. auto.
  assert (@is_mhd (Γ0 ++ Γ1, A → B) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H. 2: inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)] (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C) X d1).
  assert (E1: derrec_height d = mhd (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)).
  unfold mhd. auto.
  assert (@is_mhd (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H. 2: inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)] (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C) X d1).
  assert (E1: derrec_height d = mhd (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)).
  unfold mhd. auto.
  assert (@is_mhd (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H. 2: inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ (A ∧ B) → C :: Γ1, D))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A → B → C :: Γ1, D))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A → B → C :: Γ1, D)] (Γ0 ++ (A ∧ B) → C :: Γ1, D) X d1).
  assert (E1: derrec_height d = mhd (Γ0 ++ (A ∧ B) → C :: Γ1, D)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ0 ++ A → B → C :: Γ1, D)).
  unfold mhd. auto.
  assert (@is_mhd (Γ0 ++ (A ∧ B) → C :: Γ1, D) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H. 2: inversion H3.
  subst. apply le_False_lt. intro.
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, D))).
  pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D))).
  pose (dlCons d0 dersrecnil).
  pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)] (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, D) X d1).
  assert (E1: derrec_height d = mhd(Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)).
  unfold mhd. auto.
  assert (E2: derrec_height d0 = mhd (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
  unfold mhd. auto.
  assert (@is_mhd (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, D) d). apply PSGL4ip_termin_der_is_mhd.
  unfold is_mhd in H2. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l ; auto. rewrite Max.max_0_r in l.
  lia.
- inversion H2. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ (A → B) → C :: Γ1, D))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ B → C :: Γ1, A → B))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ C :: Γ1, D))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)] (Γ0 ++ (A → B) → C :: Γ1, D) X d3).
    assert (E1: derrec_height d0 = mhd (Γ0 ++ B → C :: Γ1, A → B)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ (A → B) → C :: Γ1, D)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ0 ++ C :: Γ1, D)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ (A → B) → C :: Γ1, D) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H4 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
  * inversion H3. 2: inversion H4. subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ (A → B) → C :: Γ1, D))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ B → C :: Γ1, A → B))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ C :: Γ1, D))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)] (Γ0 ++ (A → B) → C :: Γ1, D) X d3).
    assert (E1: derrec_height d0 = mhd (Γ0 ++ B → C :: Γ1, A → B)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ (A → B) → C :: Γ1, D)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ0 ++ C :: Γ1, D)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ (A → B) → C :: Γ1, D) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H5 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
- inversion X0. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ Box A → B :: Γ1, C))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (XBoxed_list BΓ ++ [Box A], A))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ B :: Γ1, C))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ Box A → B :: Γ1, C) X d3).
    assert (E1: derrec_height d0 = mhd (XBoxed_list BΓ ++ [Box A], A)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ Box A → B :: Γ1, C)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ0 ++ B :: Γ1, C)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ Box A → B :: Γ1, C) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H3 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
  * inversion H2. 2: inversion H3. subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ Box A → B :: Γ1, C))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (XBoxed_list BΓ ++ [Box A], A))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ0 ++ B :: Γ1, C))).
    pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
    pose (@derI _ _ (fun _ : Seq => True) [(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)] (Γ0 ++ Box A → B :: Γ1, C) X d3).
    assert (E1: derrec_height d0 = mhd (XBoxed_list BΓ ++ [Box A], A)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ Box A → B :: Γ1, C)).
    unfold mhd. auto.
    assert (E3: derrec_height d1 = mhd (Γ0 ++ B :: Γ1, C)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ Box A → B :: Γ1, C) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H5 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
- inversion X0. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGL4ip_termin3 (Γ, Box A))).
    pose (proj1_sigT2 (PSGL4ip_termin3 (XBoxed_list BΓ ++ [Box A], A))).
    pose (dlCons d0 dersrecnil).
    pose (@derI _ _ (fun _ : Seq => True) [(XBoxed_list BΓ ++ [Box A], A)] (Γ, Box A) X d1).
    assert (E1: derrec_height d0 = mhd (XBoxed_list BΓ ++ [Box A], A)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ, Box A)).
    unfold mhd. auto.
    assert (@is_mhd (Γ, Box A) d). apply PSGL4ip_termin_der_is_mhd.
    unfold is_mhd in H3. pose (H3 d2). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
  * inversion H2.
Qed.
