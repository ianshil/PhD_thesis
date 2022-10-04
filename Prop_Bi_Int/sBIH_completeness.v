Require Import Classical.
(* Used only in deciding whether a pair is derivable or not. *)

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
Require Import BiInt_bisimulation.
Require Import BiInt_Lindenbaum_lem.
Require Import wBIH_completeness.

Lemma DN_form_DN : forall n A, (DN_form (S n) A) = (DN_form n (Neg (wNeg A))).
Proof.
induction n.
- intros. simpl. auto.
- intros. simpl. pose (IHn A). rewrite <- e. simpl. auto.
Qed.

Lemma DN_clos_DN_form : forall n Γ A, (In _ Γ A) -> (In _ (DN_clos_set Γ) (DN_form n A)).
Proof.
induction n.
- intros. simpl. apply InitClo. auto.
- intros. simpl. apply IndClo. apply IHn. auto.
Qed.

Section pruning.

(* We define how to prune a model M in a point s. *)

Variable M : model.
Variable s : (@nodes M).

Fixpoint n_reachable (n: nat) (w v : @nodes M) : Prop :=
  match n with
  | 0 => w = v
  | S m => (exists u, (((@reachable M) u v) \/ ((@reachable M) v u)) /\ (n_reachable m w u))
  end.

Lemma n_reachable_DN_clos : forall n w A,
  (wforces M w (DN_form n A)) ->
    (forall v, (n_reachable n w v) -> (wforces M v A)).
Proof.
induction n.
- intros. simpl in H. inversion H0. subst. auto.
- intros. inversion H0. destruct H1. destruct H1.
  * pose (IHn w (Neg (wNeg A))). pose (DN_form_DN n A). rewrite e in H.
    pose (w0 H x H2). simpl in w1. pose (w1 v H1).
    destruct (wforces_dec A M v) ; auto. exfalso.
    pose (w0 H). pose (w1 _ H1).
    assert ((exists v0 : nodes, reachable v0 v /\ (wforces M v0 A -> False))).
    exists x. repeat split ; auto. intros. apply H3.
    apply Persistence with (w:=x) ; auto. destruct H4. destruct H4. apply f0 ; auto. exists x0 ; auto.
  * pose (IHn w (Neg (wNeg A))). pose (DN_form_DN n A). rewrite e in H.
    pose (w0 H x H2). simpl in w1. pose (w1 x).
    destruct (wforces_dec A M v) ; auto. exfalso.
    assert (exists v : nodes, reachable v x /\ (wforces M v A -> False)).
    exists v. repeat split ; auto. destruct H4. destruct H4.
    apply f. apply (@reach_refl M). exists v ; auto.
Qed.

Definition s_is_n_reachable (w : @ nodes M) : Prop :=
  exists n, @n_reachable n s w.

Definition s_pruned_worlds : Type :=
  { x  | s_is_n_reachable x}.

Definition s_pruned_rel (pw0 pw1 : s_pruned_worlds) : Prop :=
  (@reachable M) (proj1_sig pw0) (proj1_sig pw1).

Definition s_pruned_val (pw : s_pruned_worlds) (q : V) : Prop :=
  val (proj1_sig pw) q.

Lemma s_R_refl u :  (s_pruned_rel) u u.
Proof.
intros. unfold s_pruned_rel. destruct u.
simpl. auto. apply (@reach_refl M).
Qed.

Lemma s_R_trans u v w: (s_pruned_rel u v) -> (s_pruned_rel v w) -> (s_pruned_rel u w).
Proof.
intros. unfold s_pruned_rel. destruct w. destruct u. simpl.
unfold s_pruned_rel in H. simpl in H. unfold s_pruned_rel in H0. simpl in H0.
destruct v. simpl in H. simpl in H0. apply ((@reach_tran M) _ _ _ H H0).
Qed.

Lemma s_val_persist : forall u v, s_pruned_rel u v -> forall p, (s_pruned_val u p -> s_pruned_val v p).
Proof.
intros.
unfold s_pruned_val in H0. unfold s_pruned_rel in H.
unfold s_pruned_val. destruct u. destruct v. simpl. simpl in H0.
simpl in H. apply ((@persist M) _ _ H). auto.
Qed.

Instance pruned_M : model :=
      {|
        nodes := s_pruned_worlds ;
        reachable := s_pruned_rel ;
        val := s_pruned_val ;

        reach_refl := s_R_refl ;
        reach_tran := s_R_trans ;

        persist := s_val_persist ;
      |}.

End pruning.

Theorem sCounterCompleteness : forall (Γ Δ : @Ensemble (BPropF V)),
    (spair_derrec (Γ, Δ) -> False) -> ((glob_conseq Γ Δ) -> False).
Proof.
intros Γ Δ SD.
assert (J1: spair_derrec (DN_clos_set Γ, Δ) -> False).
intro. apply SD. unfold spair_derrec in H. unfold spair_derrec.
destruct H. destruct H. destruct H0. simpl in H0.
simpl in H1. exists x. repeat split ; auto. simpl.
pose (sBIH_comp _ H1 Γ). simpl in s. apply s. clear s. intros.
induction H2. apply Ids. apply IdRule_I. assumption.
apply DNs with (ps:=[(Γ, A)]). intros. inversion H3. subst. auto.
inversion H4. apply DNsRule_I.
assert (J2: wpair_derrec (DN_clos_set Γ, Δ) -> False).
intro. apply J1. apply pair_sBIH_extens_wBIH ; auto.
pose (wCounterCompleteness _ _ J2).
intro. apply f. intro. intros. unfold glob_conseq in H.

assert (Bisim: forall (pw : (s_pruned_worlds M w)),
  bisimulation M (@pruned_M M w) (fun (x : @nodes M) (y : (s_pruned_worlds M w)) => x = (proj1_sig y))).
{ intros. unfold bisimulation. intros. subst. repeat split.
  - intro. unfold s_pruned_val. auto.
  - intro. unfold s_pruned_val. auto.
  - intros. exists (proj1_sig v1). split ; auto.
  - intros. assert (J20: s_is_n_reachable M w v0).
    unfold s_is_n_reachable. destruct w1. simpl in H1. unfold s_is_n_reachable in s.
    destruct s. exists (S x0). simpl. exists x. auto.
    pose (@exist (@nodes M) (s_is_n_reachable M w) v0 J20). exists s.
    auto.
  - intros. exists (proj1_sig v1). split ; auto.
  - intros. assert (J20: s_is_n_reachable M w v0).
    unfold s_is_n_reachable. destruct w1. simpl in H1. unfold s_is_n_reachable in s.
    destruct s. exists (S x0). simpl. exists x. auto.
    pose (@exist (@nodes M) (s_is_n_reachable M w) v0 J20). exists s.
    auto. }

(* All formulae in Γ are globally true in the pruned canonical model. *)
assert (SAT: forall (pw : (s_pruned_worlds M w)) A, (In _ Γ A) ->
wforces (pruned_M M w) pw A).
{ intros. pose (bisimulation_imp_bi_int_equiv M (pruned_M M w) _ (Bisim pw)).
  pose (i A (proj1_sig pw) pw). apply i0. auto. clear i0. clear i. destruct pw. simpl.
  unfold s_is_n_reachable in s. destruct s.
  assert (J5: wforces M w (DN_form x0 A)).
  { apply H0. apply DN_clos_DN_form ; auto. }
  pose (n_reachable_DN_clos M x0 w A J5 x). auto. }

assert (J20: s_is_n_reachable M w w). unfold s_is_n_reachable. exists 0.
unfold n_reachable. auto.
pose (@exist (@nodes M) (s_is_n_reachable M w) w J20).
assert (exists B : BPropF V, In (BPropF V) Δ B /\ (wforces (pruned_M M w) s B)).
apply H. intros. intro. apply SAT ; auto. destruct H1. destruct H1. exists x. split ; auto.
assert (w=w). auto.
pose (bisimulation_imp_bi_int_equiv _ _ _ (Bisim s) x w s). 
apply i ; auto.
Qed.

Theorem sCompleteness : forall (Γ Δ : @Ensemble (BPropF V)),
    (glob_conseq Γ Δ) -> spair_derrec (Γ, Δ).
Proof.
intros Γ Δ GC. pose (sCounterCompleteness Γ Δ).
pose (classic (spair_derrec (Γ, Δ))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.