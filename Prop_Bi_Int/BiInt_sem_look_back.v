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
Require Import BiInt_soundness.
Require Import wBIH_completeness.
Require Import sBIH_completeness.
Require Import Classical.

Variable q : V.
Variable p : V.
Hypothesis diff_prop : (p = q) -> False.

Section ConseqSoundness.

Section DefModels.

Inductive UnDeux  : Type :=
 | Un : UnDeux
 | Deux : UnDeux.

Definition UDle (n m : UnDeux) : Prop :=
  match n with
   | Un => True
   | Deux => match m with
                   | Un => False
                   | Deux => True
                  end
  end.

Lemma UDle_refl : forall n, UDle n n.
Proof.
intros. destruct n ; unfold UDle ; auto.
Qed.

Lemma UDle_trans : forall n m k, (UDle n m) -> (UDle m k) -> (UDle n k).
Proof.
intros. destruct n ; unfold UDle ; auto. destruct k ; unfold UDle ; auto.
destruct m ; unfold UDle ; auto.
Qed.

Inductive UnDeuxTrois  : Type :=
 | UnDeux_I : UnDeux -> UnDeuxTrois
 | Trois : UnDeuxTrois.

Definition UDTle (n m : UnDeuxTrois) : Prop :=
  match n with
   | UnDeux_I k => match m with
                            | UnDeux_I l => UDle k l
                            | Trois => False
                           end
   | Trois => match m with
                   | UnDeux_I k => match k with
                                               | Un => False
                                               | Deux => True
                                              end
                   | Trois => True
                  end
  end.

Lemma UDTle_refl : forall n, UDTle n n.
Proof.
intros. destruct n ; unfold UDTle ; auto. apply UDle_refl.
Qed.

Lemma UDTle_trans : forall n m k, (UDTle n m) -> (UDTle m k) -> (UDTle n k).
Proof.
intros. destruct n ; unfold UDTle ; auto. destruct k ; unfold UDTle ; auto.
destruct m ; unfold UDTle ; auto. simpl in H. simpl in H0. apply (UDle_trans _ _ _ H H0) ; auto.
simpl in H0. destruct u0 ; simpl ; auto. inversion H0. simpl in H. inversion H.
destruct m ; auto. destruct k ; simpl ; auto. destruct u ; simpl ; auto.
destruct m ; auto. simpl in H0. simpl in H. destruct u ; auto.
Qed.

Definition val1 (n : UnDeux) (r : V) :=
  match n with
    | Un => False
    | Deux => True
  end.

Lemma persist_val1 : forall u v, UDle u v -> forall p, val1 u p -> val1 v p.
Proof.
intros. destruct u.
- simpl in H0. inversion H0.
- simpl in H0. destruct v.
  + simpl. inversion H.
  + simpl. auto.
Qed.

Instance M0 : model :=
      {|
        nodes := UnDeux ;
        reachable := UDle ;
        val := val1 ;

        reach_refl u := UDle_refl u ;
        reach_tran u v w := @UDle_trans u v w ;

        persist := persist_val1;
      |}.

Definition val2 (n : UnDeuxTrois) (p : V) :=
  match n with
    | UnDeux_I n => match n with
                                | Un => False
                                | Deux => True
                                end
    | Trois => True
  end.

Lemma persist_val2 : forall u v,
  UDTle u v -> forall p, val2 u p -> val2 v p.
Proof.
intros. destruct u.
- destruct u. simpl in H0. inversion H0. simpl in H0.
  destruct v ; auto.
- simpl in H0. destruct v ; simpl ; auto.
Qed.

Instance M2 : model :=
      {|
        nodes := UnDeuxTrois ;
        reachable := UDTle ;
        val := val2 ;

        reach_refl u := UDTle_refl u ;
        reach_tran u v w := @UDTle_trans u v w ;

        persist := persist_val2;
      |}.

Inductive TpFq (r : V) : Prop :=
 | Fq : ((r = q) -> False) -> TpFq r.

Definition val3 (n : UnDeuxTrois) (r : V) :=
  match n with
    | UnDeux_I n => match n with
                                | Un => TpFq r
                                | Deux => True
                                end
    | Trois => True
  end.

Lemma persist_val3 : forall u v,
  UDTle u v -> forall r, val3 u r -> val3 v r.
Proof.
intros. destruct u.
- destruct u.
  + simpl in H0. simpl in H. destruct v.
    * destruct u. simpl. auto. simpl. auto.
    * simpl. auto.
  + simpl in H0. simpl in H. destruct v.
    * destruct u. simpl. inversion H. simpl. auto.
    * simpl. auto.
- simpl in H0. simpl in H. destruct v ; auto.
  destruct u ; auto. inversion H.
Qed.




(* destruct (eq_dec_propvar r p).
  + subst. destruct v ; auto. simpl. destruct u0. split ; auto. apply diff_prop.
     apply Logic.I. simpl. apply Logic.I.
  + destruct (eq_dec_propvar r q).
    * subst. destruct v ; auto. simpl. destruct u0. simpl in H0. destruct u.
      inversion H0. exfalso ; apply H1 ; auto. 2: auto. simpl in H. inversion H.
      simpl. auto.
    * 



  + destruct u. destruct p. simpl in H0. destruct v ; auto. simpl. destruct u ; auto.
     destruct p. simpl in H0. destruct v ; auto. simpl. destruct u ; auto.
  + destruct v ; simpl ; auto. destruct u0 ; auto. simpl in H0. destruct u ; auto.
- destruct PQ1.
  + destruct p. simpl in H0. destruct v ; simpl ; auto. destruct u ; simpl ; auto.
  + simpl in H0. destruct v ; simpl ; auto. destruct u ; simpl ; auto.
Qed. *)

Instance M1 : model :=
      {|
        nodes := UnDeuxTrois ;
        reachable := UDTle ;
        val := val3 ;

        reach_refl u := UDTle_refl u ;
        reach_tran u v w := @UDTle_trans u v w ;

         persist := persist_val3;
      |}.

End DefModels.



Section Counterexamples.

(* sBIL is not a subset of wBIL. *)

Lemma Consequences_Soundness1 :
  exists s, (sBIH_rules s) /\ ((wBIH_rules s) -> False).
Proof.
exists (Singleton _ (Var p),  Neg (wNeg (Var p))).
split.
- apply DNs with (ps:=[(Singleton _  (Var p), (Var p))]).
  2: apply DNsRule_I. intros. inversion H ; subst. 2: inversion H0.
  apply Ids. apply IdRule_I. apply In_singleton.
- intro. apply wSoundness0 in H. simpl in H. unfold loc_conseq in H.
  pose (H M0 Deux).
  assert (J0: wforces M0 Deux (Neg (wNeg (Var p)))).
  { assert (forall A : BPropF V, In (BPropF V) (Singleton (BPropF V) # p) A -> wforces M0 Deux A).
    intros. inversion H0. subst. simpl. apply Logic.I.
    apply e in H0. destruct H0. destruct H0. inversion H0. subst. auto. }
  pose (J0 Deux Logic.I). simpl in w. apply w. exists Un. repeat split ; auto.
Qed.

Theorem sBIH_not_incl_wBIH : exists G,
   (spair_derrec G) /\
   ((wpair_derrec G) -> False).
Proof.
destruct Consequences_Soundness1. exists (fst x, (fun y => y = snd x)).
split. destruct x. simpl. exists [b]. repeat split ; auto. apply NoDup_cons.
intro. inversion H0. apply NoDup_nil. intros. inversion H0. subst. simpl.
auto. inversion H1. simpl. destruct H. Search Or sBIH_rules.
apply MPs with (ps:=[(e, Imp b (Or b (Bot V)));(e, b)]).
2: apply MPRule_I. intros. inversion H1. subst. apply Axs.
apply AxRule_I. apply RA2_I. exists b. exists (Bot V). auto.
inversion H2. 2: inversion H3. subst. auto.
intros. destruct H0. destruct H0. destruct x.
simpl in H1. destruct H1. destruct H. apply H3.
assert (x0 = [b] \/ x0 = []).
destruct x0 ; auto. destruct x0.
left. pose (H1 b0). destruct e0 ; auto. simpl. auto.
exfalso. inversion H0. subst. inversion H7. subst.
pose (H1 b0). destruct e0 ; auto. simpl. auto.
pose (H1 b1). destruct e0 ; auto. simpl ; auto. apply H6. simpl ; auto.
destruct H4. subst. simpl in H2.
apply absorp_Or1 ; auto. subst.
simpl in H2.
apply MP with (ps:=[(e, Imp (Bot V) b);(e, Bot V)]). 2:apply MPRule_I.
intros. inversion H4. subst. apply wEFQ. inversion H5. subst. 2: inversion H6.
auto.
Qed.

(* Failure of deduction theorem for FOsBIL *)

Lemma Consequences_Soundness2 :
  (sBIH_rules (Singleton _ (Var p), Neg (wNeg (Var p))) /\
  ((sBIH_rules (Empty_set _, Imp (Var p) (Neg (wNeg (Var p))))) -> False)).
Proof.
split.
- apply DNs with (ps:=[(Singleton _ (Var p), Var p)]).
  2: apply DNsRule_I. intros. inversion H ; subst. 2: inversion H0.
  apply Ids. apply IdRule_I. apply In_singleton.
- intro. apply sSoundness0 in H. simpl in H. unfold glob_conseq in H.
   assert (J0: (forall A, In _ (Empty_set _) A -> forall u : UnDeux, wforces M0 u  A)).
  { intros. inversion H0. }
  pose (H M0 J0 Deux).
  destruct e. destruct H0. inversion H0. subst. clear H0.
  pose (H1 Deux Logic.I Logic.I Deux Logic.I). simpl in w.
  apply w. exists Un. repeat split ; auto.
Qed.

Theorem failure_gen_sBIH_Deduction_Theorem : exists A B Γ,
  (spair_derrec (Union _ Γ (Singleton _ (A)), Singleton _ (B))) /\
  ((spair_derrec (Γ, Singleton _ (A → B))) -> False).
Proof.
exists (# p). exists (Neg (wNeg (# p))). exists (Empty_set _).
split.
- unfold spair_derrec. exists [(Neg (wNeg (# p)))].
  repeat split. apply NoDup_cons. intro. inversion H. apply NoDup_nil.
  intros. simpl. inversion H. subst. apply In_singleton. inversion H0.
  simpl. assert (Union _ (Empty_set _) (Singleton _ # p) = Singleton _ # p).
  apply Extensionality_Ensembles. unfold Same_set. split. intro. intros.
  inversion H. inversion H0. inversion H0. subst ; auto. intro. intros.
  inversion H. subst. apply Union_intror. auto. rewrite H. pose (extens_diff_sBIH p).
  apply MPs with (ps:=[(Singleton _ # p, Imp (Neg (wNeg # p)) (Or (Neg (wNeg # p)) (Bot V)));(Singleton _ # p, (Neg (wNeg # p)))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Axs. apply AxRule_I.
  apply RA2_I. exists (Neg (wNeg # p)). exists (Bot V). auto. inversion H1. subst.
  assumption. inversion H2.
- intro. apply sSoundness in H. unfold glob_conseq in H.
  assert (J1: (forall A : BPropF V, In (BPropF V) (Empty_set (BPropF V)) A -> mforces M0 A)).
  intros. inversion H0.
  pose (H M0 J1 Deux). destruct e. destruct H0. inversion H0. subst. pose (H1 Deux).
  simpl in w. pose (w Logic.I Logic.I). apply f with (v:= Deux) ; auto.
  exists Un. repeat split ; auto.
Qed.

(* DMP fails in sBIL. *)

Lemma Consequences_Soundness3 :
  (spair_derrec (Singleton _  (Var p), Union _ (Singleton _  (Var q)) (Singleton _  (Neg (wNeg (wNeg (Var q)))))))
  -> False.
Proof.
intro. apply sSoundness in H. unfold glob_conseq in H.
assert (J0: (forall A : BPropF V, In (BPropF V) (Singleton (BPropF V) # p) A -> mforces M1 A)).
{ intros. inversion H0. subst. intro. destruct w ; simpl ; auto.
  destruct u ; simpl ; auto. apply Fq. apply diff_prop. }
pose (H M1 J0 (UnDeux_I Un)).
destruct e. destruct H0. clear H. inversion H0.
subst. inversion H. subst. simpl in H1. inversion H1.
subst. inversion H. subst. clear H0. apply H2 ; auto.
subst. inversion H. subst. clear H0.
pose (H1 (UnDeux_I Deux) Logic.I).
simpl in w. apply w. exists Trois. repeat split ; auto.
intro. destruct H0. destruct H0. destruct H2.
apply H3. destruct x. destruct u ; simpl ; auto.
simpl in H3. simpl in H0. inversion H0.
simpl. auto.
Qed.

(* Failure dual deduction theorem *)

Theorem failure_gen_sBIH_Dual_Detachment_Theorem : exists A B Δ,
  (spair_derrec (Singleton _ (Excl A B), Δ)) /\
  ((spair_derrec (Singleton _ (A), Union _ (Singleton _ (B)) Δ)) -> False).
Proof.
exists (# p). exists (# q). exists (Singleton _ (Neg (wNeg (wNeg (# q))))). split.
- unfold spair_derrec. exists [(Neg (wNeg (wNeg (# q))))]. repeat split. apply NoDup_cons.
  intro. inversion H. apply NoDup_nil. intros. simpl. inversion H. subst. apply In_singleton.
  inversion H0. simpl.
  apply MPs with (ps:=[(Singleton _ (Excl # p # q), Imp (Neg (wNeg (wNeg # q))) (Or (Neg (wNeg (wNeg # q))) (Bot V)));(Singleton _ (Excl # p # q), (Neg (wNeg (wNeg # q))))]).
  2: apply MPRule_I. intros. inversion H. subst. apply Axs. apply AxRule_I.
  apply RA2_I. exists (Neg (wNeg (wNeg # q))). exists (Bot V). auto. inversion H0. subst.
  apply DNs with (ps:=[(Singleton _ (Excl # p # q), (wNeg # q))]). 2: apply DNsRule_I.
  intros. inversion H1. subst. apply sBIH_extens_wBIH.
  pose (wBIH_Detachment_Theorem (Empty_set _, Imp (Excl # p # q) (wNeg # q))). simpl in w.
  assert (Singleton _ (Excl # p # q) = Union _ (Empty_set _) (Singleton _ (Excl # p # q))).
  apply Extensionality_Ensembles. split. intro. intros. inversion H2. apply Union_intror. apply In_singleton.
  intro. intros. inversion H2. inversion H3. inversion H3. subst. apply In_singleton. rewrite H2. apply w ; try auto.
  apply wdual_residuation. pose (wBIH_Deduction_Theorem (Union _ (Empty_set _) (Singleton _ (# p)), Or # q (wNeg # q))).
  apply w0 ; auto. clear w0. clear w. pose (wBIH_monot (Empty_set _, Or # q (wNeg # q))). simpl in w.
  apply w. clear w.
  apply MP with (ps:=[(Empty_set _, Imp (Or # q (Excl (Top V) (# q))) (Or # q (wNeg # q)));(Empty_set _, Or # q (Excl (Top V) (# q)))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(Empty_set _, ((Excl (Top V) # q) → Or # q (wNeg # q)) → (Or # q (Excl (Top V) # q) → Or # q (wNeg # q)));
  (Empty_set _, ((Excl (Top V) # q) → Or # q (wNeg # q)))]).
  2: apply MPRule_I. intros. inversion H4. subst.
  apply MP with (ps:=[(Empty_set _, (# q → Or # q (wNeg # q)) → ((Excl (Top V) # q) → Or # q (wNeg # q)) → (Or # q (Excl (Top V) # q) → Or # q (wNeg # q)));
  (Empty_set _, (# q) → Or # q (wNeg # q))]).
  2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA4_I.
  exists (# q). exists (Excl (Top V) # q). exists (Or # q (wNeg # q)). auto. inversion H6. subst.
  apply Ax. apply AxRule_I. apply RA2_I. exists (# q). exists (wNeg # q). auto. inversion H7. inversion H5. subst.
  apply MP with (ps:=[(Empty_set _, ((wNeg # q) → Or # q (wNeg # q)) → (Excl (Top V) # q → Or # q (wNeg # q)));(Empty_set _, ((wNeg # q) → Or # q (wNeg # q)))]).
  2: apply MPRule_I. intros. inversion H6. subst.
  apply MP with (ps:=[(Empty_set _,(Excl (Top V) # q → (wNeg # q)) → ((wNeg # q) → Or # q (wNeg # q)) → (Excl (Top V) # q → Or # q (wNeg # q)));
  (Empty_set _, (Excl (Top V) # q → (wNeg # q)))]).
  2: apply MPRule_I. intros. inversion H7. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (Excl (Top V) # q). exists (wNeg # q).
  exists (Or # q (wNeg # q)). auto. inversion H8. subst. apply wimp_Id_gen. inversion H9.
  inversion H7. subst. apply Ax.
  apply AxRule_I. apply RA3_I. exists (# q). exists (wNeg # q). auto. inversion H8.
  inversion H6. inversion H4. subst.
  apply MP with (ps:=[(Empty_set _, Imp (Top V) (Or # q (Excl (Top V) # q)));(Empty_set _, Top V)]).
  2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
  apply RA11_I. exists (Top V). exists (# q). auto. inversion H6. subst.
  apply MP with (ps:=[(Empty_set _, Imp (Imp (Top V) (Top V)) (Top V));(Empty_set _, (Imp (Top V) (Top V)))]).
  2: apply MPRule_I. intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA15_I. exists (Top V → Top V). auto.
  inversion H8. subst. apply wimp_Id_gen. inversion H9. inversion H7. inversion H5.
  intro. intros. inversion H3. inversion H2. inversion H1.
- intro. apply sSoundness in H. unfold glob_conseq in H.
  assert (J0: (forall A : BPropF V, In (BPropF V) (Singleton (BPropF V) # p) A -> mforces M1 A)).
  { intros. inversion H0. subst. intro. destruct w ; simpl ; auto.
    destruct u ; simpl ; auto. apply Fq. apply diff_prop. }
  pose (H M1 J0 (UnDeux_I Un)).
  destruct e. destruct H0. clear H. inversion H0.
  subst. inversion H. subst. simpl in H1. inversion H1.
  subst. inversion H. subst. clear H0. apply H2 ; auto.
  subst. inversion H. subst. clear H0.
  pose (H1 (UnDeux_I Deux) Logic.I).
  simpl in w. apply w. exists Trois. repeat split ; auto.
  intro. destruct H0. destruct H0. destruct H2.
  apply H3. destruct x. destruct u ; simpl ; auto.
  simpl in H3. simpl in H0. inversion H0.
  simpl. auto.
Qed.

(* Validity on rooted models. *)

Lemma Rooted_models_validity : forall (M : model),
  (exists (r : @nodes M), forall w, (@reachable M r w)) ->
  (forall w, (wforces M w (Or (wNeg (Var p)) (Neg (wNeg (Var p)))))).
Proof.
intros. destruct H.
destruct (classic (wforces M x (Var p))).
- right. simpl. intros. destruct H2. destruct H2. destruct H3. apply H4.
  apply (@persist M x) ; auto.
- left. simpl. exists x. repeat split ; auto.
Qed.

(* Validity on rooted models, falsified on general models. *)

Lemma Consequences_Soundness4 :
  (sBIH_rules (Empty_set _, (Or (wNeg (Var p)) (Neg (wNeg (Var p)))))) -> False.
Proof.
intro. apply sSoundness0 in H. unfold glob_conseq in H.
assert (J0: (forall A, In _ (Empty_set _) A ->
forall u : UnDeuxTrois, wforces M2 u A)).
{ intros. inversion H0. }
pose (H M2 J0 Trois).
destruct e. destruct H0. clear H. simpl in H0. inversion H0.
subst. inversion H1.
- simpl in H. destruct H. destruct H. destruct H2. apply H3.
  destruct x. simpl. destruct u ; simpl ; auto. simpl. auto.
- pose (H (UnDeux_I Deux) Logic.I). simpl in w.
  apply w. exists (UnDeux_I Un). repeat split ; auto.
Qed.

End Counterexamples.

End ConseqSoundness.










