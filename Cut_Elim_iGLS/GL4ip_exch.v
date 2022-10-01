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
Require Import strong_inductionT.
Require Import Lia.

(* First, as we want to mimick sequents based on multisets of formulae we need to
obtain exchange. *)

(* Definition of exchange with lists of formulae directly. It is more general and should
make the proofs about exchange easier to handle. *) 

Inductive list_exch_L : relationT Seq  :=
  | list_exch_LI Γ0 Γ1 Γ2 Γ3 Γ4 A : list_exch_L
      (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, A) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A).

(* Some lemmas about In and exchange. *)

Lemma InT_list_exch_L : forall A l1 l2,
            (@list_exch_L (l1,A) (l2,A)) ->
            (forall x, (InT x l1 -> InT x l2) * (InT x l2 -> InT x l1)).
Proof.
intros A l1 l2 exch. inversion exch.
intro x. split.
- intro. apply InT_app_or in H2. destruct H2. apply InT_or_app. left. assumption.
  apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
  apply InT_or_app. right. apply InT_or_app. left. assumption. apply InT_app_or in i.
  destruct i. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. left.
  assumption. apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app.
  left. assumption. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
  assumption.
- intro. apply InT_app_or in H2. destruct H2. apply InT_or_app. left. assumption.
  apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
  apply InT_or_app. right. apply InT_or_app. left. assumption. apply InT_app_or in i.
  destruct i. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. left.
  assumption. apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app.
  left. assumption. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
  assumption.
Qed.

(* Some useful lemmas about list exchange. *)

Lemma list_exch_L_id : forall s, (@list_exch_L s s).
Proof.
intros s. destruct s. pose (list_exch_LI l
[] [] [] [] m). simpl in l0. assert (H: l ++ [] = l).
apply app_nil_r. rewrite H in l0. assumption.
Qed.

Lemma list_exch_L_same_R : forall s se,
    (@list_exch_L s se) ->
    (forall Γ Γe A0 A1, (s = (Γ , A0)) ->
    (se = (Γe , A1)) ->
    (A0 = A1)).
Proof.
intros s se exch. induction exch. intros Γ Γe A0 A1 E1 E2.
inversion E1. inversion E2. rewrite H1 in H3. assumption.
Qed.

Lemma list_exch_L_permL : forall s se,
    (@list_exch_L s se) ->
      (forall Γ0 Γ1 A C, s = ((Γ0 ++ C :: Γ1), A) ->
      (existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ C :: eΓ1), A))).
Proof.
intros s se exch. induction exch. intros Γ5 Γ6 A0 C E.
inversion E. apply partition_1_element in H0. destruct H0.
+ destruct s. destruct s. rewrite e. exists x. exists (x0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4).
  simpl.
  assert (E1: (x ++ C :: x0) ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4 = x ++ C :: x0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4).
  { symmetry. apply app_assoc with (l:=x) (m:=C :: x0) (n:=Γ3 ++ Γ2 ++ Γ1 ++ Γ4). }
  rewrite E1. reflexivity.
+ destruct s.
  * destruct s. destruct s. exists (Γ0 ++ Γ3 ++ Γ2 ++ x). exists (x0 ++ Γ4).
    rewrite e. assert (E1: Γ0 ++ Γ3 ++ Γ2 ++ (x ++ C :: x0) ++ Γ4 =
    (Γ0 ++ Γ3 ++ Γ2 ++ x) ++ C :: x0 ++ Γ4). repeat rewrite <- app_assoc. auto.
     rewrite E1. reflexivity.
  * destruct s.
    - destruct s. destruct s. exists (Γ0 ++ Γ3 ++ x). exists (x0 ++ Γ1 ++ Γ4).
      rewrite e. assert (E1: Γ0 ++ Γ3 ++ (x ++ C :: x0) ++ Γ1 ++ Γ4 =
      (Γ0 ++ Γ3 ++ x) ++ C :: x0 ++ Γ1 ++ Γ4). repeat rewrite <- app_assoc. auto.
      rewrite E1. reflexivity.
    - destruct s.
      { destruct s. destruct s. rewrite e. exists (Γ0 ++ x). exists (x0 ++ Γ2 ++ Γ1 ++ Γ4).
        assert (E1: Γ0 ++ (x ++ C :: x0) ++ Γ2 ++ Γ1 ++ Γ4 =
        (Γ0 ++ x) ++ C :: x0 ++ Γ2 ++ Γ1 ++ Γ4). repeat rewrite <- app_assoc. auto.
        rewrite E1. reflexivity. }
      { destruct s. destruct s. rewrite e. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ x).
        exists x0. assert (E1: Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ x ++ C :: x0 =
        (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ x) ++ C :: x0). repeat rewrite <- app_assoc. auto.
        rewrite E1. reflexivity. }
Qed.

(* Some lemmas about nobox_gen_ext and exchange. *)

Lemma nobox_gen_ext_exch_L : forall A0 A1 l0 l1 l2,
    (nobox_gen_ext l0 l1) -> (@list_exch_L (l1, A0) (l2,A0)) ->
    existsT2 l3, (nobox_gen_ext l3 l2) * (list_exch_L (l0,A1) (l3,A1)).
Proof.
intros A0 A1 l0. induction l0.
+ intros l1 l2 gen. inversion gen.
  - intro exch. inversion exch. apply app_eq_nil in H1. destruct H1. apply app_eq_nil in H3. destruct H3.
    apply app_eq_nil in H4. destruct H4. apply app_eq_nil in H5. destruct H5.
    subst. simpl. exists []. split.
    * apply univ_gen_ext_nil.
    * apply list_exch_L_id.
  - intros exch. exists []. split.
    * subst. apply all_P_univ_gen_ext_nil. intros. pose (InT_list_exch_L _ _ _ exch).
      pose (p x0). destruct p0. apply i0 in H0. inversion H0. subst. apply H.
      assumption. subst. pose (univ_gen_ext_nil_all_P gen). apply f in H0.
      assumption. assumption.
    * apply list_exch_L_id.
+ intros l1 l2 gen. induction gen.
  - intro exch. inversion exch. destruct Γ0.
    * rewrite app_nil_l in H0. rewrite app_nil_l in H. rewrite app_nil_l. destruct Γ1.
      { rewrite app_nil_l in H0. destruct Γ2.
        + rewrite app_nil_l in H0. destruct Γ3.
          - rewrite app_nil_l in H0. repeat rewrite app_nil_l in H. destruct Γ4.
            * simpl. exists []. split. apply univ_gen_ext_nil. apply list_exch_L_id.
            * inversion H0.
          - inversion H0.
        + inversion H0. }
      { inversion H0. }
    * inversion H0.
  - intro exch. inversion exch. destruct Γ0.
    * rewrite app_nil_l in H. rewrite app_nil_l in H0. rewrite app_nil_l. destruct Γ1.
      { rewrite app_nil_l in H0. destruct Γ2.
        + rewrite app_nil_l in H0. destruct Γ3.
          - rewrite app_nil_l in H0. repeat rewrite app_nil_l in H. destruct Γ4.
            * inversion H0.
            * inversion H0. simpl. subst. exists (x :: l).
              split. apply univ_gen_ext_cons. assumption. apply list_exch_L_id.
          - repeat rewrite app_nil_l in H. repeat rewrite app_nil_l. simpl. simpl in H. simpl in H0.
            inversion H0. subst. exists (x :: l). split. apply univ_gen_ext_cons. assumption. apply list_exch_L_id.
        + rewrite app_nil_l. rewrite app_nil_l in H. inversion H0. subst.
          pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p.
          pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p. subst.
          exists (x2 ++ x :: x0 ++ x3). split.
          - apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u u2).
            pose (univ_gen_ext_combine u1 u3). assumption.
          - pose (list_exch_LI [] [] (x :: x0) x2 x3 A1). repeat rewrite app_nil_l in l. assumption. }
      { inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u2).
        repeat destruct s. repeat destruct p. subst. exists (x4 ++ x2 ++ (x :: x0) ++ x5).
        split.
        - apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u u4).
          pose (univ_gen_ext_combine u1 u5). pose (univ_gen_ext_combine u3 u6). assumption.
        - pose (list_exch_LI [] (x :: x0) x2 x4 x5 A1). rewrite app_nil_l in l. assumption. }
    * inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u0).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u2).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u4).
      repeat destruct s. repeat destruct p. subst. exists (x :: x0 ++ x6 ++ x4 ++ x2 ++ x7).
      split.
      { apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u1 u6).
        pose (univ_gen_ext_combine u3 u7). pose (univ_gen_ext_combine u5 u8).
        pose (univ_gen_ext_combine u u9). assumption. }
      { assert (E1: x :: x0 ++ x2 ++ x4 ++ x6 ++ x7 = (x :: x0) ++ x2 ++ x4 ++ x6 ++ x7).
        reflexivity. rewrite E1.
        assert (E2: x :: x0 ++ x6 ++ x4 ++ x2 ++ x7 = (x :: x0) ++ x6 ++ x4 ++ x2 ++ x7).
        reflexivity. rewrite E2. apply list_exch_LI. }
  - intro exch. inversion exch. destruct Γ0.
    * rewrite app_nil_l in H. rewrite app_nil_l in H0. rewrite app_nil_l. destruct Γ1.
      { rewrite app_nil_l in H0. destruct Γ2.
        + rewrite app_nil_l in H0. destruct Γ3.
          - rewrite app_nil_l in H0. repeat rewrite app_nil_l in H. destruct Γ4.
            * inversion H0.
            * inversion H0. simpl. subst. exists l.
              split. apply univ_gen_ext_extra. assumption. assumption. apply list_exch_L_id.
          - repeat rewrite app_nil_l in H. repeat rewrite app_nil_l. simpl. simpl in H. simpl in H0.
            inversion H0. subst. exists l. split. apply univ_gen_ext_extra. assumption. assumption. apply list_exch_L_id.
        + rewrite app_nil_l. rewrite app_nil_l in H. inversion H0. subst.
          pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p0.
          pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p0. subst.
          exists (x2 ++ x0 ++ x3). split.
          - apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u u2).
            pose (univ_gen_ext_combine u1 u3). assumption. assumption.
          - pose (list_exch_LI [] [] x0 x2 x3 A1). repeat rewrite app_nil_l in l. assumption. }
      { inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p0.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u2).
        repeat destruct s. repeat destruct p0. subst. exists (x4 ++ x2 ++ x0 ++ x5).
        split.
        - apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u u4).
          pose (univ_gen_ext_combine u1 u5). pose (univ_gen_ext_combine u3 u6). assumption. assumption.
        - pose (list_exch_LI [] x0 x2 x4 x5 A1). rewrite app_nil_l in l. assumption. }
    * inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u0).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u2).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u4).
      repeat destruct s. repeat destruct p0. subst. exists (x0 ++ x6 ++ x4 ++ x2 ++ x7).
      split.
      { apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u1 u6).
        pose (univ_gen_ext_combine u3 u7). pose (univ_gen_ext_combine u5 u8).
        pose (univ_gen_ext_combine u u9). assumption. assumption. }
      { apply list_exch_LI. }
Qed.

(* Interactions between exchange and rules. *)

Lemma list_exch_L_IdP_notapplic : forall s se,
    (@list_exch_L s se) ->
    ((IdPRule [] s) -> False) ->
    ((IdPRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H. apply partition_1_element in H.
destruct H.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ # P :: x0) ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4 =
  x ++ # P :: x0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4).
  pose (app_assoc x (# P :: x0) (Γ1 ++ Γ2 ++ Γ3 ++ Γ4)). rewrite <- e0.
  auto. rewrite E. apply IdPRule_I.
- destruct s.
  + destruct s. destruct s. rewrite e.
    assert (E: Γ0 ++ Γ1 ++ Γ2 ++ (x ++ # P :: x0) ++ Γ4 =
    Γ0 ++ Γ1 ++ Γ2 ++ x ++ # P :: x0 ++ Γ4).
    pose (app_assoc x (# P :: x0) Γ4).
    simpl in e0. rewrite <- e0. reflexivity. rewrite E.
    assert (E1: Γ0 ++ Γ1 ++ Γ2 ++ x ++ # P :: x0 ++ Γ4 =
    (Γ0 ++ Γ1 ++ Γ2 ++ x) ++ # P :: x0 ++ Γ4). repeat rewrite <- app_assoc. auto.
    rewrite E1. apply IdPRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Γ0 ++ Γ1 ++ (x ++ # P :: x0) ++ Γ3 ++ Γ4 =
      (Γ0 ++ Γ1 ++ x) ++ # P :: x0 ++ Γ3 ++ Γ4). repeat rewrite <- app_assoc. auto.
      rewrite E. apply IdPRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ (x ++ # P :: x0) ++ Γ2 ++ Γ3 ++ Γ4 =
        (Γ0 ++ x) ++ # P :: x0 ++ Γ2 ++ Γ3 ++ Γ4). repeat rewrite <- app_assoc. auto.
        rewrite E. apply IdPRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x ++ # P :: x0 =
        (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x) ++ # P :: x0). repeat rewrite <- app_assoc. auto.
        rewrite E. apply IdPRule_I. }
Qed.

Lemma list_exch_L_Id_notapplic : forall s se,
    (@list_exch_L s se) ->
    ((IdRule [] s) -> False) ->
    ((IdRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H. apply partition_1_element in H.
destruct H ; subst.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ A :: x0) ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4 =
  x ++ A :: x0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4).
  pose (app_assoc x (A :: x0) (Γ1 ++ Γ2 ++ Γ3 ++ Γ4)). rewrite <- e0.
  auto. rewrite E. apply IdRule_I.
- destruct s ; subst.
  + destruct s. destruct s. rewrite e.
    assert (E: Γ0 ++ Γ1 ++ Γ2 ++ (x ++ A :: x0) ++ Γ4 =
    Γ0 ++ Γ1 ++ Γ2 ++ x ++ A :: x0 ++ Γ4).
    pose (app_assoc x (A :: x0) Γ4).
    simpl in e0. rewrite <- e0. reflexivity. rewrite E. subst.
    assert (E1: Γ0 ++ Γ1 ++ Γ2 ++ x ++ A :: x0 ++ Γ4 =
    (Γ0 ++ Γ1 ++ Γ2 ++ x) ++ A :: x0 ++ Γ4). repeat rewrite <- app_assoc. auto.
    rewrite E1. apply IdRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Γ0 ++ Γ1 ++ (x ++ A :: x0) ++ Γ3 ++ Γ4 =
      (Γ0 ++ Γ1 ++ x) ++ A :: x0 ++ Γ3 ++ Γ4). repeat rewrite <- app_assoc. auto.
      rewrite E. apply IdRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ (x ++ A :: x0) ++ Γ2 ++ Γ3 ++ Γ4 =
        (Γ0 ++ x) ++ A :: x0 ++ Γ2 ++ Γ3 ++ Γ4).
        pose (app_assoc x (A :: x0) (Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e0. simpl.
        pose (app_assoc Γ0 x (A :: x0 ++ Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e1. reflexivity. rewrite E. apply IdRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x ++ A :: x0 =
        (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x) ++ A :: x0). repeat rewrite <- app_assoc. auto.
        rewrite E. apply IdRule_I. }
Qed.

Lemma list_exch_L_BotL_notapplic : forall s se,
    (@list_exch_L s se) ->
    ((BotLRule [] s) -> False) ->
    ((BotLRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H. apply partition_1_element in H.
destruct H.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ Bot :: x0) ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4 =
  x ++ Bot :: x0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4). repeat rewrite <- app_assoc. auto.
  rewrite E. apply BotLRule_I.
- destruct s.
  + destruct s. destruct s. rewrite e.
    assert (E: Γ0 ++ Γ1 ++ Γ2 ++ (x ++ Bot :: x0) ++ Γ4 =
    Γ0 ++ Γ1 ++ Γ2 ++ x ++ Bot :: x0 ++ Γ4). repeat rewrite <- app_assoc. auto. rewrite E.
    assert (E1: Γ0 ++ Γ1 ++ Γ2 ++ x ++ Bot :: x0 ++ Γ4 =
    (Γ0 ++ Γ1 ++ Γ2 ++ x) ++ Bot :: x0 ++ Γ4). repeat rewrite <- app_assoc. auto.
    rewrite E1. apply BotLRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Γ0 ++ Γ1 ++ (x ++ Bot :: x0) ++ Γ3 ++ Γ4 =
      (Γ0 ++ Γ1 ++ x) ++ Bot :: x0 ++ Γ3 ++ Γ4). repeat rewrite <- app_assoc. auto.
      rewrite E. apply BotLRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ (x ++ Bot :: x0) ++ Γ2 ++ Γ3 ++ Γ4 =
        (Γ0 ++ x) ++ Bot :: x0 ++ Γ2 ++ Γ3 ++ Γ4). repeat rewrite <- app_assoc. auto.
        rewrite E. apply BotLRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x ++ Bot :: x0 =
        (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x) ++ Bot :: x0). repeat rewrite <- app_assoc. auto.
        rewrite E. apply BotLRule_I. }
Qed.

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent se which is an exchanged
version of s, with some premises pse that are such that they are exchanged versions
of ps. *)

Lemma AndR_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (AndRRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (AndRRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A).
exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, B). repeat split.
Qed.

Lemma AndL_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (AndLRule [ps] s) ->
  (existsT2 pse,
    (AndLRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A :: B :: Γ1, C). repeat split. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ A :: B :: Γ5 ++ Γ6, C). repeat split. apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6, C). repeat split.
        assert (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ A :: B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ (A ∧ B :: Γ4) ++ Γ6 = (Γ0 ++ Γ5) ++ And A B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply AndLRule_I.
        assert (Γ0 ++ A :: B :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (A :: B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (A :: B :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6, C). repeat split.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ A :: B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ (A ∧ B :: Γ3) ++ Γ6 =( Γ0 ++ Γ5 ++ Γ4) ++ A ∧ B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply AndLRule_I.
      assert (Γ0 ++ A :: B :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (A :: B :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (A :: B :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ A :: B :: Γ1, C). repeat split. rewrite <- app_assoc. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6, C). repeat split.
          assert (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ A :: B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ A ∧ B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ And A B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply AndLRule_I.
          assert (Γ0 ++ A :: B :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (A :: B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (A :: B :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6, C). repeat split.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ A :: B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ A ∧ B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ A ∧ B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply AndLRule_I.
        assert (Γ0 ++ A :: B :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (A :: B :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (A :: B :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ A :: B :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat rewrite <- app_assoc. repeat split.
      assert (Γ0 ++ A :: B :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ A :: B :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ A :: B :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ A :: B :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ A :: B :: Γ1, C). repeat split. 2: apply list_exch_L_id. rewrite app_assoc.
           apply AndLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ Γ3 ++ Γ6, C). repeat split.
           assert ((Γ2 ++ Γ3) ++ A :: B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (A :: B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ A :: B :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (A :: B :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ A :: B :: Γ4 ++ Γ3 ++ Γ6, C). repeat split.
        assert (Γ2 ++ Γ5 ++ (A ∧ B :: Γ4) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ A ∧ B :: Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        apply AndLRule_I.
        assert ((Γ2 ++ Γ3) ++ A :: B :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (A :: B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ A :: B :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (A :: B :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ A :: B :: Γ1, C). repeat split.
           assert (Γ2 ++ Γ4 ++ Γ3 ++ A ∧ B :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ A ∧ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           apply AndLRule_I.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ A :: B :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ A :: B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ A :: B :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ A :: B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ A :: B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (A :: B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ A :: B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (A :: B :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply AndLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply AndLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A :: B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply AndLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ A :: B :: x0 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
              assert (Γ2 ++ x ++ A ∧ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ A ∧ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              apply AndLRule_I.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ A :: B :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ A :: B :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ A :: B :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ A :: B :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ A :: B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply AndLRule_I.
              assert (Γ2 ++ Γ3 ++ x0 ++ A :: B :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ A :: B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ A :: B :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ A :: B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ x0 ++ Γ3 ++ Γ6, C). repeat split.
              assert (Γ2 ++ Γ3 ++ x0 ++ A :: B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (A :: B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ A :: B :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (A :: B :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ A :: B :: x ++ Γ3 ++ Γ6, C). split.
           assert (Γ2 ++ Γ5 ++ (x0 ++ A ∧ B :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ A ∧ B :: x ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           apply AndLRule_I.
           assert ((Γ2 ++ Γ3 ++ x0) ++ A :: B :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ A :: B :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ A :: B :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ A :: B :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ A :: B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply AndLRule_I. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ x ++ Γ6, C). repeat split.
              assert (Γ2 ++ x ++ A :: B :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (A :: B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ A :: B :: Γ5 ++ x ++ Γ6 = Γ2 ++( A :: B :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ A :: B :: Γ4 ++ x ++ Γ6, C). repeat split.
          assert (Γ2 ++ Γ5 ++ A ∧ B :: Γ4 ++ x ++ Γ6 = (Γ2 ++ Γ5) ++ A ∧ B :: Γ4 ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply AndLRule_I.
          assert (Γ2 ++ x ++ A :: B :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (A :: B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ A :: B :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (A :: B :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: B :: x0 ++ Γ6, C). repeat split.
          assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ A ∧ B :: x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A ∧ B :: x0 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply AndLRule_I.
          assert (Γ2 ++ x ++ A :: B :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ A :: B :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: B :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: B :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
Qed.

Lemma OrR1_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (OrR1Rule [ps] s) ->
  (existsT2 pse,
    (OrR1Rule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A).
split ; auto. apply OrR1Rule_I. apply list_exch_LI.
Qed.

Lemma OrR2_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (OrR2Rule [ps] s) ->
  (existsT2 pse,
    (OrR2Rule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, B).
split ; auto. apply OrR2Rule_I. apply list_exch_LI.
Qed.

Lemma OrL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (OrLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (OrLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A :: Γ1, C). exists (Γ0 ++ B :: Γ1, C). repeat split ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ A :: Γ5 ++ Γ6, C). exists (Γ0 ++ B :: Γ5 ++ Γ6, C). repeat split ; try apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
        assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ A :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ Γ5 ++ (Or A B :: Γ4) ++ Γ6 = (Γ0 ++ Γ5) ++ Or A B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply OrLRule_I.
        assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (A :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (A :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert (Γ0 ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ A :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ (Or A B :: Γ3) ++ Γ6 =( Γ0 ++ Γ5 ++ Γ4) ++ Or A B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
      apply OrLRule_I.
      assert (Γ0 ++ A :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (A :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (A :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
      assert (Γ0 ++ B :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ A :: Γ1, C). exists ((Γ0 ++ []) ++ B :: Γ1, C). repeat split ; rewrite <- app_assoc ; simpl ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
          assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ A :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          assert (Γ0 ++ Γ5 ++ Or A B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ Or A B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
          apply OrLRule_I.
          assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (A :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (A :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ0 ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ A :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ Or A B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ Or A B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply OrLRule_I.
        assert (Γ0 ++ A :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (A :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (A :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert (Γ0 ++ B :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). exists (Γ0 ++ B :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat rewrite <- app_assoc. repeat split.
      assert (Γ0 ++ A :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
      assert (Γ0 ++ B :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ B :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ B :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ B :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ A :: Γ1, C). exists ((Γ2 ++ Γ3) ++ B :: Γ1, C).  repeat split ; try apply list_exch_L_id. rewrite app_assoc.
           apply OrLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: Γ5 ++ Γ3 ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6, C). repeat split.
           assert ((Γ2 ++ Γ3) ++ A :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (A :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ A :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (A :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ Γ3 ++ Γ6, C). exists ((Γ2 ++ Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6, C). repeat split.
        assert (Γ2 ++ Γ5 ++ (Or A B :: Γ4) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ Or A B :: Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        apply OrLRule_I.
        assert ((Γ2 ++ Γ3) ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (A :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ A :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (A :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert ((Γ2 ++ Γ3) ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (B :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ A :: Γ1, C). exists ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1, C). repeat split.
           assert (Γ2 ++ Γ4 ++ Γ3 ++ Or A B :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ Or A B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           apply OrLRule_I.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ A :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ A :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ A :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ A :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ A :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (A :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (A :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: Γ1, C).  exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply OrLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: Γ1, C). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply OrLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A :: Γ1, C). exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply OrLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ A :: x0 ++ Γ4 ++ Γ3 ++ Γ6, C). exists ((Γ2 ++ x) ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
              assert (Γ2 ++ x ++ Or A B :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ Or A B :: x0 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              apply OrLRule_I.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ A :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ A :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ B :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ B :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ B :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ A :: Γ1, C). exists (Γ2 ++ x0 ++ Γ3 ++ B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply OrLRule_I.
              assert (Γ2 ++ Γ3 ++ x0 ++ A :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ A :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ A :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ A :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x0 ++ B :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ B :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: Γ5 ++ x0 ++ Γ3 ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6, C). repeat split.
              assert (Γ2 ++ Γ3 ++ x0 ++ A :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (A :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ A :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (A :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x0 ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ A :: x ++ Γ3 ++ Γ6, C). exists ((Γ2 ++ Γ5 ++ x0) ++ B :: x ++ Γ3 ++ Γ6, C). repeat split.
           assert (Γ2 ++ Γ5 ++ (x0 ++ Or A B :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ Or A B :: x ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           apply OrLRule_I.
           assert ((Γ2 ++ Γ3 ++ x0) ++ A :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ A :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ A :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ x0) ++ B :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ B :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ B :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ B :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ A :: Γ1, C). exists (Γ2 ++ x ++ B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply OrLRule_I. apply list_exch_L_id. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: Γ5 ++ x ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ x ++ Γ6, C). repeat split.
              assert (Γ2 ++ x ++ A :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (A :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ A :: Γ5 ++ x ++ Γ6 = Γ2 ++( A :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ x ++ B :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B :: Γ5 ++ x ++ Γ6 = Γ2 ++(B :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ x ++ Γ6, C). exists ((Γ2 ++ Γ5) ++ B :: Γ4 ++ x ++ Γ6, C). repeat split.
          assert (Γ2 ++ Γ5 ++ Or A B :: Γ4 ++ x ++ Γ6 = (Γ2 ++ Γ5) ++ Or A B :: Γ4 ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply OrLRule_I.
          assert (Γ2 ++ x ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (A :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ A :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (A :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ2 ++ x ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ B :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (B :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: x0 ++ Γ6, C). exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ B :: x0 ++ Γ6, C). repeat split.
          assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ Or A B :: x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ Or A B :: x0 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply OrLRule_I.
          assert (Γ2 ++ x ++ A :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ2 ++ x ++ B :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ B :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ B :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
Qed.

Lemma ImpR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (ImpRRule [ps] s) ->
  (existsT2 pse,
    (ImpRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, B). split.
  apply ImpRRule_I. assert (Γ2 ++ A :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ2 ++ [A]) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ [A]) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ Γ3 ++ Γ6,  B). split.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ Γ4 ++ Γ3 ++ Γ6). rewrite app_assoc.
    reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
    assert (Γ2 ++ Γ3 ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (A :: Γ4) ++ Γ5 ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ A :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (A :: Γ4) ++ Γ3 ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * exists ((Γ2 ++ Γ5 ++ Γ4) ++ A :: Γ3 ++ Γ6, B). split.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4) ++ Γ3 ++ Γ6). repeat rewrite app_assoc.
      reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
      assert (Γ2 ++ Γ3 ++ Γ4 ++ A :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (Γ4 ++ [A]) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (Γ4 ++ [A]) ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: Γ6, B).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: Γ1, B).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6, B).
        split. assert (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ A :: x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ x ++ x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpRRule_I.
        assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ A :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI. }
    * repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6, B).
      split. assert (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ A :: x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ x0 ++ x ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      apply ImpRRule_I.
      assert (Γ2 ++ Γ3 ++ x0 ++ A :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ A :: x) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
  + repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6, B).
    split. assert (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I.
    assert (Γ2 ++ x ++ A :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ5 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
- repeat rewrite <- app_assoc. exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, B).
  split. apply ImpRRule_I.
  assert (Γ0 ++ A :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
Qed.

Lemma AtomImpL1_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (AtomImpL1Rule [ps] s) ->
   (existsT2 pse, (@list_exch_L ps pse) *
    ((AtomImpL1Rule [pse] se) + (AtomImpL2Rule [pse] se))).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ4.
  + simpl in e0. subst. simpl. destruct Γ5.
      * simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). split ;auto. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ # P :: Γ6 ++ A :: Γ2, C). repeat split. apply list_exch_L_id. auto.
          - exists (Γ0 ++ # P :: (Γ6 ++ x0) ++ A :: Γ2, C). repeat split. apply list_exch_L_id. left.
            assert (Γ0 ++ # P :: Γ6 ++ x0 ++ # P → A :: Γ2 =Γ0 ++ # P :: (Γ6 ++ x0) ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL1Rule_I.
          - destruct x0.
            * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat split. apply list_exch_L_id. auto.
            * inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ # P :: Γ1 ++ A :: x0 ++ Γ7, C). repeat split. apply list_exch_L_id. auto. }
      * simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { destruct Γ6.
          - simpl in e1 ; subst. simpl. exists (Γ0 ++ # P :: Γ5 ++ A :: Γ2, C) . repeat split ; auto. apply list_exch_L_id.
          - inversion e1 ; subst. exists (Γ0 ++ A :: Γ6 ++ # P :: Γ5 ++ Γ7, C) . split ; auto.
            assert (Γ0 ++ # P :: Γ5 ++ A :: Γ6 ++ Γ7 = Γ0 ++ [] ++ (# P :: Γ5) ++ (A :: Γ6) ++ Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: Γ6 ++ # P :: Γ5 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ (# P :: Γ5) ++ [] ++ Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. right. repeat rewrite <- app_Assoc ; apply AtomImpL2Rule_I. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ0 ++ Γ6) ++ # P :: Γ5 ++ A :: Γ2, C). split. 2: left.
            assert (Γ0 ++ # P :: (Γ5 ++ Γ6) ++ A :: Γ2 = Γ0 ++ [] ++ (# P :: Γ5) ++ Γ6 ++ A :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H. assert ((Γ0 ++ Γ6) ++ # P :: Γ5 ++ A :: Γ2 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ [] ++ A :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ (# P :: Γ5) ++ # P → A :: Γ2 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL1Rule_I.
          - exists ((Γ0 ++ Γ6) ++ # P :: (Γ5 ++ x1) ++ A :: Γ2, C). split. 2: left.
            assert (Γ0 ++ # P :: (Γ5 ++ Γ6 ++ x1) ++ A :: Γ2 = Γ0 ++ [] ++ (# P :: Γ5) ++ Γ6 ++ x1 ++ A :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H. assert ((Γ0 ++ Γ6) ++ # P :: (Γ5 ++ x1) ++ A :: Γ2 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ [] ++ x1 ++ A :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ (# P :: Γ5) ++ x1 ++ # P → A :: Γ2 = (Γ0 ++ Γ6) ++ # P :: (Γ5 ++ x1) ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL1Rule_I.
          - destruct x1.
            * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl.
              exists ((Γ0 ++ x0) ++ # P :: Γ5 ++ A :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ # P :: Γ5 ++ x0 ++ A :: Γ2 = Γ0 ++ [] ++ (# P :: Γ5) ++ x0 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ0 ++ x0) ++ # P :: Γ5 ++ A :: Γ2 = Γ0 ++ x0 ++ (# P :: Γ5) ++ [] ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ # P :: Γ5 ++ # P → A :: Γ2 = (Γ0 ++ x0) ++ # P :: Γ5 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL1Rule_I.
            * inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl.
              exists ((Γ0 ++ x0) ++ A :: x1 ++ # P :: Γ5 ++  Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ # P :: Γ5 ++ x0 ++ A :: x1 ++ Γ7 = Γ0 ++ (# P :: Γ5) ++ [] ++ (x0 ++ A :: x1) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ0 ++ x0) ++ A :: x1 ++ # P :: Γ5 ++ Γ7 = Γ0 ++ (x0 ++ A :: x1) ++ [] ++ (# P :: Γ5) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ # P → A :: x1 ++ # P :: Γ5 ++ Γ7 = (Γ0 ++ x0) ++ # P → A :: x1 ++ # P :: Γ5 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL2Rule_I. }
        { destruct x0.
          - simpl in e1. destruct Γ6.
            + simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat split. 2: left. apply list_exch_L_id. auto.
            + inversion e1. subst. repeat rewrite <- app_assoc ; simpl. rewrite app_nil_r.
                exists (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right ; apply AtomImpL2Rule_I.
                assert (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ [] ++ (# P :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - inversion e1. subst. exists ((Γ0 ++ Γ6) ++ # P :: Γ1 ++ A :: x0 ++ Γ7, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: Γ1 ++ A :: x0 ++ Γ6 ++ Γ7 = Γ0 ++ [] ++ (# P :: Γ1 ++ A :: x0) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6) ++ # P :: Γ1 ++ A :: x0 ++ Γ7 = Γ0 ++ Γ6 ++ (# P :: Γ1 ++ A :: x0) ++ [] ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ (# P :: Γ1 ++ # P → A :: x0) ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ1 ++ # P → A :: x0 ++ Γ7). repeat rewrite <- app_assoc. auto.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply AtomImpL1Rule_I. }
  + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
     * destruct Γ5.
        { simpl in e1. destruct Γ6.
          - simpl in e1.  subst. simpl. exists (Γ0 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left. apply list_exch_L_id.
            apply AtomImpL1Rule_I.
          - inversion e1. subst. simpl. exists (Γ0 ++ A :: Γ6 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right. 2: apply AtomImpL2Rule_I.
            assert (Γ0 ++ # P :: Γ4 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ [] ++ (A :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: Γ6 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ [] ++ (# P :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
        { inversion e1. subst. simpl. exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
          assert (Γ0 ++ # P :: Γ4 ++ A :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ (A :: Γ5) ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ (# P :: Γ4) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ # P → A :: Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ Γ6) ++ # P → A :: Γ5 ++ # P :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
     * apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { destruct Γ6.
          - simpl in e1.  subst. simpl. exists (Γ0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: (Γ4 ++ Γ5) ++ A :: Γ2 = Γ0 ++ [] ++ (# P :: Γ4) ++ Γ5 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ Γ5 ++ (# P :: Γ4) ++ [] ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ Γ5) ++ # P :: Γ4 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ # P :: Γ4 ++ # P → A :: Γ2 = (Γ0 ++ Γ5) ++ # P :: Γ4 ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          - inversion e1. subst. simpl. exists (Γ0 ++ A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ # P :: (Γ4 ++ Γ5) ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ (A :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ Γ5 ++ (# P :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ A :: (Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P → A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ # P → A :: (Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: (Γ4 ++ Γ5 ++ Γ6) ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ Γ6 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ # P → A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          - exists (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ x0 ++ A :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: (Γ4 ++ Γ5 ++ Γ6 ++ x0) ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ Γ6 ++ x0 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ x0 ++ A :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ x0 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ x0 ++ A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: (Γ4 ++ x0) ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ x0 ++ # P → A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: (Γ4 ++ x0) ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          - destruct x0.
            * simpl in e1. subst. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ x1 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ x1 ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ x1 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ x1 ++ Γ5 ++ (# P :: Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x1 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ x1 ++ Γ5) ++ # P :: Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ Γ5 ++ # P :: Γ4 ++ # P → A :: Γ2 = (Γ0 ++ x1 ++ Γ5) ++ # P :: Γ4 ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            * inversion e1. subst. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ x1 ++ A :: x0 ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ x1 ++ A :: x0 ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ (x1 ++ A :: x0) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ A :: x0 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ (x1 ++ A :: x0) ++ Γ5 ++ (# P :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x1 ++ A :: x0 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ x1) ++ A :: (x0 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ # P → A :: x0 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ x1) ++ # P → A :: (x0 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
       { destruct x1.
          - simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl. destruct Γ6.
            + simpl in e1. subst. simpl. exists (Γ0 ++ x0 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ # P :: Γ4 ++ x0 ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ [] ++ x0 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ x0 ++ [] ++ (# P :: Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ x0) ++ # P :: Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ # P :: Γ4 ++ # P → A :: Γ2 = (Γ0 ++ x0) ++ # P :: Γ4 ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            + inversion e1. subst. simpl. exists (Γ0 ++ A :: Γ6 ++ x0 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ # P :: Γ4 ++ x0 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ x0 ++ (A :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: Γ6 ++ x0 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ x0 ++ (# P :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ A :: Γ6 ++ x0 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ A :: (Γ6 ++ x0) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A :: Γ6 ++ x0 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ # P → A :: (Γ6 ++ x0) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
            exists (Γ0 ++ Γ6 ++ x0 ++ A :: x1 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ # P :: Γ4 ++ x0 ++ A :: x1 ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ (x0 ++ A :: x1) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x0 ++ A :: x1 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ Γ6 ++ (x0 ++ A :: x1) ++ (# P :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ x0 ++ A :: x1 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x0) ++ A :: x1 ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x0 ++ # P → A :: x1 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x0) ++ # P → A :: x1 ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
     * destruct x0.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            + simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ # P :: Γ1 ++  A :: Γ2, C). repeat split. apply list_exch_L_id. auto.
            + inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ [] ++ (# P :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL2Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
            exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ # P :: Γ1 ++ A :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ (A :: Γ5) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ (# P :: Γ1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ # P → A :: Γ5 ++ # P :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P → A :: Γ5 ++ # P :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
       { inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
          exists (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ A :: x0 ++ Γ7, C). repeat split. 2: left.
          assert (Γ0 ++ # P :: Γ1 ++ A :: x0 ++ Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1 ++ A :: x0) ++ Γ5 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ A :: x0 ++ Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ1 ++ A :: x0) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ A :: x0 ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ1 ++ A :: x0 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ # P → A :: x0 ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ1 ++ # P → A :: x0 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
- destruct x ; simpl in e0 ; subst ; repeat rewrite <- app_assoc ; simpl.
  * destruct Γ4.
    + simpl in e0. subst. simpl. destruct Γ5.
        { simpl in e0. simpl. destruct Γ6.
          { simpl in e0. subst. simpl. exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). split ;auto. apply list_exch_L_id. }
          { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
            - destruct x.
              * simpl in e1. subst. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat rewrite <- app_assoc. repeat split. apply list_exch_L_id. auto.
              * inversion e1. subst. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ # P :: Γ1 ++ A :: x ++ Γ7, C). repeat split ; auto. apply list_exch_L_id.
            - exists (Γ0 ++ # P :: Γ6 ++ x ++ A :: Γ2, C). repeat split ; auto. repeat rewrite <- app_assoc; apply list_exch_L_id.
              repeat rewrite <- app_assoc in RA ; auto. } }
        { simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          { destruct Γ6.
            - simpl in e1. subst. simpl.
              exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) . repeat split ;auto. apply list_exch_L_id.
            - inversion e1. subst. simpl.
              exists (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7, C) . repeat split ;auto. 2: right.
              assert (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ [] ++ (# P :: Γ1) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              apply AtomImpL2Rule_I. }
          { destruct x.
            - simpl in e1. subst. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) . repeat split ;auto. apply list_exch_L_id.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7, C) . repeat split ;auto. 2: right.
                assert (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ [] ++ (# P :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL2Rule_I.
            - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Γ6 ++ # P :: Γ1 ++ A :: x ++ Γ7, C). repeat split ;auto. 2: left.
              assert (Γ0 ++ # P :: Γ1 ++ A :: x ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1 ++ A :: x) ++ [] ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P :: Γ1 ++ A :: x ++ Γ7 = Γ0 ++ Γ6 ++ [] ++ (# P :: Γ1 ++ A :: x )++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ Γ6 ++ # P :: Γ1 ++ A :: x ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ1 ++ A :: x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P :: Γ1 ++ # P → A :: x ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ1 ++ # P → A :: x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
          { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - subst. simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ2, C). repeat split ;auto. 2: left.
              assert (Γ0 ++ # P :: Γ5 ++ Γ6 ++ A :: Γ2 = Γ0 ++ [] ++ (# P :: Γ5) ++ Γ6 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ2 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ [] ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ2 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ # P → A :: Γ2 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            - simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ x0 ++ A :: Γ2, C). repeat split ;auto. 2: left.
              assert (Γ0 ++ # P :: Γ5 ++ Γ6 ++ x0 ++ A :: Γ2 = Γ0 ++ [] ++ (# P :: Γ5) ++ Γ6 ++ x0 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ x0 ++ A :: Γ2 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ [] ++ x0 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ x0 ++ A :: Γ2 = (Γ0 ++ Γ6) ++ # P :: (Γ5 ++ x0) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ x0 ++ # P → A :: Γ2 = (Γ0 ++ Γ6) ++ # P :: (Γ5 ++ x0) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            - destruct x0.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ0 ++ x ++ # P :: Γ5 ++ A :: Γ2, C). repeat split ;auto. 2: left.
                  assert (Γ0 ++ # P :: Γ5 ++ x ++ A :: Γ2 = Γ0 ++ (# P :: Γ5) ++ [] ++ x ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ # P :: Γ5 ++ A :: Γ2 = Γ0 ++ x ++ [] ++ (# P :: Γ5) ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ0 ++ x ++ # P :: Γ5 ++ A :: Γ2 = (Γ0 ++ x) ++ # P :: Γ5 ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ # P :: Γ5 ++ # P → A :: Γ2 = (Γ0 ++ x) ++ # P :: Γ5 ++ # P → A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ0 ++ x ++ A :: x0 ++ # P :: Γ5 ++ Γ7, C). repeat split ;auto. 2: right.
                  assert (Γ0 ++ # P :: Γ5 ++ x ++ A :: x0 ++ Γ7 = Γ0 ++ (# P :: Γ5) ++ [] ++ (x ++ A :: x0) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ A :: x0 ++ # P :: Γ5 ++ Γ7 = Γ0 ++ (x ++ A :: x0) ++ [] ++ (# P :: Γ5) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ0 ++ x ++ A :: x0 ++ # P :: Γ5 ++ Γ7 = (Γ0 ++ x) ++ A :: x0 ++ # P :: Γ5 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ # P → A :: x0 ++ # P :: Γ5 ++ Γ7 = (Γ0 ++ x) ++ # P → A :: x0 ++ # P :: Γ5 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. } }
    + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
      { destruct Γ5.
        - simpl in e1. destruct Γ6.
          + simpl in e1. subst. simpl.
            exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
          + inversion e1. subst. simpl.
            exists (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7, C). repeat split.
            assert (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ [] ++ (# P :: Γ1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            right. apply AtomImpL2Rule_I.
        - inversion e1. subst. simpl.
            exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ # P :: Γ1 ++ A :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ (A :: Γ5) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ (# P :: Γ1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ # P → A :: Γ5 ++ # P :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P → A :: Γ5 ++ # P :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
      { destruct x.
          - simpl in e1. destruct Γ5.
            + simpl in e1. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7, C). repeat split.
                assert (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ [] ++ (# P :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                right. apply AtomImpL2Rule_I.
            + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ0 ++ # P :: Γ1 ++ A :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1) ++ (A :: Γ5) ++ Γ6 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ (# P :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ1 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ Γ6 ++ # P → A :: Γ5 ++ # P :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P → A :: Γ5 ++ # P :: Γ1 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ A :: x ++ Γ7, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: Γ1 ++ A :: x ++ Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ1 ++ A :: x) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ A :: x ++ Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ1 ++ A :: x) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ A :: x ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ1 ++ A :: x ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ1 ++ # P → A :: x ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ1 ++ # P → A :: x ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
      {  apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        - destruct  Γ6.
          + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ [] ++ Γ5 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ Γ5 ++ [] ++ (# P :: Γ4) ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ Γ5) ++ # P :: Γ4 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ # P :: Γ4 ++ # P → A :: Γ2 = (Γ0 ++ Γ5) ++ # P :: Γ4 ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ A :: Γ6 ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ (A :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ Γ5 ++ (# P :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ A :: (Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P → A :: Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ # P → A :: (Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
        - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          + simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ Γ6 ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ Γ6 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ # P → A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          + subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ x ++ A :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ Γ6 ++ x ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ Γ6 ++ x ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ x ++ A :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ x ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ x ++ A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: (Γ4 ++ x) ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ x ++ # P → A :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P :: (Γ4 ++ x) ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          + destruct x.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ x0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ x0 ++ A :: Γ2 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ x0 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ x0 ++ Γ5 ++ (# P :: Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ Γ5 ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ x0 ++ Γ5) ++ # P :: Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ Γ5 ++ # P :: Γ4 ++ # P → A :: Γ2 = (Γ0 ++ x0 ++ Γ5) ++ # P :: Γ4 ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ x0 ++ A :: x ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ # P :: Γ4 ++ Γ5 ++ x0 ++ A :: x ++ Γ7 = Γ0 ++ (# P :: Γ4) ++ Γ5 ++ (x0 ++ A :: x) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ A :: x ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ (x0 ++ A :: x) ++ Γ5 ++ (# P :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ A :: x ++ Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ x0) ++ A :: (x ++ Γ5) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ # P → A :: x ++ Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ x0) ++ # P → A :: (x ++ Γ5) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
        - destruct x0.
          + simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ x ++ # P :: Γ4 ++ A :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ # P :: Γ4 ++ x ++ A :: Γ2  = Γ0 ++ (# P :: Γ4) ++ [] ++ x ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x ++ # P :: Γ4 ++ A :: Γ2 = Γ0 ++ x ++ [] ++ (# P :: Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x ++ # P :: Γ4 ++ A :: Γ2 = (Γ0 ++ x) ++ # P :: Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x ++ # P :: Γ4 ++ # P → A :: Γ2 = (Γ0 ++ x) ++ # P :: Γ4 ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: Γ6 ++ x ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ # P :: Γ4 ++ x ++ A :: Γ6 ++ Γ7  = Γ0 ++ (# P :: Γ4) ++ x ++ (A :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: Γ6 ++ x ++ # P :: Γ4 ++ Γ7 = Γ0 ++ (A :: Γ6) ++ x ++ (# P :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ A :: Γ6 ++ x ++ # P :: Γ4 ++ Γ7 = Γ0 ++ A :: (Γ6 ++ x) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A :: Γ6 ++ x ++ # P :: Γ4 ++ Γ7 = Γ0 ++ # P → A :: (Γ6 ++ x) ++ # P :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ x ++ A :: x0 ++ # P :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ # P :: Γ4 ++ x ++ A :: x0 ++ Γ6 ++ Γ7  = Γ0 ++ (# P :: Γ4) ++ (x ++ A :: x0) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x ++ A :: x0 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ Γ6 ++ (x ++ A :: x0) ++ (# P :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ x ++ A :: x0 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x) ++ A :: x0 ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x ++ # P → A :: x0 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x) ++ # P → A :: x0 ++ # P :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
  * inversion e0 ; subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
    + destruct Γ4.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl.
              exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
            * inversion e1. subst. simpl.
              exists (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7, C). repeat split ; auto. apply list_exch_L_id.
          - inversion e1. subst. simpl.
            exists (Γ0 ++ # P :: Γ1 ++ Γ6 ++ A :: Γ5 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ # P :: Γ1 ++ A :: Γ5 ++ Γ6 ++ Γ7  = (Γ0 ++ # P :: Γ1) ++ (A :: Γ5) ++ [] ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ A :: Γ5 ++ Γ7 = (Γ0 ++ # P :: Γ1) ++ Γ6 ++ [] ++ (A :: Γ5) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ A :: Γ5 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6) ++ A :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ # P → A :: Γ5 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6) ++ # P → A :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
       { inversion e1. subst. simpl.
          exists (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
          assert (Γ0 ++ # P :: Γ1 ++ A :: Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ # P :: Γ1) ++ (A :: Γ4) ++ Γ5 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = (Γ0 ++ # P :: Γ1) ++ Γ6 ++ Γ5 ++ (A :: Γ4) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6 ++ Γ5) ++ A :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ # P → A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6 ++ Γ5) ++ # P → A :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
    + destruct x0.
      { destruct Γ4.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl.
              exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). repeat rewrite <- app_assoc; repeat split ; auto. apply list_exch_L_id.
            * inversion e1. subst. simpl.
              exists (Γ0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7, C). repeat rewrite <- app_assoc ; repeat split ; auto. apply list_exch_L_id.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ # P :: Γ1 ++ Γ6 ++ A :: Γ5 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ # P :: Γ1 ++ A :: Γ5 ++ Γ6 ++ Γ7  = (Γ0 ++ # P :: Γ1) ++ (A :: Γ5) ++ [] ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ A :: Γ5 ++ Γ7 = (Γ0 ++ # P :: Γ1) ++ Γ6 ++ [] ++ (A :: Γ5) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ A :: Γ5 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6) ++ A :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ # P → A :: Γ5 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6) ++ # P → A :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
       { inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
          exists (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
          assert (Γ0 ++ # P :: Γ1 ++ A :: Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ # P :: Γ1) ++ (A :: Γ4) ++ Γ5 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = (Γ0 ++ # P :: Γ1) ++ Γ6 ++ Γ5 ++ (A :: Γ4) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6 ++ Γ5) ++ A :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ # P :: Γ1 ++ Γ6 ++ Γ5 ++ # P → A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ1 ++ Γ6 ++ Γ5) ++ # P → A :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. } }
      { inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
        exists (Γ0 ++ # P :: Γ1 ++ A :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL1Rule_I.
        assert (Γ0 ++ # P :: Γ1 ++ A :: x0 ++ Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ # P :: Γ1 ++ A :: x0) ++ Γ4 ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ # P :: Γ1 ++ A :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ # P :: Γ1 ++ A :: x0) ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
    + apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++ Γ4 ++ A :: Γ2, C). repeat split ; auto. 2: left. apply list_exch_L_id.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ A :: Γ2 = Γ0 ++ # P :: (x ++ Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ # P → A :: Γ2 = Γ0 ++ # P :: (x ++ Γ4) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++ A :: Γ6 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL1Rule_I.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ A :: Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ4 ++ [] ++ (A :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ A :: Γ6 ++ Γ4 ++ Γ7 = (Γ0 ++ # P :: x) ++ (A :: Γ6) ++ [] ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ # P :: x ++ Γ6 ++ A :: Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ # P :: x ++ Γ4 ++ A :: Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ4 ++ (A :: Γ5) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: x ++ Γ6 ++ A :: Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ6 ++ (A :: Γ5) ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ # P :: x ++ Γ6 ++ A :: Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6) ++ A :: Γ5 ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: x ++ Γ6 ++ # P → A :: Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6) ++ # P → A :: Γ5 ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++ Γ5 ++ Γ4 ++ A :: Γ2, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ Γ5 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ4 ++ [] ++ Γ5 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ5 ++ Γ4 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ5 ++ [] ++ Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ # P :: x ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ0 ++ # P :: (x ++ Γ5 ++ Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ5 ++ Γ4 ++ # P → A :: Γ2 = Γ0 ++ # P :: (x ++ Γ5 ++ Γ4) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++  A :: Γ6 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL1Rule_I.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ Γ5 ++ A :: Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ4 ++ Γ5 ++ (A :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ A :: Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ # P :: x) ++ (A :: Γ6) ++ Γ5 ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            * simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ A :: Γ2, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ Γ5 ++ Γ6 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ4 ++ Γ5 ++ Γ6 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ6 ++ Γ5 ++ Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ0 ++ # P :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ # P → A :: Γ2 = Γ0 ++ # P :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            * simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ Γ5 ++ Γ6 ++ x1 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ4 ++ Γ5 ++ Γ6 ++ x1 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2 = Γ0 ++ # P :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ # P → A :: Γ2 = Γ0 ++ # P :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            * destruct x1.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists(Γ0 ++ # P :: x ++ x0 ++ Γ5 ++ Γ4 ++ A :: Γ2, C). repeat split ; auto. 2: left.
                assert (Γ0 ++ # P :: x ++ Γ4 ++ Γ5 ++ x0 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ4 ++ Γ5 ++ x0 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: x ++ x0 ++ Γ5 ++ Γ4 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ x0 ++ Γ5 ++ Γ4 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ0 ++ # P :: x ++ x0 ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ0 ++ # P :: (x ++ x0 ++ Γ5 ++ Γ4) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: x ++ x0 ++ Γ5 ++ Γ4 ++ # P → A :: Γ2 = Γ0 ++ # P :: (x ++ x0 ++ Γ5 ++ Γ4) ++ # P → A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ # P :: x ++ x0 ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
                assert (Γ0 ++ # P :: x ++ Γ4 ++ Γ5 ++ x0 ++ A :: x1 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ4 ++ Γ5 ++ (x0 ++ A :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: x ++ x0 ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ # P :: x) ++ (x0 ++ A :: x1) ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ0 ++ # P :: x ++ x0 ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ # P :: (x ++ x0) ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: x ++ x0 ++ # P → A :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ # P :: (x ++ x0) ++ # P → A :: x1 ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          - destruct x0.
            * simpl in e1. destruct Γ6.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ # P :: x ++ x1 ++ Γ4 ++ A :: Γ2, C). repeat split ; auto. 2: left.
                  assert (Γ0 ++ # P :: x ++ Γ4 ++ x1 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ Γ4 ++ [] ++ x1 ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ # P :: x ++ x1 ++ Γ4 ++ A :: Γ2 = (Γ0 ++ # P :: x) ++ x1 ++ [] ++ Γ4 ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ0 ++ # P :: x ++ x1 ++ Γ4 ++ A :: Γ2 = Γ0 ++ # P :: (x ++ x1 ++ Γ4) ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ # P :: x ++ x1 ++ Γ4 ++ # P → A :: Γ2 = Γ0 ++ # P :: (x ++ x1 ++ Γ4) ++ # P → A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ # P :: x ++ A :: Γ6 ++ x1 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
                  assert (Γ0 ++ # P :: x ++ Γ4 ++ x1 ++ A :: Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ4 ++ x1 ++ (A :: Γ6) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ # P :: x ++ A :: Γ6 ++ x1 ++ Γ4 ++ Γ7 = (Γ0 ++ # P :: x) ++ (A :: Γ6) ++ x1 ++ Γ4 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  apply AtomImpL1Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++ Γ6 ++ x1 ++ A :: x0 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ # P :: x ++ Γ4 ++ x1 ++ A :: x0 ++ Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ4 ++ (x1 ++ A :: x0) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ x1 ++ A :: x0 ++ Γ4 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ6 ++ (x1 ++ A :: x0) ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ x1 ++ A :: x0 ++ Γ4 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6 ++ x1) ++ A :: x0 ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ x1 ++ # P → A :: x0 ++ Γ4 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6 ++ x1) ++ # P → A :: x0 ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
       { destruct x1.
          - simpl in e1. destruct Γ5.
            * simpl in e1. destruct Γ6.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ # P :: x ++ x0 ++ A :: Γ2, C). repeat split ; auto. 2: left. apply list_exch_L_id.
                  assert (Γ0 ++ # P :: x ++ x0 ++ A :: Γ2 = Γ0 ++ # P :: (x ++ x0) ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ # P :: x ++ x0 ++ # P → A :: Γ2 = Γ0 ++ # P :: (x ++ x0) ++ # P → A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ # P :: x ++ A :: Γ6 ++ x0 ++ Γ7, C). repeat split ; auto. 2: left.
                  assert (Γ0 ++ # P :: x ++ x0 ++ A :: Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ x0 ++ [] ++ (A :: Γ6) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ # P :: x ++ A :: Γ6 ++ x0 ++ Γ7 = (Γ0 ++ # P :: x) ++ (A :: Γ6) ++ [] ++ x0 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  apply AtomImpL1Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: x ++ Γ6 ++ A :: Γ5 ++ x0 ++ Γ7, C) . repeat split ; auto. 2: left.
              assert (Γ0 ++ # P :: x ++ x0 ++ A :: Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ x0 ++ (A :: Γ5) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ A :: Γ5 ++ x0 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ6 ++ (A :: Γ5) ++ x0 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ A :: Γ5 ++ x0 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6) ++ A :: Γ5 ++ x0 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: x ++ Γ6 ++ # P → A :: Γ5 ++ x0 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6) ++ # P → A :: Γ5 ++ x0 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ x0 ++ A :: x1 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ # P :: x ++ x0 ++ A :: x1 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ # P :: x) ++ (x0 ++ A :: x1) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ x0 ++ A :: x1 ++ Γ7 = (Γ0 ++ # P :: x) ++ Γ6 ++ Γ5 ++ (x0 ++ A :: x1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ x0 ++ A :: x1 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6 ++ Γ5 ++ x0) ++ A :: x1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: x ++ Γ6 ++ Γ5 ++ x0 ++ # P → A :: x1 ++ Γ7 = Γ0 ++ # P :: (x ++ Γ6 ++ Γ5 ++ x0) ++ # P → A :: x1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  * destruct Γ5.
      + simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ3 ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2, C). repeat rewrite <- app_assoc in RA. split ;auto.
           repeat rewrite <- app_assoc. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ3 ++ # P :: (Γ1 ++ Γ4) ++ A :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (# P :: Γ1) ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ # P :: (Γ1 ++ Γ4) ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ [] ++ Γ4 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ4) ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply AtomImpL1Rule_I.
          - destruct x.
            + simpl in e1. subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2, C). repeat rewrite <- app_assoc. repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (# P :: Γ1) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ [] ++ Γ4 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ4) ++ # P → A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ4) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            + inversion e1. subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ # P :: Γ1 ++ A :: x ++ Γ4 ++ Γ7, C). repeat rewrite <- app_assoc. repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ # P :: Γ1 ++ A :: x ++ Γ7 = Γ3 ++ Γ4 ++ [] ++ (# P :: Γ1 ++ A :: x) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ A :: x ++ Γ4 ++ Γ7 = Γ3 ++ (# P :: Γ1 ++ A :: x) ++ [] ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL1Rule_I.
          - exists (Γ3 ++ # P :: Γ6 ++ Γ4 ++ x ++ A :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ # P :: (Γ6 ++ x) ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (# P :: Γ6) ++ x ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ # P :: Γ6 ++ Γ4 ++ x ++ A :: Γ2 = Γ3 ++ (# P :: Γ6) ++ [] ++ Γ4 ++ x ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ # P :: Γ6 ++ Γ4 ++ x ++ A :: Γ2 = Γ3 ++ # P :: (Γ6 ++ Γ4 ++ x) ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ # P :: Γ6 ++ Γ4 ++ x ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ6 ++ Γ4 ++ x) ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
      + simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { destruct Γ6.
            - simpl in e1. subst. simpl. exists (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2, C).  repeat split. 2: left.
              assert ((Γ3 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (# P :: Γ1) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ [] ++ Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ4) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            - inversion e1. subst. simpl. exists (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ4 ++ Γ7, C).  repeat split. 2: right.
              assert ((Γ3 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (# P :: Γ1) ++ (A :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ (# P :: Γ1) ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              apply AtomImpL2Rule_I. }
        { destruct x.
            - simpl in e1. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (# P :: Γ1) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ [] ++ Γ4 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ4) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ4) ++ # P → A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ4 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ Γ4 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (# P :: Γ1) ++ (A :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ (# P :: Γ1) ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL2Rule_I.
            - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ # P :: Γ1 ++ A :: x ++ Γ4 ++ Γ7, C).  repeat split. 2: left.
              assert (Γ3 ++ Γ4 ++ # P :: Γ1 ++ A :: x ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (# P :: Γ1 ++ A :: x) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ Γ6 ++ # P :: Γ1 ++ A :: x ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (# P :: Γ1 ++ A :: x) ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ # P :: Γ1 ++ A :: x ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ # P :: Γ1 ++ A :: x ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ Γ6 ++ # P :: Γ1 ++ # P → A :: x ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ # P :: Γ1 ++ # P → A :: x ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ Γ4) ++ A :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ # P :: (Γ5 ++ Γ6) ++ A :: Γ2 = Γ3 ++ Γ4 ++ (# P :: Γ5) ++ Γ6 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ Γ4) ++ A :: Γ2 = Γ3 ++ Γ6 ++ (# P :: Γ5) ++ Γ4 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ Γ6 ++ (# P :: Γ5) ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ Γ6) ++ # P :: (Γ5 ++ Γ4) ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL1Rule_I.
          - exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ Γ4 ++ x1) ++ A :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ # P :: (Γ5 ++ Γ6 ++ x1) ++ A :: Γ2 = Γ3 ++ Γ4 ++ (# P :: Γ5) ++ Γ6 ++ x1 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ Γ4 ++ x1) ++ A :: Γ2 = Γ3 ++ Γ6 ++ (# P :: Γ5) ++ Γ4 ++ x1 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ Γ6 ++ (# P :: Γ5) ++ Γ4 ++ x1 ++ # P → A :: Γ2 = (Γ3 ++ Γ6) ++ # P :: (Γ5 ++ Γ4 ++ x1) ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL1Rule_I.
          - destruct x1.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ x ++ # P :: Γ5 ++ Γ4 ++ A :: Γ2, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ # P :: Γ5 ++ x ++ A :: Γ2 = Γ3 ++ Γ4 ++ (# P :: Γ5) ++ x ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ # P :: Γ5 ++ Γ4 ++ A :: Γ2 = Γ3 ++ x ++ (# P :: Γ5) ++ Γ4 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ x ++ # P :: Γ5 ++ Γ4 ++ A :: Γ2 = (Γ3 ++ x) ++ # P :: (Γ5 ++ Γ4) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ # P :: Γ5 ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ x) ++ # P :: (Γ5 ++ Γ4) ++ # P → A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ x ++ A :: x1 ++ # P :: Γ5 ++ Γ4 ++ Γ7, C).  repeat split. 2: right.
                assert (Γ3 ++ Γ4 ++ # P :: Γ5 ++ x ++ A :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ (# P :: Γ5) ++ (x ++ A :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ A :: x1 ++ # P :: Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (x ++ A :: x1) ++ (# P :: Γ5) ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ x ++ A :: x1 ++ # P :: Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ A :: x1 ++ # P :: Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ # P → A :: x1 ++ # P :: Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ # P → A :: x1 ++ # P :: Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
  * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      + simpl in e0. simpl. destruct Γ6.
        {  simpl in e0. subst. simpl. exists (Γ3 ++ Γ5 ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2, C).  repeat split. 2: left.
            assert ((Γ3 ++ Γ4 ++ Γ5) ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ Γ5 ++ # P :: Γ1 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ Γ5 ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ5 ++ [] ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ Γ5 ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2 = (Γ3 ++ Γ5 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ Γ5 ++ Γ4 ++ # P :: Γ1 ++ # P → A :: Γ2 = (Γ3 ++ Γ5 ++ Γ4) ++ # P :: Γ1 ++ # P → A :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
         { inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - simpl. exists (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2, C).  repeat split. 2: left.
              assert ((Γ3 ++ Γ4 ++ Γ5) ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (# P :: Γ1) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ Γ5 ++ Γ4 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ5 ++ Γ4) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P ::(Γ1 ++ Γ5 ++ Γ4) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
            - destruct x0.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ Γ5 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (# P :: Γ1) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ Γ5 ++ Γ4 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ Γ5 ++ Γ4) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P ::(Γ1 ++ Γ5 ++ Γ4) ++ # P → A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ # P :: Γ1 ++ A :: x0 ++ Γ5 ++ Γ4 ++ Γ7, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ Γ5 ++ # P :: Γ1 ++ A :: x0 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (# P :: Γ1 ++ A :: x0) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ A :: x0 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (# P :: Γ1 ++ A :: x0) ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. apply AtomImpL1Rule_I.
            - simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ3 ++ # P :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ A :: Γ2, C).  repeat split. 2: left.
              assert (Γ3 ++ Γ4 ++ Γ5 ++ # P :: Γ6 ++ x0 ++ A :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (# P :: Γ6) ++ x0 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ A :: Γ2 = Γ3 ++ (# P :: Γ6) ++ Γ5 ++ Γ4 ++ x0 ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ # P :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ A :: Γ2 = Γ3 ++ # P :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ # P → A :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
      + subst. apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ2, C) . repeat split. 2: left. repeat rewrite <- app_assoc ; apply list_exch_LI.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ # P :: Γ1 ++  # P → A :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ # P :: Γ1 ++  # P → A :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H.
            apply AtomImpL1Rule_I. }
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ # P :: Γ1 ++ A :: Γ2, C). split. 2: left. repeat rewrite <- app_assoc ; apply list_exch_LI. 
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ # P → A :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ # P :: Γ1 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL1Rule_I. }
          { destruct x0 ; simpl in e0 ; inversion e0 ; subst.
            - repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ x ++ Γ5 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ2, C). repeat split. repeat rewrite <- app_assoc ; apply list_exch_LI.
              assert (Γ3 ++ x ++ Γ5 ++ Γ4 ++ # P :: Γ1 ++# P → A ::  Γ2 = (Γ3 ++ x ++ Γ5 ++ Γ4) ++ # P :: Γ1 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H0. left. apply AtomImpL1Rule_I.
            - apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
              + exists((Γ3 ++ x) ++ # P :: (Γ1 ++ Γ5 ++ Γ4) ++ A :: Γ2, C). repeat split.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ # P :: Γ1) ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ # P :: (Γ1 ++ Γ5 ++ Γ4) ++ A :: Γ2 = Γ3 ++ (x ++ # P :: Γ1) ++ Γ5 ++ Γ4 ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
                  assert (Γ3 ++ (x ++ # P :: Γ1) ++ Γ5 ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ x) ++ # P :: (Γ1 ++ Γ5 ++ Γ4) ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. left. apply AtomImpL1Rule_I.
              + destruct x1.
                 *  simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                    exists (Γ3 ++ x ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ Γ4 ++ Γ5 ++ x ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++( x ++ # P :: Γ1) ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2 = Γ3 ++(x ++ # P :: Γ1) ++ Γ5 ++ Γ4 ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ A :: Γ2 = (Γ3 ++ x) ++ # P :: (Γ1 ++ Γ5 ++ Γ4) ++ A :: Γ2). repeat rewrite <- app_assoc. auto.
                    rewrite H.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ Γ5 ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ x) ++ # P :: (Γ1 ++ Γ5 ++ Γ4) ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
                    rewrite H0. apply AtomImpL1Rule_I.
                 *  inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                    exists (Γ3 ++ x ++ # P :: Γ1 ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split. 2: left.
                    assert (Γ3 ++ Γ4 ++ Γ5 ++ x ++ # P :: Γ1 ++ A :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ # P :: Γ1 ++ A :: x1) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (x ++ # P :: Γ1 ++ A :: x1) ++ Γ5 ++ Γ4 ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ # P :: Γ1 ++ A :: x1 ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
                    rewrite H.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ # P → A :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ # P :: Γ1 ++ # P → A :: x1 ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
                    rewrite H0. apply AtomImpL1Rule_I.
              + repeat rewrite <- app_assoc. simpl.
                  exists (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2, C). repeat split. 2: left.
                  assert (Γ3 ++ Γ4 ++ Γ5 ++ x ++ # P :: x0 ++ x1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ # P :: x0) ++ x1 ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2 = Γ3 ++ (x ++ # P :: x0) ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ A :: Γ2 = (Γ3 ++ x) ++ # P :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ A :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H.
                  assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ # P → A :: Γ2 = (Γ3 ++ x) ++ # P :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H0. apply AtomImpL1Rule_I. }
      + destruct x ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in e0. subst. simpl in H0. simpl. repeat rewrite <- app_assoc. simpl.
               exists ((Γ3 ++ x0 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ x0 ++ # P :: Γ1 ++ A :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert ((Γ3 ++ x0 ++ Γ4) ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ x0 ++ [] ++ Γ4 ++ # P :: Γ1 ++ A :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H1. apply list_exch_LI.
               assert (Γ3 ++ x0 ++ Γ4 ++ # P :: Γ1 ++ # P → A :: Γ2 = (Γ3 ++ x0 ++ Γ4) ++ # P :: Γ1 ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H. apply AtomImpL1Rule_I.
            - simpl in e0. inversion e0. clear H0. subst. simpl. repeat rewrite <- app_assoc. simpl.
              apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
              + exists (Γ3 ++ # P :: (Γ1 ++ x0 ++ Γ4) ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (# P :: Γ1) ++ (A :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H.
                assert (Γ3 ++ # P :: (Γ1 ++ x0 ++ Γ4) ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ x0 ++ Γ4 ++ (A :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ1 ++ x0 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x0 ++ Γ4) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H. apply AtomImpL1Rule_I.
              + destruct x.
                 * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl.
                    exists (Γ3 ++ # P :: Γ1 ++ x0 ++ Γ4 ++ A :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (# P :: Γ1) ++ A :: Γ2). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H.
                    assert (Γ3 ++ # P :: Γ1 ++ x0 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ x0 ++ Γ4 ++ A :: Γ2). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                    assert (Γ3 ++ # P :: Γ1 ++ x0 ++ Γ4 ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x0 ++ Γ4) ++ A :: Γ2). repeat rewrite <- app_assoc ; auto.
                    rewrite H.
                    assert (Γ3 ++ # P :: Γ1 ++ x0 ++ Γ4 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x0 ++ Γ4) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; auto.
                    rewrite H0. apply AtomImpL1Rule_I.
                 * inversion e1. subst. repeat rewrite <- app_assoc. simpl.
                    exists (Γ3 ++ # P :: Γ1 ++ A :: x ++ x0 ++ Γ4 ++ Γ7, C). repeat split. 2: left. 2: apply AtomImpL1Rule_I.
                    assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: x ++ Γ7 = Γ3 ++ Γ4 ++ x0 ++ (# P :: Γ1 ++ A :: x) ++ Γ7). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H.
                    assert (Γ3 ++ # P :: Γ1 ++ A :: x ++ x0 ++ Γ4 ++ Γ7 = Γ3 ++ (# P :: Γ1 ++ A :: x) ++ x0 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
              + exists (Γ3 ++ # P :: Γ6 ++ x0 ++ Γ4 ++ x ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ x0 ++ # P :: (Γ6 ++ x) ++ A :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (# P :: Γ6) ++ x ++ A :: Γ2).
                repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
                assert (Γ3 ++ # P :: Γ6 ++ x0 ++ Γ4 ++ x ++ A :: Γ2 = Γ3 ++ (# P :: Γ6) ++ x0 ++ Γ4 ++ x ++ A :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ6 ++ x0 ++ Γ4 ++ x ++ A :: Γ2 = Γ3 ++ # P :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ A :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H.
                assert (Γ3 ++ # P :: Γ6 ++ x0 ++ Γ4 ++ x ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply AtomImpL1Rule_I. }
        { apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - destruct Γ6.
             * repeat rewrite <- app_assoc ; simpl. simpl in e1. subst.
               exists (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (x0 ++ # P :: Γ1) ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (x0 ++ # P :: Γ1) ++ [] ++ Γ4 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = (Γ3 ++ x0) ++ # P :: (Γ1 ++ Γ4) ++ A :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ x0) ++ # P :: (Γ1 ++ Γ4) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H0. apply AtomImpL1Rule_I.
             * repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
               exists (Γ3 ++ A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
               assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++( x0 ++ # P :: Γ1) ++ (A :: Γ6) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ (x0 ++ # P :: Γ1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ A :: (Γ6 ++ x0) ++ # P :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert (Γ3 ++ # P → A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ # P → A :: (Γ6 ++ x0) ++ # P :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
               rewrite H0. apply AtomImpL2Rule_I.
          - destruct x1.
             * simpl in e1. destruct Γ6.
                + repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. simpl in e1. subst.
                   exists (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2, C). split ;auto. 2: left.
                   assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (x0 ++ # P :: Γ1) ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H.
                   assert (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = Γ3 ++ (x0 ++ # P :: Γ1) ++ [] ++ Γ4 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                   assert (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ A :: Γ2 = (Γ3 ++ x0) ++ # P :: (Γ1 ++ Γ4) ++ A :: Γ2). repeat rewrite <- app_assoc ; auto.
                   rewrite H.
                   assert (Γ3 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ x0) ++ # P :: (Γ1 ++ Γ4) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; auto.
                   rewrite H0. apply AtomImpL1Rule_I.
                + repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
                   exists (Γ3 ++ A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
                   assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ # P :: Γ1) ++ (A :: Γ6) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H.
                   assert (Γ3 ++ A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ (x0 ++ # P :: Γ1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                   assert (Γ3 ++ A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ A :: (Γ6 ++ x0) ++ # P :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
                   rewrite H.
                   assert (Γ3 ++ # P → A :: Γ6 ++ x0 ++ # P :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ # P → A :: (Γ6 ++ x0) ++ # P :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
                   rewrite H0. apply AtomImpL2Rule_I.
             * repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
               exists (Γ3 ++ Γ6 ++ x0 ++ # P :: Γ1 ++ A :: x1 ++ Γ4 ++ Γ7, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ # P :: Γ1 ++ A :: x1 ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ # P :: Γ1 ++ A :: x1) ++ Γ6 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: Γ1 ++ A :: x1 ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (x0 ++ # P :: Γ1 ++ A :: x1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: Γ1 ++ A :: x1 ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ # P :: Γ1 ++ A :: x1 ++ Γ4 ++ Γ7).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: Γ1 ++ # P → A :: x1 ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ # P :: Γ1 ++ # P → A :: x1 ++ Γ4 ++ Γ7).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL1Rule_I.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            + repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ A :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ # P :: x ++ Γ6 ++ A :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ # P :: x) ++ Γ6 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ A :: Γ2 = Γ3 ++ Γ6 ++ (x0 ++ # P :: x) ++ Γ4 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ A :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ # P :: (x ++ Γ4) ++ A :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ # P :: (x ++ Γ4) ++ # P → A :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL1Rule_I.
            + repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ x2 ++ A :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ # P :: x ++ Γ6 ++ x2 ++ A :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ # P :: x) ++ Γ6 ++ x2 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ x2 ++ A :: Γ2 = Γ3 ++ Γ6 ++ (x0 ++ # P :: x) ++ Γ4 ++ x2 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ x2 ++ A :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ # P :: (x ++ Γ4 ++ x2) ++ A :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P :: x ++ Γ4 ++ x2 ++ # P → A :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ # P :: (x ++ Γ4 ++ x2) ++ # P → A :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL1Rule_I.
            + destruct x2.
              *  repeat rewrite <- app_assoc ; simpl. simpl in e1. subst.
                 exists (Γ3 ++ x1 ++ x0 ++ # P :: x ++ Γ4 ++ A :: Γ2, C). split ;auto. 2: left.
                 assert (Γ3 ++ Γ4 ++ x0 ++ # P :: x ++ x1 ++ A :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ # P :: x) ++ x1 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ x0 ++ # P :: x ++ Γ4 ++ A :: Γ2 = Γ3 ++ x1 ++ (x0 ++ # P :: x) ++ Γ4 ++ A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                 assert (Γ3 ++ x1 ++ x0 ++ # P :: x ++ Γ4 ++ A :: Γ2 = (Γ3 ++ x1 ++ x0) ++ # P :: (x ++ Γ4) ++ A :: Γ2).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ x0 ++ # P :: x ++ Γ4 ++ # P → A :: Γ2 = (Γ3 ++ x1 ++ x0) ++ # P :: (x ++ Γ4) ++ # P → A :: Γ2).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL1Rule_I.
              *  repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
                 exists (Γ3 ++ x1 ++ A :: x2 ++ x0 ++ # P :: x ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
                 assert (Γ3 ++ Γ4 ++ x0 ++ # P :: x ++ x1 ++ A :: x2 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ # P :: x) ++ (x1 ++ A :: x2) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ A :: x2 ++ x0 ++ # P :: x ++ Γ4 ++ Γ7 = Γ3 ++ (x1 ++ A :: x2) ++ (x0 ++ # P :: x) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                 assert (Γ3 ++ x1 ++ A :: x2 ++ x0 ++ # P :: x ++ Γ4 ++ Γ7 = (Γ3 ++ x1) ++ A :: (x2 ++ x0) ++ # P :: x ++ Γ4 ++ Γ7).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ # P → A :: x2 ++ x0 ++ # P :: x ++ Γ4 ++ Γ7 = (Γ3 ++ x1) ++ # P → A :: (x2 ++ x0) ++ # P :: x ++ Γ4 ++ Γ7).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL2Rule_I. }
  * destruct x0 ; simpl in e0 ; inversion e0 ; subst.
      + destruct Γ5 ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in H1. subst. repeat rewrite <- app_assoc. simpl.
              exists ((Γ3 ++ x) ++ # P :: Γ1 ++ A :: Γ2, C). repeat split. 2: left. repeat rewrite <- app_assoc. apply list_exch_L_id.
              assert (Γ3 ++ x ++ # P :: Γ1 ++ # P → A :: Γ2 = (Γ3 ++ x) ++ # P :: Γ1 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL1Rule_I.
            - simpl in H1. inversion H1. subst. apply app2_find_hole in H3. destruct H3. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ x ++ (# P :: Γ1) ++ [] ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2 = Γ3 ++ [] ++ (# P :: Γ1) ++ x ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ x ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x) ++ # P → A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply AtomImpL1Rule_I.
              * destruct x0.
               + simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2, C). repeat split. 2: left.
                  assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ x ++ (# P :: Γ1) ++ [] ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2 = Γ3 ++ [] ++ (# P :: Γ1) ++ x ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
                  assert (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x) ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ # P :: Γ1 ++ x ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x) ++ # P → A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply AtomImpL1Rule_I.
               + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ3 ++ # P :: Γ1 ++ A :: x0 ++ x ++ Γ7, C). repeat split. 2: left.
                  assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: x0 ++ Γ7 = Γ3 ++ x ++ [] ++ (# P :: Γ1 ++ A :: x0) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ # P :: Γ1 ++ A :: x0 ++ x ++ Γ7 = Γ3 ++ (# P :: Γ1 ++ A :: x0) ++ [] ++ x ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply list_exch_LI.
                  apply AtomImpL1Rule_I.
              * repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
                exists (Γ3 ++ # P :: (Γ6 ++ x ++ x0) ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: Γ6 ++ x0 ++ A :: Γ2 = Γ3 ++ x ++ (# P :: Γ6) ++ [] ++ x0 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: (Γ6 ++ x ++ x0) ++ A :: Γ2 = Γ3 ++ [] ++ (# P :: Γ6) ++ x ++ x0 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ6 ++ x ++ x0 ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ6 ++ x ++ x0) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I. }
          { apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
            - destruct Γ6.
              * simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ x ++ [] ++ (# P :: Γ1) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ [] ++ x ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ1 ++ x ++ A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ1 ++ x ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H1. apply AtomImpL1Rule_I.
              * inversion e1 ; subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ x ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ x ++ (# P :: Γ1) ++ (A :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ x ++ Γ7 = Γ3 ++ (A :: Γ6) ++ (# P :: Γ1) ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                apply AtomImpL2Rule_I.
            - destruct x0.
              * simpl in e1. destruct Γ6.
                + simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                    exists (Γ3 ++ # P :: (Γ1 ++ x) ++ A :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ2 = Γ3 ++ x ++ [] ++ (# P :: Γ1) ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ # P :: (Γ1 ++ x) ++ A :: Γ2 = Γ3 ++ (# P :: Γ1) ++ [] ++ x ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    assert (Γ3 ++ # P :: Γ1 ++ x ++ # P → A :: Γ2 = Γ3 ++ # P :: (Γ1 ++ x) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
                + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                    exists (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ x ++ Γ7, C). repeat split. 2: right.
                    assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ x ++ (# P :: Γ1) ++ (A :: Γ6) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ A :: Γ6 ++ # P :: Γ1 ++ x ++ Γ7 = Γ3 ++ (A :: Γ6) ++ (# P :: Γ1) ++ x ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    apply AtomImpL2Rule_I.
              * inversion e1. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                exists ((Γ3 ++ Γ6) ++ # P :: Γ1 ++ A :: x0 ++ x ++ Γ7, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: x0 ++ Γ6 ++ Γ7 = Γ3 ++ x ++ (# P :: Γ1 ++ A :: x0) ++ Γ6 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ # P :: Γ1 ++ A :: x0 ++ x ++ Γ7 = Γ3 ++ Γ6 ++ (# P :: Γ1 ++ A :: x0) ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P :: Γ1 ++ # P → A :: x0 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ # P :: Γ1 ++ # P → A :: x0 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
            - repeat rewrite <- app_assoc. simpl. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++  A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: Γ5 ++ Γ6 ++ A :: Γ2 = Γ3 ++ x ++ (# P :: Γ5) ++ Γ6 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ A :: Γ2 = Γ3 ++ Γ6 ++ (# P :: Γ5) ++ x ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P :: Γ5 ++ x ++ # P → A :: Γ2 = (Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
              * exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x ++ x1) ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: Γ5 ++ (Γ6 ++ x1) ++ A :: Γ2 = Γ3 ++ x ++ (# P :: Γ5) ++ Γ6 ++ x1 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x ++ x1) ++ A :: Γ2 = Γ3 ++ Γ6 ++ (# P :: Γ5) ++ x ++ x1 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P :: Γ5 ++ x ++ x1 ++ # P → A :: Γ2 = (Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x ++ x1) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
              * destruct x1.
                + simpl in e1. subst. repeat rewrite <- app_assoc. simpl.
                    exists ((Γ3 ++ x0) ++ # P :: (Γ5 ++ x) ++ A :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ x ++ # P :: Γ5 ++ x0 ++ A :: Γ2 = Γ3 ++ x ++ (# P :: Γ5) ++ x0 ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x0) ++ # P :: (Γ5 ++ x) ++ A :: Γ2 = Γ3 ++ x0 ++ (# P :: Γ5) ++ x ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    assert (Γ3 ++ x0 ++ # P :: Γ5 ++ x ++ # P → A :: Γ2 = (Γ3 ++ x0) ++ # P :: (Γ5 ++ x) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
                + inversion e1. subst. repeat rewrite <- app_assoc. simpl.
                    exists ((Γ3 ++ x0) ++ A :: x1 ++ # P :: Γ5 ++ x ++ Γ7, C). repeat split. 2: right.
                    assert (Γ3 ++ x ++ # P :: Γ5 ++ x0 ++ A :: x1 ++ Γ7 = Γ3 ++ x ++( # P :: Γ5) ++ (x0 ++ A :: x1) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x0) ++ A :: x1 ++ # P :: Γ5 ++ x ++ Γ7 = Γ3 ++ (x0 ++ A :: x1) ++ (# P :: Γ5) ++ x ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    assert (Γ3 ++ x0 ++ # P → A :: x1 ++ # P :: Γ5 ++ x ++ Γ7 = (Γ3 ++ x0) ++ # P → A :: x1 ++ # P :: Γ5 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I. }
      + apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        {  destruct Γ5.
            - simpl in e1. destruct Γ6.
              * simpl in e1.  subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ x) ++ # P :: Γ1 ++ A :: Γ2, C). repeat split. 2: left.
                repeat rewrite <- app_assoc. apply list_exch_L_id.
                assert (Γ3 ++ x ++ # P :: Γ1 ++ # P → A :: Γ2 = (Γ3 ++ x) ++ # P :: Γ1 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL1Rule_I.
              * inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ3 ++ A :: (Γ6 ++ x) ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert (Γ3 ++ A :: (Γ6 ++ x) ++ # P :: Γ1 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ [] ++ (x ++ # P :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P → A :: Γ6 ++ x ++ # P :: Γ1 ++ Γ7 = Γ3 ++ # P → A :: (Γ6 ++ x) ++ # P :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL2Rule_I.
            - inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x) ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
              assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: Γ1) ++ (A :: Γ5 )++ Γ6 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H.
              assert ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x) ++ # P :: Γ1 ++ Γ7 = Γ3 ++ Γ6 ++ (A :: Γ5) ++ (x ++ # P :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ # P → A :: Γ5 ++ x ++ # P :: Γ1 ++ Γ7 = (Γ3 ++ Γ6) ++ # P → A :: (Γ5 ++ x) ++ # P :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL2Rule_I. }
        { destruct x1.
            - simpl in e1. destruct Γ5.
              + simpl in e1. destruct Γ6.
                { simpl in e1.  subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists ((Γ3 ++ x) ++ # P :: Γ1 ++ A :: Γ2, C). repeat split. 2: left.
                  repeat rewrite <- app_assoc. apply list_exch_L_id.
                  assert (Γ3 ++ x ++ # P :: Γ1 ++ # P → A :: Γ2 = (Γ3 ++ x) ++ # P :: Γ1 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply AtomImpL1Rule_I. }
                { inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists (Γ3 ++ A :: (Γ6 ++ x) ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
                  assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: Γ1) ++ [] ++ (A :: Γ6) ++ Γ7). repeat rewrite <- app_assoc. auto.
                  rewrite H.
                  assert (Γ3 ++ A :: (Γ6 ++ x) ++ # P :: Γ1 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ [] ++ (x ++ # P :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
                  rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ # P → A :: Γ6 ++ x ++ # P :: Γ1 ++ Γ7 = Γ3 ++ # P → A :: (Γ6 ++ x) ++ # P :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply AtomImpL2Rule_I. }
              + inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x) ++ # P :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: Γ1) ++ (A :: Γ5 )++ Γ6 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x) ++ # P :: Γ1 ++ Γ7 = Γ3 ++ Γ6 ++ (A :: Γ5) ++ (x ++ # P :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P → A :: Γ5 ++ x ++ # P :: Γ1 ++ Γ7 = (Γ3 ++ Γ6) ++ # P → A :: (Γ5 ++ x) ++ # P :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL2Rule_I.
            - inversion e1 ; subst ; simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
              exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: Γ1 ++ A :: x1 ++ Γ7, C). repeat split. 2: left.
              assert (Γ3 ++ x ++ # P :: Γ1 ++ A :: x1 ++ Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: Γ1 ++ A :: x1) ++ Γ5 ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: Γ1 ++ A :: x1 ++ Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ # P :: Γ1 ++ A :: x1) ++ Γ7). repeat rewrite <- app_assoc. auto.
              repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ Γ5 ++ x ++ # P :: Γ1 ++ # P → A :: x1 ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: Γ1 ++ # P → A :: x1 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL1Rule_I. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - destruct Γ6.
              * simpl in e1; subst. simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ Γ5 ++ x) ++ # P :: x0 ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ A :: Γ2 = Γ3 ++ (x ++ # P :: x0) ++ [] ++ Γ5 ++ A :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert ((Γ3 ++ Γ5 ++ x) ++ # P :: x0 ++ A :: Γ2 = Γ3 ++ Γ5 ++ [] ++ (x ++ # P :: x0) ++ A :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ5 ++ x ++ # P :: x0 ++ # P → A :: Γ2 = (Γ3 ++ Γ5 ++ x) ++ # P :: x0 ++ # P → A :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL1Rule_I.
              * inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                exists (Γ3 ++ A :: (Γ6 ++ Γ5 ++ x) ++ # P :: x0 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ A :: Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: x0) ++ Γ5 ++ (A :: Γ6) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert (Γ3 ++ A :: (Γ6 ++ Γ5 ++ x) ++ # P :: x0 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ Γ5 ++ (x ++ # P :: x0) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P → A :: Γ6 ++ Γ5 ++ x ++ # P :: x0 ++ Γ7 = Γ3 ++ # P → A :: (Γ6 ++ Γ5 ++ x) ++ # P :: x0 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL2Rule_I.
            - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: x0 ++ A :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ Γ6 ++ A :: Γ2 = Γ3 ++ (x ++ # P :: x0) ++ Γ5 ++ Γ6 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: x0 ++ A :: Γ2 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ # P :: x0) ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ x ++ # P :: x0 ++ # P → A :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: x0 ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
              * exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: (x0 ++ x1) ++ A :: Γ2, C). repeat split. 2: left.
                assert ((Γ3 ++ x) ++ # P :: (x0 ++ Γ5 ++ Γ6 ++ x1) ++ A :: Γ2 = Γ3 ++ (x ++ # P :: x0) ++ Γ5 ++ Γ6 ++ x1 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: (x0 ++ x1) ++ A :: Γ2 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ # P :: x0) ++ x1 ++ A :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ # P :: x0) ++ x1 ++ # P → A :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P :: (x0 ++ x1) ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
              * repeat rewrite <- app_assoc ; simpl. destruct x1.
                + simpl in e1. subst. simpl. exists ((Γ3 ++ x2 ++ Γ5 ++ x) ++ # P :: x0 ++ A :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ x2 ++ A :: Γ2 = Γ3 ++ (x ++ # P :: x0) ++ Γ5 ++ x2 ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x2 ++ Γ5 ++ x) ++ # P :: x0 ++ A :: Γ2 = Γ3 ++ x2 ++ Γ5 ++ (x ++ # P :: x0) ++ A :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                    assert (Γ3 ++ x2 ++ Γ5 ++ x ++ # P :: x0 ++ # P → A :: Γ2 = (Γ3 ++ x2 ++ Γ5 ++ x) ++ # P :: x0 ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
                + inversion e1 ; subst. simpl. exists ((Γ3 ++ x2) ++ A :: (x1 ++ Γ5 ++ x) ++ # P :: x0 ++ Γ7, C). repeat split. 2: right.
                    assert (Γ3 ++ x ++ # P :: x0 ++ Γ5 ++ x2 ++ A :: x1 ++ Γ7 = Γ3 ++ (x ++ # P :: x0) ++ Γ5 ++ (x2 ++ A :: x1) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x2) ++ A :: (x1 ++ Γ5 ++ x) ++ # P :: x0 ++ Γ7 = Γ3 ++ (x2 ++ A :: x1) ++ Γ5 ++ (x ++ # P :: x0) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                    assert (Γ3 ++ x2 ++ # P → A :: x1 ++ Γ5 ++ x ++ # P :: x0 ++ Γ7 = (Γ3 ++ x2) ++ # P → A :: (x1 ++ Γ5 ++ x) ++ # P :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
            - destruct x2.
              * simpl in e1. destruct Γ6.
               + simpl in e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists ((Γ3 ++ x1 ++ x) ++ # P :: x0 ++ A :: Γ2, C). repeat split. 2: left.
                  assert (Γ3 ++ x ++ # P :: x0 ++ x1 ++ A :: Γ2 = Γ3 ++ [] ++ (x ++ # P :: x0) ++ x1 ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x1 ++ x) ++ # P :: x0 ++ A :: Γ2 = Γ3 ++ x1 ++ (x ++ # P :: x0) ++ [] ++ A :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ x1 ++ x ++ # P :: x0 ++ # P → A :: Γ2 = (Γ3 ++ x1 ++ x) ++ # P :: x0 ++ # P → A :: Γ2). repeat rewrite <- app_assoc ; simpl.
                  repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
               + inversion e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists (Γ3 ++ A :: (Γ6 ++ x1 ++ x) ++ # P :: x0 ++ Γ7, C). repeat split. 2: right.
                  assert (Γ3 ++ x ++ # P :: x0 ++ x1 ++ A :: Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: x0) ++ x1 ++ (A :: Γ6) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ A :: (Γ6 ++ x1 ++ x) ++ # P :: x0 ++ Γ7 = Γ3 ++ (A :: Γ6) ++ x1 ++ (x ++ # P :: x0) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ # P → A :: Γ6 ++ x1 ++ x ++ # P :: x0 ++ Γ7 = Γ3 ++ # P → A :: (Γ6 ++ x1 ++ x) ++ # P :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                  repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
              * inversion e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ Γ6 ++ x1) ++ A :: (x2 ++ x) ++ # P :: x0 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ # P :: x0 ++ x1 ++ A :: x2 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ # P :: x0) ++ (x1 ++ A :: x2) ++ Γ6 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ x1) ++ A :: (x2 ++ x) ++ # P :: x0 ++ Γ7 = Γ3 ++ Γ6 ++ (x1 ++ A :: x2) ++ (x ++ # P :: x0) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ x1 ++ # P → A :: x2 ++ x ++ # P :: x0 ++ Γ7 = (Γ3 ++ Γ6 ++ x1) ++ # P → A :: (x2 ++ x) ++ # P :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I. }
Qed.

Lemma AtomImpL2_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (AtomImpL2Rule [ps] s) ->
   (existsT2 pse, (@list_exch_L ps pse) *
    ((AtomImpL2Rule [pse] se) + (AtomImpL1Rule [pse] se))).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ4.
  + simpl in e0. subst. simpl. destruct Γ5.
      * simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). split ;auto. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ A :: Γ6 ++ # P :: Γ2, C). repeat split. apply list_exch_L_id. auto.
          - exists (Γ0 ++ A :: (Γ6 ++ x0) ++ # P :: Γ2, C). repeat split. repeat rewrite <- app_assoc. apply list_exch_L_id. left.
            assert (Γ0 ++ # P → A :: Γ6 ++ x0 ++ # P :: Γ2 =Γ0 ++ # P → A :: (Γ6 ++ x0) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL2Rule_I.
          - destruct x0.
            * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. apply list_exch_L_id. auto.
            * inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: x0 ++ Γ7, C). repeat split. apply list_exch_L_id. auto. }
      * simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { destruct Γ6.
          - simpl in e1 ; subst. simpl. exists (Γ0 ++ A :: Γ5 ++ # P :: Γ2, C) . repeat split ; auto. apply list_exch_L_id.
          - inversion e1 ; subst. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ5 ++ Γ7, C) . split ; auto.
            assert (Γ0 ++ A :: Γ5 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ [] ++ (A :: Γ5) ++ (# P :: Γ6) ++ Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. simpl. rewrite H.
            assert (Γ0 ++ # P :: Γ6 ++ A :: Γ5 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ (A :: Γ5) ++ [] ++ Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. right. repeat rewrite <- app_assoc ; apply AtomImpL1Rule_I. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ2, C). split. 2: left.
            assert (Γ0 ++  A :: Γ5 ++ Γ6 ++ # P :: Γ2 = Γ0 ++ [] ++ (A :: Γ5) ++ Γ6 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H. assert ((Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ2 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ [] ++ # P :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ (# P → A :: Γ5) ++ # P :: Γ2 = (Γ0 ++ Γ6) ++ # P → A :: Γ5 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL2Rule_I.
          - exists ((Γ0 ++ Γ6) ++ A :: (Γ5 ++ x1) ++ # P :: Γ2, C). split. 2: left.
            assert (Γ0 ++ A :: Γ5 ++ Γ6 ++ x1 ++ # P :: Γ2 = Γ0 ++ [] ++ (A :: Γ5) ++ Γ6 ++ x1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H. assert ((Γ0 ++ Γ6) ++ A :: (Γ5 ++ x1) ++ # P :: Γ2 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ [] ++ x1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ (# P → A :: Γ5) ++ x1 ++ # P :: Γ2 = (Γ0 ++ Γ6) ++ # P → A :: (Γ5 ++ x1) ++ # P  :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL2Rule_I.
          - destruct x1.
            * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. 
              exists ((Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ A :: Γ5 ++ x0 ++ # P :: Γ2 = Γ0 ++ [] ++ (A :: Γ5) ++ x0 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ2 = Γ0 ++ x0 ++ (A :: Γ5) ++ [] ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ # P → A :: Γ5 ++ # P :: Γ2 = (Γ0 ++ x0) ++ # P → A :: Γ5 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL2Rule_I.
            * inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl.
              exists ((Γ0 ++ x0) ++ # P :: x1 ++ A :: Γ5 ++  Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ A :: Γ5 ++ x0 ++ # P :: x1 ++ Γ7 = Γ0 ++ (A :: Γ5) ++ [] ++ (x0 ++ # P :: x1) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ0 ++ x0) ++ # P :: x1 ++  A :: Γ5 ++ Γ7 = Γ0 ++ (x0 ++ # P :: x1) ++ [] ++ ( A :: Γ5) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ # P :: x1 ++ # P → A :: Γ5 ++ Γ7 = (Γ0 ++ x0) ++ # P :: x1 ++ # P → A :: Γ5 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL1Rule_I. }
        { destruct x0.
          - simpl in e1. destruct Γ6.
            + simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left. apply list_exch_L_id. auto.
            + inversion e1. subst. repeat rewrite <- app_assoc ; simpl. rewrite app_nil_r.
                exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right ; apply AtomImpL1Rule_I.
                assert (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ [] ++ (A :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - inversion e1. subst. exists ((Γ0 ++ Γ6) ++ A :: Γ1 ++ # P :: x0 ++ Γ7, C). repeat split. 2: left.
            assert (Γ0 ++ A :: (Γ1 ++ # P :: x0) ++ Γ6 ++ Γ7 = Γ0 ++ [] ++ (A :: Γ1 ++ # P :: x0) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6) ++ A :: Γ1 ++ # P :: x0 ++ Γ7 = Γ0 ++ Γ6 ++ (A :: Γ1 ++ # P :: x0) ++ [] ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ (# P → A :: Γ1 ++ # P :: x0) ++ Γ7 = (Γ0 ++ Γ6) ++ # P → A :: Γ1 ++ # P :: x0 ++ Γ7). repeat rewrite <- app_assoc. auto.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply AtomImpL2Rule_I. }
  + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
     * destruct Γ5.
        { simpl in e1. destruct Γ6.
          - simpl in e1.  subst. simpl. exists (Γ0 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left. apply list_exch_L_id.
            apply AtomImpL2Rule_I.
          - inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right. 2: apply AtomImpL1Rule_I.
            assert (Γ0 ++ A :: Γ4 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ4) ++ [] ++ (# P :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ6 ++ A :: Γ4 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ [] ++ (A :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
        { inversion e1. subst. simpl. exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
          assert (Γ0 ++ A :: Γ4 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ4) ++ (# P :: Γ5) ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ (A :: Γ4) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ # P → A :: Γ4 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ # P → A :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ4 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ A :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
     * apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { destruct Γ6.
          - simpl in e1.  subst. simpl. exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ # P :: Γ2 = Γ0 ++ [] ++ (A :: Γ4) ++ Γ5 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ Γ5 ++ (A :: Γ4) ++ [] ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ Γ5) ++ A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ # P → A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ Γ5) ++ # P → A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          - inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ (# P :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ Γ5 ++ (A :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ Γ5) ++ A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ6 ++ Γ5 ++ # P → A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ Γ5) ++ # P → A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ Γ6 ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ Γ6 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (A :: Γ4) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ (# P → A :: Γ4) ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P → A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          - exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x0 ++ # P :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ Γ6 ++ x0 ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ Γ6 ++ x0 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x0 ++ # P :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (A :: Γ4) ++ x0 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x0 ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++  A :: (Γ4 ++ x0) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ (# P → A :: Γ4) ++ x0 ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P → A :: (Γ4 ++ x0) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          - destruct x0.
            * simpl in e1. subst. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ x1 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ x1 ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ x1 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ x1 ++ Γ5 ++ (A :: Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x1 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x1 ++ Γ5) ++ A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ Γ5 ++ # P → A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x1 ++ Γ5) ++ # P → A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            * inversion e1. subst. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ x1 ++ # P :: x0 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ x1 ++ # P :: x0 ++ Γ7 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ (x1 ++ # P :: x0) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ # P :: x0 ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ (x1 ++ # P :: x0) ++ Γ5 ++ (A :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x1 ++ # P :: x0 ++ Γ5 ++ A :: Γ4 ++ Γ7 = (Γ0 ++ x1) ++ # P :: (x0 ++ Γ5) ++ A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x1 ++ # P :: x0 ++ Γ5 ++ # P → A :: Γ4 ++ Γ7 = (Γ0 ++ x1) ++ # P :: (x0 ++ Γ5) ++ # P → A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
       { destruct x1.
          - simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl. destruct Γ6.
            + simpl in e1. subst. simpl. exists (Γ0 ++ x0 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ A :: Γ4 ++ x0 ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ [] ++ x0 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ x0 ++ [] ++ (A :: Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x0) ++ A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ # P → A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x0) ++ # P → A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            + inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ x0 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ A :: Γ4 ++ x0 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ4) ++ x0 ++ (# P :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: Γ6 ++ x0 ++ A :: Γ4 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ x0 ++ (A :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ # P :: Γ6 ++ x0 ++ A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ x0) ++ A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: Γ6 ++ x0 ++ # P → A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ x0) ++ # P → A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
            exists (Γ0 ++ Γ6 ++ x0 ++ # P :: x1 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ A :: Γ4 ++ x0 ++ # P :: x1 ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ4) ++ (x0 ++ # P :: x1) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x0 ++ # P :: x1 ++ A :: Γ4 ++ Γ7 = Γ0 ++ Γ6 ++ (x0 ++ # P :: x1) ++ (A :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ x0 ++ # P :: x1 ++ A :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x0) ++ # P :: x1 ++ A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x0 ++ # P :: x1 ++ # P → A :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x0) ++ # P :: x1 ++ # P → A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
     * destruct x0.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            + simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ A :: Γ1 ++  # P :: Γ2, C). repeat split. apply list_exch_L_id. auto.
            + inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ [] ++ (A :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL1Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
            exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ A :: Γ1 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ (# P :: Γ5) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ (A :: Γ1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ # P → A :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ # P → A :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
       { inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
          exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ1 ++ # P :: x0 ++ Γ7, C). repeat split. 2: left.
          assert (Γ0 ++ A :: Γ1 ++ # P :: x0 ++ Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1 ++ # P :: x0) ++ Γ5 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ Γ5 ++A :: Γ1 ++ # P :: x0 ++ Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (A :: Γ1 ++ # P :: x0) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ1 ++ # P :: x0 ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ A :: Γ1 ++ # P :: x0 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ Γ5 ++ # P → A :: Γ1 ++ # P :: x0 ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ # P → A :: Γ1 ++ # P :: x0 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
- destruct x ; simpl in e0 ; subst ; repeat rewrite <- app_assoc ; simpl.
  * destruct Γ4.
    + simpl in e0. subst. simpl. destruct Γ5.
        { simpl in e0. simpl. destruct Γ6.
          { simpl in e0. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). split ;auto. apply list_exch_L_id. }
          { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
            - destruct x.
              * simpl in e1. subst. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat rewrite <- app_assoc. repeat split. apply list_exch_L_id. auto.
              * inversion e1. subst. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ A :: Γ1 ++ # P :: x ++ Γ7, C). repeat split ; auto. apply list_exch_L_id.
            - exists (Γ0 ++ A :: Γ6 ++ x ++ # P :: Γ2, C). repeat split ; auto. repeat rewrite <- app_assoc; apply list_exch_L_id.
              repeat rewrite <- app_assoc in RA ; auto. } }
        { simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          { destruct Γ6.
            - simpl in e1. subst. simpl.
              exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) . repeat split ;auto. apply list_exch_L_id.
            - inversion e1. subst. simpl.
              exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C) . repeat split ;auto. 2: right.
              assert (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ [] ++ (A :: Γ1) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              apply AtomImpL1Rule_I. }
          { destruct x.
            - simpl in e1. subst. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) . repeat split ;auto. apply list_exch_L_id.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C) . repeat split ;auto. 2: right.
                assert (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ [] ++ (A :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL1Rule_I.
            - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ7, C). repeat split ;auto. 2: left.
              assert (Γ0 ++ A :: Γ1 ++ # P :: x ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1 ++ # P :: x) ++ [] ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ7 = Γ0 ++ Γ6 ++ [] ++ (A :: Γ1 ++ # P :: x )++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ7 = (Γ0 ++ Γ6) ++ A :: Γ1 ++ # P :: x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P → A :: Γ1 ++ # P :: x ++ Γ7 = (Γ0 ++ Γ6) ++ # P → A :: Γ1 ++ # P :: x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
          { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - subst. simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ2, C). repeat split ;auto. 2: left.
              assert (Γ0 ++ A :: Γ5 ++ Γ6 ++ # P :: Γ2 = Γ0 ++ [] ++ (A :: Γ5) ++ Γ6 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ2 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ [] ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ2 = (Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P → A :: Γ5 ++ # P :: Γ2 = (Γ0 ++ Γ6) ++ # P → A :: Γ5 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            - simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ x0 ++ # P :: Γ2, C). repeat split ;auto. 2: left.
              assert (Γ0 ++ A :: Γ5 ++ Γ6 ++ x0 ++ # P :: Γ2 = Γ0 ++ [] ++ (A :: Γ5) ++ Γ6 ++ x0 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ x0 ++ # P :: Γ2 = Γ0 ++ Γ6 ++ (A :: Γ5) ++ [] ++ x0 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ Γ6 ++ A :: Γ5 ++ x0 ++ # P :: Γ2 = (Γ0 ++ Γ6) ++ A :: (Γ5 ++ x0) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ Γ6 ++ # P → A :: Γ5 ++ x0 ++ # P :: Γ2 = (Γ0 ++ Γ6) ++ # P → A :: (Γ5 ++ x0) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            - destruct x0.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ0 ++ x ++ A :: Γ5 ++ # P :: Γ2, C). repeat split ;auto. 2: left.
                  assert (Γ0 ++ A :: Γ5 ++ x ++ # P :: Γ2 = Γ0 ++ (A :: Γ5) ++ [] ++ x ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ A :: Γ5 ++ # P :: Γ2 = Γ0 ++ x ++ [] ++ (A :: Γ5) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ0 ++ x ++ A :: Γ5 ++ # P :: Γ2 = (Γ0 ++ x) ++ A :: Γ5 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ # P → A :: Γ5 ++ # P :: Γ2 = (Γ0 ++ x) ++ # P → A :: Γ5 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ0 ++ x ++ # P :: x0 ++ A :: Γ5 ++ Γ7, C). repeat split ;auto. 2: right.
                  assert (Γ0 ++ A :: Γ5 ++ x ++ # P :: x0 ++ Γ7 = Γ0 ++ (A :: Γ5) ++ [] ++ (x ++ # P :: x0) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ # P :: x0 ++ A :: Γ5 ++ Γ7 = Γ0 ++ (x ++ # P :: x0) ++ [] ++ (A :: Γ5) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ0 ++ x ++ # P :: x0 ++ A :: Γ5 ++ Γ7 = (Γ0 ++ x) ++ # P :: x0 ++  A :: Γ5 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ x ++ # P :: x0 ++ # P → A :: Γ5 ++ Γ7 = (Γ0 ++ x) ++ # P :: x0 ++ # P → A :: Γ5 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. } }
    + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
      { destruct Γ5.
        - simpl in e1. destruct Γ6.
          + simpl in e1. subst. simpl.
            exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
          + inversion e1. subst. simpl.
            exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split.
            assert (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ6 ++  A :: Γ1 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ [] ++ (A :: Γ1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            right. apply AtomImpL1Rule_I.
        - inversion e1. subst. simpl.
            exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ A :: Γ1 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ (# P :: Γ5) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ (A :: Γ1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ # P → A :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ # P → A :: Γ1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
      { destruct x.
          - simpl in e1. destruct Γ5.
            + simpl in e1. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split.
                assert (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ [] ++ (A :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                right. apply AtomImpL1Rule_I.
            + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ0 ++ A :: Γ1 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1) ++ (# P :: Γ5) ++ Γ6 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7 = Γ0 ++ Γ6 ++ (# P :: Γ5) ++ (A :: Γ1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ Γ6 ++ # P :: Γ5 ++ # P → A :: Γ1 ++ Γ7 = (Γ0 ++ Γ6) ++ # P :: Γ5 ++ # P → A :: Γ1 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ1 ++ # P :: x ++ Γ7, C). repeat split. 2: left.
            assert (Γ0 ++ A :: Γ1 ++ # P :: x ++ Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A :: Γ1 ++ # P :: x) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ1 ++ # P :: x ++ Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (A :: Γ1 ++ # P :: x) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ1 ++ # P :: x ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ A :: Γ1 ++ # P :: x ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P → A :: Γ1 ++ # P :: x ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ # P → A :: Γ1 ++ # P :: x ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
      {  apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        - destruct  Γ6.
          + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ [] ++ Γ5 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ Γ5 ++ [] ++ (A :: Γ4) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ Γ5) ++ A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ5 ++ # P → A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ Γ5) ++ # P → A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ # P :: Γ6 ++ Γ7 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ (# P :: Γ6) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ Γ5 ++ (A :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ Γ5) ++ A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P :: Γ6 ++ Γ5 ++ # P → A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ Γ5) ++ # P → A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
        - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          + simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ Γ6 ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ Γ6 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (A :: Γ4) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P → A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P → A :: Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          + subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
            assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ Γ6 ++ x ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ Γ6 ++ x ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x ++ # P :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (A :: Γ4) ++ x ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ A :: (Γ4 ++ x) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ # P → A :: Γ4 ++ x ++ # P :: Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ # P → A :: (Γ4 ++ x) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          + destruct x.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ x0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ x0 ++ # P :: Γ2 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ x0 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ x0 ++ Γ5 ++ (A :: Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x0 ++ Γ5) ++ A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ Γ5 ++ # P → A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x0 ++ Γ5) ++ # P → A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ x0 ++ # P :: x ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ A :: Γ4 ++ Γ5 ++ x0 ++ # P :: x ++ Γ7 = Γ0 ++ (A :: Γ4) ++ Γ5 ++ (x0 ++ # P :: x) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ # P :: x ++ Γ5 ++ A :: Γ4 ++ Γ7 = Γ0 ++ (x0 ++ # P :: x) ++ Γ5 ++ (A :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x0 ++ # P :: x ++ Γ5 ++ A :: Γ4 ++ Γ7 = (Γ0 ++ x0) ++ # P :: (x ++ Γ5) ++ A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ # P :: x ++ Γ5 ++ # P → A :: Γ4 ++ Γ7 = (Γ0 ++ x0) ++ # P :: (x ++ Γ5) ++ # P → A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
        - destruct x0.
          + simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ x ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
              assert (Γ0 ++ A :: Γ4 ++ x ++ # P :: Γ2  = Γ0 ++ (A :: Γ4) ++ [] ++ x ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x ++ A :: Γ4 ++ # P :: Γ2 = Γ0 ++ x ++ [] ++ (A :: Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ x ++ A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x) ++ A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x ++ # P → A :: Γ4 ++ # P :: Γ2 = (Γ0 ++ x) ++ # P → A :: Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ # P :: Γ6 ++ x ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
              assert (Γ0 ++ A :: Γ4 ++ x ++ # P :: Γ6 ++ Γ7  = Γ0 ++ (A :: Γ4) ++ x ++ (# P :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: Γ6 ++ x ++ A :: Γ4 ++ Γ7 = Γ0 ++ (# P :: Γ6) ++ x ++ (A :: Γ4) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ # P :: Γ6 ++ x ++ A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ x) ++ A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P :: Γ6 ++ x ++ # P → A :: Γ4 ++ Γ7 = Γ0 ++ # P :: (Γ6 ++ x) ++ # P → A :: Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I.
          + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ Γ6 ++ x ++ # P :: x0 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
            assert (Γ0 ++ A :: Γ4 ++ x ++ # P :: x0 ++ Γ6 ++ Γ7  = Γ0 ++ (A :: Γ4) ++ (x ++ # P :: x0) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x ++ # P :: x0 ++ A :: Γ4 ++ Γ7 = Γ0 ++ Γ6 ++ (x ++ # P :: x0) ++ (A :: Γ4) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ Γ6 ++ x ++ # P :: x0 ++ A :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x) ++ # P :: x0 ++ A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ Γ6 ++ x ++ # P :: x0 ++ # P → A :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x) ++ # P :: x0 ++ # P → A :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
  * inversion e0 ; subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
    + destruct Γ4.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl.
              exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
            * inversion e1. subst. simpl.
              exists (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7, C). repeat split ; auto. apply list_exch_L_id.
          - inversion e1. subst. simpl.
            exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ A :: Γ1 ++ # P :: Γ5 ++ Γ6 ++ Γ7  = (Γ0 ++ A :: Γ1) ++ (# P :: Γ5) ++ [] ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7 = (Γ0 ++ A :: Γ1) ++ Γ6 ++ [] ++ (# P :: Γ5) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7 = Γ0 ++ A :: (Γ1 ++ Γ6) ++ # P :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P → A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7 = Γ0 ++ # P → A :: (Γ1 ++ Γ6) ++ # P :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
       { inversion e1. subst. simpl.
          exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
          assert (Γ0 ++ A :: Γ1 ++ # P :: Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A :: Γ1) ++ (# P :: Γ4) ++ Γ5 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ A :: Γ1) ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ A :: (Γ1 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ # P → A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ # P → A :: (Γ1 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
    + destruct x0.
      { destruct Γ4.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl.
              exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat rewrite <- app_assoc; repeat split ; auto. apply list_exch_L_id.
            * inversion e1. subst. simpl.
              exists (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7, C). repeat rewrite <- app_assoc ; repeat split ; auto. apply list_exch_L_id.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ A :: Γ1 ++ # P :: Γ5 ++ Γ6 ++ Γ7  = (Γ0 ++ A :: Γ1) ++ (# P :: Γ5) ++ [] ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7 = (Γ0 ++ A :: Γ1) ++ Γ6 ++ [] ++ (# P :: Γ5) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7 = Γ0 ++ A :: (Γ1 ++ Γ6) ++ # P :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P → A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7 = Γ0 ++ # P → A :: (Γ1 ++ Γ6) ++ # P :: Γ5 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
       { inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
          exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
          assert (Γ0 ++ A :: Γ1 ++ # P :: Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A :: Γ1) ++ (# P :: Γ4) ++ Γ5 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = (Γ0 ++ A :: Γ1) ++ Γ6 ++ Γ5 ++ (# P :: Γ4) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ A :: (Γ1 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ # P → A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7 = Γ0 ++ # P → A :: (Γ1 ++ Γ6 ++ Γ5) ++ # P :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. } }
      { inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
        exists (Γ0 ++ A :: Γ1 ++ # P :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL2Rule_I.
        assert (Γ0 ++ A :: Γ1 ++ # P :: x0 ++ Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A :: Γ1 ++ # P :: x0) ++ Γ4 ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ A :: Γ1 ++ # P :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ A :: Γ1 ++ # P :: x0) ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
    + apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left. apply list_exch_L_id.
              assert (Γ0 ++ A :: x ++ Γ4 ++ # P :: Γ2 = Γ0 ++ A :: (x ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A  :: x ++ Γ4 ++ # P :: Γ2 = Γ0 ++ # P → A  :: (x ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++ # P :: Γ6 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL2Rule_I.
              assert (Γ0 ++ A :: x ++ Γ4 ++ # P :: Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ4 ++ [] ++ (# P :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: x ++ # P :: Γ6 ++ Γ4 ++ Γ7 = (Γ0 ++ A :: x) ++ (# P :: Γ6) ++ [] ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ A :: x ++ Γ4 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ4 ++ (# P :: Γ5) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ6 ++ (# P :: Γ5) ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ A :: (x ++ Γ6) ++ # P :: Γ5 ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P → A :: x ++ Γ6 ++ # P :: Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ # P → A :: (x ++ Γ6) ++ # P :: Γ5 ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ A :: x ++ Γ4 ++ Γ5 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ4 ++ [] ++ Γ5 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ5 ++ [] ++ Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ A :: (x ++ Γ5 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A :: x ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ # P → A :: (x ++ Γ5 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++  # P :: Γ6 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL2Rule_I.
              assert (Γ0 ++ A :: x ++ Γ4 ++ Γ5 ++ # P :: Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ4 ++ Γ5 ++ (# P :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: x ++ # P :: Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ A :: x) ++ (# P :: Γ6) ++ Γ5 ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            * simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ A :: x ++ Γ4 ++ Γ5 ++ Γ6 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ4 ++ Γ5 ++ Γ6 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++  A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ6 ++ Γ5 ++ Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ A :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ # P → A :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            * simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ A :: x ++ Γ4 ++ Γ5 ++ Γ6 ++ x1 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ4 ++ Γ5 ++ Γ6 ++ x1 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2 = Γ0 ++ A :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2 = Γ0 ++ # P → A :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            * destruct x1.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists(Γ0 ++ A :: x ++ x0 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
                assert (Γ0 ++ A :: x ++ Γ4 ++ Γ5 ++ x0 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ4 ++ Γ5 ++ x0 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ A :: x ++ x0 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ x0 ++ Γ5 ++ Γ4 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ0 ++ A :: x ++ x0 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ A :: (x ++ x0 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P → A :: x ++ x0 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ # P → A :: (x ++ x0 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ A :: x ++ x0 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
                assert (Γ0 ++ A :: x ++ Γ4 ++ Γ5 ++ x0 ++ # P :: x1 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ4 ++ Γ5 ++ (x0 ++ # P :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ A :: x ++ x0 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ A :: x) ++ (x0 ++ # P :: x1) ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ0 ++ A :: x ++ x0 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ A :: (x ++ x0) ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ0 ++ # P → A :: x ++ x0 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ # P → A :: (x ++ x0) ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          - destruct x0.
            * simpl in e1. destruct Γ6.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ A :: x ++ x1 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
                  assert (Γ0 ++ A :: x ++ Γ4 ++ x1 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ Γ4 ++ [] ++ x1 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ A :: x ++ x1 ++ Γ4 ++ # P :: Γ2 = (Γ0 ++ A :: x) ++ x1 ++ [] ++ Γ4 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ0 ++ A :: x ++ x1 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ A :: (x ++ x1 ++ Γ4) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ # P → A :: x ++ x1 ++ Γ4 ++ # P :: Γ2 = Γ0 ++ # P → A :: (x ++ x1 ++ Γ4) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ A :: x ++ # P :: Γ6 ++ x1 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
                  assert (Γ0 ++ A :: x ++ Γ4 ++ x1 ++ # P :: Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ4 ++ x1 ++ (# P :: Γ6) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ A :: x ++ # P :: Γ6 ++ x1 ++ Γ4 ++ Γ7 = (Γ0 ++ A :: x) ++ (# P :: Γ6) ++ x1 ++ Γ4 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  apply AtomImpL2Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++ Γ6 ++ x1 ++ # P :: x0 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
              assert (Γ0 ++ A :: x ++ Γ4 ++ x1 ++ # P :: x0 ++ Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ4 ++ (x1 ++ # P :: x0) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: x ++ Γ6 ++ x1 ++ # P :: x0 ++ Γ4 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ6 ++ (x1 ++ # P :: x0) ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ A :: x ++ Γ6 ++ x1 ++ # P :: x0 ++ Γ4 ++ Γ7 = Γ0 ++ A :: (x ++ Γ6 ++ x1) ++ # P :: x0 ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A :: x ++ Γ6 ++ x1 ++ # P :: x0 ++ Γ4 ++ Γ7 = Γ0 ++ # P → A :: (x ++ Γ6 ++ x1) ++ # P :: x0 ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
       { destruct x1.
          - simpl in e1. destruct Γ5.
            * simpl in e1. destruct Γ6.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ A :: x ++ x0 ++ # P :: Γ2, C). repeat split ; auto. 2: left. apply list_exch_L_id.
                  assert (Γ0 ++ A :: x ++ x0 ++ # P :: Γ2 = Γ0 ++ A :: (x ++ x0) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ # P → A :: x ++ x0 ++ # P :: Γ2 = Γ0 ++ # P → A :: (x ++ x0) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
                  exists (Γ0 ++ A :: x ++ # P :: Γ6 ++ x0 ++ Γ7, C). repeat split ; auto. 2: left.
                  assert (Γ0 ++ A :: x ++ x0 ++ # P :: Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ x0 ++ [] ++ (# P :: Γ6) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ0 ++ A :: x ++ # P :: Γ6 ++ x0 ++ Γ7 = (Γ0 ++ A :: x) ++ (# P :: Γ6) ++ [] ++ x0 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  apply AtomImpL2Rule_I.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ x0 ++ Γ7, C) . repeat split ; auto. 2: left.
              assert (Γ0 ++ A :: x ++ x0 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ x0 ++ (# P :: Γ5) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ x0 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ6 ++ (# P :: Γ5) ++ x0 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ x0 ++ Γ7 = Γ0 ++ A :: (x ++ Γ6) ++ # P :: Γ5 ++ x0 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ # P → A :: x ++ Γ6 ++ # P :: Γ5 ++ x0 ++ Γ7 = Γ0 ++ # P → A :: (x ++ Γ6) ++ # P :: Γ5 ++ x0 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl.
            exists (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ x0 ++ # P :: x1 ++ Γ7, C). repeat split ; auto. 2: left.
            assert (Γ0 ++ A :: x ++ x0 ++ # P :: x1 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A :: x) ++ (x0 ++ # P :: x1) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ x0 ++ # P :: x1 ++ Γ7 = (Γ0 ++ A :: x) ++ Γ6 ++ Γ5 ++ (x0 ++ # P :: x1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ x0 ++ # P :: x1 ++ Γ7 = Γ0 ++ A :: (x ++ Γ6 ++ Γ5 ++ x0) ++ # P :: x1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ # P → A :: x ++ Γ6 ++ Γ5 ++ x0 ++ # P :: x1 ++ Γ7 = Γ0 ++ # P → A :: (x ++ Γ6 ++ Γ5 ++ x0) ++ # P :: x1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  * destruct Γ5.
      + simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ3 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2, C). repeat rewrite <- app_assoc in RA. split ;auto.
           repeat rewrite <- app_assoc. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ3 ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (A :: Γ1) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ [] ++ Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ # P → A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ Γ4) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply AtomImpL2Rule_I.
          - destruct x.
            + simpl in e1. subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C). repeat rewrite <- app_assoc. repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (A :: Γ1) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ [] ++ Γ4 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P → A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            + inversion e1. subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7, C). repeat rewrite <- app_assoc. repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ A :: Γ1 ++ # P :: x ++ Γ7 = Γ3 ++ Γ4 ++ [] ++ (A :: Γ1 ++ # P :: x) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7 = Γ3 ++ (A :: Γ1 ++ # P :: x) ++ [] ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL2Rule_I.
          - exists (Γ3 ++ A :: Γ6 ++ Γ4 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ A :: (Γ6 ++ x) ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (A :: Γ6) ++ x ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ A :: Γ6 ++ Γ4 ++ x ++ # P :: Γ2 = Γ3 ++ (A :: Γ6) ++ [] ++ Γ4 ++ x ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ A :: Γ6 ++ Γ4 ++ x ++ # P :: Γ2 = Γ3 ++ A :: (Γ6 ++ Γ4 ++ x) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ # P → A :: Γ6 ++ Γ4 ++ x ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ6 ++ Γ4 ++ x) ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
      + simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { destruct Γ6.
            - simpl in e1. subst. simpl. exists (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
              assert ((Γ3 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (A :: Γ1) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ [] ++ Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++# P → A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            - inversion e1. subst. simpl. exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ4 ++ Γ7, C).  repeat split. 2: right.
              assert ((Γ3 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (A :: Γ1) ++ (# P :: Γ6) ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ ( A :: Γ1) ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              apply AtomImpL1Rule_I. }
        { destruct x.
            - simpl in e1. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (A :: Γ1) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ [] ++ Γ4 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P → A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ4 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (A :: Γ1) ++ (# P :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ (A :: Γ1) ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                apply AtomImpL1Rule_I.
            - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7, C).  repeat split. 2: left.
              assert (Γ3 ++ Γ4 ++ A :: Γ1 ++ # P :: x ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (A :: Γ1 ++ # P :: x) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (A :: Γ1 ++ # P :: x) ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ Γ6 ++ # P → A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ # P → A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ Γ4) ++ # P :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ A :: (Γ5 ++ Γ6) ++ # P :: Γ2 = Γ3 ++ Γ4 ++ (A :: Γ5) ++ Γ6 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ Γ4) ++ # P :: Γ2 = Γ3 ++ Γ6 ++ (A :: Γ5) ++ Γ4 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ Γ6 ++ (# P → A :: Γ5) ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ Γ6) ++ # P → A :: (Γ5 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL2Rule_I.
          - exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2, C). repeat split. 2: left.
            assert ((Γ3 ++ Γ4) ++ A :: (Γ5 ++ Γ6 ++ x1) ++ # P :: Γ2 = Γ3 ++ Γ4 ++ (A :: Γ5) ++ Γ6 ++ x1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2 = Γ3 ++ Γ6 ++ (A :: Γ5) ++ Γ4 ++ x1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ Γ6 ++ (# P → A :: Γ5) ++ Γ4 ++ x1 ++ # P :: Γ2 = (Γ3 ++ Γ6) ++ # P → A :: (Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL2Rule_I.
          - destruct x1.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ x ++ A :: Γ5 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ A :: Γ5 ++ x ++ # P :: Γ2 = Γ3 ++ Γ4 ++ (A :: Γ5) ++ x ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ A :: Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ x ++ (A :: Γ5) ++ Γ4 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ x ++ A :: Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x) ++ A :: (Γ5 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ # P → A :: Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x) ++ # P → A :: (Γ5 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ x ++ # P :: x1 ++ A :: Γ5 ++ Γ4 ++ Γ7, C).  repeat split. 2: right.
                assert (Γ3 ++ Γ4 ++ A :: Γ5 ++ x ++ # P :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ (A :: Γ5) ++ (x ++ # P :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ # P :: x1 ++ A :: Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (x ++ # P :: x1) ++ (A :: Γ5) ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ x ++ # P :: x1 ++ A :: Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ # P :: x1 ++ A :: Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ x ++ # P :: x1 ++ # P → A :: Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ # P :: x1 ++ # P → A :: Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL1Rule_I. }
  * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      + simpl in e0. simpl. destruct Γ6.
        {  simpl in e0. subst. simpl. exists (Γ3 ++ Γ5 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2, C).  repeat split. 2: left.
            assert ((Γ3 ++ Γ4 ++ Γ5) ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ Γ5 ++ A :: Γ1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ Γ5 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ5 ++ [] ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ3 ++ Γ5 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2 = (Γ3 ++ Γ5 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ3 ++ Γ5 ++ Γ4 ++ # P → A :: Γ1 ++ # P :: Γ2 = (Γ3 ++ Γ5 ++ Γ4) ++ # P → A :: Γ1 ++ # P :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
         { inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - simpl. exists (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
              assert ((Γ3 ++ Γ4 ++ Γ5) ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (A :: Γ1) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ Γ5 ++ Γ4 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P → A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A ::(Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
            - destruct x0.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ Γ5 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (A :: Γ1) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ Γ5 ++ Γ4 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P → A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A ::(Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ A :: Γ1 ++ # P :: x0 ++ Γ5 ++ Γ4 ++ Γ7, C).  repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ Γ5 ++ A :: Γ1 ++ # P :: x0 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (A :: Γ1 ++ # P :: x0) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ1 ++ # P :: x0 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (A :: Γ1 ++ # P :: x0) ++ Γ5 ++ Γ4 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. apply AtomImpL2Rule_I.
            - simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ3 ++ A :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P :: Γ2, C).  repeat split. 2: left.
              assert (Γ3 ++ Γ4 ++ Γ5 ++ A :: Γ6 ++ x0 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (A :: Γ6) ++ x0 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ A :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P :: Γ2 = Γ3 ++ (A :: Γ6) ++ Γ5 ++ Γ4 ++ x0 ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ A :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P :: Γ2 = Γ3 ++ A :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ3 ++ # P → A :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ # P :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply AtomImpL2Rule_I. }
      + subst. apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2, C) . repeat split. 2: left. repeat rewrite <- app_assoc ; apply list_exch_LI.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ # P → A :: Γ1 ++  # P :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ # P → A :: Γ1 ++  # P :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H.
            apply AtomImpL2Rule_I. }
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ A :: Γ1 ++ # P :: Γ2, C). split. 2: left. repeat rewrite <- app_assoc ; apply list_exch_LI. 
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P → A :: Γ1 ++ # P :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ # P → A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply AtomImpL2Rule_I. }
          { destruct x0 ; simpl in e0 ; inversion e0 ; subst.
            - repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ x ++ Γ5 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. repeat rewrite <- app_assoc ; apply list_exch_LI.
              assert (Γ3 ++ x ++ Γ5 ++ Γ4 ++ # P → A :: Γ1 ++# P ::  Γ2 = (Γ3 ++ x ++ Γ5 ++ Γ4) ++ # P → A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H0. left. apply AtomImpL2Rule_I.
            - apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
              + exists((Γ3 ++ x) ++ A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2, C). repeat split.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A :: Γ1) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2 = Γ3 ++ (x ++ A :: Γ1) ++ Γ5 ++ Γ4 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
                  assert (Γ3 ++ (x ++ # P → A :: Γ1) ++ Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x) ++ # P → A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. left. apply AtomImpL2Rule_I.
              + destruct x1.
                 *  simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                    exists (Γ3 ++ x ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ Γ4 ++ Γ5 ++ x ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++( x ++ A :: Γ1) ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ x ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = Γ3 ++(x ++ A :: Γ1) ++ Γ5 ++ Γ4 ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
                    assert (Γ3 ++ x ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x) ++ A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                    rewrite H.
                    assert (Γ3 ++ x ++ # P → A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x) ++ # P → A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                    rewrite H0. apply AtomImpL2Rule_I.
                 *  inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                    exists (Γ3 ++ x ++ A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split. 2: left.
                    assert (Γ3 ++ Γ4 ++ Γ5 ++ x ++ A :: Γ1 ++ # P :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A :: Γ1 ++ # P :: x1) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (x ++ A :: Γ1 ++ # P :: x1) ++ Γ5 ++ Γ4 ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
                    assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
                    rewrite H.
                    assert (Γ3 ++ x ++ # P → A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ # P → A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
                    rewrite H0. apply AtomImpL2Rule_I.
              + repeat rewrite <- app_assoc. simpl.
                  exists (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2, C). repeat split. 2: left.
                  assert (Γ3 ++ Γ4 ++ Γ5 ++ x ++ A :: x0 ++ x1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A :: x0) ++ x1 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2 = Γ3 ++ (x ++ A :: x0) ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2 = (Γ3 ++ x) ++ A :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H.
                  assert (Γ3 ++ x ++ # P → A :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2 = (Γ3 ++ x) ++ # P → A :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H0. apply AtomImpL2Rule_I. }
      + destruct x ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in e0. subst. simpl in H0. simpl. repeat rewrite <- app_assoc. simpl.
               exists ((Γ3 ++ x0 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ x0 ++ A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert ((Γ3 ++ x0 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ x0 ++ [] ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H1. apply list_exch_LI.
               assert (Γ3 ++ x0 ++ Γ4 ++ # P → A :: Γ1 ++ # P :: Γ2 = (Γ3 ++ x0 ++ Γ4) ++ # P → A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H. apply AtomImpL2Rule_I.
            - simpl in e0. inversion e0. clear H0. subst. simpl. repeat rewrite <- app_assoc. simpl.
              apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
              + exists (Γ3 ++ A :: (Γ1 ++ x0 ++ Γ4) ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (A :: Γ1) ++ (# P :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H.
                assert (Γ3 ++ A :: (Γ1 ++ x0 ++ Γ4) ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ x0 ++ Γ4 ++ (# P :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P → A :: Γ1 ++ x0 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ x0 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H. apply AtomImpL2Rule_I.
              + destruct x.
                 * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl.
                    exists (Γ3 ++ A :: Γ1 ++ x0 ++ Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (A :: Γ1) ++ # P :: Γ2). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H.
                    assert (Γ3 ++ A :: Γ1 ++ x0 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ x0 ++ Γ4 ++ # P :: Γ2). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                    assert (Γ3 ++ A :: Γ1 ++ x0 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ x0 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                    rewrite H.
                    assert (Γ3 ++ # P → A :: Γ1 ++ x0 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ x0 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                    rewrite H0. apply AtomImpL2Rule_I.
                 * inversion e1. subst. repeat rewrite <- app_assoc. simpl.
                    exists (Γ3 ++ A :: Γ1 ++ # P :: x ++ x0 ++ Γ4 ++ Γ7, C). repeat split. 2: left. 2: apply AtomImpL2Rule_I.
                    assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: x ++ Γ7 = Γ3 ++ Γ4 ++ x0 ++ (A :: Γ1 ++ # P :: x) ++ Γ7). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H.
                    assert (Γ3 ++ A :: Γ1 ++ # P :: x ++ x0 ++ Γ4 ++ Γ7 = Γ3 ++ (A :: Γ1 ++ # P :: x) ++ x0 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
              + exists (Γ3 ++ A :: Γ6 ++ x0 ++ Γ4 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A :: (Γ6 ++ x) ++ # P :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (A :: Γ6) ++ x ++ # P :: Γ2).
                repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
                assert (Γ3 ++ A :: Γ6 ++ x0 ++ Γ4 ++ x ++ # P :: Γ2 = Γ3 ++ (A :: Γ6) ++ x0 ++ Γ4 ++ x ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ A :: Γ6 ++ x0 ++ Γ4 ++ x ++ # P :: Γ2 = Γ3 ++ A :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H.
                assert (Γ3 ++ # P → A :: Γ6 ++ x0 ++ Γ4 ++ x ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply AtomImpL2Rule_I. }
        { apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - destruct Γ6.
             * repeat rewrite <- app_assoc ; simpl. simpl in e1. subst.
               exists (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (x0 ++ A :: Γ1) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (x0 ++ A :: Γ1) ++ [] ++ Γ4 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x0) ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert (Γ3 ++ x0 ++ # P → A :: Γ1 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x0) ++ # P → A :: (Γ1 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H0. apply AtomImpL2Rule_I.
             * repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
               exists (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
               assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++( x0 ++ A :: Γ1) ++ (# P :: Γ6) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ (x0 ++ A :: Γ1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ x0) ++ A :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert (Γ3 ++ # P :: Γ6 ++ x0 ++ # P → A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ x0) ++ # P → A :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
               rewrite H0. apply AtomImpL1Rule_I.
          - destruct x1.
             * simpl in e1. destruct Γ6.
                + repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. simpl in e1. subst.
                   exists (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
                   assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ [] ++ (x0 ++ A :: Γ1) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H.
                   assert (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = Γ3 ++ (x0 ++ A :: Γ1) ++ [] ++ Γ4 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                   assert (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x0) ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                   rewrite H.
                   assert (Γ3 ++ x0 ++ # P → A :: Γ1 ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x0) ++ # P → A :: (Γ1 ++ Γ4) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
                   rewrite H0. apply AtomImpL2Rule_I.
                + repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
                   exists (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
                   assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A :: Γ1) ++ (# P :: Γ6) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H.
                   assert (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ (x0 ++ A :: Γ1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                   repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                   assert (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ x0) ++ A :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
                   rewrite H.
                   assert (Γ3 ++ # P :: Γ6 ++ x0 ++ # P → A :: Γ1 ++ Γ4 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ x0) ++ # P → A :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
                   rewrite H0. apply AtomImpL1Rule_I.
             * repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
               exists (Γ3 ++ Γ6 ++ x0 ++ A :: Γ1 ++ # P :: x1 ++ Γ4 ++ Γ7, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ A :: Γ1 ++ # P :: x1 ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A :: Γ1 ++ # P :: x1) ++ Γ6 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ A :: Γ1 ++ # P :: x1 ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (x0 ++ A :: Γ1 ++ # P :: x1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ Γ6 ++ x0 ++ A :: Γ1 ++ # P :: x1 ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ A :: Γ1 ++ # P :: x1 ++ Γ4 ++ Γ7).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P → A :: Γ1 ++ # P :: x1 ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ # P → A :: Γ1 ++ # P :: x1 ++ Γ4 ++ Γ7).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL2Rule_I.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            + repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ A :: x ++ Γ6 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ A :: x) ++ Γ6 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2 = Γ3 ++ Γ6 ++ (x0 ++ A :: x) ++ Γ4 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ A :: (x ++ Γ4) ++ # P :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P → A :: x ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ # P → A :: (x ++ Γ4) ++ # P :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL2Rule_I.
            + repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ x2 ++ # P :: Γ2, C). split ;auto. 2: left.
               assert (Γ3 ++ Γ4 ++ x0 ++ A :: x ++ Γ6 ++ x2 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ A :: x) ++ Γ6 ++ x2 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ x2 ++ # P :: Γ2 = Γ3 ++ Γ6 ++ (x0 ++ A :: x) ++ Γ4 ++ x2 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
               assert (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ x2 ++ # P :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ A :: (x ++ Γ4 ++ x2) ++ # P :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
               assert (Γ3 ++ Γ6 ++ x0 ++ # P → A :: x ++ Γ4 ++ x2 ++ # P :: Γ2 = (Γ3 ++ Γ6 ++ x0) ++ # P → A :: (x ++ Γ4 ++ x2) ++ # P :: Γ2).
               repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL2Rule_I.
            + destruct x2.
              *  repeat rewrite <- app_assoc ; simpl. simpl in e1. subst.
                 exists (Γ3 ++ x1 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
                 assert (Γ3 ++ Γ4 ++ x0 ++ A :: x ++ x1 ++ # P :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ A :: x) ++ x1 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2 = Γ3 ++ x1 ++ (x0 ++ A :: x) ++ Γ4 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                 assert (Γ3 ++ x1 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x1 ++ x0) ++ A :: (x ++ Γ4) ++ # P :: Γ2).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ x0 ++ # P → A :: x ++ Γ4 ++ # P :: Γ2 = (Γ3 ++ x1 ++ x0) ++ # P → A :: (x ++ Γ4) ++ # P :: Γ2).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL2Rule_I.
              *  repeat rewrite <- app_assoc ; simpl. inversion e1. subst.
                 exists (Γ3 ++ x1 ++ # P :: x2 ++ x0 ++ A :: x ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
                 assert (Γ3 ++ Γ4 ++ x0 ++ A :: x ++ x1 ++ # P :: x2 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A :: x) ++ (x1 ++ # P :: x2) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ # P :: x2 ++ x0 ++ A :: x ++ Γ4 ++ Γ7 = Γ3 ++ (x1 ++ # P :: x2) ++ (x0 ++ A :: x) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                 repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
                 assert (Γ3 ++ x1 ++ # P :: x2 ++ x0 ++ A :: x ++ Γ4 ++ Γ7 = (Γ3 ++ x1) ++ # P :: (x2 ++ x0) ++ A :: x ++ Γ4 ++ Γ7).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
                 assert (Γ3 ++ x1 ++ # P :: x2 ++ x0 ++ # P → A :: x ++ Γ4 ++ Γ7 = (Γ3 ++ x1) ++ # P :: (x2 ++ x0) ++ # P → A :: x ++ Γ4 ++ Γ7).
                 repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL1Rule_I. }
  * destruct x0 ; simpl in e0 ; inversion e0 ; subst.
      + destruct Γ5 ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in H1. subst. repeat rewrite <- app_assoc. simpl.
              exists ((Γ3 ++ x) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left. repeat rewrite <- app_assoc. apply list_exch_L_id.
              assert (Γ3 ++ x ++ # P → A :: Γ1 ++ # P :: Γ2 = (Γ3 ++ x) ++ # P → A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL2Rule_I.
            - simpl in H1. inversion H1. subst. apply app2_find_hole in H3. destruct H3. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ x ++ (A :: Γ1) ++ [] ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ [] ++ (A :: Γ1) ++ x ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
                assert (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ x) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P → A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ x) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply AtomImpL2Rule_I.
              * destruct x0.
               + simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                  assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ x ++ (A :: Γ1) ++ [] ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ [] ++ (A :: Γ1) ++ x ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
                  assert (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ x) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ # P → A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ x) ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply AtomImpL2Rule_I.
               + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                  exists (Γ3 ++ A :: Γ1 ++ # P :: x0 ++ x ++ Γ7, C). repeat split. 2: left.
                  assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: x0 ++ Γ7 = Γ3 ++ x ++ [] ++ (A :: Γ1 ++ # P :: x0) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ A :: Γ1 ++ # P :: x0 ++ x ++ Γ7 = Γ3 ++ (A :: Γ1 ++ # P :: x0) ++ [] ++ x ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply list_exch_LI.
                  apply AtomImpL2Rule_I.
              * repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
                exists (Γ3 ++ A :: (Γ6 ++ x ++ x0) ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: Γ6 ++ x0 ++ # P :: Γ2 = Γ3 ++ x ++ (A :: Γ6) ++ [] ++ x0 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: (Γ6 ++ x ++ x0) ++ # P :: Γ2 = Γ3 ++ [] ++ (A :: Γ6) ++ x ++ x0 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply list_exch_LI.
                assert (Γ3 ++ # P → A :: Γ6 ++ x ++ x0 ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ6 ++ x ++ x0) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I. }
          { apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
            - destruct Γ6.
              * simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ x ++ [] ++ (A :: Γ1) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ [] ++ x ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                assert (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ A :: (Γ1 ++ x) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P → A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ x) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H1. apply AtomImpL2Rule_I.
              * inversion e1 ; subst. repeat rewrite <- app_assoc. simpl.
                exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ x ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ x ++ (A :: Γ1) ++ (# P :: Γ6) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ x ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ (A :: Γ1) ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                apply AtomImpL1Rule_I.
            - destruct x0.
              * simpl in e1. destruct Γ6.
                + simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                    exists (Γ3 ++ A :: (Γ1 ++ x) ++ # P :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ2 = Γ3 ++ x ++ [] ++ (A :: Γ1) ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ A :: (Γ1 ++ x) ++ # P :: Γ2 = Γ3 ++ (A :: Γ1) ++ [] ++ x ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    assert (Γ3 ++ # P → A :: Γ1 ++ x ++ # P :: Γ2 = Γ3 ++ # P → A :: (Γ1 ++ x) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
                + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                    exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ x ++ Γ7, C). repeat split. 2: right.
                    assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ x ++ (A :: Γ1) ++ (# P :: Γ6) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ x ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ (A :: Γ1) ++ x ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    apply AtomImpL1Rule_I.
              * inversion e1. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                exists ((Γ3 ++ Γ6) ++ A :: Γ1 ++ # P :: x0 ++ x ++ Γ7, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: x0 ++ Γ6 ++ Γ7 = Γ3 ++ x ++ (A :: Γ1 ++ # P :: x0) ++ Γ6 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ A :: Γ1 ++ # P :: x0 ++ x ++ Γ7 = Γ3 ++ Γ6 ++ (A :: Γ1 ++ # P :: x0) ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P → A :: Γ1 ++ # P :: x0 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ # P → A :: Γ1 ++ # P :: x0 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
            - repeat rewrite <- app_assoc. simpl. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x) ++  # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: Γ5 ++ Γ6 ++ # P :: Γ2 = Γ3 ++ x ++ (A :: Γ5) ++ Γ6 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x) ++ # P :: Γ2 = Γ3 ++ Γ6 ++ (A :: Γ5) ++ x ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P → A :: Γ5 ++ x ++ # P :: Γ2 = (Γ3 ++ Γ6) ++ # P → A :: (Γ5 ++ x) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
              * exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x ++ x1) ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: Γ5 ++ (Γ6 ++ x1) ++ # P :: Γ2 = Γ3 ++ x ++ (A :: Γ5) ++ Γ6 ++ x1 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x ++ x1) ++ # P :: Γ2 = Γ3 ++ Γ6 ++ (A :: Γ5) ++ x ++ x1 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P → A :: Γ5 ++ x ++ x1 ++ # P :: Γ2 = (Γ3 ++ Γ6) ++ # P → A :: (Γ5 ++ x ++ x1) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
              * destruct x1.
                + simpl in e1. subst. repeat rewrite <- app_assoc. simpl.
                    exists ((Γ3 ++ x0) ++ A :: (Γ5 ++ x) ++ # P :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ x ++ A :: Γ5 ++ x0 ++ # P :: Γ2 = Γ3 ++ x ++ (A :: Γ5) ++ x0 ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x0) ++ A :: (Γ5 ++ x) ++ # P :: Γ2 = Γ3 ++ x0 ++ (A :: Γ5) ++ x ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    assert (Γ3 ++ x0 ++ # P → A :: Γ5 ++ x ++ # P :: Γ2 = (Γ3 ++ x0) ++ # P → A :: (Γ5 ++ x) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
                + inversion e1. subst. repeat rewrite <- app_assoc. simpl.
                    exists ((Γ3 ++ x0) ++ # P :: x1 ++ A :: Γ5 ++ x ++ Γ7, C). repeat split. 2: right.
                    assert (Γ3 ++ x ++ A :: Γ5 ++ x0 ++ # P :: x1 ++ Γ7 = Γ3 ++ x ++( A :: Γ5) ++ (x0 ++ # P :: x1) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x0) ++ # P :: x1 ++ A :: Γ5 ++ x ++ Γ7 = Γ3 ++ (x0 ++ # P :: x1) ++ (A :: Γ5) ++ x ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
                    assert (Γ3 ++ x0 ++ # P :: x1 ++ # P → A :: Γ5 ++ x ++ Γ7 = (Γ3 ++ x0) ++ # P :: x1 ++ # P → A :: Γ5 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I. }
      + apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        {  destruct Γ5.
            - simpl in e1. destruct Γ6.
              * simpl in e1.  subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ x) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left.
                repeat rewrite <- app_assoc. apply list_exch_L_id.
                assert (Γ3 ++ x ++ # P → A :: Γ1 ++ # P :: Γ2 = (Γ3 ++ x) ++ # P → A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL2Rule_I.
              * inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ3 ++ # P :: (Γ6 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert (Γ3 ++ # P :: (Γ6 ++ x) ++ A :: Γ1 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ [] ++ (x ++ A :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ6 ++ x ++ # P → A :: Γ1 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ x) ++ # P → A :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL1Rule_I.
            - inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl.
              exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
              assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: Γ1) ++ (# P :: Γ5 )++ Γ6 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H.
              assert ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ A :: Γ1 ++ Γ7 = Γ3 ++ Γ6 ++ (# P :: Γ5) ++ (x ++ A :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ # P :: Γ5 ++ x ++ # P → A :: Γ1 ++ Γ7 = (Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ # P → A :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL1Rule_I. }
        { destruct x1.
            - simpl in e1. destruct Γ5.
              + simpl in e1. destruct Γ6.
                { simpl in e1.  subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists ((Γ3 ++ x) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left.
                  repeat rewrite <- app_assoc. apply list_exch_L_id.
                  assert (Γ3 ++ x ++ # P → A :: Γ1 ++ # P :: Γ2 = (Γ3 ++ x) ++ # P → A :: Γ1 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply AtomImpL2Rule_I. }
                { inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists (Γ3 ++ # P :: (Γ6 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                  assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: Γ1) ++ [] ++ (# P :: Γ6) ++ Γ7). repeat rewrite <- app_assoc. auto.
                  rewrite H.
                  assert (Γ3 ++ # P :: (Γ6 ++ x) ++ A :: Γ1 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ [] ++ (x ++ A :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
                  rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ # P :: Γ6 ++ x ++ # P → A :: Γ1 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ x) ++ # P → A :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply AtomImpL1Rule_I. }
              + inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: Γ1) ++ (# P :: Γ5 )++ Γ6 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ A :: Γ1 ++ Γ7 = Γ3 ++ Γ6 ++ (# P :: Γ5) ++ (x ++ A :: Γ1) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ # P :: Γ5 ++ x ++ # P → A :: Γ1 ++ Γ7 = (Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ # P → A :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL1Rule_I.
            - inversion e1 ; subst ; simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
              exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: Γ1 ++ # P :: x1 ++ Γ7, C). repeat split. 2: left.
              assert (Γ3 ++ x ++ A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: Γ1 ++ # P :: x1) ++ Γ5 ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: Γ1 ++ # P :: x1 ++ Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A :: Γ1 ++ # P :: x1) ++ Γ7). repeat rewrite <- app_assoc. auto.
              repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ Γ5 ++ x ++ # P → A :: Γ1 ++ # P :: x1 ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P → A :: Γ1 ++ # P :: x1 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply AtomImpL2Rule_I. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - destruct Γ6.
              * simpl in e1; subst. simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ # P :: Γ2 = Γ3 ++ (x ++ A :: x0) ++ [] ++ Γ5 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert ((Γ3 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2 = Γ3 ++ Γ5 ++ [] ++ (x ++ A :: x0) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ5 ++ x ++ # P → A :: x0 ++ # P :: Γ2 = (Γ3 ++ Γ5 ++ x) ++ # P → A :: x0 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL2Rule_I.
              * inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                exists (Γ3 ++ # P :: (Γ6 ++ Γ5 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: x0) ++ Γ5 ++ (# P :: Γ6) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H.
                assert (Γ3 ++ # P :: (Γ6 ++ Γ5 ++ x) ++ A :: x0 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ Γ5 ++ (x ++ A :: x0) ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ # P :: Γ6 ++ Γ5 ++ x ++ # P → A :: x0 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ Γ5 ++ x) ++ # P → A :: x0 ++ Γ7). repeat rewrite <- app_assoc. auto.
                rewrite H. apply AtomImpL1Rule_I.
            - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                assert (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ Γ6 ++ # P :: Γ2 = Γ3 ++ (x ++ A :: x0) ++ Γ5 ++ Γ6 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A :: x0) ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ x ++ # P → A :: x0 ++ # P :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P → A :: x0 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
              * exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: (x0 ++ x1) ++ # P :: Γ2, C). repeat split. 2: left.
                assert ((Γ3 ++ x) ++ A :: (x0 ++ Γ5 ++ Γ6 ++ x1) ++ # P :: Γ2 = Γ3 ++ (x ++ A :: x0) ++ Γ5 ++ Γ6 ++ x1 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: (x0 ++ x1) ++ # P :: Γ2 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A :: x0) ++ x1 ++ # P :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ # P → A :: x0) ++ x1 ++ # P :: Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ # P → A :: (x0 ++ x1) ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
              * repeat rewrite <- app_assoc ; simpl. destruct x1.
                + simpl in e1. subst. simpl. exists ((Γ3 ++ x2 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                    assert (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ x2 ++ # P :: Γ2 = Γ3 ++ (x ++ A :: x0) ++ Γ5 ++ x2 ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x2 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2 = Γ3 ++ x2 ++ Γ5 ++ (x ++ A :: x0) ++ # P :: Γ2).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                    assert (Γ3 ++ x2 ++ Γ5 ++ x ++ # P → A :: x0 ++ # P :: Γ2 = (Γ3 ++ x2 ++ Γ5 ++ x) ++ # P → A :: x0 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
                + inversion e1 ; subst. simpl. exists ((Γ3 ++ x2) ++ # P :: (x1 ++ Γ5 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                    assert (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ x2 ++ # P :: x1 ++ Γ7 = Γ3 ++ (x ++ A :: x0) ++ Γ5 ++ (x2 ++ # P :: x1) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                    assert ((Γ3 ++ x2) ++ # P :: (x1 ++ Γ5 ++ x) ++ A :: x0 ++ Γ7 = Γ3 ++ (x2 ++ # P :: x1) ++ Γ5 ++ (x ++ A :: x0) ++ Γ7).
                    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                    assert (Γ3 ++ x2 ++ # P :: x1 ++ Γ5 ++ x ++ # P → A :: x0 ++ Γ7 = (Γ3 ++ x2) ++ # P :: (x1 ++ Γ5 ++ x) ++ # P → A :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                    repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
            - destruct x2.
              * simpl in e1. destruct Γ6.
               + simpl in e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists ((Γ3 ++ x1 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                  assert (Γ3 ++ x ++ A :: x0 ++ x1 ++ # P :: Γ2 = Γ3 ++ [] ++ (x ++ A :: x0) ++ x1 ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x1 ++ x) ++ A :: x0 ++ # P :: Γ2 = Γ3 ++ x1 ++ (x ++ A :: x0) ++ [] ++ # P :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ x1 ++ x ++ # P → A :: x0 ++ # P :: Γ2 = (Γ3 ++ x1 ++ x) ++ # P → A :: x0 ++ # P :: Γ2). repeat rewrite <- app_assoc ; simpl.
                  repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL2Rule_I.
               + inversion e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists (Γ3 ++ # P :: (Γ6 ++ x1 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                  assert (Γ3 ++ x ++ A :: x0 ++ x1 ++ # P :: Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: x0) ++ x1 ++ (# P :: Γ6) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert (Γ3 ++ # P :: (Γ6 ++ x1 ++ x) ++ A :: x0 ++ Γ7 = Γ3 ++ (# P :: Γ6) ++ x1 ++ (x ++ A :: x0) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                  assert (Γ3 ++ # P :: Γ6 ++ x1 ++ x ++ # P → A :: x0 ++ Γ7 = Γ3 ++ # P :: (Γ6 ++ x1 ++ x) ++ # P → A :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                  repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I.
              * inversion e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl.
                exists ((Γ3 ++ Γ6 ++ x1) ++ # P :: (x2 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                assert (Γ3 ++ x ++ A :: x0 ++ x1 ++ # P :: x2 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A :: x0) ++ (x1 ++ # P :: x2) ++ Γ6 ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ x1) ++ # P :: (x2 ++ x) ++ A :: x0 ++ Γ7 = Γ3 ++ Γ6 ++ (x1 ++ # P :: x2) ++ (x ++ A :: x0) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
                assert (Γ3 ++ Γ6 ++ x1 ++ # P :: x2 ++ x ++ # P → A :: x0 ++ Γ7 = (Γ3 ++ Γ6 ++ x1) ++ # P :: (x2 ++ x) ++ # P → A :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply AtomImpL1Rule_I. }
Qed.

Lemma AndImpL_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (AndImpLRule [ps] s) ->
   (existsT2 pse, (AndImpLRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A → B → C :: Γ1, D). repeat split. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ A → B → C :: Γ5 ++ Γ6, D). repeat split. apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6, D). repeat split.
        assert (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ A → B → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ ((A ∧ B) → C :: Γ4) ++ Γ6 = (Γ0 ++ Γ5) ++ (A ∧ B) → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply AndImpLRule_I.
        assert (Γ0 ++ A → B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (A → B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (A → B → C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6, D). repeat split.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ A → B → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ ((A ∧ B) → C :: Γ3) ++ Γ6 =( Γ0 ++ Γ5 ++ Γ4) ++ (A ∧ B) → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply AndImpLRule_I.
      assert (Γ0 ++ A → B → C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (A → B → C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (A → B → C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ A → B → C :: Γ1, D). repeat split. rewrite <- app_assoc. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6, D). repeat split.
          assert (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ A → B → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ (A ∧ B) → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ (A ∧ B) → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply AndImpLRule_I.
          assert (Γ0 ++ A → B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (A → B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (A → B → C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6, D). repeat split.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ A → B → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ (A ∧ B) → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ (A ∧ B) → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply AndImpLRule_I.
        assert (Γ0 ++ A → B → C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (A → B → C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (A → B → C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ A → B → C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat rewrite <- app_assoc. repeat split.
      assert (Γ0 ++ A → B → C :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ A → B → C :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ A → B → C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ A → B → C :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ A → B → C :: Γ1, D). repeat split. 2: apply list_exch_L_id. rewrite app_assoc.
           apply AndImpLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ Γ3 ++ Γ6, D). repeat split.
           assert ((Γ2 ++ Γ3) ++ A → B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (A → B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ A → B → C :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (A → B → C :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ A → B → C :: Γ4 ++ Γ3 ++ Γ6, D). repeat split.
        assert (Γ2 ++ Γ5 ++ ((A ∧ B) → C :: Γ4) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ (A ∧ B) → C :: Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        apply AndImpLRule_I.
        assert ((Γ2 ++ Γ3) ++ A → B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (A → B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ A → B → C :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (A → B → C :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ A → B → C :: Γ1, D). repeat split.
           assert (Γ2 ++ Γ4 ++ Γ3 ++ (A ∧ B) → C :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ (A ∧ B) → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           apply AndImpLRule_I.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ A → B → C :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ A → B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ A → B → C :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ A → B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ A → B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (A → B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ A → B → C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (A → B → C :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A → B → C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply AndImpLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A → B → C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply AndImpLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A → B → C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply AndImpLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ A → B → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
              assert (Γ2 ++ x ++ (A ∧ B) → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ (A ∧ B) → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              apply AndImpLRule_I.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ A → B → C :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ A → B → C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ A → B → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ A → B → C :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ A → B → C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply AndImpLRule_I.
              assert (Γ2 ++ Γ3 ++ x0 ++ A → B → C :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ A → B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ A → B → C :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ A → B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ x0 ++ Γ3 ++ Γ6, D). repeat split.
              assert (Γ2 ++ Γ3 ++ x0 ++ A → B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (A → B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ A → B → C :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (A → B → C :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ A → B → C :: x ++ Γ3 ++ Γ6, D). split.
           assert (Γ2 ++ Γ5 ++ (x0 ++ (A ∧ B) → C :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ (A ∧ B) → C :: x ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           apply AndImpLRule_I.
           assert ((Γ2 ++ Γ3 ++ x0) ++ A → B → C :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ A → B → C :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ A → B → C :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ A → B → C :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ A → B → C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply AndImpLRule_I. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ x ++ Γ6, D). repeat split.
              assert (Γ2 ++ x ++ A → B → C :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (A → B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ A → B → C :: Γ5 ++ x ++ Γ6 = Γ2 ++( A → B → C :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ A → B → C :: Γ4 ++ x ++ Γ6, D). repeat split.
          assert (Γ2 ++ Γ5 ++ (A ∧ B) → C :: Γ4 ++ x ++ Γ6 = (Γ2 ++ Γ5) ++ (A ∧ B) → C :: Γ4 ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply AndImpLRule_I.
          assert (Γ2 ++ x ++ A → B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (A → B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ A → B → C :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (A → B → C :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A → B → C :: x0 ++ Γ6, D). repeat split.
          assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ (A ∧ B) → C :: x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ (A ∧ B) → C :: x0 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply AndImpLRule_I.
          assert (Γ2 ++ x ++ A → B → C :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ A → B → C :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A → B → C :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A → B → C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
Qed.

Lemma OrImpL_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (OrImpLRule [ps] s) ->
   (existsT2 pse, (OrImpLRule [pse] se) *
   ((@list_exch_L ps pse) + (existsT2 pse1, (@list_exch_L ps pse1) * (@list_exch_L pse1 pse)))).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ4.
  + simpl in e0. subst. simpl. destruct Γ5.
      * simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto. left. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ A → C :: Γ6 ++ B → C :: Γ7, D). repeat split. left. apply list_exch_L_id.
          - exists (Γ0 ++ A → C :: (Γ6 ++ x0) ++ B → C :: Γ2, D). repeat split. 2: left. 2: apply list_exch_L_id.
            assert (Γ0 ++ (A ∨ B) → C :: Γ6 ++ x0 ++ Γ2 =Γ0 ++ (A ∨ B) → C :: (Γ6 ++ x0) ++ Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I.
          - exists (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7, D). repeat split. 2: left. 2: apply list_exch_L_id. repeat rewrite <- app_assoc.
            apply OrImpLRule_I. }
      * simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { exists (Γ0 ++ Γ6 ++ (A→ C :: Γ5) ++ B→ C :: Γ7, D) . repeat split. 2: left.
          assert (Γ0 ++ Γ6 ++ (A → C :: Γ5) ++ B → C :: Γ7 = (Γ0 ++ Γ6) ++ A → C :: Γ5 ++ B → C :: Γ7). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ Γ7 = (Γ0 ++ Γ6) ++ (A ∨ B) → C :: Γ5 ++ Γ7). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply OrImpLRule_I.
          assert (Γ0 ++ A → C :: Γ5 ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ [] ++ (A → C :: Γ5 ++ [B → C]) ++ Γ6 ++ Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ6 ++ (A → C :: Γ5) ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ (A → C :: Γ5 ++ [B → C]) ++ [] ++ Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ0 ++ Γ6) ++ A→ C :: Γ5 ++ B→ C :: Γ7, D). split. 2: left. 
            assert (Γ0 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ Γ7 = (Γ0 ++ Γ6) ++ (A ∨ B) → C :: Γ5 ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. assert (Γ0 ++ A → C :: (Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ0 ++ [] ++ (A → C :: Γ5) ++ Γ6 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H. assert ((Γ0 ++ Γ6) ++ A → C :: Γ5 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ (A → C :: Γ5) ++ [] ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ0 ++ Γ6) ++ A → C :: (Γ5 ++ x1) ++ B → C :: Γ2, D). split. 2: left.
            assert (Γ0 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ x1 ++ Γ2 = (Γ0 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ x1) ++ Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. assert (Γ0 ++ A → C :: (Γ5 ++ Γ6 ++ x1) ++ B → C :: Γ2 = Γ0 ++ [] ++ (A → C :: Γ5) ++ Γ6 ++ x1 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H. assert ((Γ0 ++ Γ6) ++ A → C :: (Γ5 ++ x1) ++ B → C :: Γ2 = Γ0 ++ Γ6 ++ (A → C :: Γ5) ++ [] ++ x1 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ0 ++ x0 ++ x1) ++ A → C :: Γ5 ++ B → C :: Γ7, D). repeat split. 2: right.
            assert (Γ0 ++ (x0 ++ x1) ++ ((A ∨ B) → C :: Γ5) ++ Γ7 = (Γ0 ++ x0 ++ x1) ++ (A ∨ B) → C :: Γ5 ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. exists (Γ0 ++ x1++ A → C :: (Γ5 ++ x0) ++ B → C :: Γ7, D). repeat split.
            assert (Γ0 ++ A → C :: (Γ5 ++ x0) ++ B → C :: x1 ++ Γ7 = Γ0 ++ [] ++ (A → C :: Γ5 ++ x0 ++ [B → C]) ++ x1 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert (Γ0 ++ x1 ++ A → C :: (Γ5 ++ x0) ++ B → C :: Γ7 = Γ0 ++ x1 ++ (A → C :: Γ5 ++ x0 ++ [B → C]) ++ [] ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            assert (Γ0 ++ x1 ++ A → C :: (Γ5 ++ x0) ++ B → C :: Γ7 = Γ0 ++ [] ++ (x1 ++ A → C :: Γ5) ++ x0 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ x0 ++ x1) ++ A → C :: Γ5 ++ B → C :: Γ7 = Γ0 ++ x0 ++ (x1 ++ A → C :: Γ5) ++ [] ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
        {  exists ((Γ0 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7, D). repeat split. 2: left.
            assert (Γ0 ++ Γ6 ++ ((A ∨ B) → C :: Γ1 ++ x0) ++ Γ7 = (Γ0 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++ x0 ++ Γ7). repeat rewrite <- app_assoc. auto.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I.
            assert (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ7 = Γ0 ++ [] ++ (A → C :: Γ1 ++ B → C :: x0) ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7 = Γ0 ++ Γ6 ++ (A → C :: Γ1 ++ B → C :: x0) ++ [] ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
  + inversion e0. subst. symmetry in H1. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
     * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ7, D). repeat split. 2: right.
        assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ1) ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
        rewrite H. apply OrImpLRule_I. exists (Γ0 ++ Γ5 ++  A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7, D). repeat split.
        assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ [] ++ (A → C :: Γ1 ++ [B → C]) ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ Γ5 ++ (A → C :: Γ1 ++ [B → C]) ++ [] ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
        assert (Γ0 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ [] ++ (Γ5 ++ A → C :: Γ1 ++ [B → C]) ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ (Γ5 ++ A → C :: Γ1 ++ [B → C]) ++ [] ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
     * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7, D). repeat split.
        assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ1 ++ x0) ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: Γ1 ++ x0 ++ Γ7). repeat rewrite <- app_assoc. auto.
        simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. right.
        exists (Γ0 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ7, D). repeat split.
        assert (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ [] ++ (A → C :: Γ1 ++ B → C :: x0) ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ7 = Γ0 ++ Γ5 ++ (A → C :: Γ1 ++ B → C :: x0) ++ [] ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
        assert (Γ0 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ7 = Γ0 ++ [] ++ (Γ5 ++ A → C :: Γ1 ++ B → C :: x0) ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7 = Γ0 ++ Γ6 ++ (Γ5 ++ A → C :: Γ1 ++ B → C :: x0) ++ [] ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
     * symmetry in e1. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { exists ((Γ0 ++ Γ6 ++ x0) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split.
          assert (Γ0 ++ Γ6 ++ x0 ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. right.
          exists (Γ0 ++ x0 ++ A → C :: Γ4 ++ B → C :: Γ6 ++ Γ7, D). split.
          assert (Γ0 ++ A → C :: (Γ4 ++ x0) ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ (A → C :: Γ4) ++ x0 ++ [] ++ B → C :: Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ x0 ++ A → C :: Γ4 ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ [] ++ x0 ++ (A → C :: Γ4) ++ B → C :: Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ x0 ++ A → C :: Γ4 ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ [] ++ (x0 ++ A → C :: Γ4 ++ [B → C]) ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ0 ++ Γ6 ++ x0) ++ A → C :: Γ4 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ (x0 ++ A → C :: Γ4 ++ [B → C]) ++ [] ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
       { exists ((Γ0 ++ Γ6 ++ x0 ++ x1) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split.
          assert (Γ0 ++ Γ6 ++ (x0 ++ x1) ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ Γ6 ++ x0 ++ x1) ++ (A ∨ B) → C :: Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. right.
          exists (Γ0 ++ A → C :: Γ4 ++ B → C :: x0 ++ x1 ++ Γ6 ++ Γ7, D). split.
          assert (Γ0 ++ A → C :: (Γ4 ++ x0) ++ B → C :: x1 ++ Γ6 ++ Γ7 = (Γ0 ++ A → C :: Γ4) ++ x0 ++ [] ++ [B → C] ++ x1 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ A → C :: Γ4 ++ B → C :: x0 ++ x1 ++ Γ6 ++ Γ7 = (Γ0 ++ A → C :: Γ4) ++ [B → C] ++ [] ++ x0 ++ x1 ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          assert (Γ0 ++ A → C :: Γ4 ++ B → C :: x0 ++ x1 ++ Γ6 ++ Γ7 = Γ0 ++ (A → C :: Γ4 ++ [B → C]) ++ (x0 ++ x1) ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ0 ++ Γ6 ++ x0 ++ x1) ++ A → C :: Γ4 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ (x0 ++ x1) ++ (A → C :: Γ4 ++ [B → C]) ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ0 ++ Γ6 ++ Γ5) ++ A→ C :: Γ4 ++ B→ C :: Γ7, D). repeat split.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
            assert (Γ0 ++ A → C :: (Γ4 ++ Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ0 ++ (A → C :: Γ4) ++ Γ5 ++ Γ6 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (A → C :: Γ4) ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: (Γ4 ++ x0) ++ B → C :: Γ2, D). repeat split.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ4) ++ x0 ++ Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: (Γ4 ++ x0) ++ Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
            assert (Γ0 ++ A → C :: (Γ4 ++ Γ5 ++ Γ6 ++ x0) ++ B → C :: Γ2 = Γ0 ++ (A → C :: Γ4) ++ Γ5 ++ Γ6 ++ x0 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: (Γ4 ++ x0) ++ B → C :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (A → C :: Γ4) ++ x0 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ0 ++ x1 ++ x0 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split.
            assert (Γ0 ++ (x1 ++ x0) ++ Γ5 ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ x1 ++ x0 ++ Γ5) ++ (A ∨ B) → C :: Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. right.
            exists ((Γ0 ++ A → C :: Γ4 ++ Γ5 ++ x1) ++ [] ++ x0 ++ [B → C] ++ Γ7, D). repeat split.
            assert (Γ0 ++ A → C :: (Γ4 ++ Γ5 ++ x1) ++ B → C :: x0 ++ Γ7 = (Γ0 ++ A → C :: Γ4 ++ Γ5 ++ x1) ++ [B → C]  ++ x0 ++ [] ++ Γ7).
            repeat rewrite <- app_assoc. auto. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
            assert ((Γ0 ++ A → C :: Γ4 ++ Γ5 ++ x1) ++ [] ++ x0 ++ [B → C] ++ Γ7 = Γ0 ++ (A → C :: Γ4) ++ Γ5 ++ (x1 ++ x0) ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ x1 ++ x0 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7 = Γ0 ++ (x1 ++ x0) ++ Γ5 ++ (A → C :: Γ4) ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
- destruct x ; simpl in e0 ; subst ; repeat rewrite <- app_assoc ; simpl.
  * destruct Γ4.
    + simpl in e0. subst. simpl. destruct Γ5.
        { simpl in e0. simpl. destruct Γ6.
          { simpl in e0. subst. simpl. exists (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto. left. apply list_exch_L_id. }
          { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - exists (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D). repeat split. left. apply list_exch_L_id.
            - exists (Γ0 ++ A → C :: Γ1 ++ B → C :: x ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left. apply list_exch_L_id.
            - exists (Γ0 ++ A → C :: (Γ6 ++ x) ++ B → C :: Γ2, D). repeat split. 2: left. 2: apply list_exch_L_id.
              assert (Γ0 ++ (A ∨ B) → C :: Γ6 ++ x ++ Γ2 =Γ0 ++ (A ∨ B) → C :: (Γ6 ++ x) ++ Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply OrImpLRule_I. } }
        { simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          { exists ((Γ0 ++ Γ6) ++ A→ C :: Γ1 ++ B→ C :: Γ7, D) . repeat split. 2: left.
            assert (Γ0 ++ Γ6 ++ ((A ∨ B) → C :: Γ1) ++  Γ7 = (Γ0 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++  Γ7). repeat rewrite <- app_assoc. auto. rewrite H.
            apply OrImpLRule_I.
            assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ6 ++  Γ7 = Γ0 ++ [] ++ (A → C :: Γ1 ++ [B → C]) ++ Γ6 ++  Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6) ++ A → C :: Γ1 ++ B → C ::  Γ7 = Γ0 ++ Γ6 ++ (A → C :: Γ1 ++ [B → C]) ++ [] ++  Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
            apply list_exch_LI. }
          {  exists ((Γ0 ++  Γ6) ++ A→ C ::  Γ1 ++ B→ C :: x ++ Γ7, D). split. 2: left.
            assert (Γ0 ++  Γ6 ++ ((A ∨ B) → C ::  Γ1 ++  x) ++ Γ7 = (Γ0 ++  Γ6) ++ (A ∨ B) → C ::  Γ1 ++  x ++ Γ7). repeat rewrite <- app_assoc. auto.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I.
            assert (Γ0 ++ A → C :: Γ1 ++ B → C :: x ++ Γ6 ++ Γ7 = Γ0 ++ [] ++ (A → C ::  Γ1 ++  B → C :: x) ++  Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ0 ++ Γ6 ++ (A → C ::  Γ1 ++  B → C :: x) ++ [] ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
          { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - exists ((Γ0 ++ Γ6) ++ A → C :: Γ5 ++ B → C :: Γ7, D). repeat split.
              assert (Γ0 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ Γ7 = (Γ0 ++ Γ6) ++ (A ∨ B) → C :: Γ5 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply OrImpLRule_I. left.
              assert (Γ0 ++ A → C :: (Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ0 ++ [] ++ (A → C :: Γ5) ++ Γ6 ++ B → C :: Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ0 ++ Γ6) ++ A → C :: Γ5 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ (A → C :: Γ5) ++ [] ++ B → C :: Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            - exists ((Γ0 ++ Γ6) ++ A → C :: (Γ5 ++ x0) ++ B → C :: Γ2, D). repeat split.
              assert (Γ0 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ x0 ++ Γ2 = (Γ0 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ x0) ++ Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply OrImpLRule_I. left.
              assert (Γ0 ++ A → C :: (Γ5 ++ Γ6 ++ x0) ++ B → C :: Γ2 = Γ0 ++ [] ++ (A → C :: Γ5) ++ Γ6 ++ x0 ++ B → C :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ0 ++ Γ6) ++ A → C :: (Γ5 ++ x0) ++ B → C :: Γ2 = Γ0 ++ Γ6 ++ (A → C :: Γ5) ++ [] ++ x0 ++ B → C :: Γ2).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            - exists ((Γ0 ++ x ++ x0) ++ A → C :: Γ5 ++ B → C :: Γ7, D). repeat split.
              assert (Γ0 ++ (x ++ x0) ++ ((A ∨ B) → C :: Γ5) ++ Γ7 = (Γ0 ++ x ++ x0) ++ (A ∨ B) → C :: Γ5 ++ Γ7). repeat rewrite <- app_assoc. auto.
              rewrite H. apply OrImpLRule_I. right. exists (Γ0 ++ x0 ++ A → C :: (Γ5 ++ x) ++ B → C :: Γ7, D).
              assert (Γ0 ++ A → C :: (Γ5 ++ x) ++ B → C :: x0 ++ Γ7 = Γ0 ++ [] ++ (A → C :: Γ5 ++ x ++ [B → C]) ++ x0 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ0 ++ x0 ++ A → C :: (Γ5 ++ x) ++ B → C :: Γ7 = Γ0 ++ x0 ++ (A → C :: Γ5 ++ x ++ [B → C]) ++ [] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. repeat split.
              assert (Γ0 ++ x0 ++ (A → C :: Γ5 ++ x ++ [B → C]) ++ [] ++ Γ7 = Γ0 ++ [] ++ (x0 ++ A → C :: Γ5) ++ x ++ B → C :: Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
              assert ((Γ0 ++ x ++ x0) ++ A → C :: Γ5 ++ B → C :: Γ7 = Γ0 ++ x ++ (x0 ++ A → C :: Γ5) ++ [] ++ B → C :: Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI. } }
    + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
      { exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ7, D). repeat split.
        assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ1) ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
        rewrite H. apply OrImpLRule_I. left.
        assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A → C :: Γ1 ++ [B → C]) ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (A → C :: Γ1 ++ [B → C]) ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
      { exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7, D). repeat split.
        assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ1 ++ x) ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: Γ1 ++ x ++ Γ7). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
        assert (Γ0 ++ A → C :: Γ1 ++ B → C :: x ++ Γ5 ++ Γ6 ++ Γ7 = Γ0 ++ (A → C :: Γ1 ++ B → C :: x) ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (A → C :: Γ1 ++ B → C :: x) ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
      {  apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        - exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split.
          assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: Γ4 ++ Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. right.
          exists (Γ0 ++ [] ++ Γ5 ++ (A → C :: Γ4) ++ B → C :: Γ6 ++ Γ7, D). split.
          assert (Γ0 ++ A → C :: (Γ4 ++ Γ5) ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ (A → C :: Γ4) ++ Γ5 ++ [] ++ B → C :: Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI. simpl.
          assert (Γ0 ++ Γ5 ++ A → C :: Γ4 ++ B → C :: Γ6 ++ Γ7 = Γ0 ++ [] ++ (Γ5 ++ A → C :: Γ4 ++ [B → C]) ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ (Γ5 ++ A → C :: Γ4 ++ [B → C]) ++ [] ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
        - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: Γ4 ++ Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
            assert (Γ0 ++ A → C :: (Γ4 ++ Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ0 ++ (A → C :: Γ4) ++ Γ5 ++ Γ6 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7 = Γ0 ++ Γ6 ++ Γ5 ++ (A → C :: Γ4) ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: (Γ4 ++ x) ++ B → C :: Γ2, D). repeat split.
            assert (Γ0 ++ Γ6 ++ Γ5 ++ ((A ∨ B) → C :: Γ4) ++ x ++ Γ2 = (Γ0 ++ Γ6 ++ Γ5) ++ (A ∨ B) → C :: (Γ4 ++ x) ++ Γ2). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
            assert (Γ0 ++ A → C :: (Γ4 ++ Γ5 ++ Γ6 ++ x) ++ B → C :: Γ2 = Γ0 ++ (A → C :: Γ4) ++ Γ5 ++ Γ6 ++ x ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: (Γ4 ++ x) ++ B → C :: Γ2 = Γ0 ++ Γ6 ++ Γ5 ++ (A → C :: Γ4) ++ x ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          * exists ((Γ0 ++ x0 ++ x ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split.
            assert (Γ0 ++ (x0 ++ x) ++ Γ5 ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ x0 ++ x ++ Γ5) ++ (A ∨ B) → C :: Γ4 ++ Γ7). repeat rewrite <- app_assoc.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. right.
            exists (Γ0 ++ x0 ++ Γ5 ++ (A → C :: Γ4) ++ B → C :: x ++ Γ7, D). split.
            assert (Γ0 ++ A → C :: (Γ4 ++ Γ5 ++ x0) ++ B → C :: x ++ Γ7 = Γ0 ++ (A → C :: Γ4) ++ Γ5 ++ x0 ++ B → C :: x ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.  apply list_exch_LI. simpl.
            assert (Γ0 ++ x0 ++ Γ5 ++ A → C :: Γ4 ++ B → C :: x ++ Γ7 = (Γ0 ++ x0) ++ [] ++ (Γ5 ++ A → C :: Γ4 ++ [B → C]) ++ x ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ0 ++ x0 ++ x ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7 = (Γ0 ++ x0) ++ x ++ (Γ5 ++ A → C :: Γ4 ++ [B → C]) ++ [] ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
        - exists ((Γ0 ++ Γ6 ++ x ++ x0) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split.
          assert (Γ0 ++ Γ6 ++ (x ++ x0) ++ ((A ∨ B) → C :: Γ4) ++ Γ7 = (Γ0 ++ Γ6 ++ x ++ x0) ++ (A ∨ B) → C :: Γ4 ++ Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. right.
          exists (Γ0 ++ Γ6 ++ (x ++ B → C :: x0) ++ (A → C :: Γ4) ++ Γ7, D). split.
          assert (Γ0 ++ A → C :: (Γ4 ++ x) ++ B → C :: x0 ++ Γ6 ++ Γ7 = Γ0 ++ (A → C :: Γ4) ++ (x ++ B → C :: x0) ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.  apply list_exch_LI. simpl.
          assert (Γ0 ++ Γ6 ++ (x ++ B → C :: x0) ++ A → C :: Γ4 ++ Γ7 = (Γ0 ++ Γ6 ++ x) ++ [B → C] ++ (x0 ++ A → C :: Γ4) ++ [] ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ0 ++ Γ6 ++ x ++ x0) ++ A → C :: Γ4 ++ B → C :: Γ7 = (Γ0 ++ Γ6 ++ x) ++ [] ++ (x0 ++ A → C :: Γ4) ++ [B → C] ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
  * inversion e0 ; subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
    + exists (Γ0 ++ A → C :: (Γ1 ++ Γ6 ++ Γ5) ++ B → C :: Γ4 ++ Γ7, D). repeat split.
        assert (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ (A ∨ B) → C :: (Γ1 ++ Γ6 ++ Γ5) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
        assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A → C :: Γ1) ++ (B → C :: Γ4) ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ A → C :: (Γ1 ++ Γ6 ++ Γ5) ++ B → C :: Γ4 ++ Γ7 = (Γ0 ++ A → C :: Γ1) ++ Γ6 ++ Γ5 ++ (B → C :: Γ4) ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
    + exists (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat split. repeat rewrite <- app_assoc. apply OrImpLRule_I. left.
        assert (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ4 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A → C :: Γ1 ++ B → C :: x0) ++ Γ4 ++ Γ5 ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ A → C :: Γ1 ++ B → C :: x0) ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
    + apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
      { exists (Γ0 ++ A → C :: (x ++ Γ6) ++ B → C :: Γ5 ++ Γ4 ++ Γ7, D). repeat split.
        assert (Γ0 ++ (A ∨ B) → C :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ (A ∨ B) → C :: (x ++ Γ6) ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
        assert (Γ0 ++ A → C :: (x ++ Γ4) ++ B → C :: Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ4 ++ (B → C :: Γ5) ++ Γ6 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ A → C :: (x ++ Γ6) ++ B → C :: Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ6 ++ (B → C :: Γ5) ++ Γ4 ++ Γ7).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
      { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        - exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5) ++ B → C :: Γ4 ++ Γ7, D). repeat split.
          assert (Γ0 ++ (A ∨ B) → C :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ (A ∨ B) → C :: (x ++ Γ6 ++ Γ5) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
          assert (Γ0 ++ A → C :: (x ++ Γ4 ++ Γ5) ++ B → C :: Γ6 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ4 ++ (Γ5 ++ [B → C]) ++ Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5) ++ B → C :: Γ4 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ6 ++ (Γ5 ++ [B → C]) ++ Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
        - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          + exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ B → C :: Γ7, D). repeat split.
             assert (Γ0 ++ (A ∨ B) → C :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ (A ∨ B) → C :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ Γ7). repeat rewrite <- app_assoc.
             simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
             assert (Γ0 ++ A → C :: (x ++ Γ4 ++ Γ5 ++ Γ6) ++ B → C :: Γ7 = (Γ0 ++ A → C :: x) ++ Γ4 ++ Γ5 ++ Γ6 ++ B → C :: Γ7).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
             assert (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ B → C :: Γ7 = (Γ0 ++ A → C :: x) ++ Γ6 ++ Γ5 ++ Γ4 ++ B → C :: Γ7).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          + exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2, D). repeat split.
             assert (Γ0 ++ (A ∨ B) → C :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ Γ2 = Γ0 ++ (A ∨ B) → C :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ Γ2). repeat rewrite <- app_assoc.
             simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
             assert (Γ0 ++ A → C :: (x ++ Γ4 ++ Γ5 ++ Γ6 ++ x1) ++ B → C :: Γ2 = (Γ0 ++ A → C :: x) ++ Γ4 ++ Γ5 ++ Γ6 ++ x1 ++ B → C :: Γ2).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
             assert (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2 = (Γ0 ++ A → C :: x) ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ B → C :: Γ2).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          + exists (Γ0 ++ A → C :: (x ++ x0) ++ B → C :: x1 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat split.
             assert (Γ0 ++ (A ∨ B) → C :: x ++ (x0 ++ x1) ++ Γ5 ++ Γ4 ++ Γ7 = Γ0 ++ (A ∨ B) → C :: (x ++ x0) ++ x1 ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc.
             simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
             assert (Γ0 ++ A → C :: (x ++ Γ4 ++ Γ5 ++ x0) ++ B → C :: x1 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ4 ++ Γ5 ++ (x0 ++ B → C :: x1) ++ Γ7).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
             assert (Γ0 ++ A → C :: (x ++ x0) ++ B → C :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = (Γ0 ++ A → C :: x) ++ (x0 ++ B → C :: x1) ++ Γ5 ++ Γ4 ++ Γ7).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
        - exists (Γ0 ++ A → C :: (x ++ Γ6 ++ x1) ++ B → C :: x0 ++ Γ4 ++ Γ7, D). repeat split.
           assert (Γ0 ++ (A ∨ B) → C :: x ++ Γ6 ++ (x1 ++ x0) ++ Γ4 ++ Γ7 = Γ0 ++ (A ∨ B) → C :: (x ++ Γ6 ++ x1) ++ x0 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc.
           simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
           assert (Γ0 ++ A → C :: (x ++ Γ4 ++ x1) ++ B → C :: x0 ++ Γ6 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ4 ++ (x1 ++ B → C :: x0) ++ Γ6 ++ Γ7).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ0 ++ A → C :: (x ++ Γ6 ++ x1) ++ B → C :: x0 ++ Γ4 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ6 ++ (x1 ++ B → C :: x0) ++ Γ4 ++ Γ7).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
      { exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ x0) ++ B → C :: x1 ++ Γ7, D). repeat split.
         assert (Γ0 ++ (A ∨ B) → C :: x ++ Γ6 ++ Γ5 ++ (x0 ++ x1) ++ Γ7 = Γ0 ++ (A ∨ B) → C :: (x ++ Γ6 ++ Γ5 ++ x0) ++ x1 ++ Γ7). repeat rewrite <- app_assoc.
         simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
         assert (Γ0 ++ A → C :: (x ++ x0) ++ B → C :: x1 ++ Γ5 ++ Γ6 ++ Γ7 = (Γ0 ++ A → C :: x) ++ (x0 ++ B → C :: x1) ++ Γ5 ++ Γ6 ++ Γ7).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
         assert (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ x0) ++ B → C :: x1 ++ Γ7 = (Γ0 ++ A → C :: x) ++ Γ6 ++ Γ5 ++ (x0 ++ B → C :: x1) ++ Γ7).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  * destruct Γ5.
      + simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists ((Γ3 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto.
           assert (Γ3 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc ; auto.
           rewrite H. apply OrImpLRule_I. left. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ3 ++ A → C :: (Γ1 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
            assert (Γ3 ++ (A ∨ B) → C :: Γ1 ++ Γ4 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ1 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc ; auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (A → C :: Γ1) ++ [] ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
            rewrite H.
            assert (Γ3 ++ A → C :: (Γ1 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ [] ++ (A → C :: Γ1) ++ Γ4 ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
            rewrite H0. apply list_exch_LI.
          - exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ4 ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left.
            assert (Γ3 ++ Γ4 ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ1 ++ B → C :: x) ++ [] ++ Γ7). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H.
            assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ4 ++ Γ7 = Γ3 ++ [] ++ (A → C :: Γ1 ++ B → C :: x) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
          - exists (Γ3 ++ A → C :: (Γ6 ++ Γ4 ++ x) ++ B → C :: Γ2, D). repeat split.
            assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ Γ4 ++ x ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ Γ4 ++ x) ++ Γ2). repeat rewrite <- app_assoc ; auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ6 ++ x) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (A → C :: Γ6) ++ [] ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H.
            assert (Γ3 ++ A → C :: (Γ6 ++ Γ4 ++ x) ++ B → C :: Γ2 = Γ3 ++ [] ++ (A → C :: Γ6) ++ Γ4 ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
      + simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { exists ((Γ3 ++ Γ6) ++ A→ C :: Γ1 ++ B→ C :: Γ4 ++ Γ7, D) . repeat split. 2: left.
          assert (Γ3 ++ Γ6 ++ ((A ∨ B) → C :: Γ1) ++  Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++  Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto. rewrite H.
          apply OrImpLRule_I.
          assert ((Γ3 ++ Γ4) ++  A → C :: Γ1 ++ B → C :: Γ6 ++  Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ1 ++ [B → C]) ++ Γ6 ++  Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C ::  Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ1 ++ [B → C]) ++ Γ4 ++  Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
        { exists ((Γ3 ++  Γ6) ++ A→ C ::  Γ1 ++ B→ C :: x ++ Γ4 ++ Γ7, D). split. 2: left.
          assert (Γ3 ++  Γ6 ++ ((A ∨ B) → C ::  Γ1 ++  x) ++ Γ4 ++ Γ7 = (Γ3 ++  Γ6) ++ (A ∨ B) → C ::  Γ1 ++ x ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I.
          assert ((Γ3 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: x ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (A → C ::  Γ1 ++  B → C :: x) ++  Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (A → C ::  Γ1 ++  B → C :: x) ++ Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4) ++ B → C :: Γ7, D). repeat split.
            assert (Γ3 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ Γ4) ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ5) ++ Γ6 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4) ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ Γ4 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2, D). repeat split.
            assert (Γ3 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ Γ4 ++ x1 ++ Γ2 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ Γ4 ++ x1) ++ Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ5 ++ Γ6 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (A → C :: Γ5) ++ Γ6 ++ x1 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ Γ4 ++ x1 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ3 ++ x ++ x1) ++ A → C :: Γ5 ++ B → C :: Γ4 ++ Γ7, D). repeat split.
            assert (Γ3 ++ (x ++ x1) ++ ((A ∨ B) → C :: Γ5) ++ Γ4 ++ Γ7 = (Γ3 ++ x ++ x1) ++ (A ∨ B) → C :: Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. right. exists (Γ3 ++ (x ++ B → C :: x1) ++ (A → C :: Γ5) ++ Γ4 ++ Γ7, D). split.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ5 ++ x) ++ B → C :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ5) ++ (x ++ B → C :: x1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
            assert (Γ3 ++ (x ++ B → C :: x1) ++ (A → C :: Γ5) ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ [B → C] ++ (x1 ++ A → C :: Γ5) ++ [] ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ x ++ x1) ++ A → C :: Γ5 ++ B → C :: Γ4 ++ Γ7 = (Γ3 ++ x) ++ [] ++ (x1 ++ A → C :: Γ5) ++ [B → C] ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI. }
  * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      + simpl in e0. simpl. destruct Γ6.
          { simpl in e0. subst. simpl. exists ((Γ3 ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto.
             assert (Γ3 ++ Γ5 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ5 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc ; auto.
             rewrite H. apply OrImpLRule_I. left.
             assert ((Γ3 ++ Γ4 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ [] ++ Γ5 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
             rewrite H.
             assert ((Γ3 ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ5 ++ [] ++ Γ4 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
             rewrite H0. apply list_exch_LI. }
          { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - exists (Γ3 ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ (A ∨ B) → C :: Γ1 ++ Γ5 ++ Γ4 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ1 ++ Γ5 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc ; auto.
              rewrite H. apply OrImpLRule_I. left.
              assert ((Γ3 ++ Γ4 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (A → C :: Γ1) ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
              rewrite H.
              assert (Γ3 ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ1) ++ Γ5 ++ Γ4 ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
              rewrite H0. apply list_exch_LI.
            - exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left.
              assert (Γ3 ++ Γ4 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (A → C :: Γ1 ++ B → C :: x0) ++ Γ7). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H.
              assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (A → C :: Γ1 ++ B → C :: x0) ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
            - exists (Γ3 ++ A → C :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ Γ2). repeat rewrite <- app_assoc ; auto.
              rewrite H. apply OrImpLRule_I. left.
              assert ((Γ3 ++ Γ4 ++ Γ5) ++ A → C :: (Γ6 ++ x0) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (A → C :: Γ6) ++ x0 ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H.
              assert (Γ3 ++ A → C :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ6) ++ Γ5 ++ Γ4 ++ x0 ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
      + subst. apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D) . repeat split. 2: left.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto. rewrite H.
            apply OrImpLRule_I. repeat rewrite <- app_assoc ; apply list_exch_LI. }
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split. 2: left.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. repeat rewrite <- app_assoc ; apply list_exch_LI. }
          { destruct x0 ; simpl in e0 ; inversion e0 ; subst.
            - repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ x ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ x ++ Γ5 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ x ++ Γ5 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H0. apply OrImpLRule_I. left. repeat rewrite <- app_assoc ; apply list_exch_LI.
            - apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
              + exists((Γ3 ++ x) ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
                  assert (Γ3 ++ (x ++ (A ∨ B) → C :: Γ1) ++ Γ5 ++ Γ4 ++ Γ2 = (Γ3 ++ x) ++ (A ∨ B) → C :: (Γ1 ++ Γ5 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply OrImpLRule_I. left.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A → C :: Γ1) ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ (x ++ A → C :: Γ1) ++ Γ5 ++ Γ4 ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
              + exists ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat split.
                  assert (Γ3 ++ (x ++ (A ∨ B) → C :: Γ1 ++ x1) ++ Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ (A ∨ B) → C :: Γ1 ++ x1 ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
                  simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ5 ++ Γ4 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
              + exists ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2, D). repeat split.
                  assert (Γ3 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ5 ++ Γ4 ++ x1 ++ Γ2 = (Γ3 ++ x) ++ (A ∨ B) → C :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply OrImpLRule_I. left.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A → C :: x0) ++ x1 ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ Γ4 ++ x1 ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI. }
      + destruct x ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in e0. subst. simpl in H0. simpl. repeat rewrite <- app_assoc. simpl.
               exists ((Γ3 ++ x0 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto.
               assert (Γ3 ++ x0 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ x0 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H. apply OrImpLRule_I. left.
               assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ [] ++ x0 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert ((Γ3 ++ x0 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ x0 ++ [] ++ Γ4 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H1. apply list_exch_LI.
            - simpl in e0. inversion e0. clear H0. subst. simpl. repeat rewrite <- app_assoc. simpl.
              apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
              + exists (Γ3 ++ A → C :: (Γ1 ++ x0 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ (A ∨ B) → C :: Γ1 ++ x0 ++ Γ4 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ1 ++ x0 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (A → C :: Γ1) ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H.
                assert (Γ3 ++ A → C :: (Γ1 ++ x0 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ1) ++ x0 ++ Γ4 ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply list_exch_LI.
              + exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ x0 ++ Γ4 ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ3 ++ Γ4 ++ x0 ++ (A → C :: Γ1 ++ B → C :: x) ++ Γ7). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H.
                assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ x0 ++ Γ4 ++ Γ7 = Γ3 ++ (A → C :: Γ1 ++ B → C :: x) ++ x0 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
              + exists (Γ3 ++ A → C :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ x0 ++ Γ4 ++ x ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: (Γ6 ++ x) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (A → C :: Γ6) ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H.
                assert (Γ3 ++ A → C :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ6) ++ x0 ++ Γ4 ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
        { apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ4 ++ Γ7, D). split ;auto.
             assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: Γ1) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
             rewrite H. apply OrImpLRule_I. left.
             assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: Γ1 ++ [B → C]) ++ Γ6 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H.
             assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: Γ1 ++ [B → C]) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ4 ++ Γ7, D). split ;auto.
             assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: Γ1 ++ x1) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: Γ1 ++ x1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
             assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ6 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H.
             assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            + exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4) ++  B → C :: Γ7, D). split ;auto.
               assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: x) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: (x ++ Γ4) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
               assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: (x ++ Γ6) ++ B → C :: Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: x) ++ Γ6 ++ B → C :: Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4) ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: x) ++ Γ4 ++ B → C :: Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
            + exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4 ++ x2) ++  B → C :: Γ2, D). split ;auto.
               assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: x) ++ Γ4 ++ x2 ++ Γ2 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: (x ++ Γ4 ++ x2) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
               assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: (x ++ Γ6 ++ x2) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: x) ++ Γ6 ++ x2 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4 ++ x2) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: x) ++ Γ4 ++ x2 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
            + exists ((Γ3 ++ x1 ++ x2 ++ x0) ++ A → C :: x ++ B → C :: Γ4 ++ Γ7, D). split ;auto.
               assert (Γ3 ++ (x1 ++ x2) ++ (x0 ++ (A ∨ B) → C :: x) ++ Γ4 ++ Γ7 = (Γ3 ++ x1 ++ x2 ++ x0) ++ (A ∨ B) → C :: x ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
               exists (Γ3 ++ (x1 ++ B → C :: x2) ++ (x0 ++ A → C :: x) ++ Γ4 ++ Γ7, D). split.
               assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: (x ++ x1) ++ B → C :: x2 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: x) ++ (x1 ++ B → C :: x2) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply list_exch_LI.
               assert (Γ3 ++ (x1 ++ B → C :: x2) ++ (x0 ++ A → C :: x) ++ Γ4 ++ Γ7 = (Γ3 ++ x1) ++ [B → C] ++ (x2 ++ x0 ++ A → C :: x) ++ [] ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert ((Γ3 ++ x1 ++ x2 ++ x0) ++ A → C :: x ++ B → C :: Γ4 ++ Γ7 = (Γ3 ++ x1) ++ [] ++ (x2 ++ x0 ++ A → C :: x) ++ [B → C] ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
  * destruct x0 ; simpl in e0 ; inversion e0 ; subst.
      + destruct Γ5 ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in H1. subst. repeat rewrite <- app_assoc. simpl.
              exists ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ x ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ x) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply OrImpLRule_I. left. repeat rewrite <- app_assoc. apply list_exch_L_id.
            - simpl in H1. inversion H1. subst. apply app2_find_hole in H3. destruct H3. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ2, D). repeat split. left.
                assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ x ++ (A → C :: Γ1 ++ [B → C]) ++ [] ++ Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ2 = Γ3 ++ [] ++ (A → C :: Γ1 ++ [B → C]) ++ x ++ Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
              * repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
                exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7, D). repeat split. left.
                assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7 = Γ3 ++ x ++ (A → C :: Γ1 ++ B → C :: x0) ++ [] ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7 = Γ3 ++ [] ++ (A → C :: Γ1 ++ B → C :: x0) ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
              * repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
                exists (Γ3 ++ A → C :: (Γ6 ++ x ++ x0) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ x ++ x0 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ x ++ x0) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ x ++ A → C :: Γ6 ++ x0 ++ B → C :: Γ2 = Γ3 ++ x ++ (A → C :: Γ6) ++ [] ++ x0 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A → C :: (Γ6 ++ x ++ x0) ++ B → C :: Γ2 = Γ3 ++ [] ++ (A → C :: Γ6) ++ x ++ x0 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply list_exch_LI. }
          { apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
            - repeat rewrite <- app_assoc. simpl. exists ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ1 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
              assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7 = Γ3 ++ x ++ (A → C :: Γ1 ++ [B → C]) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ1 ++ [B → C]) ++ x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
            - repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
              exists ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ1 ++ x0 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++ x0 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
              assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ7 = Γ3 ++ x ++(A → C :: Γ1 ++ B → C :: x0) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ1 ++ B → C :: x0) ++ x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
            - repeat rewrite <- app_assoc. simpl. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * exists ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ x) ++  B → C :: Γ7, D). repeat split.
                assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ5 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ x) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ x ++ A → C :: Γ5 ++ Γ6 ++ B → C :: Γ7 = Γ3 ++ x ++ (A → C :: Γ5) ++ Γ6 ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ x) ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ x ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
              * exists ((Γ3 ++ Γ6) ++ A→ C :: (Γ5 ++ x ++ x1) ++ B→ C :: Γ2, D). repeat split.
                assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ5 ++ x ++ x1 ++ Γ2 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ x ++ x1) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ x ++ A → C :: Γ5 ++ (Γ6 ++ x1) ++ B → C :: Γ2 = Γ3 ++ x ++ (A → C :: Γ5) ++ Γ6 ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ x ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ x ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
              * exists ((Γ3 ++ x0 ++ x1) ++ A → C :: Γ5 ++ B → C :: x ++ Γ7, D). repeat split.
                assert (Γ3 ++ (x0 ++ x1) ++ (A ∨ B) → C :: Γ5 ++ x ++ Γ7 = (Γ3 ++ x0 ++ x1) ++ (A ∨ B) → C :: Γ5 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
                exists (Γ3 ++  (x0 ++ B → C :: x1) ++ (A → C :: Γ5) ++ x ++ Γ7, D). split.
                assert (Γ3 ++ x ++ A → C :: Γ5 ++ x0 ++ B → C :: x1 ++ Γ7 = Γ3 ++ x ++ (A → C :: Γ5) ++ (x0 ++ B → C :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
                assert (Γ3 ++ (x0 ++ B → C :: x1) ++ (A → C :: Γ5) ++ x ++ Γ7 = (Γ3 ++ x0) ++ [B → C] ++ (x1 ++ A → C :: Γ5) ++ [] ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ x0 ++ x1) ++ A → C :: Γ5 ++ B → C :: x ++ Γ7 = (Γ3 ++ x0) ++ [] ++  (x1 ++ A → C :: Γ5) ++ [B → C] ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI. }
      + apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        {  exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ7, D). repeat split.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: Γ1) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: Γ1 ++ [B → C]) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: Γ1 ++ [B → C]) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI. }
        { exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C ::  x1 ++ Γ7, D). repeat split.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: Γ1 ++ x1) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: Γ1 ++ x1 ++ Γ7). repeat rewrite <- app_assoc. auto.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
              exists (Γ3 ++ Γ6 ++ (Γ5 ++ [B → C]) ++ (x ++ A → C :: x0) ++ Γ7, D). split.
              assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5) ++ B → C :: Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ (Γ5 ++ [B → C]) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ (Γ5 ++ [B → C]) ++ (x ++ A → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5) ++ [B → C] ++ (x ++ A → C :: x0) ++ [] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = (Γ3 ++ Γ6 ++ Γ5) ++ [] ++ (x ++ A → C :: x0) ++ [B → C] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ Γ6 ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: x0) ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              * exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ x1 ++ Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: (x0 ++ x1) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ6 ++ x1) ++ B → C :: Γ2 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ Γ6 ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: x0) ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              * exists ((Γ3 ++ x2 ++ x1 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
                assert (Γ3 ++ (x2 ++ x1) ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ x2 ++ x1 ++ Γ5 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
                exists (Γ3 ++ (x2 ++ B → C :: x1) ++ Γ5 ++ (x ++ A → C :: x0) ++ Γ7, D). split.
                assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ x2) ++ B → C :: x1 ++ Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ (x2 ++ B → C :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
                assert (Γ3 ++ (x2 ++ B → C :: x1) ++ Γ5 ++ (x ++ A → C :: x0) ++ Γ7 = (Γ3 ++ x2) ++ [B → C] ++ (x1 ++ Γ5 ++ x ++ A → C :: x0) ++ [] ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ x2 ++ x1 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = (Γ3 ++ x2) ++ [] ++ (x1 ++ Γ5 ++ x ++ A → C :: x0) ++ [B → C] ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            - exists ((Γ3 ++ Γ6 ++ x1 ++ x2 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ (x1 ++ x2) ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ x1 ++ x2 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
              exists(Γ3 ++ Γ6 ++ (x1 ++ B → C :: x2) ++ (x ++ A → C :: x0) ++ Γ7, D). split.
              assert ((Γ3 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: x2 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ (x1 ++ B → C :: x2) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ (x1 ++ B → C :: x2) ++ (x ++ A → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ x1) ++ [B → C] ++ (x2 ++ x ++ A → C :: x0) ++ [] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6 ++ x1 ++ x2 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = (Γ3 ++ Γ6 ++ x1) ++ [] ++ (x2 ++ x ++ A → C :: x0) ++ [B → C] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
Qed.

Lemma ImpImpL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (ImpImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (ImpImpLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ B → C :: Γ1, A → B). exists (Γ0 ++ C :: Γ1, D). repeat split ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ B → C :: Γ5 ++ Γ6, A → B). exists (Γ0 ++ C :: Γ5 ++ Γ6, D). repeat split ; try apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6, D). repeat split.
        assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ Γ5 ++ ((A → B) → C :: Γ4) ++ Γ6 = (Γ0 ++ Γ5) ++ (A → B) → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ImpImpLRule_I.
        assert (Γ0 ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B → C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert (Γ0 ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6, D). repeat split.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ ((A → B) → C :: Γ3) ++ Γ6 =( Γ0 ++ Γ5 ++ Γ4) ++ (A → B) → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
      apply ImpImpLRule_I.
      assert (Γ0 ++ B → C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B → C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B → C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
      assert (Γ0 ++ C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ B → C :: Γ1, A → B). exists ((Γ0 ++ []) ++ C :: Γ1, D). repeat split ; rewrite <- app_assoc ; simpl ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6, D). repeat split.
          assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          assert (Γ0 ++ Γ5 ++ (A → B) → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ (A → B) → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
          apply ImpImpLRule_I.
          assert (Γ0 ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B → C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ0 ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6, D). repeat split.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ (A → B) → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ (A → B) → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ImpImpLRule_I.
        assert (Γ0 ++ B → C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B → C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B → C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert (Γ0 ++ C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ B → C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, A → B). exists (Γ0 ++ C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat rewrite <- app_assoc. repeat split.
      assert (Γ0 ++ B → C :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ B → C :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ B → C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ B → C :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
      assert (Γ0 ++ C :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ C :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ C :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ B → C :: Γ1, A → B). exists ((Γ2 ++ Γ3) ++ C :: Γ1, D).  repeat split ; try apply list_exch_L_id. rewrite app_assoc.
           apply ImpImpLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ B → C :: Γ5 ++ Γ3 ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ Γ3 ++ Γ6, D). repeat split.
           assert ((Γ2 ++ Γ3) ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B → C :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (B → C :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3) ++ C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ C :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (C :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ Γ3 ++ Γ6, A → B). exists ((Γ2 ++ Γ5) ++ C :: Γ4 ++ Γ3 ++ Γ6, D). repeat split.
        assert (Γ2 ++ Γ5 ++ ((A → B) → C :: Γ4) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ (A → B) → C :: Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        apply ImpImpLRule_I.
        assert ((Γ2 ++ Γ3) ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (B → C :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert ((Γ2 ++ Γ3) ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ C :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (C :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ B → C :: Γ1, A → B). exists ((Γ2 ++ Γ4 ++ Γ3) ++ C :: Γ1, D). repeat split.
           assert (Γ2 ++ Γ4 ++ Γ3 ++ (A → B) → C :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ (A → B) → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           apply ImpImpLRule_I.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B → C :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ B → C :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ C :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ C :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ B → C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B → C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B → C :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (C :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ B → C :: Γ1, A → B).  exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply ImpImpLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ B → C :: Γ1, A → B). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply ImpImpLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ B → C :: Γ1, A → B). exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply ImpImpLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ B → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6, A → B). exists ((Γ2 ++ x) ++ C :: x0 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
              assert (Γ2 ++ x ++ (A → B) → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ (A → B) → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              apply ImpImpLRule_I.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ B → C :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ B → C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ B → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ B → C :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ C :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ C :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ B → C :: Γ1, A → B). exists (Γ2 ++ x0 ++ Γ3 ++ C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply ImpImpLRule_I.
              assert (Γ2 ++ Γ3 ++ x0 ++ B → C :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ B → C :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x0 ++ C :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ C :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ B → C :: Γ5 ++ x0 ++ Γ3 ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ x0 ++ Γ3 ++ Γ6, D). repeat split.
              assert (Γ2 ++ Γ3 ++ x0 ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B → C :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (B → C :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x0 ++ C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ C :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (C :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ B → C :: x ++ Γ3 ++ Γ6, A → B). exists ((Γ2 ++ Γ5 ++ x0) ++ C :: x ++ Γ3 ++ Γ6, D). repeat split.
           assert (Γ2 ++ Γ5 ++ (x0 ++ (A → B) → C :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ (A → B) → C :: x ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           apply ImpImpLRule_I.
           assert ((Γ2 ++ Γ3 ++ x0) ++ B → C :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ B → C :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ B → C :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ B → C :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ x0) ++ C :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ C :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ C :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ C :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ B → C :: Γ1, A → B). exists (Γ2 ++ x ++ C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply ImpImpLRule_I. apply list_exch_L_id. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ B → C :: Γ5 ++ x ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ x ++ Γ6, D). repeat split.
              assert (Γ2 ++ x ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B → C :: Γ5 ++ x ++ Γ6 = Γ2 ++( B → C :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ x ++ C :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ C :: Γ5 ++ x ++ Γ6 = Γ2 ++(C :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ x ++ Γ6, A → B). exists ((Γ2 ++ Γ5) ++ C :: Γ4 ++ x ++ Γ6, D). repeat split.
          assert (Γ2 ++ Γ5 ++ (A → B) → C :: Γ4 ++ x ++ Γ6 = (Γ2 ++ Γ5) ++ (A → B) → C :: Γ4 ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply ImpImpLRule_I.
          assert (Γ2 ++ x ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (B → C :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ2 ++ x ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ C :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (C :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ B → C :: x0 ++ Γ6, A → B). exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ C :: x0 ++ Γ6, D). repeat split.
          assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ (A → B) → C :: x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ (A → B) → C :: x0 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply ImpImpLRule_I.
          assert (Γ2 ++ x ++ B → C :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ B → C :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ B → C :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ B → C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ2 ++ x ++ C :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ C :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ C :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
Qed.

Lemma BoxImpL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (BoxImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (BoxImpLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. apply univ_gen_ext_splitR in X. destruct X.
repeat destruct s. repeat destruct p. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (XBoxed_list (x ++ x0) ++ [Box A], A). exists (Γ0 ++ B :: Γ1, C). repeat split ; try apply list_exch_L_id ; auto. apply univ_gen_ext_combine ; auto. }
        { simpl in e0. inversion e0. subst. simpl. exists (XBoxed_list (x ++ x0) ++ [Box A], A). exists (Γ0 ++ B :: Γ5 ++ Γ6, C). repeat split ; try apply list_exch_L_id ; auto. apply univ_gen_ext_combine ; auto. }
      * simpl in e0. inversion e0. subst. apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p.
        apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
        exists (XBoxed_list (x ++ x4 ++ x2 ++ x5) ++ [Box A], A). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
        assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ (Box A → B :: Γ4) ++ Γ6 = (Γ0 ++ Γ5) ++ Box A → B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply BoxImpLRule_I ; auto. intro. intros. apply H2. apply in_app_or in H1. destruct H1. apply in_or_app ; auto. apply in_app_or in H1.
        destruct H1. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1. destruct H1.
        apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  auto.
        repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite XBox_app_distrib.
        repeat rewrite <- app_assoc.
        assert (XBoxed_list x ++ XBoxed_list x2 ++ XBoxed_list x4 ++ XBoxed_list x5 ++ [Box A] =
        XBoxed_list x ++ XBoxed_list x2 ++ [] ++ XBoxed_list x4 ++ XBoxed_list x5 ++ [Box A]). auto. rewrite H.
        assert (XBoxed_list x ++ XBoxed_list x4 ++ XBoxed_list x2 ++ XBoxed_list x5 ++ [Box A] =
        XBoxed_list x ++ XBoxed_list x4 ++ [] ++ XBoxed_list x2 ++ XBoxed_list x5 ++ [Box A]). auto. rewrite H0.
        apply list_exch_LI.
        assert (Γ0 ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
      apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
      apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
      exists (XBoxed_list (x ++ x3 ++ x0 ++ x2 ++ x5) ++ [Box A], A). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ (Box A → B :: Γ3) ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ Box A → B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply BoxImpLRule_I ; auto. intro. intros. apply H2. apply in_app_or in H1. destruct H1. apply in_or_app ; auto. apply in_app_or in H1.
      destruct H1. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1. destruct H1.
      apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1. destruct H1.
      apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
      repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite XBox_app_distrib.
      repeat rewrite <- app_assoc. apply list_exch_LI.
      assert (Γ0 ++ B :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- destruct x1.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. repeat rewrite <- app_assoc ; simpl.  exists (XBoxed_list (x ++ x0) ++ [Box A], A).
           exists (Γ0 ++ B :: Γ1, C). repeat split ; try apply list_exch_L_id ; try apply univ_gen_ext_combine ; auto. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl.
          apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
          exists (XBoxed_list (x ++ x0 ++ x1 ++ x3) ++ [Box A], A). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
          assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ Box A → B :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ Box A → B :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply BoxImpLRule_I ; auto. intro. intros. apply H2. apply in_app_or in H1. destruct H1. apply in_or_app ; auto. apply in_app_or in H1.
          destruct H1. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1. destruct H1.
          apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  auto.
          repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite XBox_app_distrib.
          repeat rewrite <- app_assoc.
          assert (XBoxed_list x ++ XBoxed_list x1 ++ XBoxed_list x0 ++ XBoxed_list x3 ++ [Box A] =
          XBoxed_list x ++ XBoxed_list x1 ++ [] ++ XBoxed_list x0 ++ XBoxed_list x3 ++ [Box A]). auto. rewrite H.
          assert (XBoxed_list x ++ XBoxed_list x0 ++ XBoxed_list x1 ++ XBoxed_list x3 ++ [Box A] =
          XBoxed_list x ++ XBoxed_list x0 ++ [] ++ XBoxed_list x1 ++ XBoxed_list x3 ++ [Box A]). auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ0 ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl.
        apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
        apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
        apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
        exists (XBoxed_list (x ++ x2 ++ x0 ++ x1 ++ x4) ++ [Box A], A). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ Box A → B :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ Box A → B :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply BoxImpLRule_I ; auto. intro. intros. apply H2. apply in_app_or in H1. destruct H1. apply in_or_app ; auto. apply in_app_or in H1.
        destruct H1. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1. destruct H1.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1. destruct H1. apply in_or_app ; right ; apply in_or_app ; auto.
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ;  auto.
        repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite XBox_app_distrib.
        repeat rewrite <- app_assoc. apply list_exch_LI.
        assert (Γ0 ++ B :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst.
      apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
      apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
      apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
      apply univ_gen_ext_splitR in u3. destruct u3. repeat destruct s. repeat destruct p. subst.
      exists (XBoxed_list (x ++ x2 ++ x4 ++ x3 ++ x0 ++ x6) ++ [Box A], A). exists (Γ0 ++ B :: x1 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat rewrite <- app_assoc ; repeat split.
      simpl. intro. intros. apply H2. apply in_app_or in H. destruct H. apply in_or_app ; auto. apply in_app_or in H.
      destruct H. apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H. destruct H.
      apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
      apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
      apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  auto.
      apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ;  right ; apply in_or_app ;  auto.
      repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite XBox_app_distrib.
      repeat rewrite <- app_assoc.
      assert (XBoxed_list x ++ XBoxed_list x2 ++ XBoxed_list x0 ++ XBoxed_list x3 ++ XBoxed_list x4 ++ XBoxed_list x6 ++ [Box A] =
      (XBoxed_list x ++ XBoxed_list x2) ++ XBoxed_list x0 ++ XBoxed_list x3 ++ XBoxed_list x4 ++ XBoxed_list x6 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (XBoxed_list x ++ XBoxed_list x2 ++ XBoxed_list x4 ++ XBoxed_list x3 ++ XBoxed_list x0 ++ XBoxed_list x6 ++ [Box A] =
      (XBoxed_list x ++ XBoxed_list x2) ++ XBoxed_list x4 ++ XBoxed_list x3 ++ XBoxed_list x0 ++ XBoxed_list x6 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
      assert (Γ0 ++ B :: x1 ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ B :: x1) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ B :: x1 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ B :: x1) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (XBoxed_list (x ++ x0) ++ [Box A], A). exists ((Γ2 ++ Γ3) ++ B :: Γ1, C).  repeat split ; try apply list_exch_L_id. rewrite app_assoc.
           apply BoxImpLRule_I ; try apply univ_gen_ext_combine ; auto. }
        { simpl in e0. inversion e0. subst. simpl.
           apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc.
           exists (XBoxed_list (x1 ++ x ++ x3 ++ x4) ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6, C). repeat split.
           intro. intros. apply H2. repeat rewrite <- app_assoc. apply in_app_or in H. destruct H. apply in_or_app ; auto. apply in_app_or in H.
           destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H. destruct H.
           apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  auto.
          repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite XBox_app_distrib.
          repeat rewrite <- app_assoc.
          assert (XBoxed_list x1 ++ XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list x4 ++ [Box A] =
          XBoxed_list x1 ++ XBoxed_list x3 ++ [] ++ XBoxed_list x ++ XBoxed_list x4 ++ [Box A]). auto. rewrite H.
          assert (XBoxed_list x1 ++ XBoxed_list x ++ XBoxed_list x3 ++ XBoxed_list x4 ++ [Box A] =
          XBoxed_list x1 ++ XBoxed_list x ++ [] ++ XBoxed_list x3 ++ XBoxed_list x4 ++ [Box A]). auto. rewrite H0.
          apply list_exch_LI.
           assert (Γ2 ++ Γ3 ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * simpl in e0. inversion e0. subst.
         apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
         apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
         apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
        exists (XBoxed_list (x1 ++ x0 ++ x ++ x3 ++ x5) ++ [Box A], A). exists ((Γ2 ++ Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6, C). repeat split.
        assert (Γ2 ++ Γ5 ++ (Box A → B :: Γ4) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ Box A → B :: Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        apply BoxImpLRule_I ; auto. intro. intros. apply H2. repeat rewrite <- app_assoc. apply in_app_or in H0. destruct H0. apply in_or_app ; auto. apply in_app_or in H0.
         destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H0. destruct H0.
         apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H0. destruct H0.
         apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
        repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
        repeat rewrite <- app_assoc. apply list_exch_LI.
        assert ((Γ2 ++ Γ3) ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (B :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl.
           apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
           exists (XBoxed_list (x2 ++ x4 ++ x ++ x0) ++ [Box A], A). exists ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1, C). repeat split.
           assert (Γ2 ++ Γ4 ++ Γ3 ++ Box A → B :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ Box A → B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           apply BoxImpLRule_I ; auto.
           intro. intros. apply H2. repeat rewrite <- app_assoc. apply in_app_or in H0. destruct H0. apply in_or_app ; auto. apply in_app_or in H0.
           destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H0. destruct H0.
           apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  auto.
          repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite XBox_app_distrib.
          repeat rewrite <- app_assoc.
          assert (XBoxed_list x2 ++ XBoxed_list x4 ++ XBoxed_list x ++ XBoxed_list x0 ++ [Box A] =
          XBoxed_list x2 ++ XBoxed_list x4 ++ [] ++ XBoxed_list x ++ XBoxed_list x0 ++ [Box A]). auto. rewrite H.
          assert (XBoxed_list x2 ++ XBoxed_list x ++ XBoxed_list x4 ++ XBoxed_list x0 ++ [Box A] =
          XBoxed_list x2 ++ XBoxed_list x ++ [] ++ XBoxed_list x4 ++ XBoxed_list x0 ++ [Box A]). auto. rewrite H0.
          apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. simpl.
           apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
           exists (XBoxed_list (x2 ++ x3 ++ x4 ++ x ++ x5) ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
           intro. intros. apply H2. repeat rewrite <- app_assoc. apply in_app_or in H. destruct H. apply in_or_app ; auto. apply in_app_or in H.
           destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
           repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
           repeat rewrite <- app_assoc. apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc.
           apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
           exists(XBoxed_list (x1 ++ x5 ++ x3 ++ x ++ x0) ++ [Box A], A). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply BoxImpLRule_I ; auto.
           intro. intros. apply H2. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H. apply in_app_or in H. destruct H.
           apply in_or_app ; auto. apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
           repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
           repeat rewrite <- app_assoc. apply list_exch_LI. }
        {  repeat rewrite <- app_assoc.
           apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
           apply univ_gen_ext_splitR in u3. destruct u3. repeat destruct s. repeat destruct p. subst.
           exists (XBoxed_list (x1 ++ x4 ++ x3 ++ x ++ x6 ++ x0) ++ [Box A], A). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x2 ++ B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply BoxImpLRule_I ; auto.
           intro. intros. apply H2. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H. apply in_app_or in H. destruct H.
           apply in_or_app ; auto. apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H. destruct H.
           apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; right ; apply in_or_app ; auto.
           apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; right ; apply in_or_app ; auto.
           repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
           repeat rewrite <- app_assoc. apply list_exch_LI. }
        { destruct x2.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
              apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
              exists(XBoxed_list (x2 ++ x5 ++ x3 ++ x ++ x0) ++ [Box A], A). exists (Γ2 ++ x1 ++ Γ4 ++ Γ3 ++ B :: Γ1, C). repeat split.
              assert (Γ2 ++ x1 ++ Γ4 ++ Γ3 ++ B :: Γ1 = (Γ2 ++ x1 ++ Γ4 ++ Γ3) ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x1 ++ Γ4 ++ Γ3 ++ Box A → B :: Γ1 = (Γ2 ++ x1 ++ Γ4 ++ Γ3) ++ Box A → B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply BoxImpLRule_I ; auto.
              intro. intros. apply H2. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H. apply in_app_or in H1. destruct H1.
             apply in_or_app ; auto. apply in_app_or in H1. destruct H1. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
             apply in_app_or in H1. destruct H1. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
             apply in_app_or in H1. destruct H1. apply in_or_app ; right ; apply in_or_app ; auto.
             apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ;  auto.
             repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
             repeat rewrite <- app_assoc. apply list_exch_LI.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
              apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
              exists (XBoxed_list (x3 ++ x6 ++ x5 ++ x4 ++ x ++ x7) ++ [Box A], A). exists ((Γ2 ++ x1) ++ B :: x2 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
              assert (Γ2 ++ x1 ++ Box A → B :: x2 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x1) ++ Box A → B :: x2 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              apply BoxImpLRule_I ; auto.
              intro. intros. apply H2. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H. apply in_app_or in H0. destruct H0.
              apply in_or_app ; auto. apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H0. destruct H0.
              apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
              repeat rewrite <- app_assoc.
              assert (XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list x4 ++ XBoxed_list x6 ++ XBoxed_list x5 ++ XBoxed_list x7 ++ [Box A] =
              XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list x4 ++ (XBoxed_list x6 ++ XBoxed_list x5) ++ XBoxed_list x7 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (XBoxed_list x3 ++ XBoxed_list x6 ++ XBoxed_list x5 ++ XBoxed_list x4 ++ XBoxed_list x ++ XBoxed_list x7 ++ [Box A] =
              XBoxed_list x3 ++ (XBoxed_list x6 ++ XBoxed_list x5) ++ XBoxed_list x4 ++ XBoxed_list x ++ XBoxed_list x7 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x1 ++ B :: x2 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x1 ++ B :: x2) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x1) ++ B :: x2 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x1 ++ B :: x2) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
      * destruct x1.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
              apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
              exists (XBoxed_list (x1 ++ x4 ++ x ++ x0) ++ [Box A], A). exists (Γ2 ++ x2 ++ Γ3 ++ B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply BoxImpLRule_I ; repeat rewrite <- app_assoc.
              intro. intros. apply H2. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H. apply in_app_or in H. destruct H.
              apply in_or_app ; auto. apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
              repeat rewrite <- app_assoc.
              assert (XBoxed_list x1 ++ XBoxed_list x ++ XBoxed_list x4 ++ XBoxed_list x0 ++ [Box A] =
              XBoxed_list x1 ++ XBoxed_list x ++ [] ++ XBoxed_list x4 ++ XBoxed_list x0 ++ [Box A]). auto. rewrite H.
              assert (XBoxed_list x1 ++ XBoxed_list x4 ++ XBoxed_list x ++ XBoxed_list x0 ++ [Box A] =
              XBoxed_list x1 ++ XBoxed_list x4 ++ [] ++ XBoxed_list x ++ XBoxed_list x0 ++ [Box A]). auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x2 ++ B :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x2 ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x2 ++ Γ3 ++ B :: Γ1 = Γ2 ++ x2 ++ [] ++ Γ3 ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
              apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
              exists (XBoxed_list (x1 ++ x3 ++ x4 ++ x ++ x5) ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ x2 ++ Γ3 ++ Γ6, C). repeat split.
              intro. intros. apply H2. repeat rewrite <- app_assoc. apply in_app_or in H. destruct H.
              apply in_or_app ; auto. apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
              repeat rewrite <- app_assoc. apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x2 ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x2 ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B :: Γ5 ++ x2 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ x2 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst.
          apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u1. destruct u1. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u3. destruct u3. repeat destruct s. repeat destruct p. subst.
           exists (XBoxed_list (x3 ++ x0 ++ x5 ++ x4 ++ x ++ x7) ++ [Box A], A). exists ((Γ2 ++ Γ5 ++ x2) ++ B :: x1 ++ Γ3 ++ Γ6, C). repeat split.
           assert (Γ2 ++ Γ5 ++ (x2 ++ Box A → B :: x1) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x2) ++ Box A → B :: x1 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           apply BoxImpLRule_I ; auto.
            intro. intros. apply H2. repeat rewrite <- app_assoc. apply in_app_or in H0. destruct H0.
            apply in_or_app ; auto. apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
            apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
            apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
            apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; auto.
            apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
            repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
            repeat rewrite <- app_assoc.
            assert (XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list x5 ++ XBoxed_list x4 ++ XBoxed_list x0 ++ XBoxed_list x7 ++ [Box A] =
            XBoxed_list x3 ++ XBoxed_list x ++ (XBoxed_list x5 ++ XBoxed_list x4) ++ XBoxed_list x0 ++ XBoxed_list x7 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H.
            assert (XBoxed_list x3 ++ XBoxed_list x0 ++ XBoxed_list x5 ++ XBoxed_list x4 ++ XBoxed_list x ++ XBoxed_list x7 ++ [Box A] =
            XBoxed_list x3 ++ XBoxed_list x0 ++ (XBoxed_list x5 ++ XBoxed_list x4) ++ XBoxed_list x ++ XBoxed_list x7 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H0.
            apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ x2) ++ B :: x1 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x2 ++ B :: x1) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x2) ++ B :: x1 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x2 ++ B :: x1) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
  + destruct x2.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
              apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
              exists (XBoxed_list (x2 ++ x3 ++ x0) ++ [Box A], A). exists ((Γ2 ++ x1) ++ B :: Γ1, C). repeat split.
              assert (Γ2 ++ x1 ++ Box A → B :: Γ1 = (Γ2 ++ x1) ++ Box A → B :: Γ1). rewrite <- app_assoc ; auto. rewrite H. apply BoxImpLRule_I ; auto.
              rewrite <- app_assoc in H2. auto. repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto).
              repeat rewrite app_assoc. apply list_exch_L_id. repeat rewrite <- app_assoc. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
              apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
              apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
              exists (XBoxed_list (x2 ++ x ++ x3 ++ x4) ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ x1 ++ Γ6, C). repeat split.
              intro. intros. rewrite <- app_assoc in H2. apply H2. apply in_app_or in H. destruct H.
              apply in_or_app ; auto. apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_app_or in H. destruct H. apply in_or_app ; right ; apply in_or_app ; auto.
              apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
              repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
              repeat rewrite <- app_assoc.
              assert (XBoxed_list x2 ++ XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list x4 ++ [Box A] =
              XBoxed_list x2 ++ XBoxed_list x3 ++ [] ++ XBoxed_list x ++ XBoxed_list x4 ++ [Box A]). auto. rewrite H.
              assert (XBoxed_list x2 ++ XBoxed_list x ++ XBoxed_list x3 ++ XBoxed_list x4 ++ [Box A] =
              XBoxed_list x2 ++ XBoxed_list x ++ [] ++ XBoxed_list x3 ++ XBoxed_list x4 ++ [Box A]). auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ x1 ++ B :: Γ5 ++ Γ6 = Γ2 ++ x1 ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B :: Γ5 ++ x1 ++ Γ6 = Γ2 ++(B :: Γ5) ++ [] ++ x1 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
          apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
          exists (XBoxed_list (x2 ++ x0 ++ x ++ x3 ++ x5) ++ [Box A], A). exists ((Γ2 ++ Γ5) ++ B :: Γ4 ++ x1 ++ Γ6, C). repeat split.
          assert (Γ2 ++ Γ5 ++ Box A → B :: Γ4 ++ x1 ++ Γ6 = (Γ2 ++ Γ5) ++ Box A → B :: Γ4 ++ x1 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply BoxImpLRule_I ; auto.
          intro. intros. rewrite <- app_assoc in H2. apply H2. apply in_app_or in H0. destruct H0.
          apply in_or_app ; auto. apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
          repeat rewrite <- app_assoc. apply list_exch_LI.
          assert (Γ2 ++ x1 ++ B :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x1 ++ (B :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ B :: Γ4 ++ x1 ++ Γ6 = Γ2 ++ Γ5 ++ (B :: Γ4) ++ x1 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
          apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u2. destruct u2. repeat destruct s. repeat destruct p. subst.
          apply univ_gen_ext_splitR in u3. destruct u3. repeat destruct s. repeat destruct p. subst.
          exists (XBoxed_list (x3 ++ x5 ++ x0 ++ x4 ++ x ++ x7) ++ [Box A], A). exists ((Γ2 ++ Γ5 ++ Γ4 ++ x1) ++ B :: x2 ++ Γ6, C). repeat split.
          assert (Γ2 ++ Γ5 ++ Γ4 ++ x1 ++ Box A → B :: x2 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x1) ++ Box A → B :: x2 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply BoxImpLRule_I ; auto.
          intro. intros. rewrite <- app_assoc in H2. apply H2. apply in_app_or in H0. destruct H0.
          apply in_or_app ; auto. apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_app_or in H0. destruct H0. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
          repeat rewrite <- app_assoc. repeat (apply univ_gen_ext_combine ; auto). repeat rewrite <- app_assoc. repeat rewrite XBox_app_distrib.
          repeat rewrite <- app_assoc.
          assert (XBoxed_list x3 ++ XBoxed_list x4 ++ XBoxed_list x ++ XBoxed_list x0 ++ XBoxed_list x5 ++ XBoxed_list x7 ++ [Box A] =
          XBoxed_list x3 ++ (XBoxed_list x4 ++ XBoxed_list x) ++ XBoxed_list x0 ++ XBoxed_list x5 ++ XBoxed_list x7 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (XBoxed_list x3 ++ XBoxed_list x5 ++ XBoxed_list x0 ++ XBoxed_list x4 ++ XBoxed_list x ++ XBoxed_list x7 ++ [Box A] =
          XBoxed_list x3 ++ XBoxed_list x5 ++ XBoxed_list x0 ++ (XBoxed_list x4 ++ XBoxed_list x) ++ XBoxed_list x7 ++ [Box A]). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ2 ++ x1 ++ B :: x2 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x1 ++ B :: x2) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x1) ++ B :: x2 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x1 ++ B :: x2) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
Qed.

Lemma GLR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (GLRRule [ps] s) ->
  (existsT2 pse,
    (GLRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. inversion exch. rewrite <- H1 in H2.
inversion H2. subst.
pose (@nobox_gen_ext_exch_L (Box A) A BΓ (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4) X exch).
destruct s. destruct p. inversion l.
exists (XBoxed_list (Γ5 ++ Γ8 ++ Γ7 ++ Γ6 ++ Γ9) ++ [Box A], A). split.
- apply GLRRule_I.
  * unfold is_Boxed_list. intros. apply in_exch_list in H4. subst. apply H0 in H4.
    assumption.
  * subst. assumption.
- repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply list_exch_LI.
Qed.

(* We can now prove that exchange is height-preserving admissible. *)

Theorem GL4ip_hpadm_list_exch_L : forall (k : nat) s
                                  (D0: derrec GL4ip_rules (fun _ => False) s),
        k = (derrec_height D0) ->
        (forall se, (list_exch_L s se) ->
        (existsT2 (D1 : derrec GL4ip_rules (fun _ => False) se),
          derrec_height D1 <=k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : list (MPropF) * (MPropF))
  (D0 : derrec GL4ip_rules (fun _ : list (MPropF) * (MPropF) => False) s),
x = derrec_height D0 ->
(forall se,
(list_exch_L s se) ->
(existsT2
  D1 : derrec GL4ip_rules
         (fun _ : list (MPropF) * (MPropF) => False) se,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 ip a leaf *)
- inversion f.
(* D0 is ends with an application of rule *)
- intros hei se exch. inversion exch.
  assert (DersNil: dersrec GL4ip_rules (fun _ : list (MPropF) * (MPropF) => False) []).
  apply dersrec_nil. inversion g.
  (* IdP *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In # P (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In # P (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (IdPRule [] (x ++ # P :: x0, # P)). apply IdPRule_I. apply IdP in H.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[]) (x ++ # P :: x0, # P) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* BotL *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In (Bot) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In (Bot) (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (BotLRule [] (x ++ Bot :: x0, A)). apply BotLRule_I. apply BotL in H.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[]) (x ++ Bot :: x0, A) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
 (* AndR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AndR_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply AndR in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, A0) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, B) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A0 ∧ B) a d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AndL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AndL_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply AndL in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 :: B :: Γ6, A) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrR1 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrR1_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply OrR1 in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, A0) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A0 ∨ B) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrR2 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrR2_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply OrR2 in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, B) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A0 ∨ B) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrL_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply OrL in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ5 ++ A0 :: Γ6, A) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ B :: Γ6, A) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) o d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpR_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply ImpR in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 :: Γ6, B) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Imp A0 B) i d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AtomImpL1 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AtomImpL1_app_list_exchL _ _ _ exch H1). destruct s. destruct p. destruct s.
   + apply AtomImpL1 in  a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ # P :: Γ6 ++ A0 :: Γ7, A) x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
   + apply AtomImpL2 in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ # P :: Γ6 ++ A0 :: Γ7, A) x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AtomImpL2 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AtomImpL2_app_list_exchL _ _ _ exch H1). destruct s. destruct p. destruct s.
   + apply AtomImpL2 in  a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ A0 :: Γ6 ++ # P :: Γ7, A) x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
   + apply AtomImpL1 in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ A0 :: Γ6 ++ # P :: Γ7, A)x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AndImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AndImpL_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply AndImpL in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 → B → C :: Γ6, A) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrImpL_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply OrImpL in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s0.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    destruct s.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 → C :: Γ6 ++ B → C :: Γ7, A) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
    destruct s. destruct p.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 → C :: Γ6 ++ B → C :: Γ7, A) x0 E1 x1 l). destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 x1 x2 E3 x l0).
    destruct s. pose (dlCons x3 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpImpL_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply ImpImpL in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ5 ++ B → C :: Γ6, A0 → B) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ C :: Γ6, A) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) i d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* BoxImpL *)
  * inversion X. subst. inversion H5. subst. simpl. simpl in IH.
    pose (BoxImpL_app_list_exchL _ _ _ _ exch X). repeat destruct s. repeat destruct p.
    apply BoxImpL in b. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (XBoxed_list BΓ ++ [Box A0], A0) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ B :: Γ6, A) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) b d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* GLR *)
  * inversion X. subst. inversion H5. subst. simpl. simpl in IH.
    pose (GLR_app_list_exchL _ _ _ exch X). destruct s. destruct p.
    apply GLR in g0. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (XBoxed_list BΓ ++ [Box A0], A0) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Box A0) g0 d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
Qed.

Theorem GL4ip_adm_list_exch_L : forall s,
        (derrec GL4ip_rules (fun _ => False) s) ->
        (forall se, (@list_exch_L s se) ->
        (derrec GL4ip_rules (fun _ => False) se)).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). auto.
pose (GL4ip_hpadm_list_exch_L (derrec_height X) s X J1 se H). destruct s0. auto.
Qed.

Definition exch s se := @list_exch_L s se.

Lemma GL4ip_adm_exch : forall s,
        (GL4ip_prv s) ->
        (forall se, (exch s se) ->
        (GL4ip_prv se)).
Proof.
unfold exch. unfold GL4ip_prv. apply GL4ip_adm_list_exch_L.
Qed.
