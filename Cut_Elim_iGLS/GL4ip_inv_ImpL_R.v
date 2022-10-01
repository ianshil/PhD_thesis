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
Require Import GL4ip_exch.
Require Import GL4ip_wkn.
Require Import GL4ip_PSGL4ip_remove_list.
Require Import GL4ip_PSGL4ip_dec.
Require Import GL4ip_inv_AndR_AndL.
Require Import GL4ip_inv_OrL.
Require Import GL4ip_inv_AtomImpL.
Require Import GL4ip_inv_AndImpL.
Require Import GL4ip_inv_OrImpL.
Require Import GL4ip_inv_ImpImpL_R.
Require Import GL4ip_inv_BoxImpL_R.
Require Import GL4ip_ctr.
Require Import Lia.

Theorem ImpL_hpinv_R : forall (m k : nat) s (D0: derrec GL4ip_rules (fun _ => False) s) A B Γ0 Γ1 C,
        m = (weight_form (Imp A B)) ->
        k = (derrec_height D0) ->
        (s = (Γ0 ++ Imp A B :: Γ1, C)) ->
        derrec GL4ip_rules (fun _ => False) (Γ0 ++ B :: Γ1, C).
Proof.
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the weight. *)
pose (strong_inductionT (fun (x:nat) => forall k s (D0 : derrec GL4ip_rules (fun _ => False) s) A B Γ0 Γ1 C,
        x = (weight_form (Imp A B)) ->
        k = (derrec_height D0) ->
        (s = (Γ0 ++ Imp A B :: Γ1, C)) ->
        derrec GL4ip_rules (fun _ => False) (Γ0 ++ B :: Γ1, C))).
apply d. intros n PIH. clear d.

(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall s (D0 : derrec GL4ip_rules (fun _ => False) s) A B Γ0 Γ1 C,
        n = weight_form (Imp A B) ->
        x = (derrec_height D0) ->
        (s = (Γ0 ++ Imp A B :: Γ1, C)) ->
        derrec GL4ip_rules (fun _ => False) (Γ0 ++ B :: Γ1, C))).
apply d. intros m SIH. clear d.

(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros A B Γ0 Γ1 C wei hei eq. inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ A → B :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x ++ # P :: x0, # P)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). auto.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ A → B :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, C) H1 DersNilF). auto.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    simpl in PIH. simpl in SIH.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ A → B :: Γ1, A0) = (Γ0 ++ A → B :: Γ1, A0)). auto.
    assert (J40: S (weight_form A + weight_form B) = S (weight_form A + weight_form B)). auto.
    pose (SIH _ J2 _ x _ _ _ _ _ J40 J3 J4).
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J7 : (Γ0 ++ A → B :: Γ1, B0) = (Γ0 ++ A → B :: Γ1, B0)). auto.
    pose (SIH _ J5 _ x0 _ _ _ _ _ J40 J6 J7).
    assert (AndRRule [(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)]
    (Γ0 ++ B :: Γ1, A0 ∧ B0)). apply AndRRule_I. pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
    apply AndR in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
   (ps:=[(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)])
    (Γ0 ++ B :: Γ1, And A0 B0) H0 d3). auto.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [A → B]) ++ x0) ++ A0 :: B0 :: Γ3, C) = (Γ0 ++ A → B :: x0 ++ A0 :: B0 :: Γ3, C)).
      repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
      assert (AndLRule [((Γ0 ++ B :: x0) ++ A0 :: B0 :: Γ3, C)]
       ((Γ0 ++ B :: x0) ++ A0 ∧ B0 :: Γ3, C)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       pose (dlCons d0 DersNilF). apply AndL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x0 ++ A0 :: B0 :: Γ3, C)])
       (Γ0 ++ B :: x0 ++ A0 ∧ B0 :: Γ3, C) H0 d1). auto.
  +  repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 : (Γ2 ++ A0 :: B0 :: x ++ A → B :: Γ1, C) = ((Γ2 ++ A0 :: B0 :: x) ++ A → B :: Γ1, C)).
      repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x0 _ _ _ _ _ J70 J3 J4).
      pose (dlCons d0 DersNilF).
      assert (AndLRule [((Γ2 ++ A0 :: B0 :: x) ++ B :: Γ1, C)]
       ((Γ2 ++ A0 ∧ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
       apply AndL in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: B0 :: x) ++ B :: Γ1, C)])
      ((Γ2 ++ A0 ∧ B0 :: x) ++ B :: Γ1, C) H0 d1). auto.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ A → B :: Γ1, A0) = (Γ0 ++ A → B :: Γ1, A0)). auto.
    assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
    pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
    assert (OrR1Rule [(Γ0 ++ B :: Γ1, A0)]
    (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons d0 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ B :: Γ1, A0)])
    (Γ0 ++ B  :: Γ1, Or A0 B0) H0 d1). auto.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ A → B :: Γ1, B0) = (Γ0 ++ A → B :: Γ1, B0)). auto.
    assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
    pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
    assert (OrR2Rule [(Γ0 ++ B :: Γ1, B0)]
    (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons d0 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ B :: Γ1, B0)])
    (Γ0 ++ B  :: Γ1, Or A0 B0) H0 d1). auto.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [A → B]) ++ x0) ++ A0 :: Γ3, C) = (Γ0 ++ A → B :: (x0 ++ A0 :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (((Γ0 ++ [A → B]) ++ x0) ++ B0 :: Γ3, C) = (Γ0 ++ A → B :: (x0 ++ B0 :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      pose (SIH _ J5 _ x1 _ _ _ _ _ J70 J6 J7).
      assert (OrLRule [((Γ0 ++ B :: x0) ++ A0 :: Γ3, C);((Γ0 ++ B :: x0) ++ B0 :: Γ3, C)]
      ((Γ0 ++ B :: x0) ++ A0 ∨ B0 :: Γ3, C)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ B :: x0 ++ A0 :: Γ3, C); (Γ0 ++ B :: x0 ++ B0 :: Γ3, C)])
      (Γ0 ++ B :: x0 ++ A0 ∨ B0 :: Γ3, C) H0 d3). auto.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 :(Γ2 ++ A0 :: x ++ A → B :: Γ1, C) = ((Γ2 ++ A0 :: x) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x0 _ _ _ _ _ J70 J3 J4).
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (Γ2 ++ B0 :: x ++ A → B :: Γ1, C) = ((Γ2 ++ B0 :: x) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      pose (SIH _ J5 _ x1 _ _ _ _ _ J70 J6 J7).
      assert (OrLRule [((Γ2 ++ A0 :: x) ++ B :: Γ1, C);((Γ2 ++ B0 :: x) ++ B :: Γ1, C)]
      ((Γ2 ++ A0 ∨ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply OrLRule_I. apply OrL in H0.
      pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: x) ++ B :: Γ1, C); ((Γ2 ++ B0 :: x) ++ B :: Γ1, C)])
      ((Γ2 ++ A0 ∨ B0 :: x) ++ B :: Γ1, C) H0 d3). auto.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J50: derrec_height x = derrec_height x). auto.
    assert (J51: list_exch_L (Γ2 ++ A0 :: Γ3, B0) (A0 :: Γ0 ++ A → B :: Γ1, B0)).
    assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). auto. rewrite H0.
    assert (A0 :: Γ0 ++ A → B :: Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). rewrite <- H2. auto. rewrite H1.
    apply list_exch_LI.
    pose (GL4ip_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J4: (A0 :: Γ0 ++ A → B :: Γ1, B0) = ((A0 :: Γ0) ++ A → B :: Γ1, B0)). repeat rewrite <- app_assoc. auto.
    assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
    pose (SIH _ J2 _ x0 _ _ _ _ _ J70 J3 J4).
    assert (ImpRRule [(([] ++ A0 :: Γ0) ++ B :: Γ1, B0)] ([] ++ Γ0 ++ B :: Γ1, A0 → B0)). repeat rewrite <- app_assoc. apply ImpRRule_I.
    simpl in H0. apply ImpR in H0. pose (dlCons d0 DersNilF).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[((A0 :: Γ0) ++ B :: Γ1, B0)]) (Γ0 ++ B :: Γ1, A0 → B0) H0 d1). auto.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ # P :: Γ3 ++ A0 :: Γ4, C) = (Γ0 ++ A → B :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AtomImpL1Rule [((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)). apply AtomImpL1Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL1 in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)])
       (Γ0 ++ B :: x1 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C) H0 d1). auto.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. subst. repeat rewrite <- app_assoc. auto. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P :: ((x0 ++ [A → B]) ++ x2) ++ A0 :: Γ4, C) = ((Γ2 ++ # P :: x0) ++ A → B :: x2 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL1Rule [((Γ2 ++ # P :: x0) ++ B :: x2 ++ A0 :: Γ4, C)]
         ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4, C)).
         assert ((Γ2 ++ # P :: x0) ++ B :: x2 ++ A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ B :: x2) ++ A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ B :: x2) ++ # P → A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P :: x0) ++ B :: x2 ++ A0 :: Γ4, C)])
         ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4, C) H0 d1). auto. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A → B :: Γ1, C) = ((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ A → B :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL1Rule [((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ B :: Γ1, C)]
         ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ B :: Γ1, C)])
         ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ B :: Γ1, C) H0 d1). auto. }
  (* AtomImpL2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1 ; subst. auto.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ A0 :: Γ3 ++ # P :: Γ4, C) = (Γ0 ++ A → B :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AtomImpL2Rule [((Γ0 ++ B :: x1) ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL2 in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)])
       (Γ0 ++ B :: x1 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C) H0 d1). auto.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: ((x0 ++ [A → B]) ++ x2) ++ # P :: Γ4, C) = ((Γ2 ++ A0 :: x0) ++ A → B :: x2 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C)]
         ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C)).
         assert ((Γ2 ++ A0 :: x0) ++ B :: x2 ++ # P :: Γ4 = Γ2 ++ A0 :: (x0 ++ B :: x2) ++ # P :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P  :: Γ4 = Γ2 ++ # P → A0 :: (x0 ++ B :: x2) ++ # P :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C)])
         ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C) H0 d1). auto. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ A → B :: Γ1, C) = ((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ A → B :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C)]
         ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C)])
         ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C) H0 d1). auto. }
 (* AndImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ0 ++ A0 → B0 → B :: Γ1, C) = (Γ0 ++ A0 → B0 → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J71: weight_form (A0 → B0 → B) < weight_form ((A0 ∧ B0) → B)). simpl ; lia.
       assert (J72: weight_form (A0 → B0 → B) = weight_form (A0 → (B0 → B))). auto.
       pose (PIH _ J71 _ _ _ _ _ _ _ _ J72 J3 J4).
       assert (J6: derrec_height d0 = derrec_height d0). reflexivity.
       assert (J7: (Γ0 ++ B0 → B :: Γ1, C) = (Γ0 ++ B0 → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J73: weight_form (B0 → B) < weight_form ((A0 ∧ B0) → B)). simpl ; lia.
       assert (J74: weight_form (B0 → B) = weight_form (B0 → B)). auto.
       pose (PIH _ J73 _ _ _ _ _ _ _ _ J74 J6 J7). auto.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ A0 → B0 → C0 :: Γ3, C) = (Γ0 ++ A → B :: x1 ++ A0 → B0 → C0 :: Γ3, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AndImpLRule [((Γ0 ++ B :: x1) ++ A0 → B0 → C0 :: Γ3, C)]
       ((Γ0 ++ B :: x1) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply AndImpL in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ A0 → B0 → C0 :: Γ3, C)])
       (Γ0 ++ B :: x1 ++ (A0 ∧ B0) → C0 :: Γ3, C) H0 d1). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ A0 → B0 → C0 :: x0 ++ A → B :: Γ1, C) = ((Γ2 ++ A0 → B0 → C0 :: x0) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AndImpLRule [((Γ2 ++ A0 → B0 → C0 :: x0) ++ B :: Γ1, C)]
       ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
       apply AndImpL in H0. pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → B0 → C0 :: x0) ++ B :: Γ1, C)])
       ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ B :: Γ1, C) H0 d1). auto.
  (* OrImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ0 ++ A0 → B :: Γ3 ++ B0 → B :: Γ4, C) = (Γ0 ++ A0 → B :: Γ3 ++ B0 → B :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J73: weight_form (A0 → B) < weight_form ((A0 ∨ B0) → B)). simpl ; lia.
       assert (J74: weight_form (A0 → B) = weight_form (A0 → B)). auto.
       pose (PIH _ J73 _ _ _ _ _ _ _ _ J74 J3 J4).
       assert (J6: derrec_height d0 = derrec_height d0). reflexivity.
       assert (J7: (Γ0 ++ B :: Γ3 ++ B0 → B :: Γ4, C) = ((Γ0 ++ B :: Γ3) ++ B0 → B :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J71: weight_form (B0 → B) < weight_form ((A0 ∨ B0) → B)). simpl ; lia.
       assert (J72: weight_form (B0 → B) = weight_form (B0 → B)). auto.
       pose (PIH _ J71 _ _ _ _ _ _ _ _ J72 J6 J7).
       assert (J8: ctr_L B ((Γ0 ++ B :: Γ3) ++ B :: Γ4, C) (Γ0 ++ B :: Γ3 ++ Γ4, C)). repeat rewrite <- app_assoc ; simpl.
       apply ctr_LI.
       assert (J9: derrec_height d1 = derrec_height d1). auto.
       assert (J10: weight_form B = weight_form B). auto.
       pose (@GL4ip_ctr_L _ _ _ _ J9 _ _ J10 J8). auto.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) = (Γ0 ++ A → B ::  x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (OrImpLRule [((Γ0 ++ B :: x1) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply OrImpL in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)])
       (Γ0 ++ B :: x1 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C) H0 d1). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J50: derrec_height x = derrec_height x). auto.
       assert (J51: list_exch_L (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++ A → B :: Γ1, C)).
       assert (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4 = (Γ2 ++ [A0 → C0]) ++ [] ++ Γ3 ++ [B0 → C0] ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++ A → B :: Γ1 = (Γ2 ++ [A0 → C0]) ++ [B0 → C0] ++ Γ3 ++ [] ++ Γ4).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
       assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
       assert (J4: (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++ A → B :: Γ1, C) = ((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x1 _ _ _ _ _ J70 J3 J4).
       assert (OrImpLRule [((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ B :: Γ1, C)]
       ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1, C)).
       assert ((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ B :: Γ1 = Γ2 ++ A0 → C0 :: [] ++ B0 → C0 :: x0 ++ B :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
       assert ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1 = Γ2 ++ (A0 ∨ B0) → C0 :: [] ++ x0 ++ B :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
       apply OrImpLRule_I.  apply OrImpL in H0. pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ B :: Γ1, C)])
       ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1, C) H0 d1). auto.
  (* ImpImpL *)
 * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       pose (derI (Γ0 ++ (A0 → B0) → B :: Γ1, C) g d).
       assert (J40: derrec_height d0 = derrec_height d0). auto.
       pose (ImpImpL_hpinv_R _ _ _ J40 _ _ H). destruct s. auto.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x2) ++ B0 → C0 :: Γ3, A0 → B0) = (Γ0 ++ A → B :: x2 ++ B0 → C0 :: Γ3, A0 → B0)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [A → B]) ++ x2) ++ C0 :: Γ3, C) = (Γ0 ++ A → B :: x2 ++ C0 :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       assert (ImpImpLRule [((Γ0 ++ B :: x2) ++ B0 → C0 :: Γ3, A0 → B0);((Γ0 ++ B :: x2) ++ C0 :: Γ3, C)]
       ((Γ0 ++ B :: x2) ++ (A0 → B0) → C0 :: Γ3, C)). apply ImpImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply ImpImpL in H0.
       pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x2 ++ B0 → C0 :: Γ3, A0 → B0); (Γ0 ++ B :: x2 ++ C0 :: Γ3, C)])
       (Γ0 ++ B :: x2 ++ (A0 → B0) → C0 :: Γ3, C) H0 d3). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ B0 → C0 :: x1 ++ A → B :: Γ1, A0 → B0) = ((Γ2 ++ B0 → C0 :: x1) ++ A → B :: Γ1, A0 → B0)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ C0 :: x1 ++ A → B :: Γ1, C) = ((Γ2 ++ C0 :: x1) ++ A → B :: Γ1, C)).
       repeat rewrite <- app_assoc. auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       assert (ImpImpLRule [((Γ2 ++ B0 → C0 :: x1) ++ B :: Γ1, A0 → B0);((Γ2 ++ C0 :: x1) ++ B :: Γ1, C)]
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
       apply ImpImpL in H0. pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ B0 → C0 :: x1) ++ B :: Γ1, A0 → B0); ((Γ2 ++ C0 :: x1) ++ B :: Γ1, C)])
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ B :: Γ1, C) H0 d3). auto.
  (* BoxImpL *)
 * inversion X. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    apply list_split_form in H. destruct H. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       pose (derI (Γ0 ++ Box A0 → B :: Γ1, C) g d).
       assert (J40: derrec_height d0 = derrec_height d0). auto.
       pose (BoxImpL_hpinv_R _ _ _ J40 _ _ X). destruct s. auto.
   +  apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
       apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
       inversion u2. subst. exfalso. assert (In (A → B) (((x1 ++ A → B :: l) ++ x5) ++ x2)).
       apply in_or_app ; left ; apply in_or_app ; left ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst. inversion X0. subst.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [A → B]) ++ x4) ++ B0 :: Γ3, C) = (Γ0 ++ A → B :: x4 ++ B0 :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       destruct (dec_is_boxedT B).
       { assert (existsT2 (D1 : derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list x1 ++ XBoxed_list (x5 ++ x2) ++ [Box A0], A0)),
          derrec_height D1 = derrec_height x).
          assert (XBoxed_list x1 ++ XBoxed_list (x5 ++ x2) ++ [Box A0] = XBoxed_list (((x1 ++ []) ++ x5) ++ x2) ++ [Box A0]).
          repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc ; auto. rewrite H.
          exists x ; auto. destruct X1. symmetry in e0.
          pose (@GL4ip_list_wkn_L (derrec_height x) (XBoxed_list x1) (XBoxed_list (x5 ++ x2) ++ [Box A0]) A0 x3 e0 [unBox_formula B ; B]).
          destruct s.
          assert (BoxImpLRule [(XBoxed_list x1 ++ [unBox_formula B; B] ++ XBoxed_list (x5 ++ x2) ++ [Box A0], A0);((Γ0 ++ B :: x4) ++ B0 :: Γ3, C)]
          ((Γ0 ++ B :: x4) ++ Box A0 → B0 :: Γ3, C)).
          assert (XBoxed_list x1 ++ [unBox_formula B; B] ++ XBoxed_list (x5 ++ x2) ++ [Box A0] = XBoxed_list (x1 ++ B :: x5 ++ x2) ++ [Box A0]).
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. auto.
           rewrite H. apply BoxImpLRule_I. intro. intros. apply in_app_or in H0. repeat rewrite <- app_assoc in H1.
           simpl in H1. destruct H0. apply H1. apply in_or_app ; auto. inversion H0 ; subst. destruct i. exists x7 ; subst ; auto.
           apply in_app_or in H3. destruct H3. apply H1. apply in_or_app ; right ; apply in_or_app ; auto.
           apply H1. apply in_or_app ; right ; apply in_or_app ; auto. repeat rewrite <- app_assoc.
           apply univ_gen_ext_combine ; auto. simpl. apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
           repeat rewrite <- app_assoc in X1. apply BoxImpL in X1.
           pose (dlCons d0 DersNilF). pose (dlCons x6 d1).
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list x1 ++ [unBox_formula B; B] ++ XBoxed_list (x5 ++ x2) ++ [Box A0], A0); (Γ0 ++ B :: x4 ++ B0 :: Γ3, C)])
           (Γ0 ++ B :: x4 ++ Box A0 → B0 :: Γ3, C) X1 d2). auto. }
       { assert (BoxImpLRule [(XBoxed_list (((x1 ++ []) ++ x5) ++ x2) ++ [Box A0], A0);((Γ0 ++ B :: x4) ++ B0 :: Γ3, C)]
          ((Γ0 ++ B :: x4) ++ Box A0 → B0 :: Γ3, C)).
          apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_combine ; auto.
          apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto.
           assert ((Γ0 ++ B :: x4) ++ B0 :: Γ3 = Γ0 ++ B :: x4 ++ B0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H in X1.
           assert ((Γ0 ++ B :: x4) ++ Box A0 → B0 :: Γ3 = Γ0 ++ B :: x4 ++ Box A0 → B0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H0 in X1.
           pose (dlCons d0 DersNilF). pose (dlCons x d1). apply BoxImpL in X1.
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list (((x1 ++ []) ++ x5) ++ x2) ++ [Box A0], A0); (Γ0 ++ B :: x4 ++ B0 :: Γ3, C)])
           (Γ0 ++ B :: x4 ++ Box A0 → B0 :: Γ3, C) X1 d2). auto. }
   +  repeat destruct s. repeat destruct p ; subst.
       apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
       inversion u1. subst. exfalso. assert (In (A → B) (x1 ++ x4 ++ A → B :: l)).
       apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ B0 :: x3 ++ A → B :: Γ1, C) = ((Γ2 ++ B0 :: x3) ++ A → B :: Γ1, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       destruct (dec_is_boxedT B).
       { assert (existsT2 (D1 : derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list (x1 ++ x4) ++ XBoxed_list  x5 ++ [Box A0], A0)),
          derrec_height D1 = derrec_height x).
          assert (XBoxed_list (x1 ++ x4) ++ XBoxed_list x5 ++ [Box A0] = XBoxed_list (x1++ x4 ++ x5) ++ [Box A0]).
          repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc ; auto. rewrite H.
          exists x ; auto. destruct X1. symmetry in e0.
          pose (@GL4ip_list_wkn_L (derrec_height x) (XBoxed_list (x1 ++ x4)) (XBoxed_list x5 ++ [Box A0]) A0 x2 e0 [unBox_formula B ; B]).
          destruct s.
          assert (BoxImpLRule [(XBoxed_list (x1 ++ x4) ++ [unBox_formula B; B] ++ XBoxed_list x5 ++ [Box A0], A0);((Γ2 ++ B0 :: x3) ++ B :: Γ1, C)]
          ((Γ2 ++ Box A0 → B0 :: x3) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl.
          assert (XBoxed_list (x1 ++ x4) ++ unBox_formula B :: B :: XBoxed_list x5 ++ [Box A0] = XBoxed_list (x1 ++ x4 ++ B :: x5) ++ [Box A0]).
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. auto.
           rewrite H. apply BoxImpLRule_I. intro. intros. apply in_app_or in H0. repeat rewrite <- app_assoc in H1.
           simpl in H1. destruct H0. apply H1. apply in_or_app ; auto.
           apply in_app_or in H0. destruct H0. apply H1. apply in_or_app ; right ; apply in_or_app ; auto.
           inversion H0 ; subst. destruct i. exists x7 ; subst ; auto.
           apply H1. apply in_or_app ; right ; apply in_or_app ; auto.
           apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
           apply BoxImpL in X1.
           pose (dlCons d0 DersNilF). pose (dlCons x6 d1).
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list (x1 ++ x4) ++ [unBox_formula B; B] ++ XBoxed_list x5 ++ [Box A0], A0); ((Γ2 ++ B0 :: x3) ++ B :: Γ1, C)])
           ((Γ2 ++ Box A0 → B0 :: x3) ++ B :: Γ1, C) X1 d2). auto. }
       { assert (BoxImpLRule [(XBoxed_list (x1 ++ x4 ++ x5) ++ [Box A0], A0);((Γ2 ++ B0 :: x3) ++ B :: Γ1, C)]
          ((Γ2 ++ Box A0 → B0 :: x3) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl.
          apply BoxImpLRule_I ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto.
          apply univ_gen_ext_extra ; auto. apply BoxImpL in X1.
           pose (dlCons d0 DersNilF). pose (dlCons x d1).
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list (x1 ++ x4 ++ x5) ++ [Box A0], A0); ((Γ2 ++ B0 :: x3) ++ B :: Γ1, C)])
           ((Γ2 ++ Box A0 → B0 :: x3) ++ B :: Γ1, C) X1 d2). auto. }
  (* GLR *)
  * inversion X. subst. simpl. apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    inversion u0. subst. exfalso. assert (In (A → B) (x ++ A → B :: l)). apply in_or_app ; right ; apply in_eq.
    apply H1 in H. destruct H. inversion H. subst.
    assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A0], A0)] (Γ0 ++ Γ1, Box A0)). apply GLRRule_I ; auto.
    apply univ_gen_ext_combine ; auto. apply GLR in X1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(XBoxed_list (x ++ x0) ++ [Box A0], A0)]) (Γ0 ++ Γ1, Box A0) X1 d).
    assert (J1: derrec_height d0 = derrec_height d0). auto.
    assert (J2: wkn_L B (Γ0 ++ Γ1, Box A0) (Γ0 ++ B :: Γ1, Box A0)). apply wkn_LI.
    pose (@GL4ip_wkn_L (derrec_height d0) _ d0 J1 (Γ0 ++ B :: Γ1, Box A0) B J2). destruct s. auto.
Qed.

Theorem ImpL_inv_R : forall A B Γ0 Γ1 C, derrec GL4ip_rules (fun _ => False) (Γ0 ++ Imp A B :: Γ1, C) ->
                  derrec GL4ip_rules (fun _ => False) (Γ0 ++ B :: Γ1, C).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). auto.
assert (J2: (Γ0 ++ A → B :: Γ1, C) = (Γ0 ++ A → B :: Γ1, C)). auto.
assert (J3: weight_form (A → B) = weight_form (A → B)). auto.
pose (ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J3 J1 J2). auto.
Qed.

