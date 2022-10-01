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
Require Import GL4ip_ImpL_adm.
Require Import GL4ip_inv_ImpR.
Require Import Lia.


Theorem ImpImpL_inv_L :  forall n s (D0 : derrec GL4ip_rules (fun _ => False) s) A B C D Γ0 Γ1,
                              (n = derrec_height D0) ->
                              (s = (Γ0 ++ (A  → B) → D :: Γ1, C)) ->
                              derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: B → D :: B → D :: Γ1, C).
Proof.
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall s (D0 : derrec GL4ip_rules (fun _ => False) s) A B C D Γ0 Γ1,
                              (x = derrec_height D0) ->
                              (s = (Γ0 ++ (A  → B) → D :: Γ1, C)) ->
                              derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: B → D :: B → D :: Γ1, C))).
apply d. intros n IH. clear d.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros A B C D Γ0 Γ1 hei eq. inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++  (A  → B) → D :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++ A :: B → D :: B → D :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right. inversion i.
    subst. inversion H1. subst. repeat apply InT_cons. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x ++ # P :: x0, # P)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). auto.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++  (A  → B) → D :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ A :: B → D :: B → D :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right. inversion i.
    subst. inversion H1. subst. repeat apply InT_cons. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, C) H1 DersNilF). auto.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    simpl in IH.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++  (A  → B) → D :: Γ1, A0) = (Γ0 ++  (A  → B) → D :: Γ1, A0)). auto.
    pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J7 : (Γ0 ++  (A  → B) → D :: Γ1, B0) = (Γ0 ++  (A  → B) → D :: Γ1, B0)). auto.
    pose (IH _ J5 _ x0 _ _ _ _ _ _ J6 J7).
    assert (AndRRule [(Γ0 ++ A :: B → D :: B → D :: Γ1, A0); (Γ0 ++ A :: B → D :: B → D :: Γ1, B0)]
    (Γ0 ++ A :: B → D :: B → D :: Γ1, A0 ∧ B0)). apply AndRRule_I. pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
    apply AndR in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
   (ps:=[(Γ0 ++ A :: B → D :: B → D :: Γ1, A0); (Γ0 ++ A :: B → D :: B → D :: Γ1, B0)])
    (Γ0 ++ A :: B → D :: B → D :: Γ1, A0 ∧ B0) H0 d3). auto.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [ (A  → B) → D]) ++ x0) ++ A0 :: B0 :: Γ3, C) = (Γ0 ++  (A  → B) → D :: x0 ++ A0 :: B0 :: Γ3, C)).
      repeat rewrite <- app_assoc. auto.
      pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
      assert (AndLRule [((Γ0 ++ A :: B → D :: B → D :: x0) ++ A0 :: B0 :: Γ3, C)]
       ((Γ0 ++ A :: B → D :: B → D :: x0) ++ A0 ∧ B0 :: Γ3, C)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       pose (dlCons d0 DersNilF). apply AndL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: B → D :: B → D :: x0 ++ A0 :: B0 :: Γ3, C)])
       (Γ0 ++ A :: B → D :: B → D :: x0 ++ A0 ∧ B0 :: Γ3, C) H0 d1). auto.
  +  repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 : (Γ2 ++ A0 :: B0 :: x ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ A0 :: B0 :: x) ++  (A  → B) → D :: Γ1, C)).
      repeat rewrite <- app_assoc. auto. pose (IH _ J2 _ x0 _ _ _ _ _ _ J3 J4).
      pose (dlCons d0 DersNilF).
      assert (AndLRule [((Γ2 ++ A0 :: B0 :: x) ++ A :: B → D :: B → D :: Γ1, C)]
       ((Γ2 ++ A0 ∧ B0 :: x) ++ A :: B → D :: B → D :: Γ1, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
       apply AndL in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: B0 :: x) ++ A :: B → D :: B → D :: Γ1, C)])
      ((Γ2 ++ A0 ∧ B0 :: x) ++ A :: B → D :: B → D :: Γ1, C) H0 d1). auto.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++  (A  → B) → D :: Γ1, A0) = (Γ0 ++  (A  → B) → D :: Γ1, A0)). auto.
    pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
    assert (OrR1Rule [(Γ0 ++ A :: B → D :: B → D :: Γ1, A0)]
    (Γ0 ++ A :: B → D :: B → D :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons d0 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A :: B → D :: B → D :: Γ1, A0)])
    (Γ0 ++ A :: B → D :: B → D  :: Γ1, Or A0 B0) H0 d1). auto.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++  (A  → B) → D :: Γ1, B0) = (Γ0 ++  (A  → B) → D :: Γ1, B0)). auto.
    pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
    assert (OrR2Rule [(Γ0 ++ A :: B → D :: B → D :: Γ1, B0)]
    (Γ0 ++ A :: B → D :: B → D :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons d0 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A :: B → D :: B → D :: Γ1, B0)])
    (Γ0 ++ A :: B → D :: B → D  :: Γ1, Or A0 B0) H0 d1). auto.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [ (A  → B) → D]) ++ x0) ++ A0 :: Γ3, C) = (Γ0 ++  (A  → B) → D :: (x0 ++ A0 :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (((Γ0 ++ [ (A  → B) → D]) ++ x0) ++ B0 :: Γ3, C) = (Γ0 ++  (A  → B) → D :: (x0 ++ B0 :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J5 _ x1 _ _ _ _ _ _ J6 J7).
      assert (OrLRule [((Γ0 ++ A :: B → D :: B → D :: x0) ++ A0 :: Γ3, C);((Γ0 ++ A :: B → D :: B → D :: x0) ++ B0 :: Γ3, C)]
      ((Γ0 ++ A :: B → D :: B → D :: x0) ++ A0 ∨ B0 :: Γ3, C)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ A :: B → D :: B → D :: x0 ++ A0 :: Γ3, C); (Γ0 ++ A :: B → D :: B → D :: x0 ++ B0 :: Γ3, C)])
      (Γ0 ++ A :: B → D :: B → D :: x0 ++ A0 ∨ B0 :: Γ3, C) H0 d3). auto.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 :(Γ2 ++ A0 :: x ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ A0 :: x) ++  (A  → B) → D :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J2 _ x0 _ _ _ _ _ _ J3 J4).
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (Γ2 ++ B0 :: x ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ B0 :: x) ++  (A  → B) → D :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J5 _ x1 _ _ _ _ _ _ J6 J7).
      assert (OrLRule [((Γ2 ++ A0 :: x) ++ A :: B → D :: B → D :: Γ1, C);((Γ2 ++ B0 :: x) ++ A :: B → D :: B → D :: Γ1, C)]
      ((Γ2 ++ A0 ∨ B0 :: x) ++ A :: B → D :: B → D :: Γ1, C)). repeat rewrite <- app_assoc. apply OrLRule_I. apply OrL in H0.
      pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: x) ++ A :: B → D :: B → D :: Γ1, C); ((Γ2 ++ B0 :: x) ++ A :: B → D :: B → D :: Γ1, C)])
      ((Γ2 ++ A0 ∨ B0 :: x) ++ A :: B → D :: B → D :: Γ1, C) H0 d3). auto.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J50: derrec_height x = derrec_height x). auto.
    assert (J51: list_exch_L (Γ2 ++ A0 :: Γ3, B0) (A0 :: Γ0 ++  (A  → B) → D :: Γ1, B0)).
    assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). auto. rewrite H0.
    assert (A0 :: Γ0 ++  (A  → B) → D :: Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). rewrite <- H2. auto. rewrite H1.
    apply list_exch_LI.
    pose (GL4ip_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J4: (A0 :: Γ0 ++  (A  → B) → D :: Γ1, B0) = ((A0 :: Γ0) ++  (A  → B) → D :: Γ1, B0)). repeat rewrite <- app_assoc. auto.
    pose (IH _ J2 _ x0 _ _ _ _ _ _ J3 J4).
    assert (ImpRRule [(([] ++ A0 :: Γ0) ++ A :: B → D :: B → D :: Γ1, B0)] ([] ++ Γ0 ++ A :: B → D :: B → D :: Γ1, A0 → B0)). repeat rewrite <- app_assoc. apply ImpRRule_I.
    simpl in H0. apply ImpR in H0. pose (dlCons d0 DersNilF).
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[((A0 :: Γ0) ++ A :: B → D :: B → D :: Γ1, B0)]) (Γ0 ++ A :: B → D :: B → D :: Γ1, A0 → B0) H0 d1). auto.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [ (A  → B) → D]) ++ x1) ++ # P :: Γ3 ++ A0 :: Γ4, C) = (Γ0 ++  (A  → B) → D :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
       assert (AtomImpL1Rule [((Γ0 ++ A :: B → D :: B → D :: x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ A :: B → D :: B → D :: x1) ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)). apply AtomImpL1Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL1 in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: B → D :: B → D :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)])
       (Γ0 ++ A :: B → D :: B → D :: x1 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C) H0 d1). auto.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P :: ((x0 ++ [ (A  → B) → D]) ++ x2) ++ A0 :: Γ4, C) = ((Γ2 ++ # P :: x0) ++  (A  → B) → D :: x2 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
         assert (AtomImpL1Rule [((Γ2 ++ # P :: x0) ++ A :: B → D :: B → D :: x2 ++ A0 :: Γ4, C)]
         ((Γ2 ++ # P :: x0) ++ A :: B → D :: B → D :: x2 ++ # P → A0 :: Γ4, C)).
         assert ((Γ2 ++ # P :: x0) ++ A :: B → D :: B → D :: x2 ++ A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ A :: B → D :: B → D :: x2) ++ A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P :: x0) ++ A :: B → D :: B → D :: x2 ++ # P → A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ A :: B → D :: B → D :: x2) ++ # P → A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P :: x0) ++ A :: B → D :: B → D :: x2 ++ A0 :: Γ4, C)])
         ((Γ2 ++ # P :: x0) ++ A :: B → D :: B → D :: x2 ++ # P → A0 :: Γ4, C) H0 d1). auto. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++  (A  → B) → D :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
         assert (AtomImpL1Rule [((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ A :: B → D :: B → D :: Γ1, C)]
         ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ A :: B → D :: B → D :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ A :: B → D :: B → D :: Γ1, C)])
         ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ A :: B → D :: B → D :: Γ1, C) H0 d1). auto. }
  (* AtomImpL2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [ (A  → B) → D]) ++ x1) ++ A0 :: Γ3 ++ # P :: Γ4, C) = (Γ0 ++  (A  → B) → D :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
       assert (AtomImpL2Rule [((Γ0 ++ A :: B → D :: B → D :: x1) ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       ((Γ0 ++ A :: B → D :: B → D :: x1) ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL2 in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: B → D :: B → D :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)])
       (Γ0 ++ A :: B → D :: B → D :: x1 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C) H0 d1). auto.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: ((x0 ++ [ (A  → B) → D]) ++ x2) ++ # P :: Γ4, C) = ((Γ2 ++ A0 :: x0) ++  (A  → B) → D :: x2 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: x0) ++ A :: B → D :: B → D :: x2 ++ # P :: Γ4, C)]
         ((Γ2 ++ # P → A0 :: x0) ++ A :: B → D :: B → D :: x2 ++ # P :: Γ4, C)).
         assert ((Γ2 ++ A0 :: x0) ++ A :: B → D :: B → D :: x2 ++ # P :: Γ4 = Γ2 ++ A0 :: (x0 ++ A :: B → D :: B → D :: x2) ++ # P :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P → A0 :: x0) ++ A :: B → D :: B → D :: x2 ++ # P  :: Γ4 = Γ2 ++ # P → A0 :: (x0 ++ A :: B → D :: B → D :: x2) ++ # P :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: x0) ++ A :: B → D :: B → D :: x2 ++ # P :: Γ4, C)])
         ((Γ2 ++ # P → A0 :: x0) ++ A :: B → D :: B → D :: x2 ++ # P :: Γ4, C) H0 d1). auto. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++  (A  → B) → D :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ A :: B → D :: B → D :: Γ1, C)]
         ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ A :: B → D :: B → D :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ A :: B → D :: B → D :: Γ1, C)])
         ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ A :: B → D :: B → D :: Γ1, C) H0 d1). auto. }
 (* AndImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [ (A  → B) → D]) ++ x1) ++ A0 → B0 → C0 :: Γ3, C) = (Γ0 ++  (A  → B) → D :: x1 ++ A0 → B0 → C0 :: Γ3, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
       assert (AndImpLRule [((Γ0 ++ A :: B → D :: B → D :: x1) ++ A0 → B0 → C0 :: Γ3, C)]
       ((Γ0 ++ A :: B → D :: B → D :: x1) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply AndImpL in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: B → D :: B → D :: x1 ++ A0 → B0 → C0 :: Γ3, C)])
       (Γ0 ++ A :: B → D :: B → D :: x1 ++ (A0 ∧ B0) → C0 :: Γ3, C) H0 d1). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ A0 → B0 → C0 :: x0 ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ A0 → B0 → C0 :: x0) ++  (A  → B) → D :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
       assert (AndImpLRule [((Γ2 ++ A0 → B0 → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C)]
       ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
       apply AndImpL in H0. pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → B0 → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C)])
       ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C) H0 d1). auto.
  (* OrImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [ (A  → B) → D]) ++ x1) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) = (Γ0 ++  (A  → B) → D ::  x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
       assert (OrImpLRule [((Γ0 ++ A :: B → D :: B → D :: x1) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)]
       ((Γ0 ++ A :: B → D :: B → D :: x1) ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply OrImpL in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: B → D :: B → D :: x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)])
       (Γ0 ++ A :: B → D :: B → D :: x1 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C) H0 d1). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J50: derrec_height x = derrec_height x). auto.
       assert (J51: list_exch_L (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++  (A  → B) → D :: Γ1, C)).
       assert (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4 = (Γ2 ++ [A0 → C0]) ++ [] ++ Γ3 ++ [B0 → C0] ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++  (A  → B) → D :: Γ1 = (Γ2 ++ [A0 → C0]) ++ [B0 → C0] ++ Γ3 ++ [] ++ Γ4).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
       assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
       assert (J4: (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++  (A  → B) → D :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x1 _ _ _ _ _ _ J3 J4).
       assert (OrImpLRule [((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C)]
       ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C)).
       assert ((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ A :: B → D :: B → D :: Γ1 = Γ2 ++ A0 → C0 :: [] ++ B0 → C0 :: x0 ++ A :: B → D :: B → D :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
       assert ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: B → D :: B → D :: Γ1 = Γ2 ++ (A0 ∨ B0) → C0 :: [] ++ x0 ++ A :: B → D :: B → D :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
       apply OrImpLRule_I.  apply OrImpL in H0. pose (dlCons d0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C)])
       ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: B → D :: B → D :: Γ1, C) H0 d1). auto.
  (* ImpImpL *)
 * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
      assert (J1: ImpRRule [(Γ0 ++ A:: B → D :: Γ1, B)] (Γ0 ++ B → D :: Γ1, A → B)). apply ImpRRule_I.
      pose (ImpR_inv _ _ x J1).
      assert (J2: wkn_L (B → D) (Γ0 ++ D :: Γ1, C) (Γ0 ++ B → D :: D :: Γ1, C)). apply wkn_LI.
      pose (GL4ip_adm_wkn_L x0 J2).
      assert (J3: wkn_L A (Γ0 ++ B → D :: D :: Γ1, C) ((Γ0 ++ A :: [B → D]) ++ D :: Γ1, C)). repeat rewrite <- app_assoc. apply wkn_LI.
      pose (GL4ip_adm_wkn_L d1 J3).
      assert (Γ0 ++ A :: B → D :: Γ1 = (Γ0 ++ A :: [B → D]) ++ Γ1). repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0 in d0.
      assert (J4: derrec_height d0 = derrec_height d0). auto.
      assert (J5: ((Γ0 ++ [A; B → D]) ++ Γ1, B) = ((Γ0 ++ [A; B → D]) ++ Γ1, B)). auto.
      pose (ImpL_adm _ _ _ _ _ _ _ _ J4 J5 d2). repeat rewrite <- app_assoc in d3 ; simpl in d3. auto.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [ (A  → B) → D]) ++ x2) ++ B0 → C0 :: Γ3, A0 → B0) = (Γ0 ++  (A  → B) → D :: x2 ++ B0 → C0 :: Γ3, A0 → B0)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [ (A  → B) → D]) ++ x2) ++ C0 :: Γ3, C) = (Γ0 ++  (A  → B) → D :: x2 ++ C0 :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J5 _ x0 _ _ _ _ _ _ J6 J7).
       assert (ImpImpLRule [((Γ0 ++ A :: B → D :: B → D :: x2) ++ B0 → C0 :: Γ3, A0 → B0);((Γ0 ++ A :: B → D :: B → D :: x2) ++ C0 :: Γ3, C)]
       ((Γ0 ++ A :: B → D :: B → D :: x2) ++ (A0 → B0) → C0 :: Γ3, C)). apply ImpImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply ImpImpL in H0.
       pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: B → D :: B → D :: x2 ++ B0 → C0 :: Γ3, A0 → B0); (Γ0 ++ A :: B → D :: B → D :: x2 ++ C0 :: Γ3, C)])
       (Γ0 ++ A :: B → D :: B → D :: x2 ++ (A0 → B0) → C0 :: Γ3, C) H0 d3). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ B0 → C0 :: x1 ++  (A  → B) → D :: Γ1, A0 → B0) = ((Γ2 ++ B0 → C0 :: x1) ++  (A  → B) → D :: Γ1, A0 → B0)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ _ J3 J4).
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ C0 :: x1 ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ C0 :: x1) ++  (A  → B) → D :: Γ1, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J5 _ x0 _ _ _ _ _ _ J6 J7).
       assert (ImpImpLRule [((Γ2 ++ B0 → C0 :: x1) ++ A :: B → D :: B → D :: Γ1, A0 → B0);((Γ2 ++ C0 :: x1) ++ A :: B → D :: B → D :: Γ1, C)]
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ A :: B → D :: B → D :: Γ1, C)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
       apply ImpImpL in H0. pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ B0 → C0 :: x1) ++ A :: B → D :: B → D :: Γ1, A0 → B0); ((Γ2 ++ C0 :: x1) ++ A :: B → D :: B → D :: Γ1, C)])
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ A :: B → D :: B → D :: Γ1, C) H0 d3). auto.
  (* BoxImpL *)
 * inversion X. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    apply list_split_form in H. destruct H. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
       apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
       inversion u2. subst. exfalso. assert (In ( (A  → B) → D) (((x1 ++  (A  → B) → D :: l) ++ x5) ++ x2)).
       apply in_or_app ; left ; apply in_or_app ; left ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst. inversion X0. subst.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [ (A  → B) → D]) ++ x4) ++ B0 :: Γ3, C) = (Γ0 ++  (A  → B) → D :: x4 ++ B0 :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J5 _ x0 _ _ _ _ _ _ J6 J7).
       assert (BoxImpLRule [(XBoxed_list (x1 ++ (top_boxes [A]) ++ x5 ++ x2) ++ [Box A0], A0);((Γ0 ++ A :: B → D :: B → D :: x4) ++ B0 :: Γ3, C)]
       ((Γ0 ++ A :: B → D :: B → D :: x4) ++ Box A0 → B0 :: Γ3, C)).
       { destruct (dec_is_boxedT A).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. repeat rewrite <- app_assoc in H1 ; simpl in H1.
            intro. intros. apply in_app_or in H. destruct H. apply H1. apply in_or_app ; auto.
            inversion H. subst. exists x3. auto. apply in_app_or in H0 ; destruct H0. apply H1.
            apply in_or_app ; right ; apply in_or_app ; auto. apply H1.
            apply in_or_app ; right ; apply in_or_app ;  auto.
            assert (top_boxes [A] = [A]). destruct i ; subst ; simpl ; auto.
            rewrite H. simpl. repeat rewrite <- app_assoc ; simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto. repeat apply univ_gen_ext_extra ; try intro ; try destruct X1 ; try inversion H0 ; auto.
            apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [A] = []).
            destruct A ; auto ; exfalso ; apply f ; exists A ; auto. rewrite H ; auto. simpl.
            apply BoxImpLRule_I ; simpl  ; repeat rewrite <- app_assoc in H1 ; simpl in H1 ; auto.
            rewrite <- app_assoc ; simpl.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto.
            intro. destruct X1. inversion H0. intro. destruct X1. inversion H0. apply univ_gen_ext_combine ; auto. }
       assert (existsT2 (D2 : derrec GL4ip_rules (fun _ : Seq => False) (XBoxed_list (x1 ++ top_boxes [A] ++ x5 ++ x2) ++ [Box A0], A0)),
       derrec_height D2 <= derrec_height x).
       { destruct (dec_is_boxedT A).
          - assert (top_boxes [A] = [A]). destruct i. subst ; auto. rewrite H. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (J1: derrec_height x = derrec_height x). auto.
            pose (@GL4ip_list_wkn_L _ _ _ _ _ J1 (XBoxed_list [A])). destruct s.
            assert (J2: derrec_height x3 = derrec_height x3). auto.
            assert (J3: list_exch_L (XBoxed_list (((x1 ++ []) ++ x5) ++ x2) ++ XBoxed_list [A] ++ [Box A0], A0) (XBoxed_list x1 ++ XBoxed_list [A] ++ XBoxed_list x5 ++ XBoxed_list x2 ++ [Box A0], A0)).
            repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (XBoxed_list x1 ++ XBoxed_list [] ++ XBoxed_list x5 ++ XBoxed_list x2 ++ XBoxed_list [A] ++ [Box A0] = XBoxed_list x1 ++ [] ++ (XBoxed_list x5 ++ XBoxed_list x2) ++ XBoxed_list [A] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0.
            assert (XBoxed_list x1 ++ XBoxed_list [A] ++ XBoxed_list x5 ++ XBoxed_list x2 ++ [Box A0] = XBoxed_list x1 ++ XBoxed_list [A] ++ (XBoxed_list x5 ++ XBoxed_list x2) ++ [] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H3. apply list_exch_LI.
            pose (GL4ip_hpadm_list_exch_L _ _ _ J2 _ J3). destruct s. exists x6. lia.
          - assert (top_boxes [A] = []).
            destruct A ; auto ; exfalso ; apply f ; exists A ; auto. rewrite H ; auto. simpl.
            assert (x1 ++ x5 ++ x2 = ((x1 ++ []) ++ x5) ++ x2). repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0.
            exists x. lia. }
       destruct X2. apply BoxImpL in X1.
       pose (dlCons d0 DersNilF). pose (dlCons x3 d1). repeat rewrite <- app_assoc in X1.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(XBoxed_list (x1 ++ top_boxes [A] ++ x5 ++ x2) ++ [Box A0], A0); (Γ0 ++ A :: B → D :: B → D :: x4 ++ B0 :: Γ3, C)])
       (Γ0 ++ A :: B → D :: B → D :: x4 ++ Box A0 → B0 :: Γ3, C) X1 d2). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
       inversion u1. subst. exfalso. assert (In ( (A  → B) → D) (x1 ++ x4 ++  (A  → B) → D :: l)).
       apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ B0 :: x3 ++  (A  → B) → D :: Γ1, C) = ((Γ2 ++ B0 :: x3) ++  (A  → B) → D :: Γ1, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J5 _ x0 _ _ _ _ _ _ J6 J7).
       assert (BoxImpLRule [(XBoxed_list (x1 ++ x4 ++ (top_boxes [A]) ++ x5) ++ [Box A0], A0);((Γ2 ++ B0 :: x3) ++ A :: B → D :: B → D :: Γ1, C)]
       ((Γ2 ++ Box A0 → B0 :: x3) ++ A :: B → D :: B → D :: Γ1, C)).
       { destruct (dec_is_boxedT A).
          - repeat rewrite <- app_assoc. simpl. apply BoxImpLRule_I ; auto. destruct i. subst. simpl.
            intro. intros. apply in_app_or in H. destruct H. apply H1. apply in_or_app ; auto.
            apply in_app_or in H ; destruct H. apply H1.
            apply in_or_app ; right ; apply in_or_app ; auto. inversion H. subst. exists x2. auto. apply H1.
            apply in_or_app ; right ; apply in_or_app ;  auto.
            assert (match A with
                     | Box A1 => [Box A1]
                     | _ => []
                     end = [A]). destruct i ; subst ; simpl ; auto.
            rewrite H. simpl. repeat rewrite <- app_assoc ; simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto. repeat apply univ_gen_ext_extra ; try intro ; try destruct X1 ; try inversion H0 ; auto.
          - assert (top_boxes [A] = []).
            destruct A ; auto ; exfalso ; apply f ; exists A ; auto. rewrite H ; auto. simpl. repeat rewrite <- app_assoc ; simpl.
            apply BoxImpLRule_I ; simpl  ; repeat rewrite <- app_assoc in H1 ; simpl in H1 ; auto.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto.
            intro. destruct X1. inversion H0. intro. destruct X1. inversion H0. }
       assert (existsT2 (D2 : derrec GL4ip_rules (fun _ : Seq => False) (XBoxed_list (x1 ++ x4 ++ top_boxes [A] ++ x5) ++ [Box A0], A0)),
       derrec_height D2 <= derrec_height x).
       { destruct (dec_is_boxedT A).
          - assert (top_boxes [A] = [A]). destruct i. subst ; auto. rewrite H. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (J1: derrec_height x = derrec_height x). auto.
            pose (@GL4ip_list_wkn_L _ _ _ _ _ J1 (XBoxed_list [A])). destruct s.
            assert (J2: derrec_height x2 = derrec_height x2). auto.
            assert (J3: list_exch_L (XBoxed_list (x1 ++ x4 ++ x5) ++ XBoxed_list [A] ++ [Box A0], A0) (XBoxed_list x1 ++ XBoxed_list x4 ++ XBoxed_list [A] ++ XBoxed_list x5 ++ [Box A0], A0)).
            repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (XBoxed_list x1 ++ XBoxed_list x4 ++ XBoxed_list x5 ++ XBoxed_list [A] ++ [Box A0] = (XBoxed_list x1 ++ XBoxed_list x4) ++ [] ++ XBoxed_list x5 ++ XBoxed_list [A] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0.
            assert (XBoxed_list x1 ++ XBoxed_list x4 ++ XBoxed_list [A] ++ XBoxed_list x5 ++ [Box A0] = (XBoxed_list x1 ++ XBoxed_list x4) ++ XBoxed_list [A] ++ XBoxed_list x5 ++ [] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H3. apply list_exch_LI.
            pose (GL4ip_hpadm_list_exch_L _ _ _ J2 _ J3). destruct s. exists x6. lia.
          - assert (top_boxes [A] = []).
            destruct A ; auto ; exfalso ; apply f ; exists A ; auto. rewrite H ; auto. simpl. exists x. lia. }
       destruct X2. apply BoxImpL in X1.
       pose (dlCons d0 DersNilF). pose (dlCons x2 d1). repeat rewrite <- app_assoc in X1. repeat rewrite <- app_assoc. simpl. simpl in X1.
       assert (match A with
                                  | Box A => [Box A]
                                  | _ => []
                                  end = top_boxes [A]). simpl. auto. rewrite H in X1. repeat rewrite <- app_assoc in d2.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(XBoxed_list (x1 ++ x4 ++ top_boxes [A] ++ x5) ++ [Box A0], A0); (Γ2 ++ B0 :: x3 ++ A :: B → D :: B → D :: Γ1, C)])
       (Γ2 ++ Box A0 → B0 :: x3 ++ A :: B → D :: B → D :: Γ1, C) X1 d2). auto.
  (* GLR *)
  * inversion X. subst. simpl. apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    inversion u0. subst. exfalso. assert (In ( (A  → B) → D) (x ++  (A  → B) → D :: l)). apply in_or_app ; right ; apply in_eq.
    apply H1 in H. destruct H. inversion H. subst.
    assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A0], A0)] (Γ0 ++ Γ1, Box A0)). apply GLRRule_I ; auto.
    apply univ_gen_ext_combine ; auto. apply GLR in X1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(XBoxed_list (x ++ x0) ++ [Box A0], A0)]) (Γ0 ++ Γ1, Box A0) X1 d).
    assert (J1: wkn_L (B → D) (Γ0 ++ Γ1, Box A0) (Γ0 ++ B → D :: Γ1, Box A0)). apply wkn_LI.
    pose (@GL4ip_adm_wkn_L _ d0 _ _ J1).
    assert (J2: wkn_L (B → D) (Γ0 ++ B → D :: Γ1, Box A0) (Γ0 ++ B → D :: B → D :: Γ1, Box A0)). apply wkn_LI.
    pose (@GL4ip_adm_wkn_L _ d1 _ _ J2).
    assert (J3: wkn_L A (Γ0 ++ B → D :: B → D :: Γ1, Box A0) (Γ0 ++ A :: B → D :: B → D :: Γ1, Box A0)). apply wkn_LI.
    pose (@GL4ip_adm_wkn_L _ d2 _ _ J3). auto.
Qed.







