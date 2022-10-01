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
Require Import Lia.

Theorem ImpImpL_hpinv_R : forall (k : nat) concl
        (D0 : derrec GL4ip_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem1 prem2, ((ImpImpLRule [prem1;prem2] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem2),
          derrec_height D1 <= k))).
Proof.
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec GL4ip_rules (fun _ : Seq => False) concl),
x = (derrec_height D0) ->
          ((forall prem1 prem2, ((ImpImpLRule [prem1;prem2] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem2),
          derrec_height D1 <= x))))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. intros prem1 prem2 RA. inversion RA. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ (A → B) → C :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++  C :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x ++ # P :: x0, # P)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ (A → B) → C :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ C :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, D)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, D) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: ImpImpLRule [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, A0)] (Γ0 ++ (A → B) → C :: Γ1, A0)). apply ImpImpLRule_I. simpl in IH.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J2 _ _ J3 _ _ J1). destruct s.
    assert (J4: ImpImpLRule [(Γ0 ++ B → C :: Γ1, A → B);(Γ0 ++ C :: Γ1, B0)] (Γ0 ++ (A → B) → C :: Γ1, B0)). apply ImpImpLRule_I.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (AndRRule [(Γ0 ++ C :: Γ1, A0); (Γ0 ++ C :: Γ1, B0)]
   (Γ0 ++ C :: Γ1, And A0 B0)). apply AndRRule_I. pose (dlCons x2 DersNilF). pose (dlCons x1 d0).
    apply AndR in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ C :: Γ1, A0); (Γ0 ++ C :: Γ1, B0)])
    (Γ0 ++ C :: Γ1, And A0 B0) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndLRule [((Γ0 ++ C :: x0) ++ A0 :: B0 :: Γ3, D)]
       ((Γ0 ++ C :: x0) ++ And A0 B0 :: Γ3, D)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ A0 :: B0 :: Γ3, A → B);(Γ0 ++ C :: x0 ++ A0 :: B0 :: Γ3, D)]
       (((Γ0 ++ [(A → B) → C]) ++ x0) ++ A0 :: B0 :: Γ3, D)). repeat rewrite <- app_assoc. simpl. apply ImpImpLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x1 DersNilF). apply AndL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ C :: x0 ++ A0 :: B0 :: Γ3, D)])
       (Γ0 ++ C :: x0 ++ And A0 B0 :: Γ3, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
  +  repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J4: ImpImpLRule [((Γ2 ++ A0 :: B0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ A0 :: B0 :: x) ++ C :: Γ1, D)]
      ((Γ2 ++ A0 :: B0 :: x) ++ (A → B) → C :: Γ1, D)). apply ImpImpLRule_I.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (AndLRule [(Γ2 ++ A0 :: B0 :: x ++ C :: Γ1, D)]
      (Γ2 ++ And A0 B0 :: x ++ C :: Γ1, D)). apply AndLRule_I.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply AndL in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: B0 :: x ++ C :: Γ1, D)])
      (Γ2 ++ And A0 B0 :: x ++ C :: Γ1, D) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: ImpImpLRule [(Γ0 ++ B → C :: Γ1, A → B);(Γ0 ++ C :: Γ1, A0)] (Γ0 ++ (A → B) → C :: Γ1, A0)). apply ImpImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (OrR1Rule [(Γ0 ++ C :: Γ1, A0)]
    (Γ0 ++ C :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons x0 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ C :: Γ1, A0)])
    (Γ0 ++ C :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: ImpImpLRule [(Γ0 ++ B → C :: Γ1, A → B);(Γ0 ++ C :: Γ1, B0)] (Γ0 ++ (A → B) → C :: Γ1, B0)). apply ImpImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (OrR2Rule [(Γ0 ++ C :: Γ1, B0)]
    (Γ0 ++ C :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons x0 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ C :: Γ1, B0)])
    (Γ0 ++ C :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (OrLRule [((Γ0 ++ C :: x0) ++ A0 :: Γ3, D);((Γ0 ++ C :: x0) ++ B0 :: Γ3, D)]
      ((Γ0 ++ C :: x0) ++ Or A0 B0 :: Γ3, D)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ A0 :: Γ3, A → B);(Γ0 ++ C :: x0 ++ A0 :: Γ3, D)]
      (((Γ0 ++ [(A → B) → C]) ++ x0) ++ A0 :: Γ3, D)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
      assert (J5: derrec_height x < S (dersrec_height d)). lia.
      assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ B0 :: Γ3, A → B);(Γ0 ++ C :: x0 ++ B0 :: Γ3, D)]
      (((Γ0 ++ [(A → B) → C]) ++ x0) ++ B0 :: Γ3, D)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ C :: x0 ++ A0 :: Γ3, D); (Γ0 ++ C :: x0 ++ B0 :: Γ3, D)])
      (Γ0 ++ C :: x0 ++ Or A0 B0 :: Γ3, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (OrLRule [(Γ2 ++ A0 :: x ++ C :: Γ1, D);(Γ2 ++ B0 :: x ++ C :: Γ1, D)]
      (Γ2 ++ Or A0 B0 :: x ++ C :: Γ1, D)). apply OrLRule_I. apply OrL in H0.
      assert (J4: ImpImpLRule [((Γ2 ++ A0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ A0 :: x) ++ C :: Γ1, D)]
      ((Γ2 ++ A0 :: x) ++ (A → B) → C :: Γ1, D)). apply ImpImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: ImpImpLRule [((Γ2 ++ B0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ B0 :: x) ++ C :: Γ1, D)]
      ((Γ2 ++ B0 :: x) ++ (A → B) → C :: Γ1, D)). apply ImpImpLRule_I.
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x ++ C :: Γ1, D); (Γ2 ++ B0 :: x ++ C :: Γ1, D)])
      (Γ2 ++ Or A0 B0 :: x ++ C :: Γ1, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (ImpRRule [(Γ2 ++ A0 :: C :: Γ1, B0)] (Γ2 ++ C :: Γ1, Imp A0 B0)). apply ImpRRule_I.
      assert (J4: ImpImpLRule [((Γ2 ++ [A0]) ++ B → C :: Γ1, A → B);((Γ2 ++ [A0]) ++ C :: Γ1, B0)]
      ((Γ2 ++ [A0]) ++ (A → B) → C :: Γ1, B0)). apply ImpImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply ImpR in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: C :: Γ1, B0)])
      (Γ2 ++ C :: Γ1, Imp A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (ImpRRule [(Γ2 ++ A0 :: x ++ C :: Γ1, B0)] (Γ2 ++ x ++ C :: Γ1, Imp A0 B0)). apply ImpRRule_I.
      assert (J4: ImpImpLRule [((Γ2 ++ A0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ A0 :: x) ++ C :: Γ1, B0)]
      ((Γ2 ++ A0 :: x) ++ (A → B) → C :: Γ1, B0)). apply ImpImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply ImpR in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x ++ C :: Γ1, B0)])
      (Γ2 ++ x ++ C :: Γ1, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
    + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (ImpRRule [ (Γ0 ++ A0 :: C :: Γ1, B0)]  (Γ0 ++ C :: Γ1, Imp A0 B0)). apply ImpRRule_I.
        assert (J4: ImpImpLRule [((Γ0 ++ [A0]) ++ B → C :: Γ1, A → B);((Γ0 ++ [A0]) ++ C :: Γ1, B0)]
        ((Γ0 ++ [ A0]) ++ (A → B) → C :: Γ1, B0)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (Γ0 ++ A0 :: (A → B) → C :: Γ1 = ((Γ0 ++ []) ++ A0 :: (A → B) → C :: Γ1)). repeat rewrite <- app_assoc ; simpl ; auto.
        rewrite H1 in J4. clear H1.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x0 DersNilF). apply ImpR in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A0 :: C :: Γ1, B0)])
        (Γ0 ++ C :: Γ1, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
        assert (ImpRRule [((Γ0 ++ C :: x) ++ A0 :: Γ3, B0)]  ((Γ0 ++ C :: x) ++ Γ3, Imp A0 B0)). apply ImpRRule_I.
        assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x ++ A0 :: Γ3, A → B);(Γ0 ++ C :: x ++ A0 :: Γ3, B0)]
        ((Γ0 ++ (A → B) → C :: x) ++ A0 :: Γ3, B0)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x1 DersNilF).  apply ImpR in H0. repeat rewrite <- app_assoc in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ C :: x ++ A0 :: Γ3, B0)])
        (Γ0 ++ C :: x ++ Γ3, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
  (* AtomImpL1 *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL1Rule [((Γ0 ++ C :: x0) ++ # P :: Γ3 ++ A0 :: Γ4, D)]
       ((Γ0 ++ C :: x0) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, D)). apply AtomImpL1Rule_I.
       assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ # P :: Γ3 ++ A0 :: Γ4, A → B);(Γ0 ++ C :: x0 ++ # P :: Γ3 ++ A0 :: Γ4, D)]
       (((Γ0 ++ [(A → B) → C]) ++ x0) ++ # P :: Γ3 ++ A0 :: Γ4, D)). repeat rewrite <- app_assoc ; simpl. apply ImpImpLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x1 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ C :: x0 ++ # P :: Γ3 ++ A0 :: Γ4, D)])
       (Γ0 ++ C :: x0 ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
      { inversion e0. }
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL1Rule [(Γ2 ++ # P :: (x ++ C :: x1) ++ A0 :: Γ4, D)]
        (Γ2 ++ # P :: (x ++ C :: x1) ++ Imp # P A0 :: Γ4, D)). apply AtomImpL1Rule_I.
        assert (J4: ImpImpLRule [((Γ2 ++ # P :: x) ++ B → C :: x1 ++ A0 :: Γ4, A → B);((Γ2 ++ # P :: x) ++ C :: x1 ++ A0 :: Γ4, D)]
        ((Γ2 ++ # P :: x) ++ (A → B) → C :: x1 ++ A0 :: Γ4, D)).
        apply ImpImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (Γ2 ++ # P :: x ++ (A → B) → C :: x1 ++ A0 :: Γ4 = Γ2 ++ # P :: ((x ++ [(A → B) → C]) ++ x1) ++ A0 :: Γ4).
        repeat rewrite <- app_assoc. auto. rewrite H1 in J4. clear H1.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x2 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: x ++ C :: x1 ++ A0 :: Γ4, D)])
        (Γ2 ++ # P :: x ++ C :: x1 ++ Imp # P A0 :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { repeat destruct s ; repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A0 :: x0 ++ C :: Γ1, D)]
        (Γ2 ++ # P :: Γ3 ++ Imp # P A0 :: x0 ++ C :: Γ1, D)). apply AtomImpL1Rule_I.
        assert (J4: ImpImpLRule [((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ B → C :: Γ1, A → B);((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ C :: Γ1, D)]
        ((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ (A → B) → C :: Γ1, D)).
        apply ImpImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: x0 ++ C :: Γ1, D)])
        (Γ2 ++ # P :: Γ3 ++ Imp (# P) A0 :: x0 ++ C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
  (* AtomImpL2 *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL2Rule [((Γ0 ++ C :: x0) ++ A0 :: Γ3 ++ # P :: Γ4, D)]
       ((Γ0 ++ C :: x0) ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, D)). apply AtomImpL2Rule_I.
       assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ A0 :: Γ3 ++ # P :: Γ4, A → B);(Γ0 ++ C :: x0 ++ A0 :: Γ3 ++ # P :: Γ4, D)]
       (((Γ0 ++ [(A → B) → C]) ++ x0) ++ A0 :: Γ3 ++ # P :: Γ4, D)). repeat rewrite <- app_assoc ; simpl. apply ImpImpLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x1 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ C :: x0 ++ A0 :: Γ3 ++ # P :: Γ4, D)])
       (Γ0 ++ C :: x0 ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
      { inversion e0. }
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL2Rule [(Γ2 ++ A0 :: (x ++ C :: x1) ++ # P :: Γ4, D)]
        (Γ2 ++ Imp # P A0 :: (x ++ C :: x1) ++ # P :: Γ4, D)). apply AtomImpL2Rule_I.
        assert (J4: ImpImpLRule [((Γ2 ++ A0 :: x) ++ B → C :: x1 ++ # P :: Γ4, A → B);((Γ2 ++ A0 :: x) ++ C :: x1 ++ # P :: Γ4, D)]
        ((Γ2 ++ A0 :: x) ++ (A → B) → C :: x1 ++ # P :: Γ4, D)).
        apply ImpImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (Γ2 ++ A0 :: x ++ (A → B) → C :: x1 ++ # P :: Γ4 = Γ2 ++ A0 :: ((x ++ [(A → B) → C]) ++ x1) ++ # P :: Γ4).
        repeat rewrite <- app_assoc. auto. rewrite H1 in J4. clear H1.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x2 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: x ++ C :: x1 ++ # P :: Γ4, D)])
        (Γ2 ++ Imp # P A0 :: x ++ C :: x1 ++ # P :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { repeat destruct s ; repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL2Rule [(Γ2 ++ A0 :: Γ3 ++ # P :: x0 ++ C :: Γ1, D)]
        (Γ2 ++ Imp # P A0 :: Γ3 ++ # P :: x0 ++ C :: Γ1, D)). apply AtomImpL2Rule_I.
        assert (J4: ImpImpLRule [((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ B → C :: Γ1, A → B);((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ C :: Γ1, D)]
        ((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ (A → B) → C :: Γ1, D)).
        apply ImpImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: x0 ++ C :: Γ1, D)])
        (Γ2 ++ Imp # P A0 :: Γ3 ++ # P :: x0 ++ C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
 (* AndImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (AndImpLRule [((Γ0 ++ C :: x0) ++ A0 → B0 → C0 :: Γ3, D)]
    ((Γ0 ++ C :: x0) ++ (A0 ∧ B0) → C0 :: Γ3, D)). apply AndImpLRule_I. repeat rewrite <- app_assoc in H0.
     assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ A0 → B0 → C0 :: Γ3, A → B);(Γ0 ++ C :: x0 ++ A0 → B0 → C0 :: Γ3, D)]
     (((Γ0 ++ [(A → B) → C]) ++ x0) ++ A0 → B0 → C0 :: Γ3, D)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
     assert (J5: derrec_height x < S (dersrec_height d)). lia.
     assert (J6: derrec_height x = derrec_height x). reflexivity.
     pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
     pose (dlCons x1 DersNilF). apply AndImpL in H0.
     pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ C :: x0 ++ Imp A0 (Imp B0 C0) :: Γ3, D)])
     (Γ0 ++ C :: x0 ++ Imp (And A0 B0) C0 :: Γ3, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndImpLRule [((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ C :: Γ1, D)]
      ((Γ2 ++ Imp (And A0 B0) C0 :: x) ++ C :: Γ1, D)). repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. apply AndImpLRule_I.
      assert (J4: ImpImpLRule [((Γ2 ++ A0 → B0 → C0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ A0 → B0 → C0 :: x) ++ C :: Γ1, D)]
      ((Γ2 ++ A0 → B0 → C0 :: x) ++ (A → B) → C :: Γ1, D)).
      apply ImpImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply AndImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ Imp A0 (Imp B0 C0) :: x ++ C :: Γ1, D)])
     (Γ2 ++ Imp (And A0 B0) C0 :: x ++ C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule [((Γ0 ++ C :: x0) ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)]
       ((Γ0 ++ C :: x0) ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, D)). apply OrImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, A → B);(Γ0 ++ C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)]
       (((Γ0 ++ [(A → B) → C]) ++ x0) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, D)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x1 DersNilF). apply OrImpL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)])
       (Γ0 ++ C :: x0 ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
        rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J50: derrec_height x0 = derrec_height x0). auto.
      assert (J51: list_exch_L (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, D) (Γ2 ++ A0 → C0 :: B0 → C0 :: x ++ (A → B) → C :: Γ1, D)).
      assert (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4 = (Γ2 ++ [A0 → C0]) ++ [] ++ Γ3 ++ [B0 → C0] ++ Γ4).
      repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ2 ++ A0 → C0 :: B0 → C0 :: x ++ (A → B) → C :: Γ1 = (Γ2 ++ [A0 → C0]) ++ [B0 → C0] ++ Γ3 ++ [] ++ Γ4).
      rewrite <- e0 ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
      pose (GL4ip_hpadm_list_exch_L (derrec_height x0) (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, D) x0 J50
      _ J51). destruct s. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
      assert (OrImpLRule [(Γ2 ++ A0 → C0 :: [] ++ B0 → C0 :: x ++ C :: Γ1, D)]
      (Γ2 ++ Imp (Or A0 B0) C0 :: [] ++ x ++ C :: Γ1, D)). apply OrImpLRule_I. simpl in H0.
      assert (J4: ImpImpLRule [((Γ2 ++ A0 → C0 :: B0 → C0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ A0 → C0 :: B0 → C0 :: x) ++ C :: Γ1, D)]
      ((Γ2 ++ A0 → C0 :: B0 → C0 :: x) ++ (A → B) → C :: Γ1, D)).
      apply ImpImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x2 DersNilF). apply OrImpL in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 → C0 :: B0 → C0 :: x ++ C :: Γ1, D)])
      (Γ2 ++ (A0 ∨ B0) → C0 :: x ++ C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1.
      simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* ImpImpL *)
 * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0 ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. exists x0 ; auto. simpl. lia.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
        assert (ImpImpLRule [((Γ0 ++ C :: x0) ++ Imp B0 C0 :: Γ3, Imp A0 B0); ((Γ0 ++ C :: x0) ++ C0 :: Γ3, D)]
        ((Γ0 ++ C :: x0) ++ Imp (Imp A0 B0) C0 :: Γ3, D)). apply ImpImpLRule_I. apply ImpImpL in H0.
        repeat rewrite <- app_assoc in H0. simpl in H0.
        assert (J4: ImpImpLRule [ (Γ0 ++ B → C :: x0 ++ Imp B0 C0 :: Γ3,A → B);(Γ0 ++ C :: x0 ++ Imp B0 C0 :: Γ3, Imp A0 B0)]
        (((Γ0 ++ [(A → B) → C]) ++ x0) ++ Imp B0 C0 :: Γ3, Imp A0 B0)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        assert (J7: ImpImpLRule [(Γ0 ++ B → C :: x0 ++ C0 :: Γ3, A → B);(Γ0 ++ C :: x0 ++ C0 :: Γ3, D)]
        (((Γ0 ++ [(A → B) → C]) ++ x0) ++ C0 :: Γ3, D)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
        assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
        pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ C :: x0 ++ Imp B0 C0 :: Γ3, Imp A0 B0); (Γ0 ++ C :: x0 ++ C0 :: Γ3, D)])
       (Γ0 ++ C :: x0 ++ Imp (Imp A0 B0) C0 :: Γ3, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (ImpImpLRule [(Γ2 ++ Imp B0 C0 :: x ++ C :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x ++ C :: Γ1, D)]
      (Γ2 ++ Imp (Imp A0 B0) C0 :: x ++ C :: Γ1, D)). apply ImpImpLRule_I. apply ImpImpL in H0.
      assert (J4: ImpImpLRule [((Γ2 ++ Imp B0 C0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ Imp B0 C0 :: x) ++ C :: Γ1, Imp A0 B0)]
      ((Γ2 ++ Imp B0 C0 :: x) ++ (A → B) → C :: Γ1, Imp A0 B0)). apply ImpImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: ImpImpLRule [((Γ2 ++ C0 :: x) ++ B → C :: Γ1, A → B);((Γ2 ++ C0 :: x) ++ C :: Γ1, D)]
      ((Γ2 ++ C0 :: x) ++ (A → B) → C :: Γ1, D)). apply ImpImpLRule_I.
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ Imp B0 C0 :: x ++ C :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x ++ C :: Γ1, D)])
      (Γ2 ++ Imp (Imp A0 B0) C0 :: x ++ C :: Γ1, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* BoxImpL *)
 * inversion X. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    apply list_split_form in H. destruct H. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
       apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
       inversion u2. subst. exfalso. assert (In ((A → B) → C) (((x1 ++ (A → B) → C :: l) ++ x5) ++ x2)).
       apply in_or_app ; left ; apply in_or_app ; left ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst. inversion X0. subst.
       assert (J4: ImpImpLRule [(Γ0 ++ B → C :: x4 ++ B0 :: Γ3, A → B);(Γ0 ++ C :: x4 ++ B0 :: Γ3, D)]
       (((Γ0 ++ [(A → B) → C]) ++ x4) ++ B0 :: Γ3, D)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       destruct (dec_is_boxedT C).
       { assert (existsT2 (D1 : derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list x1 ++ XBoxed_list (x5 ++ x2) ++ [Box A0], A0)),
          derrec_height D1 = derrec_height x).
          assert (XBoxed_list x1 ++ XBoxed_list (x5 ++ x2) ++ [Box A0] = XBoxed_list (((x1 ++ []) ++ x5) ++ x2) ++ [Box A0]).
          repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc ; auto. rewrite H.
          exists x ; auto. destruct X1. symmetry in e0.
          pose (@GL4ip_list_wkn_L (derrec_height x) (XBoxed_list x1) (XBoxed_list (x5 ++ x2) ++ [Box A0]) A0 x6 e0 [unBox_formula C ; C]).
          destruct s.
          assert (BoxImpLRule [(XBoxed_list x1 ++ [unBox_formula C; C] ++ XBoxed_list (x5 ++ x2) ++ [Box A0], A0);((Γ0 ++ C :: x4) ++ B0 :: Γ3, D)]
          ((Γ0 ++ C :: x4) ++ Box A0 → B0 :: Γ3, D)).
          assert (XBoxed_list x1 ++ [unBox_formula C; C] ++ XBoxed_list (x5 ++ x2) ++ [Box A0] = XBoxed_list (x1 ++ C :: x5 ++ x2) ++ [Box A0]).
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. auto.
           rewrite H. apply BoxImpLRule_I. intro. intros. apply in_app_or in H0. repeat rewrite <- app_assoc in H1.
           simpl in H1. destruct H0. apply H1. apply in_or_app ; auto. inversion H0 ; subst. destruct i. exists x8 ; subst ; auto.
           apply in_app_or in H3. destruct H3. apply H1. apply in_or_app ; right ; apply in_or_app ; auto.
           apply H1. apply in_or_app ; right ; apply in_or_app ; auto. repeat rewrite <- app_assoc.
           apply univ_gen_ext_combine ; auto. simpl. apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
           repeat rewrite <- app_assoc in X1. apply BoxImpL in X1.
           pose (dlCons x3 DersNilF). pose (dlCons x7 d0).
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list x1 ++ [unBox_formula C; C] ++ XBoxed_list (x5 ++ x2) ++ [Box A0], A0); (Γ0 ++ C :: x4 ++ B0 :: Γ3, D)])
           (Γ0 ++ C :: x4 ++ Box A0 → B0 :: Γ3, D) X1 d1). repeat rewrite <- app_assoc. exists d2. simpl.
           rewrite dersrec_height_nil ; auto. simpl in l0. lia. }
       { assert (BoxImpLRule [(XBoxed_list (((x1 ++ []) ++ x5) ++ x2) ++ [Box A0], A0);((Γ0 ++ C :: x4) ++ B0 :: Γ3, D)]
          ((Γ0 ++ C :: x4) ++ Box A0 → B0 :: Γ3, D)).
          apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_combine ; auto.
          apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto.
           assert ((Γ0 ++ C :: x4) ++ B0 :: Γ3 = Γ0 ++ C :: x4 ++ B0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H in X1.
           assert ((Γ0 ++ C :: x4) ++ Box A0 → B0 :: Γ3 = Γ0 ++ C :: x4 ++ Box A0 → B0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H0 in X1.
           pose (dlCons x3 DersNilF). pose (dlCons x d0). apply BoxImpL in X1.
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list (((x1 ++ []) ++ x5) ++ x2) ++ [Box A0], A0); (Γ0 ++ C :: x4 ++ B0 :: Γ3, D)])
           (Γ0 ++ C :: x4 ++ Box A0 → B0 :: Γ3, D) X1 d1). exists d2. simpl.
           rewrite dersrec_height_nil ; auto. lia. }
   +  repeat destruct s. repeat destruct p ; subst.
       apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
       inversion u1. subst. exfalso. assert (In ((A → B) → C) (x1 ++ x4 ++ (A → B) → C :: l)).
       apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst.
       assert (J4: ImpImpLRule [((Γ2 ++ B0 :: x3) ++ B → C :: Γ1, A → B);((Γ2 ++ B0 :: x3) ++ C :: Γ1, D)]
       ((Γ2 ++ B0 :: x3) ++ (A → B) → C :: Γ1, D)).  apply ImpImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       destruct (dec_is_boxedT C).
       { assert (existsT2 (D1 : derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list (x1 ++ x4) ++ XBoxed_list  x5 ++ [Box A0], A0)),
          derrec_height D1 = derrec_height x).
          assert (XBoxed_list (x1 ++ x4) ++ XBoxed_list x5 ++ [Box A0] = XBoxed_list (x1++ x4 ++ x5) ++ [Box A0]).
          repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc ; auto. rewrite H.
          exists x ; auto. destruct X1. symmetry in e0.
          pose (@GL4ip_list_wkn_L (derrec_height x) (XBoxed_list (x1 ++ x4)) (XBoxed_list x5 ++ [Box A0]) A0 x6 e0 [unBox_formula C ; C]).
          destruct s.
          assert (BoxImpLRule [(XBoxed_list (x1 ++ x4) ++ [unBox_formula C; C] ++ XBoxed_list x5 ++ [Box A0], A0);((Γ2 ++ B0 :: x3) ++ C :: Γ1, D)]
          ((Γ2 ++ Box A0 → B0 :: x3) ++ C :: Γ1, D)). repeat rewrite <- app_assoc. simpl.
          assert (XBoxed_list (x1 ++ x4) ++ unBox_formula C :: C :: XBoxed_list x5 ++ [Box A0] = XBoxed_list (x1 ++ x4 ++ C :: x5) ++ [Box A0]).
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. auto.
           rewrite H. apply BoxImpLRule_I. intro. intros. apply in_app_or in H0. repeat rewrite <- app_assoc in H1.
           simpl in H1. destruct H0. apply H1. apply in_or_app ; auto.
           apply in_app_or in H0. destruct H0. apply H1. apply in_or_app ; right ; apply in_or_app ; auto.
           inversion H0 ; subst. destruct i. exists x8 ; subst ; auto.
           apply H1. apply in_or_app ; right ; apply in_or_app ; auto.
           apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
           apply BoxImpL in X1.
           pose (dlCons x2 DersNilF). pose (dlCons x7 d0). repeat rewrite <- app_assoc in X1.
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list (x1 ++ x4) ++ [unBox_formula C; C] ++ XBoxed_list x5 ++ [Box A0], A0); (Γ2 ++ B0 :: x3 ++ C :: Γ1, D)])
           (Γ2 ++ Box A0 → B0 :: x3 ++ C :: Γ1, D) X1 d1). repeat rewrite <- app_assoc. exists d2. simpl.
           rewrite dersrec_height_nil ; auto. simpl in l0. lia. }
       { assert (BoxImpLRule [(XBoxed_list (x1 ++ x4 ++ x5) ++ [Box A0], A0);((Γ2 ++ B0 :: x3) ++ C :: Γ1, D)]
          ((Γ2 ++ Box A0 → B0 :: x3) ++ C :: Γ1, D)). repeat rewrite <- app_assoc. simpl.
          apply BoxImpLRule_I ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto.
          apply univ_gen_ext_extra ; auto. apply BoxImpL in X1.
           pose (dlCons x2 DersNilF). pose (dlCons x d0). repeat rewrite <- app_assoc in X1.
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(XBoxed_list (x1 ++ x4 ++ x5) ++ [Box A0], A0); (Γ2 ++ B0 :: x3 ++ C :: Γ1, D)])
           (Γ2 ++ Box A0 → B0 :: x3 ++ C :: Γ1, D) X1 d1). repeat rewrite <- app_assoc. exists d2. simpl.
           rewrite dersrec_height_nil ; auto. lia. }
  (* GLR *)
  * inversion X. subst. simpl. apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    inversion u0. subst. exfalso. assert (In ((A → B) → C) (x ++ (A → B) → C :: l)). apply in_or_app ; right ; apply in_eq.
    apply H1 in H. destruct H. inversion H. subst.
    assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A0], A0)] (Γ0 ++ Γ1, Box A0)). apply GLRRule_I ; auto.
    apply univ_gen_ext_combine ; auto. apply GLR in X1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(XBoxed_list (x ++ x0) ++ [Box A0], A0)]) (Γ0 ++ Γ1, Box A0) X1 d).
    assert (J1: derrec_height d0 = derrec_height d0). auto.
    assert (J2: wkn_L C (Γ0 ++ Γ1, Box A0) (Γ0 ++ C :: Γ1, Box A0)). apply wkn_LI.
    pose (@GL4ip_wkn_L (derrec_height d0) _ d0 J1 (Γ0 ++ C :: Γ1, Box A0) C J2). destruct s. exists x1.
    simpl. simpl in l. lia.
Qed.

Theorem ImpImpL_inv_R : forall concl prem1 prem2, (derrec GL4ip_rules (fun _ => False) concl) ->
                                      (ImpImpLRule [prem1;prem2] concl) ->
                                      (derrec GL4ip_rules (fun _ => False) prem2).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (ImpImpL_hpinv_R _ _ X J1). pose (s _ _ H). destruct s0. assumption.
Qed.







