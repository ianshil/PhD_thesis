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

Theorem ImpR_hpinv : forall (k : nat) concl
        (D0 : derrec GL4ip_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem),
          derrec_height D1 <= k))).
Proof.
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec GL4ip_rules (fun _ : Seq => False) concl),
x = derrec_height D0 ->
((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem),
          derrec_height D1 <= x))))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. intros prem RA. inversion RA. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ A :: Γ1)). assert (InT (⊥) (Γ0 ++ Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, B)). apply BotLRule_I. apply BotL in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, B) H0 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H.
  (* AndL *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndLRule  [((Γ2 ++ [A]) ++ A0 :: B0 :: Γ3, B)]
      ((Γ2 ++ [A]) ++ And A0 B0 :: Γ3, B)). apply AndLRule_I. apply AndL in H0.
      assert (J4: ImpRRule [(Γ2 ++ A :: A0 :: B0 :: Γ3, B)]
      (Γ2 ++ A0 :: B0 :: Γ3, Imp A B)). apply ImpRRule_I.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
      pose (dlCons x1 DersNilF).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A :: A0 :: B0 :: Γ3, B)])
      (Γ2 ++ A :: And A0 B0 :: Γ3, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AndLRule  [(Γ2 ++ A :: A0 :: B0 :: Γ3, B)]
        ((Γ2 ++ []) ++ A :: And A0 B0 :: Γ3, B)).
        assert (Γ2 ++ A :: A0 :: B0 :: Γ3 = (Γ2 ++ [A]) ++ A0 :: B0 :: Γ3). repeat rewrite <- app_assoc ; auto.
        assert ((Γ2 ++ []) ++ A :: And A0 B0 :: Γ3 = (Γ2 ++ [A]) ++ And A0 B0 :: Γ3). repeat rewrite <- app_assoc ; auto.
        rewrite H0. clear H0. rewrite H1. clear H1. apply AndLRule_I. apply AndL in H0.
        assert (J4: ImpRRule [(Γ2 ++ A :: A0 :: B0 :: Γ3, B)]
        (Γ2 ++ A0 :: B0 :: Γ3, Imp A B)). apply ImpRRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        pose (dlCons x0 DersNilF).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A :: A0 :: B0 :: Γ3, B)])
       ((Γ2 ++ []) ++ A :: And A0 B0 :: Γ3, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { inversion e0.  subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
         pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
         assert (AndLRule  [(Γ2 ++ A0 :: B0 :: x ++ A :: Γ1, B)]
       ((Γ2 ++ And A0 B0 :: x) ++ A :: Γ1, B)). repeat rewrite <- app_assoc. apply AndLRule_I. apply AndL in H0.
        assert (J4: ImpRRule [((Γ2 ++ A0 :: B0 :: x) ++ A :: Γ1, B)]
        ((Γ2 ++ A0 :: B0 :: x) ++ Γ1, Imp A B)). apply ImpRRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        pose (dlCons x1 DersNilF).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: B0 :: x ++ A :: Γ1, B)])
        ((Γ2 ++ And A0 B0 :: x) ++ A :: Γ1, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
    + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AndLRule  [((Γ0 ++ A :: x) ++ A0 :: B0 :: Γ3, B)]
      ((Γ0 ++ A :: x) ++ And A0 B0 :: Γ3, B)). apply AndLRule_I. apply AndL in H0. repeat rewrite <- app_assoc in H0.
      simpl in H0.
      assert (J4: ImpRRule [(Γ0 ++ A :: x ++ A0 :: B0 :: Γ3, B)]
      ((Γ0 ++ x) ++ A0 :: B0 :: Γ3, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
      pose (dlCons x1 DersNilF).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ A :: x ++ A0 :: B0 :: Γ3, B)])
      (Γ0 ++ A :: x ++ And A0 B0 :: Γ3, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrR1 *)
  * inversion H.
  (* OrR2 *)
  * inversion H.
  (* OrL *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (OrLRule [((Γ2 ++ [A]) ++ A0:: Γ3, B);((Γ2 ++ [A]) ++ B0 :: Γ3, B)]
      ((Γ2 ++ [A]) ++ Or A0 B0 :: Γ3, B)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (J4: ImpRRule [(Γ2 ++ A :: A0 :: Γ3, B)]
      (Γ2 ++ A0 :: Γ3, Imp A B)). apply ImpRRule_I.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
      assert (J7: ImpRRule [(Γ2 ++ A :: B0 :: Γ3, B)]
      (Γ2 ++ B0 :: Γ3, Imp A B)). apply ImpRRule_I.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9). pose (s _ J7). destruct s0. clear s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A :: A0 :: Γ3, B); (Γ2 ++ A :: B0 :: Γ3, B)])
      (Γ2 ++ A :: Or A0 B0 :: Γ3, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        repeat rewrite <- app_assoc. simpl.
        assert (OrLRule [((Γ2 ++ [A]) ++ A0:: Γ3, B);((Γ2 ++ [A]) ++ B0 :: Γ3, B)]
        ((Γ2 ++ [A]) ++ Or A0 B0 :: Γ3, B)). apply OrLRule_I. apply OrL in H0.
        repeat rewrite <- app_assoc in H0. simpl in H0.
        assert (J4: ImpRRule [(Γ2 ++ A :: A0 :: Γ3, B)]
        (Γ2 ++ A0 :: Γ3, Imp A B)). apply ImpRRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        assert (J7: ImpRRule [(Γ2 ++ A :: B0 :: Γ3, B)]
        (Γ2 ++ B0 :: Γ3, Imp A B)). apply ImpRRule_I.
        assert (J8: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J8 _ _ J9). pose (s _ J7). destruct s0. clear s.
        pose (dlCons x2 DersNilF). pose (dlCons x1 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A :: A0 :: Γ3, B); (Γ2 ++ A :: B0 :: Γ3, B)])
        (Γ2 ++ A :: Or A0 B0 :: Γ3, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        repeat rewrite <- app_assoc. simpl.
        assert (OrLRule [(Γ2 ++ A0 :: x ++ A :: Γ1, B);(Γ2 ++ B0 :: x ++ A :: Γ1, B)]
        (Γ2 ++ Or A0 B0 :: x ++ A :: Γ1, B)). apply OrLRule_I. apply OrL in H0.
        assert (J4: ImpRRule [((Γ2 ++ A0 :: x) ++ A :: Γ1, B)]
        ((Γ2 ++ A0 :: x) ++ Γ1, Imp A B)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        assert (J7: ImpRRule [((Γ2 ++ B0 :: x) ++ A :: Γ1, B)]
        ((Γ2 ++ B0 :: x) ++ Γ1, Imp A B)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J7. simpl in J7.
        assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J8 _ _ J9). pose (s _ J7). destruct s0. clear s.
        pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: x ++ A :: Γ1, B); (Γ2 ++ B0 :: x ++ A :: Γ1, B)])
        (Γ2 ++ Or A0 B0 :: x ++ A :: Γ1, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
    +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (OrLRule [((Γ0 ++ A :: x) ++ A0 :: Γ3, B);((Γ0 ++ A :: x) ++ B0 :: Γ3, B)]
        ((Γ0 ++ A :: x) ++ Or A0 B0 :: Γ3, B)). apply OrLRule_I. apply OrL in H0.
        repeat rewrite <- app_assoc in H0. simpl in H0.
        assert (J4: ImpRRule [(Γ0 ++ A :: x ++ A0 :: Γ3, B)]
        ((Γ0 ++ x) ++ A0 :: Γ3, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        assert (J7: ImpRRule [(Γ0 ++ A :: x ++ B0 :: Γ3, B)]
        ((Γ0 ++ x) ++ B0 :: Γ3, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
        assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J8 _ _ J9). pose (s _ J7). destruct s0. clear s.
        pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A :: x ++ A0 :: Γ3, B); (Γ0 ++ A :: x ++ B0 :: Γ3, B)])
        (Γ0 ++ A :: x ++ Or A0 B0 :: Γ3, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J1: derrec_height x = derrec_height x). auto.
    assert (J2: list_exch_L (Γ2 ++ A :: Γ3, B) (A :: Γ0 ++ Γ1, B)).
    rewrite <- H2. assert (A :: Γ2 ++ Γ3 = [] ++ [A] ++ Γ2 ++ [] ++ Γ3). auto. rewrite H0.
    assert (Γ2 ++ A :: Γ3 = [] ++ [] ++ Γ2 ++ [A] ++ Γ3). auto. rewrite H1. apply list_exch_LI.
    pose (GL4ip_hpadm_list_exch_L (derrec_height x) (Γ2 ++ A :: Γ3, B) x J1 (A :: Γ0 ++ Γ1, B) J2).
    destruct s.
    assert (J3: derrec_height x0 = derrec_height x0). auto.
    assert (J4: list_exch_L (A :: Γ0 ++ Γ1, B) (Γ0 ++ A :: Γ1, B)).
    assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). auto. rewrite H0.
    assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). auto. rewrite H1. apply list_exch_LI.
    pose (GL4ip_hpadm_list_exch_L (derrec_height x0) (A :: Γ0 ++ Γ1, B) x0 J3 (Γ0 ++ A :: Γ1, B) J4).
    destruct s. exists x1. lia.
  (* AtomImpL1 *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
 + simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AtomImpL1Rule  [((Γ2 ++ [A]) ++ # P :: Γ3 ++ A0 :: Γ4, B)]
      ((Γ2 ++ [A]) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, B)). apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (J4: ImpRRule [(Γ2 ++ A :: # P :: Γ3 ++ A0 :: Γ4, B)]
      (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, Imp A B)). apply ImpRRule_I.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
      pose (dlCons x1 DersNilF).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A :: # P :: Γ3 ++ A0 :: Γ4, B)])
      (Γ2 ++ A :: # P :: Γ3 ++ Imp # P A0 :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL1Rule  [(Γ2 ++ A :: # P :: Γ3 ++ A0 :: Γ4, B)]
        ((Γ2 ++ []) ++ A :: # P :: Γ3 ++ Imp # P A0 :: Γ4, B)).
        assert (Γ2 ++ A ::# P :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ [A]) ++ # P :: Γ3 ++ A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
        assert ((Γ2 ++ []) ++ A :: # P :: Γ3 ++ Imp # P A0 :: Γ4 = (Γ2 ++ [A]) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
        rewrite H0. clear H0. rewrite H1. clear H1. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
        assert (J4: ImpRRule [(Γ2 ++ A :: # P :: Γ3 ++ A0 :: Γ4, B)]
        (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, Imp A B)). apply ImpRRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        pose (dlCons x0 DersNilF).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A :: # P :: Γ3 ++ A0 :: Γ4, B)])
        ((Γ2 ++ []) ++ A :: # P :: Γ3 ++ Imp # P A0 :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { inversion e0.  subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
        - assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
          assert (AtomImpL1Rule  [(Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4, B)]
          ((Γ2 ++ # P :: Γ3) ++ A :: Imp # P A0 :: Γ4, B)).
          assert ((Γ2 ++ # P :: Γ3) ++ A :: Imp # P A0 :: Γ4 =Γ2 ++ # P :: (Γ3 ++ [A]) ++ Imp # P A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H0. clear H0. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
          assert (J4: ImpRRule [(Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4, B)]
          (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, Imp A B)).
          assert (Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4 = (Γ2 ++ # P :: Γ3) ++ A :: A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
          assert (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ # P :: Γ3) ++ A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H1. rewrite H2. apply ImpRRule_I.
          assert (J5: derrec_height x < S (dersrec_height d)). lia.
          assert (J6: derrec_height x = derrec_height x). reflexivity.
          pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
          pose (dlCons x1 DersNilF).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4, B)])
          ((Γ2 ++ # P :: Γ3) ++ A :: Imp # P A0 :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity.
        - destruct x0 ; simpl in e1 ; subst.
          * assert (J30: dersrec_height d = dersrec_height d). reflexivity.
            pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
            assert (AtomImpL1Rule  [(Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4, B)]
            ((Γ2 ++ # P :: Γ3 ++ []) ++ A :: Imp # P A0 :: Γ4, B)).
            assert ((Γ2 ++ # P :: Γ3 ++ []) ++ A :: Imp # P A0 :: Γ4 =Γ2 ++ # P :: (Γ3 ++ [A]) ++ Imp # P A0 :: Γ4).
            repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
            rewrite H0. clear H0. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
            assert (J4: ImpRRule [(Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4, B)]
            (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, Imp A B)).
            assert (Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4 = (Γ2 ++ # P :: Γ3) ++ A :: A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
            assert (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ # P :: Γ3) ++ A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
            rewrite H1. rewrite H2. apply ImpRRule_I.
            assert (J5: derrec_height x < S (dersrec_height d)). lia.
            assert (J6: derrec_height x = derrec_height x). reflexivity.
            pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
            pose (dlCons x0 DersNilF).
            pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
            (ps:=[(Γ2 ++ # P :: (Γ3 ++ [A]) ++ A0 :: Γ4, B)])
            ((Γ2 ++ # P :: Γ3 ++ []) ++ A :: Imp # P A0 :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
            lia. reflexivity.
          * inversion e1. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
            pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
            assert (AtomImpL1Rule  [((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ A :: Γ1, B)]
            ((Γ2 ++ # P :: Γ3 ++ Imp # P A0 :: x0) ++ A :: Γ1, B)). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
            assert (J4: ImpRRule [((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ A :: Γ1, B)]
            ((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ Γ1, Imp A B)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
            assert (J5: derrec_height x < S (dersrec_height d)). lia.
            assert (J6: derrec_height x = derrec_height x). reflexivity.
            pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
            pose (dlCons x1 DersNilF). rewrite <- app_assoc in H0. simpl in H0. rewrite <- app_assoc in H0.
            pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
            (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: x0 ++ A :: Γ1, B)])
            ((Γ2 ++ # P :: Γ3 ++ Imp # P A0 :: x0) ++ A :: Γ1, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
            lia. reflexivity.
        - assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
          assert (AtomImpL1Rule  [(Γ2 ++ # P :: (x ++ A :: x0) ++ A0 :: Γ4, B)]
          ((Γ2 ++ # P :: x) ++ A :: x0 ++ Imp # P A0 :: Γ4, B)).
          assert ((Γ2 ++ # P :: x) ++ A :: x0 ++ Imp # P A0 :: Γ4 = Γ2 ++ # P :: (x ++ A :: x0) ++ Imp # P A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H0. clear H0. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
          assert (J4: ImpRRule [(Γ2 ++ # P :: (x ++ A :: x0) ++ A0 :: Γ4, B)]
          (Γ2 ++ # P :: (x ++ x0) ++ A0 :: Γ4, Imp A B)).
          assert (Γ2 ++ # P :: (x ++ x0) ++ A0 :: Γ4 = (Γ2 ++ # P :: x) ++ x0 ++ A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
          assert (Γ2 ++ # P :: (x ++ A :: x0) ++ A0 :: Γ4 = (Γ2 ++ # P :: x) ++ A :: x0 ++ A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H1. rewrite H2. apply ImpRRule_I.
          assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
          assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
          pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
          pose (dlCons x2 DersNilF).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ2 ++ # P :: (x ++ A :: x0) ++ A0 :: Γ4, B)])
          ((Γ2 ++ # P :: x) ++ A :: x0 ++ Imp # P A0 :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity. }
    + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL1Rule  [(Γ0 ++ A :: x ++ # P :: Γ3 ++ A0 :: Γ4, B)]
       (Γ0 ++ A :: x ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, B)).
       assert (Γ0 ++ A :: x ++ # P :: Γ3 ++ Imp # P A0 :: Γ4 = (Γ0 ++ A :: x) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4). repeat rewrite <- app_assoc ; auto.
       assert (Γ0 ++ A :: x ++ # P :: Γ3 ++ A0 :: Γ4 = (Γ0 ++ A :: x) ++ # P :: Γ3 ++ A0 :: Γ4). repeat rewrite <- app_assoc ; auto. 
       rewrite H0. rewrite H1. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
       assert (J4: ImpRRule [(Γ0 ++ A :: x ++ # P :: Γ3 ++ A0 :: Γ4, B)]
       ((Γ0 ++ x) ++ # P :: Γ3 ++ A0 :: Γ4, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
       pose (dlCons x1 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:= [(Γ0 ++ A :: x ++ # P :: Γ3 ++ A0 :: Γ4, B)])
       (Γ0 ++ A :: x ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
       lia. reflexivity.
  (* AtomImpL2 *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
 + simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AtomImpL2Rule  [((Γ2 ++ [A]) ++ A0 :: Γ3 ++ # P :: Γ4, B)]
      ((Γ2 ++ [A]) ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, B)). apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (J4: ImpRRule [(Γ2 ++ A :: A0 :: Γ3 ++ # P :: Γ4, B)]
      (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, Imp A B)). apply ImpRRule_I.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
      pose (dlCons x1 DersNilF).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A ::A0 :: Γ3 ++  # P :: Γ4, B)])
      (Γ2 ++ A :: Imp # P A0 :: Γ3 ++ # P :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL2Rule  [(Γ2 ++ A ::A0  :: Γ3 ++ # P :: Γ4, B)]
        ((Γ2 ++ []) ++ A ::  Imp # P A0 :: Γ3 ++# P :: Γ4, B)).
        assert (Γ2 ++ A :: A0 :: Γ3 ++ # P :: Γ4 = (Γ2 ++ [A]) ++ A0 :: Γ3 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
        assert ((Γ2 ++ []) ++ A :: Imp # P A0 :: Γ3 ++ # P :: Γ4 = (Γ2 ++ [A]) ++ Imp # P A0 :: Γ3 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
        rewrite H0. clear H0. rewrite H1. clear H1. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
        assert (J4: ImpRRule [(Γ2 ++ A :: A0 :: Γ3 ++ # P :: Γ4, B)]
        (Γ2 ++ A0  :: Γ3 ++ # P :: Γ4, Imp A B)). apply ImpRRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        pose (dlCons x0 DersNilF).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A :: A0 :: Γ3 ++ # P :: Γ4, B)])
        ((Γ2 ++ []) ++ A ::Imp # P A0  :: Γ3 ++ # P :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { inversion e0.  subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
        - assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
          assert (AtomImpL2Rule  [(Γ2 ++ A0 :: (Γ3 ++ [A]) ++ # P :: Γ4, B)]
          ((Γ2 ++ Imp # P A0 :: Γ3) ++ A ::# P  :: Γ4, B)).
          assert ((Γ2 ++ Imp # P A0 :: Γ3) ++ A :: # P :: Γ4 =Γ2 ++ Imp # P A0 :: (Γ3 ++ [A]) ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H0. clear H0. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
          assert (J4: ImpRRule [(Γ2 ++ A0 :: (Γ3 ++ [A]) ++ # P :: Γ4, B)]
          (Γ2 ++A0 :: Γ3 ++ # P :: Γ4, Imp A B)).
          assert (Γ2 ++A0  :: (Γ3 ++ [A]) ++ # P :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ A :: # P :: Γ4). repeat rewrite <- app_assoc ; auto.
          assert (Γ2 ++A0  :: Γ3 ++ # P :: Γ4 = (Γ2 ++ A0:: Γ3) ++ # P  :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H1. rewrite H2. apply ImpRRule_I.
          assert (J5: derrec_height x < S (dersrec_height d)). lia.
          assert (J6: derrec_height x = derrec_height x). reflexivity.
          pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
          pose (dlCons x1 DersNilF).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ2 ++ A0 :: (Γ3 ++ [A]) ++ # P :: Γ4, B)])
          ((Γ2 ++ Imp # P A0 :: Γ3) ++ A :: # P :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity.
        - destruct x0 ; simpl in e1 ; subst.
          * assert (J30: dersrec_height d = dersrec_height d). reflexivity.
            pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
            assert (AtomImpL2Rule  [(Γ2 ++ A0 :: (Γ3 ++ [A]) ++ # P :: Γ4, B)]
            ((Γ2 ++ Imp # P A0 :: Γ3 ++ []) ++ A :: # P :: Γ4, B)).
            assert ((Γ2 ++ Imp # P A0 :: Γ3 ++ []) ++ A :: # P :: Γ4 =Γ2 ++ Imp # P A0 :: (Γ3 ++ [A]) ++ # P :: Γ4).
            repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
            rewrite H0. clear H0. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
            assert (J4: ImpRRule [(Γ2 ++A0  :: (Γ3 ++ [A]) ++ # P :: Γ4, B)]
            (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, Imp A B)).
            assert (Γ2 ++ A0 :: (Γ3 ++ [A]) ++ # P :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ A :: # P :: Γ4). repeat rewrite <- app_assoc ; auto.
            assert (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
            rewrite H1. rewrite H2. apply ImpRRule_I.
            assert (J5: derrec_height x < S (dersrec_height d)). lia.
            assert (J6: derrec_height x = derrec_height x). reflexivity.
            pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
            pose (dlCons x0 DersNilF).
            pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
            (ps:=[(Γ2 ++ A0 :: (Γ3 ++ [A]) ++ # P :: Γ4, B)])
            ((Γ2 ++ Imp # P A0 :: Γ3 ++ []) ++ A :: # P :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
            lia. reflexivity.
          * inversion e1. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
            pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
            assert (AtomImpL2Rule  [((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ A :: Γ1, B)]
            ((Γ2 ++ Imp # P A0 :: Γ3 ++ # P :: x0) ++ A :: Γ1, B)). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
            assert (J4: ImpRRule [((Γ2 ++  A0 :: Γ3 ++ # P :: x0) ++ A :: Γ1, B)]
            ((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ Γ1, Imp A B)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
            assert (J5: derrec_height x < S (dersrec_height d)). lia.
            assert (J6: derrec_height x = derrec_height x). reflexivity.
            pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
            pose (dlCons x1 DersNilF). rewrite <- app_assoc in H0. simpl in H0. rewrite <- app_assoc in H0.
            pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
            (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: x0 ++ A :: Γ1, B)])
            ((Γ2 ++ Imp # P A0 :: Γ3 ++ # P :: x0) ++ A :: Γ1, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
            lia. reflexivity.
        - assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
          assert (AtomImpL2Rule  [(Γ2 ++ A0 :: (x ++ A :: x0) ++ # P :: Γ4, B)]
          ((Γ2 ++ Imp # P A0 :: x) ++ A :: x0 ++ # P :: Γ4, B)).
          assert ((Γ2 ++ Imp # P A0 :: x) ++ A :: x0 ++ # P :: Γ4 = Γ2 ++ Imp # P A0 :: (x ++ A :: x0) ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H0. clear H0. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
          assert (J4: ImpRRule [(Γ2 ++A0  :: (x ++ A :: x0) ++ # P :: Γ4, B)]
          (Γ2 ++ A0 :: (x ++ x0) ++ # P :: Γ4, Imp A B)).
          assert (Γ2 ++  A0:: (x ++ x0) ++ # P :: Γ4 = (Γ2 ++A0  :: x) ++ x0 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
          assert (Γ2 ++ A0 :: (x ++ A :: x0) ++ # P :: Γ4 = (Γ2 ++ A0 :: x) ++ A :: x0 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
          rewrite H1. rewrite H2. apply ImpRRule_I.
          assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
          assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
          pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
          pose (dlCons x2 DersNilF).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ2 ++A0  :: (x ++ A :: x0) ++ # P :: Γ4, B)])
          ((Γ2 ++  Imp # P A0 :: x) ++ A :: x0 ++ # P :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity. }
    + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL2Rule  [(Γ0 ++ A :: x ++ A0 :: Γ3 ++ # P :: Γ4, B)]
       (Γ0 ++ A :: x ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, B)).
       assert (Γ0 ++ A :: x ++ Imp # P A0 :: Γ3 ++ # P :: Γ4 = (Γ0 ++ A :: x) ++ Imp # P A0 :: Γ3 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto.
       assert (Γ0 ++ A :: x ++ A0 :: Γ3 ++ # P :: Γ4 = (Γ0 ++ A :: x) ++ A0 :: Γ3 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto. 
       rewrite H0. rewrite H1. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
       assert (J4: ImpRRule [(Γ0 ++ A :: x ++ A0  :: Γ3 ++ # P:: Γ4, B)]
       ((Γ0 ++ x) ++ A0 :: Γ3 ++ # P :: Γ4, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
       pose (dlCons x1 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:= [(Γ0 ++ A :: x ++ A0 :: Γ3 ++ # P :: Γ4, B)])
       (Γ0 ++ A :: x ++Imp # P A0 :: Γ3 ++ # P :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
       lia. reflexivity.
 (* AndImpL *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AndImpLRule  [((Γ2 ++ [A]) ++ Imp A0 (Imp B0 C) :: Γ3, B)]
       ((Γ2 ++ [A]) ++ Imp (And A0 B0) C :: Γ3, B)). apply AndImpLRule_I. apply AndImpL in H0.
       repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: ImpRRule [(Γ2 ++ A :: Imp A0 (Imp B0 C) :: Γ3, B)]
       (Γ2 ++ Imp A0 (Imp B0 C) :: Γ3, Imp A B)). apply ImpRRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
       pose (dlCons x1 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ2 ++ A :: Imp A0 (Imp B0 C) :: Γ3, B)])
       (Γ2 ++ A :: Imp (And A0 B0) C :: Γ3, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
       lia. reflexivity.
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
         pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
         assert (AndImpLRule  [((Γ2 ++ [A]) ++ Imp A0 (Imp B0 C) :: Γ3, B)]
         ((Γ2 ++ []) ++ A :: Imp (And A0 B0) C :: Γ3, B)).
         assert ((Γ2 ++ []) ++ A :: Imp (And A0 B0) C :: Γ3 = (Γ2 ++ [A]) ++ Imp (And A0 B0) C :: Γ3).
         repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply AndImpLRule_I. apply AndImpL in H0.
         assert (J4: ImpRRule [((Γ2 ++ [A]) ++ Imp A0 (Imp B0 C) :: Γ3, B)]
        (Γ2 ++ Imp A0 (Imp B0 C) :: Γ3, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
         assert (J5: derrec_height x < S (dersrec_height d)). lia.
         assert (J6: derrec_height x = derrec_height x). reflexivity.
         pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
         pose (dlCons x0 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ [A]) ++ Imp A0 (Imp B0 C) :: Γ3, B)])
         ((Γ2 ++ []) ++ A :: Imp (And A0 B0) C :: Γ3, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
         lia. reflexivity. }
      { inversion e0.  subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
         pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
         assert (AndImpLRule  [(Γ2 ++ Imp A0 (Imp B0 C) :: x ++ A :: Γ1, B)]
         ((Γ2 ++ Imp (And A0 B0) C :: x) ++ A :: Γ1, B)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
         apply AndImpL in H0.
         assert (J4: ImpRRule [((Γ2 ++ Imp A0 (Imp B0 C) :: x) ++ A :: Γ1, B)]
         ((Γ2 ++ Imp A0 (Imp B0 C) :: x) ++ Γ1, Imp A B)). apply ImpRRule_I. repeat rewrite <- app_assoc in J4.
         simpl in J4.
         assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
         pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
         pose (dlCons x1 DersNilF).
         pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
         (ps:=[(Γ2 ++ Imp A0 (Imp B0 C) :: x ++ A :: Γ1, B)])
         ((Γ2 ++ Imp (And A0 B0) C :: x) ++ A :: Γ1, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
         lia. reflexivity. }
    + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AndImpLRule [((Γ0 ++ A :: x) ++ Imp A0 (Imp B0 C) :: Γ3, B)]
       ((Γ0 ++ A :: x) ++ Imp (And A0 B0) C :: Γ3, B)). apply AndImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: ImpRRule [(Γ0 ++ A :: x ++ Imp A0 (Imp B0 C) :: Γ3, B)]
       ((Γ0 ++ x) ++ Imp A0 (Imp B0 C) :: Γ3, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
       pose (dlCons x1 DersNilF). apply AndImpL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: x ++ Imp A0 (Imp B0 C) :: Γ3, B)])
       (Γ0 ++ A :: x ++ Imp (And A0 B0) C :: Γ3, B) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule  [((Γ2 ++ [A]) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)]
       ((Γ2 ++ [A]) ++ Imp (Or A0 B0) C :: Γ3 ++ Γ4, B)). apply OrImpLRule_I. apply OrImpL in H0.
       repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: ImpRRule [(Γ2 ++ A :: Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)]
       (Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, Imp A B)). apply ImpRRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
       pose (dlCons x1 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ2 ++ A :: Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)])
       (Γ2 ++ A :: Imp (Or A0 B0) C :: Γ3 ++ Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
       lia. reflexivity.
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule  [((Γ2 ++ [A]) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)]
       ((Γ2 ++ []) ++ A :: Imp (Or A0 B0) C :: Γ3 ++ Γ4, B)).
       assert ((Γ2 ++ []) ++ A :: Imp (Or A0 B0) C :: Γ3 ++ Γ4 = (Γ2 ++ [A]) ++ Imp (Or A0 B0) C :: Γ3 ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0. apply OrImpLRule_I. apply OrImpL in H0.
       assert (J4: ImpRRule [((Γ2 ++ [A]) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)]
       (Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
       pose (dlCons x0 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ [A]) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)])
       ((Γ2 ++ []) ++ A :: Imp (Or A0 B0) C :: Γ3 ++ Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
       lia. reflexivity. }
      { inversion e0.  subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
         pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
         apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
         - assert (OrImpLRule  [(Γ2 ++ Imp A0 C :: Γ3 ++  Imp B0 C :: A :: Γ4, B)]
           ((Γ2 ++ Imp (Or A0 B0) C :: Γ3) ++ A :: Γ4, B)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
           apply OrImpL in H0.
           assert (J4: ImpRRule [((Γ2 ++ Imp A0 C :: Γ3 ++ [Imp B0 C]) ++ A :: Γ4, B)]
           ((Γ2 ++ Imp A0 C :: Γ3 ++ [Imp B0 C]) ++ Γ4, Imp A B)). apply ImpRRule_I.
           repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
           assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
           assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
           pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
           pose (dlCons x DersNilF).
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: A :: Γ4, B)])
           ((Γ2 ++ Imp (Or A0 B0) C :: Γ3) ++ A :: Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
           lia. reflexivity.
         - assert (OrImpLRule  [(Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1 ++ A :: Γ1, B)]
           ((Γ2 ++ Imp (Or A0 B0) C :: Γ3 ++ x1) ++ A :: Γ1, B)). repeat rewrite <- app_assoc.
           simpl. repeat rewrite <- app_assoc. apply OrImpLRule_I. apply OrImpL in H0.
           assert (J4: ImpRRule [(Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1 ++ A :: Γ1, B)]
           (Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1 ++ Γ1, Imp A B)).
           assert (Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1 ++ A :: Γ1 = (Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1) ++ A :: Γ1).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
           assert (Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1 ++ Γ1 = (Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1) ++ Γ1).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.
           apply ImpRRule_I.
           assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
           assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
           pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
           pose (dlCons x DersNilF).
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(Γ2 ++ Imp A0 C :: Γ3 ++ Imp B0 C :: x1 ++ A :: Γ1, B)])
           ((Γ2 ++ Imp (Or A0 B0) C :: Γ3 ++ x1) ++ A :: Γ1, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
           lia. reflexivity.
         - assert (OrImpLRule  [((Γ2 ++ Imp A0 C :: x) ++ A :: x1 ++ Imp B0 C :: Γ4, B)]
           ((Γ2 ++ Imp (Or A0 B0) C :: x) ++ A :: x1 ++ Γ4, B)).
           assert ((Γ2 ++ Imp A0 C :: x) ++ A :: x1 ++ Imp B0 C :: Γ4 = Γ2 ++ Imp A0 C :: (x ++ A :: x1) ++ Imp B0 C :: Γ4).
           repeat rewrite <- app_assoc. auto. rewrite H0.
           assert ((Γ2 ++ Imp (Or A0 B0) C :: x) ++ A :: x1 ++ Γ4 = Γ2 ++ Imp (Or A0 B0) C :: (x ++ A :: x1) ++ Γ4).
           repeat rewrite <- app_assoc. auto. rewrite H1.
           apply OrImpLRule_I. apply OrImpL in H0.
           assert (J4: ImpRRule [((Γ2 ++ Imp A0 C :: x) ++ A :: x1 ++ Imp B0 C :: Γ4, B)]
           (Γ2 ++ Imp A0 C :: (x ++ x1) ++ Imp B0 C :: Γ4, Imp A B)).
           assert (Γ2 ++ Imp A0 C :: (x ++ x1) ++ Imp B0 C :: Γ4 = (Γ2 ++ Imp A0 C :: x) ++ x1 ++ Imp B0 C :: Γ4).
           repeat rewrite <- app_assoc. auto. rewrite H1. apply ImpRRule_I.
           assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
           assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
           pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
           pose (dlCons x2 DersNilF).
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[((Γ2 ++ Imp A0 C :: x) ++ A :: x1 ++ Imp B0 C :: Γ4, B)])
           ((Γ2 ++ Imp (Or A0 B0) C :: x) ++ A :: x1 ++ Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
           lia. reflexivity. }
    + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule  [((Γ0 ++ A :: x) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)]
       (Γ0 ++ A :: x ++ Imp (Or A0 B0) C :: Γ3 ++ Γ4, B)).
       assert (Γ0 ++ A :: x ++ Imp (Or A0 B0) C :: Γ3 ++ Γ4 = (Γ0 ++ A :: x) ++ Imp (Or A0 B0) C :: Γ3 ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       apply OrImpLRule_I. apply OrImpL in H0.
       assert (J4: ImpRRule [((Γ0 ++ A :: x) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)]
       ((Γ0 ++ x) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, Imp A B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
       pose (dlCons x1 DersNilF).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ0 ++ A :: x) ++ Imp A0 C :: Γ3 ++ Imp B0 C :: Γ4, B)])
       (Γ0 ++ A :: x ++ Imp (Or A0 B0) C :: Γ3 ++ Γ4, B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
       lia. reflexivity.
  (* ImpImpL *)
 * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (ImpImpLRule [(Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0); (Γ2 ++ A :: C :: Γ3, B)]
      (Γ2 ++ A :: Imp (Imp A0 B0) C :: Γ3, B)).
      assert (Γ2 ++ A :: Imp B0 C :: Γ3 = (Γ2 ++ [A]) ++ Imp B0 C :: Γ3). repeat rewrite <- app_assoc ; auto.
      rewrite H0. assert (Γ2 ++ A :: C :: Γ3 = (Γ2 ++ [A]) ++ C :: Γ3). repeat rewrite <- app_assoc ; auto.
      rewrite H1. assert (Γ2 ++ A :: Imp (Imp A0 B0) C :: Γ3 = (Γ2 ++ [A]) ++ Imp (Imp A0 B0) C :: Γ3). repeat rewrite <- app_assoc ; auto.
      rewrite H2. apply ImpImpLRule_I. apply ImpImpL in H0.
      assert (J4: ImpRRule [(Γ2 ++ A :: C :: Γ3, B)] (Γ2 ++ C :: Γ3, Imp A B)). apply ImpRRule_I.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
      assert (J1: derrec_height x0 = derrec_height x0). auto.
      assert (J2: wkn_L A (Γ2 ++ Imp B0 C :: Γ3, Imp A0 B0) (Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0)).
      apply wkn_LI.
      pose (@GL4ip_wkn_L (derrec_height x0) _ x0 J1 (Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0) A J2). destruct s.
      pose (dlCons x2 DersNilF). pose (dlCons x3 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0); (Γ2 ++ A :: C :: Γ3, B)])
      (Γ2 ++ A :: Imp (Imp A0 B0) C :: Γ3, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
        assert (ImpImpLRule [(Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0); (Γ2 ++ A :: C :: Γ3, B)]
        ((Γ2 ++ []) ++ A :: Imp (Imp A0 B0) C :: Γ3, B)).
        assert (Γ2 ++ A :: Imp B0 C :: Γ3 = (Γ2 ++ [A]) ++ Imp B0 C :: Γ3). repeat rewrite <- app_assoc ; auto.
        rewrite H0. assert (Γ2 ++ A :: C :: Γ3 = (Γ2 ++ [A]) ++ C :: Γ3). repeat rewrite <- app_assoc ; auto.
        rewrite H1. assert ((Γ2 ++ []) ++ A :: Imp (Imp A0 B0) C :: Γ3 = (Γ2 ++ [A]) ++ Imp (Imp A0 B0) C :: Γ3). repeat rewrite <- app_assoc ; auto.
        rewrite H2. apply ImpImpLRule_I. apply ImpImpL in H0.
        assert (J4: ImpRRule [(Γ2 ++ A :: C :: Γ3, B)] (Γ2 ++ C :: Γ3, Imp A B)). apply ImpRRule_I.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        assert (J1: derrec_height x = derrec_height x). auto.
        assert (J2: wkn_L A (Γ2 ++ Imp B0 C :: Γ3, Imp A0 B0) (Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0)).
        apply wkn_LI.
        pose (@GL4ip_wkn_L (derrec_height x) _ x J1 (Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0) A J2). destruct s.
        pose (dlCons x1 DersNilF). pose (dlCons x2 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A :: Imp B0 C :: Γ3, Imp A0 B0); (Γ2 ++ A :: C :: Γ3, B)])
        ((Γ2 ++ []) ++ A :: Imp (Imp A0 B0) C :: Γ3, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        repeat rewrite <- app_assoc. simpl.
        assert (ImpImpLRule [(Γ2 ++ Imp B0 C :: x ++ A :: Γ1, Imp A0 B0); (Γ2 ++ C :: x ++ A :: Γ1, B)]
        (Γ2 ++ Imp (Imp A0 B0) C :: x ++ A :: Γ1, B)). apply ImpImpLRule_I. apply ImpImpL in H0.
        assert (J4: ImpRRule [(Γ2 ++ C :: x ++ A :: Γ1, B)] (Γ2 ++ C :: x ++ Γ1, Imp A B)).
        assert (Γ2 ++ C :: x ++ A :: Γ1 = (Γ2 ++ C :: x) ++ A :: Γ1). repeat rewrite <- app_assoc ; auto.
        rewrite H1. assert (Γ2 ++ C :: x ++ Γ1 = (Γ2 ++ C :: x) ++ Γ1). repeat rewrite <- app_assoc ; auto.
        rewrite H2. apply ImpRRule_I.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        assert (J1: derrec_height x0 = derrec_height x0). auto.
        assert (J2: wkn_L A (Γ2 ++ Imp B0 C :: x ++ Γ1, Imp A0 B0) (Γ2 ++ Imp B0 C :: x ++ A :: Γ1, Imp A0 B0)).
        assert (Γ2 ++ Imp B0 C :: x ++ Γ1 = (Γ2 ++ Imp B0 C :: x) ++ Γ1). repeat rewrite <- app_assoc ; auto.
        rewrite H1. assert (Γ2 ++ Imp B0 C :: x ++ A :: Γ1 = (Γ2 ++ Imp B0 C :: x) ++ A :: Γ1). repeat rewrite <- app_assoc ; auto.
        rewrite H2. apply wkn_LI.
        pose (@GL4ip_wkn_L (derrec_height x0) _ x0 J1 _ A J2). destruct s.
        pose (dlCons x2 DersNilF). pose (dlCons x3 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ Imp B0 C :: x ++ A :: Γ1, Imp A0 B0); (Γ2 ++ C :: x ++ A :: Γ1, B)])
       (Γ2 ++ Imp (Imp A0 B0) C :: x ++ A :: Γ1, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
    + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        repeat rewrite <- app_assoc. simpl.
        assert (ImpImpLRule [((Γ0 ++ A :: x) ++ Imp B0 C :: Γ3, Imp A0 B0); ((Γ0 ++ A :: x) ++ C :: Γ3, B)]
        (Γ0 ++ A :: x ++ Imp (Imp A0 B0) C :: Γ3, B)).
        assert (Γ0 ++ A :: x ++ Imp (Imp A0 B0) C :: Γ3 =  (Γ0 ++ A :: x) ++ Imp (Imp A0 B0) C :: Γ3).
        repeat rewrite <- app_assoc ; auto. rewrite H0. apply ImpImpLRule_I. apply ImpImpL in H0.
        assert (J4: ImpRRule [((Γ0 ++ A :: x) ++ C :: Γ3, B)] ((Γ0 ++ x) ++ C :: Γ3, Imp A B)).
        repeat rewrite <- app_assoc. apply ImpRRule_I.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s.
        assert (J1: derrec_height x0 = derrec_height x0). auto.
        assert (J2: wkn_L A ((Γ0 ++ x) ++ Imp B0 C :: Γ3, Imp A0 B0) ((Γ0 ++ A :: x) ++ Imp B0 C :: Γ3, Imp A0 B0)).
        repeat rewrite <- app_assoc. apply wkn_LI.
        pose (@GL4ip_wkn_L (derrec_height x0) _ x0 J1 _ A J2). destruct s.
        pose (dlCons x2 DersNilF). pose (dlCons x3 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[((Γ0 ++ A :: x) ++ Imp B0 C :: Γ3, Imp A0 B0); ((Γ0 ++ A :: x) ++ C :: Γ3, B)])
        (Γ0 ++ A :: x ++ Imp (Imp A0 B0) C :: Γ3, B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity.
  (* BoxImpL *)
 * inversion X. subst. apply app2_find_hole in H. destruct H. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p. subst.
      assert (J4: ImpRRule [(Γ2 ++ A :: B0 :: Γ3, B)] (Γ2 ++ B0 :: Γ3, Imp A B)). apply ImpRRule_I.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s. destruct (dec_is_boxedT A).
      { assert (BoxImpLRule [(XBoxed_list (x2 ++ A :: x3) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)]
        (Γ2 ++ A :: Imp (Box A0) B0 :: Γ3, B)).
        assert (Γ2 ++ A :: Imp (Box A0) B0 :: Γ3 =  (Γ2 ++ [A]) ++ Imp (Box A0) B0 :: Γ3).
        repeat rewrite <- app_assoc ; auto. rewrite H.
        assert (Γ2 ++ A :: B0 :: Γ3 =  (Γ2 ++ [A]) ++ B0 :: Γ3).
        repeat rewrite <- app_assoc ; auto. rewrite H0. apply BoxImpLRule_I ; auto. intro.
        intros. apply in_app_or in H2. destruct H2. apply H1. apply in_or_app ; auto. inversion H2 ; subst. auto.
        apply H1 ; apply in_or_app ; auto. repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_combine.
        auto. apply univ_gen_ext_cons ; auto. apply BoxImpL in X0.
        assert (J1: derrec_height x0 = derrec_height x0). auto.
        assert (J2: wkn_L A (XBoxed_list (x2 ++ x3) ++ [Box A0], A0) ((XBoxed_list x2) ++ A :: (XBoxed_list x3) ++ [Box A0], A0)).
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
        pose (@GL4ip_wkn_L (derrec_height x0) _ x0 J1 _ A J2). destruct s.
        assert (J3: derrec_height x5 = derrec_height x5). auto.
        assert (J31: wkn_L (unBox_formula A) ((XBoxed_list x2) ++ A :: (XBoxed_list x3) ++ [Box A0], A0) (XBoxed_list (x2 ++ A :: x3) ++ [Box A0], A0)).
        repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. apply wkn_LI.
        pose (@GL4ip_wkn_L (derrec_height x5) _ x5 J3 _ (unBox_formula A) J31). destruct s.
        pose (dlCons x4 DersNilF). pose (dlCons x6 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(XBoxed_list (x2 ++ A :: x3) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)])
        (Γ2 ++ A :: Imp (Box A0) B0 :: Γ3, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { assert (BoxImpLRule [(XBoxed_list (x2 ++ x3) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)]
        (Γ2 ++ A :: Imp (Box A0) B0 :: Γ3, B)).
        assert (Γ2 ++ A :: Imp (Box A0) B0 :: Γ3 =  (Γ2 ++ [A]) ++ Imp (Box A0) B0 :: Γ3).
        repeat rewrite <- app_assoc ; auto. rewrite H.
        assert (Γ2 ++ A :: B0 :: Γ3 =  (Γ2 ++ [A]) ++ B0 :: Γ3).
        repeat rewrite <- app_assoc ; auto. rewrite H0. apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc. simpl.
        apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. apply BoxImpL in X0.
        pose (dlCons x4 DersNilF). pose (dlCons x0 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(XBoxed_list (x2 ++ x3) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)])
        (Γ2 ++ A :: Imp (Box A0) B0 :: Γ3, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
   + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
        apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p. subst.
        assert (J4: ImpRRule [(Γ2 ++ A :: B0 :: Γ3, B)] (Γ2 ++ B0 :: Γ3, Imp A B)). apply ImpRRule_I.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s. destruct (dec_is_boxedT A).
        - assert (BoxImpLRule [(XBoxed_list (x1 ++ A :: x2) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)]
          ((Γ2 ++ []) ++ A :: Imp (Box A0) B0 :: Γ3, B)).
          assert ((Γ2 ++ []) ++ A :: Imp (Box A0) B0 :: Γ3 =  (Γ2 ++ [A]) ++ Imp (Box A0) B0 :: Γ3).
          repeat rewrite <- app_assoc ; auto. rewrite H.
          assert (Γ2 ++ A :: B0 :: Γ3 =  (Γ2 ++ [A]) ++ B0 :: Γ3).
          repeat rewrite <- app_assoc ; auto. rewrite H0. apply BoxImpLRule_I ; auto. intro.
          intros. apply in_app_or in H2. destruct H2. apply H1. apply in_or_app ; auto. inversion H2 ; subst. auto.
          apply H1 ; apply in_or_app ; auto. repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_combine.
          auto. apply univ_gen_ext_cons ; auto. apply BoxImpL in X0.
          assert (J1: derrec_height x = derrec_height x). auto.
          assert (J2: wkn_L A (XBoxed_list (x1 ++ x2) ++ [Box A0], A0) ((XBoxed_list x1) ++ A :: (XBoxed_list x2) ++ [Box A0], A0)).
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
          pose (@GL4ip_wkn_L (derrec_height x) _ x J1 _ A J2). destruct s.
          assert (J3: derrec_height x4 = derrec_height x4). auto.
          assert (J31: wkn_L (unBox_formula A) ((XBoxed_list x1) ++ A :: (XBoxed_list x2) ++ [Box A0], A0) (XBoxed_list (x1 ++ A :: x2) ++ [Box A0], A0)).
          repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. apply wkn_LI.
          pose (@GL4ip_wkn_L (derrec_height x4) _ x4 J3 _ (unBox_formula A) J31). destruct s.
          pose (dlCons x3 DersNilF). pose (dlCons x5 d0).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(XBoxed_list (x1 ++ A :: x2) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)])
          ((Γ2 ++ []) ++ A :: Imp (Box A0) B0 :: Γ3, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
          lia. reflexivity.
        - assert (BoxImpLRule [(XBoxed_list (x1 ++ x2) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)]
          ((Γ2 ++ []) ++ A :: Imp (Box A0) B0 :: Γ3, B)).
          assert ((Γ2 ++ []) ++ A :: Imp (Box A0) B0 :: Γ3 =  (Γ2 ++ [A]) ++ Imp (Box A0) B0 :: Γ3).
          repeat rewrite <- app_assoc ; auto. rewrite H.
          assert (Γ2 ++ A :: B0 :: Γ3 =  (Γ2 ++ [A]) ++ B0 :: Γ3).
          repeat rewrite <- app_assoc ; auto. rewrite H0. apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc. simpl.
          apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. apply BoxImpL in X0.
          pose (dlCons x3 DersNilF). pose (dlCons x d0).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(XBoxed_list (x1 ++ x2) ++ [Box A0], A0); (Γ2 ++ A :: B0 :: Γ3, B)])
          ((Γ2 ++ []) ++ A :: Imp (Box A0) B0 :: Γ3, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
          lia. reflexivity. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
        apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p. subst. apply univ_gen_ext_splitR in u0.
        destruct u0. destruct s. repeat destruct p ; subst.
        assert (J4: ImpRRule [((Γ2 ++ B0 :: x) ++ A :: Γ1, B)] ((Γ2 ++ B0 :: x) ++ Γ1, Imp A B)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s. destruct (dec_is_boxedT A).
        - assert (BoxImpLRule [(XBoxed_list (x2 ++ x4 ++ A :: x5) ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A :: Γ1, B)]
          ((Γ2 ++ Imp (Box A0) B0 :: x) ++ A :: Γ1, B)). repeat rewrite <- app_assoc. apply BoxImpLRule_I ; auto.
          intro. intros. apply in_app_or in H. destruct H. apply H1. apply in_or_app ; auto. apply in_app_or in H. destruct H.
          apply H1. apply in_or_app ; right ; apply in_or_app;  auto. inversion H ; subst. auto.
          apply H1 ; apply in_or_app ; right ; apply in_or_app ; auto. apply univ_gen_ext_combine.
          auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto. apply BoxImpL in X0.
          assert (J1: derrec_height x0 = derrec_height x0). auto.
          assert (J2: wkn_L A (XBoxed_list (x2 ++ x4 ++ x5) ++ [Box A0], A0) ((XBoxed_list (x2 ++ x4)) ++ A :: (XBoxed_list x5) ++ [Box A0], A0)).
          assert (XBoxed_list (x2 ++ x4 ++ x5) ++ [Box A0] = (XBoxed_list (x2 ++ x4)) ++ (XBoxed_list x5) ++ [Box A0]).
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. auto. rewrite H. apply wkn_LI.
          pose (@GL4ip_wkn_L (derrec_height x0) _ x0 J1 _ A J2). destruct s.
          assert (J3: derrec_height x6 = derrec_height x6). auto.
          assert (J31: wkn_L (unBox_formula A)  (XBoxed_list (x2 ++ x4) ++ A :: XBoxed_list x5 ++ [Box A0], A0)
          (XBoxed_list (x2 ++ x4 ++ A :: x5) ++ [Box A0], A0)).
          assert (XBoxed_list (x2 ++ x4 ++ A :: x5) ++ [Box A0] = (XBoxed_list (x2 ++ x4)) ++ unBox_formula A :: A :: (XBoxed_list x5) ++ [Box A0]).
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. auto. rewrite H. apply wkn_LI.
          pose (@GL4ip_wkn_L (derrec_height x6) _ x6 J3 _ (unBox_formula A) J31). destruct s.
          pose (dlCons x3 DersNilF). pose (dlCons x7 d0).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(XBoxed_list (x2 ++ x4 ++ A :: x5) ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A :: Γ1, B)])
          ((Γ2 ++ Imp (Box A0) B0 :: x) ++ A :: Γ1, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
          lia. reflexivity.
        - assert (BoxImpLRule [(XBoxed_list (x2 ++ x4 ++ x5) ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A :: Γ1, B)]
          ((Γ2 ++ Imp (Box A0) B0 :: x) ++ A :: Γ1, B)). repeat rewrite <- app_assoc. apply BoxImpLRule_I ; auto.
          apply univ_gen_ext_combine ; auto.  apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. apply BoxImpL in X0.
          pose (dlCons x3 DersNilF). pose (dlCons x0 d0).
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(XBoxed_list (x2 ++ x4 ++ x5) ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A :: Γ1, B)])
          ((Γ2 ++ Imp (Box A0) B0 :: x) ++ A :: Γ1, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
          lia. reflexivity. }
    + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p. subst. apply univ_gen_ext_splitR in u.
      destruct u. destruct s. repeat destruct p ; subst.
      assert (J4: ImpRRule [(Γ0 ++ A :: x ++ B0 :: Γ3, B)] ((Γ0 ++ x) ++ B0 :: Γ3, Imp A B)).
      repeat rewrite <- app_assoc. apply ImpRRule_I.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J5 _ _ J6). pose (s _ J4). destruct s0. clear s. destruct (dec_is_boxedT A).
      { assert (BoxImpLRule [(XBoxed_list (x4 ++ A :: x5 ++ x3) ++ [Box A0], A0); (Γ0 ++ A :: x ++ B0 :: Γ3, B)]
        (Γ0 ++ A :: x ++ Imp (Box A0) B0 :: Γ3, B)).
        assert (Γ0 ++ A :: x ++ B0 :: Γ3 = (Γ0 ++ A :: x) ++ B0 :: Γ3). repeat rewrite <- app_assoc. auto.
        rewrite H. assert (Γ0 ++ A :: x ++ Imp (Box A0) B0 :: Γ3 = (Γ0 ++ A :: x) ++ Imp (Box A0) B0 :: Γ3). repeat rewrite <- app_assoc. auto.
        rewrite H0. apply BoxImpLRule_I ; auto. clear H. clear H0.
        intro. intros. apply in_app_or in H. destruct H. apply H1. apply in_or_app ; left. apply in_or_app ; auto.
        inversion H. subst ; auto. apply in_app_or in H0. destruct H0.
        apply H1. apply in_or_app ; left ; apply in_or_app;  auto.
        apply H1 ; apply in_or_app ; auto. repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_combine ; auto.
        apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto. apply BoxImpL in X0.
        assert (J1: derrec_height x0 = derrec_height x0). auto.
        assert (J2: wkn_L A (XBoxed_list ((x4 ++ x5) ++ x3) ++ [Box A0], A0) ((XBoxed_list x4) ++ A :: (XBoxed_list (x5 ++ x3)) ++ [Box A0], A0)).
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
        pose (@GL4ip_wkn_L (derrec_height x0) _ x0 J1 _ A J2). destruct s.
        assert (J3: derrec_height x6 = derrec_height x6). auto.
        assert (J31: wkn_L (unBox_formula A)  (XBoxed_list x4 ++ A :: XBoxed_list (x5 ++ x3) ++ [Box A0], A0)
        (XBoxed_list (x4 ++ A :: x5 ++ x3) ++ [Box A0], A0)).
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
        pose (@GL4ip_wkn_L (derrec_height x6) _ x6 J3 _ (unBox_formula A) J31). destruct s.
        pose (dlCons x2 DersNilF). pose (dlCons x7 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(XBoxed_list (x4 ++ A :: x5 ++ x3) ++ [Box A0], A0); (Γ0 ++ A :: x ++ B0 :: Γ3, B)])
        (Γ0 ++ A :: x ++ Imp (Box A0) B0 :: Γ3, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { assert (BoxImpLRule [(XBoxed_list ((x4 ++ x5) ++ x3) ++ [Box A0], A0); (Γ0 ++ A :: x ++ B0 :: Γ3, B)]
        (Γ0 ++ A :: x ++ Imp (Box A0) B0 :: Γ3, B)).
        assert (Γ0 ++ A :: x ++ B0 :: Γ3 = (Γ0 ++ A :: x) ++ B0 :: Γ3). repeat rewrite <- app_assoc ; auto.
        rewrite H. assert (Γ0 ++ A :: x ++ Imp (Box A0) B0 :: Γ3 = (Γ0 ++ A :: x) ++ Imp (Box A0) B0 :: Γ3). repeat rewrite <- app_assoc ; auto.
        rewrite H0. apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc.
        apply univ_gen_ext_combine ; auto. simpl. apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. apply BoxImpL in X0.
        pose (dlCons x2 DersNilF). pose (dlCons x0 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(XBoxed_list ((x4 ++ x5) ++ x3) ++ [Box A0], A0); (Γ0 ++ A :: x ++ B0 :: Γ3, B)])
        (Γ0 ++ A :: x ++ Imp (Box A0) B0 :: Γ3, B) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
  (* GLR *)
  * inversion X.
Qed.


Theorem ImpR_inv : forall concl prem, (derrec GL4ip_rules (fun _ => False) concl) ->
                                      (ImpRRule [prem] concl) ->
                                      (derrec GL4ip_rules (fun _ => False) prem).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (ImpR_hpinv _  _ X J1). pose (s _ H). destruct s0. assumption.
Qed.
