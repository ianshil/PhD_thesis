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

Theorem AndImpL_hpinv : forall (k : nat) concl
        (D0 : derrec GL4ip_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((AndImpLRule [prem] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem),
          (derrec_height D1 <= k)))).
Proof.
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
   (D0 : derrec GL4ip_rules (fun _ => False) concl),
        x = (derrec_height D0) ->
          ((forall prem, ((AndImpLRule [prem] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem),
          (derrec_height D1 <= x)))))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. intros prem RA. inversion RA. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ (A ∧ B) → C :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++ A → B → C :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x ++ # P :: x0, # P)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ (A ∧ B) → C :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ A → B → C :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion 0. subst. inversion H1. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, D)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, D) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: AndImpLRule [(Γ0 ++ A → B → C :: Γ1, B0)] (Γ0 ++ (A ∧ B) → C :: Γ1, B0)). apply AndImpLRule_I. simpl in IH.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J2 _ _ J3 _ J1). destruct s.
    assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: Γ1, A0)] (Γ0 ++ (A ∧ B) → C :: Γ1, A0)). apply AndImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ J4). destruct s.
    assert (AndRRule [(Γ0 ++ A → B → C :: Γ1, A0); (Γ0 ++ A → B → C :: Γ1, B0)]
   (Γ0 ++ A → B → C :: Γ1, And A0 B0)). apply AndRRule_I. pose (dlCons x1 DersNilF). pose (dlCons x2 d0).
    apply AndR in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A → B → C :: Γ1, A0); (Γ0 ++ A → B → C :: Γ1, B0)])
    (Γ0 ++ A → B → C :: Γ1, And A0 B0) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndLRule [((Γ0 ++ A → B → C :: x0) ++ A0 :: B0 :: Γ3, D)]
       ((Γ0 ++ A → B → C :: x0) ++ And A0 B0 :: Γ3, D)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ A0 :: B0 :: Γ3, D)]
       (Γ0 ++ (A ∧ B) → C :: x0 ++ A0 :: B0 :: Γ3, D)). apply AndImpLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s ((Γ0 ++ A → B → C :: x0) ++ A0 :: B0 :: Γ3, D)).
       assert (AndImpLRule [((Γ0 ++ A → B → C :: x0) ++ A0 :: B0 :: Γ3, D)] (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ A0 :: B0 :: Γ3, D)).
       repeat rewrite <- app_assoc. apply AndImpLRule_I. apply s0 in H1. destruct H1.
       pose (dlCons x1 DersNilF). apply AndL in H0.
       assert (Γ0 ++ A → B → C :: x0 ++ A0 :: B0 :: Γ3 =(Γ0 ++ A → B → C :: x0) ++ A0 :: B0 :: Γ3).
       repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ0 ++ A → B → C :: x0) ++ A0 :: B0 :: Γ3, D)])
       (Γ0 ++ A → B → C :: x0 ++ And A0 B0 :: Γ3, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
  +  repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J4: AndImpLRule [((Γ2 ++ A0 :: B0 :: x) ++ A → B → C :: Γ1, D)]
      ((Γ2 ++ A0 :: B0 :: x) ++ (A ∧ B) → C :: Γ1, D)). apply AndImpLRule_I.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (AndLRule [(Γ2 ++ A0 :: B0 :: x ++ A → B → C :: Γ1, D)]
      (Γ2 ++ And A0 B0 :: x ++ A → B → C :: Γ1, D)). apply AndLRule_I.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply AndL in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: B0 :: x ++ A → B → C :: Γ1, D)])
      (Γ2 ++ And A0 B0 :: x ++ A → B → C :: Γ1, D) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: Γ1, A0)] (Γ0 ++ (A ∧ B) → C :: Γ1, A0)). apply AndImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ J4). destruct s.
    assert (OrR1Rule [(Γ0 ++ A → B → C :: Γ1, A0)]
    (Γ0 ++ A → B → C :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons x0 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A → B → C :: Γ1, A0)])
    (Γ0 ++ A → B → C :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: Γ1, B0)] (Γ0 ++ (A ∧ B) → C :: Γ1, B0)). apply AndImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ J4). destruct s.
    assert (OrR2Rule [(Γ0 ++ A → B → C :: Γ1, B0)]
    (Γ0 ++ A → B → C :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons x0 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A → B → C :: Γ1, B0)])
    (Γ0 ++ A → B → C :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (OrLRule [((Γ0 ++ A → B → C :: x0) ++ A0 :: Γ3, D);((Γ0 ++ A → B → C :: x0) ++ B0 :: Γ3, D)]
      ((Γ0 ++ A → B → C :: x0) ++ Or A0 B0 :: Γ3, D)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ A0 :: Γ3, D)]
      (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ A0 :: Γ3, D)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
      assert (J5: derrec_height x < S (dersrec_height d)). lia.
      assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (J7: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ B0 :: Γ3, D)]
      (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ B0 :: Γ3, D)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ A → B → C :: x0 ++ A0 :: Γ3, D); (Γ0 ++ A → B → C :: x0 ++ B0 :: Γ3, D)])
      (Γ0 ++ A → B → C :: x0 ++ Or A0 B0 :: Γ3, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (OrLRule [(Γ2 ++ A0 :: x ++ A → B → C :: Γ1, D);(Γ2 ++ B0 :: x ++ A → B → C :: Γ1, D)]
      (Γ2 ++ Or A0 B0 :: x ++ A → B → C :: Γ1, D)). apply OrLRule_I. apply OrL in H0.
      assert (J4: AndImpLRule [((Γ2 ++ A0 :: x) ++ A → B → C :: Γ1, D)]
      ((Γ2 ++ A0 :: x) ++ (A ∧ B) → C :: Γ1, D)). apply AndImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (J7: AndImpLRule [((Γ2 ++ B0 :: x) ++ A → B → C :: Γ1, D)]
      ((Γ2 ++ B0 :: x) ++ (A ∧ B) → C :: Γ1, D)). apply AndImpLRule_I.
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x ++ A → B → C :: Γ1, D); (Γ2 ++ B0 :: x ++ A → B → C :: Γ1, D)])
      (Γ2 ++ Or A0 B0 :: x ++ A → B → C :: Γ1, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (ImpRRule [(Γ2 ++ A0 :: A → B → C :: Γ1, B0)] (Γ2 ++ A → B → C :: Γ1, Imp A0 B0)). apply ImpRRule_I.
      assert (J4: AndImpLRule [((Γ2 ++ [A0]) ++ A → B → C :: Γ1, B0)] ((Γ2 ++ [A0]) ++ (A ∧ B) → C :: Γ1, B0)). apply AndImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply ImpR in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: A → B → C :: Γ1, B0)])
      (Γ2 ++ A → B → C :: Γ1, Imp A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (ImpRRule [(Γ2 ++ A0 :: x ++ A → B → C :: Γ1, B0)] (Γ2 ++ x ++ A → B → C :: Γ1, Imp A0 B0)). apply ImpRRule_I.
      assert (J4: AndImpLRule [((Γ2 ++ A0 :: x) ++ A → B → C :: Γ1, B0)] ((Γ2 ++ A0 :: x) ++ (A ∧ B) → C :: Γ1, B0)). apply AndImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply ImpR in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x ++ A → B → C :: Γ1, B0)])
      (Γ2 ++ x ++ A → B → C :: Γ1, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
    + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (ImpRRule [ (Γ0 ++ A0 :: A → B → C :: Γ1, B0)]  (Γ0 ++ A → B → C :: Γ1, Imp A0 B0)). apply ImpRRule_I.
        assert (J4: AndImpLRule [((Γ0 ++ [A0]) ++ A → B → C :: Γ1, B0)] ((Γ0 ++ [A0]) ++ (A ∧ B) → C :: Γ1, B0)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s (Γ0 ++ A0 :: A → B → C :: Γ1, B0)).
        assert (AndImpLRule [(Γ0 ++ A0 :: A → B → C :: Γ1, B0)] ((Γ0 ++ []) ++ A0 :: (A ∧ B) → C :: Γ1, B0)). repeat rewrite <- app_assoc. simpl ; auto.
        apply s in H1. destruct H1.
        pose (dlCons x0 DersNilF). apply ImpR in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A0 :: A → B → C :: Γ1, B0)])
        (Γ0 ++ A → B → C :: Γ1, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
        assert (ImpRRule [((Γ0 ++ A → B → C :: x) ++ A0 :: Γ3, B0)]  ((Γ0 ++ A → B → C :: x) ++ Γ3, Imp A0 B0)). apply ImpRRule_I.
        assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x ++ A0 :: Γ3, B0)] (Γ0 ++ (A ∧ B) → C :: x ++ A0 :: Γ3, B0)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s ((Γ0 ++ A → B → C :: x) ++ A0 :: Γ3, B0)).
        assert (AndImpLRule [((Γ0 ++ A → B → C :: x) ++ A0 :: Γ3, B0)] ((Γ0 ++ (A ∧ B) → C :: x) ++ A0 :: Γ3, B0)). repeat rewrite <- app_assoc. simpl ; auto.
        apply s0 in H1. destruct H1.
        pose (dlCons x1 DersNilF). assert ((Γ0 ++ A → B → C :: x) ++ Γ3 = Γ0 ++ A → B → C :: x ++ Γ3). repeat rewrite <- app_assoc.
        auto. rewrite H1 in H0. apply ImpR in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[((Γ0 ++ A → B → C :: x) ++ A0 :: Γ3, B0)])
        (Γ0 ++ A → B → C :: x ++ Γ3, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
  (* AtomImpL1 *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL1Rule [((Γ0 ++ A → B → C :: x0) ++ # P :: Γ3 ++ A0 :: Γ4, D)]
       ((Γ0 ++ A → B → C :: x0) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, D)). apply AtomImpL1Rule_I.
       assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ # P :: Γ3 ++ A0 :: Γ4, D)] (Γ0 ++ (A ∧ B) → C :: x0 ++ # P :: Γ3 ++ A0 :: Γ4, D)). apply AndImpLRule_I.
       repeat rewrite <- app_assoc in J4. simpl in J4.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s ((Γ0 ++ A → B → C :: x0) ++ # P :: Γ3 ++ A0 :: Γ4, D)).
       assert (AndImpLRule [((Γ0 ++ A → B → C :: x0) ++ # P :: Γ3 ++ A0 :: Γ4, D)] (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ # P :: Γ3 ++ A0 :: Γ4, D)).
       repeat rewrite <- app_assoc. simpl ; auto. apply s0 in H1. destruct H1.
       pose (dlCons x1 DersNilF). apply AtomImpL1 in H0.
       assert (((Γ0 ++ A → B → C :: x0) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, D) = (Γ0 ++ A → B → C :: x0 ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, D)).
       repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ0 ++ A → B → C :: x0) ++ # P :: Γ3 ++ A0 :: Γ4, D)])
       (Γ0 ++ A → B → C :: x0 ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
      { inversion e0. }
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL1Rule [(Γ2 ++ # P :: (x ++ A → B → C :: x1) ++ A0 :: Γ4, D)]
        (Γ2 ++ # P :: (x ++ A → B → C :: x1) ++ Imp # P A0 :: Γ4, D)). apply AtomImpL1Rule_I.
        assert (J4: AndImpLRule [((Γ2 ++ # P :: x) ++ A → B → C :: x1 ++ A0 :: Γ4, D)] ((Γ2 ++ # P :: x) ++ (A ∧ B) → C :: x1 ++ A0 :: Γ4, D)).
        apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s (Γ2 ++ # P :: x ++ A → B → C :: x1 ++ A0 :: Γ4, D)).
        assert (AndImpLRule [(Γ2 ++ # P :: x ++ A → B → C :: x1 ++ A0 :: Γ4, D)] (Γ2 ++ # P :: ((x ++ [(A ∧ B) → C]) ++ x1) ++ A0 :: Γ4, D)).
        repeat rewrite <- app_assoc. simpl. auto. apply s0 in H1. destruct H1. clear s0. clear s.
        pose (dlCons x2 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: x ++ A → B → C :: x1 ++ A0 :: Γ4, D)])
        (Γ2 ++ # P :: x ++ A → B → C :: x1 ++ Imp # P A0 :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { repeat destruct s ; repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A0 :: x0 ++ A → B → C :: Γ1, D)]
        (Γ2 ++ # P :: Γ3 ++ Imp # P A0 :: x0 ++ A → B → C :: Γ1, D)). apply AtomImpL1Rule_I.
        assert (J4: AndImpLRule [((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ A → B → C :: Γ1, D)] ((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ (A ∧ B) → C :: Γ1, D)).
        apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: x0 ++ A → B → C :: Γ1, D)])
        (Γ2 ++ # P :: Γ3 ++ Imp (# P) A0 :: x0 ++ A → B → C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
  (* AtomImpL2 *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL2Rule [((Γ0 ++ A → B → C :: x0) ++ A0 :: Γ3 ++ # P :: Γ4, D)]
       ((Γ0 ++ A → B → C :: x0) ++Imp # P A0  :: Γ3 ++ # P :: Γ4, D)). apply AtomImpL2Rule_I.
       assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ A0 :: Γ3 ++ # P :: Γ4, D)] (Γ0 ++ (A ∧ B) → C :: x0 ++ A0 :: Γ3 ++ # P :: Γ4, D)). apply AndImpLRule_I.
       repeat rewrite <- app_assoc in J4. simpl in J4.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s ((Γ0 ++ A → B → C :: x0) ++ A0 :: Γ3 ++ # P :: Γ4, D)).
       assert (AndImpLRule [((Γ0 ++ A → B → C :: x0) ++ A0 :: Γ3 ++ # P :: Γ4, D)] (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ A0 :: Γ3 ++ # P :: Γ4, D)).
       repeat rewrite <- app_assoc. simpl ; auto. apply s0 in H1. destruct H1.
       pose (dlCons x1 DersNilF). apply AtomImpL2 in H0.
       assert (((Γ0 ++ A → B → C :: x0) ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, D) = (Γ0 ++ A → B → C :: x0 ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, D)).
       repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ0 ++ A → B → C :: x0) ++ A0 :: Γ3 ++ # P :: Γ4, D)])
       (Γ0 ++ A → B → C :: x0 ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
      { inversion e0. }
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL2Rule [(Γ2 ++ A0 :: (x ++ A → B → C :: x1) ++ # P :: Γ4, D)]
        (Γ2 ++ Imp # P A0 :: (x ++ A → B → C :: x1) ++ # P :: Γ4, D)). apply AtomImpL2Rule_I.
        assert (J4: AndImpLRule [((Γ2 ++ A0 :: x) ++ A → B → C :: x1 ++ # P :: Γ4, D)] ((Γ2 ++ A0 :: x) ++ (A ∧ B) → C :: x1 ++ # P :: Γ4, D)).
        apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s (Γ2 ++ A0 :: x ++ A → B → C :: x1 ++ # P :: Γ4, D)).
        assert (AndImpLRule [(Γ2 ++ A0 :: x ++ A → B → C :: x1 ++ # P :: Γ4, D)] (Γ2 ++ A0 :: ((x ++ [(A ∧ B) → C]) ++ x1) ++ # P :: Γ4, D)).
        repeat rewrite <- app_assoc. simpl. auto. apply s0 in H1. destruct H1. clear s0. clear s.
        pose (dlCons x2 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: x ++ A → B → C :: x1 ++ # P :: Γ4, D)])
        (Γ2 ++ Imp # P A0 :: x ++ A → B → C :: x1 ++ # P :: Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL2Rule [(Γ2 ++ A0 :: Γ3 ++ # P :: x0 ++ A → B → C :: Γ1, D)]
        (Γ2 ++ Imp # P A0 :: Γ3 ++ # P :: x0 ++ A → B → C :: Γ1, D)). apply AtomImpL2Rule_I.
        assert (J4: AndImpLRule [((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ A → B → C :: Γ1, D)] ((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ (A ∧ B) → C :: Γ1, D)).
        apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: x0 ++ A → B → C :: Γ1, D)])
        (Γ2 ++ Imp (# P) A0 :: Γ3 ++ # P :: x0 ++ A → B → C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
 (* AndImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0 ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. exists x ; auto. simpl. lia.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (AndImpLRule [((Γ0 ++ A → B → C :: x0) ++ A0 → B0 → C0 :: Γ3, D)]
    ((Γ0 ++ A → B → C :: x0) ++ (A0 ∧ B0) → C0 :: Γ3, D)). apply AndImpLRule_I. repeat rewrite <- app_assoc in H0.
     assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ Imp (And A0 B0) C0 :: Γ3, D)] (Γ0 ++ (A ∧ B) → C :: x0 ++ Imp (And A0 B0) C0 :: Γ3, D)). apply AndImpLRule_I.
     repeat rewrite <- app_assoc in J4. simpl in J4.
     assert (J5: derrec_height x < S (dersrec_height d)). lia.
     assert (J6: derrec_height x = derrec_height x). reflexivity.
     pose (IH _ J5 _ _ J6). pose (s ((Γ0 ++ A → B → C :: x0) ++ Imp A0 (Imp B0 C0) :: Γ3, D)).
     assert (AndImpLRule [((Γ0 ++ A → B → C :: x0) ++ Imp A0 (Imp B0 C0) :: Γ3, D)] (((Γ0 ++ [(A ∧ B) → C]) ++ x0)++ Imp A0 (Imp B0 C0) :: Γ3, D)).
     repeat rewrite <- app_assoc. apply AndImpLRule_I. apply s0 in H1. destruct H1.
     pose (dlCons x1 DersNilF). apply AndImpL in H0.
     assert (Γ0 ++ (A → B → C :: x0) ++ Imp A0 (Imp B0 C0) :: Γ3 =(Γ0 ++ A → B → C :: x0) ++ Imp A0 (Imp B0 C0) :: Γ3).
     repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
     pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[((Γ0 ++ A → B → C :: x0) ++ Imp A0 (Imp B0 C0) :: Γ3, D)])
     (Γ0 ++ A → B → C :: x0 ++ Imp (And A0 B0) C0 :: Γ3, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndImpLRule [((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ A → B → C :: Γ1, D)]
      ((Γ2 ++ Imp (And A0 B0) C0 :: x) ++ A → B → C :: Γ1, D)). repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. apply AndImpLRule_I.
      assert (J4: AndImpLRule [((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ A → B → C :: Γ1, D)] ((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ (A ∧ B) → C :: Γ1, D)).
      apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply AndImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ Imp A0 (Imp B0 C0) :: x ++ A → B → C :: Γ1, D)])
     (Γ2 ++ Imp (And A0 B0) C0 :: x ++ A → B → C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule [((Γ0 ++ A → B → C :: x0) ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)]
       ((Γ0 ++ A → B → C :: x0) ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, D)). apply OrImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)]
       (Γ0 ++ (A ∧ B) → C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)). apply AndImpLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6). pose (s (Γ0 ++ A → B → C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)).
       assert (AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)]
      (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)).
       repeat rewrite <- app_assoc. simpl ; auto. apply s0 in H1. destruct H1.
       pose (dlCons x1 DersNilF). apply OrImpL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A → B → C :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, D)])
       (Γ0 ++ A → B → C :: x0 ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
        rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl. repeat rewrite <- app_assoc. simpl.
        repeat rewrite <- app_assoc.
        assert (OrImpLRule [(Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: A → B → C :: Γ1, D)]
        (Γ2 ++ Imp (Or A0 B0) C0 :: Γ3 ++ A → B → C :: Γ1, D)). apply OrImpLRule_I.
        assert (J4: AndImpLRule [((Γ2 ++ Imp A0 C0 :: Γ3 ++ [Imp B0 C0]) ++ A → B → C :: Γ1, D)]
        ((Γ2 ++ Imp A0 C0 :: Γ3 ++ [Imp B0 C0]) ++ (A ∧ B) → C :: Γ1, D)).
        apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply OrImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: A → B → C :: Γ1, D)])
        (Γ2 ++ Imp (Or A0 B0) C0 :: Γ3 ++ A → B → C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1.
        simpl. rewrite dersrec_height_nil. lia. reflexivity. }
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (OrImpLRule [((Γ2 ++ Imp A0 C0 :: Γ3) ++ Imp B0 C0 :: x0 ++ A → B → C :: Γ1, D)]
        ((Γ2 ++ Imp (Or A0 B0) C0 :: Γ3) ++ x0 ++ A → B → C :: Γ1, D)). repeat rewrite <- app_assoc.
        simpl. apply OrImpLRule_I. simpl. repeat rewrite <- app_assoc. simpl.
        assert (J4: AndImpLRule [((Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: x0) ++ A → B → C :: Γ1, D)]
        ((Γ2 ++ Imp A0 C0 :: Γ3  ++ Imp B0 C0 :: x0) ++ (A ∧ B) → C :: Γ1, D)).
        apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply OrImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        repeat rewrite <- app_assoc in H0. simpl in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: x0 ++ A → B → C :: Γ1, D)])
        (Γ2 ++ Imp (Or A0 B0) C0 :: Γ3 ++ x0 ++ A → B → C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
        rewrite dersrec_height_nil. lia. reflexivity. }
      { destruct x0.
         - simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
           pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl. repeat rewrite <- app_assoc. simpl.
           assert (OrImpLRule [(Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A → B → C :: Γ1, D)]
           (Γ2 ++ Imp (Or A0 B0) C0 :: x ++ A → B → C :: Γ1, D)). apply OrImpLRule_I.
           assert (J4: AndImpLRule [((Γ2 ++ Imp A0 C0 :: x ++ [Imp B0 C0]) ++ A → B → C :: Γ1, D)]
           ((Γ2 ++ Imp A0 C0 :: x ++ [Imp B0 C0]) ++ (A ∧ B) → C :: Γ1, D)).
           apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
           assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
           assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
           pose (IH _ J5 _ _ J6). pose (s (Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A → B → C :: Γ1, D)).
           assert (AndImpLRule [(Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A → B → C :: Γ1, D)]
           (Γ2 ++ Imp A0 C0 :: (x ++ []) ++ Imp B0 C0 :: (A ∧ B) → C :: Γ1, D)). repeat rewrite <- app_assoc. simpl. auto.
           apply s0 in H1. destruct H1. clear s0. clear s.
           pose (dlCons x1 DersNilF). apply OrImpL in H0.
           pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
           (ps:=[(Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A → B → C :: Γ1, D)])
          (Γ2 ++ Imp (Or A0 B0) C0 :: x ++ A → B → C :: Γ1, D) H0 d0). repeat rewrite <- app_assoc. exists d1.
           simpl. rewrite dersrec_height_nil. lia. reflexivity.
      -  inversion e0. subst. simpl. repeat rewrite <- app_assoc. simpl.
          assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. clear e0.
          assert (OrImpLRule [(Γ2 ++ Imp A0 C0 :: (x ++ A → B → C :: x0) ++ Imp B0 C0 :: Γ4, D)]
          (Γ2 ++ Imp (Or A0 B0) C0 :: (x ++ A → B → C :: x0) ++ Γ4, D)). apply OrImpLRule_I.
          assert (J4: AndImpLRule [((Γ2 ++ Imp A0 C0 :: x) ++ A → B → C :: x0 ++ Imp B0 C0 :: Γ4, D)]
          ((Γ2 ++ Imp A0 C0 :: x) ++ (A ∧ B) → C :: x0 ++ Imp B0 C0 :: Γ4, D)).
          apply AndImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
          assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
          assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
          pose (IH _ J5 _ _ J6). pose (s (Γ2 ++ Imp A0 C0 :: x ++ A → B → C :: x0 ++ Imp B0 C0 :: Γ4, D)).
          assert (AndImpLRule [(Γ2 ++ Imp A0 C0 :: x ++ A → B → C :: x0 ++ Imp B0 C0 :: Γ4, D)]
          (Γ2 ++ Imp A0 C0 :: (x ++ (A ∧ B) → C :: x0) ++ Imp B0 C0 :: Γ4, D)).
          repeat rewrite <- app_assoc. simpl. auto. apply s0 in H1. destruct H1. clear s0. clear s.
          pose (dlCons x2 DersNilF). apply OrImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ2 ++ Imp A0 C0 :: x ++ A → B → C :: x0 ++ Imp B0 C0 :: Γ4, D)])
          (Γ2 ++ Imp (Or A0 B0) C0 :: x ++ A → B → C :: x0 ++ Γ4, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
          rewrite dersrec_height_nil. lia. reflexivity. }
  (* ImpImpL *)
 * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
        assert (ImpImpLRule [((Γ0 ++ A → B → C :: x0) ++ Imp B0 C0 :: Γ3, Imp A0 B0); ((Γ0 ++ A → B → C :: x0) ++ C0 :: Γ3, D)]
        ((Γ0 ++ A → B → C :: x0) ++ Imp (Imp A0 B0) C0 :: Γ3, D)). apply ImpImpLRule_I. apply ImpImpL in H0.
        repeat rewrite <- app_assoc in H0. simpl in H0.
        assert (J4: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ Imp B0 C0 :: Γ3, Imp A0 B0)]
        (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ Imp B0 C0 :: Γ3, Imp A0 B0)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        assert (J7: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ C0 :: Γ3, D)]
        (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ C0 :: Γ3, D)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
        assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J8 _ _ J9 _ J7). destruct s.
        pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A → B → C :: x0 ++ Imp B0 C0 :: Γ3, Imp A0 B0); (Γ0 ++ A → B → C :: x0 ++ C0 :: Γ3, D)])
       (Γ0 ++ A → B → C :: x0 ++ Imp (Imp A0 B0) C0 :: Γ3, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (ImpImpLRule [(Γ2 ++ Imp B0 C0 :: x ++ A → B → C :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x ++ A → B → C :: Γ1, D)]
      (Γ2 ++ Imp (Imp A0 B0) C0 :: x ++ A → B → C :: Γ1, D)). apply ImpImpLRule_I. apply ImpImpL in H0.
      assert (J4: AndImpLRule [((Γ2 ++ Imp B0 C0 :: x) ++ A → B → C :: Γ1, Imp A0 B0)]
      ((Γ2 ++ Imp B0 C0 :: x) ++ (A ∧ B) → C :: Γ1, Imp A0 B0)). apply AndImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (J7: AndImpLRule [((Γ2 ++ C0 :: x) ++ A → B → C :: Γ1, D)]
      ((Γ2 ++ C0 :: x) ++ (A ∧ B) → C :: Γ1, D)). apply AndImpLRule_I.
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ Imp B0 C0 :: x ++ A → B → C :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x ++ A → B → C :: Γ1, D)])
      (Γ2 ++ Imp (Imp A0 B0) C0 :: x ++ A → B → C :: Γ1, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* BoxImpL *)
 * inversion X. subst. apply list_split_form in H. destruct H. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in X0. simpl in X0.
      apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p.
      subst. inversion u0. subst. exfalso.
      apply is_box_is_in_boxed_list with (A:=(A ∧ B) → C) in H1. destruct H1.
      inversion H. apply in_or_app. right. apply in_eq. subst.
      assert (J50: AndImpLRule [(Γ0 ++ A → B → C :: x0 ++ B0 :: Γ3, D)]
      (((Γ0 ++ [(A ∧ B) → C]) ++ x0) ++ B0 :: Γ3, D)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
      assert (J51: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J52: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J51 _ _ J52 _ J50). destruct s.
      assert (BoxImpLRule [(XBoxed_list (x2 ++ x3)  ++ [Box A0], A0); ((Γ0 ++ A → B → C :: x0) ++ B0 :: Γ3, D)]
      ((Γ0 ++  A → B → C :: x0) ++ Imp (Box A0) B0 :: Γ3, D)). apply BoxImpLRule_I ; auto.
      repeat rewrite <- app_assoc. simpl.
      apply univ_gen_ext_combine ; auto. simpl. apply univ_gen_ext_extra ; auto. intro. destruct X1.
      inversion H. apply BoxImpL in X1.
      pose (dlCons x4 DersNilF). pose (dlCons x d0). repeat rewrite <- app_assoc in X1.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(XBoxed_list (x2 ++ x3) ++ [Box A0], A0); (Γ0 ++ A → B → C :: x0 ++ B0 :: Γ3, D)])
      (Γ0 ++ A → B → C :: x0 ++ Imp (Box A0) B0 :: Γ3, D) X1 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p.
      subst. apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p. inversion u1. subst. exfalso.
      apply is_box_is_in_boxed_list with (A:=(A ∧ B) → C) in H1. destruct H1.
      inversion H. apply in_or_app. right. apply in_or_app. right. apply in_eq. subst.
      assert (J50: AndImpLRule [((Γ2 ++ B0 :: x) ++ A → B → C :: Γ1, D)]
      ((Γ2 ++ B0 :: x) ++ (A ∧ B) → C :: Γ1, D)). apply AndImpLRule_I. repeat rewrite <- app_assoc in J50. simpl in J50.
      assert (J51: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J52: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J51 _ _ J52 _ J50). destruct s.
      assert (BoxImpLRule [(XBoxed_list (x2 ++ x4 ++ x5)  ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A → B → C :: Γ1, D)]
      (Γ2 ++ Imp (Box A0) B0 :: x ++ A → B → C :: Γ1, D)). apply BoxImpLRule_I ; auto.
      apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto.
      intro. destruct X1. inversion H. apply BoxImpL in X1.
      pose (dlCons x3 DersNilF). pose (dlCons x0 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(XBoxed_list (x2 ++ x4 ++ x5) ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A → B → C :: Γ1, D)])
      (Γ2 ++ Imp (Box A0) B0 :: x ++ A → B → C :: Γ1, D) X1 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* GLR *)
  * inversion X. subst. simpl.
    assert (GLRRule [(XBoxed_list BΓ ++ [Box A0], A0)] (Γ0 ++ A → B → C :: Γ1, Box A0)). apply GLRRule_I ; auto.
    apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst. inversion u0. exfalso.
    subst. assert (In ((A ∧ B) → C) (x ++ (A ∧ B) → C :: l)). apply in_or_app. right. apply in_eq. pose (H1 ((A ∧ B) → C) H).
    destruct e. inversion H0. apply univ_gen_ext_combine ; auto. simpl in IH. subst. apply univ_gen_ext_extra ; auto.
    intro. destruct X1. inversion H. apply GLR in X1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(XBoxed_list BΓ ++ [Box A0], A0)]) (Γ0 ++ A → B → C :: Γ1, Box A0) X1 d). exists d0. simpl. auto.
Qed.

Theorem AndImpL_inv : forall concl prem, (derrec GL4ip_rules (fun _ => False) concl) ->
                                      (AndImpLRule [prem] concl) ->
                                      (derrec GL4ip_rules (fun _ => False) prem).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (AndImpL_hpinv _  _ X J1). pose (s _ H). destruct s0. auto.
Qed.
