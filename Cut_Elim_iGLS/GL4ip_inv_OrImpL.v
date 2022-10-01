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

Theorem OrImpL_hpinv : forall (k : nat) concl
        (D0 : derrec GL4ip_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((OrImpLRule [prem] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem),
          (derrec_height D1 <= k)))).
Proof.
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec GL4ip_rules (fun _ => False) concl),
        x = (derrec_height D0) ->
          ((forall prem, ((OrImpLRule [prem] concl) ->
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
  * inversion H. subst. assert (InT # P (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. subst.
    apply InT_split in H1. destruct H1. destruct s. assert (InT # P (Γ1 ++ Γ2)). rewrite e.
    apply InT_or_app. right. apply InT_eq. apply InT_app_or in H0. destruct H0 ; apply InT_or_app;  auto.
    right. apply InT_cons ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (IdPRule [] (x ++ # P :: x0, # P)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. apply InT_app_or in H1. destruct H1.
    apply InT_or_app ; auto. apply InT_or_app ; right ; apply InT_cons ; auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, D)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, D) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: OrImpLRule [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, B0)] (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, B0)). apply OrImpLRule_I. simpl in IH.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J2 _ _ J3 _ J1). destruct s.
    assert (J4: OrImpLRule [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, A0)] (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, A0)). apply OrImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ J4). destruct s.
    assert (AndRRule [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, A0); (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 , B0)]
   (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, And A0 B0)). apply AndRRule_I. pose (dlCons x1 DersNilF). pose (dlCons x2 d0).
    apply AndR in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, A0); (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, B0)])
    (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, And A0 B0) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
       assert (J4: OrImpLRule [(Γ0 ++ A→ C :: [] ++ B → C ::  x0 ++ A0 :: B0 :: Γ4, D)]
       (((Γ0 ++ [(A ∨ B) → C]) ++ x0) ++ A0 :: B0 :: Γ4, D)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
       simpl in J4. 
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ J4). destruct s.
       pose (dlCons x1 DersNilF).
       assert (AndLRule [(Γ0 ++ A → C :: B → C :: x0 ++ A0 :: B0 :: Γ4, D)] (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: x0 ++ A0 :: B0 :: Γ4 = (Γ0 ++ A → C :: B → C :: x0) ++ A0 :: B0 :: Γ4).
       repeat rewrite <- app_assoc ; auto. rewrite H0.
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ A0 ∧ B0 :: Γ4).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply AndLRule_I. apply AndL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A → C :: B → C :: x0 ++ A0 :: B0 :: Γ4, D)])
       (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d0).
       assert (J50: derrec_height d1 = derrec_height d1). auto.
       assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1.
       assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H2. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d1 J50
       _ J51). destruct s. exists x2. simpl. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. lia.
  +  repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J4: OrImpLRule [((Γ3 ++ A0 :: B0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      ((Γ3 ++ A0 :: B0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)). apply OrImpLRule_I.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (AndLRule [(Γ3 ++ A0 :: B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      (Γ3 ++ And A0 B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)). apply AndLRule_I.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply AndL in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ3 ++ A0 :: B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
      (Γ3 ++ And A0 B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: OrImpLRule [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, A0)] (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, A0)). apply OrImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ J4). destruct s.
    assert (OrR1Rule [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, A0)]
    (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Or A0 B0)). apply OrR1Rule_I. pose (dlCons x0 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, A0)])
    (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: OrImpLRule [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, B0)] (Γ0 ++ (A ∨ B) → C :: Γ1 ++ Γ2, B0)). apply OrImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ J4). destruct s.
    assert (OrR2Rule [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, B0)]
    (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Or A0 B0)). apply OrR2Rule_I. pose (dlCons x0 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, B0)])
    (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (J4: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ A0 :: Γ4, D)]
      (((Γ0 ++ [(A ∨ B) → C]) ++ x0) ++ A0 :: Γ4, D)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
      simpl in J4.
      assert (J5: derrec_height x < S (dersrec_height d)). lia.
      assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (J7: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ B0 :: Γ4, D)]
      (((Γ0 ++ [(A ∨ B) → C]) ++ x0) ++ B0 :: Γ4, D)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
      simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ J7). destruct s.
      assert (OrLRule [((Γ0 ++ A → C :: B → C :: x0) ++ A0 :: Γ4, D);((Γ0 ++ A → C :: B → C :: x0) ++ B0 :: Γ4, D)]
      (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
      assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ A0 ∨ B0 :: Γ4).
      rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0.
      apply OrLRule_I. apply OrL in H0. repeat rewrite <- app_assoc in H0. simpl in H0.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ A → C :: B → C :: x0 ++ A0 :: Γ4, D); (Γ0 ++ A → C :: B → C :: x0 ++ B0 :: Γ4, D)])
      (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d1).
       assert (J50: derrec_height d2 = derrec_height d2). auto.
       assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1.
       assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H2. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d2) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d2 J50
       _ J51). destruct s. exists x4. simpl. simpl in l1. rewrite dersrec_height_nil in l1 ; auto. lia.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (OrLRule [(Γ3 ++ A0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D);(Γ3 ++ B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      (Γ3 ++ Or A0 B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)). apply OrLRule_I. apply OrL in H0.
      assert (J4: OrImpLRule [((Γ3 ++ A0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      ((Γ3 ++ A0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)). apply OrImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (J7: OrImpLRule [((Γ3 ++ B0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      ((Γ3 ++ B0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)). apply OrImpLRule_I.
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ3 ++ A0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D); (Γ3 ++ B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
      (Γ3 ++ Or A0 B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (ImpRRule [(Γ3 ++ A0 :: A → C :: Γ1 ++ B → C :: Γ2, B0)] (Γ3 ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0)). apply ImpRRule_I.
      assert (J4: OrImpLRule [((Γ3 ++ [A0]) ++ A → C :: Γ1 ++ B → C :: Γ2, B0)] ((Γ3 ++ [A0]) ++ (A ∨ B) → C :: Γ1 ++ Γ2, B0)). apply OrImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply ImpR in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ3 ++ A0 :: A → C :: Γ1 ++ B → C :: Γ2, B0)])
      (Γ3 ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (ImpRRule [(Γ3 ++ A0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, B0)] (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0)). apply ImpRRule_I.
      assert (J4: OrImpLRule [((Γ3 ++ A0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, B0)] ((Γ3 ++ A0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, B0)). apply OrImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply ImpR in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ3 ++ A0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, B0)])
      (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
    + destruct x.
      { simpl in e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (ImpRRule [(Γ0 ++ A0 :: A → C :: Γ1 ++ B → C :: Γ2, B0)]  (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0)). apply ImpRRule_I.
        assert (J4: OrImpLRule [((Γ0 ++ [A0]) ++ A → C :: Γ1 ++ B → C :: Γ2, B0)] ((Γ0 ++ [A0]) ++ (A ∨ B) → C :: Γ1 ++ Γ2, B0)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6). pose (s (Γ0 ++ A0 :: A → C :: Γ1 ++ B → C :: Γ2, B0)).
        assert (OrImpLRule [(Γ0 ++ A0 :: A → C :: Γ1 ++ B → C :: Γ2, B0)] ((Γ0 ++ []) ++ A0 :: (A ∨ B) → C :: Γ1 ++ Γ2, B0)). repeat rewrite <- app_assoc. simpl ; auto.
        apply s in H1. destruct H1.
        pose (dlCons x0 DersNilF). apply ImpR in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A0 :: A → C :: Γ1 ++ B → C :: Γ2, B0)])
        (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
        assert (J4: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x ++ A0 :: Γ4, B0)] ((Γ0 ++ (A ∨ B) → C :: [] ++ x) ++ A0 :: Γ4, B0)).
        repeat rewrite <- app_assoc. apply OrImpLRule_I. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        assert (ImpRRule [((Γ0 ++ A → C :: B → C :: x) ++ A0 :: Γ4, B0)]  (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, A0 → B0)).
        assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x) ++ Γ4). rewrite H2.
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ImpRRule_I. apply ImpR in H0.
        pose (dlCons x1 DersNilF). repeat rewrite <- app_assoc in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A → C :: B → C :: x ++ A0 :: Γ4, B0)])
        (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, A0 → B0) H0 d0).
       assert (J50: derrec_height d1 = derrec_height d1). auto.
       assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, A0 → B0) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, A0 → B0)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1.
       assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H3. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, A0 → B0) d1 J50
       _ J51). destruct s. exists x2. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. lia. }
  (* AtomImpL1 *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (J4: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ # P :: Γ4 ++ A0 :: Γ5, D)] (((Γ0 ++ [(A ∨ B) → C]) ++ [] ++ x0) ++ # P :: Γ4 ++ A0 :: Γ5, D)).
       repeat rewrite <- app_assoc. apply OrImpLRule_I. simpl in J4.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ J4).
       assert (AtomImpL1Rule [((Γ0 ++ A → C :: B → C :: x0) ++ # P :: Γ4 ++ A0 :: Γ5, D)]
       (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ # P :: Γ4 ++ # P → A0 :: Γ5).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL1Rule_I. destruct s.
       pose (dlCons x1 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A → C :: B → C :: x0 ++ # P :: Γ4 ++ A0 :: Γ5, D)])
       (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d0).
       assert (J50: derrec_height d1 = derrec_height d1). auto.
       assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1.
       assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H2. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d1 J50
       _ J51). destruct s. exists x2. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. simpl. lia.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
      { inversion e0. }
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J4: OrImpLRule [((Γ3 ++ # P :: x) ++ A → C :: [] ++ B → C :: x1 ++ A0 :: Γ5, D)] (Γ3 ++ # P :: ((x ++ [(A ∨ B) → C]) ++ x1) ++ A0 :: Γ5, D)).
        assert (Γ3 ++ # P :: ((x ++ [(A ∨ B) → C]) ++ x1) ++ A0 :: Γ5 = (Γ3 ++ # P :: x) ++ (A ∨ B) → C :: [] ++ x1 ++ A0 :: Γ5).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply OrImpLRule_I. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        assert (AtomImpL1Rule [((Γ3 ++ # P :: x) ++ A → C :: B → C :: x1 ++ A0 :: Γ5, D)]
        (Γ3 ++ # P :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
        assert (Γ3 ++ # P :: x ++ A → C :: B → C :: Γ1 ++ Γ2 = Γ3 ++ # P :: (x ++ A → C :: B → C :: x1) ++ # P → A0 :: Γ5).
        rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert ((Γ3 ++ # P :: x) ++ A → C :: B → C :: x1 ++ A0 :: Γ5 = Γ3 ++ # P :: (x ++ A → C :: B → C :: x1) ++ A0 :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply AtomImpL1Rule_I.
        pose (dlCons x2 DersNilF). apply AtomImpL1 in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[((Γ3 ++ # P :: x) ++ A → C :: B → C :: x1 ++ A0 :: Γ5, D)])
        (Γ3 ++ # P :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d0).
       assert (J50: derrec_height d1 = derrec_height d1). auto.
       assert (J51: list_exch_L (Γ3 ++ # P :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ3 ++ # P :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ3 ++ # P :: x ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ3 ++ # P :: x ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
       assert (Γ3 ++ # P :: x ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ3 ++ # P :: x ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ3 ++ # P :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D) d1 J50
       _ J51). destruct s. repeat rewrite <- app_assoc. simpl. exists x3. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. lia. }
      { repeat destruct s ; repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL1Rule [(Γ3 ++ # P :: Γ4 ++ A0 :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
        (Γ3 ++ # P :: Γ4 ++ Imp # P A0 :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)). apply AtomImpL1Rule_I.
        assert (J4: OrImpLRule [((Γ3 ++ # P :: Γ4 ++ A0 :: x0) ++ A → C :: Γ1 ++B → C ::  Γ2, D)] ((Γ3 ++ # P :: Γ4 ++ A0 :: x0) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)).
        apply OrImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ3 ++ # P :: Γ4 ++ A0 :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
        (Γ3 ++ # P :: Γ4 ++ Imp (# P) A0 :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
  (* AtomImpL2 *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (J4: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ A0 :: Γ4 ++ # P :: Γ5, D)] (((Γ0 ++ [(A ∨ B) → C]) ++ [] ++ x0) ++ A0 :: Γ4 ++ # P :: Γ5, D)).
       repeat rewrite <- app_assoc. apply OrImpLRule_I. simpl in J4.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ J4).
       assert (AtomImpL2Rule [((Γ0 ++ A → C :: B → C :: x0) ++ A0 :: Γ4 ++ # P :: Γ5, D)]
       (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ # P → A0 :: Γ4 ++ # P :: Γ5).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL2Rule_I. destruct s.
       pose (dlCons x1 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A → C :: B → C :: x0 ++ A0 :: Γ4 ++ # P :: Γ5, D)])
       (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d0).
       assert (J50: derrec_height d1 = derrec_height d1). auto.
       assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H1.
       assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; auto. rewrite H2. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d1 J50
       _ J51). destruct s. exists x2. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. simpl. lia.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
      { inversion e0. }
      { assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J4: OrImpLRule [((Γ3 ++ A0 :: x) ++ A → C :: [] ++ B → C :: x1 ++ # P :: Γ5, D)] (Γ3 ++ A0 :: ((x ++ [(A ∨ B) → C]) ++ x1) ++ # P :: Γ5, D)).
        assert (Γ3 ++ A0 :: ((x ++ [(A ∨ B) → C]) ++ x1) ++ # P :: Γ5 = (Γ3 ++ A0 :: x) ++ (A ∨ B) → C :: [] ++ x1 ++ # P :: Γ5).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply OrImpLRule_I. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        assert (AtomImpL2Rule [((Γ3 ++ A0 :: x) ++ A → C :: B → C :: x1 ++ # P :: Γ5, D)]
        (Γ3 ++ # P → A0 :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
        assert (Γ3 ++ # P → A0 :: x ++ A → C :: B → C :: Γ1 ++ Γ2 = Γ3 ++ # P → A0 :: (x ++ A → C :: B → C :: x1) ++ # P  :: Γ5).
        rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert ((Γ3 ++ A0 :: x) ++ A → C :: B → C :: x1 ++ # P :: Γ5 = Γ3 ++A0 :: (x ++ A → C :: B → C :: x1) ++ # P :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply AtomImpL2Rule_I.
        pose (dlCons x2 DersNilF). apply AtomImpL2 in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[((Γ3 ++ A0 :: x) ++ A → C :: B → C :: x1 ++ # P :: Γ5, D)])
        (Γ3 ++ # P → A0 :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d0).
       assert (J50: derrec_height d1 = derrec_height d1). auto.
       assert (J51: list_exch_L (Γ3 ++ # P → A0 :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ3 ++ # P → A0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ3 ++ # P → A0 :: x ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ3 ++ # P → A0 :: x ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
       assert (Γ3 ++ # P → A0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ3 ++ # P → A0 :: x ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ3 ++ # P → A0 :: x ++ A → C :: B → C :: Γ1 ++ Γ2, D) d1 J50
       _ J51). destruct s. repeat rewrite <- app_assoc. simpl. exists x3. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. lia. }
      { repeat destruct s ; repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AtomImpL2Rule [(Γ3 ++ A0 :: Γ4 ++ # P :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
        (Γ3 ++ # P → A0 :: Γ4 ++  # P :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)). apply AtomImpL2Rule_I.
        assert (J4: OrImpLRule [((Γ3 ++ A0 :: Γ4 ++ # P :: x0) ++ A → C :: Γ1 ++B → C ::  Γ2, D)] ((Γ3 ++ A0 :: Γ4 ++ # P :: x0) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)).
        apply OrImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ3 ++ A0 :: Γ4 ++ # P :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
        (Γ3 ++ # P → A0 :: Γ4 ++ # P :: x0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
 (* AndImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (J4: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ A0 → B0 → C0:: Γ4, D)] (((Γ0 ++ [(A ∨ B) → C]) ++ [] ++ x0) ++ A0 → B0 → C0 :: Γ4, D)).
     repeat rewrite <- app_assoc. apply OrImpLRule_I. simpl in J4.
     assert (J5: derrec_height x < S (dersrec_height d)). lia.
     assert (J6: derrec_height x = derrec_height x). reflexivity.
     pose (IH _ J5 _ _ J6 _ J4). destruct s.
     assert (AndImpLRule [((Γ0 ++ A → C :: B → C :: x0) ++ A0 → B0 → C0 :: Γ4, D)]
     (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
     assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ (A0 ∧ B0) → C0 :: Γ4).
     rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply AndImpLRule_I.
     repeat rewrite <- app_assoc in H0. simpl in H0.
     pose (dlCons x1 DersNilF). apply AndImpL in H0.
     pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ A → C :: B → C :: x0 ++ A0 → B0 → C0 :: Γ4, D)])
     (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d0).
     assert (J50: derrec_height d1 = derrec_height d1). auto.
     assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
     assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
     assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply list_exch_LI.
     pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d1 J50
     _ J51). destruct s. repeat rewrite <- app_assoc. simpl. exists x2. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. lia.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J4: OrImpLRule [((Γ3 ++ Imp A0 (Imp B0 C0) :: x) ++ A →C :: Γ1 ++ B → C :: Γ2, D)] ((Γ3 ++ A0 → B0 → C0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)).
      apply OrImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (AndImpLRule [(Γ3 ++ A0 → B0 → C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      ((Γ3 ++ (A0 ∧ B0) → C0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, D)). repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. apply AndImpLRule_I.
      pose (dlCons x1 DersNilF). apply AndImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ3 ++ A0 → B0 → C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
      (Γ3 ++ (A0 ∧ B0) → C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0 ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (J50: derrec_height x = derrec_height x). auto.
     assert (J51: list_exch_L (Γ0 ++ A → C :: Γ4 ++ B → C :: Γ5, D) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
     assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ4 ++ [] ++ Γ5).
     rewrite <- e ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
     assert (Γ0 ++ A → C :: Γ4 ++ B → C :: Γ5 = (Γ0 ++ [A → C]) ++ [] ++ Γ4 ++ [B → C] ++ Γ5).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
     pose (GL4ip_hpadm_list_exch_L (derrec_height x) (Γ0 ++ A → C :: Γ4 ++ B → C :: Γ5, D) x J50
     _ J51). destruct s.
     assert (J52: derrec_height x0 = derrec_height x0). auto.
     assert (J53: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) ).
     assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
     assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
     pose (GL4ip_hpadm_list_exch_L (derrec_height x0) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) x0 J52
     _ J53). destruct s. exists x1. lia.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (J4: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ Imp A0 C0 :: Γ4 ++ Imp B0 C0 :: Γ5, D)]
       (((Γ0 ++ [(A ∨ B) → C]) ++ [] ++ x0) ++ A0 → C0 :: Γ4 ++ B0 → C0 :: Γ5, D)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
       simpl in J4.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ J4). destruct s.
       assert (OrImpLRule [((Γ0 ++ A → C :: B → C :: x0) ++ A0 → C0 :: Γ4 ++ B0 → C0 :: Γ5, D)]
       (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ (A0 ∨ B0) → C0 :: Γ4 ++ Γ5).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0.
       apply OrImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       pose (dlCons x1 DersNilF). apply OrImpL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A → C :: B → C :: x0 ++ A0 → C0 :: Γ4 ++ B0 → C0 :: Γ5, D)])
       (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d0).
     assert (J50: derrec_height d1 = derrec_height d1). auto.
     assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
     assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
     assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply list_exch_LI.
     pose (GL4ip_hpadm_list_exch_L (derrec_height d1) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d1 J50
     _ J51). destruct s. repeat rewrite <- app_assoc. simpl. exists x2. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. lia.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (J50: derrec_height x0 = derrec_height x0). auto.
     assert (J51: list_exch_L (Γ3 ++ A0 → C0 :: Γ4 ++ B0 → C0 :: Γ5, D) (Γ3 ++ A0 → C0 :: B0 → C0 :: x ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)).
     assert (Γ3 ++ A0 → C0 :: B0 → C0 :: x ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ [A0 → C0]) ++ [B0 → C0] ++ [] ++ Γ4 ++ Γ5).
     rewrite <- e0 ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
     assert (Γ3 ++ A0 → C0 :: Γ4 ++ B0 → C0 :: Γ5 = (Γ3 ++ [A0 → C0]) ++ Γ4 ++ [] ++ [B0 → C0] ++ Γ5).
     repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
     pose (GL4ip_hpadm_list_exch_L (derrec_height x0) (Γ3 ++ A0 → C0 :: Γ4 ++ B0 → C0 :: Γ5, D) x0 J50
     _ J51). destruct s.
      assert (J4: OrImpLRule [((Γ3 ++ A0 → C0 :: B0 → C0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      ((Γ3 ++ A0 → C0 :: B0 → C0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)).
      apply OrImpLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (OrImpLRule [(Γ3 ++ A0 → C0 :: [] ++ B0 → C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      ((Γ3 ++ (A0 ∨ B0) → C0 :: [] ++ x) ++ A → C :: Γ1 ++ B → C :: Γ2, D)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
      simpl in H0. apply OrImpL in H0. pose (dlCons x2 DersNilF).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ3 ++ A0 → C0 :: B0 → C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
      ((Γ3 ++ (A0 ∨ B0) → C0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, D) H0 d0). exists d1.
      simpl. rewrite dersrec_height_nil ;auto. lia.
  (* ImpImpL *)
 * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
        assert (J4: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ B0 → C0 :: Γ4, A0 → B0)]
        (((Γ0 ++ [(A ∨ B) → C]) ++ [] ++ x0) ++ B0 → C0 :: Γ4, A0 → B0)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
        simpl in J4.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ J4). destruct s.
        assert (J7: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ C0 :: Γ4, D)]
        (((Γ0 ++ [(A ∨ B) → C]) ++ x0) ++ C0 :: Γ4, D)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
        simpl in J7.
        assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J8 _ _ J9 _ J7). destruct s.
        assert (ImpImpLRule [((Γ0 ++ A → C :: B → C :: x0) ++ B0 → C0 :: Γ4, A0 → B0); ((Γ0 ++ A → C :: B → C :: x0) ++ C0 :: Γ4, D)]
        (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
        assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ (A0 → B0) → C0 :: Γ4).
        rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        apply ImpImpLRule_I. apply ImpImpL in H0.
        repeat rewrite <- app_assoc in H0. simpl in H0.
        pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A → C :: B → C :: x0 ++ B0 → C0 :: Γ4, A0 → B0); (Γ0 ++ A → C :: B → C :: x0 ++ C0 :: Γ4, D)])
        (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) H0 d1).
       assert (J50: derrec_height d2 = derrec_height d2). auto.
       assert (J51: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
       assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d2) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d2 J50
       _ J51). destruct s. repeat rewrite <- app_assoc. simpl. exists x4. simpl in l1. rewrite dersrec_height_nil in l1 ; auto. lia.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (J4: OrImpLRule [((Γ3 ++ Imp B0 C0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0)]
      ((Γ3 ++ Imp B0 C0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, Imp A0 B0)). apply OrImpLRule_I.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ J4). destruct s.
      assert (J7: OrImpLRule [((Γ3 ++ C0 :: x) ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      ((Γ3 ++ C0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)). apply OrImpLRule_I.
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ J7). destruct s.
      assert (ImpImpLRule [(Γ3 ++ Imp B0 C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0); (Γ3 ++ C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      (Γ3 ++ Imp (Imp A0 B0) C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)). apply ImpImpLRule_I. apply ImpImpL in H0.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ3 ++ Imp B0 C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, Imp A0 B0); (Γ3 ++ C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
      (Γ3 ++ Imp (Imp A0 B0) C0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* BoxImpL *)
 * inversion X. subst. apply list_split_form in H. destruct H. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in X0. simpl in X0.
      apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p.
      subst. inversion u0. subst. exfalso.
      apply is_box_is_in_boxed_list with (A:=(A ∨ B) → C) in H1. destruct H1.
      inversion H. apply in_or_app. right. apply in_eq. subst.
      apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p. subst.
      assert (J50: OrImpLRule [(Γ0 ++ A → C :: [] ++ B → C :: x0 ++ B0 :: Γ4, D)]
      (((Γ0 ++ [(A ∨ B) → C]) ++ [] ++ x0) ++ B0 :: Γ4, D)). repeat rewrite <- app_assoc. apply OrImpLRule_I.
      simpl in J50.
      assert (J51: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J52: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J51 _ _ J52 _ J50). destruct s.
      assert (BoxImpLRule [(XBoxed_list (x2 ++ x4 ++ x5)  ++ [Box A0], A0); ((Γ0 ++ A → C :: B → C :: x0) ++ B0 :: Γ4, D)]
      (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D)).
      assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ A → C :: B → C :: x0) ++ Box A0 → B0 :: Γ4).
      rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H. apply BoxImpLRule_I ; auto.
      repeat rewrite <- app_assoc. simpl.
      apply univ_gen_ext_combine ; auto. simpl. apply univ_gen_ext_extra ; auto. intro. destruct X0.
      inversion H0. apply univ_gen_ext_extra ; auto. intro. destruct X0.
      inversion H0. apply univ_gen_ext_combine ; auto. apply BoxImpL in X0.
      pose (dlCons x3 DersNilF). pose (dlCons x d0). repeat rewrite <- app_assoc in X0. simpl in X0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(XBoxed_list (x2 ++ x4 ++ x5) ++ [Box A0], A0); (Γ0 ++ A → C :: B → C :: x0 ++ B0 :: Γ4, D)])
      (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) X0 d1).
       assert (J53: derrec_height d2 = derrec_height d2). auto.
       assert (J54: list_exch_L (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)).
       assert (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A → C]) ++ [B → C] ++ Γ1 ++ [] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
       assert (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A → C]) ++ [] ++ Γ1 ++ [B → C] ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
       pose (GL4ip_hpadm_list_exch_L (derrec_height d2) (Γ0 ++ A → C :: B → C :: Γ1 ++ Γ2, D) d2 J53
       _ J54). destruct s. repeat rewrite <- app_assoc. simpl. exists x6. simpl in l0. rewrite dersrec_height_nil in l0 ; auto. lia.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p.
      subst. apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p. subst. inversion u1. subst. exfalso.
      apply is_box_is_in_boxed_list with (A:=(A ∨ B) → C) in H1. destruct H1.
      inversion H. apply in_or_app. right. apply in_or_app. right. apply in_eq. subst.
      apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p. subst.
      assert (J50: OrImpLRule [((Γ3 ++ B0 :: x) ++ A → C :: Γ1 ++B → C ::  Γ2, D)]
      ((Γ3 ++ B0 :: x) ++ (A ∨ B) → C :: Γ1 ++ Γ2, D)). apply OrImpLRule_I. repeat rewrite <- app_assoc in J50. simpl in J50.
      assert (J51: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J52: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J51 _ _ J52 _ J50). destruct s.
      assert (BoxImpLRule [(XBoxed_list (x2 ++ x4 ++ x3 ++ x6)  ++ [Box A0], A0); (Γ3 ++ B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)]
      (Γ3 ++ Imp (Box A0) B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)). apply BoxImpLRule_I ; auto.
      apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto.
      intro. destruct X0. inversion H. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto.
      intro. destruct X0. inversion H. apply BoxImpL in X0.
      pose (dlCons x5 DersNilF). pose (dlCons x0 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(XBoxed_list (x2 ++ x4 ++ x3 ++ x6) ++ [Box A0], A0); (Γ3 ++ B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D)])
      (Γ3 ++ Imp (Box A0) B0 :: x ++ A → C :: Γ1 ++ B → C :: Γ2, D) X0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* GLR *)
  * inversion X. subst. simpl.
    assert (GLRRule [(XBoxed_list BΓ ++ [Box A0], A0)] (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Box A0)). apply GLRRule_I ; auto.
    apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst. inversion u0. exfalso.
    subst. assert (In ((A ∨ B) → C) (x ++ (A ∨ B) → C :: l)). apply in_or_app. right. apply in_eq. pose (H1 ((A ∨ B) → C) H).
    destruct e. inversion H0. apply univ_gen_ext_combine ; auto. simpl in IH. subst. apply univ_gen_ext_extra ; auto.
    intro. destruct X1. inversion H. apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X0. inversion H. apply GLR in X1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(XBoxed_list BΓ ++ [Box A0], A0)]) (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, Box A0) X1 d). exists d0. simpl. auto.
Qed.

Theorem OrImpL_inv : forall concl prem, (derrec GL4ip_rules (fun _ => False) concl) ->
                                      (OrImpLRule [prem] concl) ->
                                      (derrec GL4ip_rules (fun _ => False) prem).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (OrImpL_hpinv _  _ X J1). pose (s _ H). destruct s0. auto.
Qed.