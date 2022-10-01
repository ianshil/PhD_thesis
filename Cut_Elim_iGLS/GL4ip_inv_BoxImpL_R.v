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

Theorem BoxImpL_hpinv_R : forall (k : nat) concl
        (D0 : derrec GL4ip_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem1 prem2, ((BoxImpLRule [prem1;prem2] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem2),
          derrec_height D1 <= k))).
Proof.
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec GL4ip_rules (fun _ : Seq => False) concl),
x = (derrec_height D0) ->
          ((forall prem1 prem2, ((BoxImpLRule [prem1;prem2] concl) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) prem2),
          derrec_height D1 <= x))))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. intros prem1 prem2 RA. inversion RA. subst.
  apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ Box A → B :: Γ1)).
    rewrite <- H3. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++  B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x1 ++ # P :: x2, # P)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x1 ++ # P :: x2, # P) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ Box A → B :: Γ1)).
    rewrite <- H3. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x1 ++ ⊥ :: x2, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x1 ++ ⊥ :: x2, C) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: BoxImpLRule [(XBoxed_list (x ++ x0) ++ [Box A], A); (Γ0 ++ B :: Γ1, A0)] (Γ0 ++ Box A → B :: Γ1, A0)).
    apply BoxImpLRule_I ; auto. apply univ_gen_ext_combine ; auto. simpl in IH.
    assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
    pose (IH _ J2 _ _ J3 _ _ J1). destruct s.
    assert (J4: BoxImpLRule [(XBoxed_list (x ++ x0) ++ [Box A], A);(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ Box A → B :: Γ1, B0)).
    apply BoxImpLRule_I ; auto. apply univ_gen_ext_combine ; auto.
    assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (AndRRule [(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)]
   (Γ0 ++ B :: Γ1, And A0 B0)). apply AndRRule_I. pose (dlCons x4 DersNilF). pose (dlCons x3 d0).
    apply AndR in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)])
    (Γ0 ++ B :: Γ1, And A0 B0) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H3. destruct H3. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In (A0 ∧ B0) (x ++ x3 ++ A0 ∧ B0 :: l)). apply in_or_app ; right.
      apply in_or_app ; right. apply in_eq. apply H2 in H0. destruct H0. inversion H0. subst.
      assert (AndLRule [((Γ0 ++ B :: x2) ++ A0 :: B0 :: Γ3, C)]
       ((Γ0 ++ B :: x2) ++ And A0 B0 :: Γ3, C)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: BoxImpLRule [(XBoxed_list (x ++ x3 ++ (top_boxes [A0;B0]) ++ x4) ++ [Box A], A);(Γ0 ++ B :: x2 ++ A0 :: B0 :: Γ3, C)]
       (((Γ0 ++ [Box A → B]) ++ x2) ++ A0 :: B0 :: Γ3, C)).
       { repeat rewrite <- app_assoc. destruct (dec_is_boxedT A0) ; destruct (dec_is_boxedT B0).
          - apply BoxImpLRule_I ; auto. destruct i ; destruct i0. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto.
            inversion H1. subst. exists x0. auto. inversion H4. subst. exists x5 ; auto.
            apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [A0; B0] = A0 :: [B0]). destruct i ; destruct i0; subst ; simpl ; auto.
            rewrite H1. simpl. repeat apply univ_gen_ext_combine ; auto.  repeat apply univ_gen_ext_cons ; auto.
          - apply BoxImpLRule_I ; auto. destruct i. subst. assert (top_boxes [Box x0; B0] = [Box x0]).
            destruct B0 ; auto. exfalso. apply f. exists B0 ; auto. rewrite H1. simpl. intro. intros. apply in_app_or in H4.
            destruct H4. apply H2. apply in_or_app ; auto. apply in_app_or in H4 ; destruct H4. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto.
            inversion H4. subst. exists x0. auto. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [A0; B0] = [A0]). destruct i ; destruct B0 ; subst ; simpl ; auto. exfalso. apply f ; exists B0 ; auto.
            rewrite H1. simpl. repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
            apply univ_gen_ext_extra ; auto.
          - apply BoxImpLRule_I ; auto. destruct i. subst. assert (top_boxes [A0; Box x0] = [Box x0]).
            destruct A0 ; auto. exfalso. apply f. exists A0 ; auto. rewrite H1. simpl. intro. intros. apply in_app_or in H4.
            destruct H4. apply H2. apply in_or_app ; auto. apply in_app_or in H4 ; destruct H4. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto.
            inversion H4. subst. exists x0. auto. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [A0; B0] = [B0]). destruct i ; destruct A0 ; subst ; simpl ; auto. exfalso. apply f ; exists A0 ; auto.
            rewrite H1. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_extra ; auto. apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [A0; B0] = []).
            destruct A0 ; destruct B0 ; auto ; exfalso. apply f0 ; try exists B0 ; auto. apply f0 ; try exists B0 ; auto.
            apply f0 ; try exists B0 ; auto. apply f0 ; try exists B0 ; auto. apply f0 ; try exists B0 ; auto. apply f ; try exists A0 ; auto.
            try apply f ; exists A0 ; auto. apply f ; try exists A0 ; auto. apply f ; try exists A0 ; auto. apply f ; try exists A0 ; auto.
            apply f ; try exists A0 ; auto. rewrite H1 ; auto.
            apply BoxImpLRule_I ; simpl ; auto. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. }
       assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x0 DersNilF). apply AndL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x2 ++ A0 :: B0 :: Γ3, C)])
       (Γ0 ++ B :: x2 ++ And A0 B0 :: Γ3, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In (A0 ∧ B0) ((x3 ++ A0 ∧ B0 :: l) ++ x0)). apply in_or_app ; left.
      apply in_or_app ; right. apply in_eq. apply H2 in H0. destruct H0. inversion H0. subst.
      assert (AndLRule [(Γ2 ++ A0 :: B0 :: x1 ++ B :: Γ1, C)]
       (Γ2 ++ A0 ∧ B0 :: x1 ++ B :: Γ1, C)).  apply AndLRule_I. repeat rewrite <- app_assoc. simpl.
       assert (J4: BoxImpLRule [(XBoxed_list (x3 ++ (top_boxes [A0;B0]) ++ x4 ++ x0) ++ [Box A], A);((Γ2 ++ A0 :: B0 :: x1) ++ B :: Γ1, C)]
       ((Γ2 ++ A0 :: B0 :: x1) ++ Box A → B :: Γ1, C)).
       { destruct (dec_is_boxedT A0) ; destruct (dec_is_boxedT B0).
          - apply BoxImpLRule_I ; auto. destruct i ; destruct i0. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; left ; apply in_or_app ; auto.
            inversion H1. subst. exists x. auto. inversion H4. subst. exists x5 ; auto.
            apply H2. apply in_app_or in H5 ; destruct H5.
            apply in_or_app ; left ; apply in_or_app ; auto. apply in_or_app ; auto.
            assert (top_boxes [A0; B0] = A0 :: [B0]). destruct i ; destruct i0; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
            apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
          - apply BoxImpLRule_I ; auto. destruct i. subst. assert (top_boxes [Box x; B0] = [Box x]).
            destruct B0 ; auto. exfalso. apply f. exists B0 ; auto. rewrite H1. simpl. intro. intros. apply in_app_or in H4.
            destruct H4. apply H2. apply in_or_app ; left ; apply in_or_app ; auto. inversion H4. subst. exists x. auto.
            apply in_app_or in H5 ; destruct H5. apply H2.
            apply in_or_app ;left ; apply in_or_app ; auto. apply H2. apply in_or_app ; auto.
            assert (top_boxes [A0; B0] = [A0]). destruct i ; destruct B0 ; subst ; simpl ; auto. exfalso. apply f ; exists B0 ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc ; simpl. repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
            apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto.
          - apply BoxImpLRule_I ; auto. destruct i. subst. assert (top_boxes [A0; Box x] = [Box x]).
            destruct A0 ; auto. exfalso. apply f. exists A0 ; auto. rewrite H1. simpl. intro. intros. apply in_app_or in H4. repeat rewrite <- app_assoc in H2.
            destruct H4. apply H2. apply in_or_app ; auto.
            inversion H4. subst. exists x. auto. apply H2. apply in_app_or in H5 ; destruct H5.
            apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [A0; B0] = [B0]). destruct i ; destruct A0 ; subst ; simpl ; auto. exfalso. apply f ; exists A0 ; auto.
            rewrite H1. repeat rewrite <- app_assoc. simpl. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_extra ; auto. apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [A0; B0] = []).
            destruct A0 ; destruct B0 ; auto ; exfalso. apply f0 ; try exists B0 ; auto. apply f0 ; try exists B0 ; auto.
            apply f0 ; try exists B0 ; auto. apply f0 ; try exists B0 ; auto. apply f0 ; try exists B0 ; auto. apply f ; try exists A0 ; auto.
            try apply f ; exists A0 ; auto. apply f ; try exists A0 ; auto. apply f ; try exists A0 ; auto. apply f ; try exists A0 ; auto.
            apply f ; try exists A0 ; auto. rewrite H1 ; auto.
            apply BoxImpLRule_I ; simpl ; auto ; repeat rewrite <- app_assoc ; simpl.
            rewrite <- app_assoc in H2 ; auto. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
       assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x2 = derrec_height x2). reflexivity. repeat rewrite <- app_assoc in J4.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x DersNilF). apply AndL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ2 ++ (A0 :: B0 :: x1) ++ B :: Γ1, C)])
       (Γ2 ++ A0 ∧ B0 :: x1 ++ B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. simpl in l. lia. reflexivity.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: BoxImpLRule [(XBoxed_list (x ++ x0) ++ [Box A], A);(Γ0 ++ B :: Γ1, A0)] (Γ0 ++ Box A → B :: Γ1, A0)). apply BoxImpLRule_I ; auto.
    apply univ_gen_ext_combine ; auto.
    assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (OrR1Rule [(Γ0 ++ B :: Γ1, A0)] (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons x2 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ B :: Γ1, A0)])
    (Γ0 ++ B :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: BoxImpLRule [(XBoxed_list (x ++ x0) ++ [Box A], A);(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ Box A → B :: Γ1, B0)).
    apply BoxImpLRule_I ; auto ; apply univ_gen_ext_combine ; auto.
    assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (OrR2Rule [(Γ0 ++ B :: Γ1, B0)]
    (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons x2 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ B :: Γ1, B0)])
    (Γ0 ++ B :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H3. destruct H3. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (OrLRule [((Γ0 ++ B :: x2) ++ A0 :: Γ3, C);((Γ0 ++ B :: x2) ++ B0 :: Γ3, C)]
      ((Γ0 ++ B :: x2) ++ Or A0 B0 :: Γ3, C)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In (A0 ∨ B0) (x ++ x4 ++ A0 ∨ B0 :: l)). apply in_or_app ; right.
      apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
       assert (J4: BoxImpLRule [(XBoxed_list (x ++ x4 ++ (top_boxes [A0]) ++ x5) ++ [Box A], A);(Γ0 ++ B :: x2 ++ A0 :: Γ3, C)]
       (((Γ0 ++ [Box A → B]) ++ x2) ++ A0 :: Γ3, C)).
       { repeat rewrite <- app_assoc. destruct (dec_is_boxedT A0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto.
            inversion H1. subst. exists x0. auto. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat apply univ_gen_ext_combine ; auto.  repeat apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl.
            apply BoxImpLRule_I ; simpl ; auto. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. }
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       assert (J7: BoxImpLRule [(XBoxed_list (x ++ x4 ++ (top_boxes [B0]) ++ x5) ++ [Box A], A);(Γ0 ++ B :: x2 ++ B0 :: Γ3, C)]
       (((Γ0 ++ [Box A → B]) ++ x2) ++ B0 :: Γ3, C)).
       { repeat rewrite <- app_assoc. destruct (dec_is_boxedT B0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto.
            inversion H1. subst. exists x6. auto. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [B0] = [B0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat apply univ_gen_ext_combine ; auto.  repeat apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [B0] = []).
            destruct B0 ; auto ; exfalso ; apply f ; exists B0 ; auto. rewrite H1 ; auto. simpl.
            apply BoxImpLRule_I ; simpl ; auto. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. }
      assert (J8: derrec_height x3 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x3 = derrec_height x3). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      pose (dlCons x6 DersNilF). pose (dlCons x0 d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ B :: x2 ++ A0 :: Γ3, C); (Γ0 ++ B :: x2 ++ B0 :: Γ3, C)])
      (Γ0 ++ B :: x2 ++ Or A0 B0 :: Γ3, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (OrLRule [(Γ2 ++ A0 :: x1 ++ B :: Γ1, C);(Γ2 ++ B0 :: x1 ++ B :: Γ1, C)]
      (Γ2 ++ Or A0 B0 :: x1 ++ B :: Γ1, C)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In (A0 ∨ B0) ((x4 ++ A0 ∨ B0 :: l) ++ x0)). apply in_or_app ; left.
      apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
       assert (J4: BoxImpLRule [(XBoxed_list (x4 ++ (top_boxes [A0]) ++ x5 ++ x0) ++ [Box A], A);((Γ2 ++ A0 :: x1) ++ B :: Γ1, C)]
       ((Γ2 ++ A0 :: x1) ++ Box A → B :: Γ1, C)).
       { destruct (dec_is_boxedT A0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. rewrite <- app_assoc in H2. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto.
            inversion H1. subst. exists x. auto. apply H2.  apply in_app_or in H3 ; destruct H3.
            apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto. simpl.
            apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl. rewrite <- app_assoc in H2.
            apply BoxImpLRule_I ; simpl ; auto. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. }
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       assert (J7: BoxImpLRule [(XBoxed_list (x4 ++ (top_boxes [B0]) ++ x5 ++ x0) ++ [Box A], A);((Γ2 ++ B0 :: x1) ++ B :: Γ1, C)]
       ((Γ2 ++ B0 :: x1) ++ Box A → B :: Γ1, C)).
       { destruct (dec_is_boxedT B0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. rewrite <- app_assoc in H2. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto.
            inversion H1. subst. exists x6. auto. apply H2.  apply in_app_or in H3 ; destruct H3.
            apply in_or_app ; right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; auto.
            assert (top_boxes [B0] = [B0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto. simpl.
            apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [B0] = []).
            destruct B0 ; auto ; exfalso ; apply f ; exists B0 ; auto. rewrite H1 ; auto. simpl. rewrite <- app_assoc in H2.
            apply BoxImpLRule_I ; simpl ; auto. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. }
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x3 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x3 = derrec_height x3). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      pose (dlCons x6 DersNilF). pose (dlCons x d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x1 ++ B :: Γ1, C); (Γ2 ++ B0 :: x1 ++ B :: Γ1, C)])
      (Γ2 ++ Or A0 B0 :: x1 ++ B :: Γ1, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (J50: derrec_height x1 = derrec_height x1). auto.
     assert (J51: list_exch_L (Γ2 ++ A0 :: Γ3, B0) (A0 :: Γ0 ++ Box A → B :: Γ1, B0)).
     assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). auto. rewrite H0.
     assert (A0 :: Γ0 ++ Box A → B :: Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). rewrite <- H3 ; auto. rewrite H1. apply list_exch_LI.
     pose (GL4ip_hpadm_list_exch_L _ _ _ J50 _ J51). destruct s.
     assert (ImpRRule [([] ++ A0 :: Γ0 ++ B :: Γ1, B0)] ([] ++ Γ0 ++ B :: Γ1, Imp A0 B0)). apply ImpRRule_I. simpl in H0.
     assert (J4: BoxImpLRule [(XBoxed_list (top_boxes [A0] ++ x ++ x0) ++ [Box A], A);((A0 :: Γ0) ++ B :: Γ1, B0)]
     ((A0 :: Γ0) ++ Box A → B :: Γ1, B0)).
     { destruct (dec_is_boxedT A0).
        - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros.
          inversion H1. subst. exists x3. auto. apply H2 ; auto.
          assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
          rewrite H1. simpl. apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
        - assert (top_boxes [A0] = []).
          destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto.
          apply BoxImpLRule_I ; simpl ; auto. apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
     repeat rewrite <- app_assoc in J4. simpl in J4.
     assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
     assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
     pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
     pose (dlCons x3 DersNilF). apply ImpR in H0.
     pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(A0 :: Γ0 ++ B :: Γ1, B0)]) (Γ0 ++ B :: Γ1, A0 → B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H3. destruct H3. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (AtomImpL1Rule [((Γ0 ++ B :: x3) ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ B :: x3) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, C)). apply AtomImpL1Rule_I.
       apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
       inversion u1. exfalso. subst. assert (In (# P) (x ++ x2 ++ # P :: l)). apply in_or_app ; right.
       apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
       apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
       inversion u3. exfalso. subst. assert (In (# P → A0) (x ++ x2 ++ x0 ++ # P → A0 :: l)). apply in_or_app ; right.
       apply in_or_app ; right. apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
       assert (J4: BoxImpLRule [(XBoxed_list (x ++ x2 ++ x0 ++ (top_boxes [A0]) ++ x5) ++ [Box A], A);(Γ0 ++ B :: x3 ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       (((Γ0 ++ [Box A → B]) ++ x3) ++ # P :: Γ3 ++ A0 :: Γ4, C)).
       { destruct (dec_is_boxedT A0).
          - repeat rewrite <- app_assoc.  apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto. inversion H1. subst. exists x4. auto.
            apply H2. apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl. repeat rewrite <- app_assoc.
            apply BoxImpLRule_I ; simpl ; auto. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. }
       assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x4 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x3 ++ # P :: Γ3 ++ A0 :: Γ4, C)])
       (Γ0 ++ B :: x3 ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In (# P) ((x3 ++ # P :: l) ++ x0)). apply in_or_app ; left.
      apply in_or_app ; right. apply in_eq. apply H2 in H0. destruct H0. inversion H0. subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (AtomImpL1Rule [(Γ2 ++ # P :: (x2 ++ B :: x5) ++ A0 :: Γ4, C)]
        (Γ2 ++ # P :: (x2 ++ B :: x5) ++ Imp # P A0 :: Γ4, C)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc in H0 ; simpl in H0.
        apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
        inversion u2. exfalso. subst. assert (In (# P → A0) ((x3 ++ x4) ++ x ++ # P → A0 :: l)). apply in_or_app ; right.
        apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
        assert (J4: BoxImpLRule [(XBoxed_list (x3 ++ x4 ++ x ++ (top_boxes [A0]) ++ x6) ++ [Box A], A);((Γ2 ++ # P :: x2) ++ B :: x5 ++ A0 :: Γ4, C)]
        ((Γ2 ++ # P :: x2) ++ Box A → B :: x5 ++ A0 :: Γ4, C)).
       { destruct (dec_is_boxedT A0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. rewrite <- app_assoc in H2. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto. inversion H1. subst. exists x0. auto.
            apply H2. apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl. rewrite <- app_assoc in H2.
            apply BoxImpLRule_I ; simpl ; auto. repeat rewrite <- app_assoc. simpl. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. }
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert ((Γ2 ++ # P :: x2 ++ Box A → B :: x5 ++ A0 :: Γ4, C) = (Γ2 ++ # P :: ((x2 ++ [Box A → B]) ++ x5) ++ A0 :: Γ4, C)).
        repeat rewrite <- app_assoc ; auto. rewrite H1 in J4.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x0 DersNilF). apply AtomImpL1 in H0. 
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: x2 ++ B :: x5 ++ A0 :: Γ4, C)])
        (Γ2 ++ # P :: x2 ++ B :: x5 ++ Imp # P A0 :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { repeat destruct s ; repeat destruct p ; subst. simpl.
        assert (AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A0 :: x ++ B :: Γ1, C)]
        (Γ2 ++ # P :: Γ3 ++ Imp # P A0 :: x ++ B :: Γ1, C)). apply AtomImpL1Rule_I.
        inversion u1. exfalso. subst. assert (In (# P) ((x3 ++ # P :: l) ++ x0)). apply in_or_app ; left.
        apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
        apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
        inversion u3. exfalso. subst. assert (In (# P → A0) ((x3 ++ x2 ++ # P → A0 :: l) ++ x0)). apply in_or_app ; left.
        apply in_or_app ; right.  apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst. repeat rewrite <- app_assoc in H2.
        assert (J4: BoxImpLRule [(XBoxed_list (x3 ++ x2 ++ (top_boxes [A0]) ++ x5 ++ x0) ++ [Box A], A);((Γ2 ++ # P :: Γ3 ++ A0 :: x) ++ B :: Γ1, C)]
        ((Γ2 ++ # P :: Γ3 ++ A0 :: x) ++ Box A → B :: Γ1, C)).
       { destruct (dec_is_boxedT A0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. inversion H1. subst. exists x4. auto.
            apply in_app_or in H4 ; destruct H4. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
            apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl.
            apply BoxImpLRule_I ; simpl ; auto. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
        repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x4 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: x ++ B :: Γ1, C)])
        (Γ2 ++ # P :: Γ3 ++ Imp (# P) A0 :: x ++ B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
  (* AtomImpL2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H3. destruct H3. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (AtomImpL2Rule [((Γ0 ++ B :: x3) ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       ((Γ0 ++ B :: x3) ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
       apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
       inversion u1. exfalso. subst. assert (In (# P → A0) (x ++ x2 ++ # P → A0 :: l)). apply in_or_app ; right.
       apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
       apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
       inversion u3. exfalso. subst. assert (In (# P) (x ++ x2 ++ x0 ++ # P  :: l)). apply in_or_app ; right.
       apply in_or_app ; right. apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
       assert (J4: BoxImpLRule [(XBoxed_list (x ++ x2 ++ (top_boxes [A0]) ++ x0 ++ x5) ++ [Box A], A);(Γ0 ++ B :: x3 ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       (((Γ0 ++ [Box A → B]) ++ x3) ++ A0 :: Γ3 ++ # P :: Γ4, C)).
       { destruct (dec_is_boxedT A0).
          - repeat rewrite <- app_assoc.  apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. inversion H1. subst. exists x4. auto.
            apply in_app_or in H3 ; destruct H3. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            apply H2. apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl. repeat rewrite <- app_assoc.
            apply BoxImpLRule_I ; simpl ; auto. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
       assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x4 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x3 ++ A0 :: Γ3 ++ # P :: Γ4, C)])
       (Γ0 ++ B :: x3 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In (# P → A0) ((x3 ++ # P → A0 :: l) ++ x0)). apply in_or_app ; left.
      apply in_or_app ; right. apply in_eq. apply H2 in H0. destruct H0. inversion H0. subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (AtomImpL2Rule [(Γ2 ++ A0 :: (x2 ++ B :: x5) ++ # P :: Γ4, C)]
        (Γ2 ++ # P → A0 :: (x2 ++ B :: x5) ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc in H0 ; simpl in H0.
        apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
        inversion u2. exfalso. subst. assert (In (# P) ((x3 ++ x4) ++ x ++ # P :: l)). apply in_or_app ; right.
        apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
        assert (J4: BoxImpLRule [(XBoxed_list (x3 ++ (top_boxes [A0]) ++ x4 ++ x ++ x6) ++ [Box A], A);((Γ2 ++ A0 :: x2) ++ B :: x5 ++ # P :: Γ4, C)]
        ((Γ2 ++ A0 :: x2) ++ Box A → B :: x5 ++ # P :: Γ4, C)).
       { destruct (dec_is_boxedT A0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. rewrite <- app_assoc in H2. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. inversion H1. subst. exists x0. auto.
            apply in_app_or in H4 ; destruct H4. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H4 ; destruct H4. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            apply H2. apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. repeat apply univ_gen_ext_combine ; auto. simpl.
            apply univ_gen_ext_cons ; auto. repeat apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl. rewrite <- app_assoc in H2.
            apply BoxImpLRule_I ; simpl ; auto. repeat rewrite <- app_assoc. simpl. repeat apply univ_gen_ext_combine ; auto.
            repeat apply univ_gen_ext_extra ; auto. repeat apply univ_gen_ext_combine ; auto. }
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert ((Γ2 ++ A0 :: x2 ++ Box A → B :: x5 ++ # P :: Γ4, C) = (Γ2 ++ A0 :: ((x2 ++ [Box A → B]) ++ x5) ++ # P :: Γ4, C)).
        repeat rewrite <- app_assoc ; auto. rewrite H1 in J4.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x0 DersNilF). apply AtomImpL2 in H0. 
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: x2 ++ B :: x5 ++ # P :: Γ4, C)])
        (Γ2 ++ # P → A0 :: x2 ++ B :: x5 ++ # P :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
      { repeat destruct s ; repeat destruct p ; subst. simpl.
        assert (AtomImpL2Rule [(Γ2 ++ A0 :: Γ3 ++ # P :: x ++ B :: Γ1, C)]
        (Γ2 ++ # P → A0 :: Γ3 ++ # P :: x ++ B :: Γ1, C)). apply AtomImpL2Rule_I.
        inversion u1. exfalso. subst. assert (In (# P → A0) ((x3 ++ # P → A0 :: l) ++ x0)). apply in_or_app ; left.
        apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
        apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
        inversion u3. exfalso. subst. assert (In (# P) ((x3 ++ x2 ++ # P :: l) ++ x0)). apply in_or_app ; left.
        apply in_or_app ; right.  apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst. repeat rewrite <- app_assoc in H2.
        assert (J4: BoxImpLRule [(XBoxed_list (x3 ++ (top_boxes [A0]) ++ x2 ++ x5 ++ x0) ++ [Box A], A);((Γ2 ++ A0 :: Γ3 ++ # P :: x) ++ B :: Γ1, C)]
        ((Γ2 ++ A0 :: Γ3 ++ # P :: x) ++ Box A → B :: Γ1, C)).
       { destruct (dec_is_boxedT A0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. inversion H1. subst. exists x4. auto.
            apply in_app_or in H4 ; destruct H4. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. apply in_app_or in H4 ; destruct H4. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  right ; apply in_or_app ; auto.
            assert (top_boxes [A0] = [A0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto.
            apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [A0] = []).
            destruct A0 ; auto ; exfalso ; apply f ; exists A0 ; auto. rewrite H1 ; auto. simpl.
            apply BoxImpLRule_I ; simpl ; auto. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
        repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x4 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: x ++ B :: Γ1, C)])
        (Γ2 ++ # P → A0 :: Γ3 ++# P :: x ++ B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
 (* AndImpL *)
  * inversion H. subst. apply list_split_form in H3. destruct H3. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (AndImpLRule [((Γ0 ++ B :: x2) ++ A0 → B0 → C0 :: Γ3, C)]
    ((Γ0 ++ B :: x2) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I. repeat rewrite <- app_assoc in H0.
     apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
     inversion u1. exfalso. subst. assert (In ((A0 ∧ B0) → C0) (x ++ x3 ++ (A0 ∧ B0) → C0 :: l)). apply in_or_app ; right.
     apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
     assert (J4: BoxImpLRule [(XBoxed_list (x ++ x3 ++ x4) ++ [Box A], A);(Γ0 ++ B :: x2 ++ A0 → B0 → C0 :: Γ3, C)]
     (((Γ0 ++ [Box A → B]) ++ x2) ++ A0 → B0 → C0 :: Γ3, C)). repeat rewrite <- app_assoc. apply BoxImpLRule_I ; auto.
     repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X0. inversion H1.
     assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
     assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
     pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
     pose (dlCons x0 DersNilF). apply AndImpL in H0.
     pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ B :: x2 ++ Imp A0 (Imp B0 C0) :: Γ3, C)])
     (Γ0 ++ B :: x2 ++ Imp (And A0 B0) C0 :: Γ3, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndImpLRule [((Γ2 ++ Imp A0 (Imp B0 C0) :: x1) ++ B :: Γ1, C)]
      ((Γ2 ++ Imp (And A0 B0) C0 :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. apply AndImpLRule_I.
      apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In ((A0 ∧ B0) → C0) ((x3 ++ (A0 ∧ B0) → C0 :: l) ++ x0)). apply in_or_app ; left.
      apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
      assert (J4: BoxImpLRule [(XBoxed_list ((x3 ++ x4) ++ x0) ++ [Box A], A);((Γ2 ++ A0 → B0 → C0 :: x1) ++ B :: Γ1, C)]
      ((Γ2 ++ A0 → B0 → C0 :: x1) ++ Box A → B :: Γ1, C)).
      apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc ; simpl.
      repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X0 ; inversion H1.
      apply univ_gen_ext_combine ; auto. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x DersNilF). apply AndImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ Imp A0 (Imp B0 C0) :: x1 ++ B :: Γ1, C)])
     (Γ2 ++ Imp (And A0 B0) C0 :: x1 ++ B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply list_split_form in H3. destruct H3. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule [((Γ0 ++ B :: x2) ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)]
       ((Γ0 ++ B :: x2) ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
      apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In ((A0 ∨ B0) → C0) (x ++ x3 ++ (A0 ∨ B0) → C0 :: l)). apply in_or_app ; right.
      apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
      apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
       assert (J4: BoxImpLRule [(XBoxed_list (x ++ x3 ++ x0 ++ x5) ++ [Box A], A);(Γ0 ++ B :: x2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)]
       (((Γ0 ++ [Box A → B]) ++ x2) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)). repeat rewrite <- app_assoc. apply BoxImpLRule_I ; auto.
       repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X. inversion H1.
       apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X. inversion H1.
       assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x4 DersNilF). apply OrImpL in H0.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)])
       (Γ0 ++ B :: x2 ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
        rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J50: derrec_height x2 = derrec_height x2). auto.
      assert (J51: list_exch_L (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) (Γ2 ++ A0 → C0 :: B0 → C0 :: x1 ++ Box A → B :: Γ1, C)).
      assert (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4 = (Γ2 ++ [A0 → C0]) ++ [] ++ Γ3 ++ [B0 → C0] ++ Γ4).
      repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ2 ++ A0 → C0 :: B0 → C0 :: x1 ++ Box A → B :: Γ1 = (Γ2 ++ [A0 → C0]) ++ [B0 → C0] ++ Γ3 ++ [] ++ Γ4).
      rewrite <- e0 ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
      pose (GL4ip_hpadm_list_exch_L (derrec_height x2) (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) x2 J50
      _ J51). destruct s. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
      assert (OrImpLRule [(Γ2 ++ A0 → C0 :: [] ++ B0 → C0 :: x1 ++ B :: Γ1, C)]
      (Γ2 ++ Imp (Or A0 B0) C0 :: [] ++ x1 ++ B :: Γ1, C)). apply OrImpLRule_I. simpl in H0.
      apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In ((A0 ∨ B0) → C0) ((x4 ++ (A0 ∨ B0) → C0 :: l0) ++ x0)). apply in_or_app ; left.
      apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
      assert (J4: BoxImpLRule [(XBoxed_list ((x4 ++ x5) ++ x0) ++ [Box A], A);((Γ2 ++ A0 → C0 :: B0 → C0 :: x1) ++ B :: Γ1, C)]
      ((Γ2 ++ A0 → C0 :: B0 → C0 :: x1) ++ Box A → B :: Γ1, C)).
      apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc ; simpl.
      repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X0. inversion H1.
      apply univ_gen_ext_extra ; auto. intro. destruct X0. inversion H1. apply univ_gen_ext_combine ; auto.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x3 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x3 = derrec_height x3). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x DersNilF). apply OrImpL in H0.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 → C0 :: B0 → C0 :: x1 ++ B :: Γ1, C)])
      (Γ2 ++ (A0 ∨ B0) → C0 :: x1 ++ B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1.
      simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* ImpImpL *)
 * inversion H. subst. apply list_split_form in H3. destruct H3. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   +  assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
        assert (ImpImpLRule [((Γ0 ++ B :: x2) ++ Imp B0 C0 :: Γ3, Imp A0 B0); ((Γ0 ++ B :: x2) ++ C0 :: Γ3, C)]
        ((Γ0 ++ B :: x2) ++ Imp (Imp A0 B0) C0 :: Γ3, C)). apply ImpImpLRule_I. apply ImpImpL in H0.
        repeat rewrite <- app_assoc in H0. simpl in H0.
        apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
        inversion u1. exfalso. subst. assert (In ((A0 → B0) → C0) (x ++ x4 ++ (A0 → B0) → C0 :: l)). apply in_or_app ; right.
        apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
        assert (J4: BoxImpLRule [(XBoxed_list (x ++ x4 ++ x5) ++ [Box A], A);(Γ0 ++ B :: x2 ++ Imp B0 C0 :: Γ3, Imp A0 B0)]
        (((Γ0 ++ [Box A → B]) ++ x2) ++ Imp B0 C0 :: Γ3, Imp A0 B0)). repeat rewrite <- app_assoc. apply BoxImpLRule_I ; auto.
        repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X0. inversion H1.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        assert (J7: BoxImpLRule [(XBoxed_list (x ++ x4 ++ (top_boxes [C0]) ++ x5) ++ [Box A], A);(Γ0 ++ B :: x2 ++ C0 :: Γ3, C)]
        (((Γ0 ++ [Box A → B]) ++ x2) ++ C0 :: Γ3, C)).
        { destruct (dec_is_boxedT C0).
          - repeat rewrite <- app_assoc. apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H1.
            destruct H1. apply H2. apply in_or_app ; auto. apply in_app_or in H1 ; destruct H1. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. inversion H1. subst. exists x6. auto. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  auto.
            assert (top_boxes [C0] = [C0]). destruct i ; subst ; simpl ; auto.
            rewrite H1. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [C0] = []).
            destruct C0 ; auto ; exfalso ; apply f ; exists C0 ; auto. rewrite H1 ; auto. simpl. repeat rewrite <- app_assoc.
            apply BoxImpLRule_I ; simpl ; auto.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. }
        assert (J8: derrec_height x3 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x3 = derrec_height x3). reflexivity.
        pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
        pose (dlCons x6 DersNilF). pose (dlCons x0 d0).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ B :: x2 ++ Imp B0 C0 :: Γ3, Imp A0 B0); (Γ0 ++ B :: x2 ++ C0 :: Γ3, C)])
       (Γ0 ++ B :: x2 ++ Imp (Imp A0 B0) C0 :: Γ3, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (ImpImpLRule [(Γ2 ++ Imp B0 C0 :: x1 ++ B :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x1 ++ B :: Γ1, C)]
      (Γ2 ++ Imp (Imp A0 B0) C0 :: x1 ++ B :: Γ1, C)). apply ImpImpLRule_I. apply ImpImpL in H0.
      apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
      inversion u1. exfalso. subst. assert (In ((A0 → B0) → C0) ((x4 ++ (A0 → B0) → C0 :: l) ++ x0)). apply in_or_app ; left.
      apply in_or_app ; right. apply in_eq. apply H2 in H1. destruct H1. inversion H1. subst.
      assert (J4: BoxImpLRule [(XBoxed_list ((x4 ++ x5) ++ x0) ++ [Box A], A);((Γ2 ++ Imp B0 C0 :: x1) ++ B :: Γ1, Imp A0 B0)]
      ((Γ2 ++ Imp B0 C0 :: x1) ++ Box A → B :: Γ1, Imp A0 B0)). apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc. simpl.
      repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. intro. destruct X0. inversion H1.
      apply univ_gen_ext_combine ; auto.
      repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: BoxImpLRule [(XBoxed_list (x4 ++ (top_boxes [C0]) ++ x5 ++ x0) ++ [Box A], A);((Γ2 ++ C0 :: x1) ++ B :: Γ1, C)]
      ((Γ2 ++ C0 :: x1) ++ Box A → B :: Γ1, C)).
      { destruct (dec_is_boxedT C0).
        - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. rewrite <- app_assoc in H2. intro. intros. apply in_app_or in H1.
          destruct H1. apply H2. apply in_or_app ; auto. inversion H1. subst. exists x6. auto.
          apply in_app_or in H3 ; destruct H3. apply H2.
          apply in_or_app ; right ; apply in_or_app ; auto. apply H2.
          apply in_or_app ; right ; apply in_or_app ;  auto.
          assert (top_boxes [C0] = [C0]). destruct i ; subst ; simpl ; auto.
          rewrite H1. simpl. rewrite <- app_assoc ; simpl. repeat apply univ_gen_ext_combine ; auto.
          apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
        - assert (top_boxes [C0] = []).
          destruct C0 ; auto ; exfalso ; apply f ; exists C0 ; auto. rewrite H1 ; auto. simpl.
          apply BoxImpLRule_I ; simpl ; rewrite <- app_assoc in H2 ; auto. rewrite <- app_assoc ; simpl.
          repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
      repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x3 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x3 = derrec_height x3). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      pose (dlCons x6 DersNilF). pose (dlCons x d0).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ Imp B0 C0 :: x1 ++ B :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x1 ++ B :: Γ1, C)])
      (Γ2 ++ Imp (Imp A0 B0) C0 :: x1 ++ B :: Γ1, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* BoxImpL *)
 * inversion X. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    apply list_split_form in H. destruct H. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst. exists x2. lia.
   +  apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
       inversion u3. subst. exfalso. assert (In (Box A0 → B0)  (x ++ x5 ++ Box A0 → B0 :: l)).
       apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
       apply H2 in H. destruct H. inversion H. subst. rewrite <- app_assoc in u1. simpl in u1.
       apply univ_gen_ext_splitR in u1. destruct u1. destruct s. repeat destruct p ; subst.
       inversion u4. subst. exfalso. assert (In (Box A → B) ((x0 ++ Box A → B :: l) ++ x4)).
       apply in_or_app ; left ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst.
       assert (J4: BoxImpLRule [(XBoxed_list (x ++ x5 ++ (top_boxes [B0]) ++ x7) ++ [Box A], A);(Γ0 ++ B :: x6 ++ B0 :: Γ3, C)]
       (((Γ0 ++ [Box A → B]) ++ x6) ++ B0 :: Γ3, C)). repeat rewrite <- app_assoc.
       { destruct (dec_is_boxedT B0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H.
            destruct H. apply H2. apply in_or_app ; auto. apply in_app_or in H ; destruct H. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. inversion H. subst. exists x3. auto. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  auto.
            assert (top_boxes [B0] = [B0]). destruct i ; subst ; simpl ; auto.
            rewrite H. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [B0] = []).
            destruct B0 ; auto ; exfalso ; apply f ; exists B0 ; auto. rewrite H ; auto. simpl. repeat rewrite <- app_assoc.
            apply BoxImpLRule_I ; simpl ; auto.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. }
       assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       assert (BoxImpLRule [(XBoxed_list (x0 ++ (top_boxes [B]) ++ x8 ++ x4) ++ [Box A0], A0);((Γ0 ++ B :: x6) ++ B0 :: Γ3, C)]
       ((Γ0 ++ B :: x6) ++ Box A0 → B0 :: Γ3, C)).
       { destruct (dec_is_boxedT B).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. rewrite <- app_assoc in H1. apply in_app_or in H.
            destruct H. apply H1. apply in_or_app ; auto. inversion H. subst. exists x9. auto.
            apply in_app_or in H0 ; destruct H0. apply H1.
            apply in_or_app ; right ; apply in_or_app ; auto. apply H1.
            apply in_or_app ; right ; apply in_or_app ;  auto.
            assert (top_boxes [B] = [B]). destruct i ; subst ; simpl ; auto.
            rewrite H. simpl. rewrite <- app_assoc. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [B] = []).
            destruct B ; auto ; exfalso ; apply f ; exists B ; auto. rewrite H ; auto. simpl.
            apply BoxImpLRule_I ; simpl ; rewrite <- app_assoc in H1 ; auto. rewrite <- app_assoc ; simpl.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
       repeat rewrite <- app_assoc in X2.
       assert (existsT2 (D2 : derrec GL4ip_rules (fun _ : Seq => False) (XBoxed_list (x0 ++ top_boxes [B] ++ x8 ++ x4) ++ [Box A0], A0)),
       derrec_height D2 <= derrec_height x1).
       { destruct (dec_is_boxedT B).
          - assert (top_boxes [B] = [B]). destruct i. subst ; auto. rewrite H. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (J1: derrec_height x1 = derrec_height x1). auto.
            pose (@GL4ip_list_wkn_L _ _ _ _ _ J1 (XBoxed_list [B])). destruct s.
            assert (J2: derrec_height x9 = derrec_height x9). auto.
            assert (J3: list_exch_L (XBoxed_list ((x0 ++ x8) ++ x4) ++ XBoxed_list [B] ++ [Box A0], A0) (XBoxed_list x0 ++ XBoxed_list [B] ++ XBoxed_list x8 ++ XBoxed_list x4 ++ [Box A0], A0)).
            repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (XBoxed_list x0 ++ XBoxed_list x8 ++ XBoxed_list x4 ++ XBoxed_list [B] ++ [Box A0] = XBoxed_list x0 ++ [] ++ (XBoxed_list x8 ++ XBoxed_list x4) ++ XBoxed_list [B] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0.
            assert (XBoxed_list x0 ++ XBoxed_list [B] ++ XBoxed_list x8 ++ XBoxed_list x4 ++ [Box A0] = XBoxed_list x0 ++ XBoxed_list [B] ++ (XBoxed_list x8 ++ XBoxed_list x4) ++ [] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H5. apply list_exch_LI.
            pose (GL4ip_hpadm_list_exch_L _ _ _ J2 _ J3). destruct s. exists x10. lia.
          - assert (top_boxes [B] = []).
            destruct B ; auto ; exfalso ; apply f ; exists B ; auto. rewrite H ; auto. simpl. rewrite  app_assoc. exists x1. lia. }
       destruct X3. apply BoxImpL in X2.
       pose (dlCons x3 DersNilF). pose (dlCons x9 d0).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(XBoxed_list (x0 ++ top_boxes [B] ++ x8 ++ x4) ++ [Box A0], A0); (Γ0 ++ B :: x6 ++ B0 :: Γ3, C)])
       (Γ0 ++ B :: x6 ++ Box A0 → B0 :: Γ3, C) X2 d1). repeat rewrite <- app_assoc. exists d2. simpl.
       rewrite dersrec_height_nil ; auto. simpl in l0. lia.
   +  repeat destruct s. repeat destruct p ; subst.
       apply univ_gen_ext_splitR in u. destruct u. destruct s. repeat destruct p ; subst.
       inversion u3. subst. exfalso. assert (In (Box A0 → B0)  ((x6 ++ Box A0 → B0 :: l) ++ x0)).
       apply in_or_app ; left ; apply in_or_app ; right ; apply in_eq.
       apply H2 in H. destruct H. inversion H. subst.
       apply univ_gen_ext_splitR in u2. destruct u2. destruct s. repeat destruct p ; subst.
       inversion u4. subst. exfalso. assert (In (Box A → B) (x3 ++ x ++ Box A → B :: l)).
       apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
       apply H1 in H. destruct H. inversion H. subst.
       assert (J4: BoxImpLRule [(XBoxed_list (x6 ++ (top_boxes [B0]) ++ x7 ++ x0) ++ [Box A], A);((Γ2 ++ B0 :: x5) ++ B :: Γ1, C)]
      ((Γ2 ++ B0 :: x5) ++ Box A → B :: Γ1, C)).
       { destruct (dec_is_boxedT B0).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. rewrite <- app_assoc in H2. intro. intros. apply in_app_or in H.
            destruct H. apply H2. apply in_or_app ; auto. inversion H. subst. exists x4. auto. apply in_app_or in H0 ; destruct H0. apply H2.
            apply in_or_app ; right ; apply in_or_app ; auto. apply H2.
            apply in_or_app ; right ; apply in_or_app ;  auto.
            assert (top_boxes [B0] = [B0]). destruct i ; subst ; simpl ; auto.
            rewrite H. simpl. rewrite <- app_assoc ; simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
          - assert (top_boxes [B0] = []).
            destruct B0 ; auto ; exfalso ; apply f ; exists B0 ; auto. rewrite H ; auto. simpl.
            apply BoxImpLRule_I ; simpl ; rewrite <- app_assoc in H2 ; auto. rewrite <- app_assoc. simpl.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto. }
       assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x2 = derrec_height x2). reflexivity. repeat rewrite <- app_assoc in J4. rewrite <- app_assoc. simpl.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       assert (BoxImpLRule [(XBoxed_list (x3 ++ x ++ (top_boxes [B]) ++ x8) ++ [Box A0], A0);(Γ2 ++ B0 :: x5 ++ B :: Γ1, C)]
       (Γ2 ++ Box A0 → B0 :: x5 ++ B :: Γ1, C)).
       { destruct (dec_is_boxedT B).
          - apply BoxImpLRule_I ; auto. destruct i. subst. simpl. intro. intros. apply in_app_or in H.
            destruct H. apply H1. apply in_or_app ; auto.
            apply in_app_or in H ; destruct H. apply H1.
            apply in_or_app ; right ; apply in_or_app ; auto. inversion H. subst. exists x9. auto. apply H1.
            apply in_or_app ; right ; apply in_or_app ;  auto.
            assert (top_boxes [B] = [B]). destruct i ; subst ; simpl ; auto.
            rewrite H. simpl. repeat apply univ_gen_ext_combine ; auto.
            apply univ_gen_ext_cons ; auto.
          - assert (top_boxes [B] = []).
            destruct B ; auto ; exfalso ; apply f ; exists B ; auto. rewrite H ; auto. simpl.
            apply BoxImpLRule_I ; simpl  ; auto.
            repeat apply univ_gen_ext_combine ; auto. repeat apply univ_gen_ext_extra ; auto. }
       assert (existsT2 (D2 : derrec GL4ip_rules (fun _ : Seq => False) (XBoxed_list (x3 ++ x ++ top_boxes [B] ++ x8) ++ [Box A0], A0)),
       derrec_height D2 <= derrec_height x1).
       { destruct (dec_is_boxedT B).
          - assert (top_boxes [B] = [B]). destruct i. subst ; auto. rewrite H. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (J1: derrec_height x1 = derrec_height x1). auto.
            pose (@GL4ip_list_wkn_L _ _ _ _ _ J1 (XBoxed_list [B])). destruct s.
            assert (J2: derrec_height x9 = derrec_height x9). auto.
            assert (J3: list_exch_L (XBoxed_list (x3 ++ x ++ x8) ++ XBoxed_list [B] ++ [Box A0], A0) (XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list [B] ++ XBoxed_list x8 ++ [Box A0], A0)).
            repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
            assert (XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list x8 ++ XBoxed_list [B] ++ [Box A0] = (XBoxed_list x3 ++ XBoxed_list x) ++ [] ++ XBoxed_list x8 ++ XBoxed_list [B] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0.
            assert (XBoxed_list x3 ++ XBoxed_list x ++ XBoxed_list [B] ++ XBoxed_list x8 ++ [Box A0] = (XBoxed_list x3 ++ XBoxed_list x) ++ XBoxed_list [B] ++ XBoxed_list x8 ++ [] ++ [Box A0]).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H5. apply list_exch_LI.
            pose (GL4ip_hpadm_list_exch_L _ _ _ J2 _ J3). destruct s. exists x10. lia.
          - assert (top_boxes [B] = []).
            destruct B ; auto ; exfalso ; apply f ; exists B ; auto. rewrite H ; auto. simpl. exists x1. lia. }
       destruct X3. apply BoxImpL in X2.
       pose (dlCons x4 DersNilF). pose (dlCons x9 d0).
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(XBoxed_list (x3 ++ x ++ top_boxes [B] ++ x8) ++ [Box A0], A0); (Γ2 ++ (B0 :: x5) ++ B :: Γ1, C)])
       (Γ2 ++ Box A0 → B0 :: x5 ++ B :: Γ1, C) X2 d1). repeat rewrite <- app_assoc. exists d2. simpl.
       rewrite dersrec_height_nil ; auto. simpl in l0. simpl in l0. simpl in l. lia.
  (* GLR *)
  * inversion X. subst. simpl. apply univ_gen_ext_splitR in X0. destruct X0. destruct s. repeat destruct p ; subst.
    inversion u2. subst. exfalso. assert (In (Box A → B) (x1 ++ Box A → B :: l)). apply in_or_app ; right ; apply in_eq.
    apply H1 in H. destruct H. inversion H. subst.
    assert (GLRRule [(XBoxed_list (x1 ++ x2) ++ [Box A0], A0)] (Γ0 ++ Γ1, Box A0)). apply GLRRule_I ; auto.
    apply univ_gen_ext_combine ; auto. apply GLR in X1.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[(XBoxed_list (x1 ++ x2) ++ [Box A0], A0)]) (Γ0 ++ Γ1, Box A0) X1 d).
    assert (J1: derrec_height d0 = derrec_height d0). auto.
    assert (J2: wkn_L B (Γ0 ++ Γ1, Box A0) (Γ0 ++ B :: Γ1, Box A0)). apply wkn_LI.
    pose (@GL4ip_wkn_L (derrec_height d0) _ d0 J1 (Γ0 ++ B :: Γ1, Box A0) B J2). destruct s. exists x3.
    simpl. simpl in l. lia.
Qed.

Theorem BoxImpL_inv_R : forall concl prem1 prem2, (derrec GL4ip_rules (fun _ => False) concl) ->
                                      (BoxImpLRule [prem1;prem2] concl) ->
                                      (derrec GL4ip_rules (fun _ => False) prem2).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (BoxImpL_hpinv_R _ _ X J1). pose (s _ _ X0). destruct s0. assumption.
Qed.







