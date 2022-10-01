Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.
Require Import univ_gen_ext.
Require Import dd_fc.
Require Import PeanoNat.
Require Import strong_inductionT.
Require Import Lia.
Require Import GL4ip_PSGL4ip_calcs.
Require Import GL4ip_exch.
Require Import GL4ip_wkn.
Require Import GL4ip_inv_ImpR.

(* We can show that identities on formulae of all complexities are derivable in GL4ip. *)

Lemma Id_all_form0 : forall n (A : MPropF) Γ0 Γ1,
          (n = weight_form A) ->
          derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: Γ1, A).
Proof.
pose (strong_inductionT (fun (x:nat) => forall A Γ0 Γ1,
                      x = weight_form A ->
                      derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: Γ1, A))).
apply d. clear d. intros n IH. destruct A.
- intros. assert (IdPRule [] (Γ0 ++ # v :: Γ1, # v)). apply IdPRule_I. apply IdP in H0.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False) (ps:=[]).
  assumption. apply dersrec_nil.
- intros. assert (BotLRule [] (Γ0 ++ ⊥ :: Γ1, ⊥)). apply BotLRule_I. apply BotL in H0.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False) (ps:=[]).
  assumption. apply dersrec_nil.
- intros.  assert (AndLRule [(Γ0 ++ A1 :: A2 :: Γ1, And A1 A2)]  (Γ0 ++ And A1 A2 :: Γ1, And A1 A2)).
  apply AndLRule_I. apply AndL in H0.
  assert (AndRRule [(Γ0 ++ A1 :: A2 :: Γ1, A1) ; (Γ0 ++ A1 :: A2 :: Γ1, A2)] (Γ0 ++ A1 :: A2 :: Γ1, And A1 A2)).
  apply AndRRule_I. apply AndR in H1.
  assert (J1: weight_form A1 < n). subst. simpl. lia.
  pose (IH (weight_form A1) J1 A1 Γ0 (A2 :: Γ1)).
  assert (J2 : weight_form A2 < n). subst. simpl. lia.
  pose (IH (weight_form A2) J2 A2 (Γ0 ++ [A1]) Γ1). repeat rewrite <- app_assoc in d0. simpl in d0.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A1 :: A2 :: Γ1, And A1 A2)]) ; auto.
  apply dlCons. 2 : apply dersrec_nil.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A1 :: A2 :: Γ1, A1); (Γ0 ++ A1 :: A2 :: Γ1, A2)]).
  assumption. apply dlCons. auto. apply dlCons. auto. apply dersrec_nil.
- intros.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A1 :: Γ1, Or A1 A2) ; (Γ0 ++ A2 :: Γ1, Or A1 A2)]).
  apply OrL. apply OrLRule_I. apply dlCons.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A1 :: Γ1, A1)]). apply OrR1. apply OrR1Rule_I. apply dlCons. 2: apply dersrec_nil.
  assert (J1: weight_form A1 < n). subst. simpl. lia. pose (IH (weight_form A1) J1 A1 Γ0 Γ1). auto.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A2 :: Γ1, A2)]). apply OrR2. apply OrR2Rule_I. apply dlCons.
  assert (J2: weight_form A2 < n). subst. simpl. lia. pose (IH (weight_form A2) J2 A2 Γ0 Γ1). auto.
  apply dersrec_nil.
- intros. apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A1 :: Imp A1 A2 :: Γ1, A2)]). apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dersrec_nil.
  destruct A1 ; intros.
  + apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ # v :: A2 :: Γ1, A2)]). apply AtomImpL1. assert (Γ0 ++ # v :: Imp # v A2 :: Γ1 = Γ0 ++ # v :: [] ++ Imp # v A2 :: Γ1).
     auto. rewrite H0. assert (Γ0 ++ # v :: A2 :: Γ1 = Γ0 ++ # v :: [] ++ A2 :: Γ1). auto. rewrite H1. apply AtomImpL1Rule_I.
     apply dlCons. 2: apply dersrec_nil. assert (J1: (weight_form A2) < n). subst. simpl. lia. pose (IH (weight_form A2) J1 A2 (Γ0 ++ [# v]) Γ1).
     rewrite <- app_assoc in d. simpl in d. apply d. auto.
  + apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[]). apply BotL. apply BotLRule_I. apply dersrec_nil.
  + apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ A1_1 :: A1_2 :: Imp (And A1_1 A1_2) A2 :: Γ1, A2)]). apply AndL. apply AndLRule_I.
     apply dlCons. 2: apply dersrec_nil.
     apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, A2)]). apply AndImpL.
     assert (Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1 = (Γ0 ++ A1_1 :: [A1_2]) ++ Imp A1_1 (Imp A1_2 A2) :: Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H0.
     assert (Γ0 ++ A1_1 :: A1_2 :: Imp (And A1_1 A1_2) A2 :: Γ1 = (Γ0 ++ A1_1 :: [A1_2]) ++ Imp (And A1_1 A1_2) A2 :: Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H1. apply AndImpLRule_I. apply dlCons. 2: apply dersrec_nil.
     assert (J1: weight_form (Imp A1_1 (Imp A1_2 A2)) < n). simpl. simpl in H. lia.
     assert (J2: weight_form (Imp A1_1 (Imp A1_2 A2)) = weight_form (Imp A1_1 (Imp A1_2 A2))). auto.
     pose (IH (weight_form (Imp A1_1 (Imp A1_2 A2))) J1 (Imp A1_1 (Imp A1_2 A2)) Γ0 Γ1 J2).
     assert (ImpRRule [(Γ0 ++ A1_1 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, Imp A1_2 A2)] (Γ0 ++ Imp A1_1 (Imp A1_2 A2) :: Γ1, Imp A1_1 (Imp A1_2 A2))).
     apply ImpRRule_I. assert (J3: derrec_height d = derrec_height d). auto.
      pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H0). destruct s. clear l.
     assert (ImpRRule [(Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, A2)] (Γ0 ++ A1_1 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, Imp A1_2 A2)).
     assert (Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1 = (Γ0 ++ [A1_1]) ++ A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1).
     repeat rewrite <- app_assoc ; auto. rewrite H1.
     assert (Γ0 ++ A1_1 :: Imp A1_1 (Imp A1_2 A2) :: Γ1 = (Γ0 ++ [A1_1]) ++ Imp A1_1 (Imp A1_2 A2) :: Γ1).
     repeat rewrite <- app_assoc ; auto. rewrite H2. apply ImpRRule_I.
     assert (J4: derrec_height x = derrec_height x). auto.
     pose (@ImpR_hpinv (derrec_height x) _ x J4 _ H1). destruct s. auto.
  + apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[((Γ0 ++ [Or A1_1 A1_2]) ++ Imp A1_1 A2 :: [] ++ Imp A1_2 A2 :: Γ1, A2)]). apply OrImpL.
     assert (Γ0 ++ Or A1_1 A1_2 :: Imp (Or A1_1 A1_2) A2 :: Γ1 = (Γ0 ++ [Or A1_1 A1_2]) ++ Imp (Or A1_1 A1_2) A2 :: [] ++ Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H0. apply OrImpLRule_I. apply dlCons. simpl. 2: apply dersrec_nil.
     subst. repeat rewrite <- app_assoc. simpl.
     apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ A1_1 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2);(Γ0 ++ A1_2 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2)]).
     apply OrL. apply OrLRule_I. apply dlCons. 2: apply dlCons. 3: apply dersrec_nil.
     assert (J1: weight_form (Imp A1_1 A2) < weight_form (Imp (Or A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form (Imp A1_1 A2) = weight_form (Imp A1_1 A2)). auto.
     pose (IH (weight_form (Imp A1_1 A2)) J1 (Imp A1_1 A2) Γ0 (Imp A1_2 A2 :: Γ1) J2).
     assert (ImpRRule [(Γ0 ++ A1_1 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2)] (Γ0 ++ Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, Imp A1_1 A2)).
     apply ImpRRule_I. assert (J3: derrec_height d = derrec_height d). auto.
     pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H). destruct s. clear l. auto.
     assert (J1: weight_form (Imp A1_2 A2) < weight_form (Imp (Or A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form (Imp A1_2 A2) = weight_form (Imp A1_2 A2)). auto.
     pose (IH (weight_form (Imp A1_2 A2)) J1 (Imp A1_2 A2) (Γ0 ++ [Imp A1_1 A2]) Γ1 J2). repeat rewrite <- app_assoc in d.
     simpl in d.
     assert (ImpRRule [(Γ0 ++ A1_2 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2)] (Γ0 ++ Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, Imp A1_2 A2)).
     apply ImpRRule_I. assert (J3: derrec_height d = derrec_height d). auto.
     pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H). destruct s. clear l. auto.
  + apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[((Γ0 ++ [Imp A1_1 A1_2]) ++ Imp A1_2 A2 :: Γ1, Imp A1_1 A1_2);((Γ0 ++ [Imp A1_1 A1_2]) ++ A2 :: Γ1, A2)]).
     apply ImpImpL.
     assert (Γ0 ++ Imp A1_1 A1_2 :: Imp (Imp A1_1 A1_2) A2 :: Γ1 = (Γ0 ++ [Imp A1_1 A1_2]) ++ Imp (Imp A1_1 A1_2) A2 :: Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H0. apply ImpImpLRule_I. repeat rewrite <- app_assoc. simpl. subst.
     apply dlCons. 2: apply dlCons. 3: apply dersrec_nil.
     assert (J1: weight_form (Imp A1_1 A1_2) < weight_form (Imp (Imp A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form (Imp A1_1 A1_2) = weight_form (Imp A1_1 A1_2)). auto.
     pose (IH (weight_form (Imp A1_1 A1_2)) J1 (Imp A1_1 A1_2) Γ0 (Imp A1_2 A2 :: Γ1) J2). auto.
     assert (J1: weight_form A2 < weight_form (Imp (Imp A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form A2 = weight_form A2). auto.
     pose (IH (weight_form A2) J1 A2 (Γ0 ++ [Imp A1_1 A1_2]) Γ1 J2). repeat rewrite <- app_assoc in d.
     simpl in d. auto.
  + apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
     (ps:=[(XBoxed_list ((top_boxes Γ0) ++ Box A1 :: (top_boxes Γ1)) ++ [Box A1], A1) ; (Γ0 ++ Box A1 :: A2 :: Γ1, A2)]).
     apply BoxImpL. assert (Γ0 ++ Box A1 :: A2 :: Γ1 = (Γ0 ++ [Box A1]) ++ A2 :: Γ1). rewrite <- app_assoc. auto. rewrite H0.
     assert (Γ0 ++ Box A1 :: Imp (Box A1) A2 :: Γ1 = (Γ0 ++ [Box A1]) ++ Imp (Box A1) A2 :: Γ1). rewrite <- app_assoc. auto. rewrite H1.
     apply BoxImpLRule_I.
     intro. intros. apply in_app_or in H2. destruct H2. apply (is_Boxed_list_top_boxes Γ0) in H2. auto. inversion H2.
     exists  A1. auto. apply (is_Boxed_list_top_boxes Γ1) in H3. auto. rewrite <- app_assoc. simpl.
     apply univ_gen_ext_combine. apply nobox_gen_ext_top_boxes. apply univ_gen_ext_cons. apply nobox_gen_ext_top_boxes.
     apply dlCons. rewrite XBox_app_distrib. simpl. assert (J1: (weight_form A1) < n). subst. simpl. lia.
     pose (IH _ J1 A1 (XBoxed_list (top_boxes Γ0)) (Box A1 :: XBoxed_list (top_boxes Γ1) ++ [Box A1])).
     rewrite <- app_assoc. apply d. auto. assert (J2: (weight_form A2) < n). subst ; simpl ; lia. apply dlCons.
     2: apply dersrec_nil. pose (IH _ J2 A2 (Γ0 ++ [Box A1]) Γ1). rewrite <- app_assoc in d. simpl in d. apply d ; auto.
- intros. assert (GLRRule [(XBoxed_list (top_boxes (Γ0 ++ Box A :: Γ1)) ++ [Box A], A)] (Γ0 ++ Box A :: Γ1, Box A)).
  apply GLRRule_I. apply is_Boxed_list_top_boxes. rewrite top_boxes_distr_app. simpl. apply univ_gen_ext_combine.
  apply nobox_gen_ext_top_boxes. apply univ_gen_ext_cons. apply nobox_gen_ext_top_boxes.
  rewrite top_boxes_distr_app in X. simpl in X. rewrite XBox_app_distrib in X. simpl in X.
  repeat rewrite <- app_assoc in X. simpl in X. assert (J: (weight_form A) < n). subst ; simpl ; lia.
  pose (IH _ J A (XBoxed_list (top_boxes Γ0)) (Box A :: XBoxed_list (top_boxes Γ1) ++ [Box A])).
  apply GLR in X.
  apply derI with (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
  (ps:=[(XBoxed_list (top_boxes Γ0) ++ A :: Box A :: XBoxed_list (top_boxes Γ1) ++ [Box A], A)]) ; auto.
  apply dlCons. 2: apply dersrec_nil. apply d ; auto.
Qed.


Lemma Id_all_form : forall (A : MPropF) Γ0 Γ1,
          derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: Γ1, A).
Proof.
intros.
pose (@Id_all_form0 (weight_form A) A Γ0 Γ1). apply d ; auto.
Qed.

Lemma ModusPonens : forall A B Γ0 Γ1 Γ2, derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: Γ1 ++ (Imp A B) :: Γ2, B).
Proof.
intros.
pose (Id_all_form (Imp A B) (Γ0 ++ Γ1) Γ2). rewrite <- app_assoc in d.
assert (ImpRRule [(Γ0 ++ A :: Γ1 ++ Imp A B :: Γ2, B)] (Γ0 ++ Γ1 ++ Imp A B :: Γ2, Imp A B)). apply ImpRRule_I.
assert (J3: derrec_height d = derrec_height d). auto.
pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H). destruct s. auto.
Qed.
