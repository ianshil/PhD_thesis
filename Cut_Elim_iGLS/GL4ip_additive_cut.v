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
Require Import PSGL4ip_termination_measure.
Require Import PSGL4ip_termination.
Require Import GL4ip_exch.
Require Import GL4ip_ctr.
Require Import GL4ip_Id.
Require Import GL4ip_wkn.
Require Import GL4ip_inv_ImpL_R.
Require Import GL4ip_inv_AndImpL.
Require Import GL4ip_inv_OrImpL.
Require Import GL4ip_inv_AndR_AndL.
Require Import GL4ip_inv_AtomImpL.
Require Import GL4ip_inv_ImpImpL_R.
Require Import GL4ip_inv_ImpImpL_L.
Require Import GL4ip_inv_ImpR.
Require Import GL4ip_inv_OrL.
Require Import GL4ip_PSGL4ip_remove_list.
Require Import GL4ip_PSGL4ip_dec.
Require Import Lia.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Theorem GL4ip_cut_adm_main : forall n k A s Γ0 Γ1 C,
                      (n = weight_form A) ->
                      (k = mhd s) ->
                      (s = (Γ0 ++ Γ1, C)) ->
                      (derrec GL4ip_rules (fun _ => False) (Γ0 ++ Γ1, A)) ->
                      (derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)) ->
                      (derrec GL4ip_rules (fun _ => False) s).
Proof.
(* The proof is by induction on, first, size_form of the cut formula and on, second, the mhd
   of the sequent-conclusion. *)
(* We set up the strong induction on n properly first. *)
pose (strong_inductionT (fun (x:nat) => forall k A s Γ0 Γ1 C,
                      x = weight_form A ->
                      (k = mhd s) ->
                      (s = (Γ0 ++ Γ1, C)) ->
                      ((derrec GL4ip_rules (fun _ => False) (Γ0 ++ Γ1, A)) ->
                      (derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)) ->
                      (derrec GL4ip_rules (fun _ => False) s)))).
apply d. clear d. intros n PIH.
pose (strong_inductionT (fun (x:nat) => forall A s Γ0 Γ1 C,
                      n = weight_form A ->
                      (x = mhd s) ->
                      (s = (Γ0 ++ Γ1, C)) ->
                      ((derrec GL4ip_rules (fun _ => False) (Γ0 ++ Γ1, A)) ->
                      (derrec GL4ip_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)) ->
                      (derrec GL4ip_rules (fun _ => False) s)))).
apply d. clear d. intros k SIH.

(* Now we do the actual proof-theoretical work. *)
assert (DersNilF: dersrec GL4ip_rules (fun _ : Seq   => False) []).
apply dersrec_nil.
assert (DersNilT: dersrec GL4ip_rules (fun _ : Seq => True) []).
apply dersrec_nil.

intros A s Γ0 Γ1 C size MHD E D0 D1.

inversion D0. inversion H.
inversion D1. inversion H0.

(* Is the conclusion of the cut an initial sequent? *)
destruct (dec_init_rules s).

(* Yes. *)
{ destruct s0. inversion i. subst. apply Id_all_form. inversion b. subst. apply derI with (ps:=[]).
  apply BotL. apply BotLRule_I. auto. }

(* No. *)
{ inversion X ; subst.

(* Left rule is IdP *)
- inversion H1. subst.
  assert (J5 : list_exch_L (Γ0 ++ # P :: Γ1,C) (# P :: Γ2 ++ # P :: Γ3, C)).
  assert (Γ0 ++ # P :: Γ1 = [] ++ [] ++ Γ0 ++ [# P] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (# P :: Γ2 ++ # P :: Γ3 = [] ++ [# P] ++ Γ0 ++ [] ++ Γ1). simpl. rewrite <- H2. reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J5).
  assert (J0 : ctr_L (# P) (# P :: Γ2 ++ # P :: Γ3, C) (# P :: Γ2 ++ Γ3, C)).
  assert (# P :: Γ2 ++ # P :: Γ3 = [] ++ # P :: Γ2 ++ # P :: Γ3). reflexivity. rewrite H. clear H.
  assert (# P :: Γ2 ++ Γ3 = [] ++ # P :: Γ2 ++ Γ3). simpl. reflexivity. rewrite H. clear H.
  apply ctr_LI. pose (GL4ip_adm_ctr_L d J0).
  assert (J1 : list_exch_L (# P :: Γ2 ++ Γ3, C) (Γ2 ++ # P :: Γ3, C)).
  assert (# P :: Γ2 ++ Γ3 = [] ++ [# P] ++ Γ2 ++ [] ++ Γ3). reflexivity. rewrite H. clear H.
  assert (Γ2 ++ # P :: Γ3 = [] ++ [] ++ Γ2 ++ [# P] ++ Γ3). simpl. reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ d0 _ J1). assumption.

(* Left rule is BotL *)
- inversion H1. subst. assert (BotLRule [] (Γ2 ++ ⊥ :: Γ3, C)).
  apply BotLRule_I. apply BotL in H.
  pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
  (ps:=[]) (Γ2 ++ ⊥ :: Γ3, C) H DersNilF). assumption.

(* Left rule is AndR *)
- inversion H1. subst.
  assert (J0: AndLRule [(Γ0 ++ A0 :: B :: Γ1, C)] (Γ0 ++ A0 ∧ B :: Γ1, C)). apply AndLRule_I.
  pose (AndL_inv (Γ0 ++ A0 ∧ B :: Γ1, C) (Γ0 ++ A0 :: B :: Γ1, C) D1 J0).
  inversion X0. subst. inversion X4. subst. clear X6. clear X4.
  assert (J1: wkn_L B (Γ0 ++ Γ1, A0) (Γ0 ++B :: Γ1, A0)). apply wkn_LI.
  pose (GL4ip_adm_wkn_L X3 J1).
  assert (J2: weight_form A0 < weight_form (A0 ∧ B)). simpl. lia.
  assert (J3: weight_form A0 = weight_form A0). auto.
  assert (J4: mhd (Γ0 ++ B :: Γ1, C) = mhd (Γ0 ++ B :: Γ1, C)). auto.
  assert (J5: (Γ0 ++ B :: Γ1, C) = (Γ0 ++ B :: Γ1, C)). auto.
  pose (PIH _ J2 (mhd (Γ0 ++ B :: Γ1, C)) A0 (Γ0 ++ B :: Γ1, C) Γ0 (B :: Γ1) C J3 J4 J5 d0 d).
  assert (J6: weight_form B < weight_form (A0 ∧ B)). simpl. lia.
  assert (J7: weight_form B = weight_form B). auto.
  assert (J8: mhd (Γ0 ++ Γ1, C) = mhd (Γ0 ++ Γ1, C)). auto.
  assert (J9: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
  pose (PIH _ J6 (mhd (Γ0 ++ Γ1, C)) B (Γ0 ++ Γ1, C) Γ0 Γ1 C J7 J8 J9 X5 d1). assumption.

(* Left rule is AndL *)
- inversion H1. subst. inversion X0. subst. clear X4. clear X2.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H2 in d.
  assert (J0: AndLRule [((A :: Γ2) ++ A0 :: B :: Γ3, C)] ((A :: Γ2) ++ A0 ∧ B :: Γ3, C)). apply AndLRule_I.
  repeat rewrite <- app_assoc in J0. simpl in J0.
  pose (AndL_inv (A :: Γ2 ++ A0 ∧ B :: Γ3, C) (A :: Γ2 ++ A0 :: B :: Γ3, C) d J0).
  assert (J1: AndLRule  [(Γ2 ++ A0 :: B :: Γ3, C)] (Γ2 ++ A0 ∧ B :: Γ3, C)). apply AndLRule_I. apply PSAndL in J1.
  assert (J2: In (Γ2 ++ A0 :: B :: Γ3, C) [(Γ2 ++ A0 :: B :: Γ3, C)]). apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H2 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd (Γ2 ++ A0 :: B :: Γ3, C) = mhd (Γ2 ++ A0 :: B :: Γ3, C)). auto.
  assert (J5: (Γ2 ++ A0 :: B :: Γ3, C) = ([] ++ Γ2 ++ A0 :: B :: Γ3, C)). auto.
  pose (@SIH (mhd (Γ2 ++ A0 :: B :: Γ3, C)) l A (Γ2 ++ A0 :: B :: Γ3, C) [] (Γ2 ++ A0 :: B :: Γ3) C J3 J4 J5). simpl in d1.
  pose (d1 X3 d0). apply derI with (ps:=[(Γ2 ++ A0 :: B :: Γ3, C)]). apply AndL. apply AndLRule_I.
  apply dlCons ; auto. rewrite <- H2 in f. auto. rewrite <- H2 in f. auto.

(* Left rule is OrR1 *)
- inversion H1. subst.
  assert (J0: OrLRule [(Γ0 ++ A0 :: Γ1, C);(Γ0 ++ B :: Γ1, C)] (Γ0 ++ A0 ∨ B :: Γ1, C)). apply OrLRule_I.
  pose (OrL_inv (Γ0 ++ A0 ∨ B :: Γ1, C) (Γ0 ++ A0 :: Γ1, C) (Γ0 ++ B :: Γ1, C) D1 J0). destruct p.
  inversion X0. subst. clear X4. clear X0.
  assert (J2: weight_form A0 < weight_form (A0 ∨ B)). simpl. lia.
  assert (J3: weight_form A0 = weight_form A0). auto.
  assert (J4: mhd (Γ0 ++ Γ1, C) = mhd (Γ0 ++ Γ1, C)). auto.
  assert (J5: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
  pose (PIH _ J2 (mhd (Γ0 ++ Γ1, C)) A0 (Γ0 ++ Γ1, C) Γ0 Γ1 C J3 J4 J5 X3 d). auto.

(* Left rule is OrR2 *)
- inversion H1. subst.
  assert (J0: OrLRule [(Γ0 ++ A0 :: Γ1, C);(Γ0 ++ B :: Γ1, C)] (Γ0 ++ A0 ∨ B :: Γ1, C)). apply OrLRule_I.
  pose (OrL_inv (Γ0 ++ A0 ∨ B :: Γ1, C) (Γ0 ++ A0 :: Γ1, C) (Γ0 ++ B :: Γ1, C) D1 J0). destruct p.
  inversion X0. subst. clear X4. clear X0.
  assert (J2: weight_form B < weight_form (A0 ∨ B)). simpl. lia.
  assert (J3: weight_form B = weight_form B). auto.
  assert (J4: mhd (Γ0 ++ Γ1, C) = mhd (Γ0 ++ Γ1, C)). auto.
  assert (J5: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
  pose (PIH _ J2 (mhd (Γ0 ++ Γ1, C)) B (Γ0 ++ Γ1, C) Γ0 Γ1 C J3 J4 J5 X3 d0). auto.

(* Left rule is OrL *)
- inversion H1. subst. inversion X0. subst. inversion X4. subst. clear X6. clear X4. clear X0. clear X2.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H2 in d.
  assert (J0: OrLRule [((A :: Γ2) ++ A0 :: Γ3, C);((A :: Γ2) ++ B :: Γ3, C)] ((A :: Γ2) ++ A0 ∨ B :: Γ3, C)). apply OrLRule_I.
  repeat rewrite <- app_assoc in J0. simpl in J0.
  pose (OrL_inv (A :: Γ2 ++ A0 ∨ B :: Γ3, C) (A :: Γ2 ++ A0 :: Γ3, C) (A :: Γ2 ++  B :: Γ3, C) d J0). destruct p.
  assert (J1: OrLRule  [(Γ2 ++ A0 :: Γ3, C);(Γ2 ++ B :: Γ3, C)] (Γ2 ++ A0 ∨ B :: Γ3, C)). apply OrLRule_I. apply PSOrL in J1.
  assert (J2: In (Γ2 ++ A0 :: Γ3, C) [(Γ2 ++ A0 :: Γ3, C); (Γ2 ++ B :: Γ3, C)]). apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H2 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd (Γ2 ++ A0 :: Γ3, C) = mhd (Γ2 ++ A0 :: Γ3, C)). auto.
  assert (J5: (Γ2 ++ A0 :: Γ3, C) = ([] ++ Γ2 ++ A0 :: Γ3, C)). auto.
  pose (@SIH (mhd (Γ2 ++ A0 :: Γ3, C)) l A (Γ2 ++ A0 :: Γ3, C) [] (Γ2 ++ A0 :: Γ3) C J3 J4 J5). simpl in d2.
  pose (d2 X3 d0).
  assert (J6: In (Γ2 ++ B :: Γ3, C) [(Γ2 ++ A0 :: Γ3, C); (Γ2 ++ B :: Γ3, C)]). apply in_cons. apply in_eq.
  pose (RA_mhd_decreases J1 _ J6).
  assert (J7: weight_form A = weight_form A). auto.
  assert (J8: mhd (Γ2 ++ B :: Γ3, C) = mhd (Γ2 ++ B :: Γ3, C)). auto.
  assert (J9: (Γ2 ++ B :: Γ3, C) = ([] ++ Γ2 ++ B :: Γ3, C)). auto.
  pose (@SIH (mhd (Γ2 ++ B :: Γ3, C)) l0 A (Γ2 ++ B :: Γ3, C) [] (Γ2 ++ B :: Γ3) C J7 J8 J9). simpl in d4.
  pose (d4 X5 d1). apply derI with (ps:=[(Γ2 ++ A0 :: Γ3, C); (Γ2 ++ B :: Γ3, C)]). apply OrL. apply OrLRule_I.
  apply dlCons ; auto. apply dlCons ; auto. rewrite <- H2 in f. auto. rewrite <- H2 in f. auto.

(* Left rule is ImpR *)
- inversion H1. subst. inversion X0. subst. clear X4. clear X0. inversion X1. simpl.
      (* Right rule is IdP *)
      { inversion H. subst. assert (J0 : InT (# P) (Γ0 ++ (A0 → B) :: Γ1)). rewrite <- H6. apply InT_or_app.
        right. apply InT_eq. apply InT_app_or in J0. destruct J0.
        - apply InT_split in i. destruct i. destruct s. subst. rewrite H2. rewrite <- app_assoc.
          assert (IdPRule [] (x ++ (# P :: x0) ++ Γ1, # P)). apply IdPRule_I. apply IdP in H0.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) (x ++ (# P :: x0) ++ Γ1,# P) H0 DersNilF). assumption.
        - inversion i.
          * inversion H3.
          * apply InT_split in H3. destruct H3. destruct s. subst. rewrite H2. rewrite app_assoc.
            assert (IdPRule [] ((Γ0 ++ x) ++ # P :: x0, # P)). apply IdPRule_I. apply IdP in H0.
            pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) ((Γ0 ++ x) ++ # P :: x0, # P) H0 DersNilF). assumption. }
      (* Right rule is BotL *)
      { inversion H. subst. rewrite H2. assert (J0 : InT (⊥) (Γ0 ++ (A0 → B) :: Γ1)). rewrite <- H6. apply InT_or_app.
        right. apply InT_eq. apply InT_app_or in J0. destruct J0.
        - apply InT_split in i. destruct i. destruct s. subst. rewrite <- app_assoc.
          assert (BotLRule [] (x ++ (⊥ :: x0) ++ Γ1, C)). apply BotLRule_I. apply BotL in H0.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) (x ++ (⊥ :: x0) ++ Γ1, C) H0 DersNilF). assumption.
        - inversion i.
          * inversion H3.
          * apply InT_split in H3. destruct H3. destruct s. subst. rewrite app_assoc.
            assert (BotLRule [] ((Γ0 ++ x) ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H0.
            pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) ((Γ0 ++ x) ++ ⊥ :: x0, C) H0 DersNilF). assumption. }
    (* Right rule is AndR *)
    { inversion H. subst. inversion X2. subst. inversion X4. subst. rewrite H2. clear X6. clear X4.
      assert (AndRRule [(Γ0 ++ Γ1, A);(Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A ∧ B0)). apply AndRRule_I.
      assert (J3: PSGL4ip_rules [(Γ0 ++ Γ1, A);(Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A ∧ B0)).
      apply PSAndR ; try intro ; try apply f ; try auto ; try assumption. apply AndR in H0.
      assert (J21: In  (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B0)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J6: mhd (Γ0 ++ Γ1, A) = mhd (Γ0 ++ Γ1, A)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity.
      pose (@SIH (mhd (Γ0 ++ Γ1, A)) l (A0 → B) (Γ0 ++ Γ1, A)
      Γ0 Γ1 A J5 J6 J7 D0 X0).
      assert (J31: In  (Γ0 ++ Γ1, B0) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B0)]). apply in_cons. apply in_eq.
      pose (RA_mhd_decreases J3 _ J31).
      assert (J9: mhd (Γ0 ++ Γ1, B0) = mhd (Γ0 ++ Γ1, B0)). reflexivity.
      assert (J10 : (Γ0 ++ Γ1, B0) = (Γ0 ++ Γ1, B0)). reflexivity.
      pose (@SIH (mhd (Γ0 ++ Γ1, B0)) l0 (A0 → B) (Γ0 ++ Γ1, B0)
      Γ0 Γ1 B0 J5 J9 J10 D0 X5). apply derI with (ps:=[(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B0)]).
      apply AndR. apply AndRRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is AndL *)
    { inversion H. subst. inversion X2. subst. clear X4. clear X2. apply list_split_form in H6. destruct H6 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst. rewrite H2.
         assert (AndLRule [((Γ0 ++ x0) ++ A :: B0 :: Γ5, C)] ((Γ0 ++ x0) ++ A ∧ B0 :: Γ5, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules  [(Γ0 ++ x0 ++ A :: B0 :: Γ5, C)] (Γ0 ++ x0 ++ A ∧ B0 :: Γ5, C)).
        apply PSAndL ; try intro ; try apply f ; try auto ; try assumption. apply AndL in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A :: B0 :: Γ5, C) [(Γ0 ++ x0 ++ A :: B0 :: Γ5, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A :: B0 :: Γ5, C) = mhd (Γ0 ++ x0 ++ A :: B0 :: Γ5, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: B0 :: Γ5, C) = (Γ0 ++ x0 ++ A :: B0 :: Γ5, C)). reflexivity.
        assert (J01: AndLRule [((Γ0 ++ x0) ++ A :: B0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ A ∧ B0 :: Γ5, A0 → B)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in X0.
        pose (AndL_inv(Γ0 ++ x0 ++ A ∧ B0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ A :: B0 :: Γ5, A0 → B) D0 J01).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A :: B0 :: Γ5, C)) l (A0 → B) (Γ0 ++ x0 ++ A :: B0 :: Γ5, C)
        Γ0 (x0 ++ A :: B0 :: Γ5) C J5 J6 J7 d X0). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: B0 :: Γ5, C)]).
        apply AndL. assert (Γ0 ++ x0 ++ A :: B0 :: Γ5 = (Γ0 ++ x0) ++ A :: B0 :: Γ5). rewrite <- app_assoc. auto.
        rewrite H3. assert (Γ0 ++ x0 ++ A ∧ B0 :: Γ5 = (Γ0 ++ x0) ++ A ∧ B0 :: Γ5).  rewrite <- app_assoc. auto.
        rewrite H4. apply AndLRule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. rewrite H2.
        assert (AndLRule [(Γ4 ++ A :: B0 :: x ++ Γ1, C)] (Γ4 ++ A ∧ B0 :: x ++ Γ1, C)). apply AndLRule_I.
        assert (J3: PSGL4ip_rules  [(Γ4 ++ A :: B0 :: x ++ Γ1, C)] (Γ4 ++ A ∧ B0 :: x ++ Γ1, C)).
        apply PSAndL ; try intro ; try apply f ; try auto ; try assumption. apply AndL in H0.
        assert (J21: In  (Γ4 ++ A :: B0 :: x ++ Γ1, C) [(Γ4 ++ A :: B0 :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ4 ++ A :: B0 :: x ++ Γ1, C) = mhd (Γ4 ++ A :: B0 :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ4 ++ A :: B0 :: x ++ Γ1, C) = (Γ4 ++ A :: B0 :: x ++ Γ1, C)). reflexivity.
        repeat rewrite <- app_assoc in X0. simpl in X0. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndLRule [(Γ4 ++ A :: B0 :: x ++ Γ1, A0 → B)] (Γ4 ++ A ∧ B0 :: x ++ Γ1, A0 → B)). apply AndLRule_I.
        pose (AndL_inv (Γ4 ++ A ∧ B0 :: x ++ Γ1, A0 → B) (Γ4 ++ A :: B0 :: x ++ Γ1, A0 → B) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ4 ++ A :: B0 :: x ++ Γ1, C)) l (A0 → B) (Γ4 ++ A :: B0 :: x ++ Γ1, C)
        (Γ4 ++ A :: B0 :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d0. 
        pose (d0 J7 d X0). apply derI with (ps:=[(Γ4 ++ A :: B0 :: x ++ Γ1, C)]).
        apply AndL. repeat rewrite <- app_assoc. apply AndLRule_I. apply dlCons ; auto. }
    (* Right rule is OrR1 *)
    { inversion H. subst. inversion X2. subst. clear X4. clear X2.
      assert (OrR1Rule [(Γ0 ++ Γ1, A)] (Γ0 ++ Γ1, A ∨ B0)). apply OrR1Rule_I.
      assert (J3: PSGL4ip_rules [(Γ0 ++ Γ1, A)] (Γ0 ++ Γ1, A ∨ B0)).
      apply PSOrR1 ; try intro ; try apply f ; try auto ; try assumption. apply OrR1 in H0.
      assert (J21: In  (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J6: mhd (Γ0 ++ Γ1, A) = mhd (Γ0 ++ Γ1, A)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity.
      pose (@SIH (mhd (Γ0 ++ Γ1, A)) l (A0 → B) (Γ0 ++ Γ1, A)
      Γ0 Γ1 A J5 J6 J7 D0 X0). apply derI with (ps:=[(Γ0 ++ Γ1, A)]).
      apply OrR1. rewrite H2. apply OrR1Rule_I. apply dlCons ; auto. }
    (* Right rule is OrR2 *)
    { inversion H. subst. inversion X2. subst. clear X4. clear X2.
      assert (OrR2Rule [(Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A ∨ B0)). apply OrR2Rule_I.
      assert (J3: PSGL4ip_rules [(Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A ∨ B0)).
      apply PSOrR2 ; try intro ; try apply f ; try auto ; try assumption. apply OrR2 in H0.
      assert (J21: In  (Γ0 ++ Γ1, B0) [(Γ0 ++ Γ1, B0)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J6: mhd (Γ0 ++ Γ1, B0) = mhd (Γ0 ++ Γ1, B0)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, B0) = (Γ0 ++ Γ1, B0)). reflexivity. rewrite H2.
      pose (@SIH (mhd (Γ0 ++ Γ1, B0)) l (A0 → B) (Γ0 ++ Γ1, B0)
      Γ0 Γ1 B0 J5 J6 J7 D0 X0). apply derI with (ps:=[(Γ0 ++ Γ1, B0)]).
      apply OrR2. apply OrR2Rule_I. apply dlCons ; auto. }
    (* Right rule is OrL *)
    { inversion H. subst. inversion X2. subst. inversion X4. subst. clear X6. clear X4. clear X2.
      rewrite H2. apply list_split_form in H6. destruct H6 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (OrLRule [((Γ0 ++ x0) ++ A :: Γ5, C);((Γ0 ++ x0) ++ B0 :: Γ5, C)] ((Γ0 ++ x0) ++ A ∨ B0 :: Γ5, C)). apply OrLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ A :: Γ5, C); (Γ0 ++ x0 ++ B0 :: Γ5, C)] (Γ0 ++ x0 ++ A ∨ B0 :: Γ5, C)).
        apply PSOrL ; try intro ; try apply f ; try auto ; try assumption. apply OrL in H0.
        repeat rewrite <- app_assoc in X5. simpl in X5. repeat rewrite <- app_assoc in X0. simpl in X0.
        assert (J01: OrLRule [((Γ0 ++ x0) ++ A :: Γ5, A0 → B);((Γ0 ++ x0) ++ B0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ A ∨ B0 :: Γ5, A0 → B)). apply OrLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrL_inv (Γ0 ++ x0 ++ A ∨ B0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ A :: Γ5, A0 → B) (Γ0 ++ x0 ++ B0 :: Γ5, A0 → B) D0 J01).
        destruct p.
        assert (J21: In (Γ0 ++ x0 ++ A :: Γ5, C) [(Γ0 ++ x0 ++ A :: Γ5, C); (Γ0 ++ x0 ++ B0 :: Γ5, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A :: Γ5, C) = mhd (Γ0 ++ x0 ++ A :: Γ5, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ5, C) = (Γ0 ++ x0 ++ A :: Γ5, C)). reflexivity.
        pose (@SIH (mhd (Γ0 ++ x0 ++ A :: Γ5, C)) l (A0 → B) (Γ0 ++ x0 ++ A :: Γ5, C)
        Γ0 (x0 ++ A :: Γ5) C J5 J6 J7 d X0).
        assert (J22: In (Γ0 ++ x0 ++ B0 :: Γ5, C) [(Γ0 ++ x0 ++ A :: Γ5, C); (Γ0 ++ x0 ++ B0 :: Γ5, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J9: mhd (Γ0 ++ x0 ++ B0 :: Γ5, C) = mhd (Γ0 ++ x0 ++ B0 :: Γ5, C)). reflexivity.
        assert (J10 : (Γ0 ++ x0 ++ B0 :: Γ5, C) = (Γ0 ++ x0 ++ B0 :: Γ5, C)). reflexivity.
        pose (@SIH (mhd (Γ0 ++ x0 ++ B0 :: Γ5, C)) l0 (A0 → B) (Γ0 ++ x0 ++ B0 :: Γ5, C)
        Γ0 (x0 ++ B0 :: Γ5) C J8 J9 J10 d0 X5).
        apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ5, C); (Γ0 ++ x0 ++ B0 :: Γ5, C)]).
        apply OrL. assert (Γ0 ++ x0 ++ A :: Γ5 = (Γ0 ++ x0) ++ A :: Γ5). rewrite <- app_assoc. auto.
        rewrite H3. assert (Γ0 ++ x0 ++ A ∨ B0 :: Γ5 = (Γ0 ++ x0) ++ A ∨ B0 :: Γ5).  rewrite <- app_assoc. auto.
        rewrite H4. assert (Γ0 ++ x0 ++ B0 :: Γ5 = (Γ0 ++ x0) ++ B0 :: Γ5). rewrite <- app_assoc. auto.
        rewrite H5. apply OrLRule_I. apply dlCons ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
        assert (OrLRule [(Γ4 ++ A :: x ++ Γ1, C);(Γ4 ++ B0 :: x ++ Γ1, C)] (Γ4 ++ A ∨ B0 :: x ++ Γ1, C)). apply OrLRule_I.
        assert (J3: PSGL4ip_rules [(Γ4 ++ A :: x ++ Γ1, C);(Γ4 ++ B0 :: x ++ Γ1, C)] (Γ4 ++ A ∨ B0 :: x ++ Γ1, C)).
        apply PSOrL ; try intro ; try apply f ; try auto ; try assumption. apply OrL in H0. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrLRule [(Γ4 ++ A :: x ++ Γ1, A0 → B);(Γ4 ++ B0 :: x ++ Γ1, A0 → B)] (Γ4 ++ A ∨ B0 :: x ++ Γ1, A0 → B)). apply OrLRule_I.
        pose (OrL_inv (Γ4 ++ A ∨ B0 :: x ++ Γ1, A0 → B) (Γ4 ++ A :: x ++ Γ1, A0 → B) (Γ4 ++ B0 :: x ++ Γ1, A0 → B) D0 J01).
        destruct p.
        assert (J21: In (Γ4 ++ A :: x ++ Γ1, C) [(Γ4 ++ A :: x ++ Γ1, C); (Γ4 ++ B0 :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ4 ++ A :: x ++ Γ1, C) = mhd (Γ4 ++ A :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ4 ++ A :: x ++ Γ1, C) = (Γ4 ++ A :: x ++ Γ1, C)). reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ4 ++ A :: x ++ Γ1, C)) l (A0 → B) (Γ4 ++ A :: x ++ Γ1, C)
        (Γ4 ++ A :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d1. pose (d1 J7 d X0).
        assert (J22: In  (Γ4 ++ B0 :: x ++ Γ1, C) [(Γ4 ++ A :: x ++ Γ1, C); (Γ4 ++ B0 :: x ++ Γ1, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J9: mhd (Γ4 ++ B0 :: x ++ Γ1, C) = mhd (Γ4 ++ B0 :: x ++ Γ1, C)). reflexivity.
        assert (J10 : (Γ4 ++ B0 :: x ++ Γ1, C) = (Γ4 ++ B0 :: x ++ Γ1, C)). reflexivity.
        pose (@SIH (mhd (Γ4 ++ B0 :: x ++ Γ1, C)) l0 (A0 → B) (Γ4 ++ B0 :: x ++ Γ1, C)
        (Γ4 ++ B0 :: x) Γ1 C J8 J9). repeat rewrite <- app_assoc in d3. pose (d3 J10 d0 X5).
        apply derI with (ps:=[(Γ4 ++ A :: x ++ Γ1, C); (Γ4 ++ B0 :: x ++ Γ1, C)]).
        apply OrL. apply OrLRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is ImpR *)
    { inversion H. subst. inversion X2. subst. clear X4. rewrite <- H6 in D1. rewrite H2.
      assert (J1 : list_exch_L (Γ4 ++ A :: Γ5, B0) (A :: Γ0 ++ A0 → B :: Γ1, B0)).
      assert (Γ4 ++ A :: Γ5 = [] ++ [] ++ Γ4 ++ [A] ++ Γ5). reflexivity. rewrite H0. clear H0.
      assert (A :: Γ0 ++ A0 → B :: Γ1 = [] ++ [A] ++ Γ4 ++ [] ++ Γ5). rewrite <- H6. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ X0 _ J1).
      assert (ImpRRule [([] ++ A :: Γ0 ++ Γ1, B0)] ([] ++ Γ0 ++ Γ1, A → B0)). apply ImpRRule_I.
      simpl in H0.
      assert (J3: PSGL4ip_rules [(A :: Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A → B0)).
      apply PSImpR ; try intro ; try apply f ; try rewrite <- H6 ; try auto ; try assumption.
      assert (J31: GL4ip_rules [(A :: Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A → B0)).
      apply ImpR ; try assumption.
      assert (J21: In (A :: Γ0 ++ Γ1, B0) [(A :: Γ0 ++ Γ1, B0)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J6: mhd (A :: Γ0 ++ Γ1, B0) = mhd (A :: Γ0 ++ Γ1, B0)). reflexivity.
      assert (J7 : (A :: Γ0 ++ Γ1, B0) = ((A :: Γ0) ++ Γ1, B0)). reflexivity.
      pose (@SIH (mhd (A :: Γ0 ++ Γ1, B0)) l (A0 → B) (A :: Γ0 ++ Γ1, B0)
      (A :: Γ0) Γ1 B0 J5 J6 J7). simpl in d0.
      assert (wkn_L A ([] ++ Γ0 ++ Γ1, A0 → B) ([] ++ A :: Γ0 ++ Γ1, A0 → B)). apply wkn_LI. simpl in H2.
      pose (@GL4ip_adm_wkn_L (Γ0 ++ Γ1, A0 → B) D0 (A :: Γ0 ++ Γ1, A0 → B) A H3).
      pose (d0 d1 d). pose (dlCons d2 DersNilF).
      apply ImpR in H0 ; try intro ; try apply f ; try rewrite <- H7 ; try auto ; try assumption.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(A :: Γ0 ++ Γ1, B0)]) (Γ0 ++ Γ1, A → B0) H0 d3). assumption. }
    (* Right rule is AtomImpL1 *)
    { inversion H. subst. inversion X2. subst. clear X4. clear X2. apply list_split_form in H6. destruct H6 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst. rewrite H2.
        assert (AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ5 ++ A :: Γ6, C)] ((Γ0 ++ x0) ++ # P :: Γ5 ++ # P → A :: Γ6, C)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)] (Γ0 ++ x0 ++ # P :: Γ5 ++ # P → A :: Γ6, C)).
        apply PSAtomImpL1 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL1 in H0.
        assert (J21: In  (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C) [(Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C) = mhd (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C) = (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)). reflexivity.
        repeat rewrite <- app_assoc in X0. simpl in X0.
        assert (J01: AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ5 ++ A :: Γ6,A0 → B)] ((Γ0 ++ x0) ++ # P :: Γ5 ++ # P → A :: Γ6, A0 → B)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0 ++ # P :: Γ5) Γ6 (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
        pose (d D0).
        pose (@SIH (mhd (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)) l (A0 → B) (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)
        Γ0 (x0 ++ # P :: Γ5 ++ A :: Γ6) C J5 J6 J7 d0 X0). apply derI with (ps:=[(Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)]).
        apply AtomImpL1. assert (Γ0 ++ x0 ++ # P :: Γ5 ++ # P → A :: Γ6 = (Γ0 ++ x0) ++ # P :: Γ5 ++ # P → A :: Γ6). rewrite <- app_assoc. auto.
        rewrite H3. assert (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6 = (Γ0 ++ x0) ++ # P :: Γ5 ++ A :: Γ6).  rewrite <- app_assoc. auto.
        rewrite H4. apply AtomImpL1Rule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. simpl in f. rewrite H2.
        apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0. subst.
           assert (J0: list_exch_L ([] ++ [] ++ Γ2 ++ [# P] ++ Γ3, B) ([] ++ [# P] ++ ((Γ4 ++ # P :: x) ++ Γ1), B)). rewrite <- H2.
           assert ([] ++ [# P] ++ Γ2 ++ Γ3 = [] ++ [# P] ++ Γ2 ++ [] ++ Γ3). auto. rewrite H0. apply list_exch_LI.
           simpl in J0.
           pose (GL4ip_adm_list_exch_L (Γ2 ++ # P :: Γ3, B) X3 (# P :: (Γ4 ++ # P :: x) ++ Γ1, B) J0).
           repeat rewrite <- app_assoc in d. simpl in d.
           assert (J1: ctr_L (# P) ([] ++ # P :: Γ4 ++ # P :: x ++ Γ1, B) ([] ++ # P :: Γ4 ++ x ++ Γ1, B)). apply ctr_LI. simpl in J1.
           pose (GL4ip_adm_ctr_L d J1).
           assert (J3: list_exch_L ([] ++ [# P] ++ Γ4 ++ [] ++ x ++ Γ1, B) ([] ++ [] ++ Γ4 ++ [# P] ++ x ++ Γ1, B)). apply list_exch_LI.
           simpl in J3. pose (GL4ip_adm_list_exch_L _ d0 _ J3). repeat rewrite <- app_assoc. simpl.
           assert (J4: weight_form B < weight_form (# P → B)). simpl ; lia.
           assert (J5: weight_form B = weight_form B). auto.
           assert (J6: mhd (Γ4 ++ # P :: x ++ Γ1, C) = mhd (Γ4 ++ # P :: x ++ Γ1, C)). auto.
           assert (J7: (Γ4 ++ # P :: x ++ Γ1, C) = (Γ4 ++ # P :: x ++ Γ1, C)). auto.
           pose (PIH (weight_form B) J4 (mhd (Γ4 ++ # P :: x ++ Γ1, C)) B (Γ4 ++ # P :: x ++ Γ1, C)
           (Γ4 ++ # P :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 J7 d1 X0). auto.
        +  repeat destruct s. repeat destruct p. subst.
            assert (AtomImpL1Rule [(Γ4 ++ # P :: (x ++ x1) ++ A :: Γ6, C)] (Γ4 ++ # P :: (x ++ x1) ++ # P → A :: Γ6, C)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in H0.
            assert (J3: PSGL4ip_rules [(Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)] (Γ4 ++ # P :: x ++ x1 ++ # P → A :: Γ6, C)).
            apply PSAtomImpL1 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL1 in H0.
            assert (J21: In  (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C) [(Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J6: mhd (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C) = mhd (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)). reflexivity.
            assert (J7 : (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C) = (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)). reflexivity.
            repeat rewrite <- app_assoc in X0. simpl in X0.
            assert (J01: AtomImpL1Rule [(Γ4 ++ # P :: (x ++ x1) ++ A :: Γ6, A0 → B)] (Γ4 ++ # P :: (x ++ x1) ++ # P → A :: Γ6, A0 → B)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ4 ++ # P :: x ++ x1) Γ6 (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)) l (A0 → B) (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)
            (Γ4 ++ # P :: x) (x1 ++ A :: Γ6) C J5 J6). repeat rewrite <- app_assoc in d1. pose (d1 J7 d0 X0).
            apply derI with (ps:=[(Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)]). apply AtomImpL1. repeat rewrite <- app_assoc. simpl.
            assert (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6 = Γ4 ++ # P :: (x ++ x1) ++ A :: Γ6). rewrite <- app_assoc. auto.
            rewrite H3. assert (Γ4 ++ # P :: x ++ x1 ++ # P → A :: Γ6 = Γ4 ++ # P :: (x ++ x1) ++ # P → A :: Γ6).  rewrite <- app_assoc. auto.
            rewrite H4. apply AtomImpL1Rule_I. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. repeat rewrite <- app_assoc. simpl.
            assert (AtomImpL1Rule [(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)] (Γ4 ++ # P :: Γ5 ++ # P → A :: x0 ++ Γ1, C)). apply AtomImpL1Rule_I.
            assert (J3: PSGL4ip_rules [(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)] (Γ4 ++ # P :: Γ5 ++ # P → A :: x0 ++ Γ1, C)).
            apply PSAtomImpL1 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL1 in H0.
            assert (J21: In  (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C) [(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J6: mhd (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C) = mhd (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)). reflexivity.
            assert (J7 : (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C) = (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)). reflexivity.
            assert (J01: AtomImpL1Rule [(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, A0 → B)] (Γ4 ++ # P :: Γ5 ++ # P → A :: x0 ++ Γ1, A0 → B)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ4 ++ # P :: Γ5) (x0 ++ Γ1) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)) l (A0 → B) (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)
            (Γ4 ++ # P :: Γ5 ++ A :: x0) Γ1 C J5 J6). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 J7 d0 X0).
            apply derI with (ps:=[(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)]). apply AtomImpL1. apply AtomImpL1Rule_I. apply dlCons ; auto. }
    (* Right rule is AtomImpL2 *)
    { inversion H. subst. inversion X2. subst. clear X4. clear X2. apply list_split_form in H6. destruct H6 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H2.
        assert (J0: list_exch_L ([] ++ [] ++ Γ2 ++ [# P] ++ Γ3, B) ([] ++ [# P] ++ (Γ0 ++ Γ5 ++ # P :: Γ6), B)). rewrite <- H2.
        assert ([] ++ [# P] ++ Γ2 ++ Γ3 = [] ++ [# P] ++ Γ2 ++ [] ++ Γ3). auto. rewrite H0. apply list_exch_LI.
        simpl in J0.
        pose (GL4ip_adm_list_exch_L (Γ2 ++ # P :: Γ3, B) X3 (# P :: Γ0 ++ Γ5 ++ # P :: Γ6, B) J0).
        repeat rewrite <- app_assoc in d. simpl in d.
        assert (J1: ctr_L (# P) ([] ++ # P :: (Γ0 ++ Γ5) ++ # P :: Γ6, B) ([] ++ # P :: (Γ0 ++ Γ5) ++ Γ6, B)). apply ctr_LI. simpl in J1.
        repeat rewrite <- app_assoc in J1. pose (GL4ip_adm_ctr_L d J1).
        assert (J3: list_exch_L ([] ++ [# P] ++ (Γ0 ++ Γ5) ++ [] ++ Γ6, B) ([] ++ [] ++ (Γ0 ++ Γ5) ++ [# P] ++ Γ6, B)). apply list_exch_LI.
        simpl in J3. repeat rewrite <- app_assoc in J3. pose (GL4ip_adm_list_exch_L _ d0 _ J3). repeat rewrite <- app_assoc. simpl.
        assert (J4: weight_form B < weight_form (# P → B)). simpl ; lia.
        assert (J5: weight_form B = weight_form B). auto.
        assert (J6: mhd (Γ0 ++ Γ5 ++ # P :: Γ6, C) = mhd (Γ0 ++ Γ5 ++ # P :: Γ6, C)). auto.
        assert (J7:(Γ0 ++ Γ5 ++ # P :: Γ6, C) = (Γ0 ++ Γ5 ++ # P :: Γ6, C)). auto.
        pose (PIH (weight_form B) J4 (mhd (Γ0 ++ Γ5 ++ # P :: Γ6, C)) B (Γ0 ++ Γ5 ++ # P :: Γ6, C)
        Γ0 (Γ5 ++ # P :: Γ6) C J5 J6). repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 J7 d1 X0). auto.
      - repeat destruct s. repeat destruct p. subst.
        assert (AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ6, C)] ((Γ0 ++ x0) ++ # P → A :: Γ5 ++ # P :: Γ6, C)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in H0. rewrite H2.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)] (Γ0 ++ x0 ++ # P → A :: Γ5 ++ # P :: Γ6, C)).
        apply PSAtomImpL2 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL2 in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C) [(Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C) = mhd (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C) = (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)). reflexivity.
        repeat rewrite <- app_assoc in X0. simpl in X0.
        assert (J01: AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ6,A0 → B)] ((Γ0 ++ x0) ++ # P → A :: Γ5 ++ # P :: Γ6, A0 → B)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0) (Γ5 ++ # P :: Γ6) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
        pose (d D0).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)) l (A0 → B) (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)
        Γ0  (x0 ++ A :: Γ5 ++ # P :: Γ6) C J5 J6 J7 d0 X0). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)]).
        apply AtomImpL2. assert (Γ0 ++ x0 ++ # P → A :: Γ5 ++ # P :: Γ6 = (Γ0 ++ x0) ++ # P → A :: Γ5 ++ # P :: Γ6). rewrite <- app_assoc. auto.
        rewrite H3. assert (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6 = (Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ6).  rewrite <- app_assoc. auto.
        rewrite H4. apply AtomImpL2Rule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. simpl in f.
        apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0.
        +  repeat destruct s. repeat destruct p. subst. rewrite H2.
            assert (AtomImpL2Rule [(Γ4 ++ A :: (x ++ x1) ++ # P :: Γ6, C)] (Γ4 ++ # P → A :: (x ++ x1) ++ # P :: Γ6, C)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in H0.
            assert (J3: PSGL4ip_rules [(Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)] (Γ4 ++ # P → A :: x ++ x1 ++ # P :: Γ6, C)).
            apply PSAtomImpL2 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL2 in H0.
            assert (J21: In  (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C) [(Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J6: mhd (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C) = mhd (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)). reflexivity.
            assert (J7 : (Γ4 ++  A :: x ++ x1 ++ # P :: Γ6, C) = (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)). reflexivity.
            repeat rewrite <- app_assoc in X0. simpl in X0.
            assert (J01: AtomImpL2Rule [(Γ4 ++ A :: (x ++ x1) ++ # P :: Γ6, A0 → B)] (Γ4 ++ # P → A :: (x ++ x1) ++ # P :: Γ6, A0 → B)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ4 (x ++ x1 ++ # P :: Γ6) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)) l (A0 → B) (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)
            (Γ4 ++ A :: x) (x1 ++ # P :: Γ6) C J5 J6). repeat rewrite <- app_assoc in d1. pose (d1 J7 d0 X0).
            apply derI with (ps:=[(Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)]). apply AtomImpL2. repeat rewrite <- app_assoc. simpl.
            assert (Γ4 ++ # P → A :: x ++ x1 ++ # P :: Γ6 = Γ4 ++ # P → A :: (x ++ x1) ++ # P :: Γ6). rewrite <- app_assoc. auto.
            rewrite H3. assert (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6 = Γ4 ++ A :: (x ++ x1) ++ # P :: Γ6).  rewrite <- app_assoc. auto.
            rewrite H4. apply AtomImpL2Rule_I. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. rewrite H2.
            assert (AtomImpL2Rule [(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)] (Γ4 ++ # P → A :: Γ5 ++ # P :: x0 ++ Γ1, C)). apply AtomImpL2Rule_I.
            assert (J3: PSGL4ip_rules [(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)] (Γ4 ++ # P → A :: Γ5 ++ # P :: x0 ++ Γ1, C)).
            apply PSAtomImpL2 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL2 in H0.
            assert (J21: In  (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C) [(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J6: mhd (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C) = mhd (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)). reflexivity.
            assert (J7 : (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C) = (Γ4 ++  A :: Γ5 ++ # P :: x0 ++ Γ1, C)). reflexivity.
            assert (J01: AtomImpL2Rule [(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, A0 → B)] (Γ4 ++ # P → A :: Γ5 ++ # P :: x0 ++ Γ1, A0 → B)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ4 (Γ5 ++  # P :: x0 ++ Γ1) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)) l (A0 → B) (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)
            (Γ4 ++ A :: Γ5 ++ # P :: x0) Γ1 C J5 J6). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 J7 d0 X0).
            apply derI with (ps:=[(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)]). apply AtomImpL2. repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc. apply AtomImpL2Rule_I. apply dlCons ; auto. }
    (* Right rule is AndImpL *)
    { inversion H. subst. inversion X2. subst. clear X4. clear X2. apply list_split_form in H6. destruct H6 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H2.
        assert (J0: list_exch_L ([] ++ [] ++ Γ2 ++ [A ∧ B0] ++ Γ3, B) ([] ++ [A ∧ B0] ++ Γ0 ++ Γ1, B)). rewrite <- H2.
        assert (Γ2 ++ Γ3 =Γ2 ++ [] ++ Γ3). auto. rewrite H0. apply list_exch_LI. simpl in J0.
        pose (GL4ip_adm_list_exch_L _ X3 _ J0).
        assert (J1: AndLRule [([] ++ A :: B0 :: Γ0 ++ Γ1, B)] ([] ++ A ∧ B0 :: Γ0 ++ Γ1, B)). apply AndLRule_I. simpl in J1.
        pose (AndL_inv _ _ d J1).
        assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ1, A → B0 → B)).
        apply derI with (ps:=[([] ++ A :: Γ0 ++ Γ1, B0 → B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto.
        simpl. apply derI with (ps:=[([A] ++ B0 :: Γ0 ++ Γ1, B)]). apply ImpR. assert (A :: Γ0 ++ Γ1 = [A] ++ Γ0 ++ Γ1). auto.
        rewrite H0. apply ImpRRule_I. simpl. apply dlCons ; auto. simpl in X2.
        assert (J2: weight_form (A → B0 → B) < weight_form ((A ∧ B0) → B)). simpl. lia.
        assert (J3: weight_form (A → B0 → B) = weight_form (A → B0 → B)). auto.
        assert (J4: mhd (Γ0 ++ Γ1, C) = mhd (Γ0 ++ Γ1, C)). auto.
        assert (J5: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
        pose (PIH (weight_form (A → B0 → B)) J2 (mhd (Γ0 ++ Γ1, C)) (A → B0 → B) (Γ0 ++ Γ1, C)
        Γ0 Γ1 C J3 J4 J5 X2 X0). auto.
      - repeat destruct s. repeat destruct p. subst. rewrite H2.
        assert (AndImpLRule [((Γ0 ++ x0) ++ A → B0 → C0 :: Γ5, C)] ((Γ0 ++ x0) ++ (A ∧ B0) → C0 :: Γ5, C)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules  [(Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)] (Γ0 ++ x0 ++ (A ∧ B0) → C0 :: Γ5, C)).
        apply PSAndImpL ; try intro ; try apply f ; try auto ; try assumption. apply AndImpL in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C) [(Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C) = mhd (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C) = (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)). reflexivity.
        repeat rewrite <- app_assoc in X0. simpl in X0.
        assert (J01: AndImpLRule [((Γ0 ++ x0) ++ A → B0 → C0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ (A ∧ B0) → C0 :: Γ5, A0 → B)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AndImpL_inv (Γ0 ++ x0 ++ (A ∧ B0) → C0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, A0 → B) D0 J01).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)) l (A0 → B) (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)
        Γ0 (x0 ++ A → B0 → C0 :: Γ5) C J5 J6 J7 d X0). apply derI with (ps:=[(Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)]).
        apply AndImpL. assert (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5 = (Γ0 ++ x0) ++ A → B0 → C0 :: Γ5). rewrite <- app_assoc. auto.
        rewrite H3. assert (Γ0 ++ x0 ++ (A ∧ B0) → C0 :: Γ5 = (Γ0 ++ x0) ++ (A ∧ B0) → C0 :: Γ5).  rewrite <- app_assoc. auto.
        rewrite H4. apply AndImpLRule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. rewrite H2.
        assert (AndImpLRule [(Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)] (Γ4 ++ (A ∧ B0) → C0 :: x ++ Γ1, C)). apply AndImpLRule_I.
        assert (J3: PSGL4ip_rules  [(Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)] (Γ4 ++ (A ∧ B0) → C0 :: x ++ Γ1, C)).
        apply PSAndImpL ; try intro ; try apply f ; try auto ; try assumption. apply AndImpL in H0.
        assert (J21: In  (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C) [(Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C) = mhd (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C) = (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)). reflexivity.
        repeat rewrite <- app_assoc in X0. simpl in X0. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndImpLRule [(Γ4 ++ A → B0 → C0 :: x ++ Γ1, A0 → B)] (Γ4 ++ (A ∧ B0) → C0 :: x ++ Γ1, A0 → B)). apply AndImpLRule_I.
        pose (AndImpL_inv (Γ4 ++ (A ∧ B0) → C0 :: x ++ Γ1, A0 → B) (Γ4 ++ A → B0 → C0 :: x ++ Γ1, A0 → B) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)) l (A0 → B) (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)
        (Γ4 ++ A → B0 → C0 :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d0. 
        pose (d0 J7 d X0). apply derI with (ps:=[(Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)]).
        apply AndImpL. repeat rewrite <- app_assoc. apply AndImpLRule_I. apply dlCons ; auto. }
    (* Right rule is OrImpL *)
    { inversion H. subst. inversion X2. subst. clear X4. clear X2. apply list_split_form in H6. destruct H6 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H2.
        assert (J0: list_exch_L ([] ++ [] ++ Γ2 ++ [A ∨  B0] ++ Γ3, B) ([] ++ [A ∨  B0] ++ Γ0 ++ Γ5 ++ Γ6, B)). rewrite <- H2.
        assert (Γ2 ++ Γ3 =Γ2 ++ [] ++ Γ3). auto. rewrite H0. apply list_exch_LI. simpl in J0.
        pose (GL4ip_adm_list_exch_L _ X3 _ J0).
        assert (J1: OrLRule [([] ++ A :: Γ0 ++ Γ5 ++ Γ6, B);([] ++ B0 :: Γ0 ++ Γ5 ++ Γ6, B)] ([] ++ A ∨  B0 :: Γ0 ++ Γ5 ++ Γ6, B)). apply OrLRule_I. simpl in J1.
        pose (OrL_inv _ _ _ d J1). destruct p.
        assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ5 ++ Γ6, A → B)).
        apply derI with (ps:=[([] ++ A :: Γ0 ++ Γ5 ++ Γ6, B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto. simpl in X2.
        assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ5 ++ Γ6, B0 → B)).
        apply derI with (ps:=[([] ++ B0 :: Γ0 ++ Γ5 ++ Γ6, B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto. simpl in X4.
        assert (J10: wkn_L (B0 → B) ((Γ0 ++ Γ5) ++ Γ6, A → B) ((Γ0 ++ Γ5) ++ B0 → B :: Γ6, A → B)). apply wkn_LI. repeat rewrite <- app_assoc in J10.
        pose (GL4ip_adm_wkn_L X2 J10).
        assert (J2: weight_form (A → B) < weight_form ((A ∨  B0) → B)). simpl. lia.
        assert (J3: weight_form (A → B) = weight_form (A → B)). auto.
        assert (J4: mhd (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C) = mhd (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C)). auto.
        assert (J5: (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C) = (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C)). auto.
        pose (PIH (weight_form (A → B)) J2 (mhd (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C)) (A → B) (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C)
        Γ0 (Γ5 ++ B0 → B :: Γ6) C J3 J4 J5 d2 X0).
        assert (J6: weight_form (B0 → B) < weight_form ((A ∨  B0) → B)). simpl. lia.
        assert (J7: weight_form (B0 → B) = weight_form (B0 → B)). auto.
        assert (J8: mhd (Γ0 ++ Γ5 ++ Γ6,C) = mhd (Γ0 ++ Γ5 ++ Γ6,C)). auto.
        assert (J9: (Γ0 ++ Γ5 ++ Γ6,C) = ((Γ0 ++ Γ5) ++ Γ6,C)). repeat rewrite <- app_assoc. auto.
        pose (PIH (weight_form (B0 → B)) J6 (mhd (Γ0 ++ Γ5 ++ Γ6,C)) (B0 → B) (Γ0 ++ Γ5 ++ Γ6,C)
        (Γ0 ++ Γ5) Γ6 C J7 J8 J9). repeat rewrite <- app_assoc in d4. pose (d4 X4 d3). auto.
      - repeat destruct s. repeat destruct p. subst. rewrite H2.
        assert (OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6 , C)] ((Γ0 ++ x0) ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6, C)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules  [(Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)] (Γ0 ++ x0 ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6, C)).
        apply PSOrImpL ; try intro ; try apply f ; try auto ; try assumption. apply OrImpL in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) [(Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) = mhd (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) = (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)). reflexivity.
        repeat rewrite <- app_assoc in X0. simpl in X0.
        assert (J01: OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, A0 → B)] ((Γ0 ++ x0) ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6, A0 → B)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrImpL_inv (Γ0 ++ x0 ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6, A0 → B) (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, A0 → B) D0 J01).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)) l (A0 → B) (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)
        Γ0 (x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6) C J5 J6 J7 d X0). apply derI with (ps:=[(Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)]).
        apply OrImpL. assert (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6 = (Γ0 ++ x0) ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6). rewrite <- app_assoc. auto.
        rewrite H3. assert (Γ0 ++ x0 ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6 = (Γ0 ++ x0) ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6).  rewrite <- app_assoc. auto.
        rewrite H4. apply OrImpLRule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. rewrite H2.
        repeat rewrite <- app_assoc. simpl.
        assert (OrImpLRule [(Γ4 ++ A → C0 :: [] ++  B0 → C0 :: x ++ Γ1, C)] (Γ4 ++ (A ∨ B0) → C0 :: [] ++ x ++ Γ1, C)). apply OrImpLRule_I.
        simpl in H0.
        assert (J3: PSGL4ip_rules  [(Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)] (Γ4 ++ (A ∨ B0) → C0 :: x ++ Γ1, C)).
        apply PSOrImpL ; try intro ; try apply f ; try auto ; try assumption. apply OrImpL in H0.
        assert (J21: In  (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C) [(Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C) = mhd (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C) = (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)). reflexivity.
        repeat rewrite <- app_assoc in X0. simpl in X0. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrImpLRule [(Γ4 ++ A → C0 :: [] ++ B0 → C0 :: x ++ Γ1, A0 → B)] (Γ4 ++ (A ∨ B0) → C0 :: [] ++ x ++ Γ1, A0 → B)). apply OrImpLRule_I.
        simpl in J01.
        pose (OrImpL_inv (Γ4 ++ (A ∨ B0) → C0 :: x ++ Γ1, A0 → B) (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, A0 → B) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)) l (A0 → B) (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)
        (Γ4 ++ A → C0 :: B0 → C0 :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d0. simpl in d0.
        pose (d0 J7 d).
        assert (J22: list_exch_L (Γ4 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) (Γ4 ++ A → C0 :: B0 → C0 :: x ++ A0 → B :: Γ1, C)).
        rewrite <- e0. assert (Γ4 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6 =(Γ4 ++ [A → C0]) ++ Γ5 ++ [B0 → C0] ++ [] ++ Γ6).
        repeat rewrite <- app_assoc. auto. rewrite H3. assert (Γ4 ++ A → C0 :: B0 → C0 :: Γ5 ++ Γ6 =(Γ4 ++ [A → C0]) ++ [] ++ [B0 → C0] ++ Γ5 ++ Γ6).
        repeat rewrite <- app_assoc. auto. rewrite H4. apply list_exch_LI.
        pose (GL4ip_adm_list_exch_L (Γ4 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) X0 (Γ4 ++ A → C0 :: B0 → C0 :: x ++ A0 → B :: Γ1, C) J22).
        pose (d1 d2). apply derI with (ps:=[(Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)]).
        apply OrImpL. assert (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1 = Γ4 ++ A → C0 :: []++ B0 → C0 :: x ++ Γ1). auto. rewrite H3.
        assert (Γ4 ++ (A ∨ B0) → C0 :: x ++ Γ1 = Γ4 ++(A ∨ B0) → C0 :: []++ x ++ Γ1). auto. rewrite H4.
        apply OrImpLRule_I. apply dlCons ; auto. }
    (* Right rule is ImpImpL *)
    { inversion H. subst. inversion X2. subst. inversion X4. subst. clear X6. clear X4. clear X2.
      apply list_split_form in H6. destruct H6 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H2.
        assert (J0: list_exch_L ([] ++ [] ++ Γ2 ++ [A →  B0] ++ Γ3, B) ([] ++ [A →  B0] ++ Γ0 ++ Γ1, B)). rewrite <- H2.
        assert (Γ2 ++ Γ3 =Γ2 ++ [] ++ Γ3). auto. rewrite H0. apply list_exch_LI. simpl in J0.
        pose (GL4ip_adm_list_exch_L _ X3 _ J0).
        pose (ImpL_inv_R A B0 [] (Γ0 ++ Γ1) B d).
        assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ1, B0 → B)).
        apply derI with (ps:=[([] ++ B0 :: Γ0 ++ Γ1, B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto. simpl in X2. clear d0.
        assert (J2: weight_form (B0 → B) < weight_form ((A →  B0) → B)). simpl. lia.
        assert (J3: weight_form (B0 → B) = weight_form (B0 → B)). auto.
        assert (J4: mhd (Γ0 ++ Γ1, A → B0) = mhd (Γ0 ++ Γ1, A → B0)). auto.
        assert (J5: (Γ0 ++ Γ1, A → B0) = (Γ0 ++ Γ1, A → B0)). auto.
        pose (PIH (weight_form (B0 → B)) J2 (mhd (Γ0 ++ Γ1, A → B0)) (B0 → B) (Γ0 ++ Γ1, A → B0)
        Γ0 Γ1 (A → B0) J3 J4 J5 X2 X0).
        assert (J6: weight_form (A → B0) < weight_form ((A →  B0) → B)). simpl. lia.
        assert (J7: weight_form (A → B0) = weight_form (A → B0)). auto.
        assert (J8: mhd (Γ0 ++ Γ1,B) = mhd (Γ0 ++ Γ1,B)). auto.
        assert (J9: (Γ0 ++ Γ1,B) = (Γ0 ++ Γ1,B)). auto.
        pose (PIH (weight_form (A → B0)) J6 (mhd (Γ0 ++ Γ1,B)) (A → B0) (Γ0 ++ Γ1,B)
        [] (Γ0 ++ Γ1) B J7 J8 J9). simpl in d1. pose (d1 d0 d).
        assert (J10: weight_form B < weight_form ((A →  B0) → B)). simpl. lia.
        assert (J11: weight_form B = weight_form B). auto.
        assert (J12: mhd (Γ0 ++ Γ1,C) = mhd (Γ0 ++ Γ1,C)). auto.
        assert (J13: (Γ0 ++ Γ1,C) = (Γ0 ++ Γ1,C)). auto.
        pose (PIH (weight_form B) J10 (mhd (Γ0 ++ Γ1,C)) B (Γ0 ++ Γ1,C)
        Γ0 Γ1 C J11 J12 J13). simpl in d3. pose (d3 d2 X5). auto.
      - repeat destruct s. repeat destruct p. subst. rewrite H2.
        assert (ImpImpLRule [((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0);((Γ0 ++ x0) ++ C0 :: Γ5, C)] ((Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5, C)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)] (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5, C)).
        apply PSImpImpL ; try intro ; try apply f ; try auto ; try assumption. apply ImpImpL in H0.
        repeat rewrite <- app_assoc in X5. simpl in X5. repeat rewrite <- app_assoc in X3. simpl in X3.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5, A0 → B) = ((Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        assert (J31: ctr_L (B0 → C0) ((Γ0 ++ x0) ++ A :: B0 → C0 :: B0 → C0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, A0 → B)).
        assert ((Γ0 ++ x0) ++ A :: B0 → C0 :: B0 → C0 :: Γ5 = (Γ0 ++ x0 ++ [A]) ++ B0 → C0 :: [] ++ B0 → C0 :: Γ5). repeat rewrite <- app_assoc. auto.
        rewrite H3.
        assert (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5 = (Γ0 ++ x0 ++ [A]) ++ B0 → C0 :: [] ++ Γ5). repeat rewrite <- app_assoc. auto.
        rewrite H4. apply ctr_LI.
        pose (@GL4ip_adm_ctr_L ((Γ0 ++ x0) ++ A :: B0 → C0 :: B0 → C0 :: Γ5, A0 → B) d (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, A0 → B) (B0 → C0) J31).
        assert (J01: ImpImpLRule [((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0);((Γ0 ++ x0) ++ C0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5, A0 → B)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (ImpImpL_inv_R (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0) (Γ0 ++ x0 ++ C0 :: Γ5, A0 → B) D0 J01).
        assert (J22: In (Γ0 ++ x0 ++ C0 :: Γ5, C) [(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J9: mhd (Γ0 ++ x0 ++ C0 :: Γ5, C) = mhd (Γ0 ++ x0 ++ C0 :: Γ5, C)). reflexivity.
        assert (J10 : (Γ0 ++ x0 ++ C0 :: Γ5, C) = (Γ0 ++ x0 ++ C0 :: Γ5, C)). reflexivity.
        pose (@SIH (mhd (Γ0 ++ x0 ++ C0 :: Γ5, C)) l (A0 → B) (Γ0 ++ x0 ++ C0 :: Γ5, C)
        Γ0 (x0 ++ C0 :: Γ5) C J8 J9 J10 d1 X5).
        destruct (dec_init_rules ((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0)).
        +  apply derI with (ps:=[(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)]).
            apply ImpImpL. assert (Γ0 ++ x0 ++ B0 → C0 :: Γ5 = (Γ0 ++ x0) ++ B0 → C0 :: Γ5). rewrite <- app_assoc. auto.
            rewrite H3. assert (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5 = (Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5).  rewrite <- app_assoc. auto.
            rewrite H4. assert (Γ0 ++ x0 ++ C0 :: Γ5 = (Γ0 ++ x0) ++ C0 :: Γ5). rewrite <- app_assoc. auto.
            rewrite H5. apply ImpImpLRule_I. apply dlCons ; auto. destruct s. inversion i. rewrite <- app_assoc in H3. rewrite <- H3. rewrite <- H5.
            apply Id_all_form. apply derI with (ps:=[]). apply BotL. rewrite <- app_assoc in b. auto. auto. apply dlCons ; auto.
        +  assert (J32: ImpRRule [((Γ0 ++ A0 → B :: x0) ++ A :: B0 → C0 :: Γ5, B0)] ((Γ0 ++ A0 → B :: x0) ++ B0 → C0 :: Γ5, A → B0)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J32. simpl in J32. repeat rewrite <- app_assoc in X0.
            pose (ImpR_inv (Γ0 ++ A0 → B :: x0 ++ B0 → C0 :: Γ5, A → B0) (Γ0 ++ A0 → B :: x0 ++ A:: B0 → C0 :: Γ5, B0) X0 J32).
            assert (J21: In (Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0) [(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J33: ImpRRule [((Γ0 ++ x0) ++ A :: B0 → C0 :: Γ5, B0)] ((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J33. simpl in J33.
            assert (J34: In (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0) [(Γ0 ++ x0 ++ A:: B0 → C0 :: Γ5, B0)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J35: ImpRRule [((Γ0 ++ x0) ++ A :: B0 → C0 :: Γ5, B0)] ((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in f0.
            assert (J36: PSGL4ip_rules [(Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)] (Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0)).
            apply PSImpR ; try intro ; try apply f0 ; try auto ; try assumption. apply ImpR in J35.
            pose (RA_mhd_decreases J36 _ J34).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J6: mhd (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0) = mhd (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)). reflexivity.
            assert (J7 : (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)= (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)). reflexivity.
            assert (J37: mhd (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0) < mhd (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5, C)). lia.
            pose (@SIH (mhd (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)) J37 (A0 → B) (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)
            Γ0 (x0 ++ A :: B0 → C0 :: Γ5) B0 J5 J6 J7 d0 d3).
            apply derI with (ps:=[(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)]).
            apply ImpImpL. assert (Γ0 ++ x0 ++ B0 → C0 :: Γ5 = (Γ0 ++ x0) ++ B0 → C0 :: Γ5). rewrite <- app_assoc. auto.
            rewrite H3. assert (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5 = (Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5).  rewrite <- app_assoc. auto.
            rewrite H4. assert (Γ0 ++ x0 ++ C0 :: Γ5 = (Γ0 ++ x0) ++ C0 :: Γ5). rewrite <- app_assoc. auto.
            rewrite H5. apply ImpImpLRule_I. apply dlCons ; auto.
            apply derI with (ps:=[(Γ0 ++ x0 ++ A:: B0 → C0 :: Γ5, B0)]). apply ImpR ; auto. apply dlCons ; auto.
            apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. rewrite H2.
        assert (ImpImpLRule [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0);(Γ4 ++ C0 :: x ++ Γ1, C)] (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, C)). apply ImpImpLRule_I.
        assert (J3: PSGL4ip_rules [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0);(Γ4 ++ C0 :: x ++ Γ1, C)] (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, C)).
        apply PSImpImpL ; try intro ; try apply f ; try auto ; try assumption. apply ImpImpL in H0. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B) = (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        assert (J31: ctr_L (B0 → C0) (Γ4 ++ A :: B0 → C0 :: B0 → C0 :: x ++ Γ1, A0 → B) (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, A0 → B)).
        assert (Γ4 ++ A :: B0 → C0 :: B0 → C0 :: x ++ Γ1 = (Γ4 ++ [A]) ++ B0 → C0 :: [] ++ B0 → C0 :: x ++ Γ1). repeat rewrite <- app_assoc. auto.
        rewrite H3.
        assert (Γ4 ++ A :: B0 → C0 :: x ++ Γ1 = (Γ4 ++ [A]) ++ B0 → C0 :: [] ++ x ++ Γ1). repeat rewrite <- app_assoc. auto.
        rewrite H4. apply ctr_LI. pose (@GL4ip_adm_ctr_L _ d _ _ J31).
        assert (J01: ImpImpLRule [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0);(Γ4 ++ C0 :: x ++ Γ1, A0 → B)] (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B)). apply ImpImpLRule_I.
        pose (ImpImpL_inv_R (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B) (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0) (Γ4 ++ C0 :: x ++ Γ1, A0 → B) D0 J01).
        assert (J22: In  (Γ4 ++ C0 :: x ++ Γ1, C) [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0); (Γ4 ++ C0 :: x ++ Γ1, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J9: mhd (Γ4 ++ C0 :: x ++ Γ1, C) = mhd (Γ4 ++ C0 :: x ++ Γ1, C)). reflexivity.
        assert (J10 : (Γ4 ++ C0 :: x ++ Γ1, C) = (Γ4 ++ C0 :: x ++ Γ1, C)). reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ4 ++ C0 :: x ++ Γ1, C)) l (A0 → B) (Γ4 ++ C0 :: x ++ Γ1, C)
        (Γ4 ++ C0 :: x) Γ1 C J8 J9). repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 J10 d1 X5).
        destruct (dec_init_rules (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0)).
        +  apply derI with (ps:=[(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0); (Γ4 ++ C0 :: x ++ Γ1, C)]).
            apply ImpImpL. repeat rewrite <- app_assoc. apply ImpImpLRule_I. apply dlCons ; auto. destruct s. inversion i.
            apply Id_all_form. apply derI with (ps:=[]). apply BotL. auto. auto. apply dlCons ; auto.
        +  assert (J32: ImpRRule [(Γ4 ++ A :: B0 → C0 :: x ++ A0 → B :: Γ1, B0)] (Γ4 ++ B0 → C0 :: x ++ A0 → B :: Γ1, A → B0)). apply ImpRRule_I.
            pose (ImpR_inv (Γ4 ++ B0 → C0 :: x ++ A0 → B :: Γ1, A → B0) (Γ4 ++ A :: B0 → C0 :: x ++ A0 → B :: Γ1, B0) X0 J32).
            assert (J21: In (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0) [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0); (Γ4 ++ C0 :: x ++ Γ1, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J33: ImpRRule [(Γ4 ++ A :: B0 → C0 :: x ++ Γ1,  B0)] (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J33. simpl in J33.
            assert (J34: In (Γ4 ++ A :: B0 → C0 :: x ++ Γ1,  B0) [(Γ4 ++ A :: B0 → C0 :: x ++ Γ1,  B0)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J35: ImpRRule [(Γ4 ++ A :: B0 → C0 :: x ++ Γ1,  B0)] (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in f0.
            assert (J36: PSGL4ip_rules [(Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0)] (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0)).
            apply PSImpR ; try intro ; try apply f0 ; try auto ; try assumption. apply ImpR in J35.
            pose (RA_mhd_decreases J36 _ J34).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J6: mhd (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0) = mhd (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0)). reflexivity.
            assert (J7 : (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0) = (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0)). reflexivity.
            assert (J37: mhd (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0) < mhd (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, C)). lia.
            pose (@SIH (mhd (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0)) J37 (A0 → B) (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0)
            (Γ4 ++ A :: B0 → C0 :: x) Γ1 B0 J5 J6). repeat rewrite <- app_assoc in d5. pose (d5 J7 d0 d4).
            apply derI with (ps:=[(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0); (Γ4 ++ C0 :: x ++ Γ1, C)]).
            apply ImpImpL. repeat rewrite <- app_assoc. apply ImpImpLRule_I. apply dlCons ; auto.
            apply derI with (ps:=[(Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0)]). apply ImpR ; auto. apply dlCons ; auto.
            apply dlCons ; auto. }
    (* Right rule is BoxImpL *)
    { inversion X0. subst. inversion X2. subst. inversion X6. subst. clear X8. clear X6. subst. clear X2. rewrite H2.
      pose (univ_gen_ext_splitR _ _ X4). repeat destruct s. repeat destruct p. subst.
      apply list_split_form in H3. destruct H3 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst.
        assert (J50: weight_form (Box A) < weight_form (Box A → B)). simpl. lia.
        assert (J51: weight_form (Box A) = weight_form (Box A)). auto.
        assert (J52: mhd (Γ0 ++ Γ1, C) = mhd (Γ0 ++ Γ1, C)). auto.
        assert (J53: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
        pose (PIH (weight_form (Box A)) J50 (mhd (Γ0 ++ Γ1, C)) (Box A) (Γ0 ++ Γ1, C) Γ0 Γ1 C
        J51 J52 J53). apply d.
        apply derI with (ps:=[(XBoxed_list (x ++ x0) ++ [Box A], A)]). apply GLR. apply GLRRule_I ; auto.
        apply dlCons ; auto.
        assert (J60: weight_form B < weight_form (Box A → B)). simpl. lia.
        assert (J61: weight_form B = weight_form B). auto.
        assert (J62: mhd (Γ0 ++ Box A :: Γ1, C) = mhd (Γ0 ++ Box A :: Γ1, C)). auto.
        assert (J63: (Γ0 ++ Box A :: Γ1, C) = (Γ0 ++ Box A :: Γ1, C)). auto.
        pose (PIH (weight_form B) J60 (mhd (Γ0 ++ Box A :: Γ1, C)) B  (Γ0 ++ Box A :: Γ1, C)
        Γ0 (Box A :: Γ1) C J61 J62 J63). apply d0. clear d. clear d0.
        apply GL4ip_adm_list_exch_L with (s:=(Box A :: Γ2 ++ Γ3, B)).
        apply GL4ip_adm_list_exch_L with (s:=(Γ2 ++ Box A :: Γ3, B)) ; auto.
        assert (Γ2 ++ Box A :: Γ3 = [] ++ [] ++ Γ2 ++ [Box A] ++ Γ3). auto. rewrite H.
        assert (Box A :: Γ2 ++ Γ3 = [] ++ [Box A] ++ Γ2 ++ [] ++ Γ3). auto. rewrite H0. apply list_exch_LI.
        assert (Γ0 ++ Box A :: Γ1 = [] ++ [] ++ Γ0 ++ [Box A] ++ Γ1). auto. rewrite H.
        assert (Box A :: Γ2 ++ Γ3 = [] ++ [Box A] ++ Γ0 ++ [] ++ Γ1). rewrite H2. auto. rewrite H0. apply list_exch_LI.
        apply GL4ip_adm_wkn_L with (s:=(Γ0 ++ B :: Γ1, C)) (A:=Box A) ; auto.
        assert (Γ0 ++ B :: Γ1 = (Γ0 ++ [B]) ++ Γ1). rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ B :: Box A :: Γ1 = (Γ0 ++ [B]) ++ Box A :: Γ1). rewrite <- app_assoc. auto. rewrite H0. apply wkn_LI.
      - repeat destruct s ; repeat destruct p ; subst.
        pose (univ_gen_ext_splitR _ _ u). repeat destruct s. repeat destruct p.
        simpl in u1. pose (univ_gen_ext_splitR _ _ u1). repeat destruct s. repeat destruct p. subst.
        clear u. clear u1. inversion u4. subst. exfalso.
        assert (In (A0 → B) (((x4 ++ A0 → B :: l) ++ x3) ++ x0)). apply in_or_app. left. apply in_or_app. left. apply in_or_app. right. apply in_eq.
        pose (H5 (A0 → B) H). destruct e. inversion H0. subst. inversion X2. subst. clear X2. clear u4.
        repeat rewrite <- app_assoc in X7. simpl in X7.
        assert (J0: BoxImpLRule [(XBoxed_list (x4 ++ x3 ++ x0) ++ [Box A], A);((Γ0 ++ x2) ++ B0 :: Γ5, C)] ((Γ0 ++ x2) ++ Box A → B0 :: Γ5, C)).
        apply BoxImpLRule_I. repeat rewrite <- app_assoc in H5. simpl in H5. auto. repeat rewrite <- app_assoc.  apply univ_gen_ext_combine ; auto.
        apply univ_gen_ext_combine ; auto. repeat rewrite <- app_assoc in J0.
        assert (J3: PSGL4ip_rules [(XBoxed_list (x4 ++ x3 ++ x0) ++ [Box A], A); ((Γ0 ++ x2) ++ B0 :: Γ5, C)] (Γ0 ++ x2 ++ Box A → B0 :: Γ5, C)).
        rewrite <- app_assoc ; apply PSBoxImpL ; try intro ; try apply f ; try auto ; try assumption. apply BoxImpL in J0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ0 ++ x2 ++ Box A → B0 :: Γ5, A0 → B) = ((Γ0 ++ x2) ++ Box A → B0 :: Γ5, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        assert (J70: weight_form (Box A → B0) = weight_form (Box A → B0)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J70 J60 J61).
        assert (J21: In ((Γ0 ++ x2) ++ B0 :: Γ5, C) [(XBoxed_list (x4 ++ x3 ++ x0) ++ [Box A], A); ((Γ0 ++ x2) ++ B0 :: Γ5, C)]). apply in_cons.
        apply in_eq. pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd ((Γ0 ++ x2) ++ B0 :: Γ5, C) = mhd ((Γ0 ++ x2) ++ B0 :: Γ5, C)). rewrite <- app_assoc. reflexivity.
        assert (J7 : ((Γ0 ++ x2) ++ B0 :: Γ5, C) = (Γ0 ++ x2 ++ B0 :: Γ5, C)). rewrite <- app_assoc. reflexivity.
        pose (@SIH (mhd  ((Γ0 ++ x2) ++ B0 :: Γ5, C)) l (A0 → B) ((Γ0 ++ x2) ++ B0 :: Γ5, C)
        Γ0 (x2 ++ B0 :: Γ5) C J5 J6 J7).
        assert (Γ0 ++ x2 ++ B0 :: Γ5 = (Γ0 ++ x2) ++ B0 :: Γ5). rewrite <- app_assoc. auto. rewrite H in d0.
        assert (((Γ0 ++ x2) ++ B0 :: Γ5, C) = (Γ0 ++ x2 ++ B0 :: Γ5, C)). rewrite <- app_assoc. auto. rewrite H0 in d0.
        pose (d0 d X7).
        repeat rewrite <- app_assoc in X5. simpl in X5.
        apply derI with (ps:=[(XBoxed_list (x4 ++ x3 ++ x0) ++ [Box A], A); (Γ0 ++ x2 ++ B0 :: Γ5, C)]) ; auto.
        apply dlCons ; auto. apply dlCons ; auto.
      - repeat destruct s ; repeat destruct p ; subst.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p. subst. clear u0.
        inversion u2. subst. exfalso. assert (In (A0 → B) (x ++ x2 ++ A0 → B :: l)). apply in_or_app. right.
        apply in_or_app. right. apply in_eq. pose (H5 (A0 → B) H). destruct e. inversion H0. subst.
        clear u2. repeat rewrite <- app_assoc in X5. repeat rewrite <- app_assoc. simpl.
        assert (J0: BoxImpLRule [(XBoxed_list (x ++ x2 ++ x3) ++ [Box A], A);(Γ4 ++ B0 :: x1 ++ Γ1, C)] (Γ4 ++ Box A → B0 :: x1 ++ Γ1, C)).
        apply BoxImpLRule_I ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto. repeat rewrite <- app_assoc in f.
        assert (J3: PSGL4ip_rules [(XBoxed_list (x ++ x2 ++ x3) ++ [Box A], A); (Γ4 ++ B0 :: x1 ++ Γ1, C)] (Γ4 ++ Box A → B0 :: x1 ++ Γ1, C)).
        apply PSBoxImpL ; try intro ; try apply f ; try auto ; try assumption. apply BoxImpL in J0.
        repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ4 ++ Box A → B0 :: x1 ++ Γ1, A0 → B) = (Γ4 ++ Box A → B0 :: x1 ++ Γ1, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        assert (J70: weight_form (Box A → B0) = weight_form (Box A → B0)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J70 J60 J61).
        assert (J21: In (Γ4 ++ B0 :: x1 ++ Γ1, C) [(XBoxed_list (x ++ x2 ++ x3) ++ [Box A], A); (Γ4 ++ B0 :: x1 ++ Γ1, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J6: mhd (Γ4 ++ B0 :: x1 ++ Γ1, C) = mhd (Γ4 ++ B0 :: x1 ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ4 ++ B0 :: x1 ++ Γ1, C) = ((Γ4 ++ B0 :: x1) ++ Γ1, C)). repeat rewrite <- app_assoc. reflexivity.
        repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd  (Γ4 ++ B0 :: x1 ++ Γ1, C)) l (A0 → B) (Γ4 ++ B0 :: x1 ++ Γ1, C)
        (Γ4 ++ B0 :: x1) Γ1 C J5 J6 J7). repeat rewrite <- app_assoc in d0. pose (d0 d X7).
        apply derI with (ps:=[(XBoxed_list (x ++ x2 ++ x3) ++ [Box A], A); (Γ4 ++ B0 :: x1 ++ Γ1, C)]) ; auto.
        apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is GLR *)
    { inversion X0. subst. rewrite H2. inversion X2. subst. clear X6. clear X2.
      pose (univ_gen_ext_splitR _ _ X4). repeat destruct s. repeat destruct p. inversion u0. subst.
      exfalso. assert (In (A0 → B) (x ++ A0 → B :: l)). apply in_or_app. right. apply in_eq. pose (H5  (A0 → B) H).
      destruct e. inversion H0. subst. clear u0.
      apply derI with (ps:=[(XBoxed_list (x ++ x0) ++ [Box A], A)]) ; auto. apply GLR. apply GLRRule_I ; auto.
      apply univ_gen_ext_combine ; auto. apply dlCons ; auto. }

(* Left rule is AtomImpL1 *)
- inversion H1. subst. inversion X0. subst. clear X4. clear X0. clear X2.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H2 in d.
  pose (AtomImpL_inv P A0 (A :: Γ2 ++ # P :: Γ3) Γ4 C). repeat rewrite <- app_assoc in d0. simpl in d0.
  repeat rewrite <- app_assoc in d0. simpl in d0. pose (d0 d).
  assert (J1: AtomImpL1Rule  [(Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)] (Γ2 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)).
  apply AtomImpL1Rule_I. apply PSAtomImpL1 in J1.
  assert (J2: In (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C) [(Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)]). apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H2 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C) = mhd (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)). auto.
  assert (J5: (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C) = ([] ++ Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)). auto.
  pose (@SIH (mhd (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)) l A (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C) [] (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4) C J3 J4 J5). simpl in d2.
  pose (d2 X3 d1). apply derI with (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)]). apply AtomImpL1. apply AtomImpL1Rule_I.
  apply dlCons ; auto. rewrite <- H2 in f. auto. rewrite <- H2 in f. auto.

(* Left rule is AtomImpL2 *)
- inversion H1. subst. inversion X0. subst. clear X4. clear X0. clear X2.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H2 in d.
  pose (AtomImpL_inv P A0 (A :: Γ2) (Γ3 ++ # P :: Γ4) C). repeat rewrite <- app_assoc in d0. simpl in d0.
  pose (d0 d).
  assert (J1: AtomImpL2Rule  [(Γ2 ++A0  :: Γ3 ++ # P :: Γ4, C)] (Γ2 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)).
  apply AtomImpL2Rule_I. apply PSAtomImpL2 in J1.
  assert (J2: In (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C) [(Γ2 ++ A0:: Γ3 ++ # P  :: Γ4, C)]). apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H2 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C) = mhd (Γ2 ++ A0 :: Γ3 ++ # P  :: Γ4, C)). auto.
  assert (J5: (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C) = ([] ++ Γ2 ++  A0:: Γ3 ++ # P :: Γ4, C)). auto.
  pose (@SIH (mhd (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C)) l A (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C) [] (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4) C J3 J4 J5). simpl in d2.
  pose (d2 X3 d1). apply derI with (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C)]). apply AtomImpL2. apply AtomImpL2Rule_I.
  apply dlCons ; auto. rewrite <- H2 in f. auto. rewrite <- H2 in f. auto.

(* Left rule is AndImpL *)
- inversion H1. subst. inversion X0. subst. clear X4. clear X0. clear X2.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H2 in d.
  assert (J01: AndImpLRule [((A :: Γ2) ++ A0 → B → C0 :: Γ3, C)] ((A :: Γ2) ++ (A0 ∧ B) → C0 :: Γ3, C)). apply AndImpLRule_I.
  pose (AndImpL_inv ((A :: Γ2) ++ (A0 ∧ B) → C0 :: Γ3, C) ((A :: Γ2) ++ A0 → B → C0 :: Γ3, C) d J01).
  repeat rewrite <- app_assoc in d0. simpl in d0.
  assert (J1: AndImpLRule  [(Γ2 ++ A0 → B → C0 :: Γ3, C)] (Γ2 ++ (A0 ∧ B) → C0 :: Γ3, C)).
  apply AndImpLRule_I. apply PSAndImpL in J1.
  assert (J2: In (Γ2 ++ A0 → B → C0 :: Γ3, C) [(Γ2 ++ A0 → B → C0 :: Γ3, C)]). apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H2 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd (Γ2 ++ A0 → B → C0 :: Γ3, C) = mhd (Γ2 ++ A0 → B → C0 :: Γ3, C)). auto.
  assert (J5: (Γ2 ++ A0 → B → C0 :: Γ3, C) = ([] ++ Γ2 ++ A0 → B → C0 :: Γ3, C)). auto.
  pose (@SIH (mhd(Γ2 ++ A0 → B → C0 :: Γ3, C)) l A (Γ2 ++ A0 → B → C0 :: Γ3, C) [] (Γ2 ++ A0 → B → C0 :: Γ3) C J3 J4 J5). simpl in d1.
  pose (d1 X3 d0). apply derI with (ps:=[(Γ2 ++ A0 → B → C0 :: Γ3, C)]). apply AndImpL. apply AndImpLRule_I.
  apply dlCons ; auto. rewrite <- H2 in f. auto. rewrite <- H2 in f. auto.

(* Left rule is OrImpL *)
- inversion H1. subst. inversion X0. subst. clear X4. clear X0. clear X2.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H2 in d.
  assert (J01: OrImpLRule [((A :: Γ2) ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)] ((A :: Γ2) ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
  pose (OrImpL_inv ((A :: Γ2) ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C) ((A :: Γ2) ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) d J01).
  repeat rewrite <- app_assoc in d0. simpl in d0.
  assert (J1: OrImpLRule  [(Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)] (Γ2 ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C)).
  apply OrImpLRule_I. apply PSOrImpL in J1.
  assert (J2: In (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) [(Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)]). apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H2 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) = mhd (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)). auto.
  assert (J5: (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) = ([] ++ Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)). auto.
  pose (@SIH (mhd(Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)) l A (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) [] (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4) C J3 J4 J5). simpl in d1.
  pose (d1 X3 d0). apply derI with (ps:=[(Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)]). apply OrImpL. apply OrImpLRule_I.
  apply dlCons ; auto. rewrite <- H2 in f. auto. rewrite <- H2 in f. auto.

(* Left rule is ImpImpL *)
- inversion H1. subst. inversion X0. subst. inversion X4. subst. clear X4. clear X6. clear X0. clear X2.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H2 in d.
  assert (J01: ImpImpLRule [((A :: Γ2) ++ B → C0 :: Γ3, A0 → B);((A :: Γ2) ++ C0 :: Γ3, C)] ((A :: Γ2) ++ (A0 → B) → C0 :: Γ3, C)). apply ImpImpLRule_I.
  pose (ImpImpL_inv_R ((A :: Γ2) ++ (A0 → B) → C0 :: Γ3, C) ((A :: Γ2) ++ B → C0 :: Γ3, A0 → B) ((A :: Γ2) ++ C0 :: Γ3, C) d J01).
  repeat rewrite <- app_assoc in d0. simpl in d0.
  assert (J1: ImpImpLRule  [(Γ2 ++ B → C0 :: Γ3, (A0 → B));(Γ2 ++ C0 :: Γ3, C)] (Γ2 ++ (A0 → B) → C0 :: Γ3, C)).
  apply ImpImpLRule_I. apply PSImpImpL in J1.
  assert (J2: In (Γ2 ++ C0 :: Γ3, C) [(Γ2 ++ B → C0 :: Γ3, A0 → B); (Γ2 ++ C0 :: Γ3, C)]). apply in_cons. apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H2 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd(Γ2 ++ C0 :: Γ3, C) = mhd (Γ2 ++ C0 :: Γ3, C)). auto.
  assert (J5: (Γ2 ++ C0 :: Γ3, C) = ([] ++ Γ2 ++ C0 :: Γ3, C)). auto.
  pose (@SIH (mhd(Γ2 ++ C0 :: Γ3, C)) l A (Γ2 ++ C0 :: Γ3, C) [] (Γ2 ++ C0 :: Γ3) C J3 J4 J5). simpl in d1.
  pose (d1 X5 d0). apply derI with (ps:=[(Γ2 ++ B → C0 :: Γ3, A0 → B); (Γ2 ++ C0 :: Γ3, C)]). apply ImpImpL. apply ImpImpLRule_I.
  apply dlCons ; auto. apply dlCons ; auto. rewrite <- H2 in f. auto. rewrite <- H2 in f. auto.

(* Left rule is BoxImpL *)
- inversion X3. subst. inversion X0. subst. inversion X6. subst. clear X8. clear X6. clear X2. clear X0.
  assert (J00 : list_exch_L (Γ0 ++ A :: Γ1, C) (A :: Γ0 ++ Γ1, C)).
  assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H0. clear H0.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H0. clear H0.
  apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ D1 _ J00). rewrite <- H in d.
  assert (J01: BoxImpLRule [ (XBoxed_list (top_boxes (A :: Γ2 ++ Γ3)) ++ [Box A0], A0);((A :: Γ2) ++ B :: Γ3, C)] ((A :: Γ2) ++ Box A0 → B :: Γ3, C)).
  apply BoxImpLRule_I. intro. intros. apply in_top_boxes in H0. destruct H0. destruct s. destruct s. destruct p. exists x. auto.
  repeat rewrite <- app_assoc. destruct (dec_is_boxedT A). assert (top_boxes (A :: Γ2 ++ Γ3) = A :: top_boxes (Γ2 ++ Γ3)).
  destruct i. simpl. subst. auto. rewrite H0. clear H0. simpl. apply univ_gen_ext_cons.
  apply top_boxes_nobox_gen_ext. assert (top_boxes (A :: Γ2 ++ Γ3) = top_boxes (Γ2 ++ Γ3)). destruct A ; auto.
  exfalso. apply f0. exists A. auto. rewrite H0. clear H0. simpl. apply univ_gen_ext_extra ; auto.
  apply top_boxes_nobox_gen_ext.
  assert (J02: derrec_height d = derrec_height d). auto.
  pose (ImpL_inv_R (Box A0) B (A :: Γ2) Γ3 C d). simpl in d0.
  assert (J1: BoxImpLRule  [(XBoxed_list BΓ ++ [Box A0], A0); (Γ2 ++ B :: Γ3, C)] (Γ2 ++ Box A0 → B :: Γ3, C)).
  apply BoxImpLRule_I ; auto. apply PSBoxImpL in J1.
  assert (J2: In (Γ2 ++ B :: Γ3, C) [(XBoxed_list BΓ ++ [Box A0], A0); (Γ2 ++ B :: Γ3, C)]). apply in_cons. apply in_eq.
  pose (RA_mhd_decreases J1 _ J2). rewrite <- H in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J4: mhd(Γ2 ++ B :: Γ3, C) = mhd (Γ2 ++ B :: Γ3, C)). auto.
  assert (J5: (Γ2 ++ B :: Γ3, C) = ([] ++ Γ2 ++ B :: Γ3, C)). auto.
  pose (@SIH (mhd(Γ2 ++ B :: Γ3, C)) l A (Γ2 ++ B :: Γ3, C) [] (Γ2 ++ B :: Γ3) C J3 J4 J5). simpl in d1.
  pose (d1 X7 d0). apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A0], A0); (Γ2 ++ B :: Γ3, C)]). apply BoxImpL. apply BoxImpLRule_I ; auto.
  apply dlCons ; auto. apply dlCons ; auto. rewrite <- H in f. auto. rewrite <- H in f. auto.

(* Left rule is GLR *)
- inversion X3. subst. inversion X1.
    (* Right rule is IdP *)
    { inversion H. subst. assert (J0 : InT (# P) (Γ0 ++ Box A0 :: Γ1)). rewrite <- H5. apply InT_or_app.
      right. apply InT_eq. apply InT_app_or in J0. destruct J0.
      - apply InT_split in i. destruct i. destruct s. subst. rewrite <- app_assoc.
        assert (IdPRule [] (x ++ (# P :: x0) ++ Γ1, # P)). apply IdPRule_I. apply IdP in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (x ++ (# P :: x0) ++ Γ1,  # P) H0 DersNilF). assumption.
      - inversion i.
        * inversion H2.
        * apply InT_split in H2. destruct H2. destruct s. subst. rewrite app_assoc.
          assert (IdPRule [] ((Γ0 ++ x) ++ # P :: x0, # P)). apply IdPRule_I. apply IdP in H0.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ0 ++ x) ++ # P :: x0, # P) H0 DersNilF). assumption. }
    (* Right rule is BotL *)
    { inversion H. subst. assert (J0 : InT (⊥) (Γ0 ++ Box A0 :: Γ1)). rewrite <- H5. apply InT_or_app.
      right. apply InT_eq. apply InT_app_or in J0. destruct J0.
      - apply InT_split in i. destruct i. destruct s. subst. rewrite <- app_assoc.
        assert (BotLRule [] (x ++ (⊥ :: x0) ++ Γ1, C)). apply BotLRule_I. apply BotL in H0.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (x ++ (⊥ :: x0) ++ Γ1, C) H0 DersNilF). assumption.
      - inversion i.
        * inversion H2.
        * apply InT_split in H2. destruct H2. destruct s. subst. rewrite app_assoc.
          assert (BotLRule [] ((Γ0 ++ x) ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H0.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ0 ++ x) ++ ⊥ :: x0, C) H0 DersNilF). assumption. }
    (* Right rule is AndR *)
    { inversion H. subst. inversion X2. subst. inversion X6. subst. clear X6. clear X8.
      assert (AndRRule [(Γ0 ++ Γ1, A);(Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A ∧ B)). apply AndRRule_I.
      assert (J3: PSGL4ip_rules [(Γ0 ++ Γ1, A);(Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A ∧ B)).
      apply PSAndR ; try intro ; try apply f ; try auto ; try assumption. apply AndR in H0.
      assert (J21: In  (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J6: mhd (Γ0 ++ Γ1, A) = mhd (Γ0 ++ Γ1, A)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity.
      pose (@SIH (mhd (Γ0 ++ Γ1, A)) l (Box A0) (Γ0 ++ Γ1, A)
      Γ0 Γ1 A J5 J6 J7 D0 X5).
      assert (J31: In  (Γ0 ++ Γ1, B) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B)]). apply in_cons. apply in_eq.
      pose (RA_mhd_decreases J3 _ J31).
      assert (J9: mhd (Γ0 ++ Γ1, B) = mhd (Γ0 ++ Γ1, B)). reflexivity.
      assert (J10 : (Γ0 ++ Γ1, B) = (Γ0 ++ Γ1, B)). reflexivity.
      pose (@SIH (mhd (Γ0 ++ Γ1, B)) l0 (Box A0) (Γ0 ++ Γ1, B)
      Γ0 Γ1 B J5 J9 J10 D0 X7). apply derI with (ps:=[(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B)]).
      apply AndR. apply AndRRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is AndL *)
    { inversion H. subst. inversion X2. subst. clear X6. clear X2. apply list_split_form in H5. destruct H5 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AndLRule [((Γ0 ++ x0) ++ A :: B :: Γ3, C)] ((Γ0 ++ x0) ++ A ∧ B :: Γ3, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules  [(Γ0 ++ x0 ++ A :: B :: Γ3, C)] (Γ0 ++ x0 ++ A ∧ B :: Γ3, C)).
        apply PSAndL ; try intro ; try apply f ; try auto ; try assumption. apply AndL in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A :: B :: Γ3, C) [(Γ0 ++ x0 ++ A :: B :: Γ3, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A :: B :: Γ3, C) = mhd (Γ0 ++ x0 ++ A :: B :: Γ3, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: B :: Γ3, C) = (Γ0 ++ x0 ++ A :: B :: Γ3, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5.
        assert (J01: AndLRule [((Γ0 ++ x0) ++ A :: B :: Γ3, Box A0)] ((Γ0 ++ x0) ++ A ∧ B :: Γ3, Box A0)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AndL_inv(Γ0 ++ x0 ++ A ∧ B :: Γ3, Box A0) (Γ0 ++ x0 ++ A :: B :: Γ3, Box A0) D0 J01).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A :: B :: Γ3, C)) l (Box A0) (Γ0 ++ x0 ++ A :: B :: Γ3, C)
        Γ0 (x0 ++ A :: B :: Γ3) C J5 J6 J7 d X5). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: B :: Γ3, C)]).
        apply AndL. assert (Γ0 ++ x0 ++ A :: B :: Γ3 = (Γ0 ++ x0) ++ A :: B :: Γ3). rewrite <- app_assoc. auto.
        rewrite H2. assert (Γ0 ++ x0 ++ A ∧ B :: Γ3 = (Γ0 ++ x0) ++ A ∧ B :: Γ3).  rewrite <- app_assoc. auto.
        rewrite H3. apply AndLRule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
        assert (AndLRule [(Γ2 ++ A :: B :: x ++ Γ1, C)] (Γ2 ++ A ∧ B :: x ++ Γ1, C)). apply AndLRule_I.
        assert (J3: PSGL4ip_rules  [(Γ2 ++ A :: B :: x ++ Γ1, C)] (Γ2 ++ A ∧ B :: x ++ Γ1, C)).
        apply PSAndL ; try intro ; try apply f ; try auto ; try assumption. apply AndL in H0.
        assert (J21: In  (Γ2 ++ A :: B :: x ++ Γ1, C) [(Γ2 ++ A :: B :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ2 ++ A :: B :: x ++ Γ1, C) = mhd (Γ2 ++ A :: B :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ2 ++ A :: B :: x ++ Γ1, C) = (Γ2 ++ A :: B :: x ++ Γ1, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndLRule [(Γ2 ++ A :: B :: x ++ Γ1, Box A0)] (Γ2 ++ A ∧ B :: x ++ Γ1, Box A0)). apply AndLRule_I.
        pose (AndL_inv (Γ2 ++ A ∧ B :: x ++ Γ1, Box A0) (Γ2 ++ A :: B :: x ++ Γ1, Box A0) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ2 ++ A :: B :: x ++ Γ1, C)) l (Box A0) (Γ2 ++ A :: B :: x ++ Γ1, C)
        (Γ2 ++ A :: B :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d0. 
        pose (d0 J7 d X5). apply derI with (ps:=[(Γ2 ++ A :: B :: x ++ Γ1, C)]).
        apply AndL. apply AndLRule_I. apply dlCons ; auto. }
    (* Right rule is OrR1 *)
    { inversion H. subst. inversion X2. subst. clear X6. clear X2.
      assert (OrR1Rule [(Γ0 ++ Γ1, A)] (Γ0 ++ Γ1, A ∨ B)). apply OrR1Rule_I.
      assert (J3: PSGL4ip_rules [(Γ0 ++ Γ1, A)] (Γ0 ++ Γ1, A ∨ B)).
      apply PSOrR1 ; try intro ; try apply f ; try auto ; try assumption. apply OrR1 in H0.
      assert (J21: In  (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J6: mhd (Γ0 ++ Γ1, A) = mhd (Γ0 ++ Γ1, A)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity.
      pose (@SIH (mhd (Γ0 ++ Γ1, A)) l (Box A0) (Γ0 ++ Γ1, A)
      Γ0 Γ1 A J5 J6 J7 D0 X5). apply derI with (ps:=[(Γ0 ++ Γ1, A)]).
      apply OrR1. apply OrR1Rule_I. apply dlCons ; auto. }
    (* Right rule is OrR2 *)
    { inversion H. subst. inversion X2. subst. clear X6. clear X2.
      assert (OrR2Rule [(Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A ∨ B)). apply OrR2Rule_I.
      assert (J3: PSGL4ip_rules [(Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A ∨ B)).
      apply PSOrR2 ; try intro ; try apply f ; try auto ; try assumption. apply OrR2 in H0.
      assert (J21: In  (Γ0 ++ Γ1, B) [(Γ0 ++ Γ1, B)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J6: mhd (Γ0 ++ Γ1, B) = mhd (Γ0 ++ Γ1, B)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, B) = (Γ0 ++ Γ1, B)). reflexivity.
      pose (@SIH (mhd (Γ0 ++ Γ1, B)) l (Box A0) (Γ0 ++ Γ1, B)
      Γ0 Γ1 B J5 J6 J7 D0 X5). apply derI with (ps:=[(Γ0 ++ Γ1, B)]).
      apply OrR2. apply OrR2Rule_I. apply dlCons ; auto. }
    (* Right rule is OrL *)
    { inversion H. subst. inversion X2. subst. inversion X6. subst. clear X8. clear X6. clear X2.
      apply list_split_form in H5. destruct H5 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (OrLRule [((Γ0 ++ x0) ++ A :: Γ3, C);((Γ0 ++ x0) ++ B :: Γ3, C)] ((Γ0 ++ x0) ++ A ∨ B :: Γ3, C)). apply OrLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ A :: Γ3, C); (Γ0 ++ x0 ++ B :: Γ3, C)] (Γ0 ++ x0 ++ A ∨ B :: Γ3, C)).
        apply PSOrL ; try intro ; try apply f ; try auto ; try assumption. apply OrL in H0.
        repeat rewrite <- app_assoc in X5. simpl in X5. repeat rewrite <- app_assoc in X7. simpl in X7.
        assert (J01: OrLRule [((Γ0 ++ x0) ++ A :: Γ3, Box A0);((Γ0 ++ x0) ++ B :: Γ3, Box A0)] ((Γ0 ++ x0) ++ A ∨ B :: Γ3, Box A0)). apply OrLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrL_inv (Γ0 ++ x0 ++ A ∨ B :: Γ3, Box A0) (Γ0 ++ x0 ++ A :: Γ3, Box A0) (Γ0 ++ x0 ++ B :: Γ3, Box A0) D0 J01).
        destruct p.
        assert (J21: In (Γ0 ++ x0 ++ A :: Γ3, C) [(Γ0 ++ x0 ++ A :: Γ3, C); (Γ0 ++ x0 ++ B :: Γ3, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A :: Γ3, C) = mhd (Γ0 ++ x0 ++ A :: Γ3, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ3, C) = (Γ0 ++ x0 ++ A :: Γ3, C)). reflexivity.
        pose (@SIH (mhd (Γ0 ++ x0 ++ A :: Γ3, C)) l (Box A0) (Γ0 ++ x0 ++ A :: Γ3, C)
        Γ0 (x0 ++ A :: Γ3) C J5 J6 J7 d X5).
        assert (J22: In (Γ0 ++ x0 ++ B :: Γ3, C) [(Γ0 ++ x0 ++ A :: Γ3, C); (Γ0 ++ x0 ++ B :: Γ3, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J9: mhd (Γ0 ++ x0 ++ B :: Γ3, C) = mhd (Γ0 ++ x0 ++ B :: Γ3, C)). reflexivity.
        assert (J10 : (Γ0 ++ x0 ++ B :: Γ3, C) = (Γ0 ++ x0 ++ B :: Γ3, C)). reflexivity.
        pose (@SIH (mhd (Γ0 ++ x0 ++ B :: Γ3, C)) l0 (Box A0) (Γ0 ++ x0 ++ B :: Γ3, C)
        Γ0 (x0 ++ B :: Γ3) C J8 J9 J10 d0 X7).
        apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ3, C); (Γ0 ++ x0 ++ B :: Γ3, C)]).
        apply OrL. assert (Γ0 ++ x0 ++ A :: Γ3 = (Γ0 ++ x0) ++ A :: Γ3). rewrite <- app_assoc. auto.
        rewrite H2. assert (Γ0 ++ x0 ++ A ∨ B :: Γ3 = (Γ0 ++ x0) ++ A ∨ B :: Γ3).  rewrite <- app_assoc. auto.
        rewrite H3. assert (Γ0 ++ x0 ++ B :: Γ3 = (Γ0 ++ x0) ++ B :: Γ3). rewrite <- app_assoc. auto.
        rewrite H4. apply OrLRule_I. apply dlCons ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
        assert (OrLRule [(Γ2 ++ A :: x ++ Γ1, C);(Γ2 ++ B :: x ++ Γ1, C)] (Γ2 ++ A ∨ B :: x ++ Γ1, C)). apply OrLRule_I.
        assert (J3: PSGL4ip_rules [(Γ2 ++ A :: x ++ Γ1, C);(Γ2 ++ B :: x ++ Γ1, C)] (Γ2 ++ A ∨ B :: x ++ Γ1, C)).
        apply PSOrL ; try intro ; try apply f ; try auto ; try assumption. apply OrL in H0. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrLRule [(Γ2 ++ A :: x ++ Γ1, Box A0);(Γ2 ++ B :: x ++ Γ1, Box A0)] (Γ2 ++ A ∨ B :: x ++ Γ1, Box A0)). apply OrLRule_I.
        pose (OrL_inv (Γ2 ++ A ∨ B :: x ++ Γ1, Box A0) (Γ2 ++ A :: x ++ Γ1, Box A0) (Γ2 ++ B :: x ++ Γ1, Box A0) D0 J01).
        destruct p.
        assert (J21: In (Γ2 ++ A :: x ++ Γ1, C) [(Γ2 ++ A :: x ++ Γ1, C); (Γ2 ++ B :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ2 ++ A :: x ++ Γ1, C) = mhd (Γ2 ++ A :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ2 ++ A :: x ++ Γ1, C) = (Γ2 ++ A :: x ++ Γ1, C)). reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ2 ++ A :: x ++ Γ1, C)) l (Box A0) (Γ2 ++ A :: x ++ Γ1, C)
        (Γ2 ++ A :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d1. pose (d1 J7 d X5).
        assert (J22: In  (Γ2 ++ B :: x ++ Γ1, C) [(Γ2 ++ A :: x ++ Γ1, C); (Γ2 ++ B :: x ++ Γ1, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J9: mhd (Γ2 ++ B :: x ++ Γ1, C) = mhd (Γ2 ++ B :: x ++ Γ1, C)). reflexivity.
        assert (J10 : (Γ2 ++ B :: x ++ Γ1, C) = (Γ2 ++ B :: x ++ Γ1, C)). reflexivity.
        pose (@SIH (mhd (Γ2 ++ B :: x ++ Γ1, C)) l0 (Box A0) (Γ2 ++ B :: x ++ Γ1, C)
        (Γ2 ++ B :: x) Γ1 C J8 J9). repeat rewrite <- app_assoc in d3. pose (d3 J10 d0 X7).
        apply derI with (ps:=[(Γ2 ++ A :: x ++ Γ1, C); (Γ2 ++ B :: x ++ Γ1, C)]).
        apply OrL. apply OrLRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is ImpR *)
    { inversion H. subst. inversion X2. subst. clear X6. rewrite <- H5 in D1.
      assert (J1 : list_exch_L (Γ2 ++ A :: Γ3, B) (A :: Γ0 ++ Box A0 :: Γ1, B)).
      assert (Γ2 ++ A :: Γ3 = [] ++ [] ++ Γ2 ++ [A] ++ Γ3). reflexivity. rewrite H0. clear H0.
      assert (A :: Γ0 ++ Box A0 :: Γ1 = [] ++ [A] ++ Γ2 ++ [] ++ Γ3). rewrite <- H5. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI. pose (GL4ip_adm_list_exch_L _ X5 _ J1).
      assert (ImpRRule [([] ++ A :: Γ0 ++ Γ1, B)] ([] ++ Γ0 ++ Γ1, A → B)). apply ImpRRule_I.
      simpl in H0.
      assert (J3: PSGL4ip_rules [(A :: Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A → B)).
      apply PSImpR ; try intro ; try apply f ; try rewrite <- H6 ; try auto ; try assumption.
      assert (J31: GL4ip_rules [(A :: Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A → B)).
      apply ImpR ; try assumption.
      assert (J21: In (A :: Γ0 ++ Γ1, B) [(A :: Γ0 ++ Γ1, B)]). apply in_eq.
      pose (RA_mhd_decreases J3 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J6: mhd (A :: Γ0 ++ Γ1, B) = mhd (A :: Γ0 ++ Γ1, B)). reflexivity.
      assert (J7 : (A :: Γ0 ++ Γ1, B) = ((A :: Γ0) ++ Γ1, B)). reflexivity.
      pose (@SIH (mhd (A :: Γ0 ++ Γ1, B)) l (Box A0) (A :: Γ0 ++ Γ1, B)
      (A :: Γ0) Γ1 B J5 J6 J7). simpl in d0.
      assert (wkn_L A ([] ++ Γ0 ++ Γ1, Box A0) ([] ++ A :: Γ0 ++ Γ1, Box A0)). apply wkn_LI. simpl in H2.
      pose (@GL4ip_adm_wkn_L (Γ0 ++ Γ1, Box A0) D0 (A :: Γ0 ++ Γ1, Box A0) A H2).
      pose (d0 d1 d). pose (dlCons d2 DersNilF).
      apply ImpR in H0 ; try intro ; try apply f ; try rewrite <- H7 ; try auto ; try assumption.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[(A :: Γ0 ++ Γ1, B)]) (Γ0 ++ Γ1, A → B) H0 d3). assumption. }
    (* Right rule is AtomImpL1 *)
    { inversion H. subst. inversion X2. subst. clear X6. clear X2. apply list_split_form in H5. destruct H5 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ3 ++ A :: Γ4, C)] ((Γ0 ++ x0) ++ # P :: Γ3 ++ # P → A :: Γ4, C)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)] (Γ0 ++ x0 ++ # P :: Γ3 ++ # P → A :: Γ4, C)).
        apply PSAtomImpL1 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL1 in H0.
        assert (J21: In  (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C) [(Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C) = mhd (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C) = (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5.
        assert (J01: AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ3 ++ A :: Γ4,Box A0)] ((Γ0 ++ x0) ++ # P :: Γ3 ++ # P → A :: Γ4, Box A0)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0 ++ # P :: Γ3) Γ4 (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
        pose (d D0).
        pose (@SIH (mhd (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)) l (Box A0) (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)
        Γ0 (x0 ++ # P :: Γ3 ++ A :: Γ4) C J5 J6 J7 d0 X5). apply derI with (ps:=[(Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)]).
        apply AtomImpL1. assert (Γ0 ++ x0 ++ # P :: Γ3 ++ # P → A :: Γ4 = (Γ0 ++ x0) ++ # P :: Γ3 ++ # P → A :: Γ4). rewrite <- app_assoc. auto.
        rewrite H2. assert (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4 = (Γ0 ++ x0) ++ # P :: Γ3 ++ A :: Γ4).  rewrite <- app_assoc. auto.
        rewrite H3. apply AtomImpL1Rule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. simpl in f.
        apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0.
        +  repeat destruct s. repeat destruct p. subst.
            assert (AtomImpL1Rule [(Γ2 ++ # P :: (x ++ x1) ++ A :: Γ4, C)] (Γ2 ++ # P :: (x ++ x1) ++ # P → A :: Γ4, C)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in H0.
            assert (J3: PSGL4ip_rules [(Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)] (Γ2 ++ # P :: x ++ x1 ++ # P → A :: Γ4, C)).
            apply PSAtomImpL1 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL1 in H0.
            assert (J21: In  (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C) [(Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J6: mhd (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C) = mhd (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)). reflexivity.
            assert (J7 : (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C) = (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)). reflexivity.
            repeat rewrite <- app_assoc in X5. simpl in X5.
            assert (J01: AtomImpL1Rule [(Γ2 ++ # P :: (x ++ x1) ++ A :: Γ4, Box A0)] (Γ2 ++ # P :: (x ++ x1) ++ # P → A :: Γ4, Box A0)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ2 ++ # P :: x ++ x1) Γ4 (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)) l (Box A0) (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)
            (Γ2 ++ # P :: x) (x1 ++ A :: Γ4) C J5 J6). repeat rewrite <- app_assoc in d1. pose (d1 J7 d0 X5).
            apply derI with (ps:=[(Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)]). apply AtomImpL1.
            assert (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4 = Γ2 ++ # P :: (x ++ x1) ++ A :: Γ4). rewrite <- app_assoc. auto.
            rewrite H2. assert (Γ2 ++ # P :: x ++ x1 ++ # P → A :: Γ4 = Γ2 ++ # P :: (x ++ x1) ++ # P → A :: Γ4).  rewrite <- app_assoc. auto.
            rewrite H3. apply AtomImpL1Rule_I. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
            assert (AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)] (Γ2 ++ # P :: Γ3 ++ # P → A :: x0 ++ Γ1, C)). apply AtomImpL1Rule_I.
            assert (J3: PSGL4ip_rules [(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)] (Γ2 ++ # P :: Γ3 ++ # P → A :: x0 ++ Γ1, C)).
            apply PSAtomImpL1 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL1 in H0.
            assert (J21: In  (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C) [(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J6: mhd (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C) = mhd (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)). reflexivity.
            assert (J7 : (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C) = (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)). reflexivity.
            assert (J01: AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, Box A0)] (Γ2 ++ # P :: Γ3 ++ # P → A :: x0 ++ Γ1, Box A0)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ2 ++ # P :: Γ3) (x0 ++ Γ1) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)) l (Box A0) (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)
            (Γ2 ++ # P :: Γ3 ++ A :: x0) Γ1 C J5 J6). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 J7 d0 X5).
            apply derI with (ps:=[(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)]). apply AtomImpL1. apply AtomImpL1Rule_I. apply dlCons ; auto. }
    (* Right rule is AtomImpL2 *)
    { inversion H. subst. inversion X2. subst. clear X6. clear X2. apply list_split_form in H5. destruct H5 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ3 ++ # P :: Γ4, C)] ((Γ0 ++ x0) ++ # P → A :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)] (Γ0 ++ x0 ++ # P → A :: Γ3 ++ # P :: Γ4, C)).
        apply PSAtomImpL2 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL2 in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C) [(Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C) = mhd (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C) = (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5.
        assert (J01: AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ3 ++ # P :: Γ4,Box A0)] ((Γ0 ++ x0) ++ # P → A :: Γ3 ++ # P :: Γ4, Box A0)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0) (Γ3 ++ # P :: Γ4) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
        pose (d D0).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)) l (Box A0) (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)
        Γ0  (x0 ++ A :: Γ3 ++ # P :: Γ4) C J5 J6 J7 d0 X5). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)]).
        apply AtomImpL2. assert (Γ0 ++ x0 ++ # P → A :: Γ3 ++ # P :: Γ4 = (Γ0 ++ x0) ++ # P → A :: Γ3 ++ # P :: Γ4). rewrite <- app_assoc. auto.
        rewrite H2. assert (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4 = (Γ0 ++ x0) ++ A :: Γ3 ++ # P :: Γ4).  rewrite <- app_assoc. auto.
        rewrite H3. apply AtomImpL2Rule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. simpl in f.
        apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0.
        +  repeat destruct s. repeat destruct p. subst.
            assert (AtomImpL2Rule [(Γ2 ++ A :: (x ++ x1) ++ # P :: Γ4, C)] (Γ2 ++ # P → A :: (x ++ x1) ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in H0.
            assert (J3: PSGL4ip_rules [(Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)] (Γ2 ++ # P → A :: x ++ x1 ++ # P :: Γ4, C)).
            apply PSAtomImpL2 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL2 in H0.
            assert (J21: In  (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C) [(Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J6: mhd (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C) = mhd (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)). reflexivity.
            assert (J7 : (Γ2 ++  A :: x ++ x1 ++ # P :: Γ4, C) = (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)). reflexivity.
            repeat rewrite <- app_assoc in X5. simpl in X5.
            assert (J01: AtomImpL2Rule [(Γ2 ++ A :: (x ++ x1) ++ # P :: Γ4, Box A0)] (Γ2 ++ # P → A :: (x ++ x1) ++ # P :: Γ4, Box A0)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ2 (x ++ x1 ++ # P :: Γ4) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)) l (Box A0) (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)
            (Γ2 ++ A :: x) (x1 ++ # P :: Γ4) C J5 J6). repeat rewrite <- app_assoc in d1. pose (d1 J7 d0 X5).
            apply derI with (ps:=[(Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)]). apply AtomImpL2.
            assert (Γ2 ++ # P → A :: x ++ x1 ++ # P :: Γ4 = Γ2 ++ # P → A :: (x ++ x1) ++ # P :: Γ4). rewrite <- app_assoc. auto.
            rewrite H2. assert (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4 = Γ2 ++ A :: (x ++ x1) ++ # P :: Γ4).  rewrite <- app_assoc. auto.
            rewrite H3. apply AtomImpL2Rule_I. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
            assert (AtomImpL2Rule [(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)] (Γ2 ++ # P → A :: Γ3 ++ # P :: x0 ++ Γ1, C)). apply AtomImpL2Rule_I.
            assert (J3: PSGL4ip_rules [(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)] (Γ2 ++ # P → A :: Γ3 ++ # P :: x0 ++ Γ1, C)).
            apply PSAtomImpL2 ; try intro ; try apply f ; try auto ; try assumption. apply AtomImpL2 in H0.
            assert (J21: In  (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C) [(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J6: mhd (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C) = mhd (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)). reflexivity.
            assert (J7 : (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C) = (Γ2 ++  A :: Γ3 ++ # P :: x0 ++ Γ1, C)). reflexivity.
            assert (J01: AtomImpL2Rule [(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, Box A0)] (Γ2 ++ # P → A :: Γ3 ++ # P :: x0 ++ Γ1, Box A0)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ2 (Γ3 ++  # P :: x0 ++ Γ1) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (@SIH (mhd (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)) l (Box A0) (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)
            (Γ2 ++ A :: Γ3 ++ # P :: x0) Γ1 C J5 J6). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 J7 d0 X5).
            apply derI with (ps:=[(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)]). apply AtomImpL2. apply AtomImpL2Rule_I. apply dlCons ; auto. }
    (* Right rule is AndImpL *)
    { inversion H. subst. inversion X2. subst. clear X6. clear X2. apply list_split_form in H5. destruct H5 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AndImpLRule [((Γ0 ++ x0) ++ A → B → C0 :: Γ3, C)] ((Γ0 ++ x0) ++ (A ∧ B) → C0 :: Γ3, C)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules  [(Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)] (Γ0 ++ x0 ++ (A ∧ B) → C0 :: Γ3, C)).
        apply PSAndImpL ; try intro ; try apply f ; try auto ; try assumption. apply AndImpL in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C) [(Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C) = mhd (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C) = (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5.
        assert (J01: AndImpLRule [((Γ0 ++ x0) ++ A → B → C0 :: Γ3, Box A0)] ((Γ0 ++ x0) ++ (A ∧ B) → C0 :: Γ3, Box A0)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AndImpL_inv (Γ0 ++ x0 ++ (A ∧ B) → C0 :: Γ3, Box A0) (Γ0 ++ x0 ++ A → B → C0 :: Γ3, Box A0) D0 J01).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)) l (Box A0) (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)
        Γ0 (x0 ++ A → B → C0 :: Γ3) C J5 J6 J7 d X5). apply derI with (ps:=[(Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)]).
        apply AndImpL. assert (Γ0 ++ x0 ++ A → B → C0 :: Γ3 = (Γ0 ++ x0) ++ A → B → C0 :: Γ3). rewrite <- app_assoc. auto.
        rewrite H2. assert (Γ0 ++ x0 ++ (A ∧ B) → C0 :: Γ3 = (Γ0 ++ x0) ++ (A ∧ B) → C0 :: Γ3).  rewrite <- app_assoc. auto.
        rewrite H3. apply AndImpLRule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
        assert (AndImpLRule [(Γ2 ++ A → B → C0 :: x ++ Γ1, C)] (Γ2 ++ (A ∧ B) → C0 :: x ++ Γ1, C)). apply AndImpLRule_I.
        assert (J3: PSGL4ip_rules  [(Γ2 ++ A → B → C0 :: x ++ Γ1, C)] (Γ2 ++ (A ∧ B) → C0 :: x ++ Γ1, C)).
        apply PSAndImpL ; try intro ; try apply f ; try auto ; try assumption. apply AndImpL in H0.
        assert (J21: In  (Γ2 ++ A → B → C0 :: x ++ Γ1, C) [(Γ2 ++ A → B → C0 :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ2 ++ A → B → C0 :: x ++ Γ1, C) = mhd (Γ2 ++ A → B → C0 :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ2 ++ A → B → C0 :: x ++ Γ1, C) = (Γ2 ++ A → B → C0 :: x ++ Γ1, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndImpLRule [(Γ2 ++ A → B → C0 :: x ++ Γ1, Box A0)] (Γ2 ++ (A ∧ B) → C0 :: x ++ Γ1, Box A0)). apply AndImpLRule_I.
        pose (AndImpL_inv (Γ2 ++ (A ∧ B) → C0 :: x ++ Γ1, Box A0) (Γ2 ++ A → B → C0 :: x ++ Γ1, Box A0) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ2 ++ A → B → C0 :: x ++ Γ1, C)) l (Box A0) (Γ2 ++ A → B → C0 :: x ++ Γ1, C)
        (Γ2 ++ A → B → C0 :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d0. 
        pose (d0 J7 d X5). apply derI with (ps:=[(Γ2 ++ A → B → C0 :: x ++ Γ1, C)]).
        apply AndImpL. apply AndImpLRule_I. apply dlCons ; auto. }
    (* Right rule is OrImpL *)
    { inversion H. subst. inversion X2. subst. clear X6. clear X2. apply list_split_form in H5. destruct H5 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ3 ++ B → C0 :: Γ4 , C)] ((Γ0 ++ x0) ++ (A ∨ B) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules  [(Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)] (Γ0 ++ x0 ++ (A ∨ B) → C0 :: Γ3 ++ Γ4, C)).
        apply PSOrImpL ; try intro ; try apply f ; try auto ; try assumption. apply OrImpL in H0.
        assert (J21: In  (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C) [(Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C) = mhd (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C) = (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5.
        assert (J01: OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, Box A0)] ((Γ0 ++ x0) ++ (A ∨ B) → C0 :: Γ3 ++ Γ4, Box A0)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrImpL_inv (Γ0 ++ x0 ++ (A ∨ B) → C0 :: Γ3 ++ Γ4, Box A0) (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, Box A0) D0 J01).
        pose (@SIH (mhd (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)) l (Box A0) (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)
        Γ0 (x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4) C J5 J6 J7 d X5). apply derI with (ps:=[(Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)]).
        apply OrImpL. assert (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4 = (Γ0 ++ x0) ++ A → C0 :: Γ3 ++ B → C0 :: Γ4). rewrite <- app_assoc. auto.
        rewrite H2. assert (Γ0 ++ x0 ++ (A ∨ B) → C0 :: Γ3 ++ Γ4 = (Γ0 ++ x0) ++ (A ∨ B) → C0 :: Γ3 ++ Γ4).  rewrite <- app_assoc. auto.
        rewrite H3. apply OrImpLRule_I. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
        assert (OrImpLRule [(Γ2 ++ A → C0 :: [] ++  B → C0 :: x ++ Γ1, C)] (Γ2 ++ (A ∨ B) → C0 :: [] ++ x ++ Γ1, C)). apply OrImpLRule_I.
        simpl in H0.
        assert (J3: PSGL4ip_rules  [(Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)] (Γ2 ++ (A ∨ B) → C0 :: x ++ Γ1, C)).
        apply PSOrImpL ; try intro ; try apply f ; try auto ; try assumption. apply OrImpL in H0.
        assert (J21: In  (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C) [(Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C) = mhd (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C) = (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)). reflexivity.
        repeat rewrite <- app_assoc in X5. simpl in X5. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrImpLRule [(Γ2 ++ A → C0 :: [] ++ B → C0 :: x ++ Γ1, Box A0)] (Γ2 ++ (A ∨ B) → C0 :: [] ++ x ++ Γ1, Box A0)). apply OrImpLRule_I.
        simpl in J01.
        pose (OrImpL_inv (Γ2 ++ (A ∨ B) → C0 :: x ++ Γ1, Box A0) (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, Box A0) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)) l (Box A0) (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)
        (Γ2 ++ A → C0 :: B → C0 :: x) Γ1 C J5 J6). repeat rewrite <- app_assoc in d0. simpl in d0.
        pose (d0 J7 d).
        assert (J22: list_exch_L (Γ2 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C) (Γ2 ++ A → C0 :: B → C0 :: x ++ Box A0 :: Γ1, C)).
        rewrite <- e0. assert (Γ2 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4 =(Γ2 ++ [A → C0]) ++ Γ3 ++ [B → C0] ++ [] ++ Γ4).
        repeat rewrite <- app_assoc. auto. rewrite H2. assert (Γ2 ++ A → C0 :: B → C0 :: Γ3 ++ Γ4 =(Γ2 ++ [A → C0]) ++ [] ++ [B → C0] ++ Γ3 ++ Γ4).
        repeat rewrite <- app_assoc. auto. rewrite H3. apply list_exch_LI.
        pose (GL4ip_adm_list_exch_L (Γ2 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C) X5 (Γ2 ++ A → C0 :: B → C0 :: x ++ Box A0 :: Γ1, C) J22).
        pose (d1 d2). apply derI with (ps:=[(Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)]).
        apply OrImpL. assert (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1 = Γ2 ++ A → C0 :: []++ B → C0 :: x ++ Γ1). auto. rewrite H2.
        assert (Γ2 ++ (A ∨ B) → C0 :: x ++ Γ1 = Γ2 ++(A ∨ B) → C0 :: []++ x ++ Γ1). auto. rewrite H3.
        apply OrImpLRule_I. apply dlCons ; auto. }
    (* Right rule is ImpImpL *)
    { inversion H. subst. inversion X2. subst. inversion X6. subst. clear X8. clear X6. clear X2.
      apply list_split_form in H5. destruct H5 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (ImpImpLRule [((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B);((Γ0 ++ x0) ++ C0 :: Γ3, C)] ((Γ0 ++ x0) ++ (A → B) → C0 :: Γ3, C)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in H0.
        assert (J3: PSGL4ip_rules [(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)] (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3, C)).
        apply PSImpImpL ; try intro ; try apply f ; try auto ; try assumption. apply ImpImpL in H0.
        repeat rewrite <- app_assoc in X5. simpl in X5. repeat rewrite <- app_assoc in X7. simpl in X7.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3, Box A0) = ((Γ0 ++ x0) ++ (A → B) → C0 :: Γ3, Box A0)). rewrite <- app_assoc ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        assert (J31: ctr_L (B → C0) ((Γ0 ++ x0) ++ A :: B → C0 :: B → C0 :: Γ3, Box A0) (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, Box A0)).
        assert ((Γ0 ++ x0) ++ A :: B → C0 :: B → C0 :: Γ3 = (Γ0 ++ x0 ++ [A]) ++ B → C0 :: [] ++ B → C0 :: Γ3). repeat rewrite <- app_assoc. auto.
        rewrite H2.
        assert (Γ0 ++ x0 ++ A :: B → C0 :: Γ3 = (Γ0 ++ x0 ++ [A]) ++ B → C0 :: [] ++ Γ3). repeat rewrite <- app_assoc. auto.
        rewrite H3. apply ctr_LI.
        pose (@GL4ip_adm_ctr_L ((Γ0 ++ x0) ++ A :: B → C0 :: B → C0 :: Γ3, Box A0) d (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, Box A0) (B → C0) J31).
        assert (J01: ImpImpLRule [((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B);((Γ0 ++ x0) ++ C0 :: Γ3, Box A0)] ((Γ0 ++ x0) ++ (A → B) → C0 :: Γ3, Box A0)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (ImpImpL_inv_R (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3, Box A0) (Γ0 ++ x0 ++ B → C0 :: Γ3, A → B) (Γ0 ++ x0 ++ C0 :: Γ3, Box A0) D0 J01).
        assert (J22: In (Γ0 ++ x0 ++ C0 :: Γ3, C) [(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J9: mhd (Γ0 ++ x0 ++ C0 :: Γ3, C) = mhd (Γ0 ++ x0 ++ C0 :: Γ3, C)). reflexivity.
        assert (J10 : (Γ0 ++ x0 ++ C0 :: Γ3, C) = (Γ0 ++ x0 ++ C0 :: Γ3, C)). reflexivity.
        pose (@SIH (mhd (Γ0 ++ x0 ++ C0 :: Γ3, C)) l (Box A0) (Γ0 ++ x0 ++ C0 :: Γ3, C)
        Γ0 (x0 ++ C0 :: Γ3) C J8 J9 J10 d1 X7).
        destruct (dec_init_rules ((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B)).
        +  apply derI with (ps:=[(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)]).
            apply ImpImpL. assert (Γ0 ++ x0 ++ B → C0 :: Γ3 = (Γ0 ++ x0) ++ B → C0 :: Γ3). rewrite <- app_assoc. auto.
            rewrite H2. assert (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3 = (Γ0 ++ x0) ++ (A → B) → C0 :: Γ3).  rewrite <- app_assoc. auto.
            rewrite H3. assert (Γ0 ++ x0 ++ C0 :: Γ3 = (Γ0 ++ x0) ++ C0 :: Γ3). rewrite <- app_assoc. auto.
            rewrite H4. apply ImpImpLRule_I. apply dlCons ; auto. destruct s. inversion i. rewrite <- app_assoc in H2. rewrite <- H2. rewrite <- H4.
            apply Id_all_form. apply derI with (ps:=[]). apply BotL. rewrite <- app_assoc in b. auto. auto. apply dlCons ; auto.
        +  assert (J32: ImpRRule [((Γ0 ++ Box A0 :: x0) ++ A :: B → C0 :: Γ3, B)] ((Γ0 ++ Box A0 :: x0) ++ B → C0 :: Γ3, A → B)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J32. simpl in J32.
            pose (ImpR_inv (Γ0 ++ Box A0 :: x0 ++ B → C0 :: Γ3, A → B) (Γ0 ++ Box A0 :: x0 ++ A:: B → C0 :: Γ3, B) X5 J32).
            assert (J21: In (Γ0 ++ x0 ++ B → C0 :: Γ3, A → B) [(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J33: ImpRRule [((Γ0 ++ x0) ++ A :: B → C0 :: Γ3, B)] ((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J33. simpl in J33.
            assert (J34: In (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B) [(Γ0 ++ x0 ++ A:: B → C0 :: Γ3, B)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J35: ImpRRule [((Γ0 ++ x0) ++ A :: B → C0 :: Γ3, B)] ((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in f0.
            assert (J36: PSGL4ip_rules [(Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)] (Γ0 ++ x0 ++ B → C0 :: Γ3, A → B)).
            apply PSImpR ; try intro ; try apply f0 ; try auto ; try assumption. apply ImpR in J35.
            pose (RA_mhd_decreases J36 _ J34).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J6: mhd (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B) = mhd (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)). reflexivity.
            assert (J7 : (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)= (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)). reflexivity.
            assert (J37: mhd (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B) < mhd (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3, C)). lia.
            pose (@SIH (mhd (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)) J37 (Box A0) (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)
            Γ0 (x0 ++ A :: B → C0 :: Γ3) B J5 J6 J7 d0 d3).
            apply derI with (ps:=[(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)]).
            apply ImpImpL. assert (Γ0 ++ x0 ++ B → C0 :: Γ3 = (Γ0 ++ x0) ++ B → C0 :: Γ3). rewrite <- app_assoc. auto.
            rewrite H2. assert (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3 = (Γ0 ++ x0) ++ (A → B) → C0 :: Γ3).  rewrite <- app_assoc. auto.
            rewrite H3. assert (Γ0 ++ x0 ++ C0 :: Γ3 = (Γ0 ++ x0) ++ C0 :: Γ3). rewrite <- app_assoc. auto.
            rewrite H4. apply ImpImpLRule_I. apply dlCons ; auto.
            apply derI with (ps:=[(Γ0 ++ x0 ++ A:: B → C0 :: Γ3, B)]). apply ImpR ; auto. apply dlCons ; auto.
            apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f.
        assert (ImpImpLRule [(Γ2 ++ B → C0 :: x ++ Γ1, A → B);(Γ2 ++ C0 :: x ++ Γ1, C)] (Γ2 ++ (A → B) → C0 :: x ++ Γ1, C)). apply ImpImpLRule_I.
        assert (J3: PSGL4ip_rules [(Γ2 ++ B → C0 :: x ++ Γ1, A → B);(Γ2 ++ C0 :: x ++ Γ1, C)] (Γ2 ++ (A → B) → C0 :: x ++ Γ1, C)).
        apply PSImpImpL ; try intro ; try apply f ; try auto ; try assumption. apply ImpImpL in H0. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0) = (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0)). auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        assert (J31: ctr_L (B → C0) (Γ2 ++ A :: B → C0 :: B → C0 :: x ++ Γ1, Box A0) (Γ2 ++ A :: B → C0 :: x ++ Γ1, Box A0)).
        assert (Γ2 ++ A :: B → C0 :: B → C0 :: x ++ Γ1 = (Γ2 ++ [A]) ++ B → C0 :: [] ++ B → C0 :: x ++ Γ1). repeat rewrite <- app_assoc. auto.
        rewrite H2.
        assert (Γ2 ++ A :: B → C0 :: x ++ Γ1 = (Γ2 ++ [A]) ++ B → C0 :: [] ++ x ++ Γ1). repeat rewrite <- app_assoc. auto.
        rewrite H3. apply ctr_LI. pose (@GL4ip_adm_ctr_L _ d _ _ J31).
        assert (J01: ImpImpLRule [(Γ2 ++ B → C0 :: x ++ Γ1, A → B);(Γ2 ++ C0 :: x ++ Γ1, Box A0)] (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0)). apply ImpImpLRule_I.
        pose (ImpImpL_inv_R (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0) (Γ2 ++ B → C0 :: x ++ Γ1, A → B) (Γ2 ++ C0 :: x ++ Γ1, Box A0) D0 J01).
        assert (J22: In  (Γ2 ++ C0 :: x ++ Γ1, C) [(Γ2 ++ B → C0 :: x ++ Γ1, A → B); (Γ2 ++ C0 :: x ++ Γ1, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J22).
        assert (J8: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J9: mhd (Γ2 ++ C0 :: x ++ Γ1, C) = mhd (Γ2 ++ C0 :: x ++ Γ1, C)). reflexivity.
        assert (J10 : (Γ2 ++ C0 :: x ++ Γ1, C) = (Γ2 ++ C0 :: x ++ Γ1, C)). reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ2 ++ C0 :: x ++ Γ1, C)) l (Box A0) (Γ2 ++ C0 :: x ++ Γ1, C)
        (Γ2 ++ C0 :: x) Γ1 C J8 J9). repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 J10 d1 X7).
        destruct (dec_init_rules (Γ2 ++ B → C0 :: x ++ Γ1, A → B)).
        +  apply derI with (ps:=[(Γ2 ++ B → C0 :: x ++ Γ1, A → B); (Γ2 ++ C0 :: x ++ Γ1, C)]).
            apply ImpImpL. apply ImpImpLRule_I. apply dlCons ; auto. destruct s. inversion i.
            apply Id_all_form. apply derI with (ps:=[]). apply BotL. auto. auto. apply dlCons ; auto.
        +  assert (J32: ImpRRule [(Γ2 ++ A :: B → C0 :: x ++ Box A0 :: Γ1, B)] (Γ2 ++ B → C0 :: x ++ Box A0 :: Γ1, A → B)). apply ImpRRule_I.
            pose (ImpR_inv (Γ2 ++ B → C0 :: x ++ Box A0 :: Γ1, A → B) (Γ2 ++ A :: B → C0 :: x ++ Box A0 :: Γ1, B) X5 J32).
            assert (J21: In (Γ2 ++ B → C0 :: x ++ Γ1, A → B) [(Γ2 ++ B → C0 :: x ++ Γ1, A → B); (Γ2 ++ C0 :: x ++ Γ1, C)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J33: ImpRRule [(Γ2 ++ A :: B → C0 :: x ++ Γ1,  B)] (Γ2 ++ B → C0 :: x ++ Γ1, A → B)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in J33. simpl in J33.
            assert (J34: In (Γ2 ++ A :: B → C0 :: x ++ Γ1,  B) [(Γ2 ++ A :: B → C0 :: x ++ Γ1,  B)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21).
            assert (J35: ImpRRule [(Γ2 ++ A :: B → C0 :: x ++ Γ1,  B)] (Γ2 ++ B → C0 :: x ++ Γ1, A → B)). apply ImpRRule_I.
            repeat rewrite <- app_assoc in f0.
            assert (J36: PSGL4ip_rules [(Γ2 ++ A :: B → C0 :: x ++ Γ1, B)] (Γ2 ++ B → C0 :: x ++ Γ1, A → B)).
            apply PSImpR ; try intro ; try apply f0 ; try auto ; try assumption. apply ImpR in J35.
            pose (RA_mhd_decreases J36 _ J34).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J6: mhd (Γ2 ++ A :: B → C0 :: x ++ Γ1, B) = mhd (Γ2 ++ A :: B → C0 :: x ++ Γ1, B)). reflexivity.
            assert (J7 : (Γ2 ++ A :: B → C0 :: x ++ Γ1, B) = (Γ2 ++ A :: B → C0 :: x ++ Γ1, B)). reflexivity.
            assert (J37: mhd (Γ2 ++ A :: B → C0 :: x ++ Γ1, B) < mhd (Γ2 ++ (A → B) → C0 :: x ++ Γ1, C)). lia.
            pose (@SIH (mhd (Γ2 ++ A :: B → C0 :: x ++ Γ1, B)) J37 (Box A0) (Γ2 ++ A :: B → C0 :: x ++ Γ1, B)
            (Γ2 ++ A :: B → C0 :: x) Γ1 B J5 J6). repeat rewrite <- app_assoc in d5. pose (d5 J7 d0 d4).
            apply derI with (ps:=[(Γ2 ++ B → C0 :: x ++ Γ1, A → B); (Γ2 ++ C0 :: x ++ Γ1, C)]).
            apply ImpImpL. apply ImpImpLRule_I. apply dlCons ; auto.
            apply derI with (ps:=[(Γ2 ++ A :: B → C0 :: x ++ Γ1, B)]). apply ImpR ; auto. apply dlCons ; auto.
            apply dlCons ; auto. }
    (* Right rule is BoxImpL *)
    { inversion X5. subst. inversion X0. subst. clear X8. clear X0. inversion X2. subst. inversion X8. subst. clear X10.
      clear X8.
      pose (univ_gen_ext_splitR _ _ X4). repeat destruct s. repeat destruct p.
      pose (univ_gen_ext_splitR _ _ X6). repeat destruct s. repeat destruct p. subst.
      apply list_split_form in H2. destruct H2 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s ; repeat destruct p ; subst.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p.
        repeat rewrite <- app_assoc in u1. pose (univ_gen_ext_splitR _ _ u1). repeat destruct s. repeat destruct p. subst.
        simpl in u6. clear u0. clear u1. inversion u4. subst. exfalso.
        assert (In (Box A → B) (x ++ x3 ++ Box A → B :: l)). apply in_or_app. right. apply in_or_app. right. apply in_eq.
        pose (H1 (Box A → B) H). destruct e. inversion H0. subst. clear u4. inversion u6.
        subst. clear u6. repeat rewrite <- app_assoc in X9. simpl in X9.
        assert (J0: BoxImpLRule [(XBoxed_list (x6 ++ x3 ++ x2) ++ [Box A], A);((Γ0 ++ x4) ++ B :: Γ3, C)] ((Γ0 ++ x4) ++ Box A → B :: Γ3, C)).
        apply BoxImpLRule_I. intro. intros. apply in_app_or in H. destruct H. apply H4. apply in_or_app. left.
        apply in_or_app. auto. apply in_app_or in H. destruct H. apply H1. apply in_or_app. right. apply in_or_app. auto.
        apply H4. apply in_or_app ; auto. repeat rewrite <- app_assoc. apply univ_gen_ext_combine ; auto.
        apply univ_gen_ext_combine ; auto. repeat rewrite <- app_assoc in J0.
        assert (J3: PSGL4ip_rules [(XBoxed_list (x6 ++ x3 ++ x2) ++ [Box A], A); (Γ0 ++ x4 ++ B :: Γ3, C)] (Γ0 ++ x4 ++ Box A → B :: Γ3, C)).
        apply PSBoxImpL ; try intro ; try apply f ; try auto ; try assumption. apply BoxImpL in J0.
        assert (J70: derrec_height D0 = derrec_height D0). auto.
        assert (J71: (Γ0 ++ x4 ++ Box A → B :: Γ3, Box A0) = ((Γ0 ++ x4) ++ Box A → B :: Γ3, Box A0)).
        rewrite <- app_assoc ; auto.
        assert (J80: weight_form (Box A → B) = weight_form (Box A → B)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J80 J70 J71). repeat rewrite <- app_assoc in d.
        assert (J21: In (Γ0 ++ x4 ++ B :: Γ3, C) [(XBoxed_list (x6 ++ x3 ++ x2) ++ [Box A], A); (Γ0 ++ x4 ++ B :: Γ3, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ0 ++ x4 ++ B :: Γ3, C) = mhd (Γ0 ++ x4 ++ B :: Γ3, C)). reflexivity.
        assert (J7 : (Γ0 ++ x4 ++ B :: Γ3, C) = (Γ0 ++ x4 ++ B :: Γ3, C)). reflexivity.
        pose (@SIH (mhd  (Γ0 ++ x4 ++ B :: Γ3, C)) l0 (Box A0) (Γ0 ++ x4 ++ B :: Γ3, C)
        Γ0 (x4 ++ B :: Γ3) C J5 J6 J7 d X9).
        assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list (x6 ++ x3 ++ x2) ++ [Box A], A)).
        { assert (x = x6). { apply nobox_gen_ext_injective with (l:=Γ0) ; auto. intro ; intros. apply H4. apply in_or_app. left.
                                      apply in_or_app ; auto. intro ; intros. apply H1. apply in_or_app ;auto. }
          assert (x2 = x5). { apply nobox_gen_ext_injective with (l:=Γ3) ; auto. intro ; intros. apply H1. apply in_or_app. right.
                                       apply in_or_app ; auto. intro ; intros. apply H4. apply in_or_app ;auto. }
          assert (x3 = l). { apply nobox_gen_ext_injective with (l:=x4) ; auto. intro ; intros. apply H4. apply in_or_app. left. apply in_or_app. right.
                                     apply in_cons ; auto. intro ; intros. apply H1. apply in_or_app ; right. apply in_or_app ; auto. }
          subst.
          assert (J22: In (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], A) [(XBoxed_list (x6 ++ l ++ x5) ++ [Box A], A); (Γ0 ++ x4 ++ B :: Γ3, C)]). apply in_eq.
          pose (RA_mhd_decreases J3 _ J22).
          assert (J23: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
          assert (J24: mhd (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], A) = mhd (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], A)). reflexivity.
          assert (J25 : (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], A) = (XBoxed_list x6 ++ XBoxed_list (l ++ x5) ++ [Box A], A)).
          repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. reflexivity.
          pose (@SIH (mhd  (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], A)) l1 (Box A0) (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], A)
          (XBoxed_list x6) (XBoxed_list (l ++ x5) ++ [Box A]) A J23 J24 J25).
          assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list x6 ++ XBoxed_list (l ++ x5) ++ [Box A], Box A0)).
          { assert (XBoxed_list x6 ++ XBoxed_list (l ++ x5) ++ [Box A] = XBoxed_list (x6 ++ l ++ x5) ++ [Box A]). repeat rewrite XBox_app_distrib.
            repeat rewrite <- app_assoc. auto. rewrite H. clear H.
            assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (x6 ++ l ++ x5,  Box A0)).
            apply derI with (ps:=[(XBoxed_list (x6 ++ l ++ x5) ++ [Box A0], A0)]). apply GLR. apply GLRRule_I ; auto.
            apply univ_gen_ext_refl. apply dlCons ; auto.
            pose (@GL4ip_XBoxed_list_wkn_L (derrec_height X11) (x6 ++ l ++ x5) [] [] (Box A0)). simpl in s.
            repeat rewrite app_nil_r in s. assert (J50: derrec_height X11 = derrec_height X11). auto. pose (s X11 J50).
            destruct s0. clear l2.
            assert (J51: wkn_L (Box A) (XBoxed_list (x6 ++ l ++ x5), Box A0) (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], Box A0)).
            assert (XBoxed_list (x6 ++ l ++ x5) = XBoxed_list (x6 ++ l ++ x5) ++ []). rewrite app_nil_r. auto. rewrite H.
            assert ((XBoxed_list (x6 ++ l ++ x5) ++ []) ++ [Box A] = XBoxed_list (x6 ++ l ++ x5) ++ Box A :: []). repeat rewrite <- app_assoc. auto. rewrite H0.
            apply wkn_LI.
            pose (@GL4ip_adm_wkn_L (XBoxed_list (x6 ++ l ++ x5), Box A0) x (XBoxed_list (x6 ++ l ++ x5) ++ [Box A], Box A0) (Box A) J51). auto. }
          apply d1. auto.
          assert (J60: weight_form A0 < weight_form (Box A0)). simpl. lia.
          assert (J61: weight_form A0 = weight_form A0). auto.
          assert (J62: mhd (XBoxed_list x6 ++ Box A0 :: XBoxed_list (l ++ x5) ++ [Box A], A) = mhd (XBoxed_list x6 ++ Box A0 :: XBoxed_list (l ++ x5) ++ [Box A], A)).
          auto.
          assert (J63: (XBoxed_list x6 ++ Box A0 :: XBoxed_list (l ++ x5) ++ [Box A], A) = (XBoxed_list x6 ++ Box A0 :: XBoxed_list (l ++ x5) ++ [Box A], A)). auto.
          pose (PIH (weight_form A0) J60 (mhd (XBoxed_list x6 ++ Box A0 :: XBoxed_list (l ++ x5) ++ [Box A], A))
          A0 (XBoxed_list x6 ++ Box A0 :: XBoxed_list (l ++ x5) ++ [Box A], A) (XBoxed_list x6) (Box A0 :: XBoxed_list (l ++ x5) ++ [Box A])
          A J61 J62 J63). apply d2.
          apply GL4ip_adm_list_exch_L with (s:=(XBoxed_list x6 ++ Box A :: XBoxed_list (l ++ x5) ++ [Box A0], A0)).
          apply GL4ip_adm_wkn_L with (s:=(XBoxed_list x6 ++ XBoxed_list (l ++ x5) ++ [Box A0], A0)) (A:=Box A).
          repeat rewrite XBox_app_distrib in X7. rewrite XBox_app_distrib. repeat rewrite <- app_assoc in X7.
          repeat rewrite <- app_assoc. auto. apply wkn_LI.
          assert (XBoxed_list x6 ++ Box A :: XBoxed_list (l ++ x5) ++ [Box A0] = (XBoxed_list x6) ++ [Box A] ++ XBoxed_list (l ++ x5) ++ [Box A0] ++ []).
          repeat rewrite <- app_assoc. auto. rewrite H.
          assert (XBoxed_list x6 ++ Box A0 :: XBoxed_list (l ++ x5) ++ [Box A] = (XBoxed_list x6) ++ [Box A0] ++ XBoxed_list (l ++ x5) ++ [Box A] ++ []).
          repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. repeat rewrite XBox_app_distrib in X0.
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in X0. simpl in X0. auto. }
        apply derI with (ps:=[(XBoxed_list (x6 ++ x3++ x2) ++ [Box A], A); (Γ0 ++ x4 ++ B :: Γ3, C)]) ; auto.
        apply dlCons ; auto. apply dlCons ; auto. subst.
        exfalso. apply H3. exists A0. auto.
      - repeat destruct s ; repeat destruct p ; subst.
        pose (univ_gen_ext_splitR _ _ u). repeat destruct s. repeat destruct p. subst. clear u.
        pose (univ_gen_ext_splitR _ _ u2). repeat destruct s. repeat destruct p. subst. clear u2.
        inversion u4. subst. exfalso.
        assert (In (Box A → B) ((x4 ++ Box A → B :: l) ++ x0)). apply in_or_app. left. apply in_or_app. right. apply in_eq.
        pose (H1 (Box A → B) H). destruct e. inversion H0. subst. clear u4. inversion u5.
        subst. clear u5. repeat rewrite <- app_assoc in X7. repeat rewrite <- app_assoc. simpl.
        assert (J0: BoxImpLRule [(XBoxed_list (x1 ++ x ++ l) ++ [Box A], A);(Γ2 ++ B :: x3 ++ Γ1, C)] (Γ2 ++ Box A → B :: x3 ++ Γ1, C)).
        apply BoxImpLRule_I ; auto. intro. intros. apply in_app_or in H. destruct H. apply H4. apply in_or_app. auto.
        apply in_app_or in H. destruct H. apply H4. apply in_or_app. right. apply in_or_app. auto.
        apply H4. apply in_or_app. right. apply in_or_app. right. apply in_cons ; auto.
        apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto.
        assert (x1 = x4).  { apply nobox_gen_ext_injective with (l:=Γ2) ; auto. intro ; intros. apply H1. apply in_or_app. left.
                                      apply in_or_app ; auto. intro ; intros. apply H4. apply in_or_app ;auto. }
        assert (l = x0). { apply nobox_gen_ext_injective with (l:=Γ1) ; auto. intro ; intros. apply H1. apply in_or_app ; auto.
                                   intro ; intros. apply H4. apply in_or_app. right.  apply in_or_app. right. apply in_cons ;auto. }
        assert (x = x5).   { apply nobox_gen_ext_injective with (l:=x3) ; auto. intro ; intros. apply H1. apply in_or_app ; left. apply in_or_app ; auto.
                                   intro ; intros. apply H4. apply in_or_app. right.  apply in_or_app ; auto. }
        subst. repeat rewrite <- app_assoc in f.
        assert (J3: PSGL4ip_rules [(XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A); (Γ2 ++ B :: x3 ++ Γ1, C)] (Γ2 ++ Box A → B :: x3 ++ Γ1, C)).
        apply PSBoxImpL ; try intro ; try apply f ; try auto ; try assumption. apply BoxImpL in J0. repeat rewrite <- app_assoc in D0.
        assert (J4: derrec_height D0 = derrec_height D0). auto. simpl in D0.
        assert (J71: (Γ2 ++ Box A → B :: x3 ++ Γ1, Box A0) = (Γ2 ++ Box A → B :: x3 ++ Γ1, Box A0)).
        auto.
        assert (J80: weight_form (Box A → B) = weight_form (Box A → B)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J80 J4 J71).
        assert (J21: In (Γ2 ++ B :: x3 ++ Γ1, C) [(XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A); (Γ2 ++ B :: x3 ++ Γ1, C)]). apply in_cons. apply in_eq.
        pose (RA_mhd_decreases J3 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J6: mhd (Γ2 ++ B :: x3 ++ Γ1, C) = mhd (Γ2 ++ B :: x3 ++ Γ1, C)). reflexivity.
        assert (J7 : (Γ2 ++ B :: x3 ++ Γ1, C) = (Γ2 ++ B :: x3 ++ Γ1, C)). reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (@SIH (mhd (Γ2 ++ B :: x3 ++ Γ1, C)) l (Box A0) (Γ2 ++ B :: x3 ++ Γ1, C)
        (Γ2 ++ B :: x3) Γ1 C J5 J6). repeat rewrite <- app_assoc in d0. pose (d0 J7 d X9).
        assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A)).
        { assert (J22: In (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A) [(XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A); (Γ2 ++ B :: x3 ++ Γ1, C)]). apply in_eq.
          pose (RA_mhd_decreases J3 _ J22).
          assert (J23: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
          assert (J24: mhd (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A) = mhd (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A)). reflexivity.
          assert (J25 : (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A) = (XBoxed_list (x4 ++ x5) ++ XBoxed_list x0 ++ [Box A], A)).
          repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. reflexivity.
          pose (@SIH (mhd  (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A)) l0 (Box A0) (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A)
          (XBoxed_list (x4 ++ x5)) (XBoxed_list x0 ++ [Box A]) A J23 J24 J25).
          assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (XBoxed_list (x4 ++ x5) ++ XBoxed_list x0 ++ [Box A], Box A0)).
          { assert (XBoxed_list (x4 ++ x5) ++ XBoxed_list x0 ++ [Box A] = XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A]). repeat rewrite XBox_app_distrib.
            repeat rewrite <- app_assoc. auto. rewrite H. clear H.
            assert (derrec GL4ip_rules (fun _ : list (MPropF) * MPropF => False) (x4 ++ x5 ++ x0,  Box A0)).
            apply derI with (ps:=[(XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A0], A0)]). apply GLR. apply GLRRule_I ; auto.
            intro. intros. apply H1. repeat rewrite <- app_assoc. auto. apply univ_gen_ext_refl. apply dlCons ; auto.
            pose (@GL4ip_XBoxed_list_wkn_L (derrec_height X11) (x4 ++ x5 ++ x0) [] [] (Box A0)). simpl in s.
            repeat rewrite app_nil_r in s. assert (J50: derrec_height X11 = derrec_height X11). auto. pose (s X11 J50).
            destruct s0. clear l1.
            assert (J51: wkn_L (Box A) (XBoxed_list (x4 ++ x5 ++ x0), Box A0) (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], Box A0)).
            assert (XBoxed_list (x4 ++ x5 ++ x0) = XBoxed_list (x4 ++ x5 ++ x0) ++ []). rewrite app_nil_r. auto. rewrite H.
            assert ((XBoxed_list (x4 ++ x5 ++ x0) ++ []) ++ [Box A] = XBoxed_list (x4 ++ x5 ++ x0) ++ Box A :: []). repeat rewrite <- app_assoc. auto. rewrite H0.
            apply wkn_LI.
            pose (@GL4ip_adm_wkn_L (XBoxed_list (x4 ++ x5 ++ x0), Box A0) x (XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], Box A0) (Box A) J51). auto. }
          apply d2 ; auto.
          assert (J60: weight_form A0 < weight_form (Box A0)). simpl. lia.
          assert (J61: weight_form A0 = weight_form A0). auto.
          assert (J62: mhd (XBoxed_list (x4 ++ x5) ++ Box A0 :: XBoxed_list x0 ++ [Box A], A) = mhd (XBoxed_list (x4 ++ x5) ++ Box A0 :: XBoxed_list x0 ++ [Box A], A)).
          auto.
          assert (J63: (XBoxed_list (x4 ++ x5) ++ Box A0 :: XBoxed_list x0 ++ [Box A], A) = (XBoxed_list (x4 ++ x5) ++ Box A0 :: XBoxed_list x0 ++ [Box A], A)). auto.
          pose (PIH (weight_form A0) J60 (mhd (XBoxed_list (x4 ++ x5) ++ Box A0 :: XBoxed_list x0 ++ [Box A], A))
          A0 (XBoxed_list (x4 ++ x5) ++ Box A0 :: XBoxed_list x0 ++ [Box A], A) (XBoxed_list (x4 ++ x5)) (Box A0 :: XBoxed_list x0 ++ [Box A])
          A J61 J62 J63). apply d3.
          apply GL4ip_adm_list_exch_L with (s:=(XBoxed_list  (x4 ++ x5) ++ Box A :: XBoxed_list x0 ++ [Box A0], A0)).
          apply GL4ip_adm_wkn_L with (s:=(XBoxed_list (x4 ++ x5) ++ XBoxed_list x0 ++ [Box A0], A0)) (A:=Box A).
          repeat rewrite XBox_app_distrib in X7. rewrite XBox_app_distrib. repeat rewrite <- app_assoc in X7.
          repeat rewrite <- app_assoc. auto. apply wkn_LI.
          assert (XBoxed_list (x4 ++ x5) ++ Box A :: XBoxed_list x0 ++ [Box A0] = (XBoxed_list (x4 ++ x5)) ++ [Box A] ++ XBoxed_list x0 ++ [Box A0] ++ []).
          repeat rewrite <- app_assoc. auto. rewrite H.
          assert (XBoxed_list (x4 ++ x5) ++ Box A0 :: XBoxed_list x0 ++ [Box A] = (XBoxed_list (x4 ++ x5)) ++ [Box A0] ++ XBoxed_list x0 ++ [Box A] ++ []).
          repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. repeat rewrite XBox_app_distrib in X0.
          repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in X0. simpl in X0. auto. }
        apply derI with (ps:=[(XBoxed_list (x4 ++ x5 ++ x0) ++ [Box A], A); (Γ2 ++ B :: x3 ++ Γ1, C)]) ; auto.
        apply dlCons ; auto. apply dlCons ; auto. subst.
        exfalso. apply H3. exists A0. auto. }
    (* Right rule is GLR *)
    { inversion X5. subst. inversion X0. subst. clear X8. inversion X2. subst. clear X9.
      pose (univ_gen_ext_splitR _ _ X4). repeat destruct s. repeat destruct p.
      pose (univ_gen_ext_splitR _ _ X6). repeat destruct s. repeat destruct p. subst. inversion u2.
      - subst.
        assert ((XBoxed_list (x ++ x0) ++ [Box A0], A0) = ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [], A0)).
        repeat rewrite <- app_assoc. reflexivity.
        assert (X7': derrec GL4ip_rules (fun _ : Seq => False) ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [], A0)).
        rewrite <- H. assumption.
        assert (J1: wkn_L (Box A) ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [], A0) ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ (Box A) :: [], A0)).
        apply wkn_LI. assert (J2: derrec_height X7' = derrec_height X7'). reflexivity.
        pose (GL4ip_wkn_L _ J2 J1). destruct s. clear l0. clear J2. clear X7'. clear J1. clear H.
        rewrite XBox_app_distrib in x2. repeat rewrite <- app_assoc in x2.
        rewrite XBox_app_distrib in X8. repeat rewrite <- app_assoc in X8. simpl in X8.
        assert ((XBoxed_list x1 ++ A0 :: Box A0 :: XBoxed_list l ++ [Box A], A) =
        (XBoxed_list x1 ++ (A0 :: [Box A0]) ++ [] ++ XBoxed_list l ++ [Box A], A)).
        reflexivity. rewrite H in X8. clear H.
        assert (J5: list_exch_L (XBoxed_list x1 ++ [A0; Box A0] ++ [] ++ XBoxed_list l ++ [Box A], A)
        (XBoxed_list x1 ++ XBoxed_list l ++ [] ++ [A0; Box A0] ++ [Box A], A)).
        apply list_exch_LI.
        pose (GL4ip_adm_list_exch_L _ X8 _ J5). simpl in d. rewrite app_assoc in d.
        rewrite <- XBox_app_distrib in d. assert (x1 ++ l = x ++ x0).
        apply nobox_gen_ext_injective with (l:=(Γ0 ++ Γ1)) ; try assumption.
        intro. intros. apply H4. apply in_or_app. apply in_app_or in H. destruct H.
        auto. right. apply in_cons. assumption. apply univ_gen_ext_combine ; assumption.
        rewrite H in d. clear J5. clear X8. simpl in x2. rewrite app_assoc in x2.
        rewrite <- XBox_app_distrib in x2.
        assert (J6: weight_form A0 < weight_form (Box A0)). simpl. lia.
        assert (J7: weight_form A0 = weight_form A0). reflexivity.
        assert (J8: mhd (XBoxed_list (x ++ x0) ++ [Box A0; Box A], A) =
        mhd (XBoxed_list (x ++ x0) ++ [Box A0; Box A], A)). reflexivity.
        assert (J9: (XBoxed_list (x ++ x0) ++ [Box A0; Box A], A) =
        (XBoxed_list (x ++ x0) ++ [Box A0; Box A], A)). reflexivity.
        pose (@PIH (weight_form A0) J6 (mhd (XBoxed_list (x ++ x0) ++ [Box A0; Box A], A))
        A0 (XBoxed_list (x ++ x0) ++ [Box A0; Box A], A) (XBoxed_list (x ++ x0)) (Box A0 :: [Box A])
        A J7 J8 J9). pose (d0 x2 d).
        assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A0], A0)] (x ++ x0, Box A0)).
        apply GLRRule_I ; auto. apply univ_gen_ext_refl. apply GLR in X8.
        pose (dlCons X7 DersNilF).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(XBoxed_list (x ++ x0) ++ [Box A0], A0)]) (x ++ x0, Box A0) X8 d2).
        assert (J20: derrec_height d3 = derrec_height d3). reflexivity.
        pose (@GL4ip_XBoxed_list_wkn_L (derrec_height d3) (x ++ x0) [] [] (Box A0)).
        repeat rewrite app_nil_r in s. repeat rewrite app_nil_l in s. pose (s d3 J20).
        destruct s0. clear l0. clear J20. clear s. clear d3.
        assert (XBoxed_list (x ++ x0) = XBoxed_list (x ++ x0) ++ []). rewrite app_nil_r. reflexivity.
        rewrite H0 in x3. clear H0.
        assert (wkn_L (Box A) (XBoxed_list (x ++ x0) ++ [], Box A0) (XBoxed_list (x ++ x0) ++ (Box A) :: [], Box A0)).
        apply wkn_LI.
        assert (J10: derrec_height x3 = derrec_height x3). reflexivity.
        pose (GL4ip_wkn_L _ J10 H0). destruct s. clear l0. clear J10. clear x3. clear H0.
        assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A], A)] (Γ0 ++ Γ1, Box A)).
        apply GLRRule_I ; try assumption.
        assert (PSGL4ip_rules [(XBoxed_list (x ++ x0) ++ [Box A], A)] (Γ0 ++ Γ1, Box A)).
        apply PSGLR ; try intro ; try apply f ; try rewrite H5 ; try auto ; try assumption.
        assert (J40: GL4ip_rules [(XBoxed_list (x ++ x0) ++ [Box A], A)] (Γ0 ++ Γ1, Box A)).
        apply GLR ; try assumption.
        assert (l0: mhd (XBoxed_list (x ++ x0) ++ [Box A], A) < mhd (Γ0 ++ Γ1, Box A)).
        assert (J30 : In (XBoxed_list (x ++ x0) ++ [Box A], A) [(XBoxed_list (x ++ x0) ++ [Box A], A)]).
        apply in_eq. pose (RA_mhd_decreases X11 _ J30). assumption.
        assert (J10: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J11: mhd (XBoxed_list (x ++ x0) ++ [Box A], A) = mhd (XBoxed_list (x ++ x0) ++ [Box A], A)). reflexivity.
        assert (J12: (XBoxed_list (x ++ x0) ++ [Box A], A) = (XBoxed_list (x ++ x0) ++ [Box A],A) ). reflexivity.
        pose (@SIH (mhd (XBoxed_list (x ++ x0) ++ [Box A], A)) l0 (Box A0) (XBoxed_list (x ++ x0) ++ [Box A], A)
        (XBoxed_list (x ++ x0)) [Box A] A J10 J11 J12). simpl in d3. pose (d3 x4 d1). pose (dlCons d4 DersNilF).
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[(XBoxed_list (x ++ x0) ++ [Box A], A)]) (Γ0 ++ Γ1, Box A) J40 d5). auto.
      - exfalso. apply H2. exists A0. reflexivity. } }
Qed.

Theorem GL4ip_cut_adm0 : forall A Γ0 Γ1 C,
                      GL4ip_prv (Γ0 ++ Γ1, A) ->
                      GL4ip_prv (Γ0 ++ A :: Γ1, C) ->
                      GL4ip_prv (Γ0 ++ Γ1, C).
Proof.
intros.
assert (J1: weight_form A = weight_form A). reflexivity.
assert (J2: mhd (Γ0 ++ Γ1, C) = mhd (Γ0 ++ Γ1, C)). reflexivity.
assert (J3: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). reflexivity.
pose (@GL4ip_cut_adm_main (weight_form A) (mhd (Γ0 ++ Γ1, C)) A
(Γ0 ++ Γ1, C) Γ0 Γ1 C J1 J2 J3). unfold GL4ip_prv. auto.
Qed.

Theorem GL4ip_cut_adm : forall A Γ0 Γ1 C,
                      (GL4ip_prv (Γ0 ++ Γ1, A) * GL4ip_prv (Γ0 ++ A :: Γ1, C)) ->
                      GL4ip_prv (Γ0 ++ Γ1, C).
Proof.
intros.
assert (J1: weight_form A = weight_form A). reflexivity.
assert (J2: mhd (Γ0 ++ Γ1, C) = mhd (Γ0 ++ Γ1, C)). reflexivity.
assert (J3: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). reflexivity.
pose (@GL4ip_cut_adm_main (weight_form A) (mhd (Γ0 ++ Γ1, C)) A
(Γ0 ++ Γ1, C) Γ0 Γ1 C J1 J2 J3). unfold GL4ip_prv. destruct X. auto.
Qed.



