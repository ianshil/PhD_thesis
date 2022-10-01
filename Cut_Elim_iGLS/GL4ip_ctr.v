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
Require Import GL4ip_PSGL4ip_dec.
Require Import GL4ip_exch.
Require Import GL4ip_wkn.
Require Import GL4ip_inv_AndR_AndL.
Require Import GL4ip_inv_OrL.
Require Import GL4ip_inv_AtomImpL.
Require Import GL4ip_inv_AndImpL.
Require Import GL4ip_inv_OrImpL.
Require Import GL4ip_inv_ImpImpL_R.
Require Import GL4ip_inv_ImpImpL_L.
Require Import GL4ip_inv_ImpR.
Require Import GL4ip_inv_BoxImpL_R.
Require Import Lia.

Set Implicit Arguments.

(* Next is the definition for contraction of one formula on the left.
Note that while the leftmost occurrence of the formula is kept,
if we have exchange for our calculus it amounts to the same to keep
the rightmost formula. *)

Inductive ctr_L (fml : MPropF) : relationT Seq :=
  | ctr_LI Γ0 Γ1 Γ2 A : ctr_L fml
        (Γ0 ++ fml :: Γ1 ++ fml :: Γ2, A) (Γ0 ++ fml :: Γ1 ++ Γ2, A).

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent sc which is a contracted
version of s, with some premises psc that are such that they are either the same premises
(in case the contracted formula was weakened) or contracted versions of ps. *)

Lemma AndR_app_ctr_L : forall s sc A ps1 ps2,
  (@ctr_L A s sc) ->
  (AndRRule [ps1;ps2] s) ->
  (existsT2 psc1 psc2, (AndRRule [psc1;psc2] sc) * (@ctr_L A ps1 psc1) * (@ctr_L A ps2 psc2)).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1 ++ Γ2, A0). exists (Γ0 ++ A :: Γ1 ++ Γ2, B). repeat split.
Qed.

Lemma AndL_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AndLRule [ps] s) ->
  ((existsT2 psc, (AndLRule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 B C invps invpsc1 invpsc2,
                       (A = And B C) *
                       (AndLRule [invps] ps) *
                       (@ctr_L B invps invpsc1) *
                       (@ctr_L C invpsc1 invpsc2) *
                       (AndLRule [invpsc2] sc))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
  exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ4, C).
  repeat split.
  assert (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4 = (Γ2 ++ A0 :: B :: Γ3) ++ A0 :: B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H0.
  assert (Γ2 ++ A0 :: B :: Γ3 ++ And A0 B :: Γ4 = (Γ2 ++ A0 :: B :: Γ3) ++ And A0 B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H1. apply AndLRule_I.
  assert (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4 = Γ2 ++ A0 :: (B :: Γ3) ++ A0 :: B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H0.
  assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4 = Γ2 ++ A0 :: (B :: Γ3) ++ B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
  assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H0.
  assert (Γ2 ++ A0 :: B :: Γ3 ++ Γ4 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right.
    exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
    exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ4, C).
    repeat split.
    assert (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4 = (Γ2 ++ A0 :: B :: Γ3) ++ A0 :: B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ2 ++ A0 :: B :: Γ3 ++ And A0 B :: Γ4 = (Γ2 ++ A0 :: B :: Γ3) ++ And A0 B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply AndLRule_I.
    assert (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4 = Γ2 ++ A0 :: (B :: Γ3) ++ A0 :: B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4 = Γ2 ++ A0 :: (B :: Γ3) ++ B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ2 ++ A0 :: B :: Γ3 ++ Γ4 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right.
       exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
       exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ4, C).
       repeat split.
       assert (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4 = Γ2 ++ A0 :: (B :: Γ3) ++ A0 :: B :: Γ4).
       repeat rewrite <- app_assoc ; auto. rewrite H0.
       assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4 = Γ2 ++ A0 :: (B :: Γ3) ++ B :: Γ4).
       repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
       assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ B :: Γ4).
       repeat rewrite <- app_assoc ; auto. rewrite H0.
       assert (Γ2 ++ A0 :: B :: Γ3 ++ Γ4 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ Γ4).
       repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ1, C).
         exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ1, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ1, C).
         repeat split.
         assert (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ1 = Γ2 ++ A0 :: (B :: Γ3) ++ A0 :: B :: Γ1).
         repeat rewrite <- app_assoc ; auto. rewrite H0.
         assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ1 = Γ2 ++ A0 :: (B :: Γ3) ++ B :: Γ1).
         repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
         assert (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ1 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ B :: Γ1).
         repeat rewrite <- app_assoc ; auto. rewrite H0.
         assert (Γ2 ++ A0 :: B :: Γ3 ++ Γ1 = (Γ2 ++ [A0]) ++ B :: Γ3 ++ Γ1).
         repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: B :: Γ1, C). repeat split.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: B :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ A0 :: B :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ And A0 B :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ And A0 B :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
         apply AndLRule_I. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: B :: x ++ A0 :: B :: Γ4, C).
         exists (Γ2 ++ A0 :: B :: x ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: x ++ Γ4, C).
         repeat split.
         assert (Γ2 ++ A0 :: B :: x ++ A0 :: B :: Γ4 = Γ2 ++ A0 :: (B :: x) ++ A0 :: B :: Γ4).
         repeat rewrite <- app_assoc ; auto. rewrite H0.
         assert (Γ2 ++ A0 :: B :: x ++ B :: Γ4 = Γ2 ++ A0 :: (B :: x) ++ B :: Γ4).
         repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
         assert (Γ2 ++ A0 :: B :: x ++ B :: Γ4 = (Γ2 ++ [A0]) ++ B :: x ++ B :: Γ4).
         repeat rewrite <- app_assoc ; auto. rewrite H0.
         assert (Γ2 ++ A0 :: B :: x ++ Γ4 = (Γ2 ++ [A0]) ++ B :: x ++ Γ4).
         repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: x ++ A0 :: B :: x0 ++ Γ4, C). repeat split.
         assert (Γ2 ++ m :: x ++ A0 :: B :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ A0 :: B :: x0 ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: x ++ And A0 B :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ And A0 B :: x0 ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
         apply AndLRule_I.
         assert (Γ2 ++ m :: x ++ A0 :: B :: x0 ++ Γ4 = Γ2 ++ m :: (x ++ A0 :: B :: x0) ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: x ++ A0 :: B :: x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ A0 :: B :: x0) ++ m :: Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI. }
- destruct x.
  * simpl in e0. inversion e0. subst. right.
    exists A0. exists B. exists (Γ0 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
    exists (Γ0 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ0 ++ A0 :: B :: Γ3 ++ Γ4, C).
    repeat split.
    assert (Γ0 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4 = (Γ0 ++ A0 :: B :: Γ3) ++ A0 :: B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ0 ++ A0 :: B :: Γ3 ++ And A0 B :: Γ4 = (Γ0 ++ A0 :: B :: Γ3) ++ And A0 B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply AndLRule_I.
    assert (Γ0 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4 = Γ0 ++ A0 :: (B :: Γ3) ++ A0 :: B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ0 ++ A0 :: B :: Γ3 ++ B :: Γ4 = Γ0 ++ A0 :: (B :: Γ3) ++ B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    assert (Γ0 ++ A0 :: B :: Γ3 ++ B :: Γ4 = (Γ0 ++ [A0]) ++ B :: Γ3 ++ B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ0 ++ A0 :: B :: Γ3 ++ Γ4 = (Γ0 ++ [A0]) ++ B :: Γ3 ++ Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. repeat rewrite <- app_assoc. simpl. apply AndLRule_I.
  * simpl in e0. inversion e0. subst. left.
    repeat rewrite <- app_assoc. simpl.
    exists (Γ0 ++ A0 :: B :: x ++ A :: Γ3 ++ Γ4, C). repeat split.
    assert (Γ0 ++ A0 :: B :: x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ A0 :: B :: x) ++ A :: Γ3 ++ A :: Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ A0 :: B :: x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ A0 :: B :: x) ++ A :: Γ3 ++ Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
Qed.

Lemma OrR1_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (OrR1Rule [ps] s) ->
  (existsT2 psc, (OrR1Rule [psc] sc) * (@ctr_L A ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1 ++ Γ2, A0). repeat split.
Qed.

Lemma OrR2_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (OrR2Rule [ps] s) ->
  (existsT2 psc, (OrR2Rule [psc] sc) * (@ctr_L A ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1 ++ Γ2, B). repeat split.
Qed.

Lemma OrL_app_ctr_L : forall s sc A ps1 ps2,
  (@ctr_L A s sc) ->
  (OrLRule [ps1;ps2] s) ->
  ((existsT2 psc1 psc2, (OrLRule [psc1;psc2] sc) *
                       (@ctr_L A ps1 psc1) *
                       (@ctr_L A ps2 psc2))
  +
  (existsT2 B C invps11 invps12 invps21 invps22 invpsc11 invpsc22,
                       (A = Or B C) *
                       (OrLRule [invps11;invps12] ps1) *
                       (OrLRule [invps21;invps22] ps2) *
                       (@ctr_L B invps11 invpsc11) *
                       (@ctr_L C invps22 invpsc22) *
                       (OrLRule [invpsc11;invpsc22] sc))).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
  exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ4, C).
  exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C).
  exists (Γ2 ++ A0 :: Γ3 ++  Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
  repeat split.
  assert (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ A0 :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H0.
  assert (Γ2 ++ A0 :: Γ3 ++ B :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H1.
  assert (Γ2 ++ A0 :: Γ3 ++ Or A0 B :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ Or A0 B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H2. apply OrLRule_I.
  assert (Γ2 ++ B :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ B :: Γ3) ++ A0 :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H0.
  assert (Γ2 ++ B :: Γ3 ++ B :: Γ4 = (Γ2 ++ B :: Γ3) ++ B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H1.
  assert (Γ2 ++ B :: Γ3 ++ Or A0 B :: Γ4 = (Γ2 ++ B :: Γ3) ++ Or A0 B :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H2. apply OrLRule_I.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right.
    exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C).
    exists (Γ2 ++ A0 :: Γ3 ++  Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
    repeat split.
    assert (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ A0 :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ2 ++ A0 :: Γ3 ++ B :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1.
    assert (Γ2 ++ A0 :: Γ3 ++ Or A0 B :: Γ4 = (Γ2 ++ A0 :: Γ3) ++ Or A0 B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H2. apply OrLRule_I.
    assert (Γ2 ++ B :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ B :: Γ3) ++ A0 :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ2 ++ B :: Γ3 ++ B :: Γ4 = (Γ2 ++ B :: Γ3) ++ B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1.
    assert (Γ2 ++ B :: Γ3 ++ Or A0 B :: Γ4 = (Γ2 ++ B :: Γ3) ++ Or A0 B :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H2. apply OrLRule_I.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right.
       exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
      exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ4, C). exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ4, C).
      exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C).
      exists (Γ2 ++ A0 :: Γ3 ++  Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
      repeat split.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ1, C). exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ1, C).
         exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ1, C). exists (Γ2 ++ B :: Γ3 ++ B :: Γ1, C).
         exists (Γ2 ++ A0 :: Γ3 ++  Γ1, C). exists (Γ2 ++ B :: Γ3 ++ Γ1, C).
        repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: Γ1, C).  exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ B :: Γ1, C). repeat split.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ A0 :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ B :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ B :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ Or A0 B :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ Or A0 B :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.
         apply OrLRule_I. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: x ++ A0 :: Γ4, C).
         exists (Γ2 ++ B :: x ++ A0 :: Γ4, C). exists (Γ2 ++ A0 :: x ++ B :: Γ4, C).
         exists (Γ2 ++ B :: x ++ B :: Γ4, C).
         exists (Γ2 ++ A0 :: x ++  Γ4, C). exists (Γ2 ++ B :: x ++ Γ4, C).
         repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4, C).  exists (Γ2 ++ m :: x ++ B :: x0 ++ Γ4, C). repeat split.
         assert (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ A0 :: x0 ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: x ++ B :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ B :: x0 ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
         assert (Γ2 ++ m :: x ++ Or A0 B :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ Or A0 B :: x0 ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.
         apply OrLRule_I.
         assert (Γ2 ++ m :: x ++ A0 :: x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ A0 :: x0) ++ m :: Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4 = Γ2 ++ m :: (x ++ A0 :: x0) ++ Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
         assert (Γ2 ++ m :: x ++ B :: x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ B :: x0) ++ m :: Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: x ++ B :: x0 ++ Γ4 = Γ2 ++ m :: (x ++ B :: x0) ++ Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI. }
- destruct x.
  * simpl in e0. inversion e0. subst. right. repeat rewrite <- app_assoc. simpl.
    exists A0. exists B. exists (Γ0 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ0 ++ A0 :: Γ3 ++ B :: Γ4, C). exists (Γ0 ++ B :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ0 ++ B :: Γ3 ++ B :: Γ4, C).
    exists(Γ0 ++ A0 :: Γ3 ++ Γ4, C). exists(Γ0 ++ B :: Γ3 ++ Γ4, C).
    repeat split.
    assert (Γ0 ++ A0 :: Γ3 ++ A0 :: Γ4 = (Γ0 ++ A0 :: Γ3) ++ A0 :: Γ4).
    repeat rewrite <- app_assoc. simpl. auto. rewrite H0.
    assert (Γ0 ++ A0 :: Γ3 ++ B :: Γ4 = (Γ0 ++ A0 :: Γ3) ++ B :: Γ4).
    repeat rewrite <- app_assoc. simpl. auto. rewrite H1.
    assert (Γ0 ++ A0 :: Γ3 ++ Or A0 B :: Γ4 = (Γ0 ++ A0 :: Γ3) ++ Or A0 B :: Γ4).
    repeat rewrite <- app_assoc. simpl. auto. rewrite H2. apply OrLRule_I.
    assert (Γ0 ++ B :: Γ3 ++ A0 :: Γ4 = (Γ0 ++ B :: Γ3) ++ A0 :: Γ4).
    repeat rewrite <- app_assoc. simpl. auto. rewrite H0.
    assert (Γ0 ++ B :: Γ3 ++ B :: Γ4 = (Γ0 ++ B :: Γ3) ++ B :: Γ4).
    repeat rewrite <- app_assoc. simpl. auto. rewrite H1.
    assert (Γ0 ++ B :: Γ3 ++ Or A0 B :: Γ4 = (Γ0 ++ B :: Γ3) ++ Or A0 B :: Γ4).
    repeat rewrite <- app_assoc. simpl. auto. rewrite H2. apply OrLRule_I.
  * simpl in e0. inversion e0. subst. left.
    repeat rewrite <- app_assoc. simpl.
    exists (Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4, C). exists (Γ0 ++ B :: x ++ A :: Γ3 ++ Γ4, C). repeat split.
    assert (Γ0 ++ A0 :: x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ A0 :: x) ++ A :: Γ3 ++ A :: Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ A0 :: x) ++ A :: Γ3 ++ Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
    assert (Γ0 ++ B :: x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ B :: x) ++ A :: Γ3 ++ A :: Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ B :: x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ B :: x) ++ A :: Γ3 ++ Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
Qed.

Lemma ImpR_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (ImpRRule [ps] s) ->
  (existsT2 psc, (ImpRRule [psc] sc) * (@ctr_L A ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A0 :: A :: Γ3 ++ Γ4, B). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. rewrite app_assoc with (l:=Γ2).
  apply ctr_LI.
- destruct x ; subst.
  * simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
     exists (Γ2 ++ A0 :: A :: Γ3 ++ Γ4, B). repeat split.
     rewrite cons_single with (v:=A0). rewrite app_assoc.
     assert (Γ2 ++ A0 :: A :: Γ3 ++ Γ4 = (Γ2 ++ [A0]) ++ A :: Γ3 ++ Γ4).
     repeat rewrite <- app_assoc. auto. rewrite H0. apply ctr_LI.
  * simpl in e0. inversion e0. subst. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
    + repeat rewrite <- app_assoc. simpl.
       exists (Γ2 ++ m :: Γ3 ++ A0 :: Γ4, B). repeat split.
       assert (Γ2 ++ m :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ m :: Γ3) ++ A0 :: Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ m :: Γ3 ++ Γ4 = (Γ2 ++ m :: Γ3) ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H1. apply ImpRRule_I.
       assert (Γ2 ++ m :: Γ3 ++ A0 :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ m :: Γ3 ++ A0 :: m :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ m :: Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
    + destruct x0.
       { simpl in e1. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: Γ3 ++ A0 :: Γ4, B). repeat split.
         assert (Γ2 ++ m :: Γ3 ++ A0 :: Γ4 = (Γ2 ++ m :: Γ3) ++ A0 :: Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: Γ3 ++ Γ4 = (Γ2 ++ m :: Γ3) ++ Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H1. apply ImpRRule_I.
         assert (Γ2 ++ m :: Γ3 ++ A0 :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: Γ3 ++ A0 :: m :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ m :: Γ4).
         repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI. }
       { simpl in e1. inversion e1. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: Γ1, B). repeat split.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ A0 :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ImpRRule_I. }
    + repeat rewrite <- app_assoc. simpl.
       exists (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4, B). split.
       assert (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ A0 :: x0 ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ m :: x ++ x0 ++ Γ4 = (Γ2 ++ m :: x) ++ x0 ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H1. apply ImpRRule_I.
       assert (Γ2 ++ m :: x ++ A0 :: x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ A0 :: x0) ++ m :: Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4 = Γ2 ++ m :: (x ++ A0 :: x0) ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
- repeat rewrite <- app_assoc. exists (Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4, B). split. apply ImpRRule_I.
  assert (Γ0 ++ A0 :: x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ A0 :: x) ++ A :: Γ3 ++ A :: Γ4).
  repeat rewrite <- app_assoc. auto. rewrite H0.
  assert (Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ A0 :: x) ++ A :: Γ3 ++ Γ4).
  repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
Qed.

Lemma AtomImpL1_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AtomImpL1Rule [ps] s) ->
  ((existsT2 psc, (AtomImpL1Rule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 P B invps invpsc,
                       (A = Imp (# P) B) *
                       ((AtomImpL1Rule [invps] ps) + (AtomImpL2Rule [invps] ps)) *
                       (@ctr_L B invps invpsc) *
                       ((AtomImpL1Rule [invpsc] sc) + (AtomImpL2Rule [invpsc] sc)))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply list_split_form in H1. destruct H1.
repeat destruct s ; repeat destruct p ; subst.
- apply list_split_form in e. destruct e. repeat destruct s ; repeat destruct p ; subst.
  * inversion e0.
  * left. exists (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ Γ5, C). split. repeat rewrite <- app_assoc. simpl.
    apply AtomImpL1Rule_I.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ # P :: Γ5 = Γ0 ++ # P :: (Γ1 ++ A0 :: x0) ++ # P :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ Γ5 = Γ0 ++ # P :: (Γ1 ++ A0 :: x0) ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
  * repeat destruct s. repeat destruct p ; subst. left. exists (Γ0 ++ # P :: Γ4 ++ x ++ A0 :: Γ2, C). split.
    assert (Γ0 ++ # P :: Γ4 ++ x ++ A0 :: Γ2 = Γ0 ++ # P :: (Γ4 ++ x) ++ A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ # P :: Γ4 ++ x ++ # P → A0 :: Γ2 = Γ0 ++ # P :: (Γ4 ++ x) ++ # P → A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply AtomImpL1Rule_I. repeat rewrite <- app_assoc. simpl. apply ctr_LI.
- apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
  * right. exists P. exists A0. exists (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ A0 :: Γ5, C). exists (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ Γ5, C).
    repeat split ; repeat rewrite <- app_assoc ; simpl ; auto. left.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ A0 :: Γ5 = Γ0 ++ # P :: (Γ1 ++ A0 :: Γ4) ++ A0 :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ # P → A0 :: Γ5 = Γ0 ++ # P :: (Γ1 ++ A0 :: Γ4) ++ # P → A0 :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply AtomImpL1Rule_I.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ A0 :: Γ5 = (Γ0 ++ # P :: Γ1) ++ A0 :: Γ4 ++ A0 :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ Γ5 = (Γ0 ++ # P :: Γ1) ++ A0 :: Γ4 ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply ctr_LI.
    left. apply AtomImpL1Rule_I.
  * repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ # P :: Γ1 ++ A0 :: x1 ++ A :: Γ4 ++ Γ5, C). split.
    apply AtomImpL1Rule_I.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: x1 ++ A :: Γ4 ++ A :: Γ5 = (Γ0 ++ # P :: Γ1 ++ A0 :: x1) ++ A :: Γ4 ++ A :: Γ5).
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ0 ++ # P :: Γ1 ++ A0 :: x1 ++ A :: Γ4 ++ Γ5 = (Γ0 ++ # P :: Γ1 ++ A0 :: x1) ++ A :: Γ4 ++ Γ5).
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
  * repeat destruct s ; repeat destruct p ; subst ; repeat rewrite <- app_assoc ; simpl.
     apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
    + right. exists P. exists A0. exists (Γ0 ++ # P :: x0 ++ A0 :: x ++ A0 :: Γ2, C). exists (Γ0 ++ # P :: x0 ++ A0 :: x ++ Γ2, C).
        repeat split ; repeat rewrite <- app_assoc ; simpl ; auto. left. apply AtomImpL1Rule_I.
        assert (Γ0 ++ # P :: x0 ++ A0 :: x ++ A0 :: Γ2 = (Γ0 ++ # P :: x0) ++ A0 :: x ++ A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ # P :: x0 ++ A0 :: x ++ Γ2 = (Γ0 ++ # P :: x0) ++ A0 :: x ++ Γ2). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ctr_LI.
        left. apply AtomImpL1Rule_I.
    + repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ # P :: (x0 ++ A :: x) ++ A0 :: x2 ++ Γ5, C). split.
        assert (Γ0 ++ # P :: x0 ++ A :: x ++ # P → A0 :: x2 ++ Γ5 = Γ0 ++ # P :: (x0 ++ A :: x) ++ # P → A0 :: x2 ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply AtomImpL1Rule_I.
        assert (Γ0 ++ # P :: x0 ++ A :: x ++ A0 :: x2 ++ A :: Γ5 = (Γ0 ++ # P :: x0) ++ A :: (x ++ A0 :: x2) ++ A :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ # P :: (x0 ++ A :: x) ++ A0 :: x2 ++ Γ5 = (Γ0 ++ # P :: x0) ++ A :: (x ++ A0 :: x2) ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ctr_LI.
    +  repeat destruct s ; repeat destruct p ; subst.
        repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ # P :: (x0 ++ A :: Γ4 ++ x1) ++ A0 :: Γ2, C). split.
        assert (Γ0 ++ # P :: x0 ++ A :: Γ4 ++ x1 ++ # P → A0 :: Γ2 = Γ0 ++ # P :: (x0 ++ A :: Γ4 ++ x1) ++ # P → A0 :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        apply AtomImpL1Rule_I.
        assert (Γ0 ++ # P :: x0 ++ A :: Γ4 ++ A :: x1 ++ A0 :: Γ2 = (Γ0 ++ # P :: x0) ++ A :: Γ4 ++ A :: x1 ++ A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ # P :: (x0 ++ A :: Γ4 ++ x1) ++ A0 :: Γ2 = (Γ0 ++ # P :: x0) ++ A :: Γ4 ++ x1 ++ A0 :: Γ2). 
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
        apply ctr_LI.
- repeat destruct  s ; repeat destruct p ; subst. apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
  * left. exists (Γ3 ++ # P :: (x ++ Γ1) ++ A0 :: Γ2, C). repeat split.
    assert (Γ3 ++ # P :: x ++ Γ1 ++ # P → A0 :: Γ2 = Γ3 ++ # P :: (x ++ Γ1) ++ # P → A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
    apply AtomImpL1Rule_I. repeat rewrite <- app_assoc. apply ctr_LI.
  * repeat rewrite <- app_assoc ; simpl. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
    + right. exists P. exists A0. exists (Γ3 ++ A0 :: x ++ # P :: Γ1 ++ A0 :: Γ2, C). exists (Γ3 ++ A0 :: x ++ # P :: Γ1 ++ Γ2, C).
        repeat split ; repeat rewrite <- app_assoc ; simpl ; auto. right. apply AtomImpL2Rule_I.
        assert (Γ3 ++ A0 :: x ++ # P :: Γ1 ++ A0 :: Γ2 = Γ3 ++ A0 :: (x ++ # P :: Γ1) ++ A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ3 ++ A0 :: x ++ # P :: Γ1 ++ Γ2 = Γ3 ++ A0 :: (x ++ # P :: Γ1) ++ Γ2). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ctr_LI.
        right. apply AtomImpL2Rule_I.
    + repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ # P :: Γ1 ++ A0 :: x2 ++ Γ5, C). split.
        assert (Γ3 ++ A :: x ++ # P :: Γ1 ++ # P → A0 :: x2 ++ Γ5 = (Γ3 ++ A :: x) ++ # P :: Γ1 ++ # P → A0 :: x2 ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply AtomImpL1Rule_I.
        assert (Γ3 ++ A :: x ++ # P :: Γ1 ++ A0 :: x2 ++ A :: Γ5 = Γ3 ++ A :: (x ++ # P :: Γ1 ++ A0 :: x2) ++ A :: Γ5).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert ((Γ3 ++ A :: x) ++ # P :: Γ1 ++ A0 :: x2 ++ Γ5 = Γ3 ++ A :: (x ++ # P :: Γ1 ++ A0 :: x2) ++ Γ5).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
        apply ctr_LI.
    +  repeat destruct s ; repeat destruct p ; subst.
        repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ # P :: (x1 ++ x0) ++ A0 :: Γ2, C). split.
        assert (Γ3 ++ A :: x ++ # P :: x1 ++ x0 ++ # P → A0 :: Γ2 = (Γ3 ++ A :: x) ++ # P :: (x1 ++ x0) ++ # P → A0 :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        apply AtomImpL1Rule_I.
        assert (Γ3 ++ A :: x ++ # P :: x1 ++ A :: x0 ++ A0 :: Γ2 = Γ3 ++ A :: (x ++ # P :: x1) ++ A :: x0 ++ A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert ((Γ3 ++ A :: x) ++ # P :: (x1 ++ x0) ++ A0 :: Γ2 = Γ3 ++ A :: (x ++ # P :: x1) ++ x0 ++ A0 :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
        apply ctr_LI.
  * repeat destruct s ; repeat destruct p ; subst.
    left. exists ((Γ3 ++ A :: Γ4 ++ x0) ++ # P :: Γ1 ++ A0 :: Γ2, C). repeat split.
    assert (Γ3 ++ A :: Γ4 ++ x0 ++ # P :: Γ1 ++ # P → A0 :: Γ2 = (Γ3 ++ A :: Γ4 ++ x0) ++ # P :: Γ1 ++ # P → A0 :: Γ2).
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
    apply AtomImpL1Rule_I. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc. apply ctr_LI.
Qed.

Lemma AtomImpL2_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AtomImpL2Rule [ps] s) ->
  ((existsT2 psc, ((AtomImpL1Rule [psc] sc) + (AtomImpL2Rule [psc] sc)) * (@ctr_L A ps psc))
  +
  (existsT2 P B invps invpsc,
                       (A = Imp (# P) B) *
                       ((AtomImpL1Rule [invps] ps) + (AtomImpL2Rule [invps] ps)) *
                       (@ctr_L B invps invpsc) *
                       ((AtomImpL1Rule [invpsc] sc) + (AtomImpL2Rule [invpsc] sc)))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply list_split_form in H1. destruct H1.
repeat destruct s ; repeat destruct p ; subst.
- apply list_split_form in e. destruct e. repeat destruct s ; repeat destruct p ; subst.
  * inversion e0.
  * right. exists P. exists A0. exists ((Γ0 ++ A0 :: Γ1) ++ # P :: x0 ++ A0 :: Γ5, C).
    exists (Γ0 ++ A0 :: Γ1 ++ # P :: x0 ++ Γ5, C).  repeat split.
    left. assert (Γ0 ++ A0 :: Γ1 ++ # P :: x0 ++ # P → A0 :: Γ5 = (Γ0 ++ A0 :: Γ1) ++ # P :: x0 ++ # P → A0 :: Γ5). repeat rewrite <- app_assoc ; auto.
    rewrite H0. apply AtomImpL1Rule_I.
    assert ((Γ0 ++ A0 :: Γ1) ++ # P :: x0 ++ A0 :: Γ5 = Γ0 ++ A0 :: (Γ1 ++ # P :: x0) ++ A0 :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ A0 :: Γ1 ++ # P :: x0 ++ Γ5 = Γ0 ++ A0 :: (Γ1 ++ # P :: x0) ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
    right. repeat rewrite <- app_assoc. apply AtomImpL2Rule_I.
  * repeat destruct s. repeat destruct p ; subst. right. exists P. exists A0. exists ((Γ0 ++ A0 :: Γ4) ++ A0 :: x ++ # P :: Γ2, C).
    exists (Γ0 ++ A0 :: (Γ4 ++ x) ++ # P :: Γ2, C).  repeat split.
    right. assert (Γ0 ++ A0 :: (Γ4 ++ # P → A0 :: x) ++ # P :: Γ2 = (Γ0 ++ A0 :: Γ4) ++ # P → A0 :: x ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto.
    rewrite H0. apply AtomImpL2Rule_I. repeat rewrite <- app_assoc ; apply ctr_LI.
    assert (Γ0 ++ # P → A0 :: Γ4 ++ x ++ # P :: Γ2 = Γ0 ++ # P → A0 :: (Γ4 ++ x) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto.
    rewrite H0. right. apply AtomImpL2Rule_I.
- apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
  * left. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A0 :: Γ1 ++ # P :: Γ4 ++ Γ5, C). split.
    right. apply AtomImpL2Rule_I.
    assert (Γ0 ++ A0 :: Γ1 ++ # P :: Γ4 ++ # P :: Γ5 = (Γ0 ++ A0 :: Γ1) ++ # P :: Γ4 ++ # P :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ A0 :: Γ1 ++ # P :: Γ4 ++ Γ5 = (Γ0 ++ A0 :: Γ1) ++ # P :: Γ4 ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply ctr_LI.
  * repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ A0 :: Γ1 ++ # P :: x1 ++ A :: Γ4 ++ Γ5, C). split.
    right. apply AtomImpL2Rule_I.
    assert (Γ0 ++ A0 :: Γ1 ++ # P :: x1 ++ A :: Γ4 ++ A :: Γ5 = (Γ0 ++ A0 :: Γ1 ++ # P :: x1) ++ A :: Γ4 ++ A :: Γ5).
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ0 ++ A0 :: Γ1 ++ # P :: x1 ++ A :: Γ4 ++ Γ5 = (Γ0 ++ A0 :: Γ1 ++ # P :: x1) ++ A :: Γ4 ++ Γ5).
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
  * repeat destruct s ; repeat destruct p ; subst ; repeat rewrite <- app_assoc ; simpl.
     apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
    + left. exists (Γ0 ++ A0 :: x0 ++ # P :: x ++ Γ2, C). split. right. apply AtomImpL2Rule_I.
        assert (Γ0 ++ A0 :: x0 ++ # P :: x ++ # P :: Γ2 = (Γ0 ++ A0 :: x0) ++ # P :: x ++ # P :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ A0 :: x0 ++ # P :: x ++ Γ2 = (Γ0 ++ A0 :: x0) ++ # P :: x ++ Γ2). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ctr_LI.
    + repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ A0 :: (x0 ++ A :: x) ++ # P :: x2 ++ Γ5, C). split. right.
        assert (Γ0 ++ # P → A0 :: x0 ++ A :: x ++ # P :: x2 ++ Γ5 = Γ0 ++ # P → A0 :: (x0 ++ A :: x) ++ # P :: x2 ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply AtomImpL2Rule_I.
        assert (Γ0 ++ A0 :: x0 ++ A :: x ++ # P :: x2 ++ A :: Γ5 = (Γ0 ++ A0 :: x0) ++ A :: (x ++ # P :: x2) ++ A :: Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ A0 :: (x0 ++ A :: x) ++ # P :: x2 ++ Γ5 = (Γ0 ++ A0 :: x0) ++ A :: (x ++ # P :: x2) ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ctr_LI.
    +  repeat destruct s ; repeat destruct p ; subst.
        repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ A0 :: (x0 ++ A :: Γ4 ++ x1) ++ # P :: Γ2, C). split. right.
        assert (Γ0 ++ # P → A0 :: x0 ++ A :: Γ4 ++ x1 ++ # P :: Γ2 = Γ0 ++ # P → A0 :: (x0 ++ A :: Γ4 ++ x1) ++ # P :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        apply AtomImpL2Rule_I.
        assert (Γ0 ++ A0 :: x0 ++ A :: Γ4 ++ A :: x1 ++ # P :: Γ2 = (Γ0 ++ A0 :: x0) ++ A :: Γ4 ++ A :: x1 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ A0 :: (x0 ++ A :: Γ4 ++ x1) ++ # P :: Γ2 = (Γ0 ++ A0 :: x0) ++ A :: Γ4 ++ x1 ++ # P :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
        apply ctr_LI.
- repeat destruct  s ; repeat destruct p ; subst. apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
  * right. exists P. exists A0. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ A0 :: (x ++ A0 :: Γ1) ++ # P :: Γ2, C). 
    exists (Γ3 ++ A0 :: (x ++ Γ1) ++ # P :: Γ2, C). repeat split. right.
    assert (Γ3 ++ # P → A0 :: x ++ A0 :: Γ1 ++ # P :: Γ2 = Γ3 ++ # P → A0 :: (x ++ A0 :: Γ1) ++ # P :: Γ2). repeat rewrite <- app_assoc ; auto. rewrite H0.
    apply AtomImpL2Rule_I. repeat rewrite <- app_assoc ; apply ctr_LI.
    assert (Γ3 ++ # P → A0 :: x ++ Γ1 ++ # P :: Γ2 = Γ3 ++ # P → A0 :: (x ++ Γ1) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
    right. apply AtomImpL2Rule_I.
  * repeat rewrite <- app_assoc ; simpl. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
    +  left. exists (Γ3 ++ # P :: x ++ A0 :: Γ1 ++ Γ2, C). split.
        left. apply AtomImpL1Rule_I.
        assert (Γ3 ++ # P :: x ++ A0 :: Γ1 ++ # P :: Γ2 = Γ3 ++ # P :: (x ++ A0 :: Γ1) ++ # P :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ3 ++ # P :: x ++ A0 :: Γ1 ++ Γ2 = Γ3 ++ # P :: (x ++ A0 :: Γ1) ++ Γ2). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ctr_LI.
    +  repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ A0 :: Γ1 ++ # P :: x2 ++ Γ5, C). split.
        assert (Γ3 ++ A :: x ++ # P → A0 :: Γ1 ++ # P :: x2 ++ Γ5 = (Γ3 ++ A :: x) ++ # P → A0 :: Γ1 ++ # P :: x2 ++ Γ5). repeat rewrite <- app_assoc. auto. rewrite H0.
        right. apply AtomImpL2Rule_I.
        assert (Γ3 ++ A :: x ++ A0 :: Γ1 ++ # P :: x2 ++ A :: Γ5 = Γ3 ++ A :: (x ++ A0 :: Γ1 ++ # P :: x2) ++ A :: Γ5).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert ((Γ3 ++ A :: x) ++ A0 :: Γ1 ++ # P :: x2 ++ Γ5 = Γ3 ++ A :: (x ++ A0 :: Γ1 ++ # P :: x2) ++ Γ5).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
        apply ctr_LI.
    +  repeat destruct s ; repeat destruct p ; subst.
        repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ A0 :: (x1 ++ x0) ++ # P :: Γ2, C). split.
        assert (Γ3 ++ A :: x ++ # P → A0 :: x1 ++ x0 ++ # P :: Γ2 = (Γ3 ++ A :: x) ++ # P → A0 :: (x1 ++ x0) ++ # P :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        right. apply AtomImpL2Rule_I.
        assert (Γ3 ++ A :: x ++ A0 :: x1 ++ A :: x0 ++ # P :: Γ2 = Γ3 ++ A :: (x ++ A0 :: x1) ++ A :: x0 ++ # P :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert ((Γ3 ++ A :: x) ++ A0 :: (x1 ++ x0) ++ # P :: Γ2 = Γ3 ++ A :: (x ++ A0 :: x1) ++ x0 ++ # P :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
        apply ctr_LI.
  * repeat destruct s ; repeat destruct p ; subst.
    left. exists ((Γ3 ++ A :: Γ4 ++ x0) ++ A0 :: Γ1 ++ # P :: Γ2, C). split. right.
    assert (Γ3 ++ A :: Γ4 ++ x0 ++ # P → A0 :: Γ1 ++ # P :: Γ2 = (Γ3 ++ A :: Γ4 ++ x0) ++ # P → A0 :: Γ1 ++ # P :: Γ2).
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
    apply AtomImpL2Rule_I. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc. apply ctr_LI.
Qed.

Lemma AndImpL_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AndImpLRule [ps] s) ->
  ((existsT2 psc, (AndImpLRule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 B C D invps invpsc,
                       (A = Imp (And B C) D) *
                       (AndImpLRule [invps] ps) *
                       (@ctr_L (Imp B (Imp C D)) invps invpsc) *
                       (AndImpLRule [invpsc] sc))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D).
  exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
  assert (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4 = (Γ2 ++ Imp A0 (Imp B C) :: Γ3) ++ Imp A0 (Imp B C) :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H0.
  assert (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp (And A0 B) C :: Γ4 = (Γ2 ++ Imp A0 (Imp B C) :: Γ3) ++ Imp (And A0 B) C :: Γ4).
  repeat rewrite <- app_assoc ; auto. rewrite H1. apply AndImpLRule_I.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right.
    exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D).
    exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
    assert (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4 = (Γ2 ++ Imp A0 (Imp B C) :: Γ3) ++ Imp A0 (Imp B C) :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp (And A0 B) C :: Γ4 = (Γ2 ++ Imp A0 (Imp B C) :: Γ3) ++ Imp (And A0 B) C :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply AndImpLRule_I.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right.
       exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D).
       exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ1, D).
         exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ1, D). repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ Imp A0 (Imp B C) :: Γ1, D). repeat split.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ Imp (And A0 B) C :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ Imp (And A0 B) C :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ Imp A0 (Imp B C) :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ Imp A0 (Imp B C) :: Γ1).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
         apply AndImpLRule_I. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: x ++ Imp A0 (Imp B C) :: Γ4, D).
         exists (Γ2 ++ Imp A0 (Imp B C) :: x ++ Γ4, D). repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: x ++ Imp A0 (Imp B C) :: x0 ++ Γ4, D). repeat split.
         assert (Γ2 ++ m :: x ++ Imp A0 (Imp B C) :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ Imp A0 (Imp B C) :: x0 ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: x ++ Imp (And A0 B) C :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ Imp (And A0 B) C :: x0 ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
         apply AndImpLRule_I.
         assert (Γ2 ++ m :: x ++ Imp A0 (Imp B C) :: x0 ++ Γ4 = Γ2 ++ m :: (x ++ Imp A0 (Imp B C) :: x0) ++ Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
         assert (Γ2 ++ m :: x ++ Imp A0 (Imp B C) :: x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ Imp A0 (Imp B C) :: x0) ++ m :: Γ4).
         repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI. }
- destruct x.
  * simpl in e0. inversion e0. subst. right. repeat rewrite <- app_assoc. simpl.
     exists A0. exists B. exists C. exists (Γ0 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D).
     exists (Γ0 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
    assert (Γ0 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4 = (Γ0 ++ Imp A0 (Imp B C) :: Γ3) ++ Imp A0 (Imp B C) :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ0 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp (And A0 B) C :: Γ4 = (Γ0 ++ Imp A0 (Imp B C) :: Γ3) ++ Imp (And A0 B) C :: Γ4).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply AndImpLRule_I.
  * simpl in e0. inversion e0. subst. left.
    repeat rewrite <- app_assoc. simpl.
    exists (Γ0 ++ Imp A0 (Imp B C) :: x ++ A :: Γ3 ++ Γ4, D). repeat split.
    assert (Γ0 ++ Imp A0 (Imp B C) :: x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ Imp A0 (Imp B C) :: x) ++ A :: Γ3 ++ A :: Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (Γ0 ++ Imp A0 (Imp B C) :: x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ Imp A0 (Imp B C) :: x) ++ A :: Γ3 ++ Γ4).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
Qed.

Lemma OrImpL_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (OrImpLRule [ps] s) ->
  ((existsT2 psc, (OrImpLRule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 B C D invps invpsc1 invpsc2,
                       (A = Imp (Or B C) D) *
                       (OrImpLRule [invps] ps) *
                       (@ctr_L (Imp B D) invps invpsc1) *
                       (@ctr_L (Imp C D) invpsc1 invpsc2) *
                       (OrImpLRule [invpsc2] sc))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. apply app2_find_hole in H2. destruct H2.
  repeat destruct s ; destruct p ; subst.
  * right. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
    exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5, D).
    repeat split.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp (Or A0 B) C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ Imp (Or A0 B) C :: [] ++ Γ5).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ1 ++ [Imp B C]) ++ Imp A0 C :: Imp B C :: Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ1 ++ [Imp B C]) ++ Imp B C :: Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1) ++ Imp B C :: [] ++ Imp B C :: Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1) ++ Imp B C :: [] ++ Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
  * right. repeat rewrite <- app_assoc. simpl.
    exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp A0 C :: Imp B C :: Γ5, D).
    exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Γ5, D).
    repeat split.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp A0 C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp (Or A0 B) C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0) ++ Imp (Or A0 B) C :: [] ++ Γ5).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp A0 C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ1 ++ Imp B C :: x0) ++  Imp A0 C :: Imp B C :: Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ1 ++ Imp B C :: x0) ++  Imp B C :: Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1) ++ Imp B C :: x0 ++  Imp B C :: Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Γ5 = (Γ3 ++ Imp A0 C :: Γ1) ++ Imp B C :: x0 ++ Γ5).
    repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
  * destruct x0.
    + simpl in e1. subst. right. repeat rewrite <- app_assoc. simpl.
        exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
        exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D).
        repeat split.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp (Or A0 B) C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp (Or A0 B) C :: [] ++ Γ5).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++  Imp A0 C :: Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++  Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    + simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
        exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++  Imp A0 C :: Imp B C :: x0 ++ Imp B C :: Γ2, D).
        exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x0 ++ Imp B C :: Γ2, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x0 ++ Γ2, D).
        repeat split.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp A0 C :: Imp B C :: x0 ++ Imp B C :: Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp A0 C :: [] ++ Imp B C :: x0 ++ Imp B C :: Γ2).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp (Or A0 B) C :: x0 ++ Imp B C :: Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp (Or A0 B) C :: []++ x0 ++ Imp B C :: Γ2).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x0 ++ Imp B C :: Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: x0 ++ Imp B C :: Γ2).
        repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x0 ++ Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: x0 ++ Γ2).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
   + right. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
      exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D).
      repeat split.
      assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp (Or A0 B) C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp (Or A0 B) C :: [] ++ Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
      assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++ Imp A0 C :: Imp B C :: Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++ Imp B C :: Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
      assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Imp B C :: Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    + destruct x.
        { simpl in e1. subst. right. repeat rewrite <- app_assoc. simpl.
          exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
          exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D).
          repeat split.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp (Or A0 B) C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp (Or A0 B) C :: [] ++ Γ5).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++  Imp A0 C :: Imp B C :: Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++  Imp B C :: Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Imp B C :: Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
        { simpl in e1.  inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
          exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp A0 C :: Imp B C :: x ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Imp B C :: Γ2, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Γ2, D).
          repeat split.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp A0 C :: Imp B C :: x ++ Imp B C :: Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp A0 C :: [] ++ Imp B C :: x ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp (Or A0 B) C :: x ++ Imp B C :: Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp (Or A0 B) C :: [] ++ x ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Imp B C :: Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: x ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Γ2 = (Γ3 ++ Imp A0 C :: Γ4) ++ Imp B C :: x ++ Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
    +  repeat rewrite <- app_assoc. simpl. right.
        exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp A0 C :: Imp B C :: Γ5, D).
        exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Γ5, D).
        repeat split.
        assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++Imp A0 C :: Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp (Or A0 B) C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x) ++ Imp (Or A0 B) C :: [] ++ Γ5).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
        assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp A0 C :: Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ1 ++ Imp B C :: x) ++  Imp A0 C :: Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp B C :: Γ5 = Γ3 ++ Imp A0 C :: (Γ1 ++ Imp B C :: x) ++  Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
        assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++Imp B C :: Γ5 = (Γ3 ++ Imp A0 C :: Γ1) ++ Imp B C :: x ++ Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Γ5 = (Γ3 ++ Imp A0 C :: Γ1) ++ Imp B C :: x ++ Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
  * inversion e0. subst.  repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
   + inversion e1. subst. right. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D).
      exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2, D).
      exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2, D). repeat split.
      assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: [] ++ Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ3 ++ Imp (Or A0 B) C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp (Or A0 B) C :: [] ++ Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
      assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: (Imp B C :: Γ4) ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
      repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: (Imp B C :: Γ4) ++ Γ1 ++ Imp B C :: Γ2).
      repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
      assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2 = (Γ3 ++ [Imp A0 C]) ++ Imp B C :: (Γ4 ++ Γ1) ++ Imp B C :: Γ2).
      repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2 = (Γ3 ++ [Imp A0 C]) ++ Imp B C :: (Γ4 ++ Γ1) ++ Γ2).
      repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
      assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2 = Γ3 ++ Imp A0 C :: [] ++ Imp B C :: Γ4 ++ Γ1 ++ Γ2).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ3 ++ Imp (Or A0 B) C :: Γ4 ++ Γ1 ++ Γ2 = Γ3 ++ Imp (Or A0 B) C :: [] ++ Γ4 ++ Γ1 ++ Γ2).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
    + destruct x0.
        { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
          exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2, D). repeat split.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: [] ++ Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp (Or A0 B) C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp (Or A0 B) C :: [] ++ Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: (Imp B C :: Γ4) ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: (Imp B C :: Γ4) ++ Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2 = (Γ3 ++ [Imp A0 C]) ++ Imp B C :: (Γ4 ++ Γ1) ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2 = (Γ3 ++ [Imp A0 C]) ++ Imp B C :: (Γ4 ++ Γ1) ++ Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2 = Γ3 ++ Imp A0 C :: [] ++ Imp B C :: Γ4 ++ Γ1 ++ Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp (Or A0 B) C :: Γ4 ++ Γ1 ++ Γ2 = Γ3 ++ Imp (Or A0 B) C :: [] ++ Γ4 ++ Γ1 ++ Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I. }
        { simpl in e1.  inversion e1. subst. left. exists (Γ3 ++ m0 :: Γ4 ++ x0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D). split.
           assert (Γ3 ++ m0 :: Γ4 ++ x0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = (Γ3 ++ m0 :: Γ4 ++ x0) ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
           assert (Γ3 ++ m0 :: Γ4 ++ x0 ++ Imp (Or A0 B) C :: Γ1 ++ Γ2 = (Γ3 ++ m0 :: Γ4 ++ x0) ++ Imp (Or A0 B) C :: Γ1 ++ Γ2).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply OrImpLRule_I.
           repeat rewrite <- app_assoc. simpl. apply ctr_LI. }
    +  repeat rewrite <- app_assoc. simpl. destruct x0.
        { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
          exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Γ2, D). repeat split.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: [] ++ Imp B C :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp (Or A0 B) C :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp (Or A0 B) C :: [] ++ x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: (Imp B C :: x) ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Imp B C :: Γ2 = Γ3 ++ Imp A0 C :: (Imp B C :: x) ++ Γ1 ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Imp B C :: Γ2 = (Γ3 ++ [Imp A0 C]) ++ Imp B C :: (x ++ Γ1) ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Γ2 = (Γ3 ++ [Imp A0 C]) ++ Imp B C :: (x ++ Γ1) ++ Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          assert (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Γ2 = Γ3 ++ Imp A0 C :: [] ++ Imp B C :: x ++ Γ1 ++ Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ3 ++ Imp (Or A0 B) C :: x ++ Γ1 ++ Γ2 = Γ3 ++ Imp (Or A0 B) C :: [] ++ x ++ Γ1 ++ Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I. }
        { simpl in e1.  inversion e1. subst. repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
           repeat destruct s ; destruct p ; subst.
          - left. exists (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5, D). split.
           assert (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5 = (Γ3 ++ m :: x) ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
           assert (Γ3 ++ m :: x ++ Imp (Or A0 B) C :: Γ1 ++ Γ5 = (Γ3 ++ m :: x) ++ Imp (Or A0 B) C :: Γ1 ++ Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply OrImpLRule_I.
           assert (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: m :: Γ5 = Γ3 ++ m :: (x ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ m :: Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
           assert (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5 = Γ3 ++ m :: (x ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
          - left. repeat rewrite <- app_assoc. exists (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: x1 ++ Γ5, D). split.
           assert (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: x1 ++ Γ5 = (Γ3 ++ m :: x) ++ Imp A0 C :: Γ1 ++ Imp B C :: x1 ++ Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
           assert (Γ3 ++ m :: x ++ Imp (Or A0 B) C :: Γ1 ++ x1 ++ Γ5 = (Γ3 ++ m :: x) ++ Imp (Or A0 B) C :: Γ1 ++ x1 ++ Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply OrImpLRule_I.
           assert (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: x1 ++ m ::  Γ5 = Γ3 ++ m :: (x ++ Imp A0 C :: Γ1 ++ Imp B C :: x1) ++ m :: Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
           assert (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: x1 ++ Γ5 = Γ3 ++ m :: (x ++ Imp A0 C :: Γ1 ++ Imp B C :: x1) ++ Γ5).
           repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
          - destruct x1.
            * simpl in e2. subst. left. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ m :: x ++ Imp A0 C :: x0 ++ Imp B C :: Γ5, D). split.
             assert (Γ3 ++ m :: x ++ Imp A0 C :: x0 ++ Imp B C :: Γ5 = (Γ3 ++ m :: x) ++ Imp A0 C :: x0 ++ Imp B C :: Γ5).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
             assert (Γ3 ++ m :: x ++ Imp (Or A0 B) C :: x0 ++ Γ5 = (Γ3 ++ m :: x) ++ Imp (Or A0 B) C :: x0 ++ Γ5).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply OrImpLRule_I.
             assert (Γ3 ++ m :: x ++ Imp A0 C :: x0 ++ Imp B C :: m ::  Γ5 = Γ3 ++ m :: (x ++ Imp A0 C :: x0 ++ [Imp B C]) ++ m :: Γ5).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
             assert (Γ3 ++ m :: x ++ Imp A0 C :: x0 ++ Imp B C :: Γ5 = Γ3 ++ m :: (x ++ Imp A0 C :: x0 ++ [Imp B C]) ++ Γ5).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI.
            * simpl in e2. inversion e2. subst. repeat rewrite <- app_assoc. simpl. left. exists (Γ3 ++ m0 :: x ++ Imp A0 C :: x0 ++ x1 ++ Imp B C :: Γ2, D). split.
             assert (Γ3 ++ m0 :: x ++ Imp A0 C :: x0 ++ x1 ++ Imp B C :: Γ2 = (Γ3 ++ m0 :: x) ++ Imp A0 C :: (x0 ++ x1) ++ Imp B C :: Γ2).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
             assert (Γ3 ++ m0 :: x ++ Imp (Or A0 B) C :: x0 ++ x1 ++ Γ2 = (Γ3 ++ m0 :: x) ++ Imp (Or A0 B) C :: (x0 ++ x1) ++ Γ2).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply OrImpLRule_I.
             assert (Γ3 ++ m0 :: x ++ Imp A0 C :: x0 ++ m0 :: x1 ++ Imp B C :: Γ2 = Γ3 ++ m0 :: (x ++ Imp A0 C :: x0) ++ m0 :: x1 ++ Imp B C :: Γ2).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
             assert (Γ3 ++ m0 :: x ++ Imp A0 C :: x0 ++ x1 ++ Imp B C :: Γ2 = Γ3 ++ m0 :: (x ++ Imp A0 C :: x0) ++ x1 ++ Imp B C :: Γ2).
             repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply ctr_LI. }
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
   + right. exists A0. exists B. exists C. exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
      exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5, D).
      repeat split.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp (Or A0 B) C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ Imp (Or A0 B) C :: [] ++ Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (Γ1 ++ [Imp B C]) ++ Imp A0 C :: Imp B C :: Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (Γ1 ++ [Imp B C]) ++ Imp B C :: Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1) ++ Imp B C :: [] ++ Imp B C :: Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1) ++ Imp B C :: [] ++ Γ5).
      repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    + right. repeat rewrite <- app_assoc. simpl.
        exists A0. exists B. exists C. exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp A0 C :: Imp B C :: Γ5, D).
        exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp B C :: Γ5, D). exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Γ5, D).
        repeat split.
        assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp A0 C :: Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp (Or A0 B) C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x) ++ Imp (Or A0 B) C :: [] ++ Γ5).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
        assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp A0 C :: Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (Γ1 ++ Imp B C :: x) ++  Imp A0 C :: Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (Γ1 ++ Imp B C :: x) ++  Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
        assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1) ++ Imp B C :: x ++ Imp B C :: Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H0.
        assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Γ5 = (Γ0 ++ Imp A0 C :: Γ1) ++ Imp B C :: x ++ Γ5).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    +  destruct x.
        { simpl in e1. subst. repeat rewrite <- app_assoc. simpl. right.
          exists A0. exists B. exists C. exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
          exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D).
          repeat split.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp A0 C :: [] ++ Imp B C :: Γ5).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp (Or A0 B) C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ4 ++ [Imp B C]) ++ Imp (Or A0 B) C :: [] ++ Γ5).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++  Imp A0 C :: Imp B C :: Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (Γ4 ++ [Imp B C]) ++  Imp B C :: Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Imp B C :: Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: Γ4) ++ Imp B C :: [] ++ Γ5).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
        { simpl in e1. inversion e1. subst. repeat rewrite <- app_assoc. simpl. right.
          exists A0. exists B. exists C.  exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp A0 C :: Imp B C :: x ++ Imp B C :: Γ2, D).
          exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Imp B C :: Γ2, D). exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Γ2, D).
          repeat split.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp A0 C :: Imp B C:: x ++ Imp B C :: Γ2 = (Γ0 ++ Imp A0 C :: Γ4) ++ Imp A0 C :: [] ++ Imp B C :: x ++ Imp B C:: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp (Or A0 B) C :: x ++ Imp B C:: Γ2 = (Γ0 ++ Imp A0 C :: Γ4) ++ Imp (Or A0 B) C :: [] ++ x ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Imp B C :: Γ2 = (Γ0 ++ Imp A0 C :: Γ4) ++ Imp B C :: x ++ Imp B C :: Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Γ2 = (Γ0 ++ Imp A0 C :: Γ4) ++ Imp B C :: x ++ Γ2).
          repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
  * inversion e0. subst.  repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
   + left. exists(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: A :: Γ4 ++ Γ5, D). repeat split.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: A :: Γ4 ++ A :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ A :: Γ4 ++ A :: Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: A :: Γ4 ++ Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ [Imp B C]) ++ A :: Γ4 ++ Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    + left. exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ A :: Γ4 ++ Γ5, D). repeat split. repeat rewrite <- app_assoc.
       apply OrImpLRule_I.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ A :: Γ4 ++ A :: Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0) ++ A :: Γ4 ++ A :: Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
      assert (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ A :: Γ4 ++ Γ5 = (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0) ++  A :: Γ4 ++ Γ5).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
    + destruct x0.
        { simpl in e1. subst. repeat rewrite <- app_assoc. simpl. left.
          exists (Γ0 ++ Imp A0 C :: x ++ Imp B C :: A :: Γ4 ++ Γ5, D). repeat split. repeat rewrite <- app_assoc.
          assert (Γ0 ++ Imp A0 C :: x ++ Imp B C ::  A :: Γ4 ++ A :: Γ5 = (Γ0 ++ Imp A0 C :: x ++ [Imp B C]) ++ A :: Γ4 ++ A :: Γ5).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
          assert (Γ0 ++ Imp A0 C :: x ++ Imp B C :: A :: Γ4 ++ Γ5 = (Γ0 ++ Imp A0 C :: x ++ [Imp B C]) ++  A :: Γ4 ++ Γ5).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
        { simpl in e1.  inversion e1. apply app2_find_hole in H2. destruct H2.
          repeat destruct s ; destruct p ; subst.
          - left. repeat rewrite <- app_assoc. simpl.
            exists (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C ::  Γ5, D). repeat split.
            assert (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (x ++ m :: Γ4) ++ Imp B C :: Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
            assert (Γ0 ++ Imp (Or A0 B) C :: x ++ m :: Γ4 ++ Γ5 = Γ0 ++ Imp (Or A0 B) C :: (x ++ m :: Γ4) ++ Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
            assert (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C :: m :: Γ5 = (Γ0 ++ Imp A0 C :: x) ++ m :: (Γ4 ++ [Imp B C]) ++  m :: Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
            assert (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: x) ++ m :: (Γ4 ++ [Imp B C]) ++ Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          - destruct x1.
            + simpl in e2. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C ::  Γ5, D). repeat split.
              assert (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C :: Γ5 = Γ0 ++ Imp A0 C :: (x ++ m :: Γ4) ++ Imp B C :: Γ5).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
              assert (Γ0 ++ Imp (Or A0 B) C :: x ++ m :: Γ4 ++ Γ5 = Γ0 ++ Imp (Or A0 B) C :: (x ++ m :: Γ4) ++ Γ5).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
              assert (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C :: m :: Γ5 = (Γ0 ++ Imp A0 C :: x) ++ m :: (Γ4 ++ [Imp B C]) ++  m :: Γ5).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
              assert (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C :: Γ5 = (Γ0 ++ Imp A0 C :: x) ++ m :: (Γ4 ++ [Imp B C]) ++ Γ5).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
            + simpl in e2. inversion e2. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ Imp A0 C :: x ++ m0 :: Γ4 ++ x1 ++ Imp B C :: Γ2, D). repeat split.
                assert (Γ0 ++ Imp A0 C :: x ++ m0 :: Γ4 ++ x1 ++ Imp B C :: Γ2 = Γ0 ++ Imp A0 C :: (x ++ m0 :: Γ4 ++ x1) ++ Imp B C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
                assert (Γ0 ++ Imp (Or A0 B) C :: x ++ m0 :: Γ4 ++ x1 ++ Γ2 = Γ0 ++ Imp (Or A0 B) C :: (x ++ m0 :: Γ4 ++ x1) ++ Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
                assert (Γ0 ++ Imp A0 C :: x ++ m0 :: Γ4 ++ m0 :: x1 ++ Imp B C :: Γ2 = (Γ0 ++ Imp A0 C :: x) ++ m0 :: Γ4 ++ m0 :: x1 ++ Imp B C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
                assert (Γ0 ++ Imp A0 C :: x ++ m0 :: Γ4 ++ x1 ++ Imp B C :: Γ2 = (Γ0 ++ Imp A0 C :: x) ++ m0 :: Γ4 ++ x1 ++ Imp B C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI.
          - left. repeat rewrite <- app_assoc. simpl.
            exists (Γ0 ++ Imp A0 C :: x ++ m :: x0 ++ Imp B C :: x1 ++ Γ5, D). repeat split.
            assert (Γ0 ++ Imp A0 C :: x ++ m :: x0 ++ Imp B C :: x1 ++ Γ5 = Γ0 ++ Imp A0 C :: (x ++ m :: x0) ++ Imp B C :: x1 ++ Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
            assert (Γ0 ++ Imp (Or A0 B) C :: x ++ m :: x0 ++ x1 ++ Γ5 = Γ0 ++ Imp (Or A0 B) C :: (x ++ m :: x0) ++ x1 ++ Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply OrImpLRule_I.
            assert (Γ0 ++ Imp A0 C :: x ++ m :: x0 ++ Imp B C :: x1 ++ m :: Γ5 = (Γ0 ++ Imp A0 C :: x) ++ m :: (x0 ++ Imp B C :: x1) ++ m :: Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H0.
            assert (Γ0 ++ Imp A0 C :: x ++ m :: x0 ++ Imp B C :: x1 ++ Γ5 = (Γ0 ++ Imp A0 C :: x) ++ m :: (x0 ++ Imp B C :: x1) ++ Γ5).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc ; auto. rewrite H1. apply ctr_LI. }
Qed.

Lemma BoxImpL_app_ctr_L : forall s sc A ps1 ps2,
  (@ctr_L A s sc) ->
  (BoxImpLRule [ps1;ps2] s) ->
  ((existsT2 psc2, (BoxImpLRule [ps1;psc2] sc) * (@ctr_L A ps2 psc2))
  +
   (existsT2 psc11 psc12 psc2, (BoxImpLRule [psc12;psc2] sc) * (@ctr_L A ps1 psc11) * (@ctr_L (unBox_formula A) psc11 psc12)
    * (@ctr_L A ps2 psc2) * (is_boxedT A))
  +
  (((existsT2 B C invps2 invpsc2,
                       (A = Imp (Box B) C) *
                       (BoxImpLRule [ps1;invps2] ps2) *
                       (@ctr_L C invps2 invpsc2) *
                       (BoxImpLRule [ps1;invpsc2] sc))
  +
  (existsT2 B C psw11 psw12 invps2 invpsc2,
                       (A = Imp (Box B) C) *
                       (BoxImpLRule [psw12;invps2] ps2) *
                       (@ctr_L C invps2 invpsc2) *
                       (@wkn_L C ps1 psw11) *
                       (@wkn_L (unBox_formula C) psw11 psw12) *
                       (BoxImpLRule [ps1;invpsc2] sc) * (is_boxedT C))))).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst.
apply univ_gen_ext_splitR in X. destruct X. destruct s ; repeat destruct p ; subst.
inversion H3. subst. apply list_split_form in H0. destruct H0.
repeat destruct s ; repeat destruct p ; subst.
- right.
  apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p ; subst.
  inversion u1. subst. exfalso. assert (In (Box A0 → B) (x ++ x1 ++ Box A0 → B :: l)).
  apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq. apply H2 in H. destruct H. inversion H. subst.
  destruct (dec_is_boxedT B).
  + right. exists A0. exists B. exists (XBoxed_list x ++ B :: XBoxed_list (x1 ++ x2) ++ [Box A0], A0).
      exists (XBoxed_list (x ++ [B] ++ x1 ++ x2) ++ [Box A0], A0). exists ((Γ0 ++ B :: Γ3) ++ B :: Γ4, C).
      exists (Γ0 ++ B :: Γ3 ++ Γ4, C).
      repeat split.
      assert (Γ0 ++ B :: Γ3 ++ Box A0 → B :: Γ4 = (Γ0 ++ B :: Γ3) ++ Box A0 → B :: Γ4).
      repeat rewrite <- app_assoc ; auto. rewrite H. apply BoxImpLRule_I. intro. intros.
      apply in_app_or in H0 ; destruct H0. apply H2. apply in_or_app ; auto.
      simpl in H0. destruct H0. subst. destruct i. subst. exists x0. auto.
      apply in_app_or in H0 ; destruct H0. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
      apply H2. apply in_or_app ; right ; apply in_or_app ; auto. repeat rewrite <- app_assoc ; simpl.
      repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
      repeat rewrite <- app_assoc ; simpl ; apply ctr_LI. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
      apply wkn_LI. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl. apply wkn_LI. auto.
      repeat apply univ_gen_ext_combine ; auto. auto.
  +  left. exists A0. exists B. exists ((Γ0 ++ B :: Γ3) ++ B :: Γ4, C). exists (Γ0 ++ B :: Γ3 ++ Γ4, C).
      repeat split ; auto.
      assert (Γ0 ++ B :: Γ3 ++ Box A0 → B :: Γ4 = (Γ0 ++ B :: Γ3) ++ Box A0 → B :: Γ4).
      repeat rewrite <- app_assoc ; auto. rewrite H. apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc ; simpl.
      repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto.
      repeat rewrite <- app_assoc ; simpl ; apply ctr_LI. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
      repeat apply univ_gen_ext_combine ; auto.
- left.
  apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p ; subst.
  destruct (dec_is_boxedT A).
  + right.
      inversion u1. subst. 2: exfalso.
      apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
      inversion u3. subst. 2: exfalso.
      exists (XBoxed_list (x ++ x1) ++ unBox_formula A :: A :: XBoxed_list x0 ++ unBox_formula A :: XBoxed_list  l ++ [Box A0], A0).
      exists (XBoxed_list (x ++ x1 ++ A :: x0 ++ l) ++ [Box A0], A0). exists (Γ0 ++ B :: x2 ++ A :: Γ3 ++ Γ4, C).
      repeat rewrite <- app_assoc ; repeat split ; auto. intro. intros.
      apply in_app_or in H ; destruct H. apply H2. apply in_or_app ; auto.
      apply in_app_or in H ; destruct H. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
      simpl in H. destruct H. subst. destruct i. subst. exists x3. auto.
      apply H2. apply in_or_app ; right ; apply in_or_app ; auto. repeat rewrite <- app_assoc ; simpl. right. right.
      apply in_app_or in H ; destruct H. apply in_or_app ; auto. apply in_or_app ; right ; apply in_cons ; auto.
      repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto. apply univ_gen_ext_combine ; auto.
      repeat rewrite <- app_assoc ; simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
      repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
      assert (XBoxed_list x ++ XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x0 ++ unBox_formula A :: A :: XBoxed_list l ++ [Box A0] =
      (XBoxed_list x ++ XBoxed_list x1 ++ [unBox_formula A]) ++ A :: (XBoxed_list x0 ++ [unBox_formula A]) ++ A :: XBoxed_list l ++ [Box A0]).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
      assert (XBoxed_list x ++ XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x0 ++ unBox_formula A :: XBoxed_list l ++ [Box A0] =
      (XBoxed_list x ++ XBoxed_list x1 ++ [unBox_formula A]) ++ A :: (XBoxed_list x0 ++ [unBox_formula A]) ++ XBoxed_list l ++ [Box A0]).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
      repeat rewrite <- app_assoc ; simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
      repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
      assert (XBoxed_list x ++ XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x0 ++ unBox_formula A :: XBoxed_list l ++ [Box A0] =
      (XBoxed_list x ++ XBoxed_list x1) ++ unBox_formula A :: (A :: XBoxed_list x0) ++ unBox_formula A :: XBoxed_list l ++ [Box A0]).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
      assert (XBoxed_list x ++ XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x0 ++ XBoxed_list l ++ [Box A0] =
      (XBoxed_list x ++ XBoxed_list x1) ++ unBox_formula A :: (A :: XBoxed_list x0) ++ XBoxed_list l ++ [Box A0]).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
      assert (Γ0 ++ B :: x2 ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ B :: x2) ++ A :: Γ3 ++ A :: Γ4).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
      assert (Γ0 ++ B :: x2 ++ A :: Γ3 ++ Γ4 = (Γ0 ++ B :: x2) ++ A :: Γ3 ++ Γ4).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
      subst. auto. auto.
  + left.
      inversion u1. subst. exfalso. assert (In A (x ++ x1 ++ A :: l)). apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
      apply H2 in H. destruct H. subst. apply f ; exists x0 ; auto. subst.
      apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
      inversion u3. subst. exfalso. assert (In A (x ++ x1 ++ x0 ++ A :: l)).
      apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
      apply H2 in H. destruct H. subst. apply f ; exists x3 ; auto. subst.
      exists (Γ0 ++ B :: x2 ++ A :: Γ3 ++ Γ4, C).
      repeat rewrite <- app_assoc ; repeat split ; auto.
      repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. apply univ_gen_ext_combine ; auto.
      assert (Γ0 ++ B :: x2 ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ B :: x2) ++ A :: Γ3 ++ A :: Γ4).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
      assert (Γ0 ++ B :: x2 ++ A :: Γ3 ++ Γ4 = (Γ0 ++ B :: x2) ++ A :: Γ3 ++ Γ4).
      repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
- repeat destruct s ; repeat destruct p ; subst.
  apply list_split_form in e0. destruct e0.
  repeat destruct s ; repeat destruct p ; subst.
  + right.
    apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p ; subst.
    repeat rewrite <- app_assoc in H2.
    inversion u1. subst. exfalso. simpl in H2. assert (In (Box A0 → B) (x2 ++ Box A0 → B :: l ++ x0)).
    apply in_or_app ; right ;  apply in_eq. apply H2 in H. destruct H. inversion H. subst.
    destruct (dec_is_boxedT B).
    *  right. exists A0. exists B. exists (XBoxed_list (x2 ++ x3) ++ B :: XBoxed_list x0 ++ [Box A0], A0).
        exists (XBoxed_list (x2 ++ x3 ++ [B] ++ x0) ++ [Box A0], A0). exists (Γ2 ++ B :: x1 ++ B :: Γ1, C).
        exists (Γ2 ++ B :: x1 ++ Γ1, C). repeat rewrite <- app_assoc ; repeat split. intro. intros.
        apply in_app_or in H ; destruct H. apply H2. apply in_or_app ; auto.
        apply in_app_or in H ; destruct H. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
        simpl in H. destruct H. subst. destruct i. subst. exists x. auto.
        apply H2. apply in_or_app ; right ; apply in_or_app ; auto. simpl.
        repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
        assert (XBoxed_list x2 ++ XBoxed_list x3 ++ XBoxed_list x0 ++ [Box A0] = (XBoxed_list x2 ++ XBoxed_list x3) ++ XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; auto. rewrite H.
        assert (XBoxed_list x2 ++ XBoxed_list x3 ++ B :: XBoxed_list x0 ++ [Box A0] = (XBoxed_list x2 ++ XBoxed_list x3) ++ B :: XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; auto. rewrite H0. apply wkn_LI.
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        assert (XBoxed_list x2 ++ XBoxed_list x3 ++ B :: XBoxed_list x0 ++ [Box A0] = (XBoxed_list x2 ++ XBoxed_list x3) ++ B :: XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; auto. rewrite H.
        assert (XBoxed_list x2 ++ XBoxed_list x3 ++ unBox_formula B :: B :: XBoxed_list x0 ++ [Box A0] = (XBoxed_list x2 ++ XBoxed_list x3) ++ unBox_formula B :: B :: XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; auto. rewrite H0. apply wkn_LI. auto.
        repeat apply univ_gen_ext_combine ; auto. auto.
     *  left. exists A0. exists B. exists (Γ2 ++ B :: x1 ++ B :: Γ1, C). exists (Γ2 ++ B :: x1 ++ Γ1, C).
        repeat rewrite <- app_assoc ; repeat split ; auto.
        repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. repeat apply univ_gen_ext_combine ; auto.
  + left.
    apply univ_gen_ext_splitR in u0. destruct u0. repeat destruct s. repeat destruct p ; subst.
    apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p ; subst.
    destruct (dec_is_boxedT A).
    *  right.
        inversion u1. subst. 2: exfalso ; auto. inversion u2. subst. 2: exfalso ; auto.
        exists (XBoxed_list x0 ++ unBox_formula A :: A :: XBoxed_list (l0 ++ x2) ++ unBox_formula A :: XBoxed_list l ++ [Box A0], A0).
        exists (XBoxed_list (x0 ++ A :: l0 ++ x2 ++ l) ++ [Box A0], A0). exists (Γ2 ++ A :: x1 ++ B :: x3 ++ Γ4, C).
        repeat rewrite <- app_assoc ; repeat split ; auto.
        assert (Γ2 ++ A :: x1 ++ B :: x3 ++ Γ4 = (Γ2 ++ A :: x1) ++ B :: x3 ++ Γ4). rewrite <- app_assoc ; auto. rewrite H.
        assert (Γ2 ++ A :: x1 ++ [Box A0 → B] ++ x3 ++ Γ4 = (Γ2 ++ A :: x1) ++ Box A0 → B :: x3 ++ Γ4). rewrite <- app_assoc ; auto. rewrite H0.
        apply BoxImpLRule_I ; auto. intro. intros. rewrite <- app_assoc in H2. simpl in H2.
        apply in_app_or in H1 ; destruct H1. apply H2. apply in_or_app ; auto.
        simpl in H1. destruct H1. subst. destruct i. subst. exists x. auto.
        apply in_app_or in H1 ; destruct H1. apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; auto.
        apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; right ; apply in_or_app ; auto.
        apply in_app_or in H1. destruct H1 ; auto. right ; apply in_cons ; auto.
        repeat rewrite <- app_assoc ; simpl.
        repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto. repeat apply univ_gen_ext_combine ; auto.
        repeat rewrite <- app_assoc ; simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        assert (XBoxed_list x0 ++ unBox_formula A :: A :: XBoxed_list l0 ++ XBoxed_list x2 ++ unBox_formula A :: A :: XBoxed_list l ++ [Box A0] =
        (XBoxed_list x0 ++ [unBox_formula A]) ++ A :: (XBoxed_list l0 ++ XBoxed_list x2 ++ [unBox_formula A]) ++ A :: XBoxed_list l ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (XBoxed_list x0 ++ unBox_formula A :: A :: XBoxed_list l0 ++ XBoxed_list x2 ++ unBox_formula A :: XBoxed_list l ++ [Box A0] =
        (XBoxed_list x0 ++ [unBox_formula A]) ++ A :: (XBoxed_list l0 ++ XBoxed_list x2 ++ [unBox_formula A]) ++ XBoxed_list l ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
        repeat rewrite <- app_assoc ; simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        assert (XBoxed_list x0 ++ unBox_formula A :: A :: XBoxed_list l0 ++ XBoxed_list x2 ++ unBox_formula A :: XBoxed_list l ++ [Box A0] =
        XBoxed_list x0 ++ unBox_formula A :: (A :: XBoxed_list l0 ++ XBoxed_list x2) ++ unBox_formula A :: XBoxed_list l ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
        assert (XBoxed_list x0 ++ unBox_formula A :: A :: XBoxed_list l0 ++ XBoxed_list x2 ++ XBoxed_list l ++ [Box A0] =
        XBoxed_list x0 ++ unBox_formula A :: (A :: XBoxed_list l0 ++ XBoxed_list x2) ++ XBoxed_list l ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
        assert (Γ2 ++ (A :: x1) ++ B :: x3 ++ A :: Γ4 = Γ2 ++ A :: (x1 ++ B :: x3 )++ A :: Γ4).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (Γ2 ++ A :: x1 ++ B :: x3 ++ Γ4 = Γ2 ++ A :: (x1 ++ B :: x3) ++ Γ4).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
    *  left.
        inversion u1. subst. exfalso. rewrite <- app_assoc in H2. assert (In A (x0 ++ x5 ++ x2 ++ A :: l)).
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
        apply H2 in H. destruct H. subst. apply f ; exists x ; auto. subst.
        inversion u2. subst. exfalso. rewrite <- app_assoc in H2. simpl in H2. assert (In A (x0 ++ A :: l ++ x2 ++ x4)).
        apply in_or_app ; right ; apply in_eq.
        apply H2 in H. destruct H. subst. apply f ; exists x ; auto. subst.
        exists (Γ2 ++ A :: x1 ++ B :: x3 ++ Γ4, C).
        repeat rewrite <- app_assoc ; repeat split ; auto.
        assert (Γ2 ++ A :: x1 ++ B :: x3 ++ Γ4 = (Γ2 ++ A :: x1) ++ B :: x3 ++ Γ4). rewrite <- app_assoc ; auto. rewrite H.
        assert (Γ2 ++ A :: x1 ++ [Box A0 → B] ++ x3 ++ Γ4 = (Γ2 ++ A :: x1) ++ Box A0 → B :: x3 ++ Γ4). rewrite <- app_assoc ; auto. rewrite H0.
        apply BoxImpLRule_I ; auto. rewrite <- app_assoc in H2 ; auto. rewrite <- app_assoc. simpl.
        repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. repeat apply univ_gen_ext_combine ; auto.
        assert (Γ2 ++ (A :: x1) ++ B :: x3 ++ A :: Γ4 = Γ2 ++ A :: (x1 ++ B :: x3) ++ A :: Γ4).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (Γ2 ++ A :: x1 ++ B :: x3 ++ Γ4 = Γ2 ++ A :: (x1 ++ B :: x3) ++ Γ4).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
  + repeat destruct s. repeat destruct p ; subst. left.
    apply univ_gen_ext_splitR in u. destruct u. repeat destruct s. repeat destruct p ; subst.
    destruct (dec_is_boxedT A).
    *  right.
        inversion u1. subst. 2: exfalso ; auto. apply univ_gen_ext_splitR in X ; destruct X.
        destruct s. repeat destruct p ; subst. inversion u3. subst. 2: exfalso ; auto.
        exists (XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x ++ unBox_formula A :: XBoxed_list (l ++ x0) ++ [Box A0], A0).
        exists (XBoxed_list (x1 ++ A :: x ++ l ++ x0) ++ [Box A0], A0). exists (Γ2 ++ A :: Γ3 ++ x2 ++ B :: Γ1, C) .
        repeat rewrite <- app_assoc ; repeat split ; auto.
        assert (Γ2 ++ A :: Γ3 ++ x2 ++ B :: Γ1 = (Γ2 ++ A :: Γ3 ++ x2) ++ B :: Γ1).
        repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H.
        assert (Γ2 ++ A :: Γ3 ++ x2 ++ Box A0 → B :: Γ1 = (Γ2 ++ A :: Γ3 ++ x2) ++ Box A0 → B :: Γ1).
        repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; auto. rewrite H0.
        apply BoxImpLRule_I ; auto. rewrite <- app_assoc in H2. simpl in H2. rewrite <- app_assoc in H2.
        simpl in H2. intro. intros. apply in_app_or in H1 ; destruct H1. apply H2. apply in_or_app ; auto.
        simpl in H1. destruct H1. subst. destruct i. subst. exists x3. auto.
        apply in_app_or in H1 ; destruct H1. apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; auto.
        apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; right ; apply in_cons ; auto.
        repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc.
        repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto. repeat apply univ_gen_ext_combine ; auto.
        repeat rewrite <- app_assoc ; simpl ; rewrite <- app_assoc ; simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
        assert (XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list l ++ XBoxed_list x0 ++ [Box A0] =
        (XBoxed_list x1 ++ [unBox_formula A]) ++ A :: (XBoxed_list x ++ [unBox_formula A]) ++ A :: XBoxed_list l ++ XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x ++ unBox_formula A :: XBoxed_list l ++ XBoxed_list x0 ++ [Box A0] =
        (XBoxed_list x1 ++ [unBox_formula A]) ++ A :: (XBoxed_list x ++ [unBox_formula A]) ++ XBoxed_list l ++ XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
        repeat rewrite <- app_assoc ; simpl. repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. simpl.
        assert (XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x ++ unBox_formula A :: XBoxed_list l ++ XBoxed_list x0 ++ [Box A0] =
        XBoxed_list x1 ++ unBox_formula A :: (A :: XBoxed_list x) ++ unBox_formula A :: XBoxed_list l ++ XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
        assert (XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x ++ XBoxed_list l ++ XBoxed_list x0 ++ [Box A0] =
        XBoxed_list x1 ++ unBox_formula A :: (A :: XBoxed_list x) ++ XBoxed_list l ++ XBoxed_list x0 ++ [Box A0]).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; apply ctr_LI.
    *  left.
        inversion u1. subst. exfalso. rewrite <- app_assoc in H2. simpl in H2. assert (In A (x1 ++ A :: l ++ x0)).
        apply in_or_app ; right ; apply in_eq. apply H2 in H. destruct H. subst. apply f ; exists x ; auto. subst.
        apply univ_gen_ext_splitR in X ; destruct X. destruct s ; repeat destruct p ; subst.
        inversion u3. subst. exfalso. repeat rewrite <- app_assoc in H2. simpl in H2. assert (In A (x1 ++ x ++ A :: l ++ x0)).
        apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
        apply H2 in H. destruct H. subst. apply f ; exists x3 ; auto. subst.
        exists (Γ2 ++ A :: Γ3 ++ x2 ++ B :: Γ1, C).
        repeat rewrite <- app_assoc ; repeat split ; auto.
        assert (Γ2 ++ A :: Γ3 ++ x2 ++ B :: Γ1 = (Γ2 ++ A :: Γ3 ++ x2) ++ B :: Γ1).
        rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
        assert (Γ2 ++ A :: Γ3 ++ x2 ++ Box A0 → B :: Γ1 = (Γ2 ++ A :: Γ3 ++ x2) ++ Box A0 → B :: Γ1).
        rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
        apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc in H2 ; auto. rewrite <- app_assoc. simpl. rewrite <- app_assoc.
        repeat apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto. repeat apply univ_gen_ext_combine ; auto.
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; apply ctr_LI.
Qed.

Lemma GLR_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (GLRRule [ps] s) ->
    ((GLRRule [ps] sc) +
     (existsT2 psc1 psc2, (GLRRule [psc2] sc) * (@ctr_L A ps psc1) * (@ctr_L (unBox_formula A) psc1 psc2) * (is_boxedT A))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. rewrite <- H1 in H2.
inversion H2. subst. apply univ_gen_ext_elem_deep with (l3:=Γ0) (l4:=Γ1 ++ A :: Γ2) (a:=A) in X.
destruct X. 3: reflexivity.
- destruct p. apply univ_gen_ext_elem_deep with (l3:=Γ0 ++ Γ1) (l4:=Γ2) (a:=A) in u. destruct u. destruct p.
3: rewrite <- app_assoc. 3: reflexivity.
  * left. apply GLRRule_I.
    assumption.
    apply univ_gen_ext_add_elem_deep. rewrite app_assoc. assumption. assumption.
  * exfalso. apply f. repeat destruct s. repeat destruct p. subst. apply is_box_is_in_boxed_list with (A:=A) in H0 .
    unfold is_boxedT. destruct H0. exists x1. auto. apply in_or_app. right. apply in_eq.
- repeat destruct s. repeat destruct p. apply univ_gen_ext_elem_deep with (l3:=Γ1) (l4:=Γ2) (a:=A) in u0.
  destruct u0. 3: reflexivity.
  * destruct p. exfalso. subst. apply is_box_is_in_boxed_list with (A:=A) in H0. apply f. unfold is_boxedT.
    destruct H0. exists x1. auto. apply in_or_app. right. apply in_eq.
  * repeat destruct s. repeat destruct p. right. subst.
    exists ((XBoxed_list x) ++ (XBoxed_list [A]) ++ (XBoxed_list x1) ++ (unBox_formula A) :: (XBoxed_list x2) ++ [Box A0], A0).
    exists (XBoxed_list (x ++ A :: x1 ++ x2) ++ [Box A0], A0). split.
    + repeat split.
      { intro. intros. apply H0. apply in_app_or in H. destruct H. apply in_or_app. left. assumption.
        inversion H. subst. apply in_or_app. right. apply in_eq. apply in_app_or in H1. destruct H1.
        apply in_or_app. right. apply in_cons. apply in_or_app. left. assumption.
        apply in_or_app. right. apply in_cons. apply in_or_app. right. apply in_cons.
        assumption. }
      { apply univ_gen_ext_combine. assumption. apply univ_gen_ext_cons. apply univ_gen_ext_combine.
        assumption. assumption. }
      { repeat rewrite cons_single. repeat rewrite XBox_app_distrib. simpl.
        assert (E1: (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x2) ++ [Box A0] =
                     ((XBoxed_list x ++ [unBox_formula A]) ++ A :: (XBoxed_list x1 ++ [unBox_formula A]) ++ A :: XBoxed_list x2 ++ [Box A0])).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
        assert (E2: XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ unBox_formula A :: XBoxed_list x2 ++ [Box A0] =
                    (XBoxed_list x ++ [unBox_formula A]) ++ A :: (XBoxed_list x1 ++ [unBox_formula A]) ++ XBoxed_list x2 ++ [Box A0]).
        simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E2. apply ctr_LI. }
    { simpl. repeat rewrite XBox_app_distrib. simpl. repeat rewrite XBox_app_distrib.
      assert (E1: XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ unBox_formula A :: XBoxed_list x2 ++ [Box A0] =
                  XBoxed_list x ++ unBox_formula A :: (A :: XBoxed_list x1) ++ unBox_formula A :: XBoxed_list x2 ++ [Box A0]).
      simpl. repeat rewrite <- app_assoc. auto. rewrite E1.
      assert (E2: (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ XBoxed_list x2) ++ [Box A0] =
                  XBoxed_list x ++ unBox_formula A :: (A :: XBoxed_list x1) ++ XBoxed_list x2 ++ [Box A0]).
      simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
      apply ctr_LI. }
    + apply H0. apply in_or_app ; right ; apply in_eq.
Qed.

(* Now we can prove that contraction is admissible. *)

Theorem GL4ip_ctr_L : forall (m k: nat) s
        (D0 : derrec GL4ip_rules (fun _ => False) s),
        k = (derrec_height D0) ->
          (forall sc A,
          (m = weight_form A) ->
          (@ctr_L A s sc) ->
          derrec GL4ip_rules (fun _ => False) sc).
Proof.
(* Setting up the strong induction on the weight. *)
pose (strong_inductionT (fun (x:nat) => forall (k: nat) s
        (D0 : derrec GL4ip_rules (fun _ => False) s),
        k = (derrec_height D0) ->
          (forall sc A,
          (x = weight_form A) ->
          (@ctr_L A s sc) ->
          derrec GL4ip_rules (fun _ => False) sc))).
apply d. intros n PIH. clear d.

(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
(D0 : derrec GL4ip_rules (fun _ : Seq => False) s),
x = derrec_height D0 ->
forall (sc : Seq) (A : MPropF),
n = weight_form A ->
ctr_L A s sc ->
derrec GL4ip_rules (fun _ : Seq => False) sc)).
apply d. intros m SIH. clear d.

assert (DersNil: dersrec (GL4ip_rules) (fun _ : Seq => False) []). apply dersrec_nil.

(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- intros hei sc A ctr. inversion f.
(* D0 ends with an application of rule *)
- intros hei sc A wei ctr. inversion ctr. inversion g.
  (* IdP *)
  * inversion H1. rewrite <- H in H5. inversion H5. subst.
    assert (InT (# P) (Γ0 ++ A :: Γ1 ++ Γ2)).
    assert (InT (# P) (Γ0 ++ A :: Γ1 ++ A :: Γ2)). rewrite <- H7. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H. destruct H. apply InT_or_app ; auto. inversion i. subst. apply InT_or_app. right.
    apply InT_eq. subst. apply InT_app_or in H0. destruct H0. apply InT_or_app. right. apply InT_cons.
    apply InT_or_app ; auto. inversion i0. subst. apply InT_or_app. right. apply InT_eq. subst. apply InT_or_app.
    right. apply InT_cons. apply InT_or_app ; auto.
    apply InT_split in H. destruct H. destruct s. rewrite e. pose (IdPRule_I P x x0). apply IdP in i.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, # P) i DersNil). auto.
  (* BotL *)
  * inversion H1. rewrite <- H in H5. inversion H5. subst.
    assert (InT (Bot) (Γ0 ++ A :: Γ1 ++ Γ2)).
    assert (InT (Bot) (Γ0 ++ A :: Γ1 ++ A :: Γ2)). rewrite <- H7. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H. destruct H. apply InT_or_app ; auto. inversion i. subst. apply InT_or_app. right.
    apply InT_eq. subst. apply InT_app_or in H0. destruct H0. apply InT_or_app. right. apply InT_cons.
    apply InT_or_app ; auto. inversion i0. subst. apply InT_or_app. right. apply InT_eq. subst. apply InT_or_app.
    right. apply InT_cons. apply InT_or_app ; auto.
    apply InT_split in H. destruct H. destruct s. rewrite e. pose (BotLRule_I x x0 A0). apply BotL in b.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ Bot :: x0, A0) b DersNil). auto.
  (* AndR *)
  * inversion H1. subst. inversion H5. subst. pose (AndR_app_ctr_L ctr H1). repeat destruct s.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    simpl in SIH.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x1) E (Γ0 ++ A :: Γ1 ++ A :: Γ2, A1) x1 E1 x A E11 c0).
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (SIH (derrec_height x2) E2 (Γ0 ++ A :: Γ1 ++ A :: Γ2, B) x2 E3 x0 A E11 c).
    pose (dlCons d1 DersNil). pose (dlCons d0 d2). apply AndR in a.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A1 ∧ B) a d3). auto.
  (* AndL *)
  * inversion H1. subst. inversion H5. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
     pose (AndL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 :: B :: Γ4, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply AndL in a.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) a d1). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (AndR_AndL_hpinv _ _ _ J1). destruct p. clear s0. pose (s _ a0). destruct s0. clear s.
       assert (E: weight_form x0 < weight_form (x0 ∧ x1)). simpl. lia.
       assert (E1: derrec_height x5 = derrec_height x5). auto.
       assert (E11: weight_form x0 = weight_form x0). auto.
       pose (PIH _ E (derrec_height x5) x2 x5 E1 x3 x0 E11 c0).
       assert (E2: weight_form x1 < weight_form (x0 ∧ x1)). simpl. lia.
       assert (E3: derrec_height d0 = derrec_height d0). auto.
       assert (E12: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E2 (derrec_height d0) x3 d0 E3 x4 x1 E12 c).
       pose (dlCons d1 DersNil). apply AndL in a.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x4]) (Γ0 ++ x0 ∧ x1 :: Γ1 ++ Γ2, A0) a d2). auto.
  (* OrR1 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR1_app_ctr_L ctr H1). repeat destruct s.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x0) E (Γ0 ++ A :: Γ1 ++ A :: Γ2, A1) x0 E1 x A E11 c).
    pose (dlCons d0 DersNil). apply OrR1 in o.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1 ++ Γ2, A1 ∨ B) o d1). auto.
  (* OrR2 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR2_app_ctr_L ctr H1). repeat destruct s.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x0) E (Γ0 ++ A :: Γ1 ++ A :: Γ2, B) x0 E1 x A E11 c).
    pose (dlCons d0 DersNil). apply OrR2 in o.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1 ++ Γ2, A1 ∨ B) o d1). auto.
  (* OrL *)
  * inversion H1. subst. inversion H5. subst.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    pose (OrL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 :: Γ4, A0) x E1 x1 A E11 c0).
        assert (E2: derrec_height x0 < S (dersrec_height d)). lia.
        assert (E3: derrec_height x0 = derrec_height x0). auto.
        pose (SIH (derrec_height x0) E2 (Γ3 ++ B :: Γ4, A0) x0 E3 x2 A E11 c).
        pose (dlCons d1 DersNil). pose (dlCons d0 d2). apply OrL in o.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[x1;x2]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) o d3). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (OrL_hpinv _ _ _ J1 _ _ o1). repeat destruct s. destruct p.
       assert (J2: derrec_height x0 = derrec_height x0). auto.
       pose (OrL_hpinv _ _ _ J2 _ _ o0). repeat destruct s. destruct p.
       assert (E: weight_form x1 < weight_form (x1 ∨ x2)). simpl ; lia.
       assert (E1: derrec_height x9 = derrec_height x9). auto.
       assert (E11: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E (derrec_height x9) x3 x9 E1 x7 x1 E11 c0).
       assert (E2: weight_form x2 < weight_form (x1 ∨ x2)). simpl ; lia.
       assert (E3: derrec_height x12 = derrec_height x12). auto.
       assert (E12: weight_form x2 = weight_form x2). auto.
       pose (PIH _ E2 (derrec_height x12) x6 x12 E3 x8 x2 E12 c).
       pose (dlCons d1 DersNil). pose (dlCons d0 d2). apply OrL in o.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x7; x8]) (Γ0 ++ x1 ∨ x2 :: Γ1 ++ Γ2, A0) o d3). auto.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (ImpR_app_ctr_L ctr H1). destruct s.
    repeat destruct p.
    assert (E: derrec_height x < S (dersrec_height d)). lia.
    assert (E1: derrec_height x = derrec_height x). auto. simpl in SIH.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x) E (Γ3 ++ A1 :: Γ4, B) x E1 x0 A E11 c).
    pose (dlCons d0 DersNil). apply ImpR in i.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
    (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A1 → B) i d1). auto.
  (* AtomImpL1 *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (AtomImpL1_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto. simpl in SIH.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ # P :: Γ4 ++ A1 :: Γ5, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply AtomImpL1 in a.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) a d1). auto.
    + assert (existsT2 D2 : derrec GL4ip_rules (fun _ : Seq => False) x2,
       derrec_height D2 <= derrec_height x).
       { destruct s0.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL1_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL2_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia. }
       destruct X.
       assert (E: weight_form x1 < weight_form (# x0 → x1)). simpl ; lia.
       assert (E1: derrec_height x4 = derrec_height x4). auto.
       assert (E11: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E (derrec_height x4) x2 x4 E1 x3 x1 E11 c).
       pose (dlCons d0 DersNil). destruct s.
       apply AtomImpL1 in a.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x3]) (Γ0 ++ # x0 → x1 :: Γ1 ++ Γ2, A0) a d1). auto.
       apply AtomImpL2 in a.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x3]) (Γ0 ++ # x0 → x1 :: Γ1 ++ Γ2, A0) a d1). auto.
  (* AtomImpL2 *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (AtomImpL2_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto. simpl in SIH.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 :: Γ4 ++ # P :: Γ5, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). destruct s.
        apply AtomImpL1 in a.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) a d1). auto.
        apply AtomImpL2 in a.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) a d1). auto.
    + assert (existsT2 D2 : derrec GL4ip_rules (fun _ : Seq => False) x2,
       derrec_height D2 <= derrec_height x).
       { destruct s0.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL1_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL2_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia. }
       destruct X.
       assert (E: weight_form x1 < weight_form (# x0 → x1)). simpl ; lia.
       assert (E1: derrec_height x4 = derrec_height x4). auto.
       assert (E11: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E (derrec_height x4) x2 x4 E1 x3 x1 E11 c).
       pose (dlCons d0 DersNil). destruct s.
       apply AtomImpL1 in a.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x3]) (Γ0 ++ # x0 → x1 :: Γ1 ++ Γ2, A0) a d1). auto.
       apply AtomImpL2 in a.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x3]) (Γ0 ++ # x0 → x1 :: Γ1 ++ Γ2, A0) a d1). auto.
  (* AndImpL *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (AndImpL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 → B → C :: Γ4, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply AndImpL in a.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) a d1). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (AndImpL_hpinv _ _ _ J1 _ a0). destruct s.
       assert (E: weight_form (x0 → x1 → x2) < weight_form ((x0 ∧ x1) → x2)). simpl ; lia.
       assert (E1: derrec_height x5 = derrec_height x5). auto.
       assert (E11: weight_form (x0 → x1 → x2) = weight_form (x0 → x1 → x2)). auto.
       pose (PIH _ E (derrec_height x5) x3 x5 E1 x4 (x0 → x1 → x2) E11 c).
       pose (dlCons d0 DersNil). apply AndImpL in a.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x4]) (Γ0 ++ (x0 ∧ x1) → x2 :: Γ1 ++ Γ2, A0) a d1). auto.
  (* OrImpL *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (OrImpL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E  (Γ3 ++ A1 → C :: Γ4 ++ B → C :: Γ5, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply OrImpL in o.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
        (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) o d1). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (OrImpL_hpinv _ _ _ J1 _ o0). destruct s.
       assert (E: weight_form (x0 → x2) < weight_form ((x0 ∨ x1) → x2)). simpl ; lia.
       assert (E1: derrec_height x6 = derrec_height x6). auto.
       assert (E11: weight_form (x0 → x2) = weight_form (x0 → x2)). auto.
       pose (PIH _ E (derrec_height x6) x3 x6 E1 x4 (x0 → x2) E11 c0).
       assert (E2: weight_form (x1 → x2) < weight_form ((x0 ∨ x1) → x2)). simpl ; lia.
       assert (E3: derrec_height d0 = derrec_height d0). auto.
       assert (E12: weight_form (x1 → x2) = weight_form (x1 → x2)). auto.
       pose (PIH _ E2 (derrec_height d0) x4 d0 E3 x5 (x1 → x2) E12 c).
       pose (dlCons d1 DersNil). apply OrImpL in o.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x5]) (Γ0 ++ (x0 ∨ x1) → x2 :: Γ1 ++ Γ2, A0) o d2). auto.
  (* ImpImpL *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H0. destruct H0. repeat destruct s ; repeat destruct p ; subst.
    +  assert (J1: derrec_height x = derrec_height x). auto.
        assert (J2: (Γ0 ++ B → C :: Γ1 ++ (A1 → B) → C :: Γ2, A1 → B) = ((Γ0 ++ B → C :: Γ1) ++ (A1 → B) → C :: Γ2, A1 → B)).
        repeat rewrite <- app_assoc ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J1 J2). rewrite <- app_assoc in d0. simpl in d0.
        assert (E: weight_form (B → C) < weight_form ((A1 → B) → C)). simpl ; lia.
        assert (E1: derrec_height d0 = derrec_height d0). auto.
        assert (E2: weight_form (B → C) = weight_form (B → C)). auto.
        assert (E3: ctr_L (B → C) (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: B → C :: Γ2, A1 → B) (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: Γ2, A1 → B)).
        assert (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: B → C :: Γ2 = Γ0 ++ B → C :: (Γ1 ++ [A1]) ++ B → C :: B → C :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: Γ2 = Γ0 ++ B → C :: (Γ1 ++ [A1]) ++ B → C :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
        pose (PIH _ E (derrec_height d0) _ _ E1 _ _ E2 E3).
        assert (E4: derrec_height d1 = derrec_height d1). auto.
        assert (E5: ctr_L (B → C) (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: Γ2, A1 → B) (Γ0 ++ B → C :: Γ1 ++ A1 :: Γ2, A1 → B)).
        assert (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: Γ2 = Γ0 ++ B → C :: (Γ1 ++ [A1]) ++ B → C :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (Γ0 ++ B → C :: Γ1 ++ A1 :: Γ2 = Γ0 ++ B → C :: (Γ1 ++ [A1]) ++ Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
        pose (PIH _ E (derrec_height d1) _ _ E4 _ _ E2 E5).
        assert (E6: ImpRRule [(Γ0 ++ A1 :: B → C :: Γ1 ++ A1 :: Γ2, B)] (Γ0 ++ B → C :: Γ1 ++ A1 :: Γ2, A1 → B)).
        apply ImpRRule_I.
        pose (ImpR_inv _ _ d2 E6).
        assert (E7: weight_form A1 < weight_form ((A1 → B) → C)). simpl ; lia.
        assert (E8: derrec_height d3 = derrec_height d3). auto.
        assert (E9: weight_form A1 = weight_form A1). auto.
        assert (E10: ctr_L A1(Γ0 ++ A1 :: B → C :: Γ1 ++ A1 :: Γ2, B) (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)).
        assert (Γ0 ++ A1 :: B → C :: Γ1 ++ A1 :: Γ2 = Γ0 ++ A1 :: (B → C :: Γ1) ++ A1 :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2 = Γ0 ++ A1 :: (B → C :: Γ1) ++ Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
        pose (PIH _ E7 (derrec_height d3) _ _ E8 _ _ E9 E10).
        apply derI with (ps:=[(Γ0 ++ B → C :: Γ1 ++ Γ2, A1 → B);(Γ0 ++ C :: Γ1 ++ Γ2, A0)]).
        apply ImpImpL. apply ImpImpLRule_I. apply dlCons.
        apply derI with (ps:=[(Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)]). apply ImpR. apply ImpRRule_I.
        apply dlCons ; auto. apply dlCons ; auto.
        assert (E11: ImpImpLRule [((Γ0 ++ C :: Γ1) ++ B → C :: Γ2, A1 → B);((Γ0 ++ C :: Γ1) ++ C :: Γ2, A0)]
        ((Γ0 ++ C :: Γ1) ++ (A1 → B) → C :: Γ2, A0)). apply ImpImpLRule_I. repeat rewrite <- app_assoc in E11.
        simpl in E11.
        pose (ImpImpL_inv_R _ _ _ x0 E11).
        assert (E12: weight_form C < weight_form ((A1 → B) → C)). simpl ; lia.
        assert (E13: derrec_height d5 = derrec_height d5). auto.
        assert (E14: weight_form C = weight_form C). auto.
        assert (E15: ctr_L C (Γ0 ++ C :: Γ1 ++ C :: Γ2, A0) (Γ0 ++ C :: Γ1 ++ Γ2, A0)). apply ctr_LI.
        pose (PIH _ E12 (derrec_height d5) _ _ E13 _ _ E14 E15). auto.
    +  apply list_split_form in e2. destruct e2. repeat destruct s ; repeat destruct p ; subst.
        {  assert (J1: derrec_height x = derrec_height x). auto.
            assert (J2: (((Γ0 ++ [(A1 → B) → C]) ++ Γ1) ++ B → C :: Γ2, A1 → B) = (Γ0 ++ (A1 → B) → C :: Γ1 ++ B → C :: Γ2, A1 → B)).
            repeat rewrite <- app_assoc ; auto.
            pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J1 J2).
            assert (E: weight_form (B → C) < weight_form ((A1 → B) → C)). simpl ; lia.
            assert (E1: derrec_height d0 = derrec_height d0). auto.
            assert (E2: weight_form (B → C) = weight_form (B → C)). auto.
            assert (E3: ctr_L (B → C) (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ B → C :: Γ2, A1 → B) (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2, A1 → B)).
            assert (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A1]) ++ B → C :: (B → C :: Γ1) ++ B → C :: Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
            assert (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A1]) ++ B → C :: (B → C :: Γ1) ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
            pose (PIH _ E (derrec_height d0) _ _ E1 _ _ E2 E3).
            assert (E4: derrec_height d1 = derrec_height d1). auto.
            assert (E5: ctr_L (B → C) (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2, A1 → B) (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, A1 → B)).
            assert (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A1]) ++ B → C :: [] ++ B → C :: Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
            assert (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A1]) ++ B → C :: [] ++ Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
            pose (PIH _ E (derrec_height d1) _ _ E4 _ _ E2 E5).
            assert (E6: ImpRRule [(Γ0 ++ A1 :: A1 :: B → C :: Γ1 ++ Γ2, B)] (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, A1 → B)).
            apply ImpRRule_I.
            pose (ImpR_inv _ _ d2 E6).
            assert (E7: weight_form A1 < weight_form ((A1 → B) → C)). simpl ; lia.
            assert (E8: derrec_height d3 = derrec_height d3). auto.
            assert (E9: weight_form A1 = weight_form A1). auto.
            assert (E10: ctr_L A1(Γ0 ++ A1 :: A1 :: B → C :: Γ1 ++ Γ2, B) (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)).
            assert (Γ0 ++ A1 :: A1 :: B → C :: Γ1 ++ Γ2 = Γ0 ++ A1 :: [] ++ A1 :: B → C :: Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
            assert (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2 = Γ0 ++ A1 :: [] ++ B → C :: Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
            pose (PIH _ E7 (derrec_height d3) _ _ E8 _ _ E9 E10).
            apply derI with (ps:=[(Γ0 ++ B → C :: Γ1 ++ Γ2, A1 → B);(Γ0 ++ C :: Γ1 ++ Γ2, A0)]).
            apply ImpImpL. apply ImpImpLRule_I. apply dlCons.
            apply derI with (ps:=[(Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)]). apply ImpR. apply ImpRRule_I.
            apply dlCons ; auto. apply dlCons ; auto.
            assert (E11: ImpImpLRule [(Γ0 ++ B → C :: Γ1 ++ C :: Γ2, A1 → B);(Γ0 ++ C :: Γ1 ++ C :: Γ2, A0)]
            (((Γ0 ++ [(A1 → B) → C]) ++ Γ1) ++ C :: Γ2, A0)). repeat rewrite <- app_assoc ; simpl.
            apply ImpImpLRule_I.
            pose (ImpImpL_inv_R _ _ _ x0 E11).
            assert (E12: weight_form C < weight_form ((A1 → B) → C)). simpl ; lia.
            assert (E13: derrec_height d5 = derrec_height d5). auto.
            assert (E14: weight_form C = weight_form C). auto.
            assert (E15: ctr_L C (Γ0 ++ C :: Γ1 ++ C :: Γ2, A0) (Γ0 ++ C :: Γ1 ++ Γ2, A0)). apply ctr_LI.
            pose (PIH _ E12 (derrec_height d5) _ _ E13 _ _ E14 E15). auto. }
        {  assert (E: derrec_height x < S (dersrec_height d)). lia.
           assert (E1: derrec_height x = derrec_height x). auto.
           assert (E2: weight_form A = weight_form A). auto.
           assert (E3: ctr_L A (((Γ0 ++ [A]) ++ (Γ1 ++ [A]) ++ x3) ++ B → C :: Γ4, A1 → B) (Γ0 ++ A :: Γ1 ++ x3 ++ B → C :: Γ4, A1 → B)).
           repeat rewrite <- app_assoc ; simpl. apply ctr_LI.
           pose (SIH (derrec_height x) E _ x E1 _ _ E2 E3).
           assert (E4: derrec_height x0 < S (dersrec_height d)). lia.
           assert (E5: derrec_height x0 = derrec_height x0). auto.
           assert (E6: ctr_L A (((Γ0 ++ [A]) ++ (Γ1 ++ [A]) ++ x3) ++ C :: Γ4, A0) (Γ0 ++ A :: Γ1 ++ x3 ++ C :: Γ4, A0)).
           repeat rewrite <- app_assoc ; simpl. apply ctr_LI.
           pose (SIH (derrec_height x0) E4 _ x0 E5 _ _ E2 E6).
           pose (dlCons d1 DersNil). pose (dlCons d0 d2).
           apply derI with (ps:=[(Γ0 ++ A :: Γ1 ++ x3 ++ B → C :: Γ4, A1 → B); (Γ0 ++ A :: Γ1 ++ x3 ++ C :: Γ4, A0)]) ; auto.
           apply ImpImpL.
           assert (Γ0 ++ A :: Γ1 ++ x3 ++ B → C :: Γ4 = (Γ0 ++ A :: Γ1 ++ x3) ++ B → C :: Γ4).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: Γ1 ++ x3 ++ C :: Γ4 = (Γ0 ++ A :: Γ1 ++ x3) ++  C :: Γ4).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
           assert (Γ0 ++ A :: Γ1 ++ x3 ++(A1 → B) → C :: Γ4 = (Γ0 ++ A :: Γ1 ++ x3) ++ (A1 → B) → C :: Γ4).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply ImpImpLRule_I. }
        {  repeat destruct s ; repeat destruct p ; subst.
           assert (E: derrec_height x < S (dersrec_height d)). lia.
           assert (E1: derrec_height x = derrec_height x). auto.
           assert (E2: weight_form A = weight_form A). auto.
           assert (E3: ctr_L A (((Γ0 ++ [A]) ++ x2) ++ B → C :: x1 ++ A :: Γ2, A1 → B) (Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2, A1 → B)).
           assert (((Γ0 ++ [A]) ++ x2) ++ B → C :: x1 ++ A :: Γ2 =Γ0 ++ A :: (x2 ++ B → C :: x1) ++ A :: Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2 =Γ0 ++ A :: (x2 ++ B → C :: x1) ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
           pose (SIH (derrec_height x) E _ x E1 _ _ E2 E3).
           assert (E4: derrec_height x0 < S (dersrec_height d)). lia.
           assert (E5: derrec_height x0 = derrec_height x0). auto.
           assert (E6: ctr_L A (((Γ0 ++ [A]) ++ x2) ++ C :: x1 ++ A :: Γ2, A0) (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2, A0)).
           assert (((Γ0 ++ [A]) ++ x2) ++ C :: x1 ++ A :: Γ2 =Γ0 ++ A :: (x2 ++ C :: x1) ++ A :: Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2 =Γ0 ++ A :: (x2 ++ C :: x1) ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
           pose (SIH (derrec_height x0) E4 _ x0 E5 _ _ E2 E6).
           pose (dlCons d1 DersNil). pose (dlCons d0 d2).
           apply derI with (ps:=[(Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2, A1 → B); (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2, A0)]) ; auto.
           apply ImpImpL.
           assert (Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2 = (Γ0 ++ A :: x2) ++ B → C :: x1 ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2 = (Γ0 ++ A :: x2) ++ C :: x1 ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
           assert (Γ0 ++ A :: (x2 ++ (A1 → B) → C :: x1) ++ Γ2 = (Γ0 ++ A :: x2) ++ (A1 → B) → C :: x1 ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply ImpImpLRule_I. }
    + repeat destruct s ; repeat destruct p ; subst.
       assert (E: derrec_height x < S (dersrec_height d)). lia.
       assert (E1: derrec_height x = derrec_height x). auto.
       assert (E2: weight_form A = weight_form A). auto.
       assert (E3: ctr_L A (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ A :: Γ2, A1 → B) (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ Γ2, A1 → B)).
       assert (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ A :: Γ2 =(Γ3 ++ B → C :: x1) ++ A :: Γ1 ++ A :: Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
       assert (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ Γ2 =(Γ3 ++ B → C :: x1) ++ A :: Γ1 ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
       pose (SIH (derrec_height x) E _ x E1 _ _ E2 E3).
       assert (E4: derrec_height x0 < S (dersrec_height d)). lia.
       assert (E5: derrec_height x0 = derrec_height x0). auto.
       assert (E6: ctr_L A (Γ3 ++ C :: x1 ++ A :: Γ1 ++ A :: Γ2, A0) (Γ3 ++ C :: x1 ++ A :: Γ1 ++ Γ2, A0)).
       assert (Γ3 ++ C :: x1 ++ A :: Γ1 ++ A :: Γ2 =(Γ3 ++ C :: x1) ++ A :: Γ1 ++ A :: Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
       assert (Γ3 ++ C :: x1 ++ A :: Γ1 ++ Γ2 =(Γ3 ++ C :: x1) ++ A :: Γ1 ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
       pose (SIH (derrec_height x0) E4 _ x0 E5 _ _ E2 E6).
       pose (dlCons d1 DersNil). pose (dlCons d0 d2).
       apply derI with (ps:=[(Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ Γ2, A1 → B); (Γ3 ++ C :: x1 ++ A :: Γ1 ++ Γ2, A0)]) ; auto.
       apply ImpImpL. repeat rewrite <- app_assoc. simpl. apply ImpImpLRule_I.
  (* BoxImpL *)
  * inversion X. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    pose (BoxImpL_app_ctr_L ctr X). repeat destruct s.
    + destruct p. simpl in SIH.
       assert (E2: derrec_height x0 < S (dersrec_height d)). lia.
       assert (E3: derrec_height x0 = derrec_height x0). auto.
       assert (E4: weight_form A = weight_form A). auto.
       pose (SIH _ E2 _ x0 E3 x1 A E4 c).
       pose (dlCons d0 DersNil). pose (dlCons x d1). apply BoxImpL in b.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[(XBoxed_list BΓ ++ [Box A1], A1); x1]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) b). auto.
    + repeat destruct p ; subst. simpl in PIH. simpl in SIH.
       assert (E2: derrec_height x0 < S (dersrec_height d)). lia.
       assert (E3: derrec_height x0 = derrec_height x0). auto.
       assert (E4: weight_form A = weight_form A). auto.
       pose (SIH _ E2 _ x0 E3 x3 A E4 c).
       assert (E8: derrec_height x < S (dersrec_height d)). lia.
       assert (E9: derrec_height x = derrec_height x). auto.
       assert (E10: weight_form A = weight_form A). auto.
       pose (SIH _ E8 _ x E9 x1 A E10 c1).
       assert (E5: weight_form (unBox_formula A) < weight_form A). destruct i. subst. simpl ; lia.
       assert (E6: derrec_height d1 = derrec_height d1). auto.
       assert (E7: weight_form (unBox_formula A) = weight_form (unBox_formula A)). auto.
       pose (PIH _ E5 (derrec_height d1) _ _ E6 _ _ E7 c0).
       pose (dlCons d0 DersNil). pose (dlCons d2 d3). apply BoxImpL in b.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
       (ps:=[x2;x3]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) b). auto.
    + repeat destruct p ; subst. simpl in PIH. simpl in SIH.
       apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A1], A1); x4]). apply BoxImpL ; auto.
       apply dlCons ; auto. apply dlCons ; auto.
       pose (BoxImpL_inv_R _ _ _ x0 b0).
       assert (E5: weight_form x2 < weight_form (Box x1 → x2)). simpl ; lia.
       assert (E6: derrec_height d0 = derrec_height d0). auto.
       assert (E7: weight_form x2 = weight_form x2). auto.
       pose (PIH _ E5 (derrec_height d0) _ _ E6 _ _ E7 c). auto.
    + repeat destruct p. subst. simpl in PIH ; simpl in SIH.
       apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A1], A1); x6]).
       apply BoxImpL ; auto. apply dlCons ; auto. apply dlCons ; auto.
       pose (BoxImpL_inv_R _ _ _ x0 b0).
       assert (E5: weight_form x2 < weight_form (Box x1 → x2)). simpl ; lia.
       assert (E6: derrec_height d0 = derrec_height d0). auto.
       assert (E7: weight_form x2 = weight_form x2). auto.
       pose (PIH _ E5 (derrec_height d0) _ _ E6 _ _ E7 c). auto.
  (* GLR *)
  * inversion X. rewrite <- H4 in X. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (GLR_app_ctr_L ctr X). destruct s.
    + apply GLR in g0. subst. pose (derI (rules:=GL4ip_rules)
      (prems:=fun _ : Seq => False) (ps:=[(XBoxed_list BΓ ++ [Box A1], A1)])
      (Γ0 ++ A :: Γ1 ++ Γ2, A0) g0 d). auto.
   + repeat destruct s. repeat destruct p. apply GLR in g0.
      assert (E3: derrec_height x < S (dersrec_height d)). lia.
      assert (E4: derrec_height x = derrec_height x). auto.
      assert (E5: weight_form A = weight_form A). auto.
      pose (SIH (derrec_height x) E3 _ x E4 x0 A E5 c0).
      assert (E: weight_form (unBox_formula A) < weight_form A). destruct i. subst. simpl ; lia.
      assert (E1: derrec_height d0 = derrec_height d0). auto.
      assert (E2: weight_form (unBox_formula A) = weight_form (unBox_formula A)). auto.
      pose (PIH _ E (derrec_height d0) _ _ E1 _ _ E2 c).
      pose (dlCons d1 DersNil).
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : Seq => False)
      (ps:=[x1]) (Γ0 ++ A :: Γ1 ++ Γ2, A0) g0 d2). auto.
Qed.

Theorem GL4ip_adm_ctr_L : forall s, (derrec GL4ip_rules (fun _ => False) s) ->
          (forall sc A, (@ctr_L A s sc) ->
          derrec GL4ip_rules (fun _ => False) sc).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
assert (J2: weight_form A = weight_form A). auto.
pose (@GL4ip_ctr_L (weight_form A) _ _ X J1 sc A J2 H). auto.
Qed.


