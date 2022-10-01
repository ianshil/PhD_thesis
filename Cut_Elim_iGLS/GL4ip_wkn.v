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
Require Import Lia.

Set Implicit Arguments.

(* We define the relation which takes care of the notion of weakening on the left. *)

Inductive wkn_L (fml : MPropF) : relationT Seq :=
  | wkn_LI Γ0 Γ1 A : wkn_L fml
        (Γ0 ++ Γ1, A) (Γ0 ++ fml :: Γ1, A).

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent sw which is a weakened
version of s, with some premises psw that are such that they are either the same premises
(in case the weakened formula is weakened in the rule) or weakened versions of ps. *)

Lemma AndR_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (AndRRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (AndRRule [psw1;psw2] sw) * (@wkn_L A ps1 psw1) * (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1, A0). exists (Γ0 ++ A :: Γ1, B). repeat split.
Qed.

Lemma AndL_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AndLRule [ps] s) ->
  (existsT2 psw, (AndLRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: A0 :: B :: Γ1, C). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. simpl.
  assert (Γ2 ++ A :: And A0 B :: Γ1 = (Γ2 ++ [A]) ++ And A0 B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
  apply AndLRule_I.
- exists ((Γ2 ++ A :: x) ++ A0 :: B :: Γ1, C). split.
  * assert (Γ2 ++ A :: x ++ And A0 B :: Γ1 = (Γ2 ++ A :: x) ++ And A0 B :: Γ1). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply AndLRule_I ; assumption.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A :: A0 :: B :: Γ1, C).
      split. assert (E1: Γ0 ++ A :: A0 :: B :: Γ1 = (Γ0 ++ [A]) ++ A0 :: B :: Γ1). rewrite <- app_assoc.
      simpl. auto. rewrite E1. assert (E2 : Γ0 ++ A :: And A0 B :: Γ1 = (Γ0 ++ [A]) ++ And A0 B :: Γ1).
      rewrite <- app_assoc. simpl. auto. rewrite E2. apply AndLRule_I.
      repeat rewrite <- app_assoc. apply wkn_LI.
    + inversion e0. subst. exists (Γ0 ++ A0 :: B :: x ++ A :: Γ3, C). split.
      repeat rewrite <- app_assoc. apply AndLRule_I.
      assert (Γ0 ++ A0 :: B :: x ++ A :: Γ3 = (Γ0 ++ A0 :: B :: x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0.
      assert (Γ0 ++ A0 :: B :: x ++ Γ3 = (Γ0 ++ A0 :: B :: x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
Qed.

Lemma OrR1_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (OrR1Rule [ps] s) ->
  (existsT2 psw, (OrR1Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1, A0). repeat split.
Qed.

Lemma OrR2_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (OrR2Rule [ps] s) ->
  (existsT2 psw, (OrR2Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1, B). repeat split.
Qed.

Lemma OrL_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (OrLRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (OrLRule [psw1;psw2] sw) * (@wkn_L A ps1 psw1) * (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: A0 :: Γ1, C). exists (Γ2 ++ A :: B :: Γ1, C). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. simpl.
  assert (Γ2 ++ A :: B :: Γ1 = (Γ2 ++ [A]) ++ B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
  assert (Γ2 ++ A :: Or A0 B :: Γ1 = (Γ2 ++ [A]) ++ Or A0 B :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H1.
  apply OrLRule_I.
- exists ((Γ2 ++ A :: x) ++ A0 :: Γ1, C). exists ((Γ2 ++ A :: x) ++ B :: Γ1, C). repeat split.
  * assert (Γ2 ++ A :: x ++ Or A0 B :: Γ1 = (Γ2 ++ A :: x) ++ Or A0 B :: Γ1). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply OrLRule_I ; assumption.
  * repeat rewrite <- app_assoc. apply wkn_LI.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A :: A0 :: Γ1, C). exists (Γ0 ++ A :: B :: Γ1, C).
      repeat split. assert (E1: Γ0 ++ A :: A0 :: Γ1 = (Γ0 ++ [A]) ++ A0 :: Γ1). rewrite <- app_assoc.
      simpl. auto. rewrite E1.  assert (E11: Γ0 ++ A :: B :: Γ1 = (Γ0 ++ [A]) ++ B :: Γ1). rewrite <- app_assoc.
      simpl. auto. rewrite E11. assert (E2 : Γ0 ++ A :: Or A0 B :: Γ1 = (Γ0 ++ [A]) ++ Or A0 B :: Γ1).
      rewrite <- app_assoc. simpl. auto. rewrite E2. apply OrLRule_I.
    + inversion e0. subst. exists (Γ0 ++ A0 :: x ++ A :: Γ3, C). exists (Γ0 ++ B :: x ++ A :: Γ3, C). repeat split.
      repeat rewrite <- app_assoc. apply OrLRule_I.
      assert (Γ0 ++ A0 :: x ++ A :: Γ3 = (Γ0 ++ A0 :: x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0.
      assert (Γ0 ++ A0 :: x ++ Γ3 = (Γ0 ++ A0 :: x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
      assert (Γ0 ++ B :: x ++ A :: Γ3 = (Γ0 ++ B :: x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0.
      assert (Γ0 ++ B :: x ++ Γ3 = (Γ0 ++ B :: x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
Qed.

Lemma ImpR_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (ImpRRule [ps] s) ->
  (existsT2 psw, (ImpRRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A0 :: A :: Γ3, B). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. rewrite app_assoc with (l:=Γ2).
  apply wkn_LI.
- exists ((Γ2 ++ A :: x) ++ A0 :: Γ1, B). split.
  * assert (Γ2 ++ A :: x ++ Γ1 = (Γ2 ++ A :: x) ++ Γ1). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply ImpRRule_I ; assumption.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- exists (Γ0 ++ A0 :: x ++ A :: Γ3, B). split.
  * repeat rewrite <- app_assoc. apply ImpRRule_I ; assumption.
  * rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. rewrite app_assoc with (l:=Γ0).
    rewrite app_assoc. rewrite app_assoc with (l:=(Γ0 ++ [A0])). apply wkn_LI.
Qed.

Lemma AtomImpL1_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AtomImpL1Rule [ps] s) ->
  (existsT2 psw, (AtomImpL1Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ3 ++ A :: # P :: Γ1 ++ A0 :: Γ2, C). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=# P). rewrite app_assoc. simpl.
  assert (Γ3 ++ A :: # P :: Γ1 ++ Imp # P A0 :: Γ2 = (Γ3 ++ [A]) ++ # P :: Γ1 ++  Imp # P A0 :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
  apply AtomImpL1Rule_I.
- exists ((Γ3 ++ A :: x) ++ # P :: Γ1 ++ A0 :: Γ2, C). split.
  * assert (Γ3 ++ A :: x ++ # P :: Γ1 ++  Imp # P A0 :: Γ2 = (Γ3 ++ A :: x) ++ # P :: Γ1 ++ (Imp # P A0) :: Γ2). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply AtomImpL1Rule_I.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A :: # P :: Γ1 ++ A0 :: Γ2, C).
      split. assert (E1: Γ0 ++ A :: # P :: Γ1 ++ A0 :: Γ2 = (Γ0 ++ [A]) ++ # P :: Γ1 ++ A0 :: Γ2). rewrite <- app_assoc.
      simpl. auto. rewrite E1. assert (E2 : Γ0 ++ A :: # P :: Γ1 ++ (Imp # P A0) :: Γ2 = (Γ0 ++ [A]) ++ # P :: Γ1 ++ (Imp # P A0) :: Γ2).
      rewrite <- app_assoc. simpl. auto. rewrite E2. apply AtomImpL1Rule_I.
      repeat rewrite <- app_assoc. apply wkn_LI.
    + inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
       * exists (Γ0 ++ # P :: (Γ1 ++ [A]) ++ A0 :: Γ2, C). split.
         assert ((Γ0 ++ # P :: Γ1) ++ A :: (Imp # P A0) :: Γ2 = Γ0 ++ # P :: (Γ1 ++ [A]) ++ (Imp # P A0) :: Γ2). repeat rewrite <- app_assoc.
         simpl. auto. rewrite H0. apply AtomImpL1Rule_I.
         assert (Γ0 ++ # P :: Γ1 ++ A0 :: Γ2 = (Γ0 ++ # P :: Γ1) ++ A0 :: Γ2). rewrite <- app_assoc. reflexivity.
         rewrite H0.
         assert (Γ0 ++ # P :: (Γ1 ++ [A]) ++ A0 :: Γ2 = (Γ0 ++ # P :: Γ1) ++ A :: A0 :: Γ2). repeat rewrite <- app_assoc. reflexivity.
         rewrite H1. apply wkn_LI.
       * destruct x0 ;  subst ; repeat rewrite app_nil_r.
         { simpl in e1. subst. exists (Γ0 ++ # P :: (Γ1 ++ [A]) ++ A0 :: Γ2, C). split.
           assert ((Γ0 ++ # P :: Γ1) ++ A :: (Imp # P A0) :: Γ2 = Γ0 ++ # P :: (Γ1 ++ [A]) ++ (Imp # P A0) :: Γ2). repeat rewrite <- app_assoc.
           simpl. auto. rewrite H0. apply AtomImpL1Rule_I.
           assert (Γ0 ++ # P :: Γ1 ++ A0 :: Γ2 = (Γ0 ++ # P :: Γ1) ++ A0 :: Γ2). rewrite <- app_assoc. reflexivity.
           rewrite H0.
           assert (Γ0 ++ # P :: (Γ1 ++ [A]) ++ A0 :: Γ2 = (Γ0 ++ # P :: Γ1) ++ A :: A0 :: Γ2). repeat rewrite <- app_assoc. reflexivity.
           rewrite H1. apply wkn_LI. }
        { simpl in e1. inversion e1 ; subst.
          exists (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ A :: Γ4, C). split. repeat rewrite <- app_assoc. simpl.
          repeat rewrite <- app_assoc. simpl. apply AtomImpL1Rule_I.
          assert (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ Γ4 = (Γ0 ++ # P :: Γ1 ++ A0 :: x0) ++ Γ4). rewrite <- app_assoc. simpl.
          rewrite <- app_assoc. reflexivity. rewrite H0.
          assert (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ A :: Γ4 = (Γ0 ++ # P :: Γ1 ++ A0 :: x0) ++ A :: Γ4). repeat rewrite <- app_assoc. simpl.
          repeat rewrite <- app_assoc. reflexivity. rewrite H1. apply wkn_LI. }
       * exists (Γ0 ++ # P :: (x ++ A :: x0) ++ A0 :: Γ2, C). split.
         assert ((Γ0 ++ # P :: x) ++ A :: x0 ++ (Imp # P A0) :: Γ2 = Γ0 ++ # P :: (x ++ A :: x0) ++ (Imp # P A0) :: Γ2). repeat rewrite <- app_assoc.
         simpl. auto. rewrite H0. apply AtomImpL1Rule_I.
         assert (Γ0 ++ # P :: (x ++ x0) ++ A0 :: Γ2 = (Γ0 ++ # P :: x) ++ x0 ++ A0 :: Γ2). rewrite <- app_assoc. simpl.
         rewrite <- app_assoc. reflexivity. rewrite H0.
         assert (Γ0 ++ # P :: (x ++ A :: x0) ++ A0 :: Γ2 = (Γ0 ++ # P :: x) ++ A :: x0 ++ A0 :: Γ2). repeat rewrite <- app_assoc. reflexivity.
         rewrite H1. apply wkn_LI.
Qed.

Lemma AtomImpL2_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AtomImpL2Rule [ps] s) ->
  (existsT2 psw, (AtomImpL2Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ3 ++ A :: A0 :: Γ1 ++ # P :: Γ2, C). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. simpl.
  assert (Γ3 ++ A :: Imp # P A0 :: Γ1 ++ # P :: Γ2 = (Γ3 ++ [A]) ++ Imp # P A0 :: Γ1 ++  # P :: Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
  apply AtomImpL2Rule_I.
- exists ((Γ3 ++ A :: x) ++ A0 :: Γ1 ++ # P :: Γ2, C). split.
  * assert (Γ3 ++ A :: x ++ Imp # P A0 :: Γ1 ++  # P :: Γ2 = (Γ3 ++ A :: x) ++ (Imp # P A0) :: Γ1 ++ # P :: Γ2). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply AtomImpL2Rule_I.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A :: A0 :: Γ1 ++ # P :: Γ2, C).
      split. assert (E1: Γ0 ++ A :: A0 :: Γ1 ++ # P :: Γ2 = (Γ0 ++ [A]) ++ A0 :: Γ1 ++ # P :: Γ2). rewrite <- app_assoc.
      simpl. auto. rewrite E1. assert (E2 : Γ0 ++ A :: (Imp # P A0) :: Γ1 ++  # P :: Γ2 = (Γ0 ++ [A]) ++ (Imp # P A0) :: Γ1 ++ # P :: Γ2).
      rewrite <- app_assoc. simpl. auto. rewrite E2. apply AtomImpL2Rule_I.
      repeat rewrite <- app_assoc. apply wkn_LI.
    + inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
       * exists (Γ0 ++ A0 :: (Γ1 ++ [A]) ++ # P :: Γ2, C). split.
         assert ((Γ0 ++ (Imp # P A0) :: Γ1) ++ A :: # P :: Γ2 = Γ0 ++ (Imp # P A0) :: (Γ1 ++ [A]) ++ # P :: Γ2). repeat rewrite <- app_assoc.
         simpl. auto. rewrite H0. apply AtomImpL2Rule_I.
         assert (Γ0 ++ A0 :: Γ1 ++ # P :: Γ2 = (Γ0 ++ A0 :: Γ1) ++ # P :: Γ2). rewrite <- app_assoc. reflexivity.
         rewrite H0.
         assert (Γ0 ++ A0 :: (Γ1 ++ [A]) ++ # P :: Γ2 = (Γ0 ++ A0 :: Γ1) ++ A :: # P :: Γ2). repeat rewrite <- app_assoc. reflexivity.
         rewrite H1. apply wkn_LI.
       * destruct x0 ;  subst ; repeat rewrite app_nil_r.
         { simpl in e1. subst. exists (Γ0 ++ A0 :: (Γ1 ++ [A]) ++ # P :: Γ2, C). split.
           assert ((Γ0 ++ (Imp # P A0) :: Γ1) ++ A :: # P :: Γ2 = Γ0 ++(Imp # P A0)  :: (Γ1 ++ [A]) ++ # P :: Γ2). repeat rewrite <- app_assoc.
           simpl. auto. rewrite H0. apply AtomImpL2Rule_I.
           assert (Γ0 ++A0  :: Γ1 ++ # P :: Γ2 = (Γ0 ++ A0 :: Γ1) ++ # P :: Γ2). rewrite <- app_assoc. reflexivity.
           rewrite H0.
           assert (Γ0 ++ A0 :: (Γ1 ++ [A]) ++ # P :: Γ2 = (Γ0 ++ A0 :: Γ1) ++ A :: # P :: Γ2). repeat rewrite <- app_assoc. reflexivity.
           rewrite H1. apply wkn_LI. }
        { simpl in e1. inversion e1 ; subst.
          exists (Γ0 ++ A0 :: Γ1 ++ # P :: x0 ++ A :: Γ4, C). split. repeat rewrite <- app_assoc. simpl.
          repeat rewrite <- app_assoc. simpl. apply AtomImpL2Rule_I.
          assert (Γ0 ++A0  :: Γ1 ++ # P :: x0 ++ Γ4 = (Γ0 ++ A0 :: Γ1 ++ # P :: x0) ++ Γ4). rewrite <- app_assoc. simpl.
          rewrite <- app_assoc. reflexivity. rewrite H0.
          assert (Γ0 ++  A0:: Γ1 ++ # P :: x0 ++ A :: Γ4 = (Γ0 ++ A0 :: Γ1 ++ # P :: x0) ++ A :: Γ4). repeat rewrite <- app_assoc. simpl.
          repeat rewrite <- app_assoc. reflexivity. rewrite H1. apply wkn_LI. }
       * exists (Γ0 ++ A0 :: (x ++ A :: x0) ++ # P :: Γ2, C). split.
         assert ((Γ0 ++ (Imp # P A0) :: x) ++ A :: x0 ++ # P :: Γ2 = Γ0 ++ (Imp # P A0) :: (x ++ A :: x0) ++ # P :: Γ2). repeat rewrite <- app_assoc.
         simpl. auto. rewrite H0. apply AtomImpL2Rule_I.
         assert (Γ0 ++ A0 :: (x ++ x0) ++ # P :: Γ2 = (Γ0 ++ A0 :: x) ++ x0 ++ # P :: Γ2). rewrite <- app_assoc. simpl.
         rewrite <- app_assoc. reflexivity. rewrite H0.
         assert (Γ0 ++ A0 :: (x ++ A :: x0) ++ # P :: Γ2 = (Γ0 ++A0  :: x) ++ A :: x0 ++ # P :: Γ2). repeat rewrite <- app_assoc. reflexivity.
         rewrite H1. apply wkn_LI.
Qed.

Lemma AndImpL_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AndImpLRule [ps] s) ->
  (existsT2 psw, (AndImpLRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: (Imp A0 (Imp B C)) :: Γ1, D). repeat split ; try assumption.
  rewrite cons_single. rewrite app_assoc.
  assert (Γ2 ++ A :: (Imp (And A0 B) C) :: Γ1 = (Γ2 ++ [A]) ++ (Imp (And A0 B) C) :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
  apply AndImpLRule_I.
- exists ((Γ2 ++ A :: x) ++ (Imp A0 (Imp B C)) :: Γ1, D). split.
  * assert (Γ2 ++ A :: x ++ Imp (And A0 B) C :: Γ1 = (Γ2 ++ A :: x) ++ Imp (And A0 B) C :: Γ1). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply AndImpLRule_I.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A :: (Imp A0 (Imp B C)) :: Γ1, D).
      split. assert (E1: Γ0 ++ A :: (Imp A0 (Imp B C)) :: Γ1 = (Γ0 ++ [A]) ++ (Imp A0 (Imp B C)) :: Γ1). rewrite <- app_assoc.
      simpl. auto. rewrite E1. assert (E2 : Γ0 ++ A :: (Imp (And A0 B) C) :: Γ1 = (Γ0 ++ [A]) ++ (Imp (And A0 B) C) :: Γ1).
      rewrite <- app_assoc. simpl. auto. rewrite E2. apply AndImpLRule_I.
      repeat rewrite <- app_assoc. apply wkn_LI.
    + inversion e0. subst. exists (Γ0 ++ (Imp A0 (Imp B C)) :: x ++ A :: Γ3, D). split.
      repeat rewrite <- app_assoc. apply AndImpLRule_I.
      assert (Γ0 ++ (Imp A0 (Imp B C)) :: x ++ A :: Γ3 = (Γ0 ++ (Imp A0 (Imp B C)) :: x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0.
      assert (Γ0 ++ (Imp A0 (Imp B C)) :: x ++ Γ3 = (Γ0 ++ (Imp A0 (Imp B C)) :: x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
Qed.

Lemma OrImpL_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (OrImpLRule [ps] s) ->
  (existsT2 psw, (OrImpLRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ3 ++ A :: (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2, D). repeat split ; try assumption.
  rewrite cons_single. rewrite app_assoc.
  assert (Γ3 ++ A :: (Imp (Or A0 B) C) :: Γ1 ++ Γ2 = (Γ3 ++ [A]) ++ (Imp (Or A0 B) C) :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto. rewrite H0.
  apply OrImpLRule_I.
- exists ((Γ3 ++ A :: x) ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2, D). split.
  * assert (Γ3 ++ A :: x ++ (Imp (Or A0 B) C) :: Γ1 ++ Γ2 = (Γ3 ++ A :: x) ++ (Imp (Or A0 B) C) :: Γ1 ++ Γ2). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply OrImpLRule_I.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A :: (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2, D).
      split. assert (E1: Γ0 ++ A :: (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2 = (Γ0 ++ [A]) ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2). rewrite <- app_assoc.
      simpl. auto. rewrite E1. assert (E2 : Γ0 ++ A :: (Imp (Or A0 B) C) :: Γ1 ++  Γ2 = (Γ0 ++ [A]) ++ (Imp (Or A0 B) C) :: Γ1 ++  Γ2).
      rewrite <- app_assoc. simpl. auto. rewrite E2. apply OrImpLRule_I.
      repeat rewrite <- app_assoc. apply wkn_LI.
    + inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
       * exists (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: A :: Γ2, D). split.
          repeat rewrite <- app_assoc. simpl. apply OrImpLRule_I.
          assert (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2 = (Γ0 ++ (Imp A0 C) :: Γ1 ++ [(Imp B C)]) ++ Γ2). repeat rewrite <- app_assoc. simpl.
          rewrite <- app_assoc. reflexivity. rewrite H0.
          assert (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: A :: Γ2 = (Γ0 ++ (Imp A0 C) :: Γ1 ++ [(Imp B C)]) ++ A :: Γ2). rewrite <- app_assoc. simpl.
          rewrite <- app_assoc. reflexivity. rewrite H1. apply wkn_LI.
       * exists (Γ0 ++ (Imp A0 C) :: Γ1 ++  (Imp B C) :: x0 ++ A :: Γ4, D). split. repeat rewrite <- app_assoc.  simpl. 
          repeat rewrite <- app_assoc. apply OrImpLRule_I.
          assert (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: x0 ++ Γ4 = (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: x0) ++ Γ4). repeat rewrite <- app_assoc. simpl.
          rewrite <- app_assoc. reflexivity. rewrite H0.
          assert (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) ::  x0 ++ A :: Γ4 = (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: x0) ++ A :: Γ4). rewrite <- app_assoc. simpl.
          rewrite <- app_assoc. reflexivity. rewrite H1. apply wkn_LI.
       * exists (Γ0 ++ (Imp A0 C) :: (x ++ A :: x0) ++ (Imp B C) :: Γ2, D). split.
         assert ((Γ0 ++ (Imp (Or A0 B) C) :: x) ++ A :: x0 ++ Γ2 = Γ0 ++ (Imp (Or A0 B) C) :: (x ++ A :: x0) ++ Γ2). repeat rewrite <- app_assoc. auto.
         rewrite H0.  apply OrImpLRule_I.
          assert (Γ0 ++ (Imp A0 C) :: (x ++ x0) ++ (Imp B C) :: Γ2 = (Γ0 ++ (Imp A0 C) :: x) ++ x0 ++ (Imp B C) :: Γ2). repeat rewrite <- app_assoc. simpl.
          reflexivity. rewrite H0.
          assert (Γ0 ++ (Imp A0 C) :: (x ++ A :: x0) ++ (Imp B C) :: Γ2 = (Γ0 ++ (Imp A0 C) :: x) ++ A :: x0 ++ (Imp B C) :: Γ2). rewrite <- app_assoc. simpl.
          rewrite <- app_assoc. reflexivity. rewrite H1. apply wkn_LI.
Qed.

Lemma ImpImpL_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (ImpImpLRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (ImpImpLRule [psw1;psw2] sw) * (@wkn_L A ps1 psw1) * (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: (Imp B C) :: Γ1, (Imp A0 B)). exists (Γ2 ++ A :: C :: Γ1, D). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A). rewrite app_assoc. rewrite app_assoc.
  assert (Γ2 ++ A :: ((Imp (Imp A0 B)) C) :: Γ1 = (Γ2 ++ [A]) ++ ((Imp (Imp A0 B)) C) :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
  apply ImpImpLRule_I.
- exists ((Γ2 ++ A :: x) ++ (Imp B C) :: Γ1, (Imp A0 B)). exists ((Γ2 ++ A :: x) ++ C :: Γ1, D). repeat split.
  * assert (Γ2 ++ A :: x ++ ((Imp (Imp A0 B)) C) :: Γ1 = (Γ2 ++ A :: x) ++ ((Imp (Imp A0 B)) C) :: Γ1). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply ImpImpLRule_I.
  * repeat rewrite <- app_assoc. apply wkn_LI.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists ((Γ0 ++ [A]) ++ (Imp B C) :: Γ1, (Imp A0 B)) . exists ((Γ0 ++ [A]) ++ C :: Γ1, D).
      repeat split. assert (E1: Γ0 ++ A :: ((Imp (Imp A0 B)) C) :: Γ1 = (Γ0 ++ [A]) ++ ((Imp (Imp A0 B)) C) :: Γ1). rewrite <- app_assoc.
      simpl. auto. rewrite E1. apply ImpImpLRule_I. repeat rewrite <- app_assoc. apply wkn_LI. repeat rewrite <- app_assoc. apply wkn_LI.
    + inversion e0. subst. exists (Γ0 ++ (Imp B C) :: x ++ A :: Γ3, (Imp A0 B)). exists (Γ0 ++ C :: x ++ A :: Γ3, D). repeat split.
      repeat rewrite <- app_assoc. simpl. apply ImpImpLRule_I.
      assert (Γ0 ++ (Imp B C) :: x ++ A :: Γ3 = (Γ0 ++ (Imp B C) :: x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0.
      assert (Γ0 ++ (Imp B C) :: x ++ Γ3 = (Γ0 ++ (Imp B C) :: x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
      assert (Γ0 ++ C :: x ++ A :: Γ3 = (Γ0 ++ C :: x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0.
      assert (Γ0 ++ C :: x ++ Γ3 = (Γ0 ++ C :: x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
Qed.

Lemma BoxImpL_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (BoxImpLRule [ps1;ps2] s) ->
  (existsT2 psw2, (@wkn_L A ps2 psw2) *
          ((BoxImpLRule [ps1;psw2] sw) + (existsT2 psw1 psw3, (BoxImpLRule [psw3;psw2] sw)
            * (@wkn_L (unBox_formula A) ps1 psw1) * (@wkn_L A psw1 psw3)))).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
apply univ_gen_ext_splitR in X. destruct X. repeat destruct s. repeat destruct p. subst.
inversion H3. subst. apply app2_find_hole in H0. destruct H0.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: B :: Γ1, C). split. apply wkn_LI.
  assert (Γ2 ++ A :: B :: Γ1 = (Γ2 ++ [A]) ++ B :: Γ1). rewrite <- app_assoc. auto. rewrite H. clear H.
  assert (Γ2 ++ A :: (Imp (Box A0) B) :: Γ1 = (Γ2 ++ [A]) ++ (Imp  (Box A0) B) :: Γ1). rewrite <- app_assoc. auto. rewrite H. clear H.
  destruct (dec_is_boxedT A).
  + right. exists ((XBoxed_list x) ++ (unBox_formula A) :: (XBoxed_list x0) ++ [Box A0], A0).
     exists (XBoxed_list (x ++ A :: x0) ++ [Box A0], A0). repeat split. intro. intros. apply in_app_or in H. destruct H.
     apply H2. apply in_or_app. auto.
     inversion H. subst. inversion i. subst. exists x2. auto. apply H2. apply in_or_app. auto. rewrite <- app_assoc. simpl.
     apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. auto. repeat rewrite XBox_app_distrib.
     repeat rewrite <- app_assoc. apply wkn_LI. repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
     assert (XBoxed_list x ++ unBox_formula A :: XBoxed_list x0 ++ [Box A0] = (XBoxed_list x ++ [unBox_formula A]) ++ XBoxed_list x0 ++ [Box A0]).
     repeat rewrite <- app_assoc. auto. rewrite H. clear H.
     assert (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x0 ++ [Box A0] = (XBoxed_list x ++ [unBox_formula A]) ++ A :: XBoxed_list x0 ++ [Box A0]).
     repeat rewrite <- app_assoc. auto. rewrite H. clear H. apply wkn_LI.
  + left. apply BoxImpLRule_I ; auto. repeat rewrite <- app_assoc. simpl. apply univ_gen_ext_combine ; auto.
     apply univ_gen_ext_extra ; auto.
- exists ((Γ2 ++ A :: x1) ++ B :: Γ1, C). split. repeat rewrite <- app_assoc. simpl. apply wkn_LI.
  assert (Γ2 ++ A :: x1 ++ (Imp (Box A0) B) :: Γ1 = (Γ2 ++ A :: x1) ++  (Imp (Box A0) B) :: Γ1). rewrite <- app_assoc. auto. rewrite H. clear H.
  destruct (dec_is_boxedT A).
  + right. apply univ_gen_ext_splitR in u. destruct u. destruct s. destruct p. subst. destruct p.
     exists ((XBoxed_list x2) ++ (unBox_formula A) :: (XBoxed_list (x3 ++ x0)) ++ [Box A0], A0).
     exists (XBoxed_list (x2 ++ A :: x3 ++ x0) ++ [Box A0], A0). repeat split. intro. intros. apply in_app_or in H. destruct H.
     apply H2. apply in_or_app. left. apply in_or_app. auto.
     inversion H. subst. inversion i. subst. exists x. auto. apply H2. apply in_app_or in H0. destruct H0.
     apply in_or_app. left. apply in_or_app. auto. apply in_or_app. auto. rewrite <- app_assoc. simpl.
     apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. apply univ_gen_ext_combine ; auto.
     repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
     repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl. rewrite XBox_app_distrib.
     repeat rewrite <- app_assoc.
     assert (XBoxed_list x2 ++ unBox_formula A :: XBoxed_list x3 ++ XBoxed_list x0 ++ [Box A0] =
     (XBoxed_list x2 ++ [unBox_formula A]) ++ XBoxed_list x3 ++ XBoxed_list x0 ++ [Box A0]).
     repeat rewrite <- app_assoc. auto. rewrite H. clear H.
     assert (XBoxed_list x2 ++ unBox_formula A :: A :: XBoxed_list x3 ++ XBoxed_list x0 ++ [Box A0] =
     (XBoxed_list x2 ++ [unBox_formula A]) ++ A :: XBoxed_list x3 ++ XBoxed_list x0 ++ [Box A0]).
     repeat rewrite <- app_assoc. auto. rewrite H. clear H. apply wkn_LI.
  + left. apply BoxImpLRule_I ; auto. simpl. apply univ_gen_ext_combine ; auto.
     apply univ_gen_ext_add_elem_deep ; auto.
- destruct x1 ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. clear H3. exists ((Γ0 ++ [A]) ++ B :: Γ1, C) . split. repeat rewrite <- app_assoc. simpl. apply wkn_LI.
       assert (Γ0 ++ A :: (Imp (Box A0) B) :: Γ1 = (Γ0 ++ [A]) ++  (Imp (Box A0) B) :: Γ1). rewrite <- app_assoc. auto. rewrite H. clear H.
       destruct (dec_is_boxedT A).
       * right.
         exists ((XBoxed_list x) ++ (unBox_formula A) :: (XBoxed_list x0) ++ [Box A0], A0).
         exists (XBoxed_list (x ++ A :: x0) ++ [Box A0], A0). repeat split. intro. intros. apply in_app_or in H. destruct H.
         apply H2. apply in_or_app. left. auto.
         inversion H. subst. inversion i. subst. exists x1. auto. apply H2. apply in_or_app. auto. rewrite <- app_assoc. simpl.
         apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
         repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
         repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
         assert (XBoxed_list x ++ unBox_formula A :: XBoxed_list x0 ++ [Box A0] =
         (XBoxed_list x ++ [unBox_formula A]) ++ XBoxed_list x0 ++ [Box A0]).
         repeat rewrite <- app_assoc. auto. rewrite H. clear H.
         assert (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x0 ++ [Box A0] =
         (XBoxed_list x ++ [unBox_formula A]) ++ A :: XBoxed_list x0 ++ [Box A0]).
         repeat rewrite <- app_assoc. auto. rewrite H. clear H. apply wkn_LI.
       * left. apply BoxImpLRule_I ; auto. rewrite <- app_assoc. simpl. apply univ_gen_ext_combine ; auto.
          apply univ_gen_ext_extra ; auto.
    +  inversion e0. subst. apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p.
        subst. exists (Γ0 ++ B :: x1 ++ A :: Γ3, C). split. assert (Γ0 ++ B :: x1 ++ Γ3 =(Γ0 ++ B :: x1) ++ Γ3).
        repeat rewrite <- app_assoc. auto. rewrite H. clear H. assert (Γ0 ++ B :: x1 ++ A :: Γ3 =(Γ0 ++ B :: x1) ++ A :: Γ3).
        repeat rewrite <- app_assoc. auto. rewrite H. clear H. apply wkn_LI. destruct (dec_is_boxedT A).
        * right. exists ((XBoxed_list x) ++ (XBoxed_list x2) ++ (unBox_formula A) :: (XBoxed_list x3) ++ [Box A0], A0).
           exists (XBoxed_list (x ++ x2 ++ A :: x3) ++ [Box A0], A0). rewrite <- app_assoc. repeat split. intro. intros. apply in_app_or in H. destruct H.
           apply H2. apply in_or_app. left. auto. apply in_app_or in H. destruct H. apply H2. apply in_or_app ; right ; apply in_or_app ; auto.
           inversion H. subst. inversion i. subst. exists x0. auto. apply H2. apply in_or_app. right. apply in_or_app. auto.
           apply univ_gen_ext_combine ; auto. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons ; auto.
           repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc.
           assert (XBoxed_list x ++ XBoxed_list x2 ++ XBoxed_list x3 ++ [Box A0] = (XBoxed_list x ++ XBoxed_list x2) ++ XBoxed_list x3 ++ [Box A0]).
           repeat rewrite <- app_assoc. auto. rewrite H. clear H.
           assert (XBoxed_list x ++ XBoxed_list x2 ++ unBox_formula A :: XBoxed_list x3 ++ [Box A0] = (XBoxed_list x ++ XBoxed_list x2) ++ unBox_formula A :: XBoxed_list x3 ++ [Box A0]).
           repeat rewrite <- app_assoc. auto. rewrite H. clear H. apply wkn_LI.
           repeat rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
           assert (XBoxed_list x ++ XBoxed_list x2 ++ unBox_formula A :: XBoxed_list x3 ++ [Box A0] =
           (XBoxed_list x ++ XBoxed_list x2 ++ [unBox_formula A]) ++ XBoxed_list x3 ++ [Box A0]).
           repeat rewrite <- app_assoc. auto. rewrite H. clear H.
           assert (XBoxed_list x ++ XBoxed_list x2 ++ unBox_formula A :: A :: XBoxed_list x3 ++ [Box A0] =
           (XBoxed_list x ++ XBoxed_list x2 ++ [unBox_formula A]) ++ A :: XBoxed_list x3 ++ [Box A0]).
           repeat rewrite <- app_assoc. auto. rewrite H. clear H. apply wkn_LI.
        * left. repeat rewrite <- app_assoc.
          apply BoxImpLRule_I ; auto. apply univ_gen_ext_combine ; auto.
          apply univ_gen_ext_combine ; auto. apply univ_gen_ext_extra ; auto.
Qed.

Lemma GLR_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (GLRRule [ps] s) ->
  ((GLRRule [ps] sw) +
   (existsT2 psw1 psw2, (GLRRule [psw2] sw) * (@wkn_L (unBox_formula A) ps psw1) * (@wkn_L A psw1 psw2))).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. rewrite <- H1 in H2.
inversion H2. subst. destruct (dec_is_boxedT A).
  * right. apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p.
    subst. exists (((XBoxed_list x) ++ (unBox_formula A) :: (XBoxed_list x0)) ++ [Box A0], A0).
    exists (XBoxed_list (x ++ A :: x0) ++ [Box A0], A0). split. split.
    + apply GLRRule_I. intro. intros. apply in_app_or in H. destruct H. apply H0. apply in_or_app. auto.
      inversion H. subst. assumption. apply H0. apply in_or_app. auto. apply univ_gen_ext_combine.
      assumption. apply univ_gen_ext_cons. assumption.
    + rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
    + rewrite XBox_app_distrib. simpl.
      assert (E1: (XBoxed_list x ++ unBox_formula A :: XBoxed_list x0) ++ [Box A0] =
      (XBoxed_list x ++ [unBox_formula A]) ++ XBoxed_list x0 ++ [Box A0]). repeat rewrite <- app_assoc.
      simpl. reflexivity. rewrite E1.
      assert (E2: (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x0) ++ [Box A0] =
      (XBoxed_list x ++ [unBox_formula A]) ++ A :: XBoxed_list x0 ++ [Box A0]). repeat rewrite <- app_assoc.
      simpl. reflexivity. rewrite E2.
      apply wkn_LI.
  * left. apply GLRRule_I.
    + assumption.
    + apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p.
      subst. apply univ_gen_ext_combine. assumption. apply univ_gen_ext_extra. assumption.
      assumption.
Qed.

(* Now we can prove that weakening is height-preserving admissible. *)

Theorem GL4ip_wkn_L : forall (k : nat) s
        (D0 : derrec GL4ip_rules (fun _ => False) s),
        k = (derrec_height D0) ->
          (forall sw A, ((@wkn_L A s sw) ->
          existsT2 (D1 : derrec GL4ip_rules (fun _ => False) sw),
          derrec_height D1 <= k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s :(list (MPropF) * MPropF))
  (D0 : derrec GL4ip_rules (fun _ : (list (MPropF) * MPropF) => False) s),
x = derrec_height D0 ->
(forall sw A,
wkn_L A s sw ->
(existsT2
  D1 : derrec GL4ip_rules
         (fun _ : (list (MPropF) * MPropF) => False) sw,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.

assert (DersNil: dersrec (GL4ip_rules) (fun _ : (list (MPropF) * MPropF) => False) []). apply dersrec_nil.

(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- intros hei sw A wkn. inversion f.
(* D0 ends with an application of rule *)
- intros hei sw A wkn. inversion wkn. inversion g.
  (* IdP *)
  * inversion H1. rewrite <- H in H5. inversion H5. apply app2_find_hole in H7. destruct H7.
    destruct s.
    + destruct s.
      { destruct p. inversion e0. subst. pose (IdPRule_I P (Γ2 ++ [A]) Γ3). apply IdP in i. rewrite <- app_assoc in i.
        simpl in i. pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
        (ps:=[]) (Γ2 ++ A :: # P :: Γ3, # P) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { destruct p. destruct x.
        - rewrite app_nil_l in e0. inversion e0. subst.
          pose (IdPRule_I P ((Γ2 ++ []) ++ [A]) Γ3). apply IdP in i. rewrite <- app_assoc in i. simpl in i.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
          (ps:=[]) ((Γ2 ++ []) ++ A :: # P :: Γ3, # P) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity.
        - inversion e0. subst.
          pose (IdPRule_I P Γ2 (x ++ A :: Γ1)). apply IdP in i.
          assert (E0 : Γ2 ++ # P :: x ++ A :: Γ1 = (Γ2 ++ # P :: x) ++ A :: Γ1). rewrite <- app_assoc. reflexivity.
          rewrite E0 in i.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
          (ps:=[]) ((Γ2 ++ # P :: x) ++ A :: Γ1, # P) i DersNil).
          exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity. }
    + destruct p. subst. pose (IdPRule_I P (Γ0 ++ A :: x) Γ3). apply IdP in i. rewrite <- app_assoc in i. simpl in i.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
      (ps:=[]) (Γ0 ++ A :: x ++ # P :: Γ3, # P) i DersNil).
      exists d0. simpl. repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
  (* BotL *)
  * inversion H1. rewrite <- H in H5. inversion H5.
    apply app2_find_hole in H7. destruct H7. destruct s.
    + destruct s.
      { destruct p. inversion e0. subst.
        pose (BotLRule_I (Γ2 ++ [A]) Γ3 A0). apply BotL in b. rewrite <- app_assoc in b. simpl in b.
        pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
        (ps:=[]) (Γ2 ++ A :: Bot :: Γ3, A0) b DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { destruct p. destruct x.
        - rewrite app_nil_l in e0. inversion e0. subst.
          pose (BotLRule_I ((Γ2 ++ []) ++ [A]) Γ3 A0). apply BotL in b. rewrite <- app_assoc in b. simpl in b.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
          (ps:=[]) ((Γ2 ++ []) ++ A :: Bot :: Γ3, A0) b DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity.
        - inversion e0. subst.
          pose (BotLRule_I Γ2 (x ++ A :: Γ1) A0). apply BotL in b.
          assert (E0: Γ2 ++ Bot :: x ++ A :: Γ1 = (Γ2 ++ Bot :: x) ++ A :: Γ1). rewrite <- app_assoc. reflexivity.
          rewrite E0 in b.
          pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
          (ps:=[]) ((Γ2 ++ Bot :: x) ++ A :: Γ1, A0) b DersNil).
          exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity. }
    + destruct p. subst. pose (BotLRule_I (Γ0 ++ A :: x) Γ3 A0). apply BotL in b.
      assert (E0 : (Γ0 ++ A :: x) ++ Bot :: Γ3 = Γ0 ++ A :: x ++ Bot :: Γ3).
      rewrite <- app_assoc. reflexivity. rewrite E0 in b.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
      (ps:=[]) (Γ0 ++ A :: x ++ Bot :: Γ3, A0) b DersNil). exists d0. simpl.
      repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
  (* AndR *)
  * inversion H1. subst. inversion H5. subst. pose (AndR_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. inversion d. remember[(Γ0 ++ Γ1, A1); (Γ0 ++ Γ1, B)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. remember [(Γ0 ++ Γ1, B)] as ps''. destruct d0.
    inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ0 ++ Γ1, A1) d E1 x A w0).
    destruct s.
    assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E3: derrec_height d0 = derrec_height d0). auto.
    pose (IH (derrec_height d0) E2 (Γ0 ++ Γ1, B) d0 E3 x0 A w).
    destruct s.
    pose (dlCons x2 d1). pose (dlCons x1 d2). apply AndR in a.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, And A1 B) a).
    pose (d4 d3). exists d5.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
    reflexivity.
  (* AndL *)
  * inversion H1. subst. inversion H5. subst. pose (AndL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. remember [(Γ2 ++ A1 :: B :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (derrec_height d)). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ A1 :: B :: Γ3, A0) d E1 x A w).
    destruct s.
    pose (dlCons x0 d0). apply AndL in a.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0) a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
    reflexivity.
  (* OrR1 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR1_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. remember[(Γ0 ++ Γ1, A1)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (derrec_height d)). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ0 ++ Γ1, A1) d E1 x A w).
    destruct s.
    pose (dlCons x0 d0). apply OrR1 in o.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Or A1 B) o).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
    reflexivity.
  (* OrR2 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR2_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. remember[(Γ0 ++ Γ1, B)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (derrec_height d)). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ0 ++ Γ1, B) d E1 x A w).
    destruct s.
    pose (dlCons x0 d0). apply OrR2 in o.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Or A1 B) o).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
    reflexivity.
  (* OrL *)
  * inversion H1. subst. inversion H5. subst. pose (OrL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. inversion d. remember [(Γ2 ++ A1 :: Γ3, A0); (Γ2 ++ B :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. remember [(Γ2 ++ B :: Γ3, A0)] as ps''. destruct d0.
    inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E(Γ2 ++ A1 :: Γ3, A0) d E1 x A w0).
    destruct s.
    assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E3: derrec_height d0 = derrec_height d0). auto.
    pose (IH (derrec_height d0) E2(Γ2 ++ B :: Γ3, A0) d0 E3 x0 A w).
    destruct s.
    pose (dlCons x2 d1). pose (dlCons x1 d2). apply OrL in o.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, A0) o).
    pose (d4 d3). exists d5.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
    reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. pose (ImpR_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember[(Γ2 ++ A1 :: Γ3, B)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ A1 :: Γ3, B) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply ImpR in i.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Imp A1 B) i).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.  reflexivity.
  (* AtomImpL1 *)
  * inversion H1. subst. inversion H5. subst. pose (AtomImpL1_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ # P :: Γ3 ++ A1 :: Γ4, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ # P :: Γ3 ++ A1 :: Γ4, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply AtomImpL1 in a.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia. reflexivity.
  (* AtomImpL2 *)
  * inversion H1. subst. inversion H5. subst. pose (AtomImpL2_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ A1 :: Γ3 ++ # P :: Γ4, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ A1 :: Γ3 ++ # P :: Γ4, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply AtomImpL2 in a.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia. reflexivity.
  (* AndImpL *)
  * inversion H1. subst. inversion H5. subst. pose (AndImpL_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ Imp A1 (Imp B C) :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ Imp A1 (Imp B C) :: Γ3, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply AndImpL in a.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia. reflexivity.
  (* OrImpL *)
  * inversion H1. subst. inversion H5. subst. pose (OrImpL_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ Imp A1 C :: Γ3 ++ Imp B C :: Γ4, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ Imp A1 C :: Γ3 ++ Imp B C :: Γ4, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply OrImpL in o.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  o).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia. reflexivity.
  (* ImpImpL *)
  * inversion H1. subst. inversion H5. subst. pose (ImpImpL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. inversion d. remember [(Γ2 ++ Imp B C :: Γ3, Imp A1 B); (Γ2 ++ C :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. remember [(Γ2 ++ C :: Γ3, A0)] as ps''. destruct d0.
    inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ Imp B C :: Γ3, Imp A1 B) d E1 x A w0).
    destruct s.
    assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E3: derrec_height d0 = derrec_height d0). auto.
    pose (IH (derrec_height d0) E2 (Γ2 ++ C :: Γ3, A0) d0 E3 x0 A w).
    destruct s.
    pose (dlCons x2 d1). pose (dlCons x1 d2). apply ImpImpL in i.
    pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, A0) i).
    pose (d4 d3). exists d5.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
    reflexivity.
  (* BoxImpL *)
  * inversion X. subst. inversion H5. subst. pose (BoxImpL_app_wkn_L wkn X). repeat destruct s.
    repeat destruct p. destruct s.
    + remember [(XBoxed_list BΓ ++ [Box A1], A1); (Γ2 ++ B :: Γ3, A0)] as ps'. destruct d.
       inversion Heqps'. inversion Heqps'. subst. remember [(Γ2 ++ B :: Γ3, A0)] as ps''. destruct d0.
       inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
       rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
       assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
       assert (E3: derrec_height d0 = derrec_height d0). auto.
       pose (IH (derrec_height d0) E2 (Γ2 ++ B :: Γ3, A0) d0 E3 x A w).
       destruct s.
       pose (dlCons x0 d1). pose (dlCons d d2). apply BoxImpL in b.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
       (ps:=[(XBoxed_list BΓ ++ [Box A1], A1) ;x]) (Γ0 ++ A :: Γ1, A0) b).
       pose (d4 d3). exists d5.
       simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
       reflexivity.
    + repeat destruct s. repeat destruct p.
       remember [(XBoxed_list BΓ ++ [Box A1], A1); (Γ2 ++ B :: Γ3, A0)] as ps'. destruct d.
       inversion Heqps'. inversion Heqps'. subst. remember [(Γ2 ++ B :: Γ3, A0)] as ps''. destruct d0.
       inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
       rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Max.max_0_r in IH.
       assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
       assert (E1: derrec_height d = derrec_height d). auto.
       pose (IH (derrec_height d) E (XBoxed_list BΓ ++ [Box A1], A1) d E1 x0 (unBox_formula A) w1).
       destruct s.
       assert (E': derrec_height x2 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
       assert (E1': derrec_height x2 = derrec_height x2). auto.
       pose (IH (derrec_height x2) E' x0 x2 E1' x1 A w0). destruct s.
       assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
       assert (E3: derrec_height d0 = derrec_height d0). auto.
       pose (IH (derrec_height d0) E2 (Γ2 ++ B :: Γ3, A0) d0 E3 x A w).
       destruct s.
       pose (dlCons x4 d1). pose (dlCons x3 d2). apply BoxImpL in b.
       pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
       (ps:=[x1;x]) (Γ0 ++ A :: Γ1, A0) b).
       pose (d4 d3). exists d5.
       simpl. repeat rewrite dersrec_height_nil. repeat rewrite Max.max_0_r. lia.
       reflexivity.
  (* GLR *)
  * inversion X. rewrite <- H4 in X. subst. pose (GLR_app_wkn_L wkn X). destruct s.
    { apply GLR in g0. subst. pose (derI (rules:=GL4ip_rules)
      (prems:=fun _ : (list (MPropF) * MPropF) => False) (ps:=[(XBoxed_list BΓ ++ [Box A1], A1)])
      (Γ0 ++ A :: Γ1, A0) g0). subst. pose (d0 d). exists d1. simpl. reflexivity. }
    { repeat destruct s. repeat destruct p. apply GLR in g0.
      remember [(XBoxed_list BΓ ++ [Box A1], A1)] as ps'. destruct d. inversion Heqps'. subst.
      inversion Heqps'. subst. simpl. simpl in IH.
      assert (E1: derrec_height d < S (Init.Nat.max (derrec_height d) (dersrec_height d0))).
      rewrite dersrec_height_nil. rewrite Max.max_0_r. apply Lt.le_lt_n_Sm. left. reflexivity.
      assert (E2: derrec_height d = derrec_height d). auto.
      pose (IH (derrec_height d) E1 ((XBoxed_list BΓ ++ [Box A1], A1)) d E2 x (unBox_formula A) w0).
      destruct s.
      assert (E3: derrec_height x1 < S (Init.Nat.max (derrec_height d) (dersrec_height d0))).
      rewrite dersrec_height_nil. rewrite Max.max_0_r. apply Lt.le_lt_n_Sm. assumption. reflexivity.
      assert (E4: derrec_height x1 = derrec_height x1). auto.
      pose (IH (derrec_height x1) E3 x x1 E4 x0 A w). destruct s.
      pose (derI (rules:=GL4ip_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
      (ps:=[x0]) (Γ0 ++ A :: Γ1, A0) g0). subst. simpl.
      pose (dlCons x2 d0). pose (d1 d2). exists d3. simpl. rewrite dersrec_height_nil.
      repeat rewrite Max.max_0_r. apply Le.le_n_S. lia. reflexivity. }
Qed.

Theorem GL4ip_adm_wkn_L :  forall s, (derrec GL4ip_rules (fun _ => False) s) ->
          (forall sw A, (@wkn_L A s sw) ->
           (derrec GL4ip_rules (fun _ => False) sw)).
Proof.
intros.
assert (J0: derrec_height X = derrec_height X). auto.
pose (GL4ip_wkn_L X J0 H). destruct s0. auto.
Qed.


Theorem GL4ip_list_wkn_L : forall (k : nat) Γ0 Γ1 A
        (D0 : derrec GL4ip_rules (fun _ => False) (Γ0 ++ Γ1, A)),
        k = (derrec_height D0) ->
          (forall l, existsT2 (D1 : derrec GL4ip_rules (fun _ => False) (Γ0 ++ l ++ Γ1,A)),
          derrec_height D1 <= k).
Proof.
intros. induction l.
- simpl. exists D0. lia.
- simpl. destruct IHl.
  assert (E: derrec_height x = derrec_height x). reflexivity.
  assert (H0: wkn_L a (Γ0 ++ l ++ Γ1, A) (Γ0 ++ a :: l ++ Γ1, A)). apply wkn_LI.
  pose (@GL4ip_wkn_L (derrec_height x) (Γ0 ++ l ++ Γ1, A) x E (Γ0 ++ a :: l ++ Γ1, A) a H0).
  destruct s. exists x0. lia.
Qed.

Theorem GL4ip_XBoxed_list_wkn_L : forall (k : nat) Γ1 Γ0 Γ2 A
        (D0 : derrec GL4ip_rules (fun _ => False) (Γ0 ++ Γ1 ++ Γ2,A)),
        k = (derrec_height D0) ->
          (existsT2 (D1 : derrec GL4ip_rules (fun _ => False) (Γ0 ++ (XBoxed_list Γ1) ++ Γ2,A)),
           derrec_height D1 <= k).
Proof.
induction Γ1.
- intros. simpl. simpl in D0. exists D0. rewrite H. left.
- intros. simpl. assert (Γ0 ++ (a :: Γ1) ++ Γ2 = (Γ0 ++ [a]) ++ Γ1 ++ Γ2). rewrite <- app_assoc. reflexivity.
  pose (@IHΓ1 (Γ0 ++ [a]) Γ2 A). repeat rewrite <- H0 in s.
  pose (s D0 H). destruct s0. clear s.
  assert (wkn_L (unBox_formula a) ((Γ0 ++ [a]) ++ XBoxed_list Γ1 ++ Γ2, A) (Γ0 ++ unBox_formula a :: a :: XBoxed_list Γ1 ++ Γ2, A)).
  assert ((Γ0 ++ [a]) ++ XBoxed_list Γ1 ++ Γ2 = Γ0 ++ a :: XBoxed_list Γ1 ++ Γ2). rewrite <- app_assoc. reflexivity. rewrite H1.
  apply wkn_LI.
  assert (derrec_height x = derrec_height x). reflexivity.
  pose (GL4ip_wkn_L x H2 H1). destruct s. exists x0. lia.
Qed.
