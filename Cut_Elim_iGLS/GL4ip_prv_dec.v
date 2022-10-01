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
Require Import GL4ip_wkn.
Require Import GL4ip_PSGL4ip_remove_list.
Require Import GL4ip_PSGL4ip_dec.
Require Import GL4ip_Id.
Require Import Lia.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Lemma forall_elem_list : forall {A : Type} (l : list A) (P : A -> Type),
    (forall a, (InT a l) -> ((P a) + ((P a) -> False))) ->
    (existsT2 a, (InT a l) * (P a)) + ((existsT2 a, (InT a l) * (P a)) -> False).
Proof.
induction l.
- intros. right. intros. destruct X0. destruct p. inversion i.
- intros. pose (X a). assert (InT a (a :: l)). apply InT_eq. apply s in X0. destruct X0.
  * left. exists a. split. apply InT_eq. assumption.
  * assert (forall a : A, InT a l -> P a + (P a -> False)).
    { intros. apply X. apply InT_cons. assumption. }
    pose (IHl P X0). destruct s0.
    + left. destruct s0. exists x. split. apply InT_cons. firstorder. firstorder.
    + right. intro. destruct X1. destruct p. inversion i. subst. firstorder. subst. firstorder.
Qed.

Theorem PSGL4ip_imp_GL4ip : forall s (PSder: derrec PSGL4ip_rules (fun _ => False) s), (derrec GL4ip_rules (fun _ => False) s).
Proof.
intros s PSder. apply derrec_all_rect with
(Q:= fun x => (derrec GL4ip_rules (fun _ => False) x))
in PSder.
- exact PSder.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * inversion H. subst. apply Id_all_form.
  * inversion H. subst. apply derI with (ps:=[]). apply BotL. assumption.
    apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ, A); (Γ, B)]). apply AndR.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ A :: B :: Γ1, C)]). apply AndL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ, A)]). apply OrR1.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ, B)]). apply OrR2.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)]). apply OrL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1, B)]). apply ImpR.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)]). apply AtomImpL1.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)]). apply AtomImpL2.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ A → B → C :: Γ1, D)]). apply AndImpL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)]). apply OrImpL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H1. subst. apply derI with (ps:=[(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)]). apply ImpImpL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion X. subst. apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)]). apply BoxImpL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion X. subst. apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A], A)]). apply GLR.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
Qed.

Theorem GL4ip_imp_PSGL4ip : forall s (der: derrec GL4ip_rules (fun _ => False) s), (derrec PSGL4ip_rules (fun _ => False) s).
Proof.
intros s der. apply derrec_all_rect with
(Q:= fun x => (derrec PSGL4ip_rules (fun _ => False) x))
in der.
- exact der.
- intros. inversion H.
- intros ps concl rule ders IH. destruct (dec_init_rules concl).
  + destruct s0. apply derI with (ps:=[]). apply PSId. auto.
     apply dersrec_nil. apply derI with (ps:=[]). apply PSBotL. auto.
     apply dersrec_nil.
  + inversion rule.
      * inversion H. subst. apply derI with (ps:=[]). apply PSId. apply IdRule_I.
        apply dersrec_all in ders. apply dersrec_all. subst. assumption.
      * inversion H. subst. apply derI with (ps:=[]). apply PSBotL. assumption.
        apply dersrec_all in ders. apply dersrec_all. subst. assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ, A); (Γ, B)]). apply PSAndR ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A :: B :: Γ1, C)]). apply PSAndL ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ, A)]). apply PSOrR1 ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ, B)]). apply PSOrR2 ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)]). apply PSOrL ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1, B)]). apply PSImpR ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)]). apply PSAtomImpL1 ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)]). apply PSAtomImpL2 ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A → B → C :: Γ1, D)]). apply PSAndImpL ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)]). apply PSOrImpL ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion H. subst. apply derI with (ps:=[(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)]). apply PSImpImpL ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion X. subst. apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)]). apply PSBoxImpL ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
      * inversion X. subst. apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A], A)]). apply PSGLR ; auto.
        apply dersrec_all. apply dersrec_all in ders.
        apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
Qed.

Theorem PSGL4ip_dec_prv : forall k s, (k = mhd s) ->
  (derrec PSGL4ip_rules (fun _ => False) s) + ((derrec PSGL4ip_rules (fun _ => False) s) -> False).
Proof.
assert (PSDersNilF: dersrec PSGL4ip_rules (fun _ : Seq => False) []).
apply dersrec_nil.
pose (strong_inductionT (fun (x:nat) => forall s, (x = mhd s) ->
  (derrec PSGL4ip_rules (fun _ => False) s) + ((derrec PSGL4ip_rules (fun _ => False) s) -> False))).
apply s. clear s.
intros n IH s mhds. pose (finite_premises_of_S s). destruct s0.
assert (forall prems, (InT prems x) -> ((dersrec PSGL4ip_rules (fun _ => False) prems) +
((dersrec PSGL4ip_rules (fun _ => False) prems) -> False))).
{ intros. pose (p prems). destruct p0. apply p0 in H. inversion H.
  - inversion H0. subst. auto.
  - inversion H0. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ, A) [(Γ, A); (Γ, B)]). apply in_eq.
    pose (RA_mhd_decreases H _ J1).
    assert (J2: In (Γ, B) [(Γ, A); (Γ, B)]). apply in_cons. apply in_eq.
    pose (RA_mhd_decreases H _ J2).
    assert (J3: mhd (Γ, A) = mhd (Γ, A)). reflexivity.
    pose (IH _ l _ J3).
    assert (J4: mhd (Γ, B) = mhd (Γ, B)). reflexivity.
    pose (IH _ l0 _ J4). destruct s ; destruct s0.
    * pose (dlCons d0 PSDersNilF). pose (dlCons d d1). auto.
    * right. intro. inversion X. subst. inversion X1. subst. auto.
    * right. intro. inversion X. subst. auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ A :: B :: Γ1, C) [(Γ0 ++ A :: B :: Γ1, C)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ0 ++ A :: B :: Γ1, C) J1).
    assert (J2: mhd (Γ0 ++ A :: B :: Γ1, C) = mhd (Γ0 ++ A :: B :: Γ1, C)). reflexivity.
    pose (IH _ l (Γ0 ++ A :: B :: Γ1, C) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ, A) [(Γ, A)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ, A) J1).
    assert (J2: mhd (Γ, A) = mhd (Γ, A)). reflexivity.
    pose (IH _ l (Γ, A) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ, B) [(Γ, B)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ, B) J1).
    assert (J2: mhd (Γ, B) = mhd (Γ, B)). reflexivity.
    pose (IH _ l (Γ, B) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ A :: Γ1, C) [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)]). apply in_eq.
    pose (RA_mhd_decreases H _ J1).
    assert (J2: In (Γ0 ++ B :: Γ1, C) [(Γ0 ++ A :: Γ1, C); (Γ0 ++ B :: Γ1, C)]). apply in_cons. apply in_eq.
    pose (RA_mhd_decreases H _ J2).
    assert (J3: mhd (Γ0 ++ A :: Γ1, C) = mhd (Γ0 ++ A :: Γ1, C)). reflexivity.
    pose (IH _ l _ J3).
    assert (J4: mhd (Γ0 ++ B :: Γ1, C) = mhd (Γ0 ++ B :: Γ1, C)). reflexivity.
    pose (IH _ l0 _ J4). destruct s ; destruct s0.
    * pose (dlCons d0 PSDersNilF). pose (dlCons d d1). auto.
    * right. intro. inversion X. subst. inversion X1. subst. auto.
    * right. intro. inversion X. subst. auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ A :: Γ1, B) [(Γ0 ++ A :: Γ1, B)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ0 ++ A :: Γ1, B) J1).
    assert (J2: mhd (Γ0 ++ A :: Γ1, B) = mhd (Γ0 ++ A :: Γ1, B)). reflexivity.
    pose (IH _ l (Γ0 ++ A :: Γ1, B) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) [(Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) J1).
    assert (J2: mhd (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) = mhd (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C)). reflexivity.
    pose (IH _ l (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) [(Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) J1).
    assert (J2: mhd (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) = mhd (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C)). reflexivity.
    pose (IH _ l (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ A → B → C :: Γ1, D) [(Γ0 ++ A → B → C :: Γ1, D)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ0 ++ A → B → C :: Γ1, D)J1).
    assert (J2: mhd (Γ0 ++ A → B → C :: Γ1, D) = mhd (Γ0 ++ A → B → C :: Γ1, D)). reflexivity.
    pose (IH _ l (Γ0 ++ A → B → C :: Γ1, D) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) [(Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)]). apply in_eq.
    pose (RA_mhd_decreases H (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)J1).
    assert (J2: mhd (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) = mhd (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D)). reflexivity.
    pose (IH _ l (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X. subst. auto.
  - inversion H2. subst.
    assert (J1: In (Γ0 ++ B → C :: Γ1, A → B) [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)]). apply in_eq.
    pose (RA_mhd_decreases H _ J1).
    assert (J2: In (Γ0 ++ C :: Γ1, D) [(Γ0 ++ B → C :: Γ1, A → B); (Γ0 ++ C :: Γ1, D)]). apply in_cons. apply in_eq.
    pose (RA_mhd_decreases H _ J2).
    assert (J3: mhd (Γ0 ++ B → C :: Γ1, A → B) = mhd (Γ0 ++ B → C :: Γ1, A → B)). reflexivity.
    pose (IH _ l _ J3).
    assert (J4: mhd (Γ0 ++ C :: Γ1, D) = mhd (Γ0 ++ C :: Γ1, D)). reflexivity.
    pose (IH _ l0 _ J4). destruct s ; destruct s0.
    * pose (dlCons d0 PSDersNilF). pose (dlCons d d1). auto.
    * right. intro. inversion X. subst. inversion X1. subst. auto.
    * right. intro. inversion X. subst. auto.
    * right. intro. inversion X. subst. auto.
  - inversion X. subst.
    assert (J1: In (XBoxed_list BΓ ++ [Box A], A) [(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)]). apply in_eq.
    pose (RA_mhd_decreases H _ J1).
    assert (J2: In (Γ0 ++ B :: Γ1, C) [(XBoxed_list BΓ ++ [Box A], A); (Γ0 ++ B :: Γ1, C)]). apply in_cons. apply in_eq.
    pose (RA_mhd_decreases H _ J2).
    assert (J3: mhd (XBoxed_list BΓ ++ [Box A], A) = mhd (XBoxed_list BΓ ++ [Box A], A)). reflexivity.
    pose (IH _ l _ J3).
    assert (J4: mhd (Γ0 ++ B :: Γ1, C) = mhd (Γ0 ++ B :: Γ1, C)). reflexivity.
    pose (IH _ l0 _ J4). destruct s ; destruct s0.
    * pose (dlCons d0 PSDersNilF). pose (dlCons d d1). auto.
    * right. intro. inversion X1. subst. inversion X3. subst. auto.
    * right. intro. inversion X1. subst. auto.
    * right. intro. inversion X1. subst. auto.
  - inversion X. subst.
    assert (J1: In (XBoxed_list BΓ ++ [Box A], A) [(XBoxed_list BΓ ++ [Box A], A)]). apply in_eq.
    pose (RA_mhd_decreases H _ J1).
    assert (J2: mhd (XBoxed_list BΓ ++ [Box A], A) = mhd (XBoxed_list BΓ ++ [Box A], A)). reflexivity.
    pose (IH _ l _ J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X1. subst. auto. }
assert ((existsT2 prems, (InT prems x) * (dersrec PSGL4ip_rules (fun _ => False) prems)) +
(forall prems, (InT prems x) -> ((dersrec PSGL4ip_rules (fun _ => False) prems) -> False))).
{ assert ((existsT2 prems, (InT prems x) * (dersrec PSGL4ip_rules (fun _ => False) prems)) +
  ((existsT2 prems, (InT prems x) * (dersrec PSGL4ip_rules (fun _ => False) prems)) -> False)).
  { pose (@forall_elem_list _ x (fun y =>
    dersrec PSGL4ip_rules (fun _ : Seq => False) y) X). destruct s0.
    - left. auto.
    - right. auto. }
  destruct X0.
  - destruct s0. destruct p0. left. exists x0. auto.
  - right. intros. firstorder. }
destruct X0.
- destruct s0. destruct p0. pose (p x0). destruct p0. apply p0 in i. left. apply derI with (ps:=x0) ; assumption.
- pose (dec_init_rules s). repeat destruct s0.
  * left. apply derI with (ps:=[]) ; [apply PSId ; assumption | assumption].
  * left. apply derI with (ps:=[]) ; [apply PSBotL ; assumption | assumption].
  * right. intro der. inversion der.
    + inversion H.
    + subst. inversion X0.
      { inversion H. subst. apply f0. auto. }
      { inversion H. subst. apply f0. auto. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
Qed.

Theorem GL4ip_dec_prv : forall s,
  (derrec GL4ip_rules (fun _ => False) s) + ((derrec GL4ip_rules (fun _ => False) s) -> False).
Proof.
intro s.
assert (J1 : mhd s = mhd s). reflexivity.
pose (PSGL4ip_dec_prv s J1). destruct s0.
- left ; apply PSGL4ip_imp_GL4ip ; assumption.
- right ; intro ; apply f ; apply GL4ip_imp_PSGL4ip ; assumption.
Qed.