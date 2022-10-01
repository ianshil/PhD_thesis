Require Import GLS_PSGLS_calcs.
Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.
Require Import univ_gen_ext.
Require Import GLS_PSGLS_list_lems.
Require Import dd_fc.
Require Import PeanoNat.
Require Import strong_inductionT.
Require Import PSGLS_termination_measure.
Require Import PSGLS_termination.
Require Import GLS_exch.
Require Import GLS_ctr.
Require Import GLS_wkn.
Require Import GLS_PSGLS_remove_list.
Require Import GLS_PSGLS_dec.
Require Import GLS_inv_ImpR_ImpL.
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

Theorem PSGLS_imp_GLS : forall s (PSder: derrec PSGLS_rules (fun _ => False) s), (derrec GLS_rules (fun _ => False) s).
Proof.
intros s PSder. apply derrec_all_rect with
(Q:= fun x => (derrec GLS_rules (fun _ => False) x))
in PSder.
- exact PSder.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * inversion H. subst. apply derI with (ps:=[]). apply IdP. assumption.
    apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  * inversion H. subst. apply Id_all_form.
  * inversion H. subst. apply derI with (ps:=[]). apply BotL. assumption.
    apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]). apply ImpR.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H. subst. apply derI with (ps:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]). apply ImpL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons_inv in f. destruct f.
    apply ForallT_cons ; [assumption | apply ForallT_cons ; assumption].
  * inversion X. subst. apply derI with (ps:=[(XBoxed_list BΓ ++ [Box A], [A])]). apply GLR.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
Qed.

Theorem PSGLS_simulates_GLR : forall (prem concl : rel (list MPropF)), (GLRRule [prem] concl) ->
                  (derrec PSGLS_rules (fun x => (x = prem)) concl).
Proof.
intros prem concl RA. inversion RA. subst. induction X.
- apply derI with (ps:=[(XBoxed_list [] ++ [Box A], [A])]).
  + apply PSGLR.
    * intro. inversion H. apply list_eq_nil in H1. assumption.
    * intro. inversion H. apply list_eq_nil in H1. assumption.
    * intro. inversion H. apply list_eq_nil in H1. assumption.
    * assumption.
  + apply dlCons. apply dpI. auto. apply dlNil.
- pose (dec_init_rules (x :: le, Δ0 ++ Box A :: Δ1)). destruct s.
  + repeat destruct s.
    * apply derI with (ps:=[]). apply PSIdP. assumption. apply dlNil.
    * apply derI with (ps:=[]). apply PSIdB. assumption. apply dlNil.
    * apply derI with (ps:=[]). apply PSBotL. assumption. apply dlNil.
  + apply derI with (ps:=[(XBoxed_list (x :: l) ++ [Box A], [A])]).
    * apply PSGLR ; try auto.
    * apply dlCons. apply dpI. auto. apply dlNil.
- pose (dec_init_rules (x :: le, Δ0 ++ Box A :: Δ1)). destruct s.
  + repeat destruct s.
    * apply derI with (ps:=[]). apply PSIdP. assumption. apply dlNil.
    * apply derI with (ps:=[]). apply PSIdB. assumption. apply dlNil.
    * apply derI with (ps:=[]). apply PSBotL. assumption. apply dlNil.
  + destruct x.
    * apply derI with (ps:=[(XBoxed_list l ++ [Box A], [A])]).
      { apply PSGLR ; try auto. }
      { apply dlCons. apply dpI. auto. apply dlNil. }
    * apply derI with (ps:=[(XBoxed_list l ++ [Box A], [A])]).
      { apply PSGLR ; try auto. }
      { apply dlCons. apply dpI. auto. apply dlNil. }
    * apply derI with (ps:=[(XBoxed_list l ++ [Box A], [A])]).
      { apply PSGLR ; try auto. }
      { apply dlCons. apply dpI. auto. apply dlNil. }
    * apply derI with (ps:=[(XBoxed_list l ++ [Box A], [A])]).
      { apply PSGLR ; try auto. }
      { apply dlCons. apply dpI. auto. apply dlNil. }
Qed.

Lemma derrec_composition: forall X (rules : list X -> X -> Type) (prems0 prems1 : X -> Prop) (concl : X),
     (forall leaf : X, prems0 leaf -> (derrec rules prems1 leaf)) ->
     (derrec rules prems0 concl) ->
     (derrec rules prems1 concl).
Proof.
intros X rules prems0 prems1 concl HypLeaves der. apply derrec_all_rect with
(Q:= fun x => (derrec rules prems1 x))
in der.
- exact der.
- intros. apply HypLeaves. assumption.
- intros ps concl0 RA ders IH. apply dersrec_all in IH. apply derI with (ps:=ps) ; assumption.
Qed.

Theorem derrec_leaves_thms : forall (s0 s1 : rel (list MPropF)),
        (derrec PSGLS_rules (fun x => (x = s0)) s1) ->
        (derrec PSGLS_rules (fun _ => False) s0) ->
        (derrec PSGLS_rules (fun _ => False) s1).
Proof.
intros s0 s1 leaves pfs.
pose (@derrec_composition (rel (list MPropF)) PSGLS_rules (fun x => (x = s0)) (fun _ => False)
s1). apply d.
- intros. inversion H. assumption.
- assumption.
Qed.

Theorem GLS_imp_PSGLS : forall s (der: derrec GLS_rules (fun _ => False) s), (derrec PSGLS_rules (fun _ => False) s).
Proof.
intros s der. apply derrec_all_rect with
(Q:= fun x => (derrec PSGLS_rules (fun _ => False) x))
in der.
- exact der.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * inversion H. subst. apply derI with (ps:=[]). apply PSIdP. assumption.
    apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  * inversion H. subst. apply derI with (ps:=[]). apply PSBotL. assumption.
    apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  * inversion H. subst. apply derI with (ps:=[(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]). apply PSImpR.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons ; assumption.
  * inversion H. subst. apply derI with (ps:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]). apply PSImpL.
    assumption. apply dersrec_all. apply dersrec_all in ders.
    apply ForallT_cons_inv in IH. destruct IH. apply ForallT_cons_inv in f. destruct f.
    apply ForallT_cons ; [assumption | apply ForallT_cons ; assumption].
  * inversion X. subst. pose (PSGLS_simulates_GLR X). apply ForallT_inv in IH.
    pose (derrec_leaves_thms d IH). assumption.
Qed.

Theorem PSGLS_dec_der : forall k s, (k = mhd s) ->
  (derrec PSGLS_rules (fun _ => False) s) + ((derrec PSGLS_rules (fun _ => False) s) -> False).
Proof.
assert (PSDersNilF: dersrec PSGLS_rules (fun _ : rel (list MPropF) => False) []).
apply dersrec_nil.
pose (strong_inductionT (fun (x:nat) => forall s, (x = mhd s) ->
  (derrec PSGLS_rules (fun _ => False) s) + ((derrec PSGLS_rules (fun _ => False) s) -> False))).
apply s. clear s.
intros n IH s mhds. pose (finite_premises_of_S s). destruct s0.
assert (forall prems, (InT prems x) -> ((dersrec PSGLS_rules (fun _ => False) prems) +
((dersrec PSGLS_rules (fun _ => False) prems) -> False))).
{ intros. pose (p prems). destruct p0. apply p0 in X. inversion X.
  - inversion H. subst. auto.
  - inversion H. subst. auto.
  - inversion H. subst. auto.
  - inversion H. subst.
    assert (J1: In (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]). apply in_eq.
    pose (RA_mhd_decreases X (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) J1).
    assert (J2: mhd (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) = mhd (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)). reflexivity.
    pose (IH _ l (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X0. subst. auto.
  - inversion H. subst.
    assert (J1: In (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]). apply in_eq.
    pose (RA_mhd_decreases X _ J1).
    assert (J2: In (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]). apply in_cons. apply in_eq.
    pose (RA_mhd_decreases X _ J2).
    assert (J3: mhd (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) = mhd (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)). reflexivity.
    pose (IH _ l _ J3).
    assert (J4: mhd (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) = mhd (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)). reflexivity.
    pose (IH _ l0 _ J4). destruct s ; destruct s0.
    * pose (dlCons d0 PSDersNilF). pose (dlCons d d1). auto.
    * right. intro. inversion X0. subst. inversion X2. subst. auto.
    * right. intro. inversion X0. subst. auto.
    * right. intro. inversion X0. subst. auto.
  - inversion X0. subst.
    assert (J1: In (XBoxed_list BΓ ++ [Box A], [A]) [(XBoxed_list BΓ ++ [Box A], [A])]). apply in_eq.
    pose (RA_mhd_decreases X _ J1).
    assert (J2: mhd (XBoxed_list BΓ ++ [Box A], [A]) = mhd (XBoxed_list BΓ ++ [Box A], [A])). reflexivity.
    pose (IH _ l _ J2). destruct s.
    * pose (dlCons d PSDersNilF). auto.
    * right. intro. inversion X2. subst. auto. }
assert ((existsT2 prems, (InT prems x) * (dersrec PSGLS_rules (fun _ => False) prems)) +
(forall prems, (InT prems x) -> ((dersrec PSGLS_rules (fun _ => False) prems) -> False))).
{ assert ((existsT2 prems, (InT prems x) * (dersrec PSGLS_rules (fun _ => False) prems)) +
  ((existsT2 prems, (InT prems x) * (dersrec PSGLS_rules (fun _ => False) prems)) -> False)).
  { pose (@forall_elem_list _ x (fun y =>
    dersrec PSGLS_rules (fun _ : rel (list MPropF) => False) y) X). destruct s0.
    - left. auto.
    - right. auto. }
  destruct X0.
  - destruct s0. destruct p0. left. exists x0. auto.
  - right. intros. firstorder. }
destruct X0.
- destruct s0. destruct p0. pose (p x0). destruct p0. apply p0 in i. left. apply derI with (ps:=x0) ; assumption.
- pose (dec_init_rules s). repeat destruct s0.
  * left. apply derI with (ps:=[]) ; [apply PSIdP ; assumption | assumption].
  * left. apply derI with (ps:=[]) ; [apply PSIdB ; assumption | assumption].
  * left. apply derI with (ps:=[]) ; [apply PSBotL ; assumption | assumption].
  * right. intro der. inversion der.
    + inversion H.
    + subst. inversion X0.
      { inversion H. subst. apply f0. auto. }
      { inversion H. subst. apply f0. auto. }
      { inversion H. subst. apply f0. auto. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
      { subst. pose (f ps). apply f1. pose (p ps). destruct p0. apply i. assumption.
        assumption. }
Qed.

Theorem GLS_dec_der : forall s,
  (derrec GLS_rules (fun _ => False) s) + ((derrec GLS_rules (fun _ => False) s) -> False).
Proof.
intro s.
assert (J1 : mhd s = mhd s). reflexivity.
pose (PSGLS_dec_der s J1). destruct s0.
- left ; apply PSGLS_imp_GLS ; assumption.
- right ; intro ; apply f ; apply GLS_imp_PSGLS ; assumption.
Qed.







