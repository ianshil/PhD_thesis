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
Require Import GLS_additive_cut.
Require Import Lia.

Inductive CutRule : rlsT Seq :=
  | CutRule_I : forall A Γ0 Γ1 Δ0 Δ1,
          CutRule [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1) ; (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]
                    (Γ0 ++ Γ1, Δ0 ++ Δ1)
.

Inductive GLS_cut_rules : rlsT  Seq :=
  | GLS_woc : forall ps c, GLS_rules ps c -> GLS_cut_rules ps c
  | iGLS_cut : forall ps c, CutRule ps c -> GLS_cut_rules ps c
.

Definition GLS_cut_prv s := derrec GLS_cut_rules (fun _ => False) s.
Definition GLS_cut_drv s := derrec GLS_cut_rules (fun _ => True) s.

Theorem GLS_cut_elimination : forall s, (GLS_cut_prv s) -> (GLS_prv s).
Proof.
intros s D.
apply derrec_all_rect with
(Q:= fun x => (GLS_prv x))
in D ; auto.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * subst. apply derI with (ps:=ps) ; auto. apply dersrec_forall. intros. apply ForallTD_forall with (x:=ps) (x0:=c) in IH ; auto.
  * subst. inversion H. subst. apply GLS_cut_adm with (A:=A).
    apply ForallTD_forall with (x:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]) (x0:=(Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) in IH ; auto.
    apply InT_eq.
    apply ForallTD_forall with (x:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]) (x0:=(Γ0 ++ A :: Γ1, Δ0 ++ Δ1)) in IH ; auto.
    apply InT_cons ; apply InT_eq.
Defined.