Require Import K_Syntax.
Require Import wKS_calc.
Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.
Require Import univ_gen_ext.
Require Import wKS_list_lems.
Require Import dd_fc.
Require Import PeanoNat.
Require Import strong_inductionT.
Require Import wKS_termination_measure.
Require Import wKS_termination.
Require Import wKS_exch.
Require Import wKS_ctr.
Require Import wKS_wkn.
Require Import wKS_remove_list.
Require Import wKS_dec.
Require Import wKS_inv_ImpR_ImpL.
Require Import wKS_additive_cut.
Require Import Lia.

Inductive CutRule : rlsT Seq :=
  | CutRule_I : forall A Γ0 Γ1 Δ0 Δ1,
          CutRule [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1) ; (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]
                    (Γ0 ++ Γ1, Δ0 ++ Δ1)
.

Inductive wKS_cut_rules : rlsT  Seq :=
  | wKS_woc : forall ps c, wKS_rules ps c -> wKS_cut_rules ps c
  | wKS_cut : forall ps c, CutRule ps c -> wKS_cut_rules ps c
.

Definition wKS_cut_prv s := derrec wKS_cut_rules (fun _ => False) s.
Definition wKS_cut_drv s := derrec wKS_cut_rules (fun _ => True) s.

Theorem wKS_cut_elimination : forall s, (wKS_cut_prv s) -> (wKS_prv s).
Proof.
intros s D.
apply derrec_all_rect with
(Q:= fun x => (wKS_prv x))
in D ; auto.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * subst. apply derI with (ps:=ps) ; auto. apply dersrec_forall. intros. apply ForallTD_forall with (x:=ps) (x0:=c) in IH ; auto.
  * subst. inversion H. subst. apply wKS_cut_adm with (A:=A).
    apply ForallTD_forall with (x:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]) (x0:=(Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) in IH ; auto.
    apply InT_eq.
    apply ForallTD_forall with (x:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]) (x0:=(Γ0 ++ A :: Γ1, Δ0 ++ Δ1)) in IH ; auto.
    apply InT_cons ; apply InT_eq.
Defined.