Require Import GL4ip_PSGL4ip_calcs.
Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import dd_fc.
Require Import strong_inductionT.
Require Import GL4ip_additive_cut.
Require Import Lia.

Inductive CutRule : rlsT Seq :=
  | CutRule_I : forall A C Γ0 Γ1,
          CutRule [(pair (Γ0 ++ Γ1) A) ; (pair (Γ0 ++ A :: Γ1) C)]
                    (pair (Γ0 ++ Γ1) C)
.

Inductive GL4ip_cut_rules : rlsT  Seq :=
  | GL4ip_woc : forall ps c, GL4ip_rules ps c -> GL4ip_cut_rules ps c
  | GL4ip_cut : forall ps c, CutRule ps c -> GL4ip_cut_rules ps c
.

Definition GL4ip_cut_prv s := derrec GL4ip_cut_rules (fun _ => False) s.

Theorem GL4ip_cut_elimination : forall s, (GL4ip_cut_prv s) -> (GL4ip_prv s).
Proof.
intros s D.
apply derrec_all_rect with
(Q:= fun x => (derrec GL4ip_rules (fun _ => False) x))
in D ; auto.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * subst. apply derI with (ps:=ps) ; auto. apply dersrec_forall. intros. apply ForallTD_forall with (x:=ps) (x0:=c) in IH ; auto.
  * subst. inversion H. subst. apply GL4ip_cut_adm with (A:=A). split.
    apply ForallTD_forall with (x:=[(Γ0 ++ Γ1, A); (Γ0 ++ A :: Γ1, C)]) (x0:=(Γ0 ++ Γ1, A)) in IH ; auto.
    apply InT_eq.
    apply ForallTD_forall with (x:=[(Γ0 ++ Γ1, A); (Γ0 ++ A :: Γ1, C)]) (x0:=(Γ0 ++ A :: Γ1, C)) in IH ; auto.
    apply InT_cons ; apply InT_eq.
Defined.