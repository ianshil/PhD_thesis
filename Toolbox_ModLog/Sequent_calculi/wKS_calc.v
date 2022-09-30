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
Require Import K_Syntax.



Declare Scope My_scope.
Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

(* In this file we define the calculus wKS based on multisets for the propositonal modal logic
   K. *)

Definition is_boxedT (A : MPropF) : Type :=
                  exists (B : MPropF), A = Box B.

Definition is_Boxed_list (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) -> (exists (B : MPropF), A = Box B).



(* With these properties we can define restrictions of univ_gen_ext on
   formulae. *)

Definition nobox_gen_ext := univ_gen_ext (fun x => (is_boxedT x) -> False).

(* A lemmas about nobox_gen_ext. *)

Lemma nobox_gen_ext_injective : forall (l0 l1 l : list (MPropF)), (is_Boxed_list l0) -> (is_Boxed_list l1) ->
                                (nobox_gen_ext l0 l) -> (nobox_gen_ext l1 l) -> l1 = l0.
Proof.
intros l0 l1 l Hl0 Hl1 gen. generalize dependent l1.
induction gen.
- intros. inversion X. reflexivity.
- intros. inversion X.
  * subst. assert (l0 = l). apply IHgen. intro. intros. apply Hl0. apply in_cons. assumption.
    intro. intros. apply Hl1. apply in_cons. assumption. assumption. rewrite H. reflexivity.
  * subst. exfalso. apply H1. apply Hl0. apply in_eq.
- intros. apply IHgen. intro. intros. apply Hl0. assumption.
  intro. intros. apply Hl1. assumption. inversion X.
  subst. exfalso. apply p. apply Hl1. apply in_eq. subst. assumption.
Qed.

(* The next definitions help to define the combination of a list of boxed
   formulae and the unboxing of all the formulae in that list. *)

Definition unBox_formula (A : MPropF) : MPropF :=
  match A with
              | # P => # P
              | Bot => Bot
              | A --> B => A --> B
              | Box A => A
              end
.

Fixpoint unboxed_list (Γ : list (MPropF)) : list (MPropF):=
  match Γ with
  | [ ] => [ ]
  | h :: t => (unBox_formula h :: unboxed_list t)
  end
.

Fixpoint top_boxes (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Box A => (Box A) :: top_boxes t
                | _ => top_boxes t
              end
end.

(* Now that we have defined these, we can prove some properties about them. *)

Lemma unbox_app_distrib :
  forall (l1 l2: list (MPropF)), unboxed_list (l1 ++ l2) = (unboxed_list l1) ++ (unboxed_list l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l with (l:=l2). simpl. reflexivity.
- intro l2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma subl_of_boxl_is_boxl {V : Set}:
  forall (l1 l2: list (MPropF)), (incl l1 l2) -> (is_Boxed_list l2) -> (is_Boxed_list l1).
Proof.
intros. unfold is_Boxed_list. intros. apply H in H1. apply H0 in H1.
destruct H1. exists x. assumption.
Qed.

Lemma tl_of_boxl_is_boxl {V : Set}:
  forall (h : MPropF) (t l : list (MPropF)) (H: l = h :: t),
         (is_Boxed_list l) -> (is_Boxed_list t).
Proof.
intros. unfold is_Boxed_list. intros. assert (Hyp: In A l).
rewrite H. simpl. right. apply H1. apply H0 in Hyp. destruct Hyp.
exists x. assumption.
Qed.

Lemma is_box_is_in_boxed_list : forall l (A : MPropF), In A l -> is_Boxed_list l -> (exists B, Box B = A).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  + subst. unfold is_Boxed_list in H0. pose (H0 A).
    apply e in H. destruct H. exists x. symmetry. assumption.
  + apply IHl. assumption. unfold is_Boxed_list. intros. unfold is_Boxed_list in H0.
    pose (H0 A0). apply e. apply in_cons. assumption.
Qed.

Lemma top_boxes_distr_app : forall (l1 l2 : list (MPropF)),
      top_boxes (l1 ++ l2) = (top_boxes l1) ++ (top_boxes l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l. simpl. reflexivity.
- intro l2. simpl. destruct a ; try apply IHl1.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma box_in_top_boxes : forall l1 l2 A, existsT2 l3 l4, top_boxes (l1 ++ Box A :: l2) = l3 ++ Box A :: l4.
Proof.
intros. exists (top_boxes l1). exists (top_boxes l2). rewrite top_boxes_distr_app. auto.
Qed.

Lemma is_Boxed_list_top_boxes : forall l, is_Boxed_list (top_boxes l).
Proof.
intros. induction l.
- simpl. intro. intros. inversion H.
- intro. destruct a.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. destruct H.
    * exists a. auto.
    * apply IHl. assumption.
Qed.

Lemma nobox_gen_ext_top_boxes : forall l, nobox_gen_ext (top_boxes l) l.
Proof.
induction l.
- simpl. apply univ_gen_ext_refl.
- destruct a.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_cons. assumption.
Qed.


(* We use a macro for sequents *)

Definition Seq := (prod (list MPropF) (list MPropF)).


(* ---------------------------------------------------------------------------------------------------------------------------------- *)

(* Finally, we can define the rules which constitute our calculus. We gather
   it in caclulus in a definition appearing later. *)

Inductive IdPRule : rlsT Seq :=
  | IdPRule_I : forall (P : V) (Γ0 Γ1 Δ0 Δ1 : list (MPropF)),
          IdPRule [] (Γ0 ++ # P :: Γ1 , Δ0 ++ # P :: Δ1)
.

Inductive BotLRule : rlsT Seq :=
  | BotLRule_I : forall Γ0 Γ1 Δ,
          BotLRule [] (Γ0 ++ Bot :: Γ1 , Δ)
.

Inductive ImpRRule : rlsT Seq :=
  | ImpRRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpRRule [(Γ0 ++ A :: Γ1 , Δ0 ++ B :: Δ1)]
                    (Γ0 ++ Γ1 , Δ0 ++ (A --> B) :: Δ1)
.

Inductive ImpLRule : rlsT Seq :=
  | ImpLRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpLRule [(Γ0 ++ Γ1 , Δ0 ++ A :: Δ1) ;
                     (Γ0 ++ B :: Γ1 , Δ0 ++ Δ1)]
                    (Γ0 ++ (A --> B) :: Γ1 , Δ0 ++ Δ1)
.

Inductive wKRRule : rlsT Seq :=
  | wKRRule_I : forall A BΓ Γ0 Δ0 Δ1,
          (is_Boxed_list BΓ) -> (* have MS of boxed formulae prem L*)
          (nobox_gen_ext BΓ Γ0) -> (* extend BΓ in Γ0, the L of the ccl *)
         wKRRule [(unboxed_list BΓ , [A])] (Γ0 , Δ0 ++ Box A :: Δ1)
.

(* At last we can define our calculus wKS. *)

Inductive wKS_rules : rlsT Seq :=
  | IdP : forall ps c, IdPRule ps c -> wKS_rules ps c
  | BotL : forall ps c, BotLRule ps c -> wKS_rules ps c
  | ImpR : forall ps c, ImpRRule ps c -> wKS_rules ps c
  | ImpL : forall ps c, ImpLRule ps c -> wKS_rules ps c
  | wKR : forall ps c, wKRRule ps c -> wKS_rules ps c
.

(* We can show that all identities are provable in wKS. *)

Lemma Id_all_form : forall (A : MPropF) l0 l1 l2 l3,
          derrec wKS_rules (fun _ => False) (l0 ++ A :: l1, l2 ++ A :: l3).
Proof.
assert (DersNilF: dersrec wKS_rules  (fun _ : rel (list (MPropF)) => False) []).
apply dersrec_nil.

induction A.
- intros. assert (IdPRule [] (l0 ++ # v :: l1, l2 ++ # v :: l3)). apply IdPRule_I. apply IdP in H.
  pose (derI (rules:=wKS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[])
  (l0 ++ # v :: l1, l2 ++ # v :: l3) H DersNilF). assumption.
- intros. assert (BotLRule [] (l0 ++ Bot :: l1, l2 ++ Bot :: l3)). apply BotLRule_I. apply BotL in H.
  pose (derI (rules:=wKS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[])
  (l0 ++ Bot :: l1, l2 ++ Bot :: l3) H DersNilF). assumption.
- intros. assert (ImpRRule [(l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3)] (l0 ++ A1 --> A2 :: l1, l2 ++ A1 --> A2 :: l3)).
  apply ImpRRule_I. apply ImpR in H.
  assert (ImpLRule [((l0 ++ [A1]) ++ l1, l2 ++ A1 :: A2 :: l3); ((l0 ++ [A1]) ++ A2 :: l1, l2 ++ A2 :: l3)] ((l0 ++ [A1]) ++ A1 --> A2 :: l1, l2 ++ A2 :: l3)).
  apply ImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0. apply ImpL in H0.
  pose (IHA1 l0 l1 l2 (A2 :: l3)). pose (IHA2 (l0 ++ [A1]) l1 l2 l3). repeat rewrite <- app_assoc in d0. simpl in d0.
  pose (dlCons d0 DersNilF). pose (dlCons d d1).
  pose (derI (rules:=wKS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(l0 ++ A1 :: l1, l2 ++ A1 :: A2 :: l3); (l0 ++ A1 :: A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3) H0 d2). pose (dlCons d3 DersNilF).
  pose (derI (rules:=wKS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(l0 ++ A1 :: A1 --> A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 --> A2 :: l1, l2 ++ A1 --> A2 :: l3) H d4). assumption.
- intros. assert (wKRRule [(unboxed_list (top_boxes (l0 ++ Box A :: l1)), [A])] (l0 ++ Box A :: l1, l2 ++ Box A :: l3)).
  apply wKRRule_I. apply is_Boxed_list_top_boxes. rewrite top_boxes_distr_app. simpl. apply univ_gen_ext_combine.
  apply nobox_gen_ext_top_boxes. apply univ_gen_ext_cons. apply nobox_gen_ext_top_boxes.
  rewrite top_boxes_distr_app in X. simpl in X. rewrite unbox_app_distrib in X. simpl in X.
  repeat rewrite <- app_assoc in X. simpl in X.
  pose (IHA (unboxed_list (top_boxes l0)) (unboxed_list (top_boxes l1)) [] []).
  simpl in d. pose (dlCons d DersNilF). apply wKR in X.
  pose (derI (rules:=wKS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(unboxed_list (top_boxes l0) ++ A :: unboxed_list (top_boxes l1), [A])])
  (l0 ++ Box A :: l1, l2 ++ Box A :: l3) X d0). assumption.
Qed.




Definition wKS_prv s := derrec wKS_rules (fun _ => False) s.
Definition wKS_drv s := derrec wKS_rules (fun _ => True) s.


Section Subformulas.

Require Import Ensembles.

Fixpoint subform (A : MPropF) : Ensemble (MPropF) :=
match A with
 | # P => Singleton _ (# P)
 | Bot => Singleton _ (Bot)
 | Imp B C => Union _ (Singleton _ (Imp B C)) (Union _ (subform B) (subform C))
 | Box B =>  Union _ (Singleton _ (Box B)) (subform B)
end.

End Subformulas.

