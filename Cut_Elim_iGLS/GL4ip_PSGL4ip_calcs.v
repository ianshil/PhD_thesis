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



Declare Scope My_scope.
Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Global Parameter V : Set.

Parameter eq_dec_propvar : forall x y : V, {x = y}+{x <> y}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* In this file we define two calculi based on multisets for the propositonal intuitionistic modal logic
   iGL. The first one, called GL4ip, is the main calculus for iGL. The second one, named PSGL4ip,
   is essentially the calculus GL4ip with further restrictions on the application of the
   rules. In other words, the calculus PSGL4ip is a proof-search oriented version of GL4ip. *)

(* Definitions Language *)

(* First, let us define the propositional formulae we use here. *)

Inductive MPropF : Type :=
 | Var : V -> MPropF
 | Bot : MPropF
 | And : MPropF -> MPropF -> MPropF
 | Or : MPropF -> MPropF -> MPropF
 | Imp : MPropF -> MPropF -> MPropF
 | Box : MPropF -> MPropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Imp A B) (at level 16, right associativity) : My_scope.
Notation "A ∨ B" := (Or A B) (at level 16, right associativity) : My_scope.
Notation "A ∧ B" := (And A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.

Lemma eq_dec_form : forall x y : MPropF, {x = y}+{x <> y}.
Proof.
induction x.
- intros. destruct y.
  * pose (eq_dec_propvar v v0). destruct s. left ; subst ; reflexivity.
    right. intro. inversion H. apply n. assumption.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * left. reflexivity.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n.
    assumption.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n.
    assumption.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n.
    assumption.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx y). destruct s. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption.
Qed.

Fixpoint weight_form (A : MPropF) : nat :=
match A with
 | # P => 1
 | Bot => 1
 | And B C => 2 + (weight_form B) + (weight_form C)
 | Or B C => 1 + (weight_form B) + (weight_form C)
 | Imp B C => 1 + (weight_form B) + (weight_form C)
 | Box B => 1 + (weight_form B)
end.


(* Now, we can define properties of formulae. *)

Definition is_atomicT (A : MPropF) : Type :=
                  (existsT2 (P : V), A = # P) + (A = Bot).

Definition is_boxedT (A : MPropF) : Type :=
                  exists (B : MPropF), A = Box B.

Definition is_boxedT2 (A : MPropF) : Type :=
                  existsT2 (B : MPropF), A = Box B.

Definition is_primeT (A : MPropF) : Type :=
                  is_atomicT A + is_boxedT A.

(* We can define some types of lists formulae. For example, we can define
   lists of formulae which contain only propositional variables, or
   boxed formulae, or a combination of both. These are useful to define
   the rules. *)

Definition is_Atomic (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) -> ((exists (P : V), A = # P) \/ (A = ⊥)).

Definition is_Boxed_list (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) -> (exists (B : MPropF), A = Box B).

Definition is_Prime (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) ->
    (exists (B : MPropF), A = Box B) \/ (exists (P : V), A = # P) \/ (A = ⊥).

(* With these properties we can define restrictions of univ_gen_ext on
   formulae. *)

Definition atom_gen_ext := univ_gen_ext (fun x => (is_atomicT x)).

Definition nobox_gen_ext := univ_gen_ext (fun x => (is_boxedT x) -> False).

Definition prim_gen_ext := univ_gen_ext (fun x => (is_primeT x)).

(* Some lemmas about gen_ext. *)

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
              | ⊥ => ⊥
              | And A B => And A B
              | Or A B => Or A B
              | Imp A B => Imp A B
              | Box A => A
              end
.

Fixpoint XBoxed_list (Γ : list (MPropF)) : list (MPropF):=
  match Γ with
  | [ ] => [ ]
  | h :: t => (unBox_formula h :: h :: XBoxed_list t)
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

Lemma XBox_app_distrib :
  forall (l1 l2: list (MPropF)), XBoxed_list (l1 ++ l2) = (XBoxed_list l1) ++ (XBoxed_list l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l with (l:=l2). simpl. reflexivity.
- intro l2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma subl_of_boxl_is_boxl :
  forall (l1 l2: list (MPropF)), (incl l1 l2) -> (is_Boxed_list l2) -> (is_Boxed_list l1).
Proof.
intros. unfold is_Boxed_list. intros. apply H in H1. apply H0 in H1.
destruct H1. exists x. assumption.
Qed.

Lemma tl_of_boxl_is_boxl :
  forall (h : MPropF) (t l : list (MPropF)) (H: l = h :: t),
         (is_Boxed_list l) -> (is_Boxed_list t).
Proof.
intros. unfold is_Boxed_list. intros. assert (Hyp: In A l).
rewrite H. simpl. right. apply H1. apply H0 in Hyp. destruct Hyp.
exists x. assumption.
Qed.

Lemma list_preserv_XBoxed_list : forall (l : list (MPropF)), incl l (XBoxed_list l).
Proof.
induction l.
- simpl. unfold incl. intros. inversion H.
- simpl. unfold incl. intros. inversion H.
  * subst. apply in_cons. apply in_eq.
  * apply in_cons. apply in_cons. apply IHl. assumption.
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
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_cons. assumption.
Qed.

Definition Seq := (prod (list (MPropF)) (MPropF)).



(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later. *)

Inductive IdPRule : rlsT Seq :=
  | IdPRule_I : forall (P : V) (Γ0 Γ1 : list (MPropF)),
          IdPRule [] (pair (Γ0 ++ # P :: Γ1) (# P))
.

Inductive IdRule : rlsT Seq :=
  | IdRule_I : forall A Γ0 Γ1,
          IdRule [] (pair (Γ0 ++ A :: Γ1) A)
.

Inductive BotLRule : rlsT Seq :=
  | BotLRule_I : forall Γ0 Γ1 A,
          BotLRule [] (pair (Γ0 ++ (⊥) :: Γ1) A)
.

Inductive AndRRule : rlsT Seq :=
  | AndRRule_I : forall A B Γ,
          AndRRule [(pair Γ A) ; (pair Γ B)]
                    (pair Γ (And A B))
.

Inductive AndLRule : rlsT Seq :=
  | AndLRule_I : forall A B C Γ0 Γ1,
          AndLRule [(pair (Γ0 ++ A :: B :: Γ1) C)]
                    (pair (Γ0 ++ (And A B) :: Γ1) C)
.

Inductive OrR1Rule : rlsT Seq :=
  | OrR1Rule_I : forall A B Γ,
          OrR1Rule [(pair Γ A)]
                    (pair Γ (Or A B))
.

Inductive OrR2Rule : rlsT Seq :=
  | OrR2Rule_I : forall A B Γ,
          OrR2Rule [(pair Γ B)]
                    (pair Γ (Or A B))
.

Inductive OrLRule : rlsT Seq :=
  | OrLRule_I : forall A B C Γ0 Γ1,
          OrLRule [(pair (Γ0 ++ A :: Γ1) C) ; (pair (Γ0 ++ B :: Γ1) C)]
                    (pair (Γ0 ++ (Or A B) :: Γ1) C)
.

Inductive ImpRRule : rlsT Seq :=
  | ImpRRule_I : forall A B Γ0 Γ1,
          ImpRRule [(pair (Γ0 ++ A :: Γ1) B)]
                    (pair (Γ0 ++ Γ1) (Imp A B))
.

Inductive AtomImpL1Rule  : rlsT Seq :=
  | AtomImpL1Rule_I : forall P A C Γ0 Γ1 Γ2,
          AtomImpL1Rule [(pair (Γ0 ++ # P :: Γ1 ++ A :: Γ2) C)]
                    (pair (Γ0 ++ # P :: Γ1 ++ (Imp (# P) A) :: Γ2) C)
.

Inductive AtomImpL2Rule  : rlsT Seq :=
  | AtomImpL2Rule_I : forall P A C Γ0 Γ1 Γ2,
          AtomImpL2Rule [(pair (Γ0 ++ A :: Γ1 ++ # P :: Γ2) C)]
                    (pair (Γ0 ++ (Imp (# P) A) :: Γ1 ++ # P :: Γ2) C)
.

Inductive AndImpLRule  : rlsT Seq :=
  | AndImpLRule_I : forall A B C D Γ0 Γ1,
          AndImpLRule [(pair (Γ0 ++  (Imp A (Imp B C)) :: Γ1) D)]
                    (pair (Γ0 ++  (Imp (And A B) C) :: Γ1) D)
.

Inductive OrImpLRule  : rlsT Seq :=
  | OrImpLRule_I : forall A B C D Γ0 Γ1 Γ2,
          OrImpLRule [(pair (Γ0 ++ (Imp A C) :: Γ1 ++ (Imp B C) :: Γ2) D)]
                    (pair (Γ0 ++ (Imp (Or A B) C) :: Γ1 ++ Γ2) D)
.

Inductive ImpImpLRule  : rlsT Seq :=
  | ImpImpLRule_I : forall A B C D Γ0 Γ1,
          ImpImpLRule [(pair (Γ0 ++ (Imp B C) :: Γ1) (Imp A B)) ; (pair (Γ0 ++ C :: Γ1) D)]
                    (pair (Γ0 ++ (Imp (Imp A  B) C) :: Γ1) D)
.

Inductive BoxImpLRule  : rlsT Seq :=
  | BoxImpLRule_I : forall A B C BΓ Γ0 Γ1,
          (is_Boxed_list BΓ) -> (* have MS of boxed formulae prem L*)
          (nobox_gen_ext BΓ (Γ0 ++ Γ1)) -> (* extend BΓ in Γ0, the L of the ccl *)
          BoxImpLRule [(pair ((XBoxed_list BΓ) ++ [Box A]) A) ; (pair (Γ0 ++ B :: Γ1) C)]
                    (pair (Γ0 ++ (Imp (Box A) B) :: Γ1) C)
.

Inductive GLRRule : rlsT Seq :=
  | GLRRule_I : forall A BΓ Γ,
          (is_Boxed_list BΓ) -> (* have MS of boxed formulae prem L*)
          (nobox_gen_ext BΓ Γ) -> (* extend BΓ in Γ0, the L of the ccl *)
         GLRRule [(pair ((XBoxed_list BΓ) ++ [Box A]) A)] (pair Γ (Box A))
.

(* At last we can define our calculus GLS and its proof-search version PSGLS. *)

Inductive GL4ip_rules : rlsT  Seq :=
  | IdP : forall ps c, IdPRule ps c -> GL4ip_rules ps c
  | BotL : forall ps c, BotLRule ps c -> GL4ip_rules ps c
  | AndR : forall ps c, AndRRule ps c -> GL4ip_rules ps c
  | AndL : forall ps c, AndLRule ps c -> GL4ip_rules ps c
  | OrR1 : forall ps c, OrR1Rule ps c -> GL4ip_rules ps c
  | OrR2 : forall ps c, OrR2Rule ps c -> GL4ip_rules ps c
  | OrL : forall ps c, OrLRule ps c -> GL4ip_rules ps c
  | ImpR : forall ps c, ImpRRule ps c -> GL4ip_rules ps c
  | AtomImpL1 : forall ps c, AtomImpL1Rule ps c -> GL4ip_rules ps c
  | AtomImpL2 : forall ps c, AtomImpL2Rule ps c -> GL4ip_rules ps c
  | AndImpL : forall ps c, AndImpLRule ps c -> GL4ip_rules ps c
  | OrImpL : forall ps c, OrImpLRule ps c -> GL4ip_rules ps c
  | ImpImpL : forall ps c, ImpImpLRule ps c -> GL4ip_rules ps c
  | BoxImpL : forall ps c, BoxImpLRule ps c -> GL4ip_rules ps c
  | GLR : forall ps c, GLRRule ps c -> GL4ip_rules ps c
.

(* Then, we define PSGL4ip. *)

Inductive PSGL4ip_rules : rlsT  Seq :=
  | PSId : forall ps c, IdRule ps c -> PSGL4ip_rules ps c
  | PSBotL : forall ps c, BotLRule ps c -> PSGL4ip_rules ps c
  | PSAndR : forall ps c, (IdRule [] c -> False) ->
                                      (BotLRule [] c -> False) ->AndRRule ps c -> PSGL4ip_rules ps c
  | PSAndL : forall ps c, (IdRule [] c -> False) ->
                                     (BotLRule [] c -> False) ->AndLRule ps c -> PSGL4ip_rules ps c
  | PSOrR1 : forall ps c, (IdRule [] c -> False) ->
                                      (BotLRule [] c -> False) ->OrR1Rule ps c -> PSGL4ip_rules ps c
  | PSOrR2 : forall ps c, (IdRule [] c -> False) ->
                                      (BotLRule [] c -> False) ->OrR2Rule ps c -> PSGL4ip_rules ps c
  | PSOrL : forall ps c, (IdRule [] c -> False) ->
                                   (BotLRule [] c -> False) -> OrLRule ps c -> PSGL4ip_rules ps c
  | PSImpR : forall ps c, (IdRule [] c -> False) ->
                                     (BotLRule [] c -> False) ->ImpRRule ps c -> PSGL4ip_rules ps c
  | PSAtomImpL1 : forall ps c, (IdRule [] c -> False) ->
                                               (BotLRule [] c -> False) -> AtomImpL1Rule ps c -> PSGL4ip_rules ps c
  | PSAtomImpL2 : forall ps c, (IdRule [] c -> False) ->
                                               (BotLRule [] c -> False) ->AtomImpL2Rule ps c -> PSGL4ip_rules ps c
  | PSAndImpL : forall ps c, (IdRule [] c -> False) ->
                                           (BotLRule [] c -> False) -> AndImpLRule ps c -> PSGL4ip_rules ps c
  | PSOrImpL : forall ps c, (IdRule [] c -> False) ->
                                         (BotLRule [] c -> False) -> OrImpLRule ps c -> PSGL4ip_rules ps c
  | PSImpImpL : forall ps c, (IdRule [] c -> False) ->
                                           (BotLRule [] c -> False) -> ImpImpLRule ps c -> PSGL4ip_rules ps c
  | PSBoxImpL : forall ps c, (IdRule [] c -> False) ->
                                           (BotLRule [] c -> False) -> BoxImpLRule ps c -> PSGL4ip_rules ps c
  | PSGLR : forall ps c, (IdRule [] c -> False) ->
                                    (BotLRule [] c -> False) -> GLRRule ps c -> PSGL4ip_rules ps c
.

Definition GL4ip_prv s := derrec GL4ip_rules (fun _ => False) s.
Definition PSGL4ip_prv s := derrec PSGL4ip_rules (fun _ => False) s.

