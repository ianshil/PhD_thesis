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



Declare Scope My_scope.
Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

(* In this file we define two calculi based on multisets for the propositonal modal logic
   GL. The first one, called GLS, is the main calculus for GL. The second one, named PSGLS,
   is essentially the calculus GLS with further restrictions on the application of the
   rules. In other words, the calculus PSGLS is a proof-search oriented version of GLS. *)




(* ---------------------------------------------------------------------------------------------------------------------------------- *)

(* Definitions Language *)

(* First, we use a set of propositional variables on which equality is decidable. *)

Global Parameter V : Set.

Parameter eq_dec_propvar : forall x y : V, {x = y}+{x <> y}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).



(* Secondt, let us define the propositional formulas we use here. *)

Inductive MPropF : Type :=
 | Var : V -> MPropF
 | Bot : MPropF
 | Imp : MPropF -> MPropF -> MPropF
 | Box : MPropF -> MPropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Imp A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.

Lemma eq_dec_form : forall x y : MPropF, {x = y}+{x <> y}.
Proof.
induction x.
- intros. destruct y.
  * pose (eq_dec_propvar v v0). destruct s. left. subst. reflexivity.
    right. intro. inversion H. apply n. assumption.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * left. reflexivity.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
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
  * pose (IHx y). destruct s. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption.
Qed.

Fixpoint size_form (A : MPropF) : nat :=
match A with
 | # P => 1
 | Bot => 1
 | Imp B C => 1 + (size_form B) + (size_form C)
 | Box B => 1 + (size_form B)
end.

(* Now, we can prove that some properties of formulae hold. *)

Definition is_atomicT (A : MPropF) : Type :=
                  (existsT2 (P : V), A = # P) + (A = Bot).

Definition is_boxedT (A : MPropF) : Type :=
                  exists (B : MPropF), A = Box B.

Definition is_primeT (A : MPropF) : Type :=
                  is_atomicT A + is_boxedT A.

(* We can define some types of lists formulae. For example, we can define
   lists of formulae which contain only propositional variables, or
   boxed formulae, or a combination of both. These are useful to define
   the rules. *)

Definition is_Atomic (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) -> ((exists (P : V), A = # P) \/ (A = Bot)).

Definition is_Boxed_list (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) -> (exists (B : MPropF), A = Box B).

Definition is_Prime (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) ->
    (exists (B : MPropF), A = Box B) \/ (exists (P : V), A = # P) \/ (A = Bot).

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
              | Bot => Bot
              | A → B => A → B
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

(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later. *)

Inductive IdPRule : rlsT Seq :=
  | IdPRule_I : forall (P : V) (Γ0 Γ1 Δ0 Δ1 : list (MPropF)), 
          IdPRule [] (pair (Γ0 ++ # P :: Γ1) (Δ0 ++ # P :: Δ1))
.

Inductive IdBRule : rlsT Seq :=
  | IdBRule_I : forall A Γ0 Γ1 Δ0 Δ1, 
          IdBRule [] (pair (Γ0 ++ Box A :: Γ1) (Δ0 ++ Box A :: Δ1))
.

Inductive BotLRule : rlsT Seq :=
  | BotLRule_I : forall Γ0 Γ1 Δ,
          BotLRule [] (pair (Γ0 ++ (Bot) :: Γ1) Δ)
.

Inductive ImpRRule : rlsT Seq :=
  | ImpRRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpRRule [(pair (Γ0 ++ A :: Γ1) (Δ0 ++ B :: Δ1))]
                    (pair (Γ0 ++ Γ1) (Δ0 ++ (A → B) :: Δ1))
.

Inductive ImpLRule : rlsT Seq :=
  | ImpLRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpLRule ((pair (Γ0 ++ Γ1) (Δ0 ++ A :: Δ1)) ::
                     [(pair (Γ0 ++ B :: Γ1) (Δ0 ++ Δ1))])
                    (pair (Γ0 ++ (A → B) :: Γ1) (Δ0 ++ Δ1))
.

Inductive GLRRule : rlsT Seq :=
  | GLRRule_I : forall A BΓ Γ0 Δ0 Δ1,
          (is_Boxed_list BΓ) -> (* have MS of boxed formulae prem L*)
          (nobox_gen_ext BΓ Γ0) -> (* extend BΓ in Γ0, the L of the ccl *)
         GLRRule [(pair ((XBoxed_list BΓ) ++ [Box A]) [A])] (pair Γ0 (Δ0 ++ Box A :: Δ1))
.

(* At last we can define our calculus GLS and its proof-search version PSGLS. *)

Inductive GLS_rules : rlsT Seq :=
  | IdP : forall ps c, IdPRule ps c -> GLS_rules ps c
  | BotL : forall ps c, BotLRule ps c -> GLS_rules ps c
  | ImpR : forall ps c, ImpRRule ps c -> GLS_rules ps c
  | ImpL : forall ps c, ImpLRule ps c -> GLS_rules ps c
  | GLR : forall ps c, GLRRule ps c -> GLS_rules ps c
.

Inductive PSGLS_rules : rlsT Seq :=
  | PSIdP : forall ps c, IdPRule ps c -> PSGLS_rules ps c
  | PSIdB : forall ps c, IdBRule ps c -> PSGLS_rules ps c
  | PSBotL : forall ps c, BotLRule ps c -> PSGLS_rules ps c
  | PSImpR : forall ps c, ImpRRule ps c ->
                          PSGLS_rules ps c
  | PSImpL : forall ps c, ImpLRule ps c ->
                          PSGLS_rules ps c
  | PSGLR : forall ps c, (IdPRule [] c -> False) ->
                       (IdBRule [] c -> False) ->
                       (BotLRule [] c -> False) ->
                       GLRRule ps c ->
                         PSGLS_rules ps c
.

(* We can show that all identities are provable in GLS. *)

Lemma Id_all_form : forall (A : MPropF) l0 l1 l2 l3,
          derrec GLS_rules (fun _ => False) (l0 ++ A :: l1, l2 ++ A :: l3).
Proof.
assert (DersNilF: dersrec GLS_rules  (fun _ : rel (list (MPropF)) => False) []).
apply dersrec_nil.

induction A.
- intros. assert (IdPRule [] (l0 ++ # v :: l1, l2 ++ # v :: l3)). apply IdPRule_I. apply IdP in H.
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[])
  (l0 ++ # v :: l1, l2 ++ # v :: l3) H DersNilF). assumption.
- intros. assert (BotLRule [] (l0 ++ ⊥ :: l1, l2 ++ ⊥ :: l3)). apply BotLRule_I. apply BotL in H.
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[])
  (l0 ++ ⊥ :: l1, l2 ++ ⊥ :: l3) H DersNilF). assumption.
- intros. assert (ImpRRule [(l0 ++ A1 :: A1 → A2 :: l1, l2 ++ A2 :: l3)] (l0 ++ A1 → A2 :: l1, l2 ++ A1 → A2 :: l3)).
  apply ImpRRule_I. apply ImpR in H.
  assert (ImpLRule [((l0 ++ [A1]) ++ l1, l2 ++ A1 :: A2 :: l3); ((l0 ++ [A1]) ++ A2 :: l1, l2 ++ A2 :: l3)] ((l0 ++ [A1]) ++ A1 → A2 :: l1, l2 ++ A2 :: l3)).
  apply ImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0. apply ImpL in H0.
  pose (IHA1 l0 l1 l2 (A2 :: l3)). pose (IHA2 (l0 ++ [A1]) l1 l2 l3). repeat rewrite <- app_assoc in d0. simpl in d0.
  pose (dlCons d0 DersNilF). pose (dlCons d d1).
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(l0 ++ A1 :: l1, l2 ++ A1 :: A2 :: l3); (l0 ++ A1 :: A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 :: A1 → A2 :: l1, l2 ++ A2 :: l3) H0 d2). pose (dlCons d3 DersNilF).
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(l0 ++ A1 :: A1 → A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 → A2 :: l1, l2 ++ A1 → A2 :: l3) H d4). assumption.
- intros. assert (GLRRule [(XBoxed_list (top_boxes (l0 ++ Box A :: l1)) ++ [Box A], [A])] (l0 ++ Box A :: l1, l2 ++ Box A :: l3)).
  apply GLRRule_I. apply is_Boxed_list_top_boxes. rewrite top_boxes_distr_app. simpl. apply univ_gen_ext_combine.
  apply nobox_gen_ext_top_boxes. apply univ_gen_ext_cons. apply nobox_gen_ext_top_boxes.
  rewrite top_boxes_distr_app in X. simpl in X. rewrite XBox_app_distrib in X. simpl in X.
  repeat rewrite <- app_assoc in X. simpl in X.
  pose (IHA (XBoxed_list (top_boxes l0)) (Box A :: XBoxed_list (top_boxes l1) ++ [Box A]) [] []).
  simpl in d. pose (dlCons d DersNilF). apply GLR in X.
  pose (derI (rules:=GLS_rules) (prems:=fun _ : rel (list (MPropF)) => False) (ps:=[(XBoxed_list (top_boxes l0) ++ A :: Box A :: XBoxed_list (top_boxes l1) ++ [Box A], [A])])
  (l0 ++ Box A :: l1, l2 ++ Box A :: l3) X d0). assumption.
Qed.




Definition GLS_prv s := derrec GLS_rules (fun _ => False) s.
Definition GLS_drv s := derrec GLS_rules (fun _ => True) s.
Definition PSGLS_prv s := derrec PSGLS_rules (fun _ => False) s.
Definition PSGLS_drv s := derrec PSGLS_rules (fun _ => True) s.


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


