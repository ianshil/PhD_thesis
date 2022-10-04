Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Ensembles.

Require Import gen.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Global Parameter V : Set.

Parameter eq_dec_propvar : forall x y : V, {x = y}+{x <> y}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(* In this file we define two generalised Hilbert calculi based on sets for the propositonal
   bi-intuitionistic logics wBIL and sBIL.  *)

(* Definitions Language *)

(* First, let us define the propositional formulae we use here. *)

Inductive BPropF (W : Set) : Type :=
 | Var : W -> BPropF W
 | Bot : BPropF W
 | Top : BPropF W
 | And : BPropF W -> BPropF W -> BPropF W
 | Or : BPropF W -> BPropF W -> BPropF W
 | Imp : BPropF W -> BPropF W -> BPropF W
 | Excl : BPropF W -> BPropF W -> BPropF W
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Imp A B) (at level 16, right associativity) : My_scope.

Definition wNeg (A : BPropF V) := Excl (Top _) A.
Definition Neg (A : BPropF V) := Imp A (Bot _).

Fixpoint DN_form (n : nat) (A : (BPropF V)) : (BPropF V) :=
match n with
 | 0 => A
 | S m => Neg (wNeg (DN_form m A))
end.

Inductive DN_clos_set (Γ : @Ensemble (BPropF V)): @Ensemble (BPropF V) :=
  | InitClo : forall A, In _ Γ A -> DN_clos_set Γ A
  | IndClo : forall A,  DN_clos_set Γ A -> DN_clos_set Γ (Neg (wNeg A)).

Lemma eq_dec_form : forall x y : BPropF V, {x = y}+{x <> y}.
Proof.
induction x.
- intros. destruct y.
  * pose (eq_dec_propvar v w). destruct s. left. subst. reflexivity.
    right. intro. inversion H. apply n. symmetry in H1. assumption.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * auto.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * auto.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n. auto.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n. auto.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n. auto.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n. auto.
Qed.



Fixpoint size_form (A : BPropF V) : nat :=
match A with
 | # P => 1
 | Bot _ => 1
 | Top _ => 1
 | And B C => 1 + (size_form B) + (size_form C)
 | Or B C => 1 + (size_form B) + (size_form C)
 | Imp B C => 1 + (size_form B) + (size_form C)
 | Excl B C => 1 + (size_form B) + (size_form C)
end.

Fixpoint subst (f : V -> (BPropF V)) (A : (BPropF V)) : (BPropF V) :=
match A with
 | # P => (f P)
 | Bot _ => Bot _
 | Top _ => Top _
 | And B C => And (subst f B) (subst f C)
 | Or B C => Or (subst f B) (subst f C)
 | Imp B C => Imp (subst f B) (subst f C)
 | Excl B C => Excl (subst f B) (subst f C)
end.

(* Now, we candefine some properties of formulas. *)

Definition is_atomicT (A : BPropF V) : Type :=
                  (exists (P : V), A = # P) + (A = Bot _) + (A = Top _).

(* We can define some types of lists formulae. For example, we can define
   lists of formulae which contain only propositional variables. *)

Definition is_Atomic (Γ : @Ensemble (BPropF V)) : Type :=
    forall (A : BPropF V), (Γ A) -> ((exists (P : V), A = # P) + (A = Bot _) + (A = Top _)).

(* We define here the axioms. *)

Definition RA1 (A B C : BPropF V) : BPropF V := (A → B) → ((B → C) → (A → C)).
Definition RA2 (A B : BPropF V) : BPropF V := A → (Or A B).
Definition RA3 (A B : BPropF V) : BPropF V := B → (Or A B).
Definition RA4 (A B C : BPropF V) : BPropF V := (A → C) → ((B → C) → ((Or A B) → C)).
Definition RA5 (A B : BPropF V) : BPropF V := (And A B) → A.
Definition RA6 (A B : BPropF V) : BPropF V := (And A B) → B.
Definition RA7 (A B C : BPropF V) : BPropF V := (A → B) → ((A → C) → (A → (And B C))).
Definition RA8 (A B C : BPropF V) : BPropF V := (A → (B → C)) → ((And A B) → C).
Definition RA9 (A B C : BPropF V) : BPropF V := ((And A B) → C) → (A → (B → C)).
Definition RA10 (A B : BPropF V) : BPropF V := (A → B) → ((Neg B) → (Neg A)).
Definition RA11 (A B : BPropF V) : BPropF V := A → (Or B (Excl A B)).
Definition RA12 (A B : BPropF V) : BPropF V := (Excl A B) → (wNeg (A → B)).
Definition RA13 (A B C : BPropF V) : BPropF V := (Excl (Excl A B) C) → (Excl A (Or B C)).
Definition RA14 (A B : BPropF V) : BPropF V := (Neg (Excl A B)) → (A → B).
Definition RA15 (A : BPropF V) : BPropF V := A → (Top _).
Definition RA16 (A : BPropF V) : BPropF V := (Bot _) → A.

Inductive BIAxioms (A : BPropF V) : Prop :=
 | RA1_I : (exists B C D, A = (RA1 B C D)) -> BIAxioms A
 | RA2_I : (exists B C, A = (RA2 B C)) -> BIAxioms A
 | RA3_I :  (exists B C, A = (RA3 B C)) -> BIAxioms A
 | RA4_I :  (exists B C D, A = (RA4 B C D)) -> BIAxioms A
 | RA5_I :  (exists B C, A = (RA5 B C)) -> BIAxioms A
 | RA6_I :  (exists B C, A = (RA6 B C)) -> BIAxioms A
 | RA7_I :  (exists B C D, A = (RA7 B C D)) -> BIAxioms A
 | RA8_I :  (exists B C D, A = (RA8 B C D)) -> BIAxioms A
 | RA9_I :  (exists B C D, A = (RA9 B C D)) -> BIAxioms A
 | RA10_I :  (exists B C, A = (RA10 B C)) -> BIAxioms A
 | RA11_I :  (exists B C, A = (RA11 B C)) -> BIAxioms A
 | RA12_I :  (exists B C, A = (RA12 B C)) -> BIAxioms A
 | RA13_I :  (exists B C D, A = (RA13 B C D)) -> BIAxioms A
 | RA14_I :  (exists B C, A = (RA14 B C)) -> BIAxioms A
 | RA15_I :  (exists B, A = (RA15 B)) -> BIAxioms A
 | RA16_I :  (exists B, A = (RA16 B)) -> BIAxioms A.

(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later.

   We start by giving the rules common to both calculi. *)

Inductive IdRule : rls ((@Ensemble (BPropF V)) * (BPropF V)) :=
  | IdRule_I : forall A (Γ : @Ensemble _),
                  (Γ A) -> (IdRule [] (pair Γ A)).

Inductive AxRule : rls ((@Ensemble (BPropF V)) * (BPropF V)) :=
  | AxRule_I : forall Γ (A : BPropF V),
          (BIAxioms A) -> AxRule [] (pair Γ A)
.

Inductive MPRule : rls ((@Ensemble (BPropF V)) * (BPropF V)) :=
  | MPRule_I : forall A B Γ,
          MPRule [(pair Γ (A → B)); (pair Γ A)]
                    (pair Γ B)
.

(* Then we turn to the distinctive rules of each calculus. *)

Inductive DNwRule : rls ((@Ensemble (BPropF V)) * (BPropF V)) :=
  | DNwRule_I : forall (A : BPropF V) Γ,
          DNwRule [(pair (@Empty_set (BPropF V)) A)]
                    (pair Γ (Neg (wNeg A)))
.

Inductive DNsRule : rls ((@Ensemble (BPropF V)) * (BPropF V)) :=
  | DNsRule_I : forall (A : BPropF V) Γ,
          DNsRule [(pair Γ A)]
                    (pair Γ (Neg (wNeg A)))
.

(* At last we can define our calculi wBIH and sBIH. *)

Inductive wBIH_rules (s : ((@Ensemble (BPropF V)) * (BPropF V))) : Prop :=
  | Id : IdRule [] s -> wBIH_rules s
  | Ax : AxRule [] s -> wBIH_rules s
  | MP : forall ps, (forall prem, List.In prem ps -> wBIH_rules prem) -> MPRule ps s -> wBIH_rules s
  | DNw : forall ps, (forall prem, List.In prem ps -> wBIH_rules prem) -> DNwRule ps s -> wBIH_rules s
.

Inductive sBIH_rules (s : ((@Ensemble (BPropF V)) * (BPropF V))) : Prop :=
  | Ids : IdRule [] s -> sBIH_rules s
  | Axs : AxRule [] s -> sBIH_rules s
  | MPs : forall ps, (forall prem, List.In prem ps -> sBIH_rules prem) -> MPRule ps s -> sBIH_rules s
  | DNs : forall ps, (forall prem, List.In prem ps -> sBIH_rules prem) -> DNsRule ps s -> sBIH_rules s
.

(* Define the general notion of derivable pair. *)

Fixpoint list_disj (l : list (BPropF V)) : BPropF V :=
match l with
 | nil => Bot _
 | h :: t => Or h (list_disj t)
end.

Definition wpair_derrec (G : prod (@Ensemble (BPropF V)) (@Ensemble (BPropF V))) : Prop :=
    exists (l : list (BPropF V)), NoDup l /\ (forall A, List.In A l -> ((snd G) A)) /\
        (wBIH_rules (fst G, list_disj l)).

Definition spair_derrec (G : prod (@Ensemble (BPropF V)) (@Ensemble (BPropF V))) : Prop :=
    exists (l : list (BPropF V)), NoDup l /\ (forall A, List.In A l -> ((snd G) A)) /\
        (sBIH_rules (fst G, list_disj l)).

Definition complete (G : prod (@Ensemble (BPropF V)) (@Ensemble (BPropF V))) : Prop :=
    forall (A : BPropF V), (fst G) A \/ (snd G) A.


