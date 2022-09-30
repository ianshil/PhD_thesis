Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Ensembles.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments. 

Global Parameter V : Set.

Parameter eq_dec_propvar : forall p q : V, {p = q}+{p <> q}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(* Definitions Language *)

(* First, let us define the propositional formulas we use here. *)

Inductive MPropF : Type :=
 | Var : V -> MPropF
 | Bot : MPropF
 | Imp : MPropF -> MPropF -> MPropF
 | Box : MPropF -> MPropF
.

Notation "# p" := (Var p) (at level 1).
Notation "A --> B" := (Imp A B) (at level 16, right associativity).

Definition Neg (A : MPropF) := Imp A (Bot).

Fixpoint Box_power (n : nat) (A : MPropF) : MPropF :=
match n with
 | 0 => A
 | S m => Box (Box_power m A)
end.

Fixpoint Imp_Box_power (n : nat) (A B : MPropF) : MPropF :=
match n with
 | 0 => A --> B
 | S m => A --> (Imp_Box_power m (Box A) B)
end.

Inductive Box_clos_set (Γ : @Ensemble MPropF): @Ensemble MPropF :=
  | InitClo : forall A, In _ Γ A -> Box_clos_set Γ A
  | IndClo : forall A,  Box_clos_set Γ A -> Box_clos_set Γ (Box A).

Lemma eq_dec_form : forall x y : MPropF, {x = y}+{x <> y}.
Proof.
induction x.
- intros. destruct y.
  * pose (eq_dec_propvar v v0). destruct s. left. subst. reflexivity.
    right. intro. inversion H. apply n. auto.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * auto.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n. auto.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx y). destruct s. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption.
Qed.



Fixpoint size (A : MPropF) : nat :=
match A with
 | # p => 1
 | Bot => 1
 | B --> C => 1 + (size B) + (size C)
 | Box B => 1 + (size B)
end.

Fixpoint subst (f : V -> MPropF) (A : MPropF) : MPropF :=
match A with
 | # p => (f p)
 | Bot => Bot
 | B --> C => Imp (subst f B) (subst f C)
 | Box B => Box (subst f B)
end.

Definition is_atomicT (A : MPropF) : Type :=
                  (exists (p : V), A = # p) + (A = Bot).

Definition is_Atomic (Γ : @Ensemble MPropF) : Type :=
    forall (A : MPropF), (Γ A) -> ((exists (p : V), A = # p) + (A = Bot)).

Fixpoint list_Imp (A : MPropF) (l : list MPropF) : MPropF :=
match l with
 | nil => A
 | h :: t => h --> (list_Imp A t)
end.

Fixpoint Box_list (l : list MPropF) : list MPropF :=
match l with
 | nil => nil
 | h :: t => (Box h) :: (Box_list t)
end.


