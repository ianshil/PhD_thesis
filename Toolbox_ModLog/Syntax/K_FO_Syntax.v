(** * First-Order Logic *)
(** ** Syntax *)

Require Import Lia.
Require Import FunctionalExtensionality.
Require Import Ensembles.
Require Import Coq.Vectors.Vector.
Local Notation vec := t.
From Equations Require Import Equations.



(* Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(* Signatures are a record to allow for easier definitions of general transkformations on signatures *)

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  (* We use the stdlib definition of vectors to be maximally compatible  *)

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Set Elimination Schemes.

  Fixpoint subst_term (σ : nat -> term) (t : term) : term :=
    match t with
    | var n => σ n
    | func f v => func f (map (subst_term σ) v)
    end.

  Context {Σ_preds : preds_signature}.

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {unop : Type ; binop : Type ; quantop : Type}.
  Context {ops : operators}.

  Inductive kform : Type :=
  | Bot : kform
  | atom : forall (P : preds), vec term (ar_preds P) -> kform
  | un : unop -> kform -> kform
  | bin : binop -> kform -> kform -> kform
  | quant : quantop -> kform -> kform.

  Definition up (σ : nat -> term) : nat -> term := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_kform (σ : nat -> term) (phi : kform) : kform :=
    match phi with
    | Bot => Bot
    | atom P v => atom P (map (subst_term σ) v)
    | un op phi => un op (subst_kform σ phi)
    | bin op phi1 phi2 => bin op (subst_kform σ phi1) (subst_kform σ phi2)
    | quant op phi => quant op (subst_kform (up σ) phi)
    end.

End fix_signature.



(* Setting implicit arguments is crucial  *)
(* We can write term Both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

(* Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments kform  _ _ _ , _ _ {_}, {_ _ _}.
Arguments atom  _ _ _ , _ _ {_}, {_ _ _}.
Arguments bin   _ _ _ , _ _ {_}, {_ _ _}.
Arguments un   _ _ _ , _ _ {_}, {_ _ _}.
Arguments quant _ _ _ , _ _ {_}, {_ _ _}.

Arguments up         _, {_}.
Arguments subst_kform _ _ _, _ _ {_}, {_ _ _}.



(* Substitution Notation *)

Declare Scope subst_scope.
Open Scope subst_scope.

Notation "$ x" := (var x) (at level 3, format "$ '/' x") : subst_scope.
Notation "t `[ sigma ]" := (subst_term sigma t) (at level 7, left associativity, format "t '/' `[ sigma ]") : subst_scope.
Notation "phi [ sigma ]" := (subst_kform sigma phi) (at level 7, left associativity, format "phi '/' [ sigma ]") : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (at level 50) : subst_scope.
Notation "s '..'" := (scons s var) (at level 4, format "s ..") : subst_scope.
Notation "↑" := (S >> var) : subst_scope.



(* Full syntax *)

Declare Scope syn.
Open Scope syn.

Module FullSyntax.

  Inductive full_logic_un_sym : Type :=
  | Box : full_logic_un_sym.

  Inductive full_logic_bin_sym : Type :=
  | Imp : full_logic_bin_sym.

  Inductive full_logic_quant : Type :=
  | All : full_logic_quant
  | Ex : full_logic_quant.

  Definition full_operators : operators :=
    {| unop := full_logic_un_sym ; binop := full_logic_bin_sym ; quantop := full_logic_quant |}.

  #[export] Hint Immediate full_operators : typeclass_instances.

  Notation "∀ Phi" := (@quant _ _ full_operators All Phi) (at level 50) : syn.
  Notation "∃ Phi" := (@quant _ _ full_operators Ex Phi) (at level 50) : syn.
  Notation "A '-->' B" := (@bin _ _ full_operators Imp A B) (at level 43, right associativity) : syn.
  Notation "⊥" := (Bot) : syn.
  Notation "¬ A" := (A --> ⊥) (at level 42) : syn.

End FullSyntax.

Export FullSyntax.



Section fix_signature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {ops : operators}.

  (* Induction principle for terms *)

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
  | vec_inB {n} (v : t A n) : vec_in a (cons A a n v)
  | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
  Hint Constructors vec_in : core.

  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1 ; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.

Inductive InTv {A : Type} (a : A) : forall n : nat, vec A n -> Type :=
    InTv_cons_hd : forall (m : nat) (v : vec A m), InTv a (S m) (cons A a m v)
  | InTv_cons_tl : forall (m : nat) (x : A) (v : vec A m), InTv a m v -> InTv a (S m) (cons A x m v).

   Lemma term_indT (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, InTv t (ar_syms F) v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1 ; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

Lemma strong_term_ind' (p : term -> Type) :
  (forall x, p ($x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
Proof.
  intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
  - apply f1.
  - apply f2. induction v.
    + econstructor.
    + econstructor. now eapply strong_term_ind'. eauto.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.


Ltac inv H :=
  inversion H; subst; resolve_existT.

Lemma strong_term_ind (p : term -> Type) :
  (forall x, p ($x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
Proof.
intros f1 f2. eapply strong_term_ind'.
- apply f1.
- intros. apply f2. intros t. induction 1 ; inv X ; eauto.
Qed.

  (* Substitution induction principle for kformulas *)

  Fixpoint size (phi : kform) :=
    match phi with
    | atom _ _ => 1
    | Bot => 1
    | un b phi => S (size phi)
    | bin b phi psi => S (size phi + size psi)
    | quant q phi => S (size phi)
    end.

  Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
  Proof.
    intros H x. apply H.
    induction (f x).
    - intros y. lia.
    - intros y. intros [] % Lt.le_lt_or_eq.
      + apply IHn; lia.
      + apply H. injection H0. now intros ->.
  Qed.

  Lemma subst_size rho phi :
    size (subst_kform rho phi) = size phi.
  Proof.
    revert rho; induction phi; intros rho; cbn; congruence.
  Qed.

  Lemma kform_ind_subst :
    forall P : kform -> Prop,
      P Bot ->
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (u0 : unop) (f : kform), P f -> P (un u0 f)) ->
      (forall (b0 : binop) (f1 : kform), P f1 -> forall f2 : kform, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : kform), (forall sigma, P (subst_kform sigma f2)) -> P (quant q f2)) ->
      forall (f4 : kform), P f4.
  Proof.
    intros P H1 H2 H3 H4 H5 phi. induction phi using (@size_ind _ size). destruct phi.
    - apply H1.
    - apply H2.
    - apply H3. auto.
    - apply H4; apply H; cbn; lia.
    - apply H5. intros sigma. apply H. cbn. rewrite subst_size. lia.
  Qed.

End fix_signature.



(* ** Substitution lemmas *)

Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t`[sigma] = t.
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t`[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t`[sigma]`[tau] = t`[sigma >> subst_term tau].
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t`[↑]`[s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t`[↑]`[up xi] = t`[xi]`[↑].
  Proof.
    rewrite !subst_term_comp. apply subst_term_ext. reflexivity.
  Qed.

  Lemma up_ext sigma tau :
    (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_var sigma :
    (forall n, sigma n = var n) -> forall n, up sigma n = var n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_funcomp sigma tau :
    forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
  Proof.
    intros [|]; cbn; trivial.
    setoid_rewrite subst_term_comp.
    apply subst_term_ext. now intros [|].
  Qed.

  Lemma subst_ext (phi : kform) sigma tau :
    (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
  Proof.
    induction phi in sigma, tau |- *; cbn; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id (phi : kform) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbn; intros H.
    - reflexivity.
    - f_equal. erewrite map_ext; try apply map_id. intros s. now apply subst_term_id.
    - now erewrite IHphi.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_var.
  Qed.

  Lemma subst_var (phi : kform) :
    phi[var] = phi.
  Proof.
    now apply subst_id.
  Qed.

  Lemma subst_comp (phi : kform) sigma tau :
    phi[sigma][tau] = phi[sigma >> subst_term tau].
  Proof.
    induction phi in sigma, tau |- *; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. apply map_ext. intros s. apply subst_term_comp.
    - now rewrite IHphi.
    - now rewrite IHphi1, IHphi2.
    - rewrite IHphi. f_equal. now apply subst_ext, up_funcomp.
  Qed.

  Lemma subst_shift (phi : kform) s :
    phi[↑][s..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma up_kform xi psi :
    psi[↑][up xi] = psi[xi][↑].
  Proof.
    rewrite !subst_comp. apply subst_ext. reflexivity.
  Qed.

  Lemma up_decompose sigma phi :
    phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.

End Subst.

(* From Johannes https://github.com/dominik-kirst/coq-library-undecidability/blob/4c579ddc7c71659a57fbe3a16198bfcaa1b9a020/theories/FOL/Syntax/Facts.v#L956 *)

Section PredicateSubstitution.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

(* I think this definition is too generous: it will not be admissible as there can be capture of variables. *)


Fixpoint atom_subst (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> kform) (phi : kform) :=
    match phi with
    | Bot => Bot
    | atom P t => s P t
    | un b phi => un b (atom_subst s phi)
    | bin b phi psi => bin b (atom_subst s phi) (atom_subst s psi)
    | quant q phi => quant q (atom_subst s phi) 
    end.

  Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope.

  Definition atom_subst_respects  (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> kform)
    := forall P v sigma, (s P v)[sigma>> var] = s P (map (subst_term (sigma >> var)) v).

  Definition atom_subst_respects_strong (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> kform)
    := forall P v sigma, (s P v)[sigma] = s P (map (subst_term (sigma)) v).

  Lemma atom_subst_strong_to_normal s :  atom_subst_respects_strong s ->  atom_subst_respects s.
  Proof.
  intros. intro. intros. auto.
  Qed.

  Lemma atom_subst_id phi : phi[ atom /atom] = phi.
  Proof.
    induction phi ; auto.
    - cbn. now rewrite IHphi.
    - cbn. rewrite IHphi1. now rewrite IHphi2.
    - cbn. now rewrite IHphi.
  Qed.

  Lemma up_var_comp rho x : (up (rho >> var)) x = ((fun n => match n with 0 => 0 | S n => S (rho n) end) >>var) x.
  Proof.
    now destruct x.
  Qed.

  Lemma atom_subst_comp s rho phi : atom_subst_respects s -> phi[s/atom][rho>>var] = phi[rho>>var][s/atom].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - cbn. easy.
  - cbn. now rewrite IHphi.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. f_equal. rewrite ! (subst_ext _ _ _ (up_var_comp _) ). rewrite IHphi. 1:easy.
    easy.
  Qed.

  Lemma atom_subst_comp_strong s rho phi :
    atom_subst_respects_strong s -> phi[s/atom][rho] = phi[rho][s/atom].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - cbn. easy.
  - cbn. now rewrite IHphi.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. now rewrite IHphi.
  Qed.

End PredicateSubstitution.

#[global] Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope.
