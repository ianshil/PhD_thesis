Require Import Classical.
(* Used in various places:
    - existence of a derivation in the axiomtic system for a sequent
      (should be decidable as Bi-Int is, but this would require extra work)
    - existence of a formula for which a number is an encoding (if I write
      down the function I might be able to extract it)
    - some set-theoretic arguments (maybe they can be constructivised) *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Vectors.Vector.
Require Import Ensembles.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_logics.
Require Import FO_BiInt_extens_interactions.
Require Import FOwBIH_meta_interactions.
Require Import FOsBIH_meta_interactions.
Require Import FO_BiInt_remove_list.
Require Import FO_BiInt_strong_induction.

Section Lindenbaum.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Local Notation vec := t.

Section Option.

Lemma eq_dec_option_form : forall (x y : option form),  {x = y} + {x <> y}.
Proof.
intros. destruct x ; destruct y ; auto. 2-3: right ; intro ; inversion H.
destruct (eq_dec_form f f0). subst. left ; auto. right. intro. inversion H. auto.
Qed.

Variable f : nat -> option form.
Hypothesis Hf : forall x, exists n, f n = Some x.

Definition f_unoption :
  nat -> form.
Proof.
  intros x. remember (f x) as opt. destruct opt.
  - exact f0.
  - exact bot.
Defined.

Lemma f_unoption_surj :
  forall x, exists n, f_unoption n = x.
Proof.
unfold f_unoption. intros. pose (Hf x). destruct e. exists x0. destruct (f x0). inversion H ; auto.
inversion H.
Qed.

End Option.



(* Closed theories / lists *)

Inductive unused_term (n : nat) : term -> Prop :=
| ut_var m : (n <> m) -> unused_term n (var m)
| ut_func f v : (forall t, Vector.In t v -> unused_term n t) -> unused_term n (func f v).

Inductive unused (n : nat) : form -> Prop :=
| uf_bot : unused n bot
| uf_top : unused n top
| uf_atom P v : (forall t, Vector.In t v -> unused_term n t) -> unused n (atom P v)
| uf_bin op phi psi : unused n phi -> unused n psi -> unused n (bin op phi psi)
| uf_quant q phi : unused (S n) phi -> unused n (quant q phi).

Definition unused_L n l := forall phi, List.In phi l -> unused n phi.
Definition unused_S n X := forall phi, In _ X phi -> unused n phi.
Definition First_unused n Γ:= (unused_S n Γ) /\ (forall m, (unused_S m Γ) -> n <= m).
Definition closed phi := forall n, unused n phi.
Definition closed_L l := forall phi, List.In phi l -> closed phi.
Definition closed_S X := forall phi, In _ X phi -> closed phi.







(* Interactions between unused and quantifiers. *)

Lemma vec_in_VectorIn_term : forall (n : nat) (v : vec term n) (t : term), vec_in t v -> Vector.In t v.
Proof.
induction n.
- intros. inversion X.
- intros. inversion X. subst. destruct H. apply In_cons_hd. destruct H. subst. apply In_cons_tl. apply IHn ; auto.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.


Ltac inv H :=
  inversion H; subst; resolve_existT.

Lemma vec_map_ext X Y (f g : X -> Y) n (v : vec X n) :
    (forall x, vec_in x v -> f x = g x) -> map f v = map g v.
Proof.
  intros Hext; induction v in Hext |-*; cbn.
  - reflexivity.
  - rewrite IHv, (Hext h). 1: reflexivity. apply vec_inB. intros. apply Hext. apply vec_inS. auto.
Qed.

Lemma subst_unused_term xi sigma P t :
    (forall x, (P x) \/ (~ (P x))) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused_term m t) ->
    subst_term xi t = subst_term sigma t.
Proof.
intros Hdec Hext Hunused. induction t using strong_term_ind; cbn;   simpl.
  - destruct (Hdec x) as [H % Hunused | H % Hext].
    + inversion H; subst; congruence.
    + congruence.
  - f_equal. apply vec_map_ext. intros t H'. apply (H t H'). intros n H2 % Hunused. inv H2. apply H1.
    apply vec_in_VectorIn_term ; auto. apply eq_dec_funcs.
Qed.

Definition shift_P P n :=
    match n with
    | O => False
    | S n' => P n'
    end.

Lemma subst_unused_form xi sigma P phi :
    (forall x, (P x) \/ (~ P x)) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused m phi) ->
    subst_form xi phi = subst_form sigma phi.
Proof.
induction phi in xi,sigma,P |-*; intros Hdec Hext Hunused; cbn; simpl ; auto.
  - f_equal. apply vec_map_ext. intros s H. apply (subst_unused_term _ _ _ _ Hdec Hext).
    intros m H' % Hunused. inv H'. apply H1 ; auto. apply vec_in_VectorIn_term ; auto. apply eq_dec_preds.
  - rewrite IHphi1 with (sigma := sigma) (P := P). rewrite IHphi2 with (sigma := sigma) (P := P).
    all: try tauto. all: intros m H % Hunused; now inversion H.
  - erewrite IHphi with (P := shift_P P). 1: reflexivity.
    + intros [| x]; [now right| now apply Hdec].
    + intros [| m]; [reflexivity|]. intros Heq % Hext; unfold ">>"; cbn. unfold ">>". rewrite Heq ; auto.
    + intros [| m]; [destruct 1| ]. intros H % Hunused; now inversion H.
Qed.

Lemma subst_unused_single xi sigma n phi :
    unused n phi -> (forall m, n <> m -> xi m = sigma m) -> subst_form xi phi = subst_form sigma phi.
Proof.
intros Hext Hunused. apply subst_unused_form with (P := fun m => n = m). all: intuition ; subst.
pose (eq_dec_nat n x). destruct s ; auto. auto.
Qed.

Definition cycle_shift n x := if eq_dec_nat n x then $0 else $(S x).

Lemma cycle_shift_subject n phi : unused (S n) phi -> phi[($n)..][cycle_shift n] = phi.
Proof.
intros H. rewrite subst_comp. rewrite (subst_unused_single ($n.. >> subst_term (cycle_shift n)) var (S n) _ H).
apply subst_var.
intros m H'. unfold funcomp. unfold cycle_shift.
destruct (eq_dec_nat n n); simpl ; try congruence. destruct m.
simpl. destruct (eq_dec_nat n n); simpl ; try congruence.
simpl. destruct (eq_dec_nat n m); simpl ; try congruence.
Qed.



Lemma cycle_shift_shift n phi : unused n phi -> phi[cycle_shift n] = phi[↑].
Proof.
intros H. apply (subst_unused_single _ _ _ _ H). intros m ?. unfold cycle_shift. destruct (eq_dec_nat n m).
subst. exfalso ; auto. auto.
Qed.

Theorem EC_unused0 : forall s,
  FOwBIH_rules s ->
  (forall n Γ A B, (fst s = Γ) ->
                          (snd s = A[$n..] --> B) ->
                          (unused_S n (fun x => In _ Γ x \/ x = B \/ x = ∃ A)) ->
                          (FOwBIH_rules (Γ, (∃ A) --> B))).
Proof.
intros. destruct s. simpl in H0. simpl in H1. subst.
assert (unused (S n) A). unfold unused_S in H2. pose (H2 (∃ A)).
assert (In form (fun x : form => In form Γ x \/ x = B \/ x = ∃ A) (∃ A)). unfold In ; auto.
apply H2 in H0. inversion H0. auto.
pose (FOwBIH_subst _ (cycle_shift n) H). simpl in f.
pose (cycle_shift_subject n A H0). rewrite e in f. clear e.
pose (cycle_shift_shift n B). rewrite e in f.
assert ((fun x : form => exists B : form, x = B[cycle_shift n] /\ In form Γ B) =
fun x : form => exists B : form, x = B[↑] /\ In form Γ B).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H1 ; subst.
destruct H3 ; subst. unfold In. exists x0 ; split ; auto. rewrite cycle_shift_shift ; auto.
apply H2. unfold In ; auto. unfold In. inversion H1. exists x0. destruct H3 ; subst. split ; auto.
rewrite cycle_shift_shift ; auto. apply H2. unfold In ; auto. 2: apply H2 ; unfold In ; auto.
rewrite H1 in f.
apply EC with (ps:=[(((fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)), A --> (B[↑])))]).
2: apply ECRule_I. intros. inversion H3. subst. 2: inversion H4.
auto.
Qed.

Theorem EC_unused : forall n Γ A B,
  unused_S n (fun x => In _ Γ x \/ x = B \/ x = ∃ A) ->
  FOwBIH_rules (Γ, A[$n..] --> B) ->
  FOwBIH_rules (Γ, (∃ A) --> B).
Proof.
intros. apply (EC_unused0 _ H0 n) ; auto.
Qed.

Theorem Gen_unused0 : forall s,
  FOwBIH_rules s ->
  (forall n Γ A, (fst s = Γ) ->
                          (snd s = A[$n..]) ->
                          (unused_S n (fun x => In _ Γ x \/ x = ∀ A)) ->
                          (FOwBIH_rules (Γ, ∀ A))).
Proof.
intros. destruct s. simpl in H0. simpl in H1. subst.
assert (unused (S n) A). unfold unused_S in H2. pose (H2 (∀ A)).
assert (In form (fun x : form => In form Γ x \/ x = ∀ A) (∀ A)). unfold In ; auto.
apply H2 in H0. inversion H0. auto.
pose (FOwBIH_subst _ (cycle_shift n) H). simpl in f.
pose (cycle_shift_subject n A H0). rewrite e in f. clear e.
assert ((fun x : form => exists B : form, x = B[cycle_shift n] /\ In form Γ B) =
fun x : form => exists B : form, x = B[↑] /\ In form Γ B).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H1 ; subst.
destruct H3 ; subst. unfold In. exists x0 ; split ; auto. rewrite cycle_shift_shift ; auto.
apply H2. unfold In ; auto. unfold In. inversion H1. exists x0. destruct H3 ; subst. split ; auto.
rewrite cycle_shift_shift ; auto. apply H2. unfold In ; auto. rewrite H1 in f.
apply Gen with (ps:=[((fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)), A)]).
2: apply GenRule_I. intros. inversion H3. subst. 2: inversion H4. auto.
Qed.

Theorem Gen_unused : forall n Γ A,
  unused_S n (fun x => In _ Γ x \/ x = ∀ A) ->
  FOwBIH_rules (Γ, A[$n..]) ->
  FOwBIH_rules (Γ, ∀ A).
Proof.
intros. apply (Gen_unused0 _ H0 n) ; auto.
Qed.

(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* We assume given an encoding. *)

Variable encode0 : form -> nat.
Hypothesis encode0_inj : forall (A B : form) (n0 : nat), encode0 A = encode0 B -> A = B.

(* But we use another encoding. *)

Definition encode : form -> nat := fun x => S (encode0 x).

Lemma encode_no_0 : forall A, (encode A = 0) -> False.
Proof.
intros. unfold encode in H. lia.
Qed.

Lemma encode_inj : forall A B, (encode A = encode B) -> A = B.
Proof.
intros. unfold encode in H. unfold encode in H. inversion H.
apply encode0_inj in H1 ; auto.
Qed.

(* We can prove the existence of a decoding function from the function encode. *)

Lemma decoding_inh :
  {g : nat -> option (form) | (forall A, g (encode A) = Some A) /\
                                  (forall n, (forall (E : {A : _ | encode A = n}), (g n = Some (proj1_sig E))) /\
                                             (((exists A, encode A = n) -> False) -> g n = None)) }.
Proof.
apply constructive_definite_description.
assert (H : forall n, exists! op, (forall E : {A : form | encode A = n},
    op = Some (proj1_sig E)) /\ (((exists A : form, encode A = n) -> False) ->
    op = None)).
{ intro n. destruct (classic (exists A, encode A = n)).
  destruct H. exists (Some x). unfold unique. repeat split. intros.
  subst. simpl. destruct E. simpl. pose (encode_inj x x0). symmetry in e.
  pose (e0 e). rewrite e1. auto.
  intro. exfalso. apply H0. exists x. auto. intros. destruct H0.
  assert ({A : form | encode A = n}). exists x. auto. pose (H0 X).
  destruct X. simpl in e. rewrite <- e0 in H. pose (encode_inj x x0).
  pose (e1 H).
  rewrite <- e2 in e. auto. exists None. unfold unique. repeat split. intros.
  exfalso. apply H. destruct E. exists x. auto. intros. destruct H0. apply H1 in H.
  auto. }
exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
split.
- split.
  + intros A.
    destruct (constructive_definite_description _ _).
    simpl. destruct a. assert ({A0 : form | encode A0 = encode A}). exists A. auto.
    pose (H0 X). destruct X. simpl in e. pose (encode_inj x0 A).
    pose (e1 e0). rewrite <- e2. auto.
  + intros n.
    now destruct (constructive_definite_description _ _).
- intros g' [H1 H2].
  apply functional_extensionality.
  intros n.
  destruct (constructive_definite_description _ _) as [x e].
  simpl. destruct e. destruct (classic (exists A, encode A = n)).
  + clear H3. destruct H4. assert ({A : form | encode A = n}). exists x0. auto.
    pose (H0 X). pose (H2 n). destruct a. pose (H4 X). destruct X. simpl in e0.
    simpl in e. rewrite e. rewrite e0. auto.
  + pose (H3 H4). rewrite e. pose (H2 n). destruct a. pose (H6 H4). rewrite e0. auto.
Qed.

Definition decoding : nat -> option (form) := proj1_sig decoding_inh.

Lemma encode_decode_Id : forall A, decoding (encode A) = Some A.
Proof.
intro. unfold decoding. destruct decoding_inh. destruct a. auto.
Qed.






(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* How we build extensions. *)

Definition gen_choice_code (Γ Δ : @Ensemble (form)) (n :nat) : prod (Ensemble form) (Ensemble form) :=
match decoding n with
| None => (Γ, Δ)
| Some A => match A with
            | quant q A => match q with
                        | All => pair (fun x => (In _ Γ x) \/ (((wpair_der ((Union _ Γ (Singleton _ (quant All A))), Δ)) -> False) /\ x = (quant All A)))
                                           (fun x => (In _ Δ x) \/ ((wpair_der ((Union _ Γ (Singleton _ (quant All A))),Δ)) /\ (x = (quant All A) \/
                                                          (exists n, (First_unused n (fun y => In _ Γ y \/ In _ Δ y \/ y = (quant All A)) /\ x = A[(var n)..])))))
                        | Ex => pair (fun x => (In _ Γ x) \/ (((wpair_der ((Union _ Γ (Singleton _ (quant Ex A))), Δ)) -> False) /\ (x = (quant Ex A) \/
                                                          (exists n, (First_unused n (fun y => In _ Γ y \/ In _ Δ y \/ y = (quant Ex A)) /\ x = A[(var n)..])))))
                                            (fun x => (In _ Δ x) \/ ((wpair_der ((Union _ Γ (Singleton _ (quant Ex A))),Δ)) /\ x = (quant Ex A)))
                        end
            | A => pair (fun x => (In _ Γ x) \/ (((wpair_der ((Union _ Γ (Singleton _ A)), Δ)) -> False) /\ x = A))
                             (fun x => (In _ Δ x) \/ ((wpair_der ((Union _ Γ (Singleton _ A)),Δ)) /\ x = A))
            end
end.






(* ------------------------------------------------------------------------------------------------------ *)

(* Now we turn to the Lindenbaum extension. *)

(* Definition of the extension *)

Fixpoint nextension_theory (Γ Δ : @Ensemble (form)) (n : nat) :  prod (Ensemble form) (Ensemble form) :=
match n with
| 0 => (Γ, Δ)
| S m => gen_choice_code (fst (nextension_theory Γ Δ m)) (snd (nextension_theory Γ Δ m)) (S m)
end.

Definition extension_theory (Γ Δ : @Ensemble (form)) : prod (Ensemble form) (Ensemble form) :=
 pair (fun x => (exists n, In _ (fst (nextension_theory Γ Δ n)) x))
        (fun x => (exists n, In _ (snd (nextension_theory Γ Δ n)) x)).


(* Properties of the extension *)

Lemma nextension_theory_extens : forall n (Γ Δ: @Ensemble (form)) x,
    (In (form) Γ x -> In (form) (fst (nextension_theory Γ Δ n)) x) /\
    (In (form) Δ x -> In (form) (snd (nextension_theory Γ Δ n)) x).
Proof.
induction n.
- simpl. auto.
- simpl. intros. split ; intro.
  + pose (IHn Γ Δ x). destruct a. pose (H0 H). unfold gen_choice_code.
     destruct (decoding (S n)).
    * destruct f ; auto ; simpl ; unfold In ; auto. destruct q.
      ++ simpl. auto.
      ++ simpl. auto.
    * auto.
  + pose (IHn Γ Δ x). destruct a. pose (H1 H). unfold gen_choice_code.
     destruct (decoding (S n)).
    * destruct f ; auto ; simpl ; unfold In ; auto. destruct q.
      ++ simpl. auto.
      ++ simpl. auto.
    * auto.
Qed.

(* Each step creates an extension of the theory in the previous step. *)

Lemma nextension_theory_extens_le : forall m n (Γ Δ: @Ensemble (form)) x,
    (In (form) (fst (nextension_theory Γ Δ n)) x -> (le n m) -> In (form) (fst (nextension_theory Γ Δ m)) x) /\
    (In (form) (snd (nextension_theory Γ Δ n)) x -> (le n m) -> In (form) (snd (nextension_theory Γ Δ m)) x).
Proof.
induction m.
- intros. split ; intros ; simpl ; inversion H0 ; subst ; simpl in H ; auto.
- intros. split ; intros ; inversion H0.
  + subst. auto.
  + subst. simpl. unfold In. apply IHm in H ; auto. unfold gen_choice_code.
    destruct (decoding (S m)).
    * destruct f ; simpl ; auto. destruct q ; simpl ; auto.
    * auto.
  + subst. auto.
  + subst. simpl. unfold In. apply IHm in H ; auto. unfold gen_choice_code.
    destruct (decoding (S m)).
    * destruct f ; simpl ; auto. destruct q ; simpl ; auto.
    * auto.
Qed.

Lemma extension_theory_extens_nextension : forall n (Γ Δ: @Ensemble (form)) x,
    (In (form) (fst (nextension_theory Γ Δ n)) x -> In (form) (fst (extension_theory Γ Δ)) x) /\
    (In (form) (snd (nextension_theory Γ Δ n)) x -> In (form) (snd (extension_theory Γ Δ)) x).
Proof.
intros. unfold extension_theory. unfold In. split ; exists n ; auto.
Qed.

(* So the resulting theory is an extension of the initial theory. *)

Lemma extension_theory_extens : forall (Γ Δ: @Ensemble (form)) x,
    (In (form) Γ x -> In (form) (fst (extension_theory Γ Δ)) x) /\
    (In (form) Δ x -> In (form) (snd (extension_theory Γ Δ)) x).
Proof.
intros. unfold extension_theory. unfold In. split ; exists 0 ; auto.
Qed.





(* Existence of unused variables *)

Lemma exist_unused_S_exists_First_unused : forall X n,
  (unused_S n X) ->
  (exists n, First_unused n X).
Proof.
intro X. unfold First_unused.
pose (strong_induction (fun z => unused_S z X -> exists m : nat, unused_S m X /\ (forall k : nat, unused_S k X -> m <= k))).
apply e. clear e. intros.
destruct (classic (exists m : nat, unused_S m X /\ m < n)).
- destruct H1. destruct H1. apply (H _ H2) ; auto.
- exists n. split ; auto. intros. destruct (Nat.lt_ge_cases k n). exfalso. apply H1. exists k ; split ; auto. auto.
Qed.

Lemma unused_list_disj : forall n l, (forall A, List.In A l -> unused n A) -> unused n (list_disj l).
Proof.
induction l.
- intros. simpl. apply uf_bot.
- intros. simpl. apply uf_bin. apply H. apply in_eq. apply IHl. intros. apply H. apply in_cons ; auto.
Qed.

Lemma unused_list_conj : forall n l, (forall A, List.In A l -> unused n A) -> unused n (list_conj l).
Proof.
induction l.
- intros. simpl. apply uf_top.
- intros. simpl. apply uf_bin. apply H. apply in_eq. apply IHl. intros. apply H. apply in_cons ; auto.
Qed.

Lemma exist_unused_term_exists_First_unused : forall t n,
  (unused_term n t) ->
  (exists n, (unused_term n t) /\ (forall m, unused_term m t -> n <= m)).
Proof.
intro t.
pose (strong_induction (fun z => unused_term z t -> exists n0 : nat, unused_term n0 t /\ (forall m : nat, unused_term m t -> n0 <= m))).
apply e. clear e. intros.
destruct (classic (exists m : nat, unused_term m t /\ m < n)).
- destruct H1. destruct H1. apply (H _ H2) ; auto.
- exists n. split ; auto. intros. destruct (Nat.lt_ge_cases m n). exfalso. apply H1. exists m ; split ; auto. auto.
Qed.

Lemma max_list_infinite_unused : forall l, (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n : nat, m <= n -> unused_term n t)) ->
(exists m : nat, (forall t, List.In t l -> (unused_term m t /\ (forall n : nat, m <= n -> unused_term n t)))).
Proof.
induction l ; intros.
- exists 0. intros. inversion H0.
- assert (J1: List.In a (a :: l)). apply in_eq.
  pose (H _ J1). destruct e. destruct H0.
  assert (J2: (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n : nat, m <= n -> unused_term n t))).
  intros. apply H. apply in_cons. auto. apply IHl in J2. destruct J2. exists (max x x0). intros. inversion H3.
  subst. split ; auto. apply H1 ; lia. intros. apply H1 ; auto. lia. split. apply H2 ; auto. lia. intros. apply H2 ; auto. lia.
Qed.

Lemma term_infinite_unused : forall (t : term), (exists n, (unused_term n t) /\ (forall m, n <= m -> unused_term m t)).
Proof.
intros. induction t.
- destruct x. exists 1. split. apply ut_var. intro. inversion H. intros. apply ut_var. lia. exists (S (S x)). split.
  apply ut_var. lia. intros. apply ut_var. lia.
- pose (VectorDef.to_list v).
  assert (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n, m <= n -> unused_term n t)).
  intros. apply IH.
  apply VectorSpec.to_list_In in H. auto. apply max_list_infinite_unused in H. destruct H. exists x. split.
  apply ut_func. intros.
  apply VectorSpec.to_list_In in H0. pose (H t). destruct a ; auto. intros. apply ut_func. intros.
  apply VectorSpec.to_list_In in H1. pose (H t). destruct a ; auto.
Qed.

Lemma term_unused : forall (t : term), (exists m, unused_term m t /\ (forall n, unused_term n t -> m <= n)).
Proof.
intros. pose (term_infinite_unused t). destruct e. destruct H.
pose (exist_unused_term_exists_First_unused t x H). auto.
Qed.

Lemma form_infinite_unused : forall (A : form), (exists n, (unused n A) /\ forall m, n <= m -> unused m A).
Proof.
intros. induction A.
- exists 0. split. apply uf_bot. intros. apply uf_bot.
- exists 0. split. apply uf_top. intros. apply uf_top.
- unfold First_unused. unfold unused_S. pose (VectorDef.to_list t).
  assert (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n, m <= n -> unused_term n t)).
  intros. apply term_infinite_unused. apply max_list_infinite_unused in H. destruct H. exists x. split.
  apply uf_atom. intros. apply VectorSpec.to_list_In in H0. pose (H t0). destruct a ; auto. intros. apply uf_atom. intros.
  apply VectorSpec.to_list_In in H1. pose (H t0). destruct a ; auto.
- unfold First_unused. unfold unused_S. destruct IHA1. destruct H. destruct IHA2. destruct H1.
  exists (max x0 x). split. apply uf_bin. apply H0 ; lia. apply H2 ; lia. intros.
  apply uf_bin. apply H0 ; lia. apply H2 ; lia.
- destruct IHA. destruct H. exists x. split. apply uf_quant. apply H0. lia. intros.
  apply uf_quant. apply H0. lia.
Qed.

Lemma form_First_unused : forall (A : form), (exists m, First_unused m (fun y : form => In _ (Singleton _ A) y)).
Proof.
intros. pose (form_infinite_unused A). destruct e. destruct H.
assert (unused_S x (fun y : form => y = A)). unfold unused_S. intros.
inversion H1. subst. auto.
pose (exist_unused_S_exists_First_unused (fun y => y = A) x H1). destruct e.
exists x0. split. destruct H2. intro. intros. apply H2. inversion H4. unfold In. auto.
intros. destruct H2. apply H4. intro. intros. apply H3. inversion H5 ; subst. unfold In.
apply In_singleton.
Qed.


Lemma closed_infinite_unused : forall X,
  (closed_S X) ->
  (exists n, (unused_S n X) /\ forall m, n <= m -> unused_S m X).
Proof.
intros. exists 0. split. unfold closed_S in H. intro. intros. apply H. auto.
intros. unfold closed_S in H. intro. intros. apply H. auto.
Qed.

Lemma infinite_unused_finite_superset : forall X,
  (exists n, (unused_S n X) /\ forall m, (n <= m -> unused_S m X)) ->
  (forall l, (exists n, forall m, n <= m -> unused_S m (Union _ X (fun x => List.In x l)))).
Proof.
intros. induction l.
- simpl. assert (X = Union form X (fun _ : form => False)). apply Extensionality_Ensembles.
  split ; intro ; intro. apply Union_introl ; auto. inversion H0 ; auto. inversion H1 ; auto. rewrite <- H0 ; auto.
  destruct H. exists x. destruct H. auto.
- destruct IHl. pose (form_infinite_unused a). destruct e. destruct H1. exists (max x0 x).
  intros. simpl. intro. intros. inversion H4. assert (x <= m). lia. apply H0 in H7. pose (H7 phi). apply u.
  apply Union_introl ; auto. subst. inversion H5. subst. apply H2. lia. assert (x <= m). lia.
  apply H0 in H7. apply (H7 phi). apply Union_intror. unfold In ; auto.
Qed.

Lemma unused_finite_superset : forall X,
  (exists n, (unused_S n X) /\ forall m,(n <= m -> unused_S m X)) ->
  (forall l, (exists n, First_unused n (Union _ X (fun x => List.In x l)))).
Proof.
intros.
pose (infinite_unused_finite_superset X H l). destruct e. assert (x <= x). auto.
pose (H0 x H1). pose (exist_unused_S_exists_First_unused _ _ u). auto.
Qed.

Lemma nextension_infinite_unused : forall n (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (exists k,forall m, k <= m ->
          unused_S m (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y)).
Proof.
induction n ; intros.
- simpl. exists 0. unfold closed_S in H. unfold closed_S in H0. unfold First_unused. unfold closed in H.
  unfold closed in H0. unfold unused_S. intros. inversion H3. apply (H _ H4). apply (H0 _ H4).
- simpl. unfold gen_choice_code. destruct (decoding (S n)).
  * simpl. destruct f ; simpl.
    + assert ((fun y : form =>
       In form (fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/ (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥), snd (nextension_theory Γ Δ n)) -> False) /\ x = ⊥) y \/
       In form (fun x : form => In form (snd (nextension_theory Γ Δ n)) x \/ wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥), snd (nextension_theory Γ Δ n)) /\ x = ⊥) y) =
       Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun x => List.In x (⊥ :: List.nil))).
       apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H2. inversion H3. apply Union_introl.
       unfold In ; auto. destruct H4. apply Union_intror ; subst. unfold In. apply in_eq. inversion H3. apply Union_introl ; unfold In ; auto.
       destruct H4. destruct H5. subst. apply Union_intror ; unfold In ; apply in_eq. inversion H2. subst. inversion H3.
       unfold In. auto. unfold In. auto. subst. inversion H3. subst. unfold In.
       destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥), snd (nextension_theory Γ Δ n)))).
       right. right. auto. left. auto. inversion H4. rewrite H2. clear H2. pose (IHn _ _ H H0 H1).
       assert (exists m : nat, unused_S m (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y) /\ (forall k : nat, m <= k -> unused_S k (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y))).
       destruct e. exists x. split. apply H2 ; auto. auto. apply (infinite_unused_finite_superset _ H2 (⊥ :: List.nil)) ; auto.
    + assert ((fun y : form =>
       In form (fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/ (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊤), snd (nextension_theory Γ Δ n)) -> False) /\ x = ⊤) y \/
       In form (fun x : form => In form (snd (nextension_theory Γ Δ n)) x \/ wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊤), snd (nextension_theory Γ Δ n)) /\ x = ⊤) y) =
       Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun x => List.In x (⊤ :: List.nil))).
       apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H2. inversion H3. apply Union_introl.
       unfold In ; auto. destruct H4. apply Union_intror ; subst. unfold In. apply in_eq. inversion H3. apply Union_introl ; unfold In ; auto.
       destruct H4. destruct H5. subst. apply Union_intror ; unfold In ; apply in_eq. inversion H2. subst. inversion H3.
       unfold In. auto. unfold In. auto. subst. inversion H3. subst. unfold In.
       destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊤), snd (nextension_theory Γ Δ n)))).
       right. right. auto. left. auto. inversion H4. rewrite H2. clear H2. apply infinite_unused_finite_superset.
       pose (IHn _ _ H H0 H1). destruct e. exists x. split ; auto.
    + assert ((fun y : form =>
       In form (fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/ (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t)), snd (nextension_theory Γ Δ n)) -> False) /\ x = atom P t) y \/
       In form (fun x : form => In form (snd (nextension_theory Γ Δ n)) x \/ wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t)), snd (nextension_theory Γ Δ n)) /\ x = atom P t) y) =
       Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun x => List.In x ((atom P t) :: List.nil))).
       apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H2. inversion H3. apply Union_introl.
       unfold In ; auto. destruct H4. apply Union_intror ; subst. unfold In. apply in_eq. inversion H3. apply Union_introl ; unfold In ; auto.
       destruct H4. destruct H5. subst. apply Union_intror ; unfold In ; apply in_eq. inversion H2. subst. inversion H3.
       unfold In. auto. unfold In. auto. subst. inversion H3. subst. unfold In.
       destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t)), snd (nextension_theory Γ Δ n)))).
       right. right. auto. left. auto. inversion H4. rewrite H2. clear H2. apply infinite_unused_finite_superset. pose (IHn _ _ H H0 H1). destruct e. exists x. split ; auto.
    + assert ((fun y : form =>
       In form (fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/ (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2)), snd (nextension_theory Γ Δ n)) -> False) /\ x = bin b f1 f2) y \/
       In form (fun x : form => In form (snd (nextension_theory Γ Δ n)) x \/ wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2)), snd (nextension_theory Γ Δ n)) /\ x = bin b f1 f2) y) =
       Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun x => List.In x ((bin b f1 f2) :: List.nil))).
       apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H2. inversion H3. apply Union_introl.
       unfold In ; auto. destruct H4. apply Union_intror ; subst. unfold In. apply in_eq. inversion H3. apply Union_introl ; unfold In ; auto.
       destruct H4. destruct H5. subst. apply Union_intror ; unfold In ; apply in_eq. inversion H2. subst. inversion H3.
       unfold In. auto. unfold In. auto. subst. inversion H3. subst. unfold In.
       destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2)), snd (nextension_theory Γ Δ n)))).
       right. right. auto. left. auto. inversion H4. rewrite H2. clear H2. apply infinite_unused_finite_superset. pose (IHn _ _ H H0 H1). destruct e. exists x. split ; auto.
    + destruct q.
       -- simpl. pose (IHn _ _ H H0 H1).
          assert (exists k : nat, unused_S k (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y) /\ (forall m : nat, k <= m -> unused_S m (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y))).
          destruct e. exists x ; split ; auto.
          pose (infinite_unused_finite_superset _ H2 (∀ f :: List.nil)).
          destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)))).
       ++ clear e. destruct e0. assert (J0: x <= x). auto. pose (H4 _ J0). apply exist_unused_S_exists_First_unused in u. destruct u.
            assert ((fun y : form =>
            In form (fun x1 : form => In form (fst (nextension_theory Γ Δ n)) x1 \/ (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)) -> False) /\ x1 = ∀ f) y \/
            In form (fun x1 : form =>
            In form (snd (nextension_theory Γ Δ n)) x1 \/
            wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)) /\
            (x1 = ∀ f \/ (exists n0 : nat, First_unused n0 (fun y0 : form => In form (fst (nextension_theory Γ Δ n)) y0 \/ In form (snd (nextension_theory Γ Δ n)) y0 \/ y0 = ∀ f) /\ x1 = f[$n0..]))) y) =
            Union _ (Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun z => List.In z (∀ f :: List.nil))) (fun z => List.In z (f[$x0..] :: List.nil))).
            apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H6. inversion H7. apply Union_introl. apply Union_introl.
            unfold In ; auto. destruct H8. subst. apply Union_introl ; apply Union_intror ; subst. unfold In. apply in_eq. inversion H7. apply Union_introl ; apply Union_introl ; unfold In ; auto.
            destruct H8. destruct H9. subst. apply Union_introl ; apply Union_intror ; unfold In ; apply in_eq. destruct H9. destruct H9. subst.
            apply Union_intror. unfold In. assert (x2 = x0). unfold First_unused in H9. unfold unused_S in H9. destruct H9.
            unfold First_unused in H5. unfold unused_S in H5. destruct H5. assert (x2 <= x0). apply H10 ; auto. intros. apply H5 ; auto.
            inversion H12. apply Union_introl ; unfold In ; auto. destruct H13. apply Union_introl ; unfold In ; auto. subst. apply Union_intror ; unfold In ; apply in_eq.
            assert (x0 <= x2). apply H11 ; auto. intros. apply H9 ; auto. inversion H13. subst. unfold In. inversion H14 ; auto. subst. inversion H14.
            subst. unfold In ; auto. inversion H15. lia.
            rewrite H10. apply in_eq.
            inversion H6. subst. unfold In. inversion H7. subst. inversion H8. auto. auto. subst. inversion H8.
            subst. right. right. repeat split ; auto. inversion H9. subst. inversion H7. subst. unfold In. right. right. repeat split ; auto. right. exists x0.
            split ; auto. unfold First_unused. unfold unused_S. unfold First_unused in H5. unfold unused_S in H5. destruct H5.
            split ; intros ; auto. apply H5. inversion H9. unfold In. apply Union_introl ; unfold In ; auto. destruct H10.
            apply Union_introl ; unfold In ; auto. subst. apply Union_intror. unfold In ; apply in_eq. apply H8 ; auto.
            intros. apply H9. inversion H10. subst. unfold In ; unfold In in H11 ; destruct H11 ; auto. subst. inversion H11 ; subst. unfold In ; auto.
            inversion H12. inversion H8. rewrite H6. clear H6. apply infinite_unused_finite_superset.
            exists x. split ; auto.
       ++ clear e. destruct e0. assert (J0: x <= x). auto. pose (H4 _ J0). apply exist_unused_S_exists_First_unused in u. destruct u.
            assert ((fun y : form =>
            In form (fun x1 : form => In form (fst (nextension_theory Γ Δ n)) x1 \/ (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)) -> False) /\ x1 = ∀ f) y \/
            In form (fun x1 : form =>
            In form (snd (nextension_theory Γ Δ n)) x1 \/
            wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)) /\
            (x1 = ∀ f \/ (exists n0 : nat, First_unused n0 (fun y0 : form => In form (fst (nextension_theory Γ Δ n)) y0 \/ In form (snd (nextension_theory Γ Δ n)) y0 \/ y0 = ∀ f) /\ x1 = f[$n0..]))) y) =
            Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun z => List.In z (∀ f :: List.nil))).
            apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H6. inversion H7. apply Union_introl. unfold In ; auto.
            destruct H8. subst. apply Union_intror ; subst. unfold In. apply in_eq. inversion H7. apply Union_introl ; unfold In ; auto.
            destruct H8. destruct H9. subst. apply Union_intror ; unfold In ; apply in_eq. exfalso ; auto.
            inversion H6. subst. unfold In. inversion H7 ; auto. subst. inversion H7 ; subst. unfold In. left. right ; auto. inversion H8.
            rewrite H6. clear H6. exists x ; intros. apply H4. auto.
       -- simpl. pose (IHn _ _ H H0 H1).
          assert (exists k : nat, unused_S k (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y) /\ (forall m : nat, k <= m -> unused_S m (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y))).
          destruct e. exists x ; split ; auto.
          pose (infinite_unused_finite_superset _ H2 (∃ f :: List.nil)).
          destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)))).
       ++ clear e. destruct e0. assert (J0: x <= x). auto. pose (H4 _ J0). apply exist_unused_S_exists_First_unused in u. destruct u.
            assert ((fun y : form => In form (fun x1 : form => In form (fst (nextension_theory Γ Δ n)) x1 \/
            (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)) -> False) /\
            (x1 = ∃ f \/ (exists n0 : nat, First_unused n0 (fun y0 : form => In form (fst (nextension_theory Γ Δ n)) y0 \/ In form (snd (nextension_theory Γ Δ n)) y0 \/ y0 = ∃ f) /\ x1 = f[$n0..]))) y \/
            In form (fun x1 : form => In form (snd (nextension_theory Γ Δ n)) x1 \/ wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)) /\ x1 = ∃ f) y) =
            Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun z => List.In z (∃ f :: List.nil))).
            apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H6. inversion H7. apply Union_introl. unfold In ; auto.
            destruct H8. exfalso ; auto. inversion H7. apply Union_introl ; unfold In ; auto. destruct H8. subst. apply Union_intror ; unfold In ; apply in_eq.
            inversion H6. subst. unfold In. inversion H7 ; auto. subst. inversion H7 ; subst. unfold In. right. auto. inversion H8.
            rewrite H6. clear H6. exists x ; intros. apply H4. auto.
       ++ clear e. destruct e0. assert (J0: x <= x). auto. pose (H4 _ J0). apply exist_unused_S_exists_First_unused in u. destruct u.
            assert ((fun y : form => In form (fun x1 : form => In form (fst (nextension_theory Γ Δ n)) x1 \/
            (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)) -> False) /\
            (x1 = ∃ f \/ (exists n0 : nat, First_unused n0 (fun y0 : form => In form (fst (nextension_theory Γ Δ n)) y0 \/ In form (snd (nextension_theory Γ Δ n)) y0 \/ y0 = ∃ f) /\ x1 = f[$n0..]))) y \/
            In form (fun x1 : form => In form (snd (nextension_theory Γ Δ n)) x1 \/ wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)) /\ x1 = ∃ f) y) =
            Union _ (Union _ (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In _ (snd (nextension_theory Γ Δ n)) y) (fun z => List.In z (∃ f :: List.nil))) (fun z => List.In z (f[$x0..] :: List.nil))).
            apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H6. inversion H7. apply Union_introl. apply Union_introl.
            unfold In ; auto. destruct H8. destruct H9. subst. apply Union_introl ; apply Union_intror ; subst. unfold In. apply in_eq. destruct H9. destruct H9.
            subst. apply Union_intror ; unfold In ; auto. assert (x2 = x0). unfold First_unused in H9. unfold unused_S in H9. destruct H9.
            unfold First_unused in H5. unfold unused_S in H5. destruct H5. assert (x2 <= x0). apply H10 ; auto. intros. apply H5 ; auto.
            inversion H12. apply Union_introl ; unfold In ; auto. destruct H13. apply Union_introl ; unfold In ; auto. subst. apply Union_intror ; unfold In ; apply in_eq.
            assert (x0 <= x2). apply H11 ; auto. intros. apply H9 ; auto. inversion H13. subst. unfold In. inversion H14 ; auto. subst. inversion H14.
            subst. unfold In ; auto. inversion H15. lia. rewrite H10. apply in_eq.
            inversion H7. apply Union_introl ; unfold In ; auto. apply Union_introl ; unfold In ; auto. destruct H8. exfalso ; auto.
            inversion H6. subst. unfold In. inversion H7. subst. inversion H8 ; auto. subst. inversion H8.
            subst. left. right. repeat split ; auto. inversion H9. subst. inversion H7. subst. unfold In. left. right. repeat split ; auto. right. exists x0.
            split ; auto. unfold First_unused. unfold unused_S. unfold First_unused in H5. unfold unused_S in H5. destruct H5.
            split ; intros ; auto. apply H5. inversion H9. unfold In. apply Union_introl ; unfold In ; auto. destruct H10.
            apply Union_introl ; unfold In ; auto. subst. apply Union_intror. unfold In ; apply in_eq. apply H8 ; auto.
            intros. apply H9. inversion H10. subst. unfold In ; unfold In in H11 ; destruct H11 ; auto. subst. inversion H11 ; subst. unfold In ; auto.
            inversion H12. inversion H8. rewrite H6. clear H6. apply infinite_unused_finite_superset.
            exists x. split ; auto.
  * apply IHn ; auto.
Qed.

Lemma nextension_unused : forall n (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (exists m, First_unused m (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y)).
Proof.
intros. pose (nextension_infinite_unused n _ _ H H0 H1). destruct e. assert (x <= x). auto.
pose (H2 x H3). apply exist_unused_S_exists_First_unused in u. auto.
Qed.


(* The extension preserves provability. *)

Lemma der_nextension_theory_mextension_theory_le : forall n m (Γ Δ: @Ensemble (form)) A,
  (FOwBIH_rules (fst (nextension_theory Γ Δ n), A)) -> (le n m) ->
    (FOwBIH_rules  (fst (nextension_theory Γ Δ m), A)).
Proof.
intros.
pose (FOwBIH_monot (fst (nextension_theory Γ Δ n), A) H (fst (nextension_theory Γ Δ m))).
simpl in f. apply f. intro. intros. apply nextension_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma wpair_der_nextension_theory_mextension_theory_le : forall n m (Γ Δ: @Ensemble (form)) A,
  (wpair_der (fst (nextension_theory Γ Δ n), Singleton _ A)) -> (le n m) ->
    (wpair_der  (fst (nextension_theory Γ Δ m), Singleton _ A)).
Proof.
intros. destruct H. destruct H. destruct H1. simpl in H1. simpl in H2.
destruct x.
- simpl in H2. pose (FOwBIH_monot (fst (nextension_theory Γ Δ n), ⊥) H2 (fst (nextension_theory Γ Δ m))).
  simpl in f. exists []. repeat split ; auto. simpl. apply f. intro. intros.
  apply nextension_theory_extens_le with (n:=n) ; auto.
- simpl in H2. simpl in H1. destruct x. simpl in H2. apply absorp_Or1 in H2.
  assert (List.In f (f :: List.nil)). apply in_eq. apply H1 in H3. inversion H3. subst.
  exists [f]. repeat split ; auto. simpl.
  apply MP with (ps:=[(fst (nextension_theory Γ Δ m), f --> (f ∨ ⊥));(fst (nextension_theory Γ Δ m), f)]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Ax. apply AxRule_I.
  apply RA2_I. exists f. exists ⊥ ; auto. inversion H5 ; subst. 2: inversion H6.
  pose (FOwBIH_monot (fst (nextension_theory Γ Δ n), f) H2 (fst (nextension_theory Γ Δ m))).
  apply f0. simpl. intro. intros. apply nextension_theory_extens_le with (n:=n) ; auto.
  exfalso. inversion H. apply H5. subst. assert (J1: List.In f (f :: f0 :: x)). apply in_eq.
  apply H1 in J1. inversion J1 ; subst. assert (J2: List.In f0 (f :: f0 :: x)). apply in_cons.
  apply in_eq. apply H1 in J2. inversion J2 ; subst. apply in_eq.
Qed.

(* Having Cut is quite convenient. *)

Lemma Cut : forall (Γ Δ: @Ensemble (form)) A,
        wpair_der (Union _ Γ (Singleton _ A), Δ)  ->
        wpair_der (Γ, Union _ Δ (Singleton _ A))  ->
        wpair_der (Γ, Δ).
Proof.
intros.
destruct H. destruct H0. destruct H. destruct H1. destruct H0. destruct H3.
simpl in H2. simpl in H4. simpl in H3. simpl in H1.
exists ((remove eq_dec_form A x0) ++ (remove_list (remove eq_dec_form A x0) x)). repeat split.
apply add_remove_list_preserve_NoDup ; auto.
apply NoDup_remove ; auto. simpl. intros. apply in_app_or in H5. destruct H5.
apply in_remove in H5. destruct H5. apply H3 in H5. inversion H5 ; auto. subst.
inversion H7 ; subst ; exfalso ; auto. apply In_remove_list_In_list in H5.
apply H1 in H5. auto. simpl.
apply FOwBIH_Deduction_Theorem with (A0:=A) (B:= list_disj x) (Γ0:=Γ) in H2 ; auto.
pose (Id_list_disj_remove Γ (remove eq_dec_form A x0) x).
pose (list_disj_remove_form _ _ A H4).
assert (J1: FOwBIH_rules (Γ, list_disj (remove eq_dec_form A x0) --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))).
apply Id_list_disj.
apply MP with (ps:=[(Γ, (A ∨ list_disj (remove eq_dec_form A x0)) --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x)));
(Γ, A ∨ list_disj (remove eq_dec_form A x0))]). 2: apply MPRule_I.
intros. inversion H5. subst. 2: inversion H6 ; subst ; auto. 2: inversion H7.
apply MP with (ps:=[(Γ, (list_disj (remove eq_dec_form A x0) --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))) --> ((A ∨ list_disj (remove eq_dec_form A x0)) --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))));
(Γ, (list_disj (remove eq_dec_form A x0) --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))))]). 2: apply MPRule_I.
intros. inversion H6. subst. 2: inversion H7 ; subst ; auto. 2: inversion H8.
apply MP with (ps:=[(Γ, (A --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))) --> (list_disj (remove eq_dec_form A x0) --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))) --> ((A ∨ list_disj (remove eq_dec_form A x0)) --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))));
(Γ, (A --> (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))))]). 2: apply MPRule_I.
intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA4_I. exists A.
exists (list_disj (remove eq_dec_form A x0)).
exists ((list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))). auto. clear H7. clear H6.
inversion H8 ; subst. 2: inversion H6.
apply MP with (ps:=[(Γ, (list_disj x --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x)) --> (A --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x)));
(Γ, list_disj x --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply MP with (ps:=[(Γ, (A --> list_disj x) --> (list_disj x --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x)) --> (A --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x)));
(Γ,A --> list_disj x)]).
2: apply MPRule_I. intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA1_I.
exists A. exists (list_disj x). exists (list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x)).
auto. inversion H9. subst. 2: inversion H10. auto. inversion H7. subst. 2: inversion H9.
auto.
Qed.

(* The extension is unprovable. *)

Lemma Under_pair_add_left_or_right : forall (Γ Δ: @Ensemble (form)) A, (wpair_der (Γ, Δ) -> False) ->
  ((wpair_der (Union _ Γ (Singleton _ A), Δ)  -> False) \/  (wpair_der (Γ, Union _ Δ (Singleton _ A))  -> False)).
Proof.
intros.
destruct (classic (wpair_der (Union _ Γ (Singleton _ A), Δ))) ; auto.
destruct (classic (wpair_der (Γ, Union _ Δ (Singleton _ A)))) ; auto.
exfalso. apply H. apply (Cut _ _ _ H0 H1).
Qed.

Lemma Under_nextension_theory : forall n (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (wpair_der (nextension_theory Γ Δ n) -> False).
Proof.
induction n ; intros Γ Δ ClΓ ClΔ ; intros.
- simpl in H0. auto.
- simpl in H0. apply IHn with (Γ:=Γ) (Δ:=Δ) ; auto. unfold gen_choice_code in H0.
  remember (decoding (S n)) as code. destruct code.
  + destruct f ; auto ; destruct H0 ; destruct H0 ; destruct H1.
    (* Then in each case check if either adding to the left or the right preserve provability. *)
    * simpl in H2. assert (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥), snd (nextension_theory Γ Δ n))).
      exists []. repeat split ; auto. apply NoDup_nil. intros. inversion H3. simpl. apply Id. apply IdRule_I. apply Union_intror.
      apply In_singleton.
      assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
     (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥), snd (nextension_theory Γ Δ n)) -> False) /\ x = ⊥) =
     (fst (nextension_theory Γ Δ n))).
     apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5. exfalso ; auto. unfold In.
     left ; auto. rewrite H4 in H2. clear H4. exists (remove eq_dec_form ⊥ x). repeat split ; auto. apply NoDup_remove ; auto.
     intros. assert (List.In A x). apply in_remove in H4. destruct H4. auto.
     apply H1 in H5. inversion H5 ; auto. destruct H6 ; destruct H7 ; subst. exfalso. apply remove_not_in_anymore in H4. auto.
     apply der_list_disj_bot. auto.
    * simpl in H2. 
      assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
      (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊤), snd (nextension_theory Γ Δ n)) -> False) /\ x = ⊤) =
      Union _  (fst (nextension_theory Γ Δ n)) (Singleton _ ⊤)).
      apply Extensionality_Ensembles. split ; intro ; intro. inversion H3 ; auto. apply Union_introl.
      auto. destruct H4. subst. apply Union_intror. apply In_singleton. unfold In. inversion H3 ; auto. subst.
      right. inversion H4. split ; auto. subst. intro. apply (IHn _ _ ClΓ ClΔ H). destruct H5. destruct H5. destruct H6.
      exists x0. repeat split ; auto. simpl in H7.
      apply MP with (ps:=[(fst (nextension_theory Γ Δ n), ⊤ --> list_disj x0);
      (fst (nextension_theory Γ Δ n), ⊤)]). 2: apply MPRule_I. intros. inversion H8. subst.
      apply (FOwBIH_Deduction_Theorem _ H7) ; auto. inversion H9. subst. apply wTop. inversion H10.
      rewrite H3 in H2. clear H3. exists x. repeat split ; auto. intros. apply H1 in H3. simpl in H3. inversion H3 ; auto. destruct H4 ; subst.
      exfalso. apply (IHn _ _ ClΓ ClΔ H). destruct H4. destruct H4. destruct H5.
      exists x0. repeat split ; auto. simpl in H6.
      apply MP with (ps:=[(fst (nextension_theory Γ Δ n), ⊤ --> list_disj x0);
      (fst (nextension_theory Γ Δ n), ⊤)]). 2: apply MPRule_I. intros. inversion H7. subst.
      apply (FOwBIH_Deduction_Theorem _ H6) ; auto. inversion H8. subst. apply wTop. inversion H9.
      apply MP with (ps:=[(fst (nextension_theory Γ Δ n), ⊤ --> list_disj x);
      (fst (nextension_theory Γ Δ n), ⊤)]). 2: apply MPRule_I. intros. inversion H3. subst.
      apply (FOwBIH_Deduction_Theorem _ H2) ; auto. inversion H4. subst. apply wTop. inversion H5.
    * simpl in H2. simpl in H1. destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t)), snd (nextension_theory Γ Δ n)))).
      { assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
        (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t)), snd (nextension_theory Γ Δ n)) -> False) /\
        x = atom P t) = (fst (nextension_theory Γ Δ n))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
        rewrite H4 in H2. clear H4.
        destruct (classic (wpair_der (fst (nextension_theory Γ Δ n), Union form (snd (nextension_theory Γ Δ n)) (Singleton form (atom P t))))).
        - apply (Cut _ _ _ H3 H4).
        - destruct (In_dec x (atom P t)).
          + exfalso. apply H4. exists x. repeat split ; auto. intros ; auto. apply H1 in H5. simpl.
             inversion H5 ; auto. apply Union_introl ; auto. destruct H6 ; destruct H7 ; subst. apply Union_intror.
             apply In_singleton.
          + exists x. repeat split ; auto. intros. pose (H1 _ H5). inversion i ; auto. destruct H6 ; destruct H7 ; subst. exfalso ; auto. }
      { assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
        (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t)), snd (nextension_theory Γ Δ n)) -> False) /\
        x = atom P t) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (atom P t))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. apply Union_introl ; auto.
        destruct H5. subst. apply Union_intror. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
        subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. simpl.
        apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
    * simpl in H2. simpl in H1.
      destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2)), snd (nextension_theory Γ Δ n)))).
      { assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
        (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2)), snd (nextension_theory Γ Δ n)) -> False) /\
        x = (bin b f1 f2)) = (fst (nextension_theory Γ Δ n))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
        rewrite H4 in H2. clear H4.
        destruct (classic (wpair_der (fst (nextension_theory Γ Δ n), Union form (snd (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))))).
        - apply (Cut _ _ _ H3 H4).
        - destruct (In_dec x (bin b f1 f2)).
          + exfalso. apply H4. exists x. repeat split ; auto. intros ; auto. apply H1 in H5. simpl.
             inversion H5 ; auto. apply Union_introl ; auto. destruct H6 ; destruct H7 ; subst. apply Union_intror.
             apply In_singleton.
          + exists x. repeat split ; auto. intros. pose (H1 _ H5). inversion i ; auto. destruct H6 ; destruct H7 ; subst. exfalso ; auto. }
      { assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
        (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2)), snd (nextension_theory Γ Δ n)) -> False) /\
        x = (bin b f1 f2)) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (bin b f1 f2))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. apply Union_introl ; auto.
        destruct H5. subst. apply Union_intror. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
        subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. simpl.
        apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
    * destruct q.
      -- simpl in H2. simpl in H1.
          destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)))).
          { assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
            (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)) -> False) /\
            x = ∀ f) = (fst (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
            rewrite H4 in H2. clear H4. apply (Cut _ _ _ H3). destruct H3. destruct H3. simpl in H4. destruct H4. destruct (In_dec x (∀ f)).
            - destruct (classic (exists n0 : nat, First_unused n0
              (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y \/ y = ∀ f) /\
              List.In f[$n0..] x)).
              + destruct H6. destruct H6. exists (remove eq_dec_form f[$x1..] x). repeat split ; auto. apply remove_preserv_NoDup ; auto.
                 intros. apply in_remove in H8. destruct H8. apply H1 in H8. unfold In. simpl. inversion H8. apply Union_introl ; auto.
                 destruct H10. destruct H11. subst. apply Union_intror ; apply In_singleton. exfalso. destruct H11. destruct H11. subst.
                 apply H9. assert (x2 = x1). unfold First_unused in H11. unfold unused_S in H11. destruct H11.
                 unfold First_unused in H6. unfold unused_S in H6. destruct H6. assert (x2 <= x1).  apply H12 ; auto.
                 assert (x1 <= x2).  apply H13 ; auto. lia. subst. auto. simpl.
                 pose (remove_disj x f[$x1..] (fst (nextension_theory Γ Δ n))).
                 assert (FOwBIH_rules (fst (nextension_theory Γ Δ n), f[$x1..] ∨ list_disj (remove eq_dec_form f[$x1..] x))).
                 apply MP with (ps:=[(fst (nextension_theory Γ Δ n), list_disj x --> f[$x1..] ∨ list_disj (remove eq_dec_form f[$x1..] x));
                 (fst (nextension_theory Γ Δ n), list_disj x)]). 2: apply MPRule_I. intros. inversion H8. subst. auto. inversion H9.
                 subst. auto. inversion H10. apply comm_Or in H8. pose (FOwBIH_finite _ H8). destruct e. destruct H9.
                 destruct p. destruct e. pose (finite_context_list_conj _ _ f1 x3 H9). simpl in f2.
                 assert (J1: FOwBIH_rules (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ list_disj (f[$x1..] :: List.nil))).
                 simpl. apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..]) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..])]). 2: apply MPRule_I.
                 intros. inversion H10. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (f[$x1..] --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..]) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))));
                 (Singleton form (list_conj x3), f[$x1..] --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)))]). 2: apply MPRule_I.
                 intros. inversion H11. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))) --> (f[$x1..] --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..]) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)))]). 2: apply MPRule_I.
                 intros. inversion H12. subst. apply Ax. apply AxRule_I. apply RA4_I. exists (list_disj (remove eq_dec_form f[$x1..] x)).
                 exists (f[$x1..]). exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)). auto. inversion H13. subst. 2: inversion H14.
                 apply Ax. apply AxRule_I. apply RA2_I. exists (list_disj (remove eq_dec_form f[$x1..] x)). exists (f[$x1..] ∨ ⊥). auto.
                 inversion H12. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), ((f[$x1..] ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)) --> (f[$x1..] --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)));
                 (Singleton form (list_conj x3), (f[$x1..] ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))]).
                 2: apply MPRule_I. intros. inversion H13. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (f[$x1..] --> (f[$x1..] ∨ ⊥)) --> ((f[$x1..] ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)) --> (f[$x1..] --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)));
                 (Singleton form (list_conj x3), f[$x1..] --> (f[$x1..] ∨ ⊥))]).
                 2: apply MPRule_I. intros. inversion H14. subst. apply Ax. apply AxRule_I. apply RA1_I.
                 exists f[$x1..]. exists (f[$x1..] ∨ ⊥). exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)). auto.
                 inversion H15. 2: inversion H16. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (f[$x1..]). exists ⊥. auto.
                 inversion H14. 2: inversion H15. subst. apply Ax. apply AxRule_I. apply RA3_I. exists (list_disj (remove eq_dec_form f[$x1..] x)).
                 exists (f[$x1..] ∨ ⊥). auto. inversion H13. inversion H11. subst. 2: inversion H12. auto.
                 pose (FOwBIH_Dual_Deduction_Theorem (list_conj x3) (list_disj (remove eq_dec_form f[$x1..] x)) (f[$x1..] :: List.nil) J1).
                 simpl in f3. apply absorp_Or1 in f3.
                 assert (J2: unused_S x1 (fun x0 : form => In form (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x))) x0 \/ x0 = ∀ f)).
                 unfold unused_S. intros. inversion H10. inversion H11. subst. apply uf_bin. apply unused_list_conj. intros.
                 apply H9 in H12. apply i0 in H12. simpl in H12. unfold First_unused in H6. unfold unused_S in H6.
                 destruct H6. apply H6. unfold In ; auto. apply unused_list_disj. intros. unfold First_unused in H6. unfold unused_S in H6.
                 destruct H6. apply H6. unfold In. apply in_remove in H12. destruct H12. apply H1 in H12. inversion H12 ; auto.
                 destruct H15. destruct H16 ; subst; auto. destruct H16. exfalso. destruct H16. subst. apply H14.
                 unfold First_unused in H16. unfold unused_S in H16. destruct H16. assert (x4 = x1). assert (x4 <= x1).
                 apply H17 ; auto. assert (x1 <= x4). apply H13 ; auto. lia. subst. auto. subst. unfold First_unused in H6. unfold unused_S in H6.
                 destruct H6. apply H6. unfold In ; auto.
                 pose (Gen_unused x1 (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x))) f J2 f3).
                 assert (J3: FOwBIH_rules (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x)), (∀ f) ∨ ⊥)).
                 apply MP with (ps:=[(Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x)), (∀ f) --> ((∀ f) ∨ ⊥));
                 (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x)), (∀ f))]). 2: apply MPRule_I.
                 intros. inversion H10. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (∀ f). exists ⊥ ; auto.
                 inversion H11. subst. 2: inversion H12. auto.
                 pose (FOwBIH_Dual_Detachment_Theorem (list_conj x3) (list_disj (remove eq_dec_form f[$x1..] x)) (∀ f :: List.nil) J3).
                 simpl in f5.
                 assert (FOwBIH_rules (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))).
                 apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥)) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥))]). 2: apply MPRule_I.
                 intros. inversion H10. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (((∀ f) ∨ ⊥) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥)) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))));
                 (Singleton form (list_conj x3), ((∀ f) ∨ ⊥) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)))]). 2: apply MPRule_I.
                 intros. inversion H11. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))) --> (((∀ f) ∨ ⊥) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥)) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)))]). 2: apply MPRule_I.
                 intros. inversion H12. subst. apply Ax. apply AxRule_I. apply RA4_I. exists (list_disj (remove eq_dec_form f[$x1..] x)).
                 exists ((∀ f) ∨ ⊥). exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)). auto. inversion H13. subst. 2: inversion H14.
                 apply Ax. apply AxRule_I. apply RA2_I. exists (list_disj (remove eq_dec_form f[$x1..] x)). exists (∀ f). auto.
                 inversion H12. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (⊥ --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) --> (((∀ f) ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)));
                 (Singleton form (list_conj x3), ⊥ --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))]).
                 2: apply MPRule_I. intros. inversion H13. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), ((∀ f) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) --> (⊥ --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) --> ((∀ f) ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f));
                 (Singleton form (list_conj x3), ((∀ f) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)))]).
                 2: apply MPRule_I. intros. inversion H14. subst. apply Ax. apply AxRule_I. apply RA4_I.
                 exists (∀ f). exists ⊥. exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)). auto.
                 inversion H15. 2: inversion H16. subst. apply Ax. apply AxRule_I. apply RA3_I. exists (list_disj (remove eq_dec_form f[$x1..] x)). exists (∀ f). auto.
                 inversion H14. 2: inversion H15. subst. apply wEFQ. inversion H13. inversion H11. subst. 2: inversion H12. auto.
                 pose (list_conj_finite_context x3 x2 (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) H9 H10).
                 apply FOwBIH_monot with (Γ1:=fst (nextension_theory Γ Δ n)) in f6. simpl in f6.
                 apply comm_Or in f6. apply list_disj_In in f6. auto. apply in_in_remove ; auto. intro.
                 assert (size (∀ f) = size (f[$x1..])). rewrite H11 ; auto. simpl in H12. rewrite subst_size in H12.
                 lia. simpl. intro. intros. apply i0 in H11. auto.
              + exists x. repeat split ; auto. intros. pose (H1 _ H7). unfold In. simpl. inversion i0. apply Union_introl ; auto.
                 destruct H8. destruct H9. subst. apply Union_intror ; apply In_singleton. exfalso. destruct H9. destruct H9. subst.
                 apply H6. exists x1. split ; auto.
            - destruct (classic (exists n0 : nat, First_unused n0
              (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y \/ y = ∀ f) /\
              List.In f[$n0..] x)).
              + destruct H6. destruct H6. exists ((∀ f) :: remove eq_dec_form f[$x1..] x). repeat split ; auto. apply NoDup_cons.
                 intro. apply f0. apply in_remove in H8. destruct H8 ; auto. apply remove_preserv_NoDup ; auto.
                 intros. inversion H8. subst. apply Union_intror ; apply In_singleton.
                 apply in_remove in H9. destruct H9. apply H1 in H9. unfold In. simpl. inversion H9. apply Union_introl ; auto.
                 destruct H11. destruct H12. subst. apply Union_intror ; apply In_singleton. exfalso. destruct H12. destruct H12. subst.
                 apply H10. assert (x2 = x1). unfold First_unused in H12. unfold unused_S in H12. destruct H12.
                 unfold First_unused in H6. unfold unused_S in H6. destruct H6. assert (x2 <= x1). apply H13 ; auto.
                 assert (x1 <= x2).  apply H14 ; auto. lia. subst. auto. simpl.
                 pose (remove_disj x f[$x1..] (fst (nextension_theory Γ Δ n))).
                 assert (FOwBIH_rules (fst (nextension_theory Γ Δ n), f[$x1..] ∨ list_disj (remove eq_dec_form f[$x1..] x))).
                 apply MP with (ps:=[(fst (nextension_theory Γ Δ n), list_disj x --> f[$x1..] ∨ list_disj (remove eq_dec_form f[$x1..] x));
                 (fst (nextension_theory Γ Δ n), list_disj x)]). 2: apply MPRule_I. intros. inversion H8. subst. auto. inversion H9.
                 subst. auto. inversion H10. apply comm_Or in H8. pose (FOwBIH_finite _ H8). destruct e. destruct H9.
                 destruct p. destruct e. pose (finite_context_list_conj _ _ f2 x3 H9). apply comm_Or. simpl in f3.
                 assert (J1: FOwBIH_rules (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ list_disj (f[$x1..] :: List.nil))).
                 simpl. apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..]) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..])]). 2: apply MPRule_I.
                 intros. inversion H10. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (f[$x1..] --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..]) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))));
                 (Singleton form (list_conj x3), f[$x1..] --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)))]). 2: apply MPRule_I.
                 intros. inversion H11. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))) --> (f[$x1..] --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ f[$x1..]) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)))]). 2: apply MPRule_I.
                 intros. inversion H12. subst. apply Ax. apply AxRule_I. apply RA4_I. exists (list_disj (remove eq_dec_form f[$x1..] x)).
                 exists (f[$x1..]). exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)). auto. inversion H13. subst. 2: inversion H14.
                 apply Ax. apply AxRule_I. apply RA2_I. exists (list_disj (remove eq_dec_form f[$x1..] x)). exists (f[$x1..] ∨ ⊥). auto.
                 inversion H12. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), ((f[$x1..] ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)) --> (f[$x1..] --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)));
                 (Singleton form (list_conj x3), (f[$x1..] ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥))]).
                 2: apply MPRule_I. intros. inversion H13. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (f[$x1..] --> (f[$x1..] ∨ ⊥)) --> ((f[$x1..] ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)) --> (f[$x1..] --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)));
                 (Singleton form (list_conj x3), f[$x1..] --> (f[$x1..] ∨ ⊥))]).
                 2: apply MPRule_I. intros. inversion H14. subst. apply Ax. apply AxRule_I. apply RA1_I.
                 exists f[$x1..]. exists (f[$x1..] ∨ ⊥). exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (f[$x1..] ∨ ⊥)). auto.
                 inversion H15. 2: inversion H16. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (f[$x1..]). exists ⊥. auto.
                 inversion H14. 2: inversion H15. subst. apply Ax. apply AxRule_I. apply RA3_I. exists (list_disj (remove eq_dec_form f[$x1..] x)).
                 exists (f[$x1..] ∨ ⊥). auto. inversion H13. inversion H11. subst. 2: inversion H12. auto.
                 pose (FOwBIH_Dual_Deduction_Theorem (list_conj x3) (list_disj (remove eq_dec_form f[$x1..] x)) (f[$x1..] :: List.nil) J1).
                 simpl f4. apply absorp_Or1 in f4.
                 assert (J2: unused_S x1 (fun x0 : form => In form (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x))) x0 \/ x0 = ∀ f)).
                 unfold unused_S. intros. inversion H10. inversion H11. subst. apply uf_bin. apply unused_list_conj. intros.
                 apply H9 in H12. apply i in H12. simpl in H12. unfold First_unused in H6. unfold unused_S in H6.
                 destruct H6. apply H6. unfold In ; auto. apply unused_list_disj. intros. unfold First_unused in H6. unfold unused_S in H6.
                 destruct H6. apply H6. unfold In. apply in_remove in H12. destruct H12. apply H1 in H12. inversion H12 ; auto.
                 destruct H15. destruct H16 ; subst; auto. destruct H16. exfalso. destruct H16. subst. apply H14.
                 unfold First_unused in H16. unfold unused_S in H16. destruct H16. assert (x4 = x1). assert (x4 <= x1).
                 apply H17 ; auto. assert (x1 <= x4). apply H13 ; auto. lia. subst. auto. subst. unfold First_unused in H6. unfold unused_S in H6.
                 destruct H6. apply H6. unfold In ; auto.
                 pose (Gen_unused x1 (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x))) f J2 f4).
                 assert (J3: FOwBIH_rules (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x)), (∀ f) ∨ ⊥)).
                 apply MP with (ps:=[(Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x)), (∀ f) --> ((∀ f) ∨ ⊥));
                 (Singleton form (list_conj x3 --< list_disj (remove eq_dec_form f[$x1..] x)), (∀ f))]). 2: apply MPRule_I.
                 intros. inversion H10. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (∀ f). exists ⊥ ; auto.
                 inversion H11. subst. 2: inversion H12. auto.
                 pose (FOwBIH_Dual_Detachment_Theorem (list_conj x3) (list_disj (remove eq_dec_form f[$x1..] x)) (∀ f :: List.nil) J3).
                 simpl in f4.
                 assert (FOwBIH_rules (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))).
                 apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥)) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥))]). 2: apply MPRule_I.
                 intros. inversion H10. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (((∀ f) ∨ ⊥) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥)) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))));
                 (Singleton form (list_conj x3), ((∀ f) ∨ ⊥) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)))]). 2: apply MPRule_I.
                 intros. inversion H11. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))) --> (((∀ f) ∨ ⊥) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))) --> ((list_disj (remove eq_dec_form f[$x1..] x) ∨ ((∀ f) ∨ ⊥)) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))));
                 (Singleton form (list_conj x3), list_disj (remove eq_dec_form f[$x1..] x) --> (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)))]). 2: apply MPRule_I.
                 intros. inversion H12. subst. apply Ax. apply AxRule_I. apply RA4_I. exists (list_disj (remove eq_dec_form f[$x1..] x)).
                 exists ((∀ f) ∨ ⊥). exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)). auto. inversion H13. subst. 2: inversion H14.
                 apply Ax. apply AxRule_I. apply RA2_I. exists (list_disj (remove eq_dec_form f[$x1..] x)). exists (∀ f). auto.
                 inversion H12. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), (⊥ --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) --> (((∀ f) ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)));
                 (Singleton form (list_conj x3), ⊥ --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f))]).
                 2: apply MPRule_I. intros. inversion H13. subst.
                 apply MP with (ps:=[(Singleton form (list_conj x3), ((∀ f) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) --> (⊥ --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) --> ((∀ f) ∨ ⊥) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f));
                 (Singleton form (list_conj x3), ((∀ f) --> list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)))]).
                 2: apply MPRule_I. intros. inversion H14. subst. apply Ax. apply AxRule_I. apply RA4_I.
                 exists (∀ f). exists ⊥. exists (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)). auto.
                 inversion H15. 2: inversion H16. subst. apply Ax. apply AxRule_I. apply RA3_I. exists (list_disj (remove eq_dec_form f[$x1..] x)). exists (∀ f). auto.
                 inversion H14. 2: inversion H15. subst. apply wEFQ. inversion H13. inversion H11. subst. 2: inversion H12. auto.
                 pose (list_conj_finite_context x3 x2 (list_disj (remove eq_dec_form f[$x1..] x) ∨ (∀ f)) H9 H10).
                 apply FOwBIH_monot with (Γ1:=fst (nextension_theory Γ Δ n)) in f7. simpl in f7. auto.
                 intro. simpl. intros. apply i in H11. auto.
              + exists x. repeat split ; auto. intros. pose (H1 _ H7). unfold In. simpl. inversion i. apply Union_introl ; auto.
                 destruct H8. destruct H9. subst. apply Union_intror ; apply In_singleton. exfalso. destruct H9. destruct H9. subst.
                 apply H6. exists x1. split ; auto. }
          { assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
            (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f)), snd (nextension_theory Γ Δ n)) -> False) /\
            x = (∀ f)) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (∀ f))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. apply Union_introl ; auto.
            destruct H5. subst. apply Union_intror. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
            subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. simpl.
            apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
      -- simpl in H2. simpl in H1.
          destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)))).
          { assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
            (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)) -> False) /\
            (x = ∃ f \/ (exists n0 : nat, First_unused n0
            (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y \/ y = ∃ f) /\
            x = f[$n0..]))) = (fst (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
            rewrite H4 in H2. clear H4. apply (Cut _ _ _ H3). destruct H3. destruct H3. simpl in H4. destruct H4.
            exists (x0 ++ remove_list x0 x). repeat split. apply add_remove_list_preserve_NoDup ; auto. intros.
            simpl. apply in_app_or in H6. destruct H6. apply Union_introl ; apply H4 ; auto. apply In_remove_list_In_list in H6.
            apply H1 in H6. inversion H6. apply Union_introl ; auto. destruct H7. subst. apply Union_intror ; apply In_singleton.
            simpl. apply MP with (ps:=[(fst (nextension_theory Γ Δ n), list_disj x --> list_disj (x0 ++ remove_list x0 x));
            (fst (nextension_theory Γ Δ n), list_disj x)]). 2: apply MPRule_I. intros. inversion H6. subst.
            apply Id_list_disj_remove. inversion H7. subst. auto. inversion H8. }
          { assert (exists n0 : nat, First_unused n0 (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y \/ y = ∃ f)).
            assert (J0: (exists n0 : nat, unused_S n0 (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y) /\
            (forall m : nat, n0 <= m -> unused_S m (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y)))).
            pose (nextension_infinite_unused n _ _ ClΓ ClΔ H). destruct e. exists x0. split. apply H4 ; auto. auto.
            pose (unused_finite_superset _ J0 (∃ f :: List.nil)). destruct e. exists x0. unfold First_unused in H4. unfold unused_S in H4. destruct H4.
            unfold First_unused. unfold unused_S. split ; auto. intros. apply H4. unfold In. inversion H6. apply Union_introl ; unfold In ; auto.
            destruct H7. apply Union_introl. unfold In ; auto. apply Union_intror. unfold In ; subst ; apply in_eq. intros. apply H5.
            intros. apply H6. unfold In. inversion H7 ; auto. subst. inversion H8 ; auto. subst. inversion H8 ; subst ; auto. inversion H9. destruct H4.
            assert ((fun x : form => In form (fst (nextension_theory Γ Δ n)) x \/
            (wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), snd (nextension_theory Γ Δ n)) -> False) /\
            (x = ∃ f \/ (exists n0 : nat, First_unused n0
            (fun y : form => In form (fst (nextension_theory Γ Δ n)) y \/ In form (snd (nextension_theory Γ Δ n)) y \/ y = ∃ f) /\
            x = f[$n0..]))) = Union _ (Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (∃ f))) (Singleton _ f[$x0..])).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H5 ; auto. apply Union_introl ; apply Union_introl ; auto.
            destruct H6. destruct H7. subst. apply Union_introl ; apply Union_intror. apply In_singleton. unfold In. destruct H7.
            destruct H7. subst. apply Union_intror. assert (x0 = x2). unfold First_unused in H7. unfold unused_S in H7. destruct H7.
            unfold First_unused in H4. unfold unused_S in H4. destruct H4. assert (x0 <= x2). apply H9 ; auto.
            assert (x2 <= x0).  apply H8 ; auto. lia. rewrite H8. apply In_singleton. unfold In.
            inversion H5 ; auto. subst. inversion H6 ; auto. subst. right. repeat split ; auto. left. inversion H7 ; subst ; auto.
            subst. right ; split ; auto. right. inversion H6 ; subst. exists x0. split ; auto.
            rewrite H5 in H2. clear H5.
            assert ((fun x : form => In form (snd (nextension_theory Γ Δ n)) x \/ wpair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)),
            snd (nextension_theory Γ Δ n)) /\ x = ∃ f) = (snd (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H5. auto. destruct H6. exfalso ; auto. unfold In ; auto.
            rewrite H5 in H1. clear H5.
            apply FOwBIH_Deduction_Theorem with (A:=f[$x0..]) (B:=list_disj x)
            (Γ0:=(Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)))) in H2 ; auto.
            assert (J1: FOwBIH_rules (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), list_disj x)).
            apply MP with (ps:=[(Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), (∃ f) --> list_disj x);
            (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)), (∃ f))]). 2: apply MPRule_I. intros.
            inversion H5. subst. apply EC_unused with (n:=x0) ; auto. destruct H4. unfold unused_S. unfold unused_S in H4.
            intros. inversion H7. inversion H8. subst. apply H4. unfold In ; auto. subst. inversion H9. subst. apply H4 ; unfold In ; auto.
            destruct H8. subst. apply unused_list_disj. intros. apply H1 in H8. apply H4. unfold In ; auto. subst.
            apply H4. unfold In. auto.
            inversion H6 ; subst. 2: inversion H7. apply Id. apply IdRule_I. apply Union_intror ; apply In_singleton.
            exfalso. apply H3. exists x. repeat split ; auto. }
  + auto.
Qed.

Lemma encode_In_L_or_R : forall (A : form) (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (In form (fst (nextension_theory Γ Δ (encode A))) A \/ In form (snd (nextension_theory Γ Δ (encode A))) A).
Proof.
intros. simpl. unfold gen_choice_code.
remember (encode A) as n.
assert (S (encode0 A) = encode A). auto. rewrite H2. clear H2.
rewrite encode_decode_Id. destruct A.
- simpl. right. unfold In. right. split ; auto. exists []. repeat split ; auto.
  apply NoDup_nil. intros. inversion H2. simpl. apply Id. apply IdRule_I. apply Union_intror.
  apply In_singleton.
- simpl. left. unfold In. right. repeat split ; auto. intros.
  apply (Under_nextension_theory (encode0 ⊤) _ _ H H0 H1).
  assert (wpair_der ((fst (nextension_theory Γ Δ (encode0 ⊤))) , Union form (snd (nextension_theory Γ Δ (encode0 ⊤))) (Singleton form ⊤))).
  exists [⊤]. repeat split ; auto. apply NoDup_cons. intro. inversion H3. apply NoDup_nil.
  intros. inversion H3. apply Union_intror. subst. apply In_singleton. inversion H4.
  simpl. apply MP with (ps:=[(fst (nextension_theory Γ Δ (encode0 ⊤)), ⊤ --> (⊤ ∨ ⊥));(fst (nextension_theory Γ Δ (encode0 ⊤)), ⊤)]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA2_I. exists ⊤. exists ⊥. auto.
  inversion H4. subst. 2: inversion H5. apply wTop. pose (Cut _ _ _ H2 H3).
  rewrite surjective_pairing. auto.
- simpl. destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ (encode0 (atom P t)))) (Singleton form (atom P t)), snd (nextension_theory Γ Δ (encode0 (atom P t)))))).
  right. unfold In. right. repeat split ; auto. unfold In. left. right. split ; auto.
- simpl. destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ (encode0 (bin b A1 A2)))) (Singleton form (bin b A1 A2)), snd (nextension_theory Γ Δ (encode0 (bin b A1 A2)))))).
  right. unfold In. right. repeat split ; auto. left. unfold In. right. auto.
- simpl. destruct q.
  + simpl. destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ (encode0 (∀ A)))) (Singleton form (∀ A)), snd (nextension_theory Γ Δ (encode0 (∀ A)))))).
     right. unfold In. right. repeat split ; auto. left. unfold In. right ; auto.
  + simpl. destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ (encode0 (∃ A)))) (Singleton form (∃ A)), snd (nextension_theory Γ Δ (encode0 (∃ A)))))).
     right. unfold In. right. repeat split ; auto. left. unfold In. right. repeat split ; auto.
Qed.

Lemma In_extension_In_encode_L : forall (A : form) (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  In form (fst (extension_theory Γ Δ)) A ->
  In form (fst (nextension_theory Γ Δ (encode A))) A.
Proof.
intros. pose (encode_In_L_or_R A _ _ H H0 H1). destruct o ; auto.
exfalso. unfold extension_theory in H2. simpl in H2. inversion H2.
pose (Nat.max_dec x (encode A)). destruct s.
 apply (Under_nextension_theory x _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (Init.Nat.max x (encode A0)) (encode A0) Γ Δ A0).
destruct a. apply H7 in H3 ; try lia. rewrite e in H3 ; auto. simpl.
apply MP with (ps:=[(fst (nextension_theory Γ Δ x), A --> (A ∨ ⊥)); (fst (nextension_theory Γ Δ x), A)]).
2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists A. exists ⊥. auto. inversion H6. 2: inversion H7. subst.
apply Id. apply IdRule_I. auto.
apply (Under_nextension_theory (encode A) _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (Init.Nat.max x (encode A0)) x Γ Δ A0).
destruct a. apply H6 in H4 ; try lia. rewrite e in H4 ; auto. simpl (list_disj (A :: List.nil)).
apply MP with (ps:=[(fst (nextension_theory Γ Δ (encode A)), A --> (A ∨ ⊥)); (fst (nextension_theory Γ Δ (encode A)), A)]).
2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists A. exists ⊥. auto. inversion H6. 2: inversion H7. subst.
apply Id. apply IdRule_I.
pose (nextension_theory_extens_le (encode A) x Γ Δ A).
destruct a. apply H7. 2: lia. auto.
Qed.

Lemma In_extension_In_encode_R : forall (A : form) (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  In form (snd (extension_theory Γ Δ)) A ->
  In form (snd (nextension_theory Γ Δ (encode A))) A.
Proof.
intros. pose (encode_In_L_or_R A _ _ H H0 H1). destruct o ; auto.
exfalso. unfold extension_theory in H2. simpl in H2. inversion H2.
pose (Nat.max_dec x (encode A)). destruct s.
 apply (Under_nextension_theory x _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6. auto.
apply MP with (ps:=[(fst (nextension_theory Γ Δ x), A --> (A ∨ ⊥)); (fst (nextension_theory Γ Δ x), A)]).
2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists A. exists ⊥. auto. inversion H6. 2: inversion H7. subst.
apply Id. apply IdRule_I.
pose (nextension_theory_extens_le x (encode A) Γ Δ A).
destruct a. apply H7 ; try lia ; auto.
apply (Under_nextension_theory (encode A) _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (encode A0) x Γ Δ A0).
destruct a. apply H7 ; try lia ; auto.
apply MP with (ps:=[(fst (nextension_theory Γ Δ (encode A)), A --> (A ∨ ⊥)); (fst (nextension_theory Γ Δ (encode A)), A)]).
2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists A. exists ⊥. auto. inversion H6. 2: inversion H7. subst.
apply Id. apply IdRule_I.
pose (nextension_theory_extens_le (encode A) x Γ Δ A).
destruct a. auto.
Qed.

Lemma max_list_encode : forall l, (exists m, forall n, (exists A, encode A = n /\ List.In A l) -> n <= m).
Proof.
induction l.
- exists 0. intros. destruct H. destruct H. inversion H0.
- destruct IHl. exists (Nat.max (encode a) x). intros. destruct H0. destruct H0.
  inversion H1. subst. lia. subst.
  assert (exists A : form, encode A = encode x0 /\ List.In A l). exists x0 ; auto.
  pose (H (encode x0) H0). lia.
Qed.

Lemma Under_extension_theory : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (wpair_der (extension_theory Γ Δ) -> False).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. unfold extension_theory in H0. destruct H0. destruct H0. destruct H1. simpl in H1.
simpl in H2. pose (FOwBIH_finite _ H2). destruct e. simpl in H3. destruct H3. destruct p. destruct e.
assert (exists ml, forall n, (exists A, encode A = n /\ List.In A x1) -> n <= ml).
apply max_list_encode. destruct H4.
assert (exists mr, forall n, (exists A, encode A = n /\ List.In A x) -> n <= mr).
apply max_list_encode. destruct H5.
pose (Under_nextension_theory (max x2 x3) _ _ ClΓ ClΔ H). apply f0.
exists x. repeat split ; auto.
intros. pose (H1 _ H6). pose (In_extension_In_encode_R A _ _ ClΓ ClΔ H).
assert (In form (snd (extension_theory Γ Δ)) A). inversion i0. unfold extension_theory.
simpl. unfold In. exists x4 ; auto. apply i1 in H7.
pose (nextension_theory_extens_le (Init.Nat.max x2 x3) (encode A) Γ Δ A).
destruct a. apply H9 ; auto. assert (exists A0 : form, encode A0 = encode A /\ List.In A0 x).
exists A ; auto. pose (H5 (encode A) H10). lia.
apply (FOwBIH_monot _ f). simpl. intro. intro.
pose (In_extension_In_encode_L x4 _ _ ClΓ ClΔ H).
pose (i _ H6). pose (H3 x4). destruct p. pose (i2 H6).
pose (nextension_theory_extens_le (Init.Nat.max x2 x3) (encode x4) Γ Δ x4).
destruct a. apply H7 ; auto. assert (exists A : form, encode A = encode x4 /\ List.In A x1).
exists x4 ; auto. pose (H4 (encode x4) H9). lia.
Qed.


(* The extension is consistent. *)

Lemma Consist_nextension_theory : forall n (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (wpair_der (fst (nextension_theory Γ Δ n), Singleton _ ⊥) -> False).
Proof.
intros n Γ Δ ClΓ ClΔ ; intros. pose (Under_nextension_theory n Γ Δ ClΓ ClΔ H).
apply f. exists []. repeat split ; auto. apply NoDup_nil.
intros. inversion H1. simpl. destruct H0. destruct H0. destruct H1.
simpl in H2. simpl in H1. destruct x. simpl in H2 ; auto.
destruct x. assert (J1: List.In f0 (f0 :: List.nil)). apply in_eq. pose (H1 _ J1).
inversion i ; subst ; auto. simpl in H2. apply absorp_Or2. auto.
exfalso.  assert (J1: List.In f0 (f0 :: f1 :: x)). apply in_eq.
apply H1 in J1. inversion J1. subst. assert (J2: List.In f1 (⊥ :: f1 :: x)).
apply in_cons. apply in_eq. apply H1 in J2. inversion J2. subst.
inversion H0. subst. apply H5. apply in_eq.
Qed.

Lemma Consist_extension_theory : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (wpair_der (fst (extension_theory Γ Δ), Singleton _ ⊥) -> False).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. destruct H0. destruct H0. destruct H1.
simpl in H2. simpl in H1. apply (Under_extension_theory Γ Δ) ; auto. exists [].
repeat split ; auto. apply NoDup_nil. intros. inversion H3.
simpl. destruct x. simpl in H2. auto. destruct x.
assert (J1: List.In f (f :: List.nil)). apply in_eq. apply H1 in J1. inversion J1. subst. simpl in H2.
apply absorp_Or1 ; auto. exfalso.
assert (J1: List.In f (f :: f0 :: x)). apply in_eq. apply H1 in J1. inversion J1. subst.
assert (J2: List.In f0 (⊥ :: f0 :: x)). apply in_cons. apply in_eq. apply H1 in J2. inversion J2. subst.
inversion H0. apply H5 ; subst ; apply in_eq.
Qed.




(* The extension is complete. *)

Lemma Complete_Lind_pair : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  complete (extension_theory Γ Δ).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. intro. simpl. unfold In.
destruct (classic (wpair_der ((Union _ (fst (nextension_theory Γ Δ (encode0 A))) (Singleton _ A)), snd (nextension_theory Γ Δ (encode0 A))))).
- right. exists (encode A). simpl. unfold gen_choice_code. remember (decoding (S (encode0 A))) as o.
  destruct o.
  + assert (S (encode0 A) = encode A). auto. rewrite H1 in Heqo. rewrite encode_decode_Id in Heqo. inversion Heqo. subst.
     clear H1. clear Heqo. destruct A.
      * simpl. right. repeat split ; auto.
      * simpl. exfalso. apply (Under_extension_theory _ _ ClΓ ClΔ H).
         assert (wpair_der ((fst (nextension_theory Γ Δ (encode0 ⊤))), Union form (snd (nextension_theory Γ Δ (encode0 ⊤)))(Singleton form ⊤))).
         exists [⊤]. repeat split ; auto. apply NoDup_cons. intro. inversion H1. apply NoDup_nil.
         intros. inversion H1. subst. simpl. apply Union_intror. apply In_singleton. inversion H2. simpl.
         apply MP with (ps:=[(fst (nextension_theory Γ Δ (encode0 ⊤)), ⊤ --> (⊤ ∨ ⊥));(fst (nextension_theory Γ Δ (encode0 ⊤)), ⊤)]).
         2: apply MPRule_I. intros. inversion H1. subst. 2: inversion H2 ; subst ; try apply wTop ; try inversion H3.
         apply Ax. apply AxRule_I. apply RA2_I. exists ⊤. exists ⊥ ; auto. pose (Cut _ _ _ H0 H1).
         destruct w. destruct H2. destruct H3. simpl in H3. simpl in H4. exists x. repeat split ; auto.
         intros. apply H3 in H5. pose (nextension_theory_extens (encode0 ⊤) Γ Δ A). destruct a.
        apply (extension_theory_extens_nextension (encode0 ⊤)) ; auto.
        apply (FOwBIH_monot _ H4). intro. apply (extension_theory_extens_nextension (encode0 ⊤)) ; auto.
      * simpl. right. repeat split ; auto.
      * simpl. right. repeat split ; auto.
      * destruct q.
        -- simpl. right. repeat split ; auto.
        -- simpl. right. repeat split ; auto.
  + exfalso. assert (S (encode0 A) = encode A). auto. rewrite H1 in Heqo. rewrite encode_decode_Id in Heqo. inversion Heqo.
- left. exists (encode A). simpl. unfold gen_choice_code. remember (decoding (S (encode0 A))) as o.
  destruct o.
  + assert (S (encode0 A) = encode A). auto. rewrite H1 in Heqo. rewrite encode_decode_Id in Heqo. inversion Heqo. subst.
     clear H1. clear Heqo. destruct A ; simpl ; try right ; repeat split ; auto.
     destruct q.
     * simpl. right ; repeat split ; auto.
     * simpl. right ; repeat split ; auto.
  + exfalso. assert (S (encode0 A) = encode A). auto. rewrite H1 in Heqo. rewrite encode_decode_Id in Heqo. inversion Heqo.
Qed.


(* The extension is closed under derivations. *)

Lemma closeder_fst_Lind_pair : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (forall A, FOwBIH_rules (fst (extension_theory Γ Δ), A) -> (In _ (fst (extension_theory Γ Δ)) A)).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. destruct (classic (In form (fst (extension_theory Γ Δ)) A)) ; auto.
exfalso. pose (Complete_Lind_pair _ _ ClΓ ClΔ H). unfold complete in c. pose (c A). destruct o ; auto.
apply (Under_extension_theory _ _ ClΓ ClΔ H). exists [A]. repeat split ; auto.
apply NoDup_cons. intro. inversion H3. apply NoDup_nil. intros. inversion H3 ; subst.
auto. inversion H4. simpl.
apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, A --> (A ∨ ⊥));
(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, A)]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA2_I.
exists A. exists ⊥ ; auto. inversion H4 ; subst ; auto ; inversion H5.
Qed.


(* The extension is prime. *)

Lemma primeness_fst_Lind_pair0 : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (forall A1 A2, (wpair_der (fst (extension_theory Γ Δ), Singleton _ (A1 ∨ A2))) ->
                        ((In _ (fst (extension_theory Γ Δ)) A1) \/ (In _ (fst (extension_theory Γ Δ)) A2))).
Proof.
intros Γ Δ ClΓ ClΔ ; intros.
destruct (classic (In form (fst (extension_theory Γ Δ)) A1)) ; auto.
destruct (classic (In form (fst (extension_theory Γ Δ)) A2)) ; auto.
exfalso. apply (Under_extension_theory _ _ ClΓ ClΔ H).
pose (Complete_Lind_pair _ _ ClΓ ClΔ H). unfold complete in c.
destruct H0. destruct H0. destruct H3. simpl in H3. simpl in H4.
destruct x.
- simpl in H4. exists []. repeat split ; auto. intros. inversion H5.
- simpl in H4. destruct x.
  + simpl in H4. assert (J1: List.In f (f :: List.nil)). apply in_eq. apply H3 in J1.
     inversion J1. subst. destruct (eq_dec_form A1 A2).
    * subst. exists [A2]. repeat split ; auto. apply NoDup_cons.
      intro. inversion H5. apply NoDup_nil. intros. inversion H5 ; subst.
      2: inversion H6. pose (c A). destruct o ; auto. exfalso ; auto.
      simpl.
      apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, ((A2 ∨ A2) ∨ ⊥) --> (A2 ∨ ⊥));
      (fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x,  (A2 ∨ A2) ∨ ⊥)]).
      2: apply MPRule_I. intros. inversion H5. subst. apply wmonotR_Or.
      apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, (A2 --> A2) --> (A2 ∨ A2 --> A2));
      (fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, A2 --> A2)]). 2: apply MPRule_I.
      intros. inversion H6. subst.
      apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, (A2 --> A2) --> (A2 --> A2) --> (A2 ∨ A2 --> A2));
      (fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, A2 --> A2)]). 2: apply MPRule_I.
      intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA4_I. exists A2. exists A2. exists A2. auto.
      inversion H8. 2: inversion H9. subst. apply wimp_Id_gen. inversion H7. 2: inversion H8. subst. apply wimp_Id_gen.
      inversion H6. subst. 2: inversion H7. auto.
    * subst. exists [A1;A2]. repeat split ; auto. apply NoDup_cons.
      intro. inversion H5. subst. auto. inversion H6. apply NoDup_cons. intro.
      inversion H5. apply NoDup_nil. intros. inversion H5 ; subst. pose (c A). destruct o ; auto. exfalso ; auto.
      inversion H6 ; subst. pose (c A). destruct o ; auto. exfalso ; auto. inversion H7. simpl.
      apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, (A1 ∨ A2)--> (A1 ∨ (A2 ∨ ⊥)));
      (fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x,  (A1 ∨ A2))]).
      2: apply MPRule_I. intros. inversion H5. subst.
      apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, (A2 -->  (A1 ∨ (A2 ∨ ⊥))) --> ((A1 ∨ A2) --> (A1 ∨ (A2 ∨ ⊥))));
      (fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x,  A2 -->  (A1 ∨ (A2 ∨ ⊥)))]).
      2: apply MPRule_I. intros. inversion H6. subst.
      apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, (A1 -->  (A1 ∨ (A2 ∨ ⊥))) --> (A2 -->  (A1 ∨ (A2 ∨ ⊥))) --> ((A1 ∨ A2) --> (A1 ∨ (A2 ∨ ⊥))));
      (fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x,  A1 -->  (A1 ∨ (A2 ∨ ⊥)))]).
      2: apply MPRule_I. intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA4_I. exists A1. exists A2.
      exists (A1 ∨ (A2 ∨ ⊥)). auto. inversion H8. 2: inversion H9. subst. apply Ax. apply AxRule_I.
      apply RA2_I. exists A1. exists (A2 ∨ ⊥) ; auto. inversion H7. 2: inversion H8. subst.
      apply MP with (ps:=[(fun x : form => exists n0 : nat, In form (fst (nextension_theory Γ Δ n0)) x, ((A2 ∨ ⊥) --> A1 ∨ (A2 ∨ ⊥)) --> (A2 --> A1 ∨ (A2 ∨ ⊥)));
      (fun x : form => exists n0 : nat, In form (fst (nextension_theory Γ Δ n0)) x, (A2 ∨ ⊥) --> A1 ∨ (A2 ∨ ⊥))]).
      2: apply MPRule_I. intros. inversion H8. subst.
      apply MP with (ps:=[(fun x : form => exists n0 : nat, In form (fst (nextension_theory Γ Δ n0)) x, (A2--> (A2 ∨ ⊥)) --> ((A2 ∨ ⊥) --> A1 ∨ (A2 ∨ ⊥)) --> (A2 --> A1 ∨ (A2 ∨ ⊥)));
      (fun x : form => exists n0 : nat, In form (fst (nextension_theory Γ Δ n0)) x, A2 --> (A2 ∨ ⊥))]).
      2: apply MPRule_I. intros. inversion H9. subst. apply Ax. apply AxRule_I. apply RA1_I. exists A2.
      exists (A2 ∨ ⊥). exists (A1 ∨ (A2 ∨ ⊥)) ; auto. inversion H10 ; subst. 2: inversion H11.
      apply Ax. apply AxRule_I. apply RA2_I. exists A2. exists ⊥ ; auto. inversion H9 ; subst.
      2: inversion H10. apply Ax. apply AxRule_I. apply RA3_I. exists A1. exists (A2 ∨ ⊥). auto.
      inversion H6. 2: inversion H7. subst. apply absorp_Or1 ; auto.
  + exfalso. inversion H0. apply H7. subst. assert (J1: List.In f (f :: f0 :: x)). apply in_eq.
     assert (J2: List.In f0 (f :: f0 :: x)). apply in_cons. apply in_eq. apply H3 in J1. apply H3 in J2.
     inversion J1. inversion J2. subst. apply in_eq.
Qed.

Lemma primeness_fst_Lind_pair : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (forall A1 A2, In _ (fst (extension_theory Γ Δ)) (A1 ∨ A2) ->
                     ((In _ (fst (extension_theory Γ Δ)) A1) \/ (In _ (fst (extension_theory Γ Δ)) A2))).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. apply primeness_fst_Lind_pair0 ; auto. exists [(A1 ∨ A2)].
simpl ; repeat split ; auto. apply NoDup_cons. intro. inversion H1. apply NoDup_nil.
intros. inversion H1 ; try firstorder.
subst. unfold In. apply In_singleton.
apply MP with (ps:=[(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, (A1 ∨ A2) --> (A1 ∨ A2) ∨ ⊥);
(fun x : form => exists n : nat, In form (fst (nextension_theory Γ Δ n)) x, (A1 ∨ A2))]).
2: apply MPRule_I. intros. inversion H1 ; subst. apply Ax. apply AxRule_I. apply RA2_I. exists (A1 ∨ A2).
exists bot. auto. inversion H2 ; subst. 2: inversion H3. apply Id. apply IdRule_I. auto.
Qed.

Lemma list_primeness_fst_Lind_pair : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (forall x, In _ (fst (extension_theory Γ Δ)) (list_disj x) -> 
                       ((In _ (fst (extension_theory Γ Δ)) ⊥) \/ (exists A, List.In A x /\ (In _ (fst (extension_theory Γ Δ)) A)))).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. induction x.
- simpl in H0. left. auto.
- simpl. simpl in H0. apply primeness_fst_Lind_pair in H0 ; auto. destruct H0. right.
  exists a. auto. apply IHx in H0. destruct H0. left. auto.
  right. destruct H0. destruct H0. clear IHx. exists x0. auto.
Qed.

(* The extension witnesses existentials on the left. *)

Definition witness_Ex Γ := forall A, In _ Γ (∃ A) -> (exists t, In _ Γ A[t..]).

Lemma Lwitness_Ex_help : forall A (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  In form (fst (extension_theory Γ Δ)) (∃ A) ->
  (exists n, In form (fst (nextension_theory Γ Δ (encode (∃ A)))) A[(var n)..]).
Proof.
intros.
pose (In_extension_In_encode_L (∃ A) _ _ H H0 H1 H2).
simpl. unfold gen_choice_code.
assert (S (encode0 (∃ A)) = encode (∃ A)). auto. rewrite H3. clear H3.
rewrite encode_decode_Id. simpl.
assert (Unused: exists n0 : nat, First_unused n0 (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∃ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∃ A)))) y \/ y = ∃ A)).
pose (nextension_infinite_unused (encode0 (∃ A)) _ _ H H0 H1).
assert (J0: (exists n : nat, unused_S n (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∃ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∃ A)))) y)
/\ (forall m : nat, n <= m -> unused_S m (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∃ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∃ A)))) y)))).
destruct e. exists x. split. apply H3 ; auto. auto.
pose (unused_finite_superset _ J0 (∃ A :: List.nil)). destruct e0. clear J0. clear e. exists x.
assert ((Union form (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∃ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∃ A)))) y)
(fun x : form => List.In x (∃ A :: List.nil))) = (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∃ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∃ A)))) y \/ y = ∃ A)).
apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H4 ; subst ; auto. inversion H5 ; subst ; auto.
right. right. inversion H5. subst ; auto. inversion H6. unfold In. inversion H4 ; subst ; auto. apply Union_introl. unfold In ; auto.
destruct H5. apply Union_introl. unfold In ; auto. subst. apply Union_intror.
unfold In. apply in_eq.
rewrite H4 in H3. auto.
destruct Unused. exists x. unfold In. right. split.
intro. destruct H4. simpl in H4. destruct H4. destruct H5.
apply (Under_nextension_theory (encode (∃ A)) _ _ H H0 H1).
exists x0. repeat split ; auto. intros. apply H5 in H7.
assert (encode0 (∃ A) <= encode (∃ A)). unfold encode. lia.
pose (nextension_theory_extens_le (encode (∃ A)) (encode0 (∃ A)) Γ Δ A0). destruct a.
apply H10 ; auto.
apply MP with (ps:=[(fst (nextension_theory Γ Δ (encode (∃ A))), (∃ A) --> list_disj x0);(fst (nextension_theory Γ Δ (encode (∃ A))), ∃ A)]).
2: apply MPRule_I. intros. inversion H7. subst.
apply (FOwBIH_Deduction_Theorem (Union form (fst (nextension_theory Γ Δ (encode (∃ A)))) (Singleton form (∃ A)), list_disj x0)) ; auto.
apply (FOwBIH_monot _ H6) ; auto. intro. intros. inversion H8 ; subst. apply Union_introl.
apply (nextension_theory_extens_le (encode (∃ A)) (encode0 (∃ A)) Γ Δ x1) ; auto. unfold encode ; auto.
apply Union_intror ; auto. inversion H8. subst. 2: inversion H9. apply Id. apply IdRule_I.
auto. right. exists x. unfold First_unused. unfold unused_S. unfold First_unused in H3.
unfold unused_S in H3. destruct H3. repeat split. intros. apply H3. auto. intros.
apply H4 ; auto.
Qed.

Lemma Lwitness_Ex_fst_Lind_pair : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (witness_Ex (fst (extension_theory Γ Δ))).
Proof.
intros. unfold witness_Ex. intros. simpl in H2.
assert (exists n, In form (fst (nextension_theory Γ Δ (encode (∃ A)))) A[(var n)..]).
apply Lwitness_Ex_help ; auto.
destruct H3. exists $x. apply extension_theory_extens_nextension in H3. auto.
Qed.



(* The extension witnesses universals on the right. *)

Definition witness_All Δ := forall A, In _ Δ (∀ A) -> (exists t, In _ Δ A[t..]).

Lemma Rwitness_All_help : forall A (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  In form (snd (extension_theory Γ Δ)) (∀ A) ->
  (exists n, In form (snd (nextension_theory Γ Δ (encode (∀ A)))) A[(var n)..]).
Proof.
intros.
pose (In_extension_In_encode_R (∀ A) _ _ H H0 H1).
simpl. unfold gen_choice_code.
assert (S (encode0 (∀ A)) = encode (∀ A)). auto. rewrite H3. clear H3.
rewrite encode_decode_Id. simpl.
assert (Unused: exists n0 : nat, First_unused n0 (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∀ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∀ A)))) y \/ y = ∀ A)).
pose (nextension_infinite_unused (encode0 (∀ A)) _ _ H H0 H1).
assert (J0: (exists n : nat, unused_S n (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∀ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∀ A)))) y)
/\ (forall m : nat, n <= m -> unused_S m (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∀ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∀ A)))) y)))).
destruct e. exists x. split. apply H3 ; auto. auto.
pose (unused_finite_superset _ J0 (∀ A :: List.nil)). destruct e0. clear e. clear J0. exists x.
assert ((Union form (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∀ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∀ A)))) y)
(fun x : form => List.In x (∀ A :: List.nil))) = (fun y : form => In form (fst (nextension_theory Γ Δ (encode0 (∀ A)))) y \/ In form (snd (nextension_theory Γ Δ (encode0 (∀ A)))) y \/ y = ∀ A)).
apply Extensionality_Ensembles. split ; intro ; intro. unfold In. inversion H4 ; subst ; auto. inversion H5 ; subst ; auto.
right. right. inversion H5. subst ; auto. inversion H6. unfold In. inversion H4 ; subst ; auto. apply Union_introl. unfold In ; auto.
destruct H5. apply Union_introl. unfold In ; auto. subst. apply Union_intror. unfold In. apply in_eq. rewrite H4 in H3. auto.
destruct Unused. exists x. unfold In. right. split.
destruct (classic (wpair_der (Union form (fst (nextension_theory Γ Δ (encode0 (∀ A)))) (Singleton form (∀ A)), snd (nextension_theory Γ Δ (encode0 (∀ A)))))) ; auto.
exfalso. apply (Under_nextension_theory (encode (∀ A)) _ _ H H0 H1). exists [∀ A].
repeat split ; auto. apply NoDup_cons. intro. inversion H5. apply NoDup_nil. intros.
inversion H5. subst. apply i ; auto. inversion H6. simpl.
apply MP with (ps:=[(fst (gen_choice_code (fst (nextension_theory Γ Δ (encode0 (∀ A)))) (snd (nextension_theory Γ Δ (encode0 (∀ A)))) (S (encode0 (∀ A)))), (∀ A) --> (∀ A) ∨ ⊥);
(fst (gen_choice_code (fst (nextension_theory Γ Δ (encode0 (∀ A)))) (snd (nextension_theory Γ Δ (encode0 (∀ A)))) (S (encode0 (∀ A)))), (∀ A))]).
2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA2_I. exists (∀ A). exists ⊥. auto.
inversion H6. 2: inversion H7. subst. apply Id. apply IdRule_I.
clear H6. clear H5. unfold gen_choice_code. assert (S (encode0 (∀ A)) = encode (∀ A)). auto.
rewrite H5. rewrite encode_decode_Id. simpl. unfold In. right. auto. right.
exists x. unfold First_unused. unfold unused_S. unfold First_unused in H3.
unfold unused_S in H3. destruct H3. repeat split. intros. apply H3. auto. intros.
apply H4 ; auto.
Qed.

Lemma Rwitness_All_fst_Lind_pair : forall (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (wpair_der (Γ, Δ) -> False) ->
  (witness_All (snd (extension_theory Γ Δ))).
Proof.
intros. unfold witness_All. intros. simpl in H2.
assert (exists n, In form (snd (nextension_theory Γ Δ (encode (∀ A)))) A[(var n)..]).
apply Rwitness_All_help ; auto.
destruct H3. exists $x. apply extension_theory_extens_nextension in H3. auto.
Qed.


(* ---------------------------------------------------------------------------------------------------------------------------- *)

(* Finally, we obtain the Lindenbaum lemma. *)

Lemma Lindenbaum_lemma : forall (Γ Δ: Ensemble form),
    (closed_S Γ) ->
    (closed_S Δ) ->
    (wpair_der (Γ, Δ) -> False) ->
    (exists Lind, Included _ Γ (fst Lind) /\
                   Included _ Δ (snd Lind) /\
                   complete Lind /\
                   witness_Ex (fst Lind) /\
                   witness_All (snd Lind) /\
                   (wpair_der Lind -> False)).
Proof.
intros Γ Δ ClΓ ClΔ notder.
exists (extension_theory Γ Δ). repeat split.
- intro. apply extension_theory_extens.
- intro. apply extension_theory_extens. 
- apply Complete_Lind_pair ; auto.
- apply Lwitness_Ex_fst_Lind_pair ; auto.
- apply Rwitness_All_fst_Lind_pair ; auto.
- apply Under_extension_theory ; auto.
Qed.


End Lindenbaum.


