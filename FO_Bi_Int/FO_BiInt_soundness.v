Require Import List.
Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_Kripke_sem.
Require Import Classical.
Require Import Ensembles.
Require Import Lia.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

(* ** Soundness **)

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Lemma Ax_valid : forall A, BIAxioms A -> kvalid A.
Proof.
intros A AX. inversion AX.
- destruct H ; destruct H ; destruct H ; subst. unfold RA1 ; cbn. unfold kvalid. intros. simpl ; intros.
  apply H2 ; auto. apply H0 ; auto. apply (reach_tran H1 H3).
- destruct H ; destruct H ; subst ; simpl. intro. intros. unfold RA2 ; cbn. intros. auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. auto.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. destruct H4.
  apply H0 ; auto. apply (reach_tran H1 H3). apply H2 ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct H0 ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct H0 ; auto.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. split. apply H0 ; auto.
  apply (reach_tran H1 H3). apply H2 ; auto.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. destruct H2.
  pose (H0 _ H1 H2). apply k ; auto. apply reach_refl.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. apply H0.
  apply (reach_tran H1 H3). split ; auto. apply ksat_mon with (u0:=v0) ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply H0 in H4.
  apply (H2 _ H3 H4). apply (reach_tran H1 H3).
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros.
  destruct (classic (rho ⊩( v) x0)) ; auto. right. exists v. repeat split ; auto. apply reach_refl.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct H0. destruct H0.
  destruct H1. exists x1. repeat split ; auto. intros. apply H2. apply H3 ; auto. apply reach_refl.
- destruct H ; destruct H ; destruct H ; subst. unfold kvalid. cbn. intros. destruct H0. destruct H0.
  destruct H1. destruct H0. destruct H0. destruct H3. exists x3. repeat split ; auto. apply (reach_tran H3 H1).
  intro. destruct H5. apply H4 ; auto. apply H2. apply (ksat_mon H3 H5).
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. destruct (classic (rho ⊩( v0) x0)) ; auto.
  exfalso. apply (H0 _ H1). exists v0 ; repeat split ; auto. apply reach_refl.
- destruct H ; subst ; simpl. intro. intros. cbn. intros. apply I.
- destruct H ; subst ; simpl. intro. intros. cbn. intros. inversion H0.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply H0 ; auto.
  apply ksat_comp. auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply ksat_comp.
  unfold funcomp. eapply (ksat_ext v). 2: eapply (H0 (eval rho x0)). intros. unfold scons. destruct x1 ; auto.
- destruct H ; destruct H ; subst ; simpl. intro. intros. cbn. intros. apply ksat_comp in H0.
  eexists (eval rho x0). eapply (ksat_ext v). 2: eapply H0. unfold funcomp. intros. unfold scons. destruct x1 ; auto.
Qed.

Lemma wSoundness0 : forall s, FOwBIH_rules s -> kvalid_ctx (fst s) (snd s).
Proof.
intros s Hprv. induction Hprv; subst; cbn; intros D M u rho HX.
(* Id *)
- inversion H. subst. apply HX ; auto.
(* Ax *)
- inversion H ; subst. apply Ax_valid ; auto.
(* MP *)
- inversion H1. subst. simpl.
  assert (J1: kvalid_ctx Γ (A --> B)). apply (H0 (Γ, A --> B)). apply in_eq.
  assert (J2: kvalid_ctx Γ A). apply (H0 (Γ, A)). apply in_cons ; apply in_eq.
  simpl in HX. unfold kvalid_ctx in J1,J2. pose (J1 _ _ _ _ HX). pose (J2 _ _ _ _ HX).
  simpl in k. apply k ; auto. apply reach_refl.
(* DNw *)
- inversion H1. subst. simpl. intros. destruct H3. destruct H3. destruct H4.
  assert (J1: kvalid_ctx (Empty_set _) A). apply (H0 (Empty_set _, A)). apply in_eq.
  simpl in HX. unfold kvalid_ctx in J1.
  assert (J2: forall psi : form, In _ (Empty_set _) psi -> rho ⊩( x) psi). intros. inversion H6.
  pose (J1 _ _ x _ J2). apply H5. auto.
(* Gen *)
- inversion H1. subst. simpl in HX. simpl. intros.
  assert (J1: kvalid_ctx (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) A).
  apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A)). apply in_eq.
  unfold kvalid_ctx in J1. apply J1. intros. inversion H2. destruct H3. subst.
  apply HX in H4. apply ksat_comp. simpl. unfold funcomp. simpl. auto.
(* EC *)
- inversion H1. subst. simpl in HX. simpl. intros.
  assert (J1: kvalid_ctx (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) (A --> B[↑])).
  apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑])). apply in_eq.
  unfold kvalid_ctx in J1. destruct H3.
  assert (J2: (forall psi : form, In _ (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) psi -> (x .: rho) ⊩( u) psi)). intros.
  destruct H4. destruct H4. subst. apply HX in H5. apply ksat_comp.
  simpl. unfold funcomp. simpl. auto. pose (J1 _ _ u (x .: rho) J2). simpl in k. apply k in H3 ; auto.
  apply ksat_comp in H3. unfold funcomp in H3. simpl in H3. auto.
Qed.

Lemma wSoundness1 : forall s, FOwBIH_rules s -> loc_conseq (fst s) (fun x => x = (snd s)).
Proof.
intros. apply wSoundness0 in H. destruct s. simpl ; simpl in H. intro. unfold kvalid_ctx in H.
intros. exists f. split ; auto. unfold In. auto.
Qed.

Lemma wSoundnessThm (A : form) : FOwBIH_rules (Empty_set _, A) -> kvalid A.
Proof.
intros. apply wSoundness0 in H. simpl in H. unfold kvalid_ctx in H. unfold kvalid. intros.
apply H. intros. inversion H0.
Qed.

Lemma list_disj_witn : forall D (M : kmodel D) u rho l,
    (ksat u rho (list_disj l)) -> (exists A, (List.In A l) /\ (ksat u rho A)).
Proof.
induction l.
- simpl. intros. inversion H.
- simpl. intros. destruct H.
  * exists a. split. apply in_eq. assumption.
  * apply IHl in H. destruct H. destruct H. exists x. split ; try assumption. apply in_cons ; auto.
Qed.

Theorem wSoundness : forall Γ Δ, wpair_der (Γ, Δ) -> (loc_conseq Γ Δ).
Proof.
intros Γ Δ wpair. destruct wpair. simpl in H. destruct H. destruct H0.
apply wSoundness1 in H1. simpl in H1. intro. intros. unfold loc_conseq in H1.
pose (H1 _ _ _ _ H2). destruct e. destruct H3. inversion H3. subst.
induction x.
- simpl in H0. exfalso. simpl in H4. inversion H4.
- simpl in IHx. simpl in H4. simpl in H3. simpl in H1. destruct H4.
  * exists a. split. apply H0. apply in_eq. auto.
  * apply list_disj_witn in H4. destruct H4. destruct H4. exists x0. split.
    apply H0. apply in_cons ; auto. auto.
Qed.

Theorem sSoundness1 :  forall s, FOsBIH_rules s -> glob_conseq (fst s) (fun x => x = (snd s)).
Proof.
intros s Hprv. induction Hprv; subst; cbn ; intros D M rho HX u .
(* Ids *)
- inversion H. subst ; simpl in HX ; simpl. exists A ; split ; auto. unfold In ; auto.
(* Axs *)
- inversion H ; subst ; simpl. exists A ; split ; auto. unfold In ; auto. apply Ax_valid ; auto.
(* MPs *)
- inversion H1. subst ; simpl in HX ; simpl. exists B ; split ; auto. unfold In ; auto.
  assert (J1: glob_conseq Γ (fun x => x = (A --> B))). apply (H0 (Γ, A --> B)). apply in_eq.
  assert (J2: glob_conseq Γ (fun x => x = A)). apply (H0 (Γ, A)). apply in_cons ; apply in_eq.
  unfold glob_conseq in J1,J2. pose (J1 _ _ rho HX u). pose (J2 _ _ rho HX u).
  destruct e. destruct e0. destruct H2. destruct H3. inversion H2 ; subst.
  inversion H3. subst. apply H4 ; auto. apply reach_refl.
(* DNs *)
- inversion H1. subst ; simpl in HX ; simpl. exists (¬ (∞ A)) ; split ; auto. unfold In ; auto. simpl. intros.
  destruct H3. destruct H3. destruct H4.
  assert (J1: glob_conseq Γ (fun x => x = A)). apply (H0 (Γ, A)). apply in_eq.
  unfold glob_conseq in J1.
  assert (J2: forall A : form, In form Γ A -> forall (u : nodes (domain:=D)), rho ⊩( u) A). intros.
  auto. pose (J1 _ _ rho J2 x). destruct e. destruct H6. inversion H6 ; subst. auto.
(* Gens *)
- inversion H1. subst; simpl in HX ; simpl. exists (∀ A) ; split ; auto. unfold In ; auto. intro.
  assert (J1: glob_conseq (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) (fun x => x = A)). 
  apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A)). apply in_eq.
  unfold glob_conseq in J1.
  assert (J2: forall A : form,
      In form (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) A -> forall (u : nodes (domain:=D)), (j .: rho) ⊩( u) A).
  intros. destruct H2. destruct H2. subst.
  pose (HX _ H3 u0). apply ksat_comp. simpl. unfold funcomp. simpl. auto.
  pose (J1 _ _ (j .: rho) J2 u). destruct e. destruct H2. inversion H2 ; subst ; auto.
(* ECs *)
- inversion H1. subst ; simpl in HX ; simpl. exists ((∃ A) --> B) ; split ; auto. unfold In ; auto. cbn ; intros.
  assert (J1: glob_conseq (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) (fun x => x = (A --> B[↑]))).
  apply (H0 (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A --> B[↑])). apply in_eq.
  unfold glob_conseq in J1. destruct H3.
  assert (J2: forall A : form, In form (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) A -> 
  forall (u : nodes (domain:=D)), (x .: rho) ⊩( u) A). intros.
  destruct H4. destruct H4. subst. pose (HX _ H5 u0). apply ksat_comp.
  simpl. unfold funcomp. simpl. auto. pose (J1 _ _ (x .: rho) J2 u). simpl in e. destruct e. destruct H4. inversion H4. subst.
  simpl in H5. pose (H5 _ H2 H3). apply ksat_comp in k. unfold funcomp in k. simpl in k. auto.
Qed.

Theorem sSoundness : forall Γ Δ, spair_der (Γ, Δ) -> (glob_conseq Γ Δ).
Proof.
intros Γ Δ gpair. destruct gpair. simpl in H. destruct H. destruct H0.
apply sSoundness1 in H1. simpl in H1. intro. intros.
induction x.
- simpl in H1. exfalso. simpl in H0.
  assert (J1: forall A : form, In form Γ A -> forall (u0 : nodes (domain:=D)), rho ⊩( u0) A).
  intros. apply H2. auto. pose (H1 _ _ rho J1 u). destruct e. destruct H3.
  inversion H3 ; subst. auto.
- assert (J1: forall A : form, In form Γ A -> forall (u0 : nodes (domain:=D)), rho ⊩( u0) A).
  intros. apply H2. auto.
  pose (H1 _ _ rho J1 u). destruct e. destruct H3. inversion H3. subst.
  simpl in H3. simpl in H4. destruct H4.
  * exists a. split. apply H0. apply in_eq. assumption.
  * apply list_disj_witn in H4. destruct H4. destruct H4. exists x0. split ; auto.
    apply H0. apply in_cons. assumption.
Qed.

End Soundness.


(* Consequences of soundness results. *)

Section ConseqSoundness.

Section DefModels.

Inductive UnDeux  : Type :=
 | Un : UnDeux
 | Deux : UnDeux.

Definition UDle (n m : UnDeux) : Prop :=
  match n with
   | Un => True
   | Deux => match m with
                   | Un => False
                   | Deux => True
                  end
  end.

Lemma UDle_refl : forall n, UDle n n.
Proof.
intros. destruct n ; unfold UDle ; auto.
Qed.

Lemma UDle_trans : forall n m k, (UDle n m) -> (UDle m k) -> (UDle n k).
Proof.
intros. destruct n ; unfold UDle ; auto. destruct k ; unfold UDle ; auto.
destruct m ; unfold UDle ; auto.
Qed.

Inductive UnDeuxTrois  : Type :=
 | UnDeux_I : UnDeux -> UnDeuxTrois
 | Trois : UnDeuxTrois.

Definition UDTle (n m : UnDeuxTrois) : Prop :=
  match n with
   | UnDeux_I k => match m with
                            | UnDeux_I l => UDle k l
                            | Trois => False
                           end
   | Trois => match m with
                   | UnDeux_I k => match k with
                                               | Un => False
                                               | Deux => True
                                              end
                   | Trois => True
                  end
  end.

Lemma UDTle_refl : forall n, UDTle n n.
Proof.
intros. destruct n ; unfold UDTle ; auto. apply UDle_refl.
Qed.

Lemma UDTle_trans : forall n m k, (UDTle n m) -> (UDTle m k) -> (UDTle n k).
Proof.
intros. destruct n ; unfold UDTle ; auto. destruct k ; unfold UDTle ; auto.
destruct m ; unfold UDTle ; auto. simpl in H. simpl in H0. apply (UDle_trans H H0) ; auto.
simpl in H0. destruct u0 ; simpl ; auto. inversion H0. simpl in H. inversion H.
destruct m ; auto. destruct k ; simpl ; auto. destruct u ; simpl ; auto.
destruct m ; auto. simpl in H0. simpl in H. destruct u ; auto.
Qed.

Inductive P1pred  : Type :=
 | P : P1pred.

Definition ar_P1pred (P : P1pred) : nat :=
  match P with
   | P1pred => 1
  end.

Instance preds_P1 : preds_signature :=
  {| preds := P1pred ; ar_preds := ar_P1pred  |}.

Context {Σ_funcs : funcs_signature}.

Variable domain : Type.

Context {I : interp domain}.
Variable assign : nat -> domain.

Definition k_P1 (n : UnDeux) (P1 : P1pred) :=
  match n with
    | Un => match P1 with
                   | P => (fun (v : Vector.t domain (ar_P1pred P)) => False)
                 end
    | Deux => match P1 with
                   | P => (fun (v : Vector.t domain (ar_P1pred P)) => True)
                 end
  end.

Lemma mon_P1 : forall u v,
  UDle u v -> forall P1 (t : Vector.t domain (ar_preds P1)), (@k_P1 u P1 t) -> (@k_P1 v P1 t).
Proof.
intros. destruct u.
- simpl in H0. destruct P1. inversion H0.
- simpl in H0. destruct P1. destruct v.
  + simpl. inversion H.
  + simpl. auto.
Qed.

Instance M0 : kmodel domain :=
      {|
        nodes := UnDeux ;

        reachable := UDle ;
        reach_refl u := UDle_refl u ;
        reach_tran u v w := @UDle_trans u v w ;

        k_interp := I ;
        k_P := k_P1 ;

        mon_P := mon_P1;
      |}.

Definition k_P1M2 (n : UnDeuxTrois) (P1 : P1pred) :=
  match n with
    | UnDeux_I n => match n with
                                | Un => match P1 with
                                               | P => (fun (v : Vector.t domain (ar_P1pred P)) => False)
                                             end
                                | Deux => match P1 with
                                               | P => (fun (v : Vector.t domain (ar_P1pred P)) => True)
                                             end
                                end
    | Trois => match P1 with
                   | P => (fun (v : Vector.t domain (ar_P1pred P)) => True)
                 end
  end.

Lemma mon_P1M2 : forall u v,
  UDTle u v -> forall P1 (t : Vector.t domain ((@ar_preds preds_P1)  P1)), (@k_P1M2 u P1 t) -> (@k_P1M2 v P1 t).
Proof.
intros. destruct u.
- destruct P1. destruct u. simpl in H0. inversion H0. simpl in H0.
  destruct v ; auto. simpl. destruct u ; auto.
- destruct P1. simpl in H0. destruct v ; simpl ; auto. destruct u ; simpl ; auto.
Qed.

Instance M2 : @kmodel Σ_funcs preds_P1 domain :=
      {|
        nodes := UnDeuxTrois ;

        reachable := UDTle ;
        reach_refl u := UDTle_refl u ;
        reach_tran u v w := @UDTle_trans u v w ;

        k_interp := I ;
        k_P := k_P1M2 ;

        mon_P := mon_P1M2;
      |}.

Inductive PQ1pred  : Type :=
 | P1pred_I : P1pred -> PQ1pred
 | Q : PQ1pred.

Definition ar_PQ1pred (R : PQ1pred) : nat :=
  match R with
   | P1pred_I P => 1
   | Q => 1
  end.

Instance preds_PQ1 : preds_signature :=
  {| preds := PQ1pred ; ar_preds := ar_PQ1pred  |}.


Definition k_PQ1 (n : UnDeuxTrois) (PQ1 : PQ1pred) :=
  match n with
    | UnDeux_I n => match n with
                                | Un => match PQ1 with
                                               | P1pred_I P => (fun (v : Vector.t domain (ar_PQ1pred (P1pred_I P))) => True)
                                               | Q => (fun (v : Vector.t domain (ar_PQ1pred Q)) => False)
                                             end
                                | Deux => match PQ1 with
                                               | P1pred_I P => (fun (v : Vector.t domain (ar_PQ1pred (P1pred_I P))) => True)
                                               | Q => (fun (v : Vector.t domain (ar_PQ1pred Q)) => True)
                                             end
                                end
    | Trois => match PQ1 with
                   | P1pred_I P => (fun (v : Vector.t domain (ar_PQ1pred (P1pred_I P))) => True)
                   | Q => (fun (v : Vector.t domain (ar_PQ1pred Q)) => True)
                 end
  end.

Lemma mon_PQ1 : forall u v,
  UDTle u v -> forall PQ1 (t : Vector.t domain (ar_preds PQ1)), (@k_PQ1 u PQ1 t) -> (@k_PQ1 v PQ1 t).
Proof.
intros. destruct u.
- destruct PQ1.
  + destruct u. destruct p. simpl in H0. destruct v ; auto. simpl. destruct u ; auto.
     destruct p. simpl in H0. destruct v ; auto. simpl. destruct u ; auto.
  + destruct v ; simpl ; auto. destruct u0 ; auto. simpl in H0. destruct u ; auto.
- destruct PQ1.
  + destruct p. simpl in H0. destruct v ; simpl ; auto. destruct u ; simpl ; auto.
  + simpl in H0. destruct v ; simpl ; auto. destruct u ; simpl ; auto.
Qed.

Instance M1 : kmodel domain :=
      {|
        nodes := UnDeuxTrois ;

        reachable := UDTle ;
        reach_refl u := UDTle_refl u ;
        reach_tran u v w := @UDTle_trans u v w ;

        k_interp := I ;
        k_P := k_PQ1 ;

        mon_P := mon_PQ1;
      |}.

End DefModels.



Section Counterexamples.

Context {Σ_funcs : funcs_signature}.
Variable domain : Type.
Context {I : interp domain}.
Variable assign : nat -> domain.

(* sFOBIL is not a subset of wFOBIL. *)

Lemma Consequences_Soundness1 :
  exists (s : prod (Ensemble (@form Σ_funcs preds_P1 _)) (@form Σ_funcs preds_P1 _)), (FOsBIH_rules s) /\ ((FOwBIH_rules s) -> False).
Proof.
exists (Singleton (@form Σ_funcs preds_P1 _)  (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))),
¬ ∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _)))).
split.
- apply DNs with (ps:=[(Singleton (@form Σ_funcs preds_P1 _)  (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))),
  (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))))]).
  2: apply DNsRule_I. intros. inversion H ; subst. 2: inversion H0.
  apply Ids. apply IdRule_I. apply In_singleton.
- intro. apply wSoundness0 in H. simpl in H. unfold kvalid_ctx in H.
  pose (H domain (@M0 Σ_funcs domain I) Deux assign).
  assert (J0: @ksat  Σ_funcs preds_P1 domain (@M0 Σ_funcs domain I) Deux assign (¬ (∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _)))))).
  { apply k. intros. inversion H0. subst. simpl. auto. }
  pose (J0 Deux Logic.I). simpl in k0. apply k0. exists Un. repeat split ; auto.
Qed.

(* Failure of deduction theorem for FOsBIL *)

Lemma Consequences_Soundness2 :
  (FOsBIH_rules (Singleton (@form Σ_funcs preds_P1 _)  (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))),
  ¬ ∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))))) /\
  ((FOsBIH_rules (Empty_set (@form Σ_funcs preds_P1 _),
  (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))) --> (¬ ∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _)))))) -> False).
Proof.
split.
- apply DNs with (ps:=[(Singleton (@form Σ_funcs preds_P1 _)  (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))),
  (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))))]).
  2: apply DNsRule_I. intros. inversion H ; subst. 2: inversion H0.
  apply Ids. apply IdRule_I. apply In_singleton.
- intro. apply sSoundness1 in H. simpl in H. unfold glob_conseq in H.
   assert (J0: (forall A : (@form Σ_funcs preds_P1 _), In (@form Σ_funcs preds_P1 _) (Empty_set (@form Σ_funcs preds_P1 _)) A ->
    forall u : UnDeux, @ksat  Σ_funcs preds_P1 domain (@M0 Σ_funcs domain I) u assign A)).
  { intros. inversion H0. }
  pose (H domain (@M0 Σ_funcs domain I) assign J0 Deux).
  destruct e. destruct H0. inversion H0. subst. clear H0.
  pose (H1 Deux Logic.I Logic.I Deux Logic.I). simpl in k.
  apply k. exists Un. repeat split ; auto.
Qed.

(* DMP fails in FOsBIL. *)

Lemma Consequences_Soundness3 :
  (spair_der
  (Singleton (@form Σ_funcs preds_PQ1 _)  (@atom Σ_funcs preds_PQ1 _ (P1pred_I P) (Vector.cons _ ($0) _ (Vector.nil _))),
   Union (@form Σ_funcs preds_PQ1 _)
   (Singleton (@form Σ_funcs preds_PQ1 _)  (@atom Σ_funcs preds_PQ1 _ Q (Vector.cons _ ($0) _ (Vector.nil _))))
   (Singleton (@form Σ_funcs preds_PQ1 _)  (¬ ∞ ∞ (@atom Σ_funcs preds_PQ1 _ Q (Vector.cons _ ($0) _ (Vector.nil _)))))))
  -> False.
Proof.
intro. apply sSoundness in H. unfold glob_conseq in H.
assert (J0: (forall A : form,
    In form (Singleton form (@atom Σ_funcs preds_PQ1 _ (P1pred_I P) (Vector.cons term $0 0 (Vector.nil term)))) A ->
    forall u : nodes (domain:=domain), @ksat  Σ_funcs preds_PQ1 domain (@M1 Σ_funcs domain I) u assign A)).
{ intros. inversion H0. subst. destruct u ; simpl ; auto.
  destruct u ; simpl ; auto. }
pose (H domain (@M1 Σ_funcs domain I) assign J0 (UnDeux_I Un)).
destruct e. destruct H0. clear H. inversion H0.
subst. inversion H. subst. simpl in H1. inversion H1.
subst. inversion H. subst. clear H0.
pose (H1 (UnDeux_I Deux) Logic.I).
simpl in k. apply k. exists Trois. repeat split ; auto.
intro. destruct H0. destruct H0. destruct H2.
apply H3. destruct x. destruct u ; simpl ; auto.
simpl. auto.
Qed.

(* Validity on rooted models. *)

Lemma Rooted_models_validity : forall (M : @kmodel Σ_funcs preds_P1 domain),
  (exists (r : @nodes Σ_funcs preds_P1 domain M), forall w, (@reachable Σ_funcs preds_P1 domain M r w)) ->
  (forall w, (@ksat  Σ_funcs preds_P1 domain M w assign
  (∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))) ∨ ¬ ∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _)))))).
Proof.
intros. destruct H.
destruct (classic (@ksat  Σ_funcs preds_P1 domain M x assign (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))))).
- right. simpl. intros. destruct H2. destruct H2. destruct H3. apply H4.
  apply (@mon_P Σ_funcs preds_P1 domain M x) ; auto.
- left. simpl. exists x. repeat split ; auto.
Qed.

(* Validity on rooted models, falsified on general models. *)

Lemma Consequences_Soundness4 :
  (FOsBIH_rules (Empty_set (@form Σ_funcs preds_P1 _),
  ∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _))) ∨ ¬ ∞ (@atom Σ_funcs preds_P1 _ P (Vector.cons _ ($0) _ (Vector.nil _)))))
  -> False.
Proof.
intro. apply sSoundness1 in H. unfold glob_conseq in H.
assert (J0: (forall A : (@form Σ_funcs preds_P1 _), In (@form Σ_funcs preds_P1 _) (Empty_set (@form Σ_funcs preds_P1 _)) A ->
forall u : UnDeuxTrois, @ksat  Σ_funcs preds_P1 domain (@M2 Σ_funcs domain I) u assign A)).
{ intros. inversion H0. }
pose (H domain (@M2 Σ_funcs domain I)  assign J0 Trois).
destruct e. destruct H0. clear H. simpl in H0. inversion H0.
subst. inversion H1.
- simpl in H. destruct H. destruct H. destruct H2. apply H3.
  destruct x. simpl. destruct u ; simpl ; auto. simpl. auto.
- pose (H (UnDeux_I Deux) Logic.I). simpl in k.
  apply k. exists (UnDeux_I Un). repeat split ; auto.
Qed.

End Counterexamples.

End ConseqSoundness.
