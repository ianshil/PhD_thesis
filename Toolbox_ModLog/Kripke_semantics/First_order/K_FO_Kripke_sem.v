(* * Kripke Semantics *)

Require Import K_FO_Syntax.
Local Set Impicit Arguments.
Local Unset Strict Impicit.

Require Import Coq.Vectors.Vector.
Local Notation vec := Vector.t.
Require Import Ensembles.

Section Semantics.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

    Variable D : Type.

    Class interp_fun :=
      {
        i_func : forall f : syms, vec D (ar_syms f) -> D
      }.

    Definition assign := nat -> D.

    Context {I : interp_fun}.

    Fixpoint eval (alpha : assign) (t : term) : D :=
      match t with
      | var s => alpha s
      | func f v => i_func f (Vector.map (eval alpha) v)
      end.

Lemma eval_ext alpha xi t :
      (forall x, alpha x = xi x) -> eval alpha t = eval xi t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

Lemma eval_comp alpha xi t :
      eval alpha (subst_term xi t) = eval (xi >> eval alpha) t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.

  End Semantics.

Section Kripke.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Section Model.

   Variable D : Type.

    Class FOkmodel :=
      {
        nodes : Type ;
        reachable : nodes -> nodes -> Prop ;
        k_interp : interp_fun D ;
        k_P : nodes -> forall P : preds, Vector.t D (ar_preds P) -> Prop
      }.

    Variable M : FOkmodel.

Fixpoint wforces w (alpha : assign D) (phi : kform) : Prop :=
      match phi with
      | atom P v => k_P w P (Vector.map (@eval _ D k_interp alpha) v)
      | Bot => False
      | bin Imp psi chi => wforces w alpha psi -> wforces w alpha chi
      | un Box psi => forall v, reachable w v -> wforces v alpha psi
      | quant All psi => forall j, wforces w (j .: alpha) psi
      | quant Ex psi => exists j, wforces w (j .: alpha) psi
      end.

Definition mforces alpha phi : Prop := forall w, wforces w alpha phi.

  End Model.

  Notation "alpha  '⊩(' u ')'  phi" := (wforces u alpha phi) (at level 20).
  Notation "alpha '⊩(' u , M ')' phi" := (@wforces _ M u alpha phi) (at level 20).



  Section Substs.

    Variable D : Type.
    Context {M : FOkmodel D}.

Ltac comp := repeat (progress (cbn in *; autounfold in *)).

    Lemma wforces_ext u alpha xi phi :
      (forall x, alpha x = xi x) -> alpha ⊩(u,M) phi <-> xi ⊩(u,M) phi.
    Proof.
      induction phi as [ | |  | | ] in alpha, xi, u |-* ; intros Hext ; comp ; try tauto.
      - erewrite Vector.map_ext. reflexivity. intros a. now apply eval_ext.
      - destruct u0 ; split.
        * intros. apply H in H0. pose (IHphi v alpha xi Hext). apply i in H0. auto.
        * intros. apply H in H0. pose (IHphi v alpha xi Hext). apply i in H0. auto.
      - destruct b; split.
        * intros. pose (IHphi1 u _ _ Hext). apply i in H0. apply H in H0.
          pose (IHphi2 u _ _ Hext). apply i0 in H0. auto.
        * intros. pose (IHphi1 u _ _ Hext). apply i in H0. apply H in H0.
          pose (IHphi2 u _ _ Hext). apply i0 in H0. auto.
      - destruct q ; split. 1-2: intros H d; apply (IHphi _ (d .: alpha) (d .: xi)). all: ((intros []; cbn; congruence) + auto).
        1-2: intro H ; destruct H ; exists x ; apply (IHphi _ (x .: alpha) (x .: xi)). all: ((intros []; cbn; congruence) + auto).
    Qed.

    Lemma wforces_comp u alpha xi phi :
      alpha ⊩(u,M) phi[xi] <-> (xi >> eval D alpha (I := @k_interp _ M)) ⊩(u,M) phi.
    Proof.
      induction phi in alpha, xi, u |-*; comp ; try tauto.
      - erewrite Vector.map_map. erewrite Vector.map_ext. reflexivity. apply eval_comp.
      - destruct u0. now setoid_rewrite IHphi.
      - destruct b. setoid_rewrite IHphi1 ; now setoid_rewrite IHphi2.
      - destruct q ; setoid_rewrite IHphi. split; intros H d; eapply wforces_ext. 2, 4: apply (H d).
        1-2: intros []; cbn ; trivial ; unfold funcomp ; now erewrite eval_comp.
        split ; intros ; destruct H ; exists x ; eapply wforces_ext. 2,4: apply H.
        1-2:intros []; cbn; trivial; unfold funcomp; now erewrite eval_comp.
    Qed.

  End Substs.


Section Conseq_Rel.

Definition loc_conseq Γ A :=
  forall D (M : FOkmodel D) w alpha,
     (forall (B : kform), In _ Γ B -> wforces D M w alpha B) -> wforces D M w alpha A.

Definition glob_conseq Γ A :=
    forall D (M : FOkmodel D) alpha,
    (forall B, In _ Γ B -> mforces D M alpha B) ->
    (mforces D M alpha A).


   Definition kvalid_ctx A phi :=
    forall D (M : FOkmodel D) u alpha, (forall psi, In _ A psi -> wforces _ _ u alpha psi) -> wforces _ _ u alpha phi.

  Definition kvalid phi :=
    forall D (M : FOkmodel D) u alpha, wforces _ _ u alpha phi.

  Definition wforcesis phi :=
    exists D (M : FOkmodel D) u alpha, wforces _ _ u alpha phi.

End Conseq_Rel.


End Kripke.

Notation "alpha  '⊩(' u ')'  phi" := (wforces u alpha phi) (at level 20).
Notation "alpha '⊩(' u , M ')' phi" := (@wforces _ _ _ M _ u alpha phi) (at level 20).






