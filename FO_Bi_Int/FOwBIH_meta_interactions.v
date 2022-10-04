Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_remove_list.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_logics.
Require Import FO_BiInt_extens_interactions.

Section wMeta.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.


Lemma wThm_irrel : forall A B Γ, FOwBIH_rules (Γ, A --> (B --> A)).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ,((A ∧ B) --> A) --> (A --> (B --> A)));(Γ, ((A ∧ B) --> A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply Ax. apply AxRule_I. apply RA9_I. exists A. exists B. exists A. auto.
inversion H0. subst. apply Ax.
apply AxRule_I. apply RA5_I. exists A. exists B. auto. inversion H1.
Qed.

Lemma wimp_Id_gen : forall A Γ, FOwBIH_rules (Γ, A --> A).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, ((A ∧ A) --> A) --> (A --> A)); (Γ, ((A ∧ A) --> A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((((A ∧ A) --> A) ∧ A) --> A) --> ((A ∧ A) --> A) --> (A --> A)); (Γ, (((A ∧ A) --> A) ∧ A) --> A)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA9_I.
exists ((A ∧ A) --> A). exists A. exists A. auto. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA6_I.
exists ((A ∧ A) --> A). exists A. auto. inversion H2. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists A. exists A. auto. inversion H1.
Qed.

Lemma comm_And_obj : forall A B Γ,
    (FOwBIH_rules (Γ, (A ∧ B) --> (B ∧ A))).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ, ((A ∧ B) --> A) --> ((A ∧ B) --> (B ∧ A)));(Γ, ((A ∧ B) --> A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((A ∧ B) --> B) --> ((A ∧ B) --> A) --> ((A ∧ B) --> (B ∧ A)));(Γ, ((A ∧ B) --> B))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists (A ∧ B). exists B. exists A.
auto. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists A. exists B. auto. inversion H2.
inversion H0. subst. apply Ax. apply AxRule_I. apply RA5_I. exists A. exists B. auto.
inversion H1.
Qed.

Lemma wContr_Bot : forall A Γ, FOwBIH_rules (Γ, (A ∧ ¬ A) --> ⊥).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, (((¬ A) ∧ A) --> ⊥) --> ((A ∧ ¬ A) --> ⊥));(Γ, ((¬ A) ∧ A )--> ⊥)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((A ∧ ¬ A) --> ((¬ A) ∧ A )) --> (((¬ A) ∧ A ) --> ⊥) --> ((A ∧ ¬ A) --> ⊥));(Γ, (A ∧ ¬ A) --> ((¬ A) ∧ A ))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (A ∧ ¬ A). exists ((¬ A) ∧ A ). exists (⊥). auto. inversion H1.
subst. apply comm_And_obj. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ, ((¬ A) --> A --> ⊥) --> (((¬ A) ∧ A )  --> ⊥));(Γ, ((¬ A) --> A --> ⊥))]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
apply AxRule_I. apply RA8_I. exists (¬ A). exists A. exists (⊥). auto. inversion H2.
subst. 2: inversion H3. 2: inversion H1. apply wimp_Id_gen.
Qed.

Lemma wmonotR_Or : forall A B Γ,
    (FOwBIH_rules (Γ, A --> B)) ->
    (forall C, FOwBIH_rules (Γ, (A ∨ C) --> (B ∨ C))).
Proof.
intros A B Γ D C.
apply MP with (ps:=[(Γ, (C --> (B ∨ C)) --> ((A ∨ C) --> (B ∨ C)));(Γ,(C --> (B ∨ C)))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A --> (B ∨ C)) --> (C --> (B ∨ C)) --> ((A ∨ C) --> (B ∨ C)));(Γ,(A --> (B ∨ C)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists C.
exists ((B ∨ C)). auto. inversion H1. subst.
apply MP with (ps:=[(Γ, (B --> (B ∨ C)) --> (A --> (B ∨ C)));(Γ,((B --> (B ∨ C))))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, (A --> B) --> (B --> (B ∨ C)) --> (A --> (B ∨ C)));(Γ,(A --> B))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists A. exists B. exists ((B ∨ C)). auto.
inversion H4. subst. assumption. inversion H5. inversion H3. subst. apply Ax.
apply AxRule_I. apply RA2_I. exists B. exists C.
auto. inversion H4. inversion H2. inversion H0. subst. apply Ax. apply AxRule_I. apply RA3_I.
exists B. exists C. auto. inversion H1.
Qed.

Lemma wmonotL_Or : forall A B Γ,
    (FOwBIH_rules (Γ, A --> B)) ->
    (forall C, FOwBIH_rules (Γ, (C ∨ A) --> (C ∨ B))).
Proof.
intros A B Γ D C.
apply MP with (ps:=[(Γ, (A --> (C ∨ B)) --> ((C ∨ A) --> (C ∨ B)));(Γ,(A --> (C ∨ B)))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (C --> (C ∨ B)) --> (A --> (C ∨ B)) --> ((C ∨ A) --> (C ∨ B)));(Γ,(C --> (C ∨ B)))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA4_I. exists C. exists A.
exists (C ∨ B). auto. inversion H1. subst. apply Ax.
apply AxRule_I. apply RA2_I. exists C. exists B.
auto. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ, (B --> (C ∨ B)) --> (A --> (C ∨ B)));(Γ,((B --> (C ∨ B))))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply MP with (ps:=[(Γ, (A --> B) --> (B --> (C ∨ B)) --> (A --> (C ∨ B)));(Γ,(A --> B))]).
2: apply MPRule_I. intros. inversion H2. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists A. exists B. exists (C ∨ B). auto. inversion H3. subst.
assumption. inversion H4. inversion H2. subst. apply Ax.
apply AxRule_I. apply RA3_I. exists C. exists B.
auto. inversion H3. inversion H1.
Qed.

Lemma comm_Or_obj : forall A B Γ, (FOwBIH_rules (Γ, (A ∨ B) --> (B ∨ A))).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ, (B --> (B ∨ A)) --> ((A ∨ B) --> (B ∨ A)));(Γ, (B --> (B ∨ A)))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A --> (B ∨ A)) --> (B --> (B ∨ A)) --> ((A ∨ B) --> (B ∨ A)));(Γ, (A --> (B ∨ A)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists B. exists ((B ∨ A)).
auto. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists B. exists A. auto.
inversion H2. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists B. exists A. auto.
inversion H1.
Qed.

Lemma comm_Or : forall A B Γ, (FOwBIH_rules (Γ, (A ∨ B))) -> (FOwBIH_rules (Γ, (B ∨ A))).
Proof.
intros A B Γ D.
apply MP with (ps:=[(Γ, (A ∨ B) --> (B ∨ A));(Γ, (A ∨ B))]).
2: apply MPRule_I. intros. inversion H. subst. apply comm_Or_obj.
inversion H0. subst. assumption. inversion H1.
Qed.

Lemma wmonot_Or2 : forall A B Γ, (FOwBIH_rules (Γ, A --> B)) ->
    (forall C, FOwBIH_rules (Γ, ((A ∨ C)) --> (C ∨ B))).
Proof.
intros A B Γ D C.
apply MP with (ps:=[(Γ, (C --> (C ∨ B)) --> ((A ∨ C) --> (C ∨ B)));(Γ, C --> (C ∨ B))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A --> (C ∨ B)) --> (C --> (C ∨ B)) --> ((A ∨ C) --> (C ∨ B)));(Γ, A --> (C ∨ B))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax.
apply AxRule_I. apply RA4_I. exists A. exists C. exists (C ∨ B). auto.
inversion H1. subst.
apply MP with (ps:=[(Γ, (B --> (C ∨ B)) --> (A --> (C ∨ B)));(Γ, B --> (C ∨ B))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, (A --> B) --> (B --> (C ∨ B)) --> (A --> (C ∨ B)));(Γ, A --> B)]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists B. exists (C ∨ B).
auto. inversion H4. subst. assumption. inversion H5. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists C. exists B. auto. inversion H4.
inversion H2. inversion H0. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists C. exists B. auto. inversion H1.
Qed.

Theorem wdual_residuation0 : forall A B C,
  (FOwBIH_rules (Empty_set _, (A --< B) --> C) ->
      FOwBIH_rules (Empty_set _, A --> ((B ∨ C)))).
Proof.
intros A B C D. pose (@wmonot_Or2 (A --< B) C (Empty_set _) D B).
apply MP with (ps:=[(Empty_set _, (((A --< B) ∨ B) --> (B ∨ C)) --> (A --> (B ∨ C)));(Empty_set _,((A --< B) ∨ B) --> (B ∨ C))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Empty_set _, (A --> ((A --< B) ∨ B)) --> (((A --< B) ∨ B) --> (B ∨ C)) --> (A --> (B ∨ C)));(Empty_set _,(A --> ((A --< B) ∨ B)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (((A --< B) ∨ B)). exists ((B ∨ C)). auto.
inversion H1. subst.
apply MP with (ps:=[(Empty_set _, ((B ∨ (A --< B)) --> ((A --< B) ∨ B)) --> (A --> ((A --< B) ∨ B)));(Empty_set _,((B ∨ (A --< B)) --> ((A --< B) ∨ B)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Empty_set _, (A --> (B ∨ (A --< B))) --> ((B ∨ (A --< B)) --> ((A --< B) ∨ B)) --> (A --> ((A --< B) ∨ B)));(Empty_set _,(A --> (B ∨ (A --< B))))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists A. exists ((B ∨ (A --< B))). exists (((A --< B) ∨ B)).
auto. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA11_I. exists A. exists B. auto. inversion H5.
inversion H3. subst. apply comm_Or_obj. inversion H4. inversion H2. inversion H0.
subst. assumption. inversion H1.
Qed.

Lemma wTop : forall Γ, FOwBIH_rules (Γ, ⊤).
Proof.
intros. apply MP with (ps:=[(Γ, (⊤ --> ⊤) --> ⊤);(Γ, ⊤ --> ⊤)]). 2: apply MPRule_I.
intros. inversion H. subst. apply Ax. apply AxRule_I. apply RA15_I. exists (⊤ --> ⊤). auto.
inversion H0. 2: inversion H1. subst. apply wimp_Id_gen.
Qed.

Lemma wDN_to_form : forall A Γ, (FOwBIH_rules (Γ, (¬ (∞ A)) --> A)).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, ⊤  --> (¬ (∞ A)) --> A);(Γ, ⊤)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((⊤ ∧ ¬ ∞ A) --> A) --> (⊤ --> ((¬ (∞ A))) --> A));(Γ, ((⊤ ∧ ¬ ∞ A) --> A))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
apply RA9_I. exists ⊤. exists (¬ (∞ A)). exists A. auto.
inversion H1. subst.
apply MP with (ps:=[(Γ, (((¬ ∞ A) ∧ ⊤)--> A) --> ((⊤ ∧ ¬ ∞ A) --> A));(Γ, ((¬ ∞ A) ∧ ⊤)--> A)]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, ((⊤ ∧ ¬ ∞ A) --> ((¬ ∞ A) ∧ ⊤)) --> (((¬ ∞ A) ∧ ⊤)--> A) --> ((⊤ ∧ ¬ ∞ A) --> A));
(Γ, ((⊤ ∧ ¬ ∞ A) --> ((¬ ∞ A) ∧ ⊤)))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (⊤ ∧ ¬ ∞ A). exists ((¬ ∞ A) ∧ ⊤).
exists A. auto. inversion H4. subst.
apply MP with (ps:=[(Γ, ((⊤ ∧ ¬ ∞ A) --> ⊤) --> (⊤ ∧ ¬ ∞ A) --> ((¬ ∞ A) ∧ ⊤));
(Γ, (⊤ ∧ ¬ ∞ A) --> ⊤)]). 2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, ((⊤ ∧ ¬ ∞ A) --> ¬ ∞ A) --> ((⊤ ∧ ¬ ∞ A) --> ⊤) --> (⊤ ∧ ¬ ∞ A) --> ((¬ ∞ A) ∧ ⊤));
(Γ, (⊤ ∧ ¬ ∞ A) --> ¬ ∞ A)]). 2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists (⊤ ∧ ¬ ∞ A).
exists (¬ ∞ A). exists ⊤. auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists ⊤.
exists (¬ (∞ A)). auto. inversion H8. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists ⊤.
exists (¬ (∞ A)). auto. inversion H7. inversion H5. inversion H3. subst.
apply MP with (ps:=[(Γ, ((¬ (∞ A)) --> ⊤ --> A) --> ((¬ (∞ A)) ∧ ⊤) --> A);
(Γ, ((¬ (∞ A)) --> ⊤ --> A))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA8_I. exists (¬ (∞ A)).
exists ⊤. exists A. auto. inversion H5. subst.
apply MP with (ps:=[(Γ, (((∞ A) --> (⊥)) --> ⊤ --> A) --> ((¬ (∞ A)) --> ⊤ --> A));
(Γ, (((∞ A) --> (⊥)) --> ⊤ --> A))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply MP with (ps:=[(Γ, ((¬ (∞ A)) --> ((∞ A) --> (⊥))) --> (((∞ A) --> (⊥)) --> ⊤ --> A) --> ((¬ (∞ A)) --> ⊤ --> A));
(Γ, (¬ (∞ A)) --> ((∞ A) --> (⊥)))]). 2: apply MPRule_I. intros. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (¬ (∞ A)).
exists (∞ A --> ⊥). exists (⊤ --> A). auto. inversion H8. subst.
apply wimp_Id_gen. inversion H9.
inversion H7. subst.
apply MP with (ps:=[(Γ, (((⊤ --< A) --> ⊥) --> ⊤ --> A) --> (∞ A --> ⊥) --> ⊤ --> A);(Γ, ((⊤ --< A) --> ⊥) --> ⊤ --> A)]).
2: apply MPRule_I. intros. inversion H8. subst.
apply MP with (ps:=[(Γ, ((∞ A --> ⊥) --> ((⊤ --< A) --> ⊥)) --> (((⊤ --< A) --> ⊥) --> ⊤ --> A) --> (∞ A --> ⊥) --> ⊤ --> A);
(Γ, (∞ A --> ⊥) --> ((⊤ --< A) --> ⊥))]).
2: apply MPRule_I. intros. inversion H9. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists (∞ A --> ⊥). exists ((⊤ --< A) --> ⊥).
exists (⊤ --> A). auto. inversion H10. subst.
apply MP with (ps:=[(Γ, ((⊤ --< A) --> (∞ A)) --> ((∞ A --> ⊥) --> (⊤ --< A) --> ⊥));(Γ, ((⊤ --< A) --> (∞ A)))]).
2: apply MPRule_I. intros. inversion H11. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (⊤ --< A). exists (∞ A). exists (⊥). auto. inversion H12. subst.
apply wimp_Id_gen.
inversion H13. inversion H11. inversion H9. subst.
apply MP with (ps:=[(Γ, (¬ (⊤ --< A) --> ⊤ --> A) --> (((⊤ --< A) --> ⊥) --> ⊤ --> A));(Γ, (¬ (⊤ --< A) --> ⊤ --> A))]).
2: apply MPRule_I. intros. inversion H10. subst.
apply MP with (ps:=[(Γ, (((⊤ --< A) --> ⊥) --> ¬ (⊤ --< A)) --> (¬ (⊤ --< A) --> ⊤ --> A) --> (((⊤ --< A) --> ⊥) --> ⊤ --> A));
(Γ, ((⊤ --< A) --> ⊥) --> ¬ (⊤ --< A))]).
2: apply MPRule_I. intros. inversion H11. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists ((⊤ --< A) --> ⊥). exists (¬ (⊤ --< A)).
exists (⊤ --> A). auto. inversion H12. subst.
apply wimp_Id_gen.
inversion H13. inversion H11. subst. apply Ax. apply AxRule_I.
apply RA14_I. exists ⊤. exists A. auto. inversion H12. inversion H10.
inversion H8. inversion H6. inversion H4. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ, (A --> A) --> ⊤);(Γ, A --> A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA15_I. exists (A --> A). auto. inversion H2.
subst. apply wimp_Id_gen. inversion H3. inversion H1.
Qed.

Lemma wEFQ : forall A Γ, FOwBIH_rules (Γ, ⊥ --> A).
Proof.
intros A Γ. apply Ax. apply AxRule_I. apply RA16_I. exists A. auto.
Qed.

Lemma absorp_Or1 : forall A Γ,
    (FOwBIH_rules (Γ, A ∨ ⊥)) ->
    (FOwBIH_rules (Γ, A)).
Proof.
intros A Γ D.
apply MP with (ps:=[(Γ, (A ∨ ⊥) --> A);(Γ, A ∨ ⊥)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (⊥ --> A) --> ((A ∨ ⊥) --> A));(Γ, (⊥ --> A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A --> A) --> (⊥ --> A) --> ((A ∨ ⊥) --> A));(Γ, A --> A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists (⊥).
exists A. auto. inversion H2. subst. apply wimp_Id_gen. inversion H3.
inversion H1. subst. apply wEFQ. inversion H2. inversion H0. subst.
assumption. inversion H1.
Qed.

Lemma absorp_Or2 : forall A Γ,
    (FOwBIH_rules (Γ, ⊥ ∨ A)) ->
    (FOwBIH_rules (Γ, A)).
Proof.
intros A Γ D.
apply MP with (ps:=[(Γ, (⊥ ∨ A) --> A);(Γ, ⊥ ∨ A)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A --> A) --> ((⊥ ∨ A) --> A));(Γ, (A --> A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (⊥ --> A) --> (A --> A) --> ((⊥ ∨ A) --> A));(Γ, ⊥ --> A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists ⊥. exists A.
exists A. auto. inversion H2. subst. apply wEFQ. inversion H1. inversion H3.
inversion H3. inversion H1. subst. apply wimp_Id_gen. inversion H2.
inversion H0. subst. assumption. inversion H1.
Qed.

Theorem wdual_residuation : forall A B C,
  (FOwBIH_rules (Empty_set _, (A --< B) --> C) ->
      FOwBIH_rules (Empty_set _, A --> ((B ∨ C)))) *
  (FOwBIH_rules (Empty_set _, A --> ((B ∨ C))) ->
      FOwBIH_rules (Empty_set _, (A --< B) --> C)).
Proof.
intros A B C. split.
- intro D. pose (@wmonot_Or2 (A --< B) C (Empty_set _) D B).
  apply MP with (ps:=[(Empty_set _, (((A --< B) ∨ B) --> (B ∨ C)) --> (A --> (B ∨ C)));(Empty_set _,((A --< B) ∨ B) --> (B ∨ C))]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Empty_set _, (A --> ((A --< B) ∨ B)) --> (((A --< B) ∨ B) --> (B ∨ C)) --> (A --> (B ∨ C)));(Empty_set _,(A --> ((A --< B) ∨ B)))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists (((A --< B) ∨ B)). exists ((B ∨ C)). auto.
  inversion H1. subst.
  apply MP with (ps:=[(Empty_set _, ((B ∨ (A --< B)) --> ((A --< B) ∨ B)) --> (A --> ((A --< B) ∨ B)));(Empty_set _,((B ∨ (A --< B)) --> ((A --< B) ∨ B)))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Empty_set _, (A --> (B ∨ (A --< B))) --> ((B ∨ (A --< B)) --> ((A --< B) ∨ B)) --> (A --> ((A --< B) ∨ B)));(Empty_set _,(A --> (B ∨ (A --< B))))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists ((B ∨ (A --< B))). exists (((A --< B) ∨ B)).
  auto. inversion H4. subst.
  apply Ax. apply AxRule_I. apply RA11_I. exists A. exists B. auto. inversion H5. inversion H3. subst. apply comm_Or_obj.
  inversion H4. inversion H2. inversion H0. subst. assumption. inversion H1.
- intro D. apply MP with (ps:=[(Empty_set _, ((C ∨ (A --< ((B ∨ C)))) --> C) --> ((A --< B) --> C));(Empty_set _, (C ∨ (A --< ((B ∨ C)))) --> C)]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Empty_set _, ((A --< B) --> (C ∨ (A --< ((B ∨ C))))) --> ((C ∨ (A --< ((B ∨ C)))) --> C) --> ((A --< B) --> C));(Empty_set _, (A --< B) --> (C ∨ (A --< ((B ∨ C)))))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists (A --< B). exists (C ∨ (A --< ((B ∨ C)))). exists C. auto. inversion H1. subst.
  apply MP with (ps:=[(Empty_set _, ((C ∨ ((A --< B) --< C)) --> (C ∨ (A --< ((B ∨ C))))) --> ((A --< B) --> (C ∨ (A --< ((B ∨ C))))));(Empty_set _, ((C ∨ ((A --< B) --< C)) --> (C ∨ (A --< ((B ∨ C))))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Empty_set _, ((A --< B) --> (C ∨ ((A --< B) --< C)))--> (C ∨ ((A --< B) --< C) --> C ∨ (A --< B ∨ C)) --> (A --< B) --> C ∨ (A --< B ∨ C));
  (Empty_set _, ((A --< B) --> (C ∨ ((A --< B) --< C))))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (A --< B). exists (C ∨ ((A --< B) --< C)).
  exists (C ∨ (A --< ((B ∨ C)))). auto. inversion H4. subst.
  apply Ax. apply AxRule_I. apply RA11_I. exists (A --< B). exists C. auto. inversion H5.
  inversion H3. subst. apply wmonotL_Or.
  apply Ax. apply AxRule_I. apply RA13_I.
  exists A. exists B. exists C. auto. inversion H4. inversion H2. inversion H0. subst. 2: inversion H1.
  apply MP with (ps:=[(Empty_set _, ((C ∨ ⊥) --> C) --> (C ∨ (A --< ((B ∨ C))) --> C));
  (Empty_set _, ((C ∨ ⊥) --> C))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply MP with (ps:=[(Empty_set _, (C ∨ (A --< ((B ∨ C))) --> (C ∨ ⊥)) --> ((C ∨ ⊥) --> C) --> (C ∨ (A --< ((B ∨ C))) --> C));
  (Empty_set _, (C ∨ (A --< ((B ∨ C))) --> (C ∨ ⊥)))]). 2: apply MPRule_I. intros. inversion H2. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (C ∨ (A --< ((B ∨ C)))).
  exists (C ∨ ⊥). exists C. auto. inversion H3. subst. apply wmonotL_Or.
  apply MP with (ps:=[(Empty_set _, (((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C))))) --> ⊥) --> ((A --< ((B ∨ C))) --> ⊥));
  (Empty_set _, (((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C))))) --> ⊥))]). 2: apply MPRule_I. intros. inversion H4. subst.
  apply MP with (ps:=[(Empty_set _, ((A --< ((B ∨ C))) --> ((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C)))))) --> (((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C))))) --> ⊥) --> ((A --< (B ∨ C)) --> ⊥));
  (Empty_set _, ((A --< ((B ∨ C))) --> ((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C)))))))]). 2: apply MPRule_I. intros. inversion H5. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (A --< ((B ∨ C))).
  exists ((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C))))). exists (⊥). auto. inversion H6. subst.
  apply MP with (ps:=[(Empty_set _, ((A --< (B ∨ C)) --> (¬ (∞ (A --> (B ∨ C))))) --> ((A --< (B ∨ C)) --> ((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C)))))));
  (Empty_set _, ((A --< (B ∨ C)) --> (¬ (∞ (A --> (B ∨ C))))))]). 2: apply MPRule_I. intros. inversion H7. subst.
  apply MP with (ps:=[(Empty_set _, ((A --< (B ∨ C)) --> (∞ (A --> (B ∨ C)))) --> ((A --< (B ∨ C)) --> (¬ (∞ (A --> (B ∨ C))))) --> ((A --< (B ∨ C)) --> ((∞ (A --> (B ∨ C))) ∧ (¬ (∞ (A --> (B ∨ C)))))));
  (Empty_set _, ((A --< (B ∨ C)) --> (∞ (A --> (B ∨ C)))))]). 2: apply MPRule_I. intros. inversion H8. subst.
  apply Ax. apply AxRule_I. apply RA7_I. exists ((A --< (B ∨ C))).
  exists (∞ (A --> (B ∨ C))). exists (¬ (∞ (A --> (B ∨ C)))). auto. inversion H9.
  subst. apply Ax. apply AxRule_I. apply RA12_I. exists A. exists ((B ∨ C)). auto.
  inversion H10. inversion H8. subst.
  apply MP with (ps:=[(Empty_set _, (¬ (∞ (A --> (B ∨ C)))) --> ((A --< (B ∨ C)) --> ¬ (∞ (A --> (B ∨ C)))));
  (Empty_set _, (¬ (∞ (A --> (B ∨ C)))))]). 2: apply MPRule_I. intros. inversion H9. subst.
  apply wThm_irrel. inversion H10. subst. apply DNw with (ps:=[(Empty_set _, A --> (B ∨ C))]).
  intros. inversion H11. subst. assumption. inversion H12. apply DNwRule_I.
  inversion H11.
  inversion H9. inversion H7. inversion H5. subst. apply wContr_Bot. inversion H6.
  inversion H4. inversion H2. subst.
  apply MP with (ps:=[(Empty_set _, (⊥ --> C) --> ((C ∨ ⊥) --> C));(Empty_set _, (⊥ --> C))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(Empty_set _, (C --> C) --> (⊥ --> C) --> ((C ∨ ⊥) --> C));(Empty_set _, (C --> C))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Ax.
  apply AxRule_I. apply RA4_I. exists C. exists (⊥). exists C. auto.
  inversion H5. subst. apply wimp_Id_gen. inversion H6. inversion H4. subst.
  apply wEFQ. inversion H5. inversion H3.
Qed.

Lemma wAThm_irrel : forall A B Γ, FOwBIH_rules (Γ, (A --< B) --> A).
Proof.
intros A B Γ. pose (FOwBIH_monot (Empty_set _, (A --< B) --> A)). simpl in f.
assert (FOwBIH_rules (Empty_set _, (A --< B) --> A)).
apply wdual_residuation. apply Ax. apply AxRule_I.
apply RA3_I. exists B. exists A. auto. apply f with (Γ1:= Γ) in H.
auto. intro. intro. inversion H0.
Qed.

Theorem wdual_residuation_gen : forall A B C,
  (wpair_der (Empty_set _, Singleton _ ((A --< B) --> C)  ) ->
      wpair_der (Empty_set _, Singleton _ (A --> ((B ∨ C))))) *
  (wpair_der (Empty_set _, Singleton _ (A --> ((B ∨ C)))) ->
      wpair_der (Empty_set _, Singleton _ ((A --< B) --> C))).
Proof.
intros A B C. split.
- intro. exists [(A --> (B ∨ C))]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. simpl. apply In_singleton. inversion H1.
  * destruct H. destruct H. pose (wdual_residuation A B C). destruct p. simpl.
    simpl in f. simpl in f0. simpl in H0. destruct H0. destruct x.
    + simpl in H1. apply MP with (ps:=[(Empty_set _, ⊥ --> ((A --> (B ∨ C)) ∨ ⊥));(Empty_set _, ⊥)]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax.
      apply AxRule_I. apply RA3_I. exists (A --> (B ∨ C)). exists (⊥). auto.
      inversion H3. subst. assumption. inversion H4.
    + assert (x=nil). inversion H. subst. assert (f1 = ((A --< B) --> C)). pose (H0 f1).
      assert (List.In f1 (f1 :: x)). apply in_eq. apply i in H2. inversion H2. subst. auto.
      subst. destruct x. reflexivity. exfalso. apply H4. pose (H0 f1).
      assert (List.In f1 ((A --< B) --> C :: f1 :: x)). apply in_cons. apply in_eq.
      apply i in H2. inversion H2. subst. apply in_eq. subst.
      assert (f1 = (A --< B) --> C).
      pose (H0 f1). assert (List.In f1 (f1 :: nil)). apply in_eq. apply i in H2. inversion H2. auto.
      subst. apply absorp_Or1 in H1. apply f in H1.
      apply MP with (ps:=[(Empty_set _, (A --> (B ∨ C)) --> ((A --> (B ∨ C)) ∨ ⊥));(Empty_set _, (A --> (B ∨ C)))]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I.
      exists (A --> (B ∨ C)). exists (⊥). auto. inversion H3. subst. assumption.
      inversion H4.
- intro. exists  [((A --< B) --> C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. simpl. apply In_singleton. inversion H1.
  * destruct H. destruct H. pose (wdual_residuation A B C). destruct p. clear f. simpl.
    simpl in H0. simpl in f0. destruct H0. destruct x.
    + simpl in H1. apply MP with (ps:=[(Empty_set _, ⊥ --> (((A --< B) --> C) ∨ ⊥));(Empty_set _, ⊥)]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax.
      apply AxRule_I. apply RA3_I. exists ((A --< B) --> C). exists (⊥). auto.
      inversion H3. subst. assumption. inversion H4.
    + assert (x=nil). inversion H. subst. assert (f = (A --> (B ∨ C))). pose (H0 f).
      assert (List.In f (f :: x)). apply in_eq. apply i in H2. inversion H2 ; auto. subst.
      destruct x. reflexivity. exfalso. apply H4. pose (H0 f).
      assert (List.In f (A --> (B ∨ C) :: f :: x)). apply in_cons. apply in_eq.
      apply i in H2. inversion H2. subst. apply in_eq. subst.
      simpl in H1. assert (f = A --> (B ∨ C)).
      pose (H0 f). assert (List.In f (f :: nil)). apply in_eq. apply i in H2. destruct H2 ; auto. inversion H2.
      subst. apply absorp_Or1 in H1. apply f0 in H1.
      apply MP with (ps:=[(Empty_set _, ((A --< B) --> C) --> (((A --< B) --> C) ∨ ⊥));(Empty_set _, ((A --< B) --> C))]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I.
      exists ((A --< B) --> C). exists (⊥). auto. inversion H4. subst. assumption.
      inversion H5.
Qed.

Lemma wBiLEM : forall A Γ, FOwBIH_rules (Γ, A ∨ (∞ A)).
Proof.
intros.
pose (FOwBIH_monot (Empty_set _, A ∨ (∞ A))). assert (FOwBIH_rules (Empty_set _, A ∨ (∞ A))).
apply MP with (ps:=[(Empty_set _, ⊤ --> (A ∨ (⊤ --< A)));(Empty_set _, ⊤)]). 2: apply MPRule_I.
intros. inversion H. subst. apply wdual_residuation. apply wimp_Id_gen. inversion H0.
2: inversion H1. subst. apply wTop. apply f with (Γ1:=Γ) in H. auto.
intro ; intro ; inversion H0.
Qed.

Theorem FOwBIH_Detachment_Theorem0 : forall A B Γ,
           (FOwBIH_rules (Γ, A --> B)) ->
           (FOwBIH_rules  (Union _ Γ (Singleton _ A), B)).
Proof.
intros.
apply MP with (ps:=[(Union form Γ (Singleton form A), A --> B);(Union form Γ (Singleton form A), A)]).
2: apply MPRule_I. intros. inversion H0. subst.
apply FOwBIH_monot with (Γ1:=Union form Γ (Singleton form A)) in H. simpl in H. auto.
intro. intros. simpl in H1. apply Union_introl. auto. inversion H1. subst. 2: inversion H2.
apply Id. apply IdRule_I. apply Union_intror. apply In_singleton.
Qed.


Theorem FOwBIH_Detachment_Theorem : forall s,
           (FOwBIH_rules s) ->
           (forall A B Γ, (fst s = Γ) ->
                          (snd s = A --> B) ->
                          FOwBIH_rules  (Union _ Γ (Singleton _ A), B)).
Proof.
intros. destruct s. subst. simpl in H1. subst. simpl. apply FOwBIH_Detachment_Theorem0. auto.
Qed.

Theorem FOwBIH_Deduction_Theorem : forall s,
           (FOwBIH_rules s) ->
           (forall A B Γ, (fst s = Union form Γ (Singleton form A)) ->
                          (snd s = B) ->
                          FOwBIH_rules (Γ, A --> B)).
Proof.
intros s D. induction D.
(* Id *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. inversion H0.
  + subst. apply MP with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H2. subst.
    apply wThm_irrel. inversion H3. subst. apply Id. apply IdRule_I. assumption.
    inversion H4.
  + subst. inversion H1 ; subst. apply wimp_Id_gen.
(* Ax *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl.
  apply MP with (ps:=[(Γ, A0 --> A --> A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply wThm_irrel. inversion H2. subst.
  apply Ax. apply AxRule_I. assumption. inversion H3.
(* MP *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J20: List.In (Union form Γ (Singleton form A), A0 --> B0) ((Union form Γ (Singleton form A), A0 --> B0) :: (Union form Γ (Singleton form A), A0) :: nil)).
  apply in_eq. pose (H0 _ J20 A (A0 --> B0) Γ). assert (J50: FOwBIH_rules (Γ, A --> A0 --> B0)). apply f ; auto.
  apply MP with (ps:=[(Γ, ((A ∧ A0) --> B0) --> (A --> B0));(Γ, (A ∧ A0) --> B0)]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (A --> (A ∧ A0)) --> ((A ∧ A0) --> B0) --> (A --> B0));(Γ, A --> (A ∧ A0))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists ((A ∧ A0)). exists B0. auto.
  inversion H4. subst. 2: inversion H5.
  apply MP with (ps:=[(Γ, (A --> A0) --> (A --> (A ∧ A0)));(Γ, A --> A0)]).
  2: apply MPRule_I. intros. inversion H5. subst.
  apply MP with (ps:=[(Γ, (A --> A) --> (A --> A0) --> (A --> (A ∧ A0)));(Γ, A --> A)]).
  2: apply MPRule_I. intros. inversion H6. subst. apply Ax.
  apply AxRule_I. apply RA7_I. exists A. exists A. exists A0. auto. inversion H7.
  subst. apply wimp_Id_gen. inversion H8. inversion H6. subst. 2: inversion H7.
  assert (J30: List.In (Union form Γ (Singleton form A), A0) ((Union form Γ (Singleton form A), A0 --> B0) :: (Union form Γ (Singleton form A), A0) :: nil)).
  apply in_cons. apply in_eq. pose (H0 _ J30 A A0 Γ). apply f0 ; auto. inversion H3. subst.
  apply MP with (ps:=[(Γ, (A --> A0 --> B0) --> ((A ∧ A0) --> B0));(Γ, (A --> A0 --> B0))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Ax.
  apply AxRule_I. apply RA8_I. exists A. exists A0. exists B0. auto.
  inversion H5. subst. assumption. inversion H6. inversion H4.
(* DNw *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: FOwBIH_rules (Empty_set _, ¬ (∞ A0))).
  apply DNw with (ps:=[(Empty_set _, A0)]). 2: apply DNwRule_I. assumption. apply FOwBIH_monot with (Γ1:=Γ) in J1.
  simpl in J1.
  apply MP with (ps:=[(Γ, (¬ (∞ A0)) --> A --> ¬ (∞ A0)); (Γ, ¬ (∞ A0))]).
  2: apply MPRule_I. intros. inversion H2. subst. apply wThm_irrel.
  inversion H3. subst. 2: inversion H4. assumption.
  intro. simpl. intro. inversion H2.
(* Gen *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: FOwBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form (Union _  Γ (Singleton _ A)) B, A0)). apply H. apply in_eq.
  assert (FOwBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (subst_form ↑ A) --> A0)).
  apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form (Union _  Γ (Singleton _ A)) B, A0)) ; auto.
  apply in_eq. simpl. apply Extensionality_Ensembles. split ; intro ; intro.
  unfold In in H2. destruct H2. destruct H2. subst. inversion H3. subst. unfold In.
  apply Union_introl. exists x0. split ; auto. subst. inversion H2 ; subst.
  apply Union_intror. apply In_singleton. unfold In. destruct H2.
  destruct H2. destruct H2. subst. exists x0. split ; auto. apply Union_introl ; auto.
  inversion H2. subst. exists A ; split ; auto. apply Union_intror. apply In_singleton.
  apply MP with (ps:=[(Γ, (∀ (A[↑] --> A0)) --> (A --> (∀ A0)));(Γ, ∀ (A[↑] --> A0))]). 2: apply MPRule_I.
  intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA17_I. exists A. exists A0. auto. inversion H4.
  subst. 2: inversion H5. apply Gen with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A[↑] --> A0)]). 2: apply GenRule_I.
  intros. inversion H5. 2: inversion H6. subst. auto.
(* EC *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: FOwBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form (Union form Γ (Singleton form A)) B, A0 --> B0[↑])). apply H. apply in_eq.
  assert (FOwBIH_rules (fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A[↑] --> A0 --> B0[↑])). apply H0 with (prem:=(fun x : form => exists B : form, x = B[↑] /\ In form (Union form Γ (Singleton form A)) B, A0 --> B0[↑])) ; auto.
  apply in_eq. simpl. apply Extensionality_Ensembles. split ; intro ; intro.
  unfold In in H2. destruct H2. destruct H2. subst. inversion H3. subst. unfold In.
  apply Union_introl. exists x0. split ; auto. subst. inversion H2 ; subst.
  apply Union_intror. apply In_singleton. unfold In. destruct H2.
  destruct H2. destruct H2. subst. exists x0. split ; auto. apply Union_introl ; auto.
  inversion H2. subst. exists A ; split ; auto. apply Union_intror. apply In_singleton.
  apply MP with (ps:=[(Γ, ((A ∧ (∃ A0)) --> B0) --> (A --> (∃ A0) --> B0));(Γ, (A ∧ (∃ A0)) --> B0)]). 2: apply MPRule_I.
  intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA9_I. exists A. exists (∃ A0). exists B0. auto. inversion H4.
  subst. 2: inversion H5.
  apply MP with (ps:=[(Γ, (((∃ A0) ∧ A) --> B0) --> ((A ∧ (∃ A0)) --> B0));(Γ, (∃ A0) ∧ A --> B0)]). 2: apply MPRule_I.
  intros. inversion H5. subst.
  apply MP with (ps:=[(Γ, ((A ∧ (∃ A0)) --> ((∃ A0) ∧ A)) --> (((∃ A0) ∧ A) --> B0) --> ((A ∧ (∃ A0)) --> B0));(Γ, (A ∧ (∃ A0)) --> ((∃ A0) ∧ A))]). 2: apply MPRule_I.
  intros. inversion H6. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (A ∧ (∃ A0)). exists ((∃ A0) ∧ A). exists B0.
  auto. inversion H7. 2: inversion H8. subst. apply comm_And_obj. inversion H6. 2: inversion H7. subst.
  apply MP with (ps:=[(Γ, ((∃ A0) --> A --> B0) --> ((∃ A0) ∧ A --> B0));(Γ, (∃ A0) --> A --> B0)]). 2: apply MPRule_I.
  intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA8_I. exists (∃ A0). exists A. exists B0. auto. inversion H8.
  2: inversion H9. subst. apply EC with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A0 --> (A --> B0)[↑])]). 2: apply ECRule_I.
  intros. inversion H9. 2: inversion H10. subst. simpl.
  apply MP with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, ((A0 ∧ A[↑]) --> B0[↑]) --> A0 --> A[↑] --> B0[↑]);(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (A0 ∧ A[↑]) --> B0[↑])]).
  2: apply MPRule_I. intros. inversion H10. subst. apply Ax. apply AxRule_I. apply RA9_I. exists A0. exists A[↑]. exists B0[↑]. auto.
  inversion H11. subst. 2: inversion H12.
  apply MP with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (A[↑] ∧ A0 --> B0[↑]) --> (A0 ∧ A[↑] --> B0[↑]));(fun x : form => exists B : form, x = B[↑] /\ In form Γ B,  A[↑] ∧ A0 --> B0[↑])]).
  2: apply MPRule_I. intros. inversion H12. subst.
  apply MP with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, ((A0 ∧ A[↑] ) --> (A[↑] ∧ A0)) --> (A[↑] ∧ A0 --> B0[↑]) --> (A0 ∧ A[↑] --> B0[↑]));(fun x : form => exists B : form, x = B[↑] /\ In form Γ B,  (A0 ∧ A[↑] ) --> (A[↑] ∧ A0))]).
  2: apply MPRule_I. intros. inversion H13. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (A0 ∧ A[↑]).
  exists (A[↑] ∧ A0). exists B0[↑]. auto. inversion H14. 2: inversion H15. subst. apply comm_And_obj.
  inversion H13. 2: inversion H14. subst.
  apply MP with (ps:=[(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, (A[↑] --> A0 --> B0[↑]) --> (A[↑] ∧ A0 --> B0[↑]));(fun x : form => exists B : form, x = B[↑] /\ In form Γ B, A[↑] --> A0 --> B0[↑])]).
  2: apply MPRule_I. intros. inversion H14. subst. apply Ax. apply AxRule_I. apply RA8_I. exists A[↑].
  exists A0. exists B0[↑]. auto. inversion H15. 2: inversion H16. subst. auto.
Qed.

Theorem gen_FOwBIH_Detachment_Theorem : forall A B Γ,
  wpair_der (Γ, Singleton _ (A --> B)) ->
      wpair_der (Union form Γ (Singleton form A),  Singleton _ B).
Proof.
intros A B Γ wpair. unfold wpair_der. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. simpl. apply In_singleton. inversion H0.
apply MP with (ps:=[ (Union form Γ (Singleton form A), B --> (B ∨ ⊥)); (Union form Γ (Singleton form A), B)]).
2: apply MPRule_I. intros. inversion H. subst. apply Ax. apply AxRule_I. apply RA2_I.
exists B. exists (⊥). auto. inversion H0. subst. 2: inversion H1.
destruct wpair. destruct H1. destruct H2. simpl in H3. destruct x.
apply MP with (ps:=[(Union form Γ (Singleton form A), ⊥ --> B);(Union form Γ (Singleton form A), ⊥)]).
2: apply MPRule_I. intros. inversion H4. subst. apply wEFQ. inversion H5. subst. 2: inversion H6.
simpl in H3. apply FOwBIH_monot with (Γ1:= Union form Γ (Singleton form A)) in H3. simpl in H3. auto.
simpl. intro. intro. apply Union_introl ; auto.
destruct x. simpl in H3. assert (f=A --> B). pose (H2 f). assert (List.In f (f :: nil)). apply in_eq.
apply i in H4. inversion H4. auto. subst. apply absorp_Or1 in H3.
assert (J1: Γ = Γ). reflexivity.
assert (J2: A --> B = A --> B). reflexivity.
pose (FOwBIH_Detachment_Theorem (Γ, A --> B) H3 A B Γ J1 J2). assumption.
exfalso. simpl in H1. inversion H1. apply H6. subst. pose (H2 f).
assert (List.In f (f :: f0 :: x)). apply in_eq. pose (i H4). inversion i0. subst.
pose (H2 f0). assert (List.In f0 (A --> B :: f0 :: x)). apply in_cons. apply in_eq.
pose (i1 H5). inversion i2. subst. apply in_eq.
Qed.

Theorem gen_FOwBIH_Deduction_Theorem : forall A B Γ,
  wpair_der (Union form Γ (Singleton form A), Singleton _ B) ->
      wpair_der (Γ, Singleton _ (A --> B)).
Proof.
intros A B Γ wpair. unfold wpair_der. simpl. exists [(A --> B)]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. apply In_singleton. inversion H0.
apply MP with (ps:=[(Γ, (A --> B) --> ((A --> B) ∨ ⊥)); (Γ, (A --> B))]).
2: apply MPRule_I. intros. inversion H. subst. apply Ax. apply AxRule_I. apply RA2_I.
exists (A --> B). exists (⊥). auto. inversion H0. subst. 2: inversion H1.
destruct wpair. destruct H1. destruct H2. simpl in H3. simpl in H2. destruct x. simpl in H3.
assert (J1: Union form Γ (Singleton form A) = Union form Γ (Singleton form A)). reflexivity.
assert (J2: ⊥ = ⊥). reflexivity.
pose (FOwBIH_Deduction_Theorem (Union form Γ (Singleton form A), ⊥) H3 A (⊥) Γ J1 J2).
apply MP with (ps:=[(Γ, (⊥ --> B) --> (A --> B));(Γ, ⊥ --> B)]).
2: apply MPRule_I. intros. inversion H4. subst.
apply MP with (ps:=[(Γ, (A --> ⊥) --> (⊥ --> B) --> (A --> B));(Γ, A --> ⊥)]).
2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA1_I. exists A.
exists (⊥). exists B. auto. inversion H6. subst. 2: inversion H7. assumption.
inversion H5. subst. 2: inversion H6. apply wEFQ.
destruct x. simpl in H3. assert (f=B). pose (H2 f). assert (List.In f (f :: nil)). apply in_eq.
apply i in H4. inversion H4. auto. subst. apply absorp_Or1 in H3.
assert (J1: Union form Γ (Singleton form A) = Union form Γ (Singleton form A)). reflexivity.
assert (J2: B = B). reflexivity.
pose (FOwBIH_Deduction_Theorem (Union form Γ (Singleton form A), B) H3 A B Γ J1 J2). assumption.
exfalso. simpl in H2. inversion H1. apply H6. subst. pose (H2 f).
assert (List.In f (f :: f0 :: x)). apply in_eq. pose (i H4). inversion i0. subst.
pose (H2 f0). assert (List.In f0 (f :: f0 :: x)). apply in_cons. apply in_eq.
pose (i1 H5). inversion i2. subst. apply in_eq.
Qed.

Theorem FOwBIH_Dual_Detachment_Theorem : forall A B Δ,
           (FOwBIH_rules (Singleton _ (A --< B), list_disj Δ)) ->
           (FOwBIH_rules (Singleton _ A, B ∨ (list_disj Δ))).
Proof.
intros A B Δ D.
assert (J1: Singleton _ (A --< B) = Union _ (Empty_set form) (Singleton _ (A --< B))).
apply Extensionality_Ensembles. split ; intro ; intro. apply Union_intror. auto.
inversion H. subst. inversion H0. auto.
assert (J2: list_disj Δ = list_disj Δ). reflexivity.
pose (FOwBIH_Deduction_Theorem (Singleton _ (A --< B), list_disj Δ) D (A --< B) (list_disj Δ) (Empty_set _) J1 J2).
apply wdual_residuation in f.
assert (J3: Empty_set form = Empty_set form). reflexivity.
assert (J4: A --> (B ∨ (list_disj Δ)) = A --> (B ∨ (list_disj Δ))). reflexivity.
pose (FOwBIH_Detachment_Theorem (Empty_set _, A --> B ∨ (list_disj Δ)) f A (B ∨ (list_disj Δ))
(Empty_set _) J3 J4).
assert (Union form (Empty_set form) (Singleton form A) = Singleton form A).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H ; auto. inversion H0.
apply Union_intror ; auto. rewrite H in f0 ; auto.
Qed.

Theorem FOwBIH_Dual_Deduction_Theorem : forall A B Δ,
           (FOwBIH_rules (Singleton _ A, B ∨ (list_disj Δ))) ->
           (FOwBIH_rules (Singleton _ (A --< B), list_disj Δ)).
Proof.
intros A B Δ D.
assert (J1: Singleton _ A = Union _ (Empty_set _) (Singleton _ A)).
apply Extensionality_Ensembles. split ; intro ; intro. apply Union_intror. auto.
inversion H. subst. inversion H0. auto.
assert (J2: B ∨ (list_disj Δ) = B ∨ (list_disj Δ)). reflexivity.
pose (FOwBIH_Deduction_Theorem (Singleton _ A, B ∨ (list_disj Δ)) D A (B ∨ (list_disj Δ))
(Empty_set _) J1 J2). apply wdual_residuation in f.
assert (J3: Empty_set _ = Empty_set form). reflexivity.
assert (J4: (A --< B) --> list_disj Δ = (A --< B) --> list_disj Δ). reflexivity.
pose (FOwBIH_Detachment_Theorem (Empty_set _, (A --< B) --> list_disj Δ) f (A --< B)
(list_disj Δ) (Empty_set _) J3 J4).
assert (Union form (Empty_set form) (Singleton form (A --< B)) = Singleton form (A --< B)).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H ; auto. inversion H0.
apply Union_intror ; auto. rewrite H in f0 ; auto.
Qed.

Lemma In_remove : forall (A : form) B (l : list (form)), List.In A (remove eq_dec_form B l) -> List.In A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in H. destruct (eq_dec_form B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : form) B (l : list (form)), InT A (remove eq_dec_form B l) -> InT A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in X. destruct (eq_dec_form B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion X.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (form)), NoDup l -> NoDup (remove eq_dec_form A l).
Proof.
intro A. induction l.
- intro. simpl. apply NoDup_nil.
- intro H. simpl. destruct (eq_dec_form A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.

Lemma remove_disj : forall l B Γ, FOwBIH_rules (Γ, list_disj l --> B ∨ (list_disj (remove eq_dec_form B l))).
Proof.
induction l.
- intros. simpl. apply Ax. apply AxRule_I. apply RA3_I.
  exists B. exists (⊥). auto.
- intros. pose (IHl B Γ). simpl. destruct (eq_dec_form B a).
  * subst. simpl.
    apply MP with (ps:=[(Γ, ((list_disj l) --> a ∨ (list_disj (remove eq_dec_form a l))) --> (a ∨ (list_disj l) --> a ∨ (list_disj (remove eq_dec_form a l))));
    (Γ, (list_disj l) --> a ∨ (list_disj (remove eq_dec_form a l)))]).
    2: apply MPRule_I. intros. inversion H. subst.
    apply MP with (ps:=[(Γ, (a --> a ∨ (list_disj (remove eq_dec_form a l))) --> ((list_disj l) --> a ∨ (list_disj (remove eq_dec_form a l))) --> (a ∨ (list_disj l) --> a ∨ (list_disj (remove eq_dec_form a l))));
    (Γ, a --> a ∨ (list_disj (remove eq_dec_form a l)))]).
    2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
    apply RA4_I. exists a. exists (list_disj l). exists (a ∨ (list_disj (remove eq_dec_form a l))).
    auto. inversion H1. subst. apply Ax. apply AxRule_I.
    apply RA2_I. exists a. exists (list_disj (remove eq_dec_form a l)).
    auto. inversion H2. inversion H0. subst. assumption. inversion H1.
  * simpl.
    apply MP with (ps:=[(Γ, (a ∨ (B ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))) --> (a ∨ (list_disj l) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, (a ∨ (B ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H. subst.
    apply MP with (ps:=[(Γ, (a ∨ (list_disj l) --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))) --> (a ∨ (B ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))) --> (a ∨ (list_disj l) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, (a ∨ (list_disj l) --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H0. subst. apply Ax.
    apply AxRule_I. apply RA1_I. exists (a ∨ (list_disj l)). exists (a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))).
    exists (B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))). auto. inversion H1. subst.
    apply MP with (ps:=[(Γ, (list_disj l --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))) --> (a ∨ (list_disj l) --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, list_disj l --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l))))]). 2: apply MPRule_I.
    intros. inversion H2. subst.
    apply MP with (ps:=[(Γ, (a --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))) --> (list_disj l --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))) --> (a ∨ (list_disj l) --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, a --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l))))]). 2: apply MPRule_I.
    intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA4_I.
    exists a. exists (list_disj l). exists (a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))).
    auto. inversion H4. subst. apply Ax. apply AxRule_I. apply RA2_I.
    exists a. exists (B ∨ (list_disj (remove eq_dec_form B l))). auto. inversion H5.
    inversion H3. subst.
    apply MP with (ps:=[(Γ, ((B ∨ (list_disj (remove eq_dec_form B l))) --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))) --> (list_disj l --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, (B ∨ (list_disj (remove eq_dec_form B l))) --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l))))]).
    2: apply MPRule_I. intros. inversion H4. subst.
    apply MP with (ps:=[(Γ, (list_disj l --> (B ∨ (list_disj (remove eq_dec_form B l)))) --> ((B ∨ (list_disj (remove eq_dec_form B l))) --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))) --> (list_disj l --> a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, (list_disj l --> (B ∨ (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (list_disj l).
    exists (B ∨ (list_disj (remove eq_dec_form B l))). exists (a ∨ (B ∨ (list_disj (remove eq_dec_form B l)))).
    auto. inversion H6. subst. assumption. inversion H7. inversion H5. subst.
    apply Ax. apply AxRule_I. apply RA3_I. exists a. exists (B ∨ (list_disj (remove eq_dec_form B l))).
    auto. inversion H6. inversion H4. inversion H2. inversion H0. subst.
    apply MP with (ps:=[(Γ, ((B ∨ (list_disj (remove eq_dec_form B l)) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))) --> (a ∨ (B ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l))))));
    (Γ, ((B ∨ (list_disj (remove eq_dec_form B l)) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l))))))]).
    2: apply MPRule_I. intros. inversion H1. subst.
    apply MP with (ps:=[(Γ, (a --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))) --> ((B ∨ (list_disj (remove eq_dec_form B l)) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))) --> (a ∨ (B ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l))))));
    (Γ, (a --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
    apply RA4_I. exists a. exists (B ∨ (list_disj (remove eq_dec_form B l))).
    exists (B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))). auto. inversion H3. subst.
    apply MP with (ps:=[(Γ, ((a ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))) --> (a --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, (a ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l))))]).
    2: apply MPRule_I. intros. inversion H4. subst.
    apply MP with (ps:=[(Γ, (a --> (a ∨ (list_disj (remove eq_dec_form B l)))) --> ((a ∨ (list_disj (remove eq_dec_form B l))) --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))) --> (a --> B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))));
    (Γ, (a --> (a ∨ (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
    apply RA1_I. exists a. exists (a ∨ (list_disj (remove eq_dec_form B l))).
    exists (B ∨ (a ∨ (list_disj (remove eq_dec_form B l)))). auto. inversion H6. subst.
    apply Ax. apply AxRule_I.
    apply RA2_I. exists a. exists (list_disj (remove eq_dec_form B l)).
    auto. inversion H7. inversion H5. subst. apply Ax. apply AxRule_I.
    apply RA3_I. exists B. exists (a ∨ (list_disj (remove eq_dec_form B l))).
    auto. inversion H6. inversion H4. inversion H2. subst. apply wmonotL_Or.
    apply Ax. apply AxRule_I.
    apply RA3_I. exists a. exists (list_disj (remove eq_dec_form B l)).
    auto. inversion H3. inversion H1.
Qed.

Theorem gen_FOwBIH_Dual_Detachment_Theorem : forall A B Δ,
  wpair_der (Singleton _ (A --< B), Δ) ->
      wpair_der (Singleton _ A, Union _ (Singleton _ B) Δ).
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. simpl in H0. simpl in H1.
exists (B :: (remove eq_dec_form B x)). repeat split.
apply NoDup_cons. apply remove_In. apply NoDup_remove. assumption.
intros. inversion H2 ; subst ; simpl ; auto. left. apply In_singleton.
right. apply H0. apply In_remove with (B:=B). assumption.
simpl. pose (FOwBIH_Dual_Detachment_Theorem A B x H1).
apply MP with (ps:=[(Singleton _ A, (B ∨ (list_disj x)) --> (B ∨ (list_disj (remove eq_dec_form B x))));
(Singleton _ A, (B ∨ (list_disj x)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Singleton _ A, ((list_disj x) --> (B ∨ (list_disj (remove eq_dec_form B x)))) --> (((B ∨ (list_disj x)) --> (B ∨ (list_disj (remove eq_dec_form B x))))));
(Singleton _ A, (list_disj x) --> (B ∨ (list_disj (remove eq_dec_form B x))))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply MP with (ps:=[(Singleton _ A, (B --> (B ∨ (list_disj (remove eq_dec_form B x)))) --> (((list_disj x) --> (B ∨ (list_disj (remove eq_dec_form B x)))) --> (((B ∨ (list_disj x)) --> (B ∨ (list_disj (remove eq_dec_form B x)))))));
(Singleton _ A, B --> (B ∨ (list_disj (remove eq_dec_form B x))))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA4_I.
exists B. exists (list_disj x). exists (B ∨ (list_disj (remove eq_dec_form B x))).
auto. inversion H5. subst. apply Ax. apply AxRule_I. apply RA2_I.
exists B. exists (list_disj (remove eq_dec_form B x)). auto. inversion H6.
inversion H4. subst. apply remove_disj. inversion H5. inversion H3. subst. assumption.
inversion H4.
Qed.

Theorem gen_FOwBIH_Dual_Deduction_Theorem : forall A B Δ,
  wpair_der (Singleton _ A, Union _ (Singleton _ B) Δ) ->
      wpair_der (Singleton _ (A --< B), Δ).
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. simpl in H0. simpl in H1.
exists (remove eq_dec_form B x). repeat split.
apply NoDup_remove. assumption.
intros. simpl. pose (H0 A0). pose (In_remove _ _ _ H2). apply i in i0.
destruct i0. inversion H3. subst. exfalso. pose (remove_In eq_dec_form x x0).
apply n. assumption. assumption. simpl.
pose (FOwBIH_Dual_Deduction_Theorem A B (remove eq_dec_form B x)). apply f.
apply MP with (ps:=[(Singleton _ A, (list_disj x) --> (B ∨ (list_disj (remove eq_dec_form B x))));
(Singleton _ A, list_disj x)]). 2: apply MPRule_I. intros. inversion H2. subst. apply remove_disj.
inversion H3. subst. assumption. inversion H4.
Qed.








(* ------------------------------------------------------------------------------------------------------ *)

(* We can then prove that the constant domain axiom is derivable in FOwBIH, and hence in FOsBIH. *)

Theorem Constant_Domain_Ax : forall A B, FOwBIH_rules (Empty_set _, (∀(A ∨ B[↑])) --> ((∀ A) ∨ B)).
Proof.
intros.
apply MP with (ps:=[(Empty_set _,(B ∨ (∀ A) --> (∀ A) ∨ B) --> ((∀ A ∨ B[↑]) --> (∀ A) ∨ B));(Empty_set _, B ∨ (∀ A) --> (∀ A) ∨ B)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Empty_set _, ((∀ A ∨ B[↑]) --> B ∨ (∀ A)) --> (B ∨ (∀ A) --> (∀ A) ∨ B) --> ((∀ A ∨ B[↑]) --> (∀ A) ∨ B));
(Empty_set _, (∀ A ∨ B[↑]) --> B ∨ (∀ A))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA1_I.
exists (∀ A ∨ B[↑]). exists (B ∨ (∀ A)). exists ((∀ A) ∨ B). auto. inversion H1. 2: inversion H2.
subst. pose (wdual_residuation (∀ (A ∨ B[↑])) B (∀ A)). destruct p. apply f. clear f.
clear f0. apply FOwBIH_Deduction_Theorem with (s:=(Singleton _ ((∀ A ∨ B[↑]) --< B), ∀ A)) ; auto.
apply Gen with (ps:=[((fun x => exists C, ((x = (subst_form ↑) C) /\ In _ (Singleton _ ((∀ A ∨ B[↑]) --< B)) C)), A)]). 2: apply GenRule_I.
intros. inversion H2. 2: inversion H3. subst. simpl.
assert (FOwBIH_rules (Empty_set form, ((∀ A[up ↑] ∨ B[↑][up ↑]) --< B[↑]) --> A)).
{ pose (wdual_residuation(∀ A[up ↑] ∨ B[↑][up ↑]) B[↑] A). destruct p. apply f0. clear f. clear f0.
apply MP with (ps:=[(Empty_set _, ((A ∨ B[↑]) --> (B[↑] ∨ A)) --> ((∀ A[up ↑] ∨ B[↑][up ↑]) --> (B[↑] ∨ A)));
(Empty_set _, (A ∨ B[↑]) --> (B[↑] ∨ A))]). intros. 2: apply MPRule_I. inversion H3. subst.
apply MP with (ps:=[(Empty_set _, ((∀ A[up ↑] ∨ B[↑][up ↑]) --> (A ∨ B[↑])) --> ((A ∨ B[↑]) --> (B[↑] ∨ A)) --> ((∀ A[up ↑] ∨ B[↑][up ↑]) --> (B[↑] ∨ A)));
(Empty_set _, (∀ A[up ↑] ∨ B[↑][up ↑]) --> (A ∨ B[↑]))]). intros. 2: apply MPRule_I. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists ((∀ A[up ↑] ∨ B[↑][up ↑])). exists (A ∨ B[↑]). exists (B[↑] ∨ A).
auto. inversion H5. 2: inversion H6. subst. rewrite up_form.
apply Ax. apply AxRule_I. apply RA18_I. unfold RA18. exists (A[up ↑] ∨ B[↑][↑]). exists (var 0). simpl.
rewrite up_decompose. rewrite subst_var. rewrite <- up_form. rewrite up_decompose. rewrite subst_var. auto.
inversion H4 ; subst. apply comm_Or_obj. inversion H5. }
assert (J1: Empty_set _ = Empty_set form). auto.
assert (J2: ((∀ A[up ↑] ∨ B[↑][up ↑]) --< B[↑]) --> A = ((∀ A[up ↑] ∨ B[↑][up ↑]) --< B[↑]) --> A). auto.
pose (FOwBIH_Detachment_Theorem (Empty_set _, ((∀ A[up ↑] ∨ B[↑][up ↑]) --< B[↑]) --> A) H3
((∀ A[up ↑] ∨ B[↑][up ↑]) --< B[↑]) A (Empty_set _) J1 J2).
assert ((fun x : form => exists C : form, x = C[↑] /\ In form (Singleton form ((∀ A ∨ B[↑]) --< B)) C) =
Union form (Empty_set form) (Singleton form ((∀ A[up ↑] ∨ B[↑][up ↑]) --< B[↑]))).
apply Extensionality_Ensembles. split ; intro ; intro. destruct H4. destruct H4. subst.
apply Union_intror. inversion H5. subst. simpl. apply In_singleton. unfold In.
inversion H4. subst. inversion H5. subst. inversion H5. subst.
exists ((∀ A ∨ B[↑]) --< B). split ; simpl ; auto. apply In_singleton.
rewrite H4. auto. apply Extensionality_Ensembles. simpl ; split ; intro ; intro.
inversion H2. subst. apply Union_intror. apply In_singleton. inversion H2.
subst. inversion H3. subst. inversion H3. apply In_singleton. inversion H0.
subst. apply comm_Or_obj. inversion H1.
Qed.











(* ------------------------------------------------------------------------------------------------------ *)

(* Some proof-theoretical results about list_disj. They are helpful in the manipulation
    of prime theories. *)

Lemma Id_list_disj : forall Γ l0 l1,
  FOwBIH_rules (Γ, list_disj l0 --> list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- simpl. apply wEFQ.
- simpl. apply wmonotL_Or. apply IHl0.
Qed.

Lemma list_disj_app : forall l0 Γ A l1,
  FOwBIH_rules (Γ, A --> list_disj (l0 ++ l1)) -> FOwBIH_rules (Γ, A --> ((list_disj l0) ∨ (list_disj l1))).
Proof.
induction l0.
- simpl. intros.
  apply MP with (ps:=[(Γ, ((list_disj l1) --> ⊥ ∨ (list_disj l1)) --> (A --> ⊥ ∨ (list_disj l1)));(Γ, (list_disj l1) --> ⊥ ∨ (list_disj l1))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A --> (list_disj l1)) --> ((list_disj l1) --> ⊥ ∨ (list_disj l1)) --> (A --> ⊥ ∨ (list_disj l1)));(Γ,A --> (list_disj l1))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists (list_disj l1). exists (⊥ ∨ (list_disj l1)). auto. inversion H2.
  2: inversion H3. subst. assumption. inversion H1. 2: inversion H2. subst. apply Ax.
  apply AxRule_I. apply RA3_I. exists ⊥. exists (list_disj l1). auto.
- simpl. intros.
  apply MP with (ps:=[(Γ, (a ∨ (list_disj (l0 ++ l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)) --> (A --> (a ∨ (list_disj l0)) ∨ (list_disj l1)));
  (Γ,  (a ∨ (list_disj (l0 ++ l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A --> a ∨ (list_disj (l0 ++ l1))) --> (a ∨ (list_disj (l0 ++ l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)) --> (A --> (a ∨ (list_disj l0)) ∨ (list_disj l1)));
  (Γ,  A --> a ∨ (list_disj (l0 ++ l1)))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists (a ∨ (list_disj (l0 ++ l1))). exists ((a ∨ (list_disj l0)) ∨ (list_disj l1)).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst.
  apply MP with (ps:=[(Γ, (a ∨ ((list_disj l0) ∨ (list_disj l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)) --> (a ∨ (list_disj (l0 ++ l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)));
  (Γ, (a ∨ ((list_disj l0) ∨ (list_disj l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (a ∨ (list_disj (l0 ++ l1)) --> a ∨ ((list_disj l0) ∨ (list_disj l1))) --> (a ∨ ((list_disj l0) ∨ (list_disj l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)) --> (a ∨ (list_disj (l0 ++ l1)) --> (a ∨ (list_disj l0)) ∨ (list_disj l1)));
  (Γ, (a ∨ (list_disj (l0 ++ l1)) --> a ∨ ((list_disj l0) ∨ (list_disj l1))))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists (a ∨ (list_disj (l0 ++ l1))). exists (a ∨ ((list_disj l0) ∨ (list_disj l1))).
  exists ((a ∨ (list_disj l0)) ∨ (list_disj l1)). auto. inversion H4. 2: inversion H5.
  subst. apply wmonotL_Or. apply IHl0. apply wimp_Id_gen. inversion H3. 2: inversion H4. subst.
  remember (list_disj l0) as E. remember (list_disj l1) as F.
  apply MP with (ps:=[(Γ, ((E ∨ F) --> (a ∨ E) ∨ F) --> (a ∨ (E ∨ F) --> (a ∨ E) ∨ F));
  (Γ, ((E ∨ F) --> (a ∨ E) ∨ F))]). 2: apply MPRule_I. intros. inversion H4. rewrite <- H5.
  apply MP with (ps:=[(Γ, (a --> (a ∨ E) ∨ F) --> ((E ∨ F) --> (a ∨ E) ∨ F) --> (a ∨ (E ∨ F) --> (a ∨ E) ∨ F));
  (Γ, (a --> (a ∨ E) ∨ F))]). 2: apply MPRule_I. intros. inversion H6. rewrite <- H7.
  apply Ax. apply AxRule_I. apply RA4_I. exists a. exists (E ∨ F). exists ((a ∨ E) ∨ F).
  auto. inversion H7. 2: inversion H8. rewrite <- H8.
  apply MP with (ps:=[(Γ, ((a ∨ E) --> (a ∨ E) ∨ F) --> (a --> (a ∨ E) ∨ F));(Γ, ((a ∨ E) --> (a ∨ E) ∨ F))]).
  2: apply MPRule_I. intros. inversion H9. rewrite <- H10.
  apply MP with (ps:=[(Γ, (a --> (a ∨ E)) --> ((a ∨ E) --> (a ∨ E) ∨ F) --> (a --> (a ∨ E) ∨ F));(Γ, a --> (a ∨ E))]).
  2: apply MPRule_I. intros. inversion H11. rewrite <- H12. apply Ax. apply AxRule_I.
  apply RA1_I. exists a. exists (a ∨ E). exists ((a ∨ E) ∨ F). auto.
  inversion H12. 2: inversion H13. rewrite <- H13. apply Ax. apply AxRule_I. apply RA2_I.
  exists a. exists E. auto. inversion H10. 2: inversion H11. rewrite <- H11. apply Ax.
  apply AxRule_I. apply RA2_I. exists (a ∨ E). exists F. auto. inversion H5. 2: inversion H6.
  rewrite <- H6. apply wmonotR_Or. apply Ax. apply AxRule_I. apply RA3_I. exists a. exists E. auto.
Qed.

Lemma list_disj_app0 : forall l0 Γ A l1,
  FOwBIH_rules (Γ, A --> ((list_disj l0) ∨ (list_disj l1))) -> FOwBIH_rules (Γ, A --> list_disj (l0 ++ l1)).
Proof.
induction l0.
- simpl. intros.
  apply MP with (ps:=[(Γ, (⊥ ∨ (list_disj l1) --> list_disj l1) --> (A --> list_disj l1));
  (Γ, ⊥ ∨ (list_disj l1) --> list_disj l1)]). 2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A --> ⊥ ∨ (list_disj l1)) --> (⊥ ∨ (list_disj l1) --> list_disj l1) --> (A --> list_disj l1));
  (Γ, A --> ⊥ ∨ (list_disj l1))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (⊥ ∨ (list_disj l1)).
  exists (list_disj l1). auto. inversion H2. 2: inversion H3. subst. auto. inversion H1.
  2: inversion H2. subst.
  apply MP with (ps:=[(Γ, ((list_disj l1) --> list_disj l1) --> (⊥ ∨ (list_disj l1) --> list_disj l1));
  (Γ, (list_disj l1) --> list_disj l1)]). 2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (⊥ --> list_disj l1) --> ((list_disj l1) --> list_disj l1) --> (⊥ ∨ (list_disj l1) --> list_disj l1));
  (Γ, ⊥ --> list_disj l1)]). 2: apply MPRule_I. intros. inversion H3. subst.
  apply Ax. apply AxRule_I. apply RA4_I. exists ⊥. exists (list_disj l1).
  exists (list_disj l1). auto. inversion H4. 2: inversion H5. subst. apply wEFQ.
  inversion H3. 2: inversion H4. subst. apply wimp_Id_gen.
- simpl. intros.
  apply MP with (ps:=[(Γ, ((a ∨ (list_disj l0)) ∨ (list_disj l1) --> a ∨ (list_disj (l0 ++ l1))) --> (A --> a ∨ (list_disj (l0 ++ l1))));
  (Γ, ((a ∨ (list_disj l0)) ∨ (list_disj l1) --> a ∨ (list_disj (l0 ++ l1))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A --> (a ∨ (list_disj l0)) ∨ (list_disj l1)) --> ((a ∨ (list_disj l0)) ∨ (list_disj l1) --> a ∨ (list_disj (l0 ++ l1))) --> (A --> a ∨ (list_disj (l0 ++ l1))));
  (Γ,  A --> (a ∨ (list_disj l0)) ∨ (list_disj l1))]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists A. exists ((a ∨ (list_disj l0)) ∨ (list_disj l1)). exists (a ∨ (list_disj (l0 ++ l1))).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst.
  apply MP with (ps:=[(Γ, (a ∨ ((list_disj l0) ∨ (list_disj l1)) --> a ∨ (list_disj (l0 ++ l1))) --> ((a ∨ (list_disj l0)) ∨ (list_disj l1) --> a ∨ (list_disj (l0 ++ l1))));
  (Γ, (a ∨ ((list_disj l0) ∨ (list_disj l1)) --> a ∨ (list_disj (l0 ++ l1))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, ((a ∨ (list_disj l0)) ∨ (list_disj l1) --> a ∨ ((list_disj l0) ∨ (list_disj l1))) --> (a ∨ ((list_disj l0) ∨ (list_disj l1)) --> a ∨ (list_disj (l0 ++ l1))) --> ((a ∨ (list_disj l0)) ∨ (list_disj l1) --> a ∨ (list_disj (l0 ++ l1))));
  (Γ, ((a ∨ (list_disj l0)) ∨ (list_disj l1) --> a ∨ ((list_disj l0) ∨ (list_disj l1))))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists ((a ∨ (list_disj l0)) ∨ (list_disj l1)).
  exists (a ∨ ((list_disj l0) ∨ (list_disj l1))). exists (a ∨ (list_disj (l0 ++ l1))).
  auto. inversion H4. 2: inversion H5.
  subst. remember (list_disj l0) as E. remember (list_disj l1) as F.
  apply MP with (ps:=[(Γ, (F --> a ∨ (E ∨ F)) --> ((a ∨ E) ∨ F --> a ∨ (E ∨ F)));
  (Γ, F --> a ∨ (E ∨ F))]). 2: apply MPRule_I. intros. inversion H5. rewrite <- H6.
  apply MP with (ps:=[(Γ, ((a ∨ E) --> a ∨ (E ∨ F)) --> (F --> a ∨ (E ∨ F)) --> ((a ∨ E) ∨ F --> a ∨ (E ∨ F)));
  (Γ, ((a ∨ E) --> a ∨ (E ∨ F)))]). 2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
  apply Ax. apply AxRule_I. apply RA4_I. exists (a ∨ E). exists F. exists (a ∨ (E ∨ F)).
  auto. inversion H8. 2: inversion H9. rewrite <- H9. apply wmonotL_Or. apply Ax.
  apply AxRule_I. apply RA2_I. exists E. exists F. auto. inversion H6. 2: inversion H7.
  rewrite <- H7.
  apply MP with (ps:=[(Γ, ((E ∨ F) --> a ∨ (E ∨ F)) --> (F --> a ∨ (E ∨ F)));(Γ, ((E ∨ F) --> a ∨ (E ∨ F)))]).
  2: apply MPRule_I. intros. inversion H8. rewrite <- H9.
  apply MP with (ps:=[(Γ, (F --> (E ∨ F)) --> ((E ∨ F) --> a ∨ (E ∨ F)) --> (F --> a ∨ (E ∨ F)));(Γ, F --> (E ∨ F))]).
  2: apply MPRule_I. intros. inversion H10. rewrite <- H11. apply Ax. apply AxRule_I.
  apply RA1_I. exists F. exists (E ∨ F). exists (a ∨ (E ∨ F)). auto.
  inversion H11. 2: inversion H12. rewrite <- H12. apply Ax. apply AxRule_I. apply RA3_I.
  exists E. exists F. auto. inversion H9. 2: inversion H10. rewrite <- H10. apply Ax.
  apply AxRule_I. apply RA3_I. exists a. exists (E ∨ F). auto. inversion H3. 2: inversion H4.
  rewrite <- H4. apply wmonotL_Or. apply IHl0. apply wimp_Id_gen.
Qed.

Lemma list_disj_remove_app : forall l0 l1 Γ A,
FOwBIH_rules (Γ, list_disj (l0 ++ remove_list l0 l1) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove_list l0 l1)))).
Proof.
induction l0.
- simpl. intros. apply remove_disj.
- simpl. intros.
  apply MP with (ps:=[(Γ, (a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  --> A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) --> (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  --> A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))));
  (Γ,a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  --> A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1))))))]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Γ, (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  --> a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) --> (a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))
  --> A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))) --> (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  --> A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))));
  (Γ,(a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))
  --> a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA1_I.
  exists (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))).
  exists (a ∨ (A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))).
  exists (A ∨ (a ∨ (list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1)))))). auto.
  inversion H1. 2: inversion H2. subst.
  { simpl. apply wmonotL_Or. clear H1. clear H0. clear H.
    remember (remove eq_dec_form a (remove_list l0 l1)) as E.
    apply MP with (ps:=[(Γ, (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E))) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A E))) --> (list_disj (l0 ++ E) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A E))));
    (Γ, (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E))) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A E))))]).
    2: apply MPRule_I. intros. inversion H. rewrite <- H0.
    apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) --> A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))) --> (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E))) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A E))) --> (list_disj (l0 ++ E) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A E))));
    (Γ, (list_disj (l0 ++ E) --> A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))))]).
    2: apply MPRule_I. intros. inversion H1. rewrite <- H2. apply Ax. apply AxRule_I.
    apply RA1_I. exists (list_disj (l0 ++ E)). exists (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))).
    exists (A ∨ (list_disj (l0 ++ remove eq_dec_form A E))). auto. inversion H2. rewrite <- H3.
    { simpl. apply MP with (ps:=[(Γ, (((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) --> A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))) --> (list_disj (l0 ++ E) --> A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))));
    (Γ, (((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) --> A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))))]).
    2: apply MPRule_I. intros. inversion H4. rewrite <- H5.
    apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) --> ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E))))) --> (((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) --> A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))) --> (list_disj (l0 ++ E) --> A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))));
    (Γ, (list_disj (l0 ++ E) --> ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E))))))]).
    2: apply MPRule_I. intros. inversion H6. rewrite <- H7. apply Ax. apply AxRule_I. apply RA1_I.
    exists (list_disj (l0 ++ E)). exists ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))).
    exists (A ∨ ((list_disj l0) ∨ (list_disj (remove eq_dec_form A E)))). auto.
    inversion H7. 2: inversion H8. rewrite <- H8.
    { remember ((list_disj l0) ∨ (A ∨ (list_disj (remove eq_dec_form A E)))) as F.
      apply MP with (ps:=[(Γ, (((list_disj l0) ∨ (list_disj E)) --> F) --> (list_disj (l0 ++ E) --> F));
      (Γ, (((list_disj l0) ∨ (list_disj E)) --> F))]). 2: apply MPRule_I. intros.
      inversion H9. rewrite <- H10.
      apply MP with (ps:=[(Γ, (list_disj (l0 ++ E) --> ((list_disj l0) ∨ (list_disj E))) --> (((list_disj l0) ∨ (list_disj E)) --> F) --> (list_disj (l0 ++ E) --> F));
      (Γ, list_disj (l0 ++ E) --> ((list_disj l0) ∨ (list_disj E)))]). 2: apply MPRule_I. intros.
      inversion H11. rewrite <- H12. apply Ax. apply AxRule_I. apply RA1_I.
      exists (list_disj (l0 ++ E)). exists ((list_disj l0) ∨ (list_disj E)). exists F. auto.
      inversion H12. 2: inversion H13. rewrite <- H13. apply list_disj_app. apply wimp_Id_gen.
      inversion H10. 2: inversion H11. rewrite <- H11. clear H11. clear H10.
      clear H9. clear H8. clear H7. clear H6. clear H5. clear H0. clear H4.
      clear H3. clear H2. clear H1. clear H. rewrite HeqF. apply wmonotL_Or.
      apply remove_disj. }
    inversion H5. 2: inversion H6. rewrite <- H6. remember (list_disj l0) as D.
    remember (list_disj (remove eq_dec_form A E)) as F.
    apply MP with (ps:=[(Γ, (A ∨ F --> A ∨ (D ∨ F)) --> (D ∨ (A ∨ F) --> A ∨ (D ∨ F)));(Γ, (A ∨ F) --> A ∨ (D ∨ F))]).
    2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
    apply MP with (ps:=[(Γ, (D --> A ∨ (D ∨ F)) --> (A ∨ F --> A ∨ (D ∨ F)) --> (D ∨ (A ∨ F) --> A ∨ (D ∨ F)));(Γ, D --> A ∨ (D ∨ F))]).
    2: apply MPRule_I. intros. inversion H9. rewrite <- H10. apply Ax. apply AxRule_I.
    apply RA4_I. exists D. exists (A ∨ F). exists (A ∨ (D ∨ F)). auto. inversion H10. 2: inversion H11.
    rewrite <- H11.
    apply MP with (ps:=[(Γ, ((D ∨ F) --> A ∨ (D ∨ F)) --> (D --> A ∨ (D ∨ F)));(Γ, ((D ∨ F) --> A ∨ (D ∨ F)))]).
    2: apply MPRule_I. intros. inversion H12. rewrite <- H13.
    apply MP with (ps:=[(Γ, (D --> (D ∨ F)) --> ((D ∨ F) --> A ∨ (D ∨ F)) --> (D --> A ∨ (D ∨ F)));(Γ, D --> (D ∨ F))]).
    2: apply MPRule_I. intros. inversion H14. rewrite <- H15. apply Ax. apply AxRule_I.
    apply RA1_I. exists D. exists (D ∨ F). exists (A ∨ (D ∨ F)). auto. inversion H15.
    rewrite <- H16. apply Ax. apply AxRule_I. apply RA2_I. exists D. exists F. auto.
    inversion H16. inversion H13. rewrite <- H14. apply Ax. apply AxRule_I. apply RA3_I.
    exists A. exists (D ∨ F). auto. inversion H14. inversion H8. rewrite <- H9.
    apply wmonotL_Or. apply Ax. apply AxRule_I. apply RA3_I. exists D. exists F. auto.
    inversion H9. }
    inversion H3. inversion H0. 2: inversion H1. rewrite <- H1. apply wmonotL_Or. apply list_disj_app0.
    apply wimp_Id_gen. }
  inversion H0. 2: inversion H1. subst.
  remember ((list_disj (l0 ++ remove eq_dec_form A (remove eq_dec_form a (remove_list l0 l1))))) as E.
  apply MP with (ps:=[(Γ, ((A ∨ E) --> A ∨ (a ∨ E)) --> (a ∨ (A ∨ E) --> A ∨ (a ∨ E)));
  (Γ, ((A ∨ E) --> A ∨ (a ∨ E)))]). 2: apply MPRule_I. intros. inversion H1. rewrite <- H2.
  apply MP with (ps:=[(Γ, (a --> A ∨ (a ∨ E)) --> ((A ∨ E) --> A ∨ (a ∨ E)) --> (a ∨ (A ∨ E) --> A ∨ (a ∨ E)));
  (Γ, (a --> A ∨ (a ∨ E)))]). 2: apply MPRule_I. intros. inversion H3. rewrite <- H4. clear H4.
  clear H2. apply Ax. apply AxRule_I. apply RA4_I. exists a. exists (A ∨ E).
  exists (A ∨ (a ∨ E)). auto. inversion H4. 2: inversion H5. rewrite <- H5.
  apply MP with (ps:=[(Γ, ((a ∨ E) --> A ∨ (a ∨ E)) --> (a --> A ∨ (a ∨ E))); (Γ, ((a ∨ E) --> A ∨ (a ∨ E)))]).
  2: apply MPRule_I. intros. inversion H6. rewrite <- H7.
  apply MP with (ps:=[(Γ, (a --> (a ∨ E)) --> ((a ∨ E) --> A ∨ (a ∨ E)) --> (a --> A ∨ (a ∨ E))); (Γ, a --> (a ∨ E))]).
  2: apply MPRule_I. intros. inversion H8. rewrite <- H9. apply Ax. apply AxRule_I. apply RA1_I.
  exists a. exists (a ∨ E). exists (A ∨ (a ∨ E)). auto. inversion H9.
  rewrite <- H10. 2: inversion H10. apply Ax. apply AxRule_I. apply RA2_I.
  exists a. exists E. auto. inversion H7. 2: inversion H8. rewrite <- H8.
  apply Ax. apply AxRule_I. apply RA3_I. exists A. exists (a ∨ E). auto.
  inversion H2. rewrite <- H3. apply wmonotL_Or. apply Ax. apply AxRule_I.
  apply RA3_I. exists a. exists E. auto. inversion H3.
Qed.

Lemma Id_list_disj_remove : forall Γ l0 l1,
  FOwBIH_rules (Γ, list_disj l1 --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
induction l0.
- intros. simpl. apply wimp_Id_gen.
- simpl. intros.
  apply MP with (ps:=[(Γ, (list_disj (l0 ++ remove_list l0 l1) --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) --> (list_disj l1 --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, list_disj (l0 ++ remove_list l0 l1) --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1))))]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Γ, (list_disj l1 --> list_disj (l0 ++ remove_list l0 l1)) --> (list_disj (l0 ++ remove_list l0 l1) --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) --> (list_disj l1 --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ,list_disj l1 --> list_disj (l0 ++ remove_list l0 l1))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
  apply RA1_I. exists (list_disj l1). exists (list_disj (l0 ++ remove_list l0 l1)).
  exists (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))). auto.
  inversion H1. 2: inversion H2. subst. apply IHl0. inversion H0. subst.
  clear H. clear H0. apply list_disj_remove_app. inversion H1.
Qed.

Lemma der_list_disj_remove1 : forall Γ A l0 l1,
    (FOwBIH_rules (Γ, A --> list_disj l0)) ->
    (FOwBIH_rules (Γ, A --> list_disj (l0 ++ remove_list l0 l1))).
Proof.
intros Γ A. induction l0.
- simpl. intros.
  apply MP with (ps:=[(Γ, (⊥ --> list_disj l1) --> (A --> list_disj l1));
  (Γ, ⊥ --> list_disj l1)]). 2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A --> ⊥) --> (⊥ --> list_disj l1) --> (A --> list_disj l1));
  (Γ, A --> ⊥)]). 2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists ⊥. exists (list_disj l1).
  auto. inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst. apply wEFQ.
- intros. subst. simpl. simpl in H.
  apply MP with (ps:=[(Γ, (a ∨ (list_disj l0) --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) --> (A --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, (a ∨ (list_disj l0) --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))))]).
  2: apply MPRule_I. intros. inversion H0. subst.
  apply MP with (ps:=[(Γ, (A --> a ∨ (list_disj l0)) --> (a ∨ (list_disj l0) --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))) --> (A --> a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))));
  (Γ, A --> a ∨ (list_disj l0))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (a ∨ (list_disj l0)).
  exists (a ∨ (list_disj (l0 ++ remove eq_dec_form a (remove_list l0 l1)))). auto.
  inversion H2. 2: inversion H3. subst. auto. inversion H1. 2: inversion H2.
  subst. clear H0. clear H1. apply wmonotL_Or. apply Id_list_disj.
Qed.

Lemma der_list_disj_remove2 : forall Γ A l0 l1,
    (FOwBIH_rules (Γ, A --> list_disj l1)) ->
    (FOwBIH_rules (Γ, A --> list_disj (l0 ++ remove_list l0 l1))).
Proof.
intros.
apply MP with (ps:=[(Γ, (list_disj l1 --> (list_disj (l0 ++ (remove_list l0 l1)))) --> (A --> (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, (list_disj l1 --> (list_disj (l0 ++ (remove_list l0 l1)))))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A --> list_disj l1) --> (list_disj l1 --> (list_disj (l0 ++ (remove_list l0 l1)))) --> (A --> (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, A --> list_disj l1)]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists A. exists (list_disj l1). exists (list_disj (l0 ++ (remove_list l0 l1))).
auto. inversion H2. 2 : inversion H3. subst. auto. inversion H1. subst. 2: inversion H2.
clear H0. clear H1.
apply MP with (ps:=[(Γ, ((list_disj (l0 ++ (remove_list l0 l1))) --> (list_disj (l0 ++ (remove_list l0 l1)))) --> (list_disj l1 --> (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, (list_disj (l0 ++ (remove_list l0 l1))) --> (list_disj (l0 ++ (remove_list l0 l1))))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (list_disj l1 --> (list_disj (l0 ++ (remove_list l0 l1)))) --> ((list_disj (l0 ++ (remove_list l0 l1))) --> (list_disj (l0 ++ (remove_list l0 l1)))) --> (list_disj l1 --> (list_disj (l0 ++ (remove_list l0 l1)))));
(Γ, (list_disj l1 --> (list_disj (l0 ++ (remove_list l0 l1)))))]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA1_I.
exists (list_disj l1). exists ((list_disj (l0 ++ (remove_list l0 l1)))).
exists (list_disj (l0 ++ (remove_list l0 l1))). auto. inversion H2.
2: inversion H3. subst. clear H1. clear H2. clear H0. apply Id_list_disj_remove.
inversion H1. 2: inversion H2. subst. clear H0. clear H1. apply wimp_Id_gen.
Qed.

Lemma der_list_disj_bot : forall l Γ,
  FOwBIH_rules (Γ, list_disj l) -> FOwBIH_rules (Γ, list_disj (remove eq_dec_form ⊥ l)).
Proof.
induction l.
- simpl. intros ; auto.
- intros. simpl in H. simpl. destruct (eq_dec_form ⊥ a).
  + subst. apply IHl. apply absorp_Or2 ; auto.
  + simpl. apply MP with (ps:=[(Γ, (a ∨ list_disj l) --> (a ∨ list_disj (remove eq_dec_form ⊥ l)));(Γ, a ∨ list_disj l)]).
     intros. 2: apply MPRule_I. inversion H0. subst.
     apply MP with (ps:=[(Γ, (list_disj l --> a ∨ list_disj (remove eq_dec_form ⊥ l)) --> ((a ∨ list_disj l) --> (a ∨ list_disj (remove eq_dec_form ⊥ l))));
     (Γ, list_disj l --> a ∨ list_disj (remove eq_dec_form ⊥ l))]).
     intros. 2: apply MPRule_I. inversion H1. subst.
     apply MP with (ps:=[(Γ, (a --> a ∨ list_disj (remove eq_dec_form ⊥ l)) --> (list_disj l --> a ∨ list_disj (remove eq_dec_form ⊥ l)) --> ((a ∨ list_disj l) --> (a ∨ list_disj (remove eq_dec_form ⊥ l))));
     (Γ, a --> a ∨ list_disj (remove eq_dec_form ⊥ l))]).
     intros. 2: apply MPRule_I. inversion H2. subst. apply Ax. apply AxRule_I. apply RA4_I.
     exists a. exists (list_disj l). exists (a ∨ list_disj (remove eq_dec_form ⊥ l)). auto. inversion H3 ; subst.
     2: inversion H4. apply Ax. apply AxRule_I. apply RA2_I. exists a. exists (list_disj (remove eq_dec_form ⊥ l)). auto.
     inversion H2 ; subst. 2: inversion H3.
     apply MP with (ps:=[(Γ, (list_disj (remove eq_dec_form ⊥ l) --> a ∨ list_disj (remove eq_dec_form ⊥ l)) --> (list_disj l --> a ∨ list_disj (remove eq_dec_form ⊥ l)));
     (Γ, (list_disj (remove eq_dec_form ⊥ l) --> a ∨ list_disj (remove eq_dec_form ⊥ l)))]). 2: apply MPRule_I.
     intros. inversion H3. subst.
     apply MP with (ps:=[(Γ, (list_disj l --> list_disj (remove eq_dec_form ⊥ l)) --> (list_disj (remove eq_dec_form ⊥ l) --> a ∨ list_disj (remove eq_dec_form ⊥ l)) --> (list_disj l --> a ∨ list_disj (remove eq_dec_form ⊥ l)));
     (Γ, list_disj l --> list_disj (remove eq_dec_form ⊥ l))]). 2: apply MPRule_I.
     intros. inversion H4. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (list_disj l).
     exists (list_disj (remove eq_dec_form ⊥ l)). exists (a ∨ list_disj (remove eq_dec_form ⊥ l)). auto.
     inversion H5. subst. apply FOwBIH_Deduction_Theorem with (s:=(Union _ Γ (Singleton _ (list_disj l)), list_disj (remove eq_dec_form ⊥ l))) ; auto.
     apply IHl. apply Id. apply IdRule_I. apply Union_intror. apply In_singleton. inversion H6.
     inversion H4. subst. 2: inversion H5. apply Ax. apply AxRule_I. apply RA3_I. exists a.
     exists (list_disj (remove eq_dec_form ⊥ l)). auto. inversion H1. subst. 2: inversion H2. auto.
Qed.

Lemma list_disj_remove_form : forall l Γ A,
  FOwBIH_rules (Γ, list_disj l) -> FOwBIH_rules (Γ, A ∨ list_disj (remove eq_dec_form A l)).
Proof.
intros. pose (remove_disj l A Γ).
apply FOwBIH_Detachment_Theorem with (A:= list_disj l) (B:=A ∨ list_disj (remove eq_dec_form A l)) (Γ:=Γ) in f ; auto.
pose (FOwBIH_comp _ f Γ). apply f0. intros. simpl in H0. inversion H0 ; subst.
apply Id. apply IdRule_I. auto. inversion H1. subst. auto.
Qed.

Lemma list_disj_In0 : forall l Γ A,
  List.In A l ->
  FOwBIH_rules (Γ, A --> list_disj l).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  * subst. simpl. apply Ax. apply AxRule_I. apply RA2_I. exists A. exists (list_disj l). auto.
  * simpl. apply MP with (ps:=[(Γ, (list_disj l --> a ∨ list_disj l) --> (A --> a ∨ list_disj l));(Γ, (list_disj l --> a ∨ list_disj l))]).
    2: apply MPRule_I. intros. inversion H1. subst.
    apply MP with (ps:=[(Γ, (A --> list_disj l) --> (list_disj l --> a ∨ list_disj l) --> (A --> a ∨ list_disj l));(Γ, (A --> list_disj l))]).
    2: apply MPRule_I. intros. inversion H2. subst.
    apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (list_disj l). exists (a ∨ list_disj l). auto. inversion H3.
    subst. 2: inversion H4. apply IHl ; auto. inversion H2. subst. apply Ax. apply AxRule_I. apply RA3_I. exists a. exists (list_disj l). auto.
    inversion H3.
Qed.

Lemma list_disj_In : forall l Γ A,
  List.In A l ->
  FOwBIH_rules (Γ, A ∨ list_disj l) ->
  FOwBIH_rules (Γ,list_disj l).
Proof.
induction l.
- simpl. intros. inversion H.
- intros. simpl. simpl in H0.
  apply MP with (ps:=[(Γ, (A ∨ (a ∨ list_disj l)) --> (a ∨ list_disj l));(Γ, A ∨ (a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H1. 2: inversion H2 ; subst ; auto. 2: inversion H3. subst.
  apply MP with (ps:=[(Γ, ((a ∨ list_disj l) --> (a ∨ list_disj l)) --> ((A ∨ (a ∨ list_disj l)) --> (a ∨ list_disj l)));(Γ, (a ∨ list_disj l) --> (a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (A --> (a ∨ list_disj l)) --> ((a ∨ list_disj l) --> (a ∨ list_disj l)) --> ((A ∨ (a ∨ list_disj l)) --> (a ∨ list_disj l)));(Γ, A --> (a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA4_I. exists A. exists (a ∨ list_disj l ). exists (a ∨ list_disj l ). auto.
  inversion H4. subst. 2: inversion H5.
  inversion H. subst. apply Ax. apply AxRule_I. apply RA2_I. exists A. exists (list_disj l). auto.
  apply MP with (ps:=[(Γ, (list_disj l --> a ∨ list_disj l) --> (A --> a ∨ list_disj l));(Γ, (list_disj l --> a ∨ list_disj l))]).
  2: apply MPRule_I. intros. inversion H6. subst.
  apply MP with (ps:=[(Γ, (A --> list_disj l) --> (list_disj l --> a ∨ list_disj l) --> (A --> a ∨ list_disj l));(Γ, (A --> list_disj l))]).
  2: apply MPRule_I. intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA1_I. exists A.
  exists (list_disj l). exists (a ∨ list_disj l). auto. inversion H8. subst. apply list_disj_In0 ; auto. inversion H9.
  inversion H7. subst. apply Ax. apply AxRule_I. apply RA3_I. exists a. exists (list_disj l). auto. inversion H8.
  inversion H3. subst. 2: inversion H4. apply wimp_Id_gen.
Qed.


(* ------------------------------------------------------------------------------------------------------ *)

(* Some proof-theoretical results about list_conj. *)

Lemma list_conj_in_list : forall Γ l A,
  List.In A l ->
  FOwBIH_rules (Γ, (list_conj l) --> A).
Proof.
induction l.
- intros. inversion H.
- intros. simpl. inversion H. subst. apply Ax. apply AxRule_I. apply RA5_I.
  exists A. exists (list_conj l). auto. apply IHl in H0.
  apply MP with (ps:=[(Γ, (list_conj l --> A) --> (a ∧ list_conj l --> A));(Γ, list_conj l --> A)]).
  2: apply MPRule_I. intros. inversion H1. subst.
  apply MP with (ps:=[(Γ, (a ∧ list_conj l --> list_conj l) --> (list_conj l --> A) --> (a ∧ list_conj l --> A));(Γ, a ∧ list_conj l --> list_conj l)]).
  2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists (a ∧ list_conj l). exists (list_conj l). exists A. auto. inversion H3. subst.
  apply Ax. apply AxRule_I. apply RA6_I. exists a. exists (list_conj l). auto. inversion H4.
  inversion H2. subst. auto. inversion H3.
Qed.

Lemma finite_context_list_conj : forall Γ A,
  FOwBIH_rules (Γ, A) ->
  (forall l, (forall A : form, (Γ A -> List.In A l) * (List.In A l -> Γ A)) ->
  FOwBIH_rules (Singleton _ (list_conj l), A)).
Proof.
intros. pose (FOwBIH_comp _ H (Singleton form (list_conj l))). apply f. intros. clear f.
simpl in H1.
apply MP with (ps:=[(Singleton form (list_conj l), (list_conj l) --> A0);(Singleton form (list_conj l), list_conj l)]).
2: apply MPRule_I. intros. inversion H2. subst. apply list_conj_in_list. apply H0. auto.
inversion H3. subst. 2: inversion H4. apply Id. apply IdRule_I. apply In_singleton.
Qed.

Lemma der_list_conj_finite_context : forall l (Γ : Ensemble _),
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  FOwBIH_rules (Γ, list_conj l).
Proof.
induction l ; intros.
- simpl. apply wTop.
- simpl. destruct (In_dec l a).
  + assert (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)).
     intros. split ; intro. apply H in H0. inversion H0. subst. auto. auto.
     apply H. apply in_cons ; auto. pose (IHl Γ H0).
     apply MP with (ps:=[(Γ, list_conj l --> (a ∧ list_conj l));(Γ, list_conj l)]). 2: apply MPRule_I.
     intros. inversion H1. subst.
     apply MP with (ps:=[(Γ, (list_conj l --> list_conj l) --> (list_conj l --> (a ∧ list_conj l)));(Γ, list_conj l --> list_conj l)]). 2: apply MPRule_I.
     intros. inversion H2. subst.
     apply MP with (ps:=[(Γ, (list_conj l --> a) --> (list_conj l --> list_conj l) --> (list_conj l --> (a ∧ list_conj l)));(Γ, list_conj l --> a)]). 2: apply MPRule_I.
     intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA7_I. exists (list_conj l). exists a. exists (list_conj l). auto.
     inversion H4. 2: inversion H5. subst. apply MP with (ps:=[(Γ, a --> list_conj l --> a);(Γ, a)]).
     2: apply MPRule_I. intros. inversion H5. subst. apply wThm_irrel. inversion H6. subst. apply Id.
     apply IdRule_I. apply H. apply in_eq. inversion H7. inversion H3. subst. apply wimp_Id_gen. inversion H4.
     inversion H2 ; subst ; auto. inversion H3.
  + assert (J1: (forall B : form, ((fun x : form => In form Γ x /\ x <> a) B -> List.In B l) * (List.In B l -> (fun x : form => In form Γ x /\ x <> a) B))).
     intros. split ; intro. destruct H0. apply H in H0. inversion H0. subst. exfalso. apply H1 ; auto. auto.
     split. apply H. apply in_cons ; auto. intro. subst. auto.
     pose (IHl (fun x => In _ Γ x /\ x <> a) J1).
     apply MP with (ps:=[(Γ, list_conj l --> (a ∧ list_conj l));(Γ, list_conj l)]). 2: apply MPRule_I.
     intros. inversion H0. subst.
     apply MP with (ps:=[(Γ, (list_conj l --> list_conj l) --> (list_conj l --> (a ∧ list_conj l)));(Γ, list_conj l --> list_conj l)]). 2: apply MPRule_I.
     intros. inversion H1. subst.
     apply MP with (ps:=[(Γ, (list_conj l --> a) --> (list_conj l --> list_conj l) --> (list_conj l --> (a ∧ list_conj l)));(Γ, list_conj l --> a)]). 2: apply MPRule_I.
     intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA7_I. exists (list_conj l). exists a. exists (list_conj l). auto.
     inversion H3. 2: inversion H4. subst. apply MP with (ps:=[(Γ, a --> list_conj l --> a);(Γ, a)]).
     2: apply MPRule_I. intros. inversion H4. subst. apply wThm_irrel. inversion H5. subst. apply Id.
     apply IdRule_I. apply H. apply in_eq. inversion H6. inversion H2. subst. apply wimp_Id_gen. inversion H3.
     inversion H1 ; subst ; auto. 2: inversion H2. apply FOwBIH_monot with (Γ1:=Γ) in f0. apply f0. simpl. intro. intros.
     inversion H2. auto.
Qed.

Lemma list_conj_finite_context : forall l (Γ : Ensemble _) A,
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  FOwBIH_rules (Singleton _ (list_conj l), A) ->
  FOwBIH_rules (Γ, A).
Proof.
intros.
assert (FOwBIH_rules (Singleton form (list_conj l), list_conj l)). apply Id. apply IdRule_I. apply In_singleton.
assert (forall A : form, In form (fst (Singleton form (list_conj l), list_conj l)) A -> FOwBIH_rules (Γ, A)).
intros. simpl in H2. inversion H2. subst. apply der_list_conj_finite_context ; auto.
pose (FOwBIH_comp (Singleton form (list_conj l), A) H0 Γ H2). simpl in f. auto.
Qed.




(* ---------------------------------------------------------------------------------------------------------------------------------------------------- *)

(* The dual of the modus ponens rule holds in FOwBIH. *)

Theorem dual_MP : forall A B Δ,
  wpair_der (Singleton _ (A --< B), Δ) ->
  wpair_der (Singleton _ B, Δ) ->
      wpair_der (Singleton _ A, Δ).
Proof.
intros. destruct H. destruct H0. destruct H. destruct H1. destruct H0. destruct H3. simpl in H1.
simpl in H2. simpl in H3. simpl in H4. unfold wpair_der. exists (x ++ remove_list x x0). repeat split.
apply add_remove_list_preserve_NoDup ; auto. intros. simpl. apply in_app_or in H5. destruct H5.
apply H1 ; auto. apply In_remove_list_In_list in H5. apply H3 ; auto. simpl.
assert (FOwBIH_rules (Singleton form (A --< B), list_disj (x ++ remove_list x x0))).
assert (Singleton form (A --< B) = Union _ (Empty_set _) (Singleton form (A --< B))).
apply Extensionality_Ensembles. split ; intro ; intro. apply Union_intror ; auto.
inversion H5. inversion H6. auto. rewrite H5. clear H5.
apply FOwBIH_Detachment_Theorem with (s:=(Empty_set form, (A --< B) --> list_disj (x ++ remove_list x x0))) ; auto.
apply der_list_disj_remove1. apply FOwBIH_Deduction_Theorem with (s:=( Union _ (Empty_set _) (Singleton form (A --< B)),list_disj x)) ; auto.
assert (Union form (Empty_set form) (Singleton form (A --< B)) = Singleton form (A --< B)).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H5. inversion H6. auto.
apply Union_intror ; auto. rewrite H5. clear H5. auto.
assert (FOwBIH_rules (Singleton form B, list_disj (x ++ remove_list x x0))).
assert (Singleton form B = Union _ (Empty_set _) (Singleton form B)).
apply Extensionality_Ensembles. split ; intro ; intro. apply Union_intror ; auto.
inversion H6. inversion H7. auto. rewrite H6. clear H6.
apply FOwBIH_Detachment_Theorem with (s:=(Empty_set form, B --> list_disj (x ++ remove_list x x0))) ; auto.
apply der_list_disj_remove2. apply FOwBIH_Deduction_Theorem with (s:=( Union _ (Empty_set _) (Singleton form B),list_disj x0)) ; auto.
assert (Union form (Empty_set form) (Singleton form B) = Singleton form B).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H6. inversion H7. auto.
apply Union_intror ; auto. rewrite H6. clear H6. auto.
assert (Singleton _ A = Union _ (Empty_set _) (Singleton _ A)). apply Extensionality_Ensembles.
split ; intro ; intro. apply Union_intror ; auto. inversion H7. subst. inversion H8. subst. auto.
rewrite H7. clear H7.
apply FOwBIH_Detachment_Theorem with (s:=(Empty_set form, A --> list_disj (x ++ remove_list x x0))) ; auto.
apply MP with (ps:=[(Empty_set form, ((B ∨ (A --< B)) --> list_disj (x ++ remove_list x x0)) --> (A --> list_disj (x ++ remove_list x x0)));
(Empty_set form, ((B ∨ (A --< B)) --> list_disj (x ++ remove_list x x0)))]). 2: apply MPRule_I.
intros. inversion H7 ; subst.
apply MP with (ps:=[(Empty_set form, (A --> (B ∨ (A --< B))) --> ((B ∨ (A --< B)) --> list_disj (x ++ remove_list x x0)) --> (A --> list_disj (x ++ remove_list x x0)));
(Empty_set form, A --> (B ∨ (A --< B)))]). 2: apply MPRule_I.
intros. inversion H8 ; subst. apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (B ∨ (A --< B)).
exists (list_disj (x ++ remove_list x x0)). auto. inversion H9 ; subst. 2: inversion H10. apply Ax.
apply AxRule_I. apply RA11_I. exists A. exists B ; auto. inversion H8. subst. 2: inversion H9.
apply MP with (ps:=[(Empty_set form, ((A --< B) --> list_disj (x ++ remove_list x x0)) --> ((B ∨ (A --< B)) --> list_disj (x ++ remove_list x x0)));
(Empty_set form, (A --< B) --> list_disj (x ++ remove_list x x0))]). 2: apply MPRule_I.
intros. inversion H9. subst.
apply MP with (ps:=[(Empty_set form, (B --> list_disj (x ++ remove_list x x0)) --> ((A --< B) --> list_disj (x ++ remove_list x x0)) --> ((B ∨ (A --< B)) --> list_disj (x ++ remove_list x x0)));
(Empty_set form, B --> list_disj (x ++ remove_list x x0))]). 2: apply MPRule_I.
intros. inversion H10. subst. apply Ax. apply AxRule_I. apply RA4_I. exists B. exists (A --< B).
exists (list_disj (x ++ remove_list x x0)). auto. inversion H11 ; subst. 2: inversion H12.
apply FOwBIH_Deduction_Theorem with (s:=(Union _ (Empty_set _) (Singleton form B), list_disj (x ++ remove_list x x0))) ; auto.
assert (Union form (Empty_set form) (Singleton form B) = Singleton form B).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H12. inversion H13. auto.
apply Union_intror ; auto. rewrite H12 ; auto. inversion H10. 2: inversion H11. subst.
apply FOwBIH_Deduction_Theorem with (s:=(Union _ (Empty_set _) (Singleton form (A --< B)), list_disj (x ++ remove_list x x0))) ; auto.
assert (Union form (Empty_set form) (Singleton form (A --< B)) = Singleton form (A --< B)).
apply Extensionality_Ensembles. split ; intro ; intro. inversion H11. inversion H12. auto.
apply Union_intror ; auto. rewrite H11 ; auto.
Qed.































(* ---------------------------------------------------------------------------------------------------------------------------------------------------- *)


(* To help for the results about FOsBIH. *)

Lemma eq_dec_nat : forall (n m : nat), (n = m) + (n <> m).
Proof.
induction n.
- destruct m.
  * auto.
  * auto.
- intro m. destruct m.
  * auto.
  * destruct IHn with (m:=m).
    + left. lia.
    + right. lia.
Qed.

Lemma wT_for_DN : forall A n m Γ, (le m n) -> (FOwBIH_rules (Γ, (DN_form n A) --> (DN_form m A))).
Proof.
intro A. induction n.
- intros. assert (m = 0). lia. rewrite H0. simpl. apply wimp_Id_gen.
- intros. destruct (eq_dec_nat m (S n)).
  * subst. apply wimp_Id_gen.
  * assert (m <= n). lia. pose (IHn m Γ H0).
    apply MP with (ps:=[(Γ, (DN_form n A --> DN_form m A) --> (DN_form (S n) A --> DN_form m A));(Γ, (DN_form n A --> DN_form m A))]).
    2: apply MPRule_I. intros. inversion H1. subst.
    apply MP with (ps:=[(Γ, (DN_form (S n) A --> DN_form n A) --> (DN_form n A --> DN_form m A) --> (DN_form (S n) A --> DN_form m A));(Γ, (DN_form (S n) A --> DN_form n A))]).
    2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (DN_form (S n) A).
    exists (DN_form n A). exists (DN_form m A). auto. inversion H3. subst. apply wDN_to_form.
    inversion H4. inversion H2. subst. assumption. inversion H3.
Qed.

Lemma wExcl_mon : forall A B C,
  (FOwBIH_rules (Empty_set _, A --> B)) ->
  (FOwBIH_rules (Empty_set _, (A --< C) --> (B --< C))).
Proof.
intros. apply wdual_residuation.
apply MP with (ps:=[(Empty_set _, (B --> C ∨ (B --< C)) --> (A --> C ∨ (B --< C)));
(Empty_set _, (B --> C ∨ (B --< C)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Empty_set _, (A --> B) --> (B --> C ∨ (B --< C)) --> (A --> C ∨ (B --< C)));
(Empty_set _, (A --> B))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (C ∨ (B --< C)). auto. inversion H2. subst. assumption. inversion H3.
inversion H1. subst.
apply Ax. apply AxRule_I. apply RA11_I. exists B. exists C. auto. inversion H2.
Qed.

Lemma wmon_Excl : forall A B C,
  (FOwBIH_rules (Empty_set _, A --> B)) ->
  (FOwBIH_rules (Empty_set _, (C --< B) --> (C --< A))).
Proof.
intros. apply wdual_residuation.
apply MP with (ps:=[(Empty_set _, (A ∨ (C --< A) --> B ∨ (C --< A)) --> (C --> B ∨ (C --< A)));
(Empty_set _, (A ∨ (C --< A) --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Empty_set _, (C --> A ∨ (C --< A)) --> (A ∨ (C --< A) --> B ∨ (C --< A)) --> (C --> B ∨ (C --< A)));
(Empty_set _, C --> A ∨ (C --< A))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists C. exists (A ∨ (C --< A)).
exists (B ∨ (C --< A)). auto. inversion H2. subst.
apply Ax. apply AxRule_I. apply RA11_I. exists C. exists A.
auto. inversion H3. inversion H1. subst. 2: inversion H2.
apply MP with (ps:=[(Empty_set _, ((C --< A) --> B ∨ (C --< A)) --> (A ∨ (C --< A) --> B ∨ (C --< A)));
(Empty_set _, ((C --< A) --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Empty_set _, (A --> B ∨ (C --< A)) --> ((C --< A) --> B ∨ (C --< A)) --> (A ∨ (C --< A) --> B ∨ (C --< A)));
(Empty_set _, (A --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists (C --< A).
exists (B ∨ (C --< A)). auto. inversion H4. subst.
apply MP with (ps:=[(Empty_set _, (B --> B ∨ (C --< A)) --> (A --> B ∨ (C --< A)));
(Empty_set _, (B --> B ∨ (C --< A)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Empty_set _, (A --> B) --> (B --> B ∨ (C --< A)) --> (A --> B ∨ (C --< A)));
(Empty_set _, (A --> B))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (B ∨ (C --< A)). auto. inversion H7. subst. assumption.
inversion H8. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists B. exists (C --< A). auto.
inversion H7. inversion H5. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists B. exists (C --< A). auto.
inversion H4.
Qed.

Lemma wOr_Neg : forall A B C Γ,
  (FOwBIH_rules (Γ, A --> (B ∨ C))) ->
  (FOwBIH_rules (Γ, ((¬ B) ∧ A) --> C)).
Proof.
intros.
apply MP with (ps:=[(Γ, (((¬ B) ∧ ((B ∨ C))) --> C) --> ((¬ B) ∧ A --> C));(Γ, (¬ B) ∧ ((B ∨ C)) --> C)]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (((¬ B) ∧ A) --> ((¬ B) ∧ ((B ∨ C)))) --> (((¬ B) ∧ ((B ∨ C))) --> C) --> ((¬ B) ∧ A --> C));
(Γ, (((¬ B) ∧ A) --> ((¬ B) ∧ ((B ∨ C)))))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists ((¬ B) ∧ A). exists ((¬ B) ∧ ((B ∨ C))).
exists C. auto. inversion H2. subst.
apply MP with (ps:=[(Γ, ((¬ B) ∧ A --> ((B ∨ C))) --> ((¬ B) ∧ A --> (¬ B) ∧ ((B ∨ C))));
(Γ, ((¬ B) ∧ A --> ((B ∨ C))))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply MP with (ps:=[(Γ, ((¬ B) ∧ A --> (¬ B)) --> ((¬ B) ∧ A --> ((B ∨ C))) --> ((¬ B) ∧ A --> (¬ B) ∧ ((B ∨ C))));
(Γ, ((¬ B) ∧ A --> (¬ B)))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists ((¬ B) ∧ A). exists (¬ B).
exists ((B ∨ C)). auto. inversion H5. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists (¬ B). exists A. auto.
inversion H6. inversion H4. subst.
apply MP with (ps:=[(Γ, (A --> (B ∨ C)) --> ((¬ B) ∧ A --> (B ∨ C)));
(Γ, (A --> (B ∨ C)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, ((¬ B) ∧ A --> A) --> (A --> (B ∨ C)) --> ((¬ B) ∧ A --> (B ∨ C)));
(Γ, ((¬ B) ∧ A --> A))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists ((¬ B) ∧ A). exists A.
exists ((B ∨ C)). auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists (¬ B). exists A. auto.
inversion H8. inversion H6. subst. assumption. inversion H7. inversion H5. inversion H3.
inversion H1. subst.
apply MP with (ps:=[(Γ, ((B ∨ C) ∧ (¬ B) --> C) --> ((¬ B) ∧ ((B ∨ C)) --> C));
(Γ, ((B ∨ C) ∧ (¬ B) --> C))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, ((¬ B) ∧ ((B ∨ C)) --> (B ∨ C) ∧ (¬ B)) --> ((B ∨ C) ∧ (¬ B) --> C) --> ((¬ B) ∧ ((B ∨ C)) --> C));
(Γ, (¬ B) ∧ ((B ∨ C)) --> (B ∨ C) ∧ (¬ B))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists ((¬ B) ∧ ((B ∨ C))). exists ((B ∨ C) ∧ (¬ B)).
exists C. auto. inversion H4. subst.
apply MP with (ps:=[(Γ, ((¬ B) ∧ ((B ∨ C)) --> (¬ B)) --> ((¬ B) ∧ ((B ∨ C)) --> (B ∨ C) ∧ (¬ B)));
(Γ, ((¬ B) ∧ ((B ∨ C)) --> (¬ B)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, ((¬ B) ∧ ((B ∨ C)) --> ((B ∨ C))) --> ((¬ B) ∧ ((B ∨ C)) --> (¬ B)) --> ((¬ B) ∧ ((B ∨ C)) --> (B ∨ C) ∧ (¬ B)));
(Γ, ((¬ B) ∧ ((B ∨ C)) --> ((B ∨ C))))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists ((¬ B) ∧ ((B ∨ C))). exists ((B ∨ C)).
exists (¬ B). auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists (¬ B). exists ((B ∨ C)).
auto. inversion H8. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists (¬ B). exists ((B ∨ C)).
auto. inversion H7. inversion H5. inversion H3. subst.
apply MP with (ps:=[(Γ, (((B ∨ C)) --> (¬ B) --> C) --> ((B ∨ C) ∧ (¬ B) --> C));
(Γ, (((B ∨ C)) --> (¬ B) --> C))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA8_I. exists ((B ∨ C)). exists (¬ B). exists C.
auto. inversion H5. subst.
apply MP with (ps:=[(Γ, (C --> ¬ B --> C) --> ((B ∨ C) --> ¬ B --> C));
(Γ, (C --> ¬ B --> C))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply MP with (ps:=[(Γ, (B --> ¬ B --> C) --> (C --> ¬ B --> C) --> ((B ∨ C) --> ¬ B --> C));
(Γ, (B --> ¬ B --> C))]).
2: apply MPRule_I. intros. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (¬ B --> C). auto. inversion H8. subst.
apply MP with (ps:=[(Γ, ((B ∧ (¬ B)) --> C) --> (B --> ¬ B --> C));
(Γ, ((B ∧ (¬ B)) --> C))]).
2: apply MPRule_I. intros. inversion H9. subst.
apply Ax. apply AxRule_I. apply RA9_I. exists B. exists (¬ B). exists C.
auto. inversion H10. subst.
apply MP with (ps:=[(Γ, (⊥ --> C) --> (B ∧ (¬ B) --> C));
(Γ, (⊥ --> C))]).
2: apply MPRule_I. intros. inversion H11. subst.
apply MP with (ps:=[(Γ, (B ∧ (¬ B) --> ⊥) --> (⊥ --> C) --> (B ∧ (¬ B) --> C));
(Γ, (B ∧ (¬ B) --> ⊥))]).
2: apply MPRule_I. intros. inversion H12. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (B ∧ (¬ B)). exists (⊥).
exists (C). auto. inversion H13. subst. apply wContr_Bot. inversion H14. inversion H12. subst.
apply wEFQ. inversion H13. inversion H11. inversion H9. inversion H7. subst.
apply wThm_irrel. inversion H8. inversion H6. inversion H4. inversion H2.
Qed.

Lemma wNeg_Top : forall A B Γ,
  (FOwBIH_rules (Γ, ((∞ A) --> B))) ->
  (FOwBIH_rules (Γ, (⊤ --< A) --> B)).
Proof.
intros A B Γ D. apply MP with (ps:=[(Γ, (∞ A --> B) --> ((⊤ --< A) --> B));
(Γ, (∞ A --> B))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((⊤ --< A) --> ∞ A) --> (∞ A --> B) --> (⊤ --< A) --> B);
(Γ, ((⊤ --< A) --> ∞ A))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I.
apply RA1_I. exists (⊤ --< A). exists (∞ A). exists B. auto.
inversion H1. subst. apply wimp_Id_gen.
inversion H2. inversion H0. subst. assumption. inversion H1.
Qed.

Lemma Top_wNeg : forall A B Γ,
  (FOwBIH_rules (Γ, (⊤ --< A) --> B)) ->
  (FOwBIH_rules (Γ, ((∞ A) --> B))).
Proof.
intros A B Γ D. apply MP with (ps:=[(Γ, ((⊤ --< A) --> B) --> (∞ A --> B));
(Γ, ((⊤ --< A) --> B))]). 2: apply MPRule_I. intros. inversion H. subst.
intros. apply MP with (ps:=[(Γ, (∞ A --> (⊤ --< A)) --> ((⊤ --< A) --> B) --> ∞ A --> B);
(Γ, (∞ A --> (⊤ --< A)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I.
apply RA1_I. exists (∞ A). exists (⊤ --< A). exists B. auto.
inversion H1. subst. apply wimp_Id_gen.
inversion H2. inversion H0. subst. assumption. inversion H1.
Qed.

Lemma Top_wNeg_cons : forall A B Γ,
  (FOwBIH_rules (Γ, A --> (⊤ --< B))) ->
  (FOwBIH_rules (Γ, A --> (∞ B))).
Proof.
intros. apply MP with (ps:=[(Γ, ((⊤ --< B) --> ∞ B) --> (A --> ∞ B));
(Γ, ((⊤ --< B) --> ∞ B))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A --> (⊤ --< B)) --> ((⊤ --< B) --> ∞ B) --> (A --> ∞ B));
(Γ, (A --> (⊤ --< B)))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I.
apply RA1_I. exists A. exists (⊤ --< B). exists (∞ B). auto.
inversion H2. subst. assumption. inversion H3. inversion H1. subst.
apply wimp_Id_gen. inversion H2.
Qed.

Lemma Or_imp_assoc : forall A B C D Γ,
  (FOwBIH_rules (Γ, A --> ((B ∨ C) ∨ D))) ->
  (FOwBIH_rules (Γ, A --> (B ∨ (C ∨ D)))).
Proof.
intros.
apply MP with (ps:=[(Γ, ((B ∨ C) ∨ D --> B ∨ (C ∨ D)) --> (A --> B ∨ (C ∨ D)));
(Γ, ((B ∨ C) ∨ D --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A --> (B ∨ C) ∨ D) --> ((B ∨ C) ∨ D --> B ∨ (C ∨ D)) --> (A --> B ∨ (C ∨ D)));
(Γ, (A --> (B ∨ C) ∨ D))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists ((B ∨ C) ∨ D).
exists (B ∨ (C ∨ D)). auto. inversion H2. subst.
assumption. inversion H3. inversion H1. subst.
apply MP with (ps:=[(Γ, (D --> B ∨ (C ∨ D)) --> ((B ∨ C) ∨ D --> B ∨ (C ∨ D)));
(Γ, (D --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, (((B ∨ C)) --> B ∨ (C ∨ D)) --> (D --> B ∨ (C ∨ D)) --> ((B ∨ C) ∨ D --> B ∨ (C ∨ D)));
(Γ, (((B ∨ C)) --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists ((B ∨ C)).
exists D. exists (B ∨ (C ∨ D)). auto. inversion H4. subst.
apply MP with (ps:=[(Γ, (C --> B ∨ (C ∨ D)) --> ((B ∨ C) --> B ∨ (C ∨ D)));
(Γ, C --> B ∨ (C ∨ D))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, (B --> B ∨ (C ∨ D)) --> (C --> B ∨ (C ∨ D)) --> ((B ∨ C) --> B ∨ (C ∨ D)));
(Γ, B --> B ∨ (C ∨ D))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (B ∨ (C ∨ D)). auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists B. exists (C ∨ D). auto.
inversion H8. inversion H6. subst.
apply MP with (ps:=[(Γ, ((C ∨ D) --> B ∨ (C ∨ D)) --> (C --> B ∨ (C ∨ D)));
(Γ, (C ∨ D) --> B ∨ (C ∨ D))]). 2: apply MPRule_I. intros. inversion H7. subst.
apply MP with (ps:=[(Γ, (C --> (C ∨ D)) --> ((C ∨ D) --> B ∨ (C ∨ D)) --> (C --> B ∨ (C ∨ D)));
(Γ, (C --> (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H8. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists C. exists (C ∨ D).
exists (B ∨ (C ∨ D)). auto. inversion H9. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists C. exists D. auto. inversion H10.
inversion H8. subst. apply Ax. apply AxRule_I.
apply RA3_I. exists B. exists (C ∨ D). auto. inversion H9. inversion H7. inversion H5.
inversion H3. subst.
apply MP with (ps:=[(Γ, ((C ∨ D) --> B ∨ (C ∨ D)) --> (D --> B ∨ (C ∨ D)));
(Γ, ((C ∨ D) --> B ∨ (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply MP with (ps:=[(Γ, (D --> (C ∨ D)) --> ((C ∨ D) --> B ∨ (C ∨ D)) --> (D --> B ∨ (C ∨ D)));
(Γ, (D --> (C ∨ D)))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists D. exists (C ∨ D).
exists (B ∨ (C ∨ D)). auto. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists C. exists D. auto. inversion H7.
inversion H5. subst. apply Ax. apply AxRule_I. apply RA3_I. exists B. exists (C ∨ D). auto.
inversion H6. inversion H4. inversion H2.
Qed.

Lemma wClaim1 : forall A B Γ,
    (FOwBIH_rules (Γ, (¬ (A --< B)) --> ((∞ B) --> (∞ A)))).
Proof.
intros A B Γ.
pose (FOwBIH_monot (Empty_set _, (¬ (A --< B)) --> ((∞ B) --> ∞ A))). apply f.
apply MP with (ps:=[(Empty_set _, (((¬ (A --< B)) ∧ (∞ B)) --> ∞ A) --> (¬ (A --< B) --> ∞ B --> ∞ A));
(Empty_set _, ((¬ (A --< B)) ∧ (∞ B)) --> ∞ A)]). 2: apply MPRule_I. intros. inversion H. subst.
apply Ax. apply AxRule_I. apply RA9_I. exists (¬ (A --< B)).
exists (∞ B). exists (∞ A). auto. inversion H0. subst.
apply MP with (ps:=[(Empty_set _, ((⊤ --< ((B ∨ (A --< B)))) --> ∞ A) --> ((¬ (A --< B)) ∧ (∞ B) --> ∞ A));
(Empty_set _, (⊤ --< ((B ∨ (A --< B)))) --> ∞ A)]). 2: apply MPRule_I. intros. inversion H1. subst.
apply MP with (ps:=[(Empty_set _, ((¬ (A --< B)) ∧ (∞ B) --> (⊤ --< ((B ∨ (A --< B))))) --> ((⊤ --< ((B ∨ (A --< B)))) --> ∞ A) --> ((¬ (A --< B)) ∧ (∞ B) --> ∞ A));
(Empty_set _, ((¬ (A --< B)) ∧ (∞ B) --> (⊤ --< ((B ∨ (A --< B))))))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists ((¬ (A --< B)) ∧ (∞ B)).
exists (⊤ --< ((B ∨ (A --< B)))). exists (∞ A). auto. inversion H3. subst.
apply wOr_Neg. apply Top_wNeg. apply wdual_residuation.
apply Or_imp_assoc. apply wdual_residuation. apply wimp_Id_gen. inversion H4. inversion H2. subst.
apply Top_wNeg_cons. apply wmon_Excl. apply Ax. apply AxRule_I.
apply RA11_I. exists A. exists B. auto. inversion H3. inversion H1.
intro. intro. inversion H.
Qed.

Lemma wDN_dist_imp : forall A B Γ,
    (FOwBIH_rules (Γ, (¬ (∞ (A --> B))) --> ((¬ (∞ A)) --> (¬ (∞ B))))).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ, (((∞ B) --> ∞ A) --> ¬ (∞ A) --> ¬ (∞ B)) --> (¬ (∞ (A --> B)) --> ¬ (∞ A) --> ¬ (∞ B)));
(Γ, (((∞ B) --> ∞ A) --> ¬ (∞ A) --> ¬ (∞ B)))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (¬ (∞ (A --> B)) --> ((∞ B) --> ∞ A)) --> (((∞ B) --> ∞ A) --> ¬ (∞ A) --> ¬ (∞ B)) --> (¬ (∞ (A --> B)) --> ¬ (∞ A) --> ¬ (∞ B)));
(Γ, (¬ (∞ (A --> B)) --> ((∞ B) --> ∞ A)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (¬ (∞ (A --> B))).
exists (∞ B --> ∞ A). exists (¬ (∞ A) --> ¬ (∞ B)). auto. inversion H1. subst.
apply MP with (ps:=[(Γ,((¬ (A --< B)) --> (∞ B --> ∞ A)) --> (¬ (∞ (A --> B)) --> ∞ B --> ∞ A));
(Γ, ((¬ (A --< B)) --> (∞ B --> ∞ A)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ,(¬ (∞ (A --> B)) --> (¬ (A --< B))) --> ((¬ (A --< B)) --> (∞ B --> ∞ A)) --> (¬ (∞ (A --> B)) --> ∞ B --> ∞ A));
(Γ, (¬ (∞ (A --> B)) --> (¬ (A --< B))))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (¬ (∞ (A --> B))).
exists (¬ (A --< B)). exists (∞ B --> ∞ A). auto. inversion H4. subst.
apply MP with (ps:=[(Γ, ((A --< B) --> (∞ (A --> B))) --> (¬ (∞ (A --> B)) --> ¬ (A --< B)));
(Γ, (A --< B) --> (∞ (A --> B)))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply Ax. apply AxRule_I. apply RA10_I. exists (A --< B).
exists (∞ (A --> B)). auto. inversion H6. subst. apply Ax.
apply AxRule_I. apply RA12_I. exists A. exists B. auto. inversion H7. inversion H5.
inversion H3. subst. apply wClaim1. inversion H4. inversion H2. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA10_I. exists (∞ B).
exists (∞ A). auto. inversion H1.
Qed.

End wMeta.



