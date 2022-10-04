Require Import List.
Export ListNotations.

Require Import genT.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import BiInt_GHC.
Require Import BiInt_logics.
Require Import BiInt_extens_interactions.

Lemma wThm_irrel : forall A B Γ, wBIH_rules (Γ, A → (B → A)).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ,(And A B → A) → (A → (B → A)));(Γ, (And A B → A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply Ax. apply AxRule_I. apply RA9_I. exists A. exists B. exists A. auto.
inversion H0. subst. apply Ax.
apply AxRule_I. apply RA5_I. exists A. exists B. auto. inversion H1.
Qed.

Lemma wimp_Id_gen : forall A Γ, wBIH_rules (Γ, A → A).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, (And A A → A) → (A → A)); (Γ, (And A A → A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((And (And A A → A) A) → A) → (And A A → A) → (A → A)); (Γ, (And (And A A → A) A) → A)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA9_I.
exists (And A A → A). exists A. exists A. auto. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA6_I.
exists (And A A → A). exists A. auto. inversion H2. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists A. exists A. auto. inversion H1.
Qed.

Lemma comm_And_obj : forall A B Γ,
    (wBIH_rules (Γ, And A B → And B A)).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ, (And A B → A) → (And A B → And B A));(Γ, (And A B → A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (And A B → B) → (And A B → A) → (And A B → And B A));(Γ, (And A B → B))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists (And A B). exists B. exists A.
auto. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists A. exists B. auto. inversion H2.
inversion H0. subst. apply Ax. apply AxRule_I. apply RA5_I. exists A. exists B. auto.
inversion H1.
Qed.

Lemma wContr_Bot : forall A Γ, wBIH_rules (Γ, And A (Neg A) → (Bot V)).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, (And (Neg A) A → Bot V) → (And A (Neg A) → Bot V));(Γ, And (Neg A) A → Bot V)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (And A (Neg A) → And (Neg A) A) → (And (Neg A) A → Bot V) → (And A (Neg A) → Bot V));(Γ, And A (Neg A) → And (Neg A) A)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (And A (Neg A)). exists (And (Neg A) A). exists (Bot V). auto. inversion H1.
subst. apply comm_And_obj. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ, ((Neg A) → A → Bot V) → (And (Neg A) A  → Bot V));(Γ, ((Neg A) → A → Bot V))]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
apply AxRule_I. apply RA8_I. exists (Neg A). exists A. exists (Bot V). auto. inversion H2.
subst. apply wimp_Id_gen. inversion H3. inversion H1.
Qed.

Lemma wmonotR_Or : forall A B Γ,
    (wBIH_rules (Γ, A → B)) ->
    (forall C, wBIH_rules (Γ, (Or A C) → (Or B C))).
Proof.
intros A B Γ D C.
apply MP with (ps:=[(Γ, (C → Or B C) → (Or A C → Or B C));(Γ,(C → Or B C))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A → Or B C) → (C → Or B C) → (Or A C → Or B C));(Γ,(A → Or B C))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists C.
exists (Or B C). auto. inversion H1. subst.
apply MP with (ps:=[(Γ, (B → Or B C) → (A → Or B C));(Γ,((B → Or B C)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, (A → B) → (B → Or B C) → (A → Or B C));(Γ,(A → B))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists A. exists B. exists (Or B C). auto.
inversion H4. subst. assumption. inversion H5. inversion H3. subst. apply Ax.
apply AxRule_I. apply RA2_I. exists B. exists C.
auto. inversion H4. inversion H2. inversion H0. subst. apply Ax. apply AxRule_I. apply RA3_I.
exists B. exists C. auto. inversion H1.
Qed.

Lemma wmonotL_Or : forall A B Γ,
    (wBIH_rules (Γ, A → B)) ->
    (forall C, wBIH_rules (Γ, (Or C A) → (Or C B))).
Proof.
intros A B Γ D C.
apply MP with (ps:=[(Γ, (A → Or C B) → ((Or C A) → (Or C B)));(Γ,(A → Or C B))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (C → Or C B) → (A → Or C B) → ((Or C A) → (Or C B)));(Γ,(C → Or C B))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA4_I. exists C. exists A.
exists (Or C B). auto. inversion H1. subst. apply Ax.
apply AxRule_I. apply RA2_I. exists C. exists B.
auto. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ, (B → Or C B) → (A → Or C B));(Γ,((B → Or C B)))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply MP with (ps:=[(Γ, (A → B) → (B → Or C B) → (A → Or C B));(Γ,(A → B))]).
2: apply MPRule_I. intros. inversion H2. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists A. exists B. exists (Or C B). auto. inversion H3. subst.
assumption. inversion H4. inversion H2. subst. apply Ax.
apply AxRule_I. apply RA3_I. exists C. exists B.
auto. inversion H3. inversion H1.
Qed.

Lemma comm_Or_obj : forall A B Γ, (wBIH_rules (Γ, Or A B → Or B A)).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ, (B → Or B A) → (Or A B → Or B A));(Γ, (B → Or B A))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A → Or B A) → (B → Or B A) → (Or A B → Or B A));(Γ, (A → Or B A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists B. exists (Or B A).
auto. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists B. exists A. auto.
inversion H2. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists B. exists A. auto.
inversion H1.
Qed.

Lemma comm_Or : forall A B Γ, (wBIH_rules (Γ, Or A B)) -> (wBIH_rules (Γ, Or B A)).
Proof.
intros A B Γ D.
apply MP with (ps:=[(Γ, Or A B → Or B A);(Γ, Or A B)]).
2: apply MPRule_I. intros. inversion H. subst. apply comm_Or_obj.
inversion H0. subst. assumption. inversion H1.
Qed.

Lemma wmonot_Or2 : forall A B Γ, (wBIH_rules (Γ, A → B)) ->
    (forall C, wBIH_rules (Γ, (Or A C) → (Or C B))).
Proof.
intros A B Γ D C.
apply MP with (ps:=[(Γ, (C → Or C B) → (Or A C → Or C B));(Γ, C → Or C B)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (A → Or C B) → (C → Or C B) → (Or A C → Or C B));(Γ, A → Or C B)]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax.
apply AxRule_I. apply RA4_I. exists A. exists C. exists (Or C B). auto.
inversion H1. subst.
apply MP with (ps:=[(Γ, (B → Or C B) → (A → Or C B));(Γ, B → Or C B)]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, (A → B) → (B → Or C B) → (A → Or C B));(Γ, A → B)]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists B. exists (Or C B).
auto. inversion H4. subst. assumption. inversion H5. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists C. exists B. auto. inversion H4.
inversion H2. inversion H0. subst. apply Ax. apply AxRule_I.
apply RA2_I. exists C. exists B. auto. inversion H1.
Qed.

Theorem wdual_residuation0 : forall A B C,
  (wBIH_rules (Empty_set _, (Excl A B) → C) ->
      wBIH_rules (Empty_set _, A → (Or B C))).
Proof.
intros A B C D. pose (@wmonot_Or2 (Excl A B) C (Empty_set _) D B).
apply MP with (ps:=[(Empty_set _, (Or (Excl A B) B → Or B C) → (A → Or B C));(Empty_set _,Or (Excl A B) B → Or B C)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Empty_set _, (A → Or (Excl A B) B) → (Or (Excl A B) B → Or B C) → (A → Or B C));(Empty_set _,(A → Or (Excl A B) B))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (Or (Excl A B) B). exists (Or B C). auto.
inversion H1. subst.
apply MP with (ps:=[(Empty_set _, (Or B (Excl A B) → Or (Excl A B) B) → (A → Or (Excl A B) B));(Empty_set _,(Or B (Excl A B) → Or (Excl A B) B))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Empty_set _, (A → Or B (Excl A B)) → (Or B (Excl A B) → Or (Excl A B) B) → (A → Or (Excl A B) B));(Empty_set _,(A → Or B (Excl A B)))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists A. exists (Or B (Excl A B)). exists (Or (Excl A B) B).
auto. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA11_I. exists A. exists B. auto. inversion H5.
inversion H3. subst. apply comm_Or_obj. inversion H4. inversion H2. inversion H0.
subst. assumption. inversion H1.
Qed.

Lemma wDN_to_form : forall A Γ, (wBIH_rules (Γ, Neg (wNeg A)→ A)).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, (Top _)  → Neg (wNeg A) → A);(Γ, Top _)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, ((And (Top _) (Neg (wNeg A))) → A) → ((Top _) → (Neg (wNeg A)) → A));(Γ, ((And (Top _) (Neg (wNeg A))) → A))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
apply RA9_I. exists (Top V). exists (Neg (wNeg A)). exists A. auto.
inversion H1. subst.
apply MP with (ps:=[(Γ, ((And (Neg (wNeg A)) (Top V))→ A) → (And (Top V) (Neg (wNeg A)) → A));(Γ, (And (Neg (wNeg A)) (Top V))→ A)]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, ((And (Top V) (Neg (wNeg A))) → (And (Neg (wNeg A)) (Top V))) → ((And (Neg (wNeg A)) (Top V))→ A) → (And (Top V) (Neg (wNeg A)) → A));
(Γ, ((And (Top V) (Neg (wNeg A))) → (And (Neg (wNeg A)) (Top V))))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (And (Top V) (Neg (wNeg A))). exists (And (Neg (wNeg A)) (Top V)).
exists A. auto. inversion H4. subst.
apply MP with (ps:=[(Γ, (And (Top V) (Neg (wNeg A)) → (Top V)) → And (Top V) (Neg (wNeg A)) → And (Neg (wNeg A)) (Top V));
(Γ, And (Top V) (Neg (wNeg A)) → (Top V))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, (And (Top V) (Neg (wNeg A)) → (Neg (wNeg A))) → (And (Top V) (Neg (wNeg A)) → (Top V)) → And (Top V) (Neg (wNeg A)) → And (Neg (wNeg A)) (Top V));
(Γ, And (Top V) (Neg (wNeg A)) → (Neg (wNeg A)))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists (And (Top V) (Neg (wNeg A))).
exists (Neg (wNeg A)). exists (Top V). auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists (Top V).
exists (Neg (wNeg A)). auto. inversion H8. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists (Top V).
exists (Neg (wNeg A)). auto. inversion H7. inversion H5. inversion H3. subst.
apply MP with (ps:=[(Γ, ((Neg (wNeg A)) → (Top V) → A) → And (Neg (wNeg A)) (Top V) → A);
(Γ, ((Neg (wNeg A)) → (Top V) → A))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA8_I. exists (Neg (wNeg A)).
exists (Top V). exists A. auto. inversion H5. subst.
apply MP with (ps:=[(Γ, (((wNeg A) → (Bot V)) → Top V → A) → (Neg (wNeg A) → Top V → A));
(Γ, (((wNeg A) → (Bot V)) → Top V → A))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply MP with (ps:=[(Γ, (Neg (wNeg A) → ((wNeg A) → (Bot V))) → (((wNeg A) → (Bot V)) → Top V → A) → (Neg (wNeg A) → Top V → A));
(Γ, Neg (wNeg A) → ((wNeg A) → (Bot V)))]). 2: apply MPRule_I. intros. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (Neg (wNeg A)).
exists (wNeg A → Bot V). exists (Top V → A). auto. inversion H8. subst.
apply wimp_Id_gen. inversion H9.
inversion H7. subst.
apply MP with (ps:=[(Γ, (((Excl (Top V) A) → Bot V) → Top V → A) → (wNeg A → Bot V) → Top V → A);(Γ, ((Excl (Top V) A) → Bot V) → Top V → A)]).
2: apply MPRule_I. intros. inversion H8. subst.
apply MP with (ps:=[(Γ, ((wNeg A → Bot V) → ((Excl (Top V) A) → Bot V)) → (((Excl (Top V) A) → Bot V) → Top V → A) → (wNeg A → Bot V) → Top V → A);
(Γ, (wNeg A → Bot V) → ((Excl (Top V) A) → Bot V))]).
2: apply MPRule_I. intros. inversion H9. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists (wNeg A → Bot V). exists (Excl (Top V) A → Bot V).
exists (Top V → A). auto. inversion H10. subst.
apply MP with (ps:=[(Γ, (Excl (Top V) A → (wNeg A)) → ((wNeg A → Bot V) → Excl (Top V) A → Bot V));(Γ, (Excl (Top V) A → (wNeg A)))]).
2: apply MPRule_I. intros. inversion H11. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (Excl (Top V) A). exists (wNeg A). exists (Bot V). auto. inversion H12. subst.
apply wimp_Id_gen.
inversion H13. inversion H11. inversion H9. subst.
apply MP with (ps:=[(Γ, (Neg (Excl (Top V) A) → Top V → A) → ((Excl (Top V) A → Bot V) → Top V → A));(Γ, (Neg (Excl (Top V) A) → Top V → A))]).
2: apply MPRule_I. intros. inversion H10. subst.
apply MP with (ps:=[(Γ, ((Excl (Top V) A → Bot V) → Neg (Excl (Top V) A)) → (Neg (Excl (Top V) A) → Top V → A) → ((Excl (Top V) A → Bot V) → Top V → A));
(Γ, (Excl (Top V) A → Bot V) → Neg (Excl (Top V) A))]).
2: apply MPRule_I. intros. inversion H11. subst. apply Ax.
apply AxRule_I. apply RA1_I. exists (Excl (Top V) A → Bot V). exists (Neg (Excl (Top V) A)).
exists (Top V → A). auto. inversion H12. subst.
apply wimp_Id_gen.
inversion H13. inversion H11. subst. apply Ax. apply AxRule_I.
apply RA14_I. exists (Top V). exists A. auto. inversion H12. inversion H10.
inversion H8. inversion H6. inversion H4. inversion H2. inversion H0. subst.
apply MP with (ps:=[(Γ, Imp (Imp A A) (Top V));(Γ, Imp A A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA15_I. exists (A → A). auto. inversion H2.
subst. apply wimp_Id_gen. inversion H3. inversion H1.
Qed.

Lemma wEFQ : forall A Γ, wBIH_rules (Γ, (Bot V) → A).
Proof.
intros A Γ.
apply MP with (ps:=[(Γ, ((Neg (wNeg A)) → A) → (Bot V → A));(Γ, (Neg (wNeg A)) → A)]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (Bot V → (Neg (wNeg A))) → ((Neg (wNeg A)) → A) → (Bot V → A));(Γ, (Bot V) → (Neg (wNeg A)))]).
2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (Bot V). exists (Neg (wNeg A)). exists A. auto.
inversion H1. subst.
apply MP with (ps:=[(Γ, (Neg (Top V) → Neg (wNeg A)) → (Bot V → Neg (wNeg A)));
(Γ, Neg (Top V) → Neg (wNeg A))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, (Bot V → Neg (Top V)) → (Neg (Top V) → Neg (wNeg A)) → (Bot V → Neg (wNeg A)));
(Γ, Bot V → Neg (Top V))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (Bot V). exists (Neg (Top V)). exists (Neg (wNeg A)). auto.
inversion H4. subst.
apply MP with (ps:=[(Γ, (((Top V) → (Bot V)) → Neg (Top V)) → (Bot V → Neg (Top V)));
(Γ, ((Top V) → (Bot V)) → Neg (Top V))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, (Bot V → ((Top V) → (Bot V))) → (((Top V) → (Bot V)) → Neg (Top V)) → (Bot V → Neg (Top V)));
(Γ, Bot V → ((Top V) → (Bot V)))]).
2: apply MPRule_I. intros. inversion H6. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (Bot V). exists ((Top V) → (Bot V)). exists (Neg (Top V)). auto.
inversion H7. subst. apply wThm_irrel. inversion H8. inversion H6. subst.
apply wimp_Id_gen. inversion H7. inversion H5. inversion H3. subst.
apply MP with (ps:=[(Γ, ((wNeg A) → (Top V)) → (Neg (Top V) → Neg (wNeg A)));
(Γ, ((wNeg A) → (Top V)))]).
2: apply MPRule_I. intros. inversion H4. subst. apply Ax. apply AxRule_I.
apply RA10_I. exists (wNeg A). exists (Top V). auto. inversion H5. subst.
apply MP with (ps:=[(Γ, (Top V) → (wNeg A → Top V));(Γ, Top V)]).
2: apply MPRule_I. intros. inversion H6. subst. apply wThm_irrel.
inversion H7. subst.
apply MP with (ps:=[(Γ, (A → A) → Top V);(Γ, A → A)]).
2: apply MPRule_I. intros. inversion H8. subst. apply Ax. apply AxRule_I.
apply RA15_I. exists (A → A). auto. inversion H9. subst. apply wimp_Id_gen.
inversion H10. inversion H8. inversion H6. inversion H4. inversion H2.
inversion H0. subst. apply wDN_to_form. inversion H1.
Qed.

Lemma absorp_Or1 : forall A Γ,
    (wBIH_rules (Γ, Or A (Bot V))) ->
    (wBIH_rules (Γ, A)).
Proof.
intros A Γ D.
apply MP with (ps:=[(Γ, Imp (Or A (Bot V)) A);(Γ, Or A (Bot V))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (Bot V → A) → (Or A (Bot V) → A));(Γ, (Bot V → A))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A → A) → (Bot V → A) → (Or A (Bot V) → A));(Γ, A → A)]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists (Bot V).
exists A. auto. inversion H2. subst. apply wimp_Id_gen. inversion H3.
inversion H1. subst. apply wEFQ. inversion H2. inversion H0. subst.
assumption. inversion H1.
Qed.

Theorem wdual_residuation : forall A B C,
  (wBIH_rules (Empty_set _, (Excl A B) → C) ->
      wBIH_rules (Empty_set _, A → (Or B C))) *
  (wBIH_rules (Empty_set _, A → (Or B C)) ->
      wBIH_rules (Empty_set _, (Excl A B) → C)).
Proof.
intros A B C. split.
- intro D. pose (@wmonot_Or2 (Excl A B) C (Empty_set _) D B).
  apply MP with (ps:=[(Empty_set _, (Or (Excl A B) B → Or B C) → (A → Or B C));(Empty_set _,Or (Excl A B) B → Or B C)]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Empty_set _, (A → Or (Excl A B) B) → (Or (Excl A B) B → Or B C) → (A → Or B C));(Empty_set _,(A → Or (Excl A B) B))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists (Or (Excl A B) B). exists (Or B C). auto.
  inversion H1. subst.
  apply MP with (ps:=[(Empty_set _, (Or B (Excl A B) → Or (Excl A B) B) → (A → Or (Excl A B) B));(Empty_set _,(Or B (Excl A B) → Or (Excl A B) B))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Empty_set _, (A → Or B (Excl A B)) → (Or B (Excl A B) → Or (Excl A B) B) → (A → Or (Excl A B) B));(Empty_set _,(A → Or B (Excl A B)))]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists (Or B (Excl A B)). exists (Or (Excl A B) B).
  auto. inversion H4. subst.
  apply Ax. apply AxRule_I. apply RA11_I. exists A. exists B. auto. inversion H5. inversion H3. subst. apply comm_Or_obj.
  inversion H4. inversion H2. inversion H0. subst. assumption. inversion H1.
- intro D. apply MP with (ps:=[(Empty_set _, ((Or C (Excl A (Or B C))) → C) → (Excl A B → C));(Empty_set _, (Or C (Excl A (Or B C))) → C)]).
  2: apply MPRule_I. intros. inversion H. subst.
  apply MP with (ps:=[(Empty_set _, (Excl A B → (Or C (Excl A (Or B C)))) → ((Or C (Excl A (Or B C))) → C) → (Excl A B → C));(Empty_set _, Excl A B → (Or C (Excl A (Or B C))))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I. apply RA1_I.
  exists (Excl A B). exists (Or C (Excl A (Or B C))). exists C. auto. inversion H1. subst.
  apply MP with (ps:=[(Empty_set _, ((Or C (Excl (Excl A B) C)) → Or C (Excl A (Or B C))) → (Excl A B → Or C (Excl A (Or B C))));(Empty_set _, ((Or C (Excl (Excl A B) C)) → Or C (Excl A (Or B C))))]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Empty_set _, (Excl A B → (Or C (Excl (Excl A B) C)))→ ((Or C (Excl (Excl A B) C)) → Or C (Excl A (Or B C))) → (Excl A B → Or C (Excl A (Or B C))));
  (Empty_set _, (Excl A B → (Or C (Excl (Excl A B) C))))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (Excl A B). exists (Or C (Excl (Excl A B) C)).
  exists (Or C (Excl A (Or B C))). auto. inversion H4. subst.
  apply Ax. apply AxRule_I. apply RA11_I. exists (Excl A B). exists C. auto. inversion H5.
  inversion H3. subst. apply wmonotL_Or.
  apply Ax. apply AxRule_I. apply RA13_I.
  exists A. exists B. exists C. auto. inversion H4. inversion H2. inversion H0. subst. 2: inversion H1.
  apply MP with (ps:=[(Empty_set _, (Or C (Bot _) → C) → (Or C (Excl A (Or B C)) → C));
  (Empty_set _, (Or C (Bot _) → C))]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply MP with (ps:=[(Empty_set _, (Or C (Excl A (Or B C)) → Or C (Bot _)) → (Or C (Bot _) → C) → (Or C (Excl A (Or B C)) → C));
  (Empty_set _, (Or C (Excl A (Or B C)) → Or C (Bot _)))]). 2: apply MPRule_I. intros. inversion H2. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (Or C (Excl A (Or B C))).
  exists (Or C (Bot V)). exists C. auto. inversion H3. subst. apply wmonotL_Or.
  apply MP with (ps:=[(Empty_set _, ((And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))) → Bot V) → (Excl A (Or B C) → Bot V));
  (Empty_set _, ((And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))) → Bot V))]). 2: apply MPRule_I. intros. inversion H4. subst.
  apply MP with (ps:=[(Empty_set _, (Excl A (Or B C) → (And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C))))) → ((And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))) → Bot V) → (Excl A (Or B C) → Bot V));
  (Empty_set _, (Excl A (Or B C) → (And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C))))))]). 2: apply MPRule_I. intros. inversion H5. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (Excl A (Or B C)).
  exists (And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))). exists (Bot V). auto. inversion H6. subst.
  apply MP with (ps:=[(Empty_set _, (Excl A (Or B C) → (Neg (wNeg (A → Or B C)))) → (Excl A (Or B C) → And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))));
  (Empty_set _, (Excl A (Or B C) → (Neg (wNeg (A → Or B C)))))]). 2: apply MPRule_I. intros. inversion H7. subst.
  apply MP with (ps:=[(Empty_set _, (Excl A (Or B C) → (wNeg (A → Or B C))) → (Excl A (Or B C) → (Neg (wNeg (A → Or B C)))) → (Excl A (Or B C) → And (wNeg (A → Or B C)) (Neg (wNeg (A → Or B C)))));
  (Empty_set _, (Excl A (Or B C) → (wNeg (A → Or B C))))]). 2: apply MPRule_I. intros. inversion H8. subst.
  apply Ax. apply AxRule_I. apply RA7_I. exists (Excl A (Or B C)).
  exists (wNeg (A → Or B C)). exists (Neg (wNeg (A → Or B C))). auto. inversion H9.
  subst. apply Ax. apply AxRule_I. apply RA12_I. exists A. exists (Or B C).
  auto. inversion H10. inversion H8. subst.
  apply MP with (ps:=[(Empty_set _, (Neg (wNeg (A → Or B C))) → (Excl A (Or B C) → Neg (wNeg (A → Or B C))));
  (Empty_set _, (Neg (wNeg (A → Or B C))))]). 2: apply MPRule_I. intros. inversion H9. subst.
  apply wThm_irrel. inversion H10. subst. apply DNw with (ps:=[(Empty_set _, A → Or B C)]).
  2: apply DNwRule_I. intros. inversion H11. subst. assumption. inversion H12. inversion H11.
  inversion H9. inversion H7. inversion H5. subst. apply wContr_Bot. inversion H6.
  inversion H4. inversion H2. subst.
  apply MP with (ps:=[(Empty_set _, (Bot V → C) → (Or C (Bot V) → C));(Empty_set _, (Bot V → C))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(Empty_set _, (C → C) → (Bot V → C) → (Or C (Bot V) → C));(Empty_set _, (C → C))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Ax.
  apply AxRule_I. apply RA4_I. exists C. exists (Bot V). exists C. auto.
  inversion H5. subst. apply wimp_Id_gen. inversion H6. inversion H4. subst.
  apply wEFQ. inversion H5. inversion H3.
Qed.

Lemma wAThm_irrel : forall A B Γ, wBIH_rules (Γ, (Excl A B) → A).
Proof.
intros A B Γ. pose (wBIH_monot (Empty_set _, Excl A B → A)). apply w.
apply wdual_residuation. apply Ax. apply AxRule_I.
apply RA3_I. exists B. exists A. auto. intro. intros. simpl in H.
inversion H.
Qed.

Theorem wdual_residuation_gen : forall A B C,
  (wpair_derrec (Empty_set _, Singleton _ ((Excl A B) → C)) ->
      wpair_derrec (Empty_set _, Singleton _ (A → (Or B C)))) *
  (wpair_derrec (Empty_set _, Singleton _ (A → (Or B C))) ->
      wpair_derrec (Empty_set _, Singleton _ ((Excl A B) → C))).
Proof.
intros A B C. split.
- intro. exists [(A → Or B C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H. subst. simpl. inversion H0. subst. apply In_singleton. inversion H2.
  * destruct H. destruct H. pose (wdual_residuation A B C). destruct p. simpl.
    simpl in w. simpl in w0. simpl in H0. destruct H0. destruct x.
    + simpl in H1. apply MP with (ps:=[(Empty_set _, Bot V → Or (A → Or B C) (Bot V));(Empty_set _, Bot V)]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax.
      apply AxRule_I. apply RA3_I. exists (A → Or B C). exists (Bot V). auto.
      inversion H3. subst. assumption. inversion H4.
    + assert (x=nil). inversion H. subst. assert (b = (Excl A B → C)). pose (H0 b).
      assert (List.In b (b :: x)). apply in_eq. apply s in H2. inversion H2. reflexivity.
      subst. destruct x. reflexivity. exfalso. apply H4. pose (H0 b).
      assert (List.In b (Excl A B → C :: b :: x)). apply in_cons. apply in_eq.
      apply s in H2. inversion H2. subst. apply in_eq. subst. simpl in H1. assert (b= Excl A B → C).
      pose (H0 b). assert (List.In b [b]). apply in_eq. apply s in H2. inversion H2. auto.
      subst. apply absorp_Or1 in H1. apply w in H1.
      apply MP with (ps:=[(Empty_set _, (A → Or B C) → (Or (A → Or B C) (Bot V)));(Empty_set _, (A → Or B C))]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I.
      exists (A → Or B C). exists (Bot V). auto. inversion H3. subst. assumption.
      inversion H4.
- intro. exists [(Excl A B → C)]. repeat split.
  * apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  * intros. inversion H0. subst. simpl. inversion H0. subst. apply In_singleton. inversion H1. inversion H1.
  * destruct H. destruct H. pose (wdual_residuation A B C). destruct p. clear w. simpl.
    simpl in H0. simpl in w0. destruct H0. destruct x.
    + simpl in H1. apply MP with (ps:=[(Empty_set _, Bot V → Or (Excl A B → C) (Bot V));(Empty_set _, Bot V)]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax.
      apply AxRule_I. apply RA3_I. exists (Excl A B → C). exists (Bot V). auto.
      inversion H3. subst. assumption. inversion H4.
    + assert (x=nil). inversion H. subst. assert (b = (A → Or B C)). pose (H0 b).
      assert (List.In b (b :: x)). apply in_eq. apply s in H2. inversion H2. reflexivity.
      subst. destruct x. reflexivity. exfalso. apply H4. pose (H0 b).
      assert (List.In b (A → Or B C :: b :: x)). apply in_cons. apply in_eq.
      apply s in H2. inversion H2. subst. apply in_eq. subst. simpl in H1. assert (b= A → Or B C).
      pose (H0 b). assert (List.In b [b]). apply in_eq. apply s in H2. inversion H2. auto.
      subst. apply absorp_Or1 in H1. apply w0 in H1.
      apply MP with (ps:=[(Empty_set _, (Excl A B → C) → (Or (Excl A B → C) (Bot V)));(Empty_set _, (Excl A B → C))]).
      2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA2_I.
      exists (Excl A B → C). exists (Bot V). auto. inversion H3. subst. assumption.
      inversion H4.
Qed.

Lemma wTop : forall Γ, wBIH_rules (Γ, Top V).
Proof.
intros. apply MP with (ps:=[(Γ, Imp (Imp (Top V) (Top V)) (Top V));(Γ, (Imp (Top V) (Top V)))]).
2: apply MPRule_I. intros. inversion H. subst. apply Ax. apply AxRule_I.
apply RA15_I. exists (Top V → Top V). auto. inversion H0. subst. apply wimp_Id_gen.
inversion H1.
Qed.

Lemma wBiLEM : forall A Γ, wBIH_rules (Γ, Or A (wNeg A)).
Proof.
intros. pose (wBIH_monot (Empty_set _, Or A (wNeg A))). apply w.
apply MP with (ps:=[(Empty_set _, (Or A (Excl (Top V) A)) → (Or A (wNeg A)));(Empty_set _, (Or A (Excl (Top V) A)))]).
2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Empty_set _, ((Excl (Top V) A) → (Or A (wNeg A))) → ((Or A (Excl (Top V) A)) → (Or A (wNeg A))));(Empty_set _, ((Excl (Top V) A) → (Or A (wNeg A))))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Empty_set _, (A → (Or A (wNeg A))) → ((Excl (Top V) A) → (Or A (wNeg A))) → ((Or A (Excl (Top V) A)) → (Or A (wNeg A))));(Empty_set _, (A → (Or A (wNeg A))))]).
2: apply MPRule_I. intros. inversion H1. subst. apply Ax. apply AxRule_I. apply RA4_I.
exists A. exists (Excl (Top V) A). exists (Or A (wNeg A)). auto. inversion H2.
subst. apply Ax. apply AxRule_I. apply RA2_I. exists A. exists (wNeg A). auto.
inversion H3. inversion H1. subst.
apply MP with (ps:=[(Empty_set _, ((wNeg A) → Or A (wNeg A)) → (Excl (Top V) A → Or A (wNeg A)));(Empty_set _, ((wNeg A) → Or A (wNeg A)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Empty_set _, (Excl (Top V) A → (wNeg A)) → ((wNeg A) → Or A (wNeg A)) → (Excl (Top V) A → Or A (wNeg A)));(Empty_set _, (Excl (Top V) A → (wNeg A)))]).
2: apply MPRule_I. intros. inversion H3. subst. apply Ax. apply AxRule_I.
apply RA1_I. exists (Excl (Top V) A). exists (wNeg A). exists (Or A (wNeg A)).
auto. inversion H4. 2: inversion H5. subst. apply wimp_Id_gen.
 inversion H3. subst. apply Ax. apply AxRule_I. apply RA3_I. exists A.
exists (wNeg A). auto. inversion H4. inversion H2. inversion H0. subst. 2: inversion H1.
apply MP with (ps:=[(Empty_set _, Imp (Top V) (Or A (Excl (Top V) A)));(Empty_set _, Top V)]). 2: apply MPRule_I.
intros. inversion H1. subst. apply wdual_residuation. apply wimp_Id_gen. inversion H2.
2: inversion H3. subst. apply wTop. intro. intros. inversion H.
Qed.

Theorem wBIH_Detachment_Theorem : forall s,
           (wBIH_rules s) ->
           (forall A B Γ, (fst s = Γ) ->
                          (snd s = A → B) ->
                          wBIH_rules  (Union _ Γ (Singleton _ (A)), B)).
Proof.
intros s D. induction D.
(* Id *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst.
  simpl. apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A B);(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Id.
  apply IdRule_I. apply Union_introl. assumption. inversion H2. subst.
  apply Id. apply IdRule_I. apply Union_intror. apply In_singleton. inversion H3.
(* Ax *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id2. subst. simpl.
  apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A B);(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H1. subst. apply Ax.
  apply AxRule_I. assumption. inversion H2. subst. apply Id. apply IdRule_I.
  apply Union_intror. apply In_singleton. inversion H3.
(* MP *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. simpl.
  assert (J01: List.In (Γ0, A0 → A → B) [(Γ0, A0 → A → B); (Γ0, A0)]). apply in_eq.
  assert (J1: Γ0 = Γ0). reflexivity.
  assert (J2: A0 → A → B = A0 → A → B). reflexivity.
  pose (H0 (Γ0, A0 → A → B) J01 A0 (Imp A B) Γ0 J1 J2).
  assert (wBIH_rules (Γ0, A → B)).
  assert (J3: (forall A1 : BPropF V, fst (Union _ Γ0 (Singleton _ A0), A → B) A1 ->
  wBIH_rules (Γ0, A1))).
  intro. simpl. intro. inversion H2. subst. apply Id.
  apply IdRule_I. assumption. subst. inversion H3. subst.
  assert (J02: List.In (Γ0, A1) [(Γ0, A1 → A → B); (Γ0, A1)]). apply in_cons. apply in_eq.
  pose (H (Γ0, A1) J02). assumption.
  pose (wBIH_comp (Union _ Γ0 (Singleton _ A0), A → B) w Γ0 J3). simpl in w0. assumption.
  apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), (Imp A B));(Union _ Γ0 (Singleton _ A), A)]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(Union _ Γ0 (Singleton _ A), Imp A0 (Imp A B));(Union _ Γ0 (Singleton _ A), A0)]).
  2: apply MPRule_I. intros. inversion H4. subst.
  assert (J4: Included _ (fst (Γ0, A0 → A → B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption. pose (H (Γ0, A0 → A → B) J01).
  pose (wBIH_monot (Γ0, A0 → A → B) w0 (Union _ Γ0 (Singleton _ A)) J4). assumption.
  inversion H5. subst.
  assert (J4: Included _ (fst (Γ0, A0 → A → B)) (Union _ Γ0 (Singleton _ A))).
  simpl. intro. intro. apply Union_introl. assumption.
  pose (wBIH_monot (Γ0, A0)). apply w0. apply H. apply in_cons. apply in_eq.
  auto. inversion H6. inversion H4. subst. apply Id. apply IdRule_I. apply Union_intror.
  apply In_singleton. inversion H5.
(* DNw *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id2. subst. inversion id2. subst. simpl.
  assert (J01: List.In (Empty_set (BPropF V), A0) [(Empty_set (BPropF V), A0)]). apply in_eq.
  apply H in J01. remember (Union (BPropF V) Γ0 (Singleton (BPropF V)  (wNeg A0))) as Γ.
  apply MP with (ps:=[(Γ, (And (wNeg A0) (Neg (wNeg A0))) → Bot _); (Γ, And (wNeg A0) (Neg (wNeg A0)))]).
  2: apply MPRule_I. intros. inversion H2. rewrite <- H3. apply wContr_Bot. inversion H3.
  rewrite <- H4.
  apply MP with (ps:=[(Γ,(Top V →  (And (wNeg A0) (Neg (wNeg A0)))));(Γ, Top V)]).
  2: apply MPRule_I. intros. inversion H5. rewrite <- H6.
  apply MP with (ps:=[(Γ,(Top V → (Neg (wNeg A0))) →(Top V →  (And (wNeg A0) (Neg (wNeg A0)))));(Γ, Top V → (Neg (wNeg A0)))]).
  2: apply MPRule_I. intros. inversion H7. rewrite <- H8.
  apply MP with (ps:=[(Γ,(Top V → (wNeg A0)) → (Top V → (Neg (wNeg A0))) → (Top V → (And (wNeg A0) (Neg (wNeg A0)))));(Γ, Top V → (wNeg A0))]).
  2: apply MPRule_I. intros. inversion H9. rewrite <- H10. apply Ax. apply AxRule_I.
  apply RA7_I. exists (Top V). exists (wNeg A0). exists (Neg (wNeg A0)). auto. inversion H10. 2: inversion H11.
  rewrite <- H11.
  apply MP with (ps:=[(Γ, wNeg A0 → Top V → wNeg A0);(Γ, wNeg A0)]). intros. 2: apply MPRule_I.
  inversion H12. rewrite <- H13. apply wThm_irrel. inversion H13. 2: inversion H14. rewrite <- H14.
  apply Id. apply IdRule_I. subst. apply Union_intror. apply In_singleton.
  inversion H8. rewrite <- H9.
  apply MP with (ps:=[(Γ, Neg (wNeg A0) → Top V → Neg (wNeg A0));(Γ, Neg (wNeg A0))]). intros. 2: apply MPRule_I.
  inversion H10. rewrite <- H11. apply wThm_irrel. inversion H11. 2: inversion H12. rewrite <- H12.
  apply DNw with (ps:=[(Empty_set (BPropF V), A0)]) ; auto. apply DNwRule_I. inversion H9.
  inversion H6. subst. apply wTop. inversion H7. inversion H4.
Qed.

Theorem wBIH_Deduction_Theorem : forall s,
           (wBIH_rules s) ->
           (forall A B Γ, (fst s = Union _ Γ (Singleton _ (A))) ->
                          (snd s = B) ->
                          wBIH_rules (Γ, A → B)).
Proof.
intros s D. induction D.
(* Id *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl. inversion H0.
  + subst. apply MP with (ps:=[(Γ, A0 → A → A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H2. subst.
    apply wThm_irrel. inversion H3. subst. apply Id. apply IdRule_I. assumption.
    inversion H4.
  + subst. inversion H1. subst. apply wimp_Id_gen.
(* Ax *)
- intros A B Γ id1 id2. inversion H. subst. simpl in id1. subst. simpl.
  apply MP with (ps:=[(Γ, A0 → A → A0);(Γ, A0)]). 2: apply MPRule_I. intros. inversion H1. subst.
  apply wThm_irrel. inversion H2. subst.
  apply Ax. apply AxRule_I. assumption. inversion H3.
(* MP *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
  assert (J2: A0 → B0 = A0 → B0). reflexivity.
  assert (J20: List.In (Union (BPropF V) Γ (Singleton (BPropF V) A), A0 → B0) [(Union (BPropF V) Γ (Singleton (BPropF V) A), A0 → B0); (Union (BPropF V) Γ (Singleton (BPropF V) A), A0)]).
  apply in_eq.
  pose (H0 (Union (BPropF V) Γ (Singleton (BPropF V) A),  A0 → B0) J20
  A (Imp A0 B0) Γ J1 J2).
  assert (J3: A0 = A0). reflexivity.
  apply MP with (ps:=[(Γ, (And A A0 → B0) → (A → B0));(Γ, And A A0 → B0)]).
  2: apply MPRule_I. intros. inversion H2. subst.
  apply MP with (ps:=[(Γ, (A → And A A0) → (And A A0 → B0) → (A → B0));(Γ, A → And A A0)]).
  2: apply MPRule_I. intros. inversion H3. subst. apply Ax.
  apply AxRule_I. apply RA1_I. exists A. exists (And A A0). exists B0. auto.
  inversion H4. subst. 2: inversion H5.
  apply MP with (ps:=[(Γ, (A → A0) → (A → And A A0));(Γ, A → A0)]).
  2: apply MPRule_I. intros. inversion H5. subst.
  apply MP with (ps:=[(Γ, (A → A) → (A → A0) → (A → And A A0));(Γ, A → A)]).
  2: apply MPRule_I. intros. inversion H6. subst. apply Ax.
  apply AxRule_I. apply RA7_I. exists A. exists A. exists A0. auto. inversion H7.
  subst. apply wimp_Id_gen. inversion H8. inversion H6. subst. 2: inversion H7.
  assert (J30: List.In (Union (BPropF V) Γ (Singleton (BPropF V) A), A0) [(Union (BPropF V) Γ (Singleton (BPropF V) A), A0 → B0); (Union (BPropF V) Γ (Singleton (BPropF V) A), A0)]).
  apply in_cons. apply in_eq. assert (J40: A0 = A0). reflexivity.
  pose (H0 (Union (BPropF V) Γ (Singleton (BPropF V) A), A0) J30
  A A0 Γ J1 J40). auto. inversion H3. subst.
  apply MP with (ps:=[(Γ, (A → A0 → B0) → (And A A0 → B0));(Γ, (A → A0 → B0))]).
  2: apply MPRule_I. intros. inversion H4. subst. apply Ax.
  apply AxRule_I. apply RA8_I. exists A. exists A0. exists B0. auto.
  inversion H5. subst. assumption. inversion H6. inversion H4.
(* DNw *)
- intros A B Γ id1 id2. inversion H1. subst. simpl in id1. subst. simpl.
  assert (J1: wBIH_rules (Empty_set _, Neg (wNeg A0))).
  apply DNw with (ps:=[(Empty_set _, A0)]). 2: apply DNwRule_I. assumption.
  assert (J2: Included _ (fst (Empty_set _, Neg (wNeg A0))) Γ). intro. intro. inversion H2.
  pose (wBIH_monot (Empty_set _, Neg (wNeg A0)) J1 Γ J2). simpl in w.
  apply MP with (ps:=[(Γ, Neg (wNeg A0) → A → Neg (wNeg A0)); (Γ, Neg (wNeg A0))]).
  2: apply MPRule_I. intros. inversion H2. subst. apply wThm_irrel.
  inversion H3. subst. 2: inversion H4. assumption.
Qed.

Theorem gen_wBIH_Detachment_Theorem : forall A B Γ,
  wpair_derrec (Γ, Singleton _ (A → B)) ->
      wpair_derrec (Union _ Γ (Singleton _ (A)), Singleton _ (B)).
Proof.
intros A B Γ wpair. unfold wpair_derrec. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H.
subst. simpl. apply In_singleton. inversion H0. simpl.
apply MP with (ps:=[ (Union _ Γ (Singleton _ A), Imp B (Or B (Bot V))); (Union _ Γ (Singleton _ A), B)]).
2: apply MPRule_I. intros. inversion H. subst. apply Ax. apply AxRule_I. apply RA2_I.
exists B. exists (Bot V). auto. inversion H0. subst. 2: inversion H1.
destruct wpair. destruct H1. destruct H2. simpl in H3. destruct x.
apply MP with (ps:=[(Union _ Γ (Singleton _ A), Imp (Bot V) B);(Union _ Γ (Singleton _ A), (Bot V))]).
2: apply MPRule_I. intros. inversion H4. subst. apply wEFQ. inversion H5. subst. 2: inversion H6.
assert (J1: Included _ (fst (Γ, Bot V)) (Union _ Γ (Singleton _ A))). intro. intro. apply Union_introl.
assumption.
pose (wBIH_monot (Γ , Bot V) H3 (Union _ Γ (Singleton _ A)) J1). assumption.
destruct x. simpl in H3. assert (b=A → B). pose (H2 b). assert (List.In b [b]). apply in_eq.
apply s in H4. inversion H4. reflexivity. subst. apply absorp_Or1 in H3.
assert (J1: Γ = Γ). reflexivity.
assert (J2: A → B = A → B). reflexivity.
pose (wBIH_Detachment_Theorem (Γ, A → B) H3 A B Γ J1 J2). assumption.
exfalso. simpl in H1. inversion H1. apply H6. subst. pose (H2 b).
assert (List.In b (b :: b0 :: x)). apply in_eq. pose (s H4). inversion s0. subst.
pose (H2 b0). assert (List.In b0 (A → B :: b0 :: x)). apply in_cons. apply in_eq.
pose (s1 H5). inversion s2. subst. apply in_eq.
Qed.

Theorem gen_wBIH_Deduction_Theorem : forall A B Γ,
  wpair_derrec (Union _ Γ (Singleton _ (A)), Singleton _ (B)) ->
      wpair_derrec (Γ, Singleton _ (A → B)).
Proof.
intros A B Γ wpair. unfold wpair_derrec. simpl. exists [(A → B)]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H.
subst. simpl. apply In_singleton. inversion H0. simpl.
apply MP with (ps:=[(Γ, Imp (A → B) (Or (A → B) (Bot V))); (Γ, (A → B))]).
2: apply MPRule_I. intros. inversion H. subst. apply Ax. apply AxRule_I. apply RA2_I.
exists (A → B). exists (Bot V). auto. inversion H0. subst. 2: inversion H1.
destruct wpair. destruct H1. destruct H2. simpl in H3. simpl in H2. destruct x. simpl in H3.
assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
assert (J2: Bot V = Bot V). reflexivity.
pose (wBIH_Deduction_Theorem (Union _ Γ (Singleton _ A), Bot V) H3 A (Bot V) Γ J1 J2).
apply MP with (ps:=[(Γ, (Bot V → B) → (A → B));(Γ, Bot V → B)]).
2: apply MPRule_I. intros. inversion H4. subst.
apply MP with (ps:=[(Γ, (A → Bot V) → (Bot V → B) → (A → B));(Γ, A → Bot V)]).
2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA1_I. exists A.
exists (Bot V). exists B. auto. inversion H6. subst. 2: inversion H7. assumption.
inversion H5. subst. 2: inversion H6. apply wEFQ.
destruct x. simpl in H3. assert (b=B). pose (H2 b). assert (List.In b [b]). apply in_eq.
apply s in H4. inversion H4. reflexivity. subst. apply absorp_Or1 in H3.
assert (J1: Union _ Γ (Singleton _ A) = Union _ Γ (Singleton _ A)). reflexivity.
assert (J2: B = B). reflexivity.
pose (wBIH_Deduction_Theorem (Union _ Γ (Singleton _ A), B) H3 A B Γ J1 J2). assumption.
exfalso. simpl in H2. inversion H1. apply H6. subst. pose (H2 b).
assert (List.In b (b :: b0 :: x)). apply in_eq. pose (s H4). inversion s0. subst.
pose (H2 b0). assert (List.In b0 (b :: b0 :: x)). apply in_cons. apply in_eq.
pose (s1 H5). inversion s2. subst. apply in_eq.
Qed.

Theorem wBIH_Dual_Detachment_Theorem : forall A B Δ,
           (wBIH_rules (Singleton _ (Excl A B), list_disj Δ)) ->
           (wBIH_rules (Singleton _ (A), Or B (list_disj Δ))).
Proof.
intros A B Δ D.
assert (J1: Singleton _ (Excl A B) = Union _ (Empty_set _) (Singleton _ (Excl A B))).
apply Extensionality_Ensembles. split. intro. intro. inversion H. subst. apply Union_intror.
apply In_singleton. intro. intro. inversion H. inversion H0. inversion H0. subst. apply In_singleton.
assert (J2: list_disj Δ = list_disj Δ). reflexivity.
pose (wBIH_Deduction_Theorem (Singleton _ (Excl A B), list_disj Δ) D (Excl A B) (list_disj Δ)
(Empty_set _) J1 J2).
apply wdual_residuation in w.
assert (J3: @Empty_set (BPropF V) = @Empty_set _). reflexivity.
assert (J4: A → Or B (list_disj Δ) = A → Or B (list_disj Δ)). reflexivity.
pose (wBIH_Detachment_Theorem (Empty_set _, A → Or B (list_disj Δ)) w A (Or B (list_disj Δ))
(Empty_set _) J3 J4). assert (Union _ (Empty_set _) (Singleton _ A) = Singleton _ A).
apply Extensionality_Ensembles. split. intro. intro. inversion H. inversion H0.
assumption. intro. intro. apply Union_intror. assumption. rewrite H in w0. assumption.
Qed.

Theorem wBIH_Dual_Deduction_Theorem : forall A B Δ,
           (wBIH_rules (Singleton _ (A), Or B (list_disj Δ))) ->
           (wBIH_rules (Singleton _ (Excl A B), list_disj Δ)).
Proof.
intros A B Δ D.
assert (J1: Singleton _ A = Union _ (Empty_set _) (Singleton _ A)). apply Extensionality_Ensembles.
split. intro. intro. apply Union_intror. assumption. intro. intro. inversion H. inversion H0. assumption.
assert (J2: Or B (list_disj Δ) = Or B (list_disj Δ)). reflexivity.
pose (wBIH_Deduction_Theorem (Singleton _ A, Or B (list_disj Δ)) D A (Or B (list_disj Δ))
(Empty_set _) J1 J2). apply wdual_residuation in w.
assert (J3: @Empty_set (BPropF V) = Empty_set _). reflexivity.
assert (J4: Excl A B → list_disj Δ = Excl A B → list_disj Δ). reflexivity.
pose (wBIH_Detachment_Theorem (Empty_set _, Excl A B → list_disj Δ) w (Excl A B)
(list_disj Δ) (Empty_set _) J3 J4).
assert (Union _ (Empty_set _) (Singleton _ (Excl A B)) = Singleton _ (Excl A B)).
apply Extensionality_Ensembles. split. intro. intro. inversion H. inversion H0.
assumption. intro. intro. apply Union_intror. assumption.
rewrite H in w0. assumption.
Qed.

Lemma In_remove : forall (A : BPropF V) B (l : list (BPropF V)), List.In A (remove eq_dec_form B l) -> List.In A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in H. destruct (eq_dec_form B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : BPropF V) B (l : list (BPropF V)), InT A (remove eq_dec_form B l) -> InT A l.
Proof.
intros A B. induction l.
- simpl. auto.
- intro. simpl in H. destruct (eq_dec_form B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (BPropF V)), NoDup l -> NoDup (remove eq_dec_form A l).
Proof.
intro A. induction l.
- intro. simpl. apply NoDup_nil.
- intro H. simpl. destruct (eq_dec_form A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.

Lemma remove_disj : forall l B Γ, wBIH_rules (Γ, list_disj l → Or B (list_disj (remove eq_dec_form B l))).
Proof.
induction l.
- intros. simpl. apply Ax. apply AxRule_I. apply RA3_I.
  exists B. exists (Bot V). auto.
- intros. pose (IHl B Γ). simpl. destruct (eq_dec_form B a).
  * subst. simpl.
    apply MP with (ps:=[(Γ, ((list_disj l) → Or a (list_disj (remove eq_dec_form a l))) → (Or a (list_disj l) → Or a (list_disj (remove eq_dec_form a l))));
    (Γ, (list_disj l) → Or a (list_disj (remove eq_dec_form a l)))]).
    2: apply MPRule_I. intros. inversion H. subst.
    apply MP with (ps:=[(Γ, (a → Or a (list_disj (remove eq_dec_form a l))) → ((list_disj l) → Or a (list_disj (remove eq_dec_form a l))) → (Or a (list_disj l) → Or a (list_disj (remove eq_dec_form a l))));
    (Γ, a → Or a (list_disj (remove eq_dec_form a l)))]).
    2: apply MPRule_I. intros. inversion H0. subst. apply Ax. apply AxRule_I.
    apply RA4_I. exists a. exists (list_disj l). exists (Or a (list_disj (remove eq_dec_form a l))).
    auto. inversion H1. subst. apply Ax. apply AxRule_I.
    apply RA2_I. exists a. exists (list_disj (remove eq_dec_form a l)).
    auto. inversion H2. inversion H0. subst. assumption. inversion H1.
  * simpl.
    apply MP with (ps:=[(Γ, (Or a (Or B (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l)))) → (Or a (list_disj l) → Or B (Or a (list_disj (remove eq_dec_form B l)))));
    (Γ, (Or a (Or B (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H. subst.
    apply MP with (ps:=[(Γ, (Or a (list_disj l) → Or a (Or B (list_disj (remove eq_dec_form B l)))) → (Or a (Or B (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l)))) → (Or a (list_disj l) → Or B (Or a (list_disj (remove eq_dec_form B l)))));
    (Γ, (Or a (list_disj l) → Or a (Or B (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H0. subst. apply Ax.
    apply AxRule_I. apply RA1_I. exists (Or a (list_disj l)). exists (Or a (Or B (list_disj (remove eq_dec_form B l)))).
    exists (Or B (Or a (list_disj (remove eq_dec_form B l)))). auto. inversion H1. subst.
    apply MP with (ps:=[(Γ, (list_disj l → Or a (Or B (list_disj (remove eq_dec_form B l)))) → (Or a (list_disj l) → Or a (Or B (list_disj (remove eq_dec_form B l)))));
    (Γ, list_disj l → Or a (Or B (list_disj (remove eq_dec_form B l))))]). 2: apply MPRule_I.
    intros. inversion H2. subst.
    apply MP with (ps:=[(Γ, (a → Or a (Or B (list_disj (remove eq_dec_form B l)))) → (list_disj l → Or a (Or B (list_disj (remove eq_dec_form B l)))) → (Or a (list_disj l) → Or a (Or B (list_disj (remove eq_dec_form B l)))));
    (Γ, a → Or a (Or B (list_disj (remove eq_dec_form B l))))]). 2: apply MPRule_I.
    intros. inversion H3. subst. apply Ax. apply AxRule_I. apply RA4_I.
    exists a. exists (list_disj l). exists (Or a (Or B (list_disj (remove eq_dec_form B l)))).
    auto. inversion H4. subst. apply Ax. apply AxRule_I. apply RA2_I.
    exists a. exists (Or B (list_disj (remove eq_dec_form B l))). auto. inversion H5.
    inversion H3. subst.
    apply MP with (ps:=[(Γ, ((Or B (list_disj (remove eq_dec_form B l))) → Or a (Or B (list_disj (remove eq_dec_form B l)))) → (list_disj l → Or a (Or B (list_disj (remove eq_dec_form B l)))));
    (Γ, (Or B (list_disj (remove eq_dec_form B l))) → Or a (Or B (list_disj (remove eq_dec_form B l))))]).
    2: apply MPRule_I. intros. inversion H4. subst.
    apply MP with (ps:=[(Γ, (list_disj l → (Or B (list_disj (remove eq_dec_form B l)))) → ((Or B (list_disj (remove eq_dec_form B l))) → Or a (Or B (list_disj (remove eq_dec_form B l)))) → (list_disj l → Or a (Or B (list_disj (remove eq_dec_form B l)))));
    (Γ, (list_disj l → (Or B (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (list_disj l).
    exists (Or B (list_disj (remove eq_dec_form B l))). exists (Or a (Or B (list_disj (remove eq_dec_form B l)))).
    auto. inversion H6. subst. assumption. inversion H7. inversion H5. subst.
    apply Ax. apply AxRule_I. apply RA3_I. exists a. exists (Or B (list_disj (remove eq_dec_form B l))).
    auto. inversion H6. inversion H4. inversion H2. inversion H0. subst.
    apply MP with (ps:=[(Γ, ((Or B (list_disj (remove eq_dec_form B l)) → Or B (Or a (list_disj (remove eq_dec_form B l)))) → (Or a (Or B (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l))))));
    (Γ, ((Or B (list_disj (remove eq_dec_form B l)) → Or B (Or a (list_disj (remove eq_dec_form B l))))))]).
    2: apply MPRule_I. intros. inversion H1. subst.
    apply MP with (ps:=[(Γ, (a → Or B (Or a (list_disj (remove eq_dec_form B l)))) → ((Or B (list_disj (remove eq_dec_form B l)) → Or B (Or a (list_disj (remove eq_dec_form B l)))) → (Or a (Or B (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l))))));
    (Γ, (a → Or B (Or a (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I.
    apply RA4_I. exists a. exists (Or B (list_disj (remove eq_dec_form B l))).
    exists (Or B (Or a (list_disj (remove eq_dec_form B l)))). auto. inversion H3. subst.
    apply MP with (ps:=[(Γ, ((Or a (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l)))) → (a → Or B (Or a (list_disj (remove eq_dec_form B l)))));
    (Γ, (Or a (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l))))]).
    2: apply MPRule_I. intros. inversion H4. subst.
    apply MP with (ps:=[(Γ, (a → (Or a (list_disj (remove eq_dec_form B l)))) → ((Or a (list_disj (remove eq_dec_form B l))) → Or B (Or a (list_disj (remove eq_dec_form B l)))) → (a → Or B (Or a (list_disj (remove eq_dec_form B l)))));
    (Γ, (a → (Or a (list_disj (remove eq_dec_form B l)))))]).
    2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
    apply RA1_I. exists a. exists (Or a (list_disj (remove eq_dec_form B l))).
    exists (Or B (Or a (list_disj (remove eq_dec_form B l)))). auto. inversion H6. subst.
    apply Ax. apply AxRule_I.
    apply RA2_I. exists a. exists (list_disj (remove eq_dec_form B l)).
    auto. inversion H7. inversion H5. subst. apply Ax. apply AxRule_I.
    apply RA3_I. exists B. exists (Or a (list_disj (remove eq_dec_form B l))).
    auto. inversion H6. inversion H4. inversion H2. subst. apply wmonotL_Or.
    apply Ax. apply AxRule_I.
    apply RA3_I. exists a. exists (list_disj (remove eq_dec_form B l)).
    auto. inversion H3. inversion H1.
Qed.

Theorem gen_wBIH_Dual_Detachment_Theorem : forall A B Δ,
  wpair_derrec (Singleton _ (Excl A B), Δ) ->
      wpair_derrec (Singleton _ (A), Union _ (Singleton _ (B)) Δ).
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. simpl in H0. simpl in H1.
exists (B :: (remove eq_dec_form B x)). repeat split.
apply NoDup_cons. apply remove_In. apply NoDup_remove. assumption.
intros. inversion H2. subst. apply Union_introl. apply In_singleton. subst.
apply Union_intror. apply H0. apply In_remove with (B:=B). assumption.
simpl.
pose (wBIH_Dual_Detachment_Theorem A B x H1).
apply MP with (ps:=[(Singleton _ A, Imp (Or B (list_disj x)) (Or B (list_disj (remove eq_dec_form B x))));
(Singleton _ A, (Or B (list_disj x)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Singleton _ A, Imp (Imp (list_disj x) (Or B (list_disj (remove eq_dec_form B x)))) ((Imp (Or B (list_disj x)) (Or B (list_disj (remove eq_dec_form B x))))));
(Singleton _ A, Imp (list_disj x) (Or B (list_disj (remove eq_dec_form B x))))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply MP with (ps:=[(Singleton _ A, Imp (Imp (B) (Or B (list_disj (remove eq_dec_form B x)))) (Imp (Imp (list_disj x) (Or B (list_disj (remove eq_dec_form B x)))) ((Imp (Or B (list_disj x)) (Or B (list_disj (remove eq_dec_form B x)))))));
(Singleton _ A, Imp B (Or B (list_disj (remove eq_dec_form B x))))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA4_I.
exists B. exists (list_disj x). exists (Or B (list_disj (remove eq_dec_form B x))).
auto. inversion H5. subst. apply Ax. apply AxRule_I. apply RA2_I.
exists B. exists (list_disj (remove eq_dec_form B x)). auto. inversion H6.
inversion H4. subst. apply remove_disj. inversion H5. inversion H3. subst. assumption.
inversion H4.
Qed.

Theorem gen_wBIH_Dual_Deduction_Theorem : forall A B Δ,
  wpair_derrec (Singleton _ (A), Union _ (Singleton _ (B)) Δ) ->
      wpair_derrec (Singleton _ (Excl A B), Δ).
Proof.
intros A B Δ wpair. destruct wpair. destruct H. destruct H0. simpl in H0. simpl in H1.
exists (remove eq_dec_form B x). repeat split.
apply NoDup_remove. assumption.
intros. simpl. pose (H0 A0). pose (In_remove _ _ _ H2). apply u in i.
inversion i. exfalso. subst. inversion H3. subst.
pose (remove_In eq_dec_form x A0). apply n. assumption. assumption.
simpl.
pose (wBIH_Dual_Deduction_Theorem A B (remove eq_dec_form B x)). apply w.
apply MP with (ps:=[(Singleton _ A, Imp (list_disj x) (Or B (list_disj (remove eq_dec_form B x))));
(Singleton _ A, list_disj x)]). 2: apply MPRule_I. intros. inversion H2. subst. apply remove_disj.
inversion H3. subst. assumption. inversion H4.
Qed.



(* To help for the results about sBIH. *)

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

Lemma wT_for_DN : forall A n m Γ, (le m n) -> (wBIH_rules (Γ, (DN_form n A) → (DN_form m A))).
Proof.
intro A. induction n.
- intros. assert (m = 0). lia. rewrite H0. simpl. apply wimp_Id_gen.
- intros. destruct (eq_dec_nat m (S n)).
  * subst. apply wimp_Id_gen.
  * assert (m <= n). lia. pose (IHn m Γ H0).
    apply MP with (ps:=[(Γ, (DN_form n A → DN_form m A) → (DN_form (S n) A → DN_form m A));(Γ, (DN_form n A → DN_form m A))]).
    2: apply MPRule_I. intros. inversion H1. subst.
    apply MP with (ps:=[(Γ, (DN_form (S n) A → DN_form n A) → (DN_form n A → DN_form m A) → (DN_form (S n) A → DN_form m A));(Γ, (DN_form (S n) A → DN_form n A))]).
    2: apply MPRule_I. intros. inversion H2. subst. apply Ax. apply AxRule_I. apply RA1_I. exists (DN_form (S n) A).
    exists (DN_form n A). exists (DN_form m A). auto. inversion H3. subst. apply wDN_to_form.
    inversion H4. inversion H2. subst. assumption. inversion H3.
Qed.

Lemma wExcl_mon : forall A B C,
  (wBIH_rules (Empty_set _, A → B)) ->
  (wBIH_rules (Empty_set _, (Excl A C) → (Excl B C))).
Proof.
intros. apply wdual_residuation.
apply MP with (ps:=[(Empty_set _, (B → Or C (Excl B C)) → (A → Or C (Excl B C)));
(Empty_set _, (B → Or C (Excl B C)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Empty_set _, (A → B) → (B → Or C (Excl B C)) → (A → Or C (Excl B C)));
(Empty_set _, (A → B))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (Or C (Excl B C)). auto. inversion H2. subst. assumption. inversion H3.
inversion H1. subst.
apply Ax. apply AxRule_I. apply RA11_I. exists B. exists C. auto. inversion H2.
Qed.

Lemma wmon_Excl : forall A B C,
  (wBIH_rules (Empty_set _, A → B)) ->
  (wBIH_rules (Empty_set _, (Excl C B) → (Excl C A))).
Proof.
intros. apply wdual_residuation.
apply MP with (ps:=[(Empty_set _, (Or A (Excl C A) → Or B (Excl C A)) → (C → Or B (Excl C A)));
(Empty_set _, (Or A (Excl C A) → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Empty_set _, (C → Or A (Excl C A)) → (Or A (Excl C A) → Or B (Excl C A)) → (C → Or B (Excl C A)));
(Empty_set _, C → Or A (Excl C A))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists C. exists (Or A (Excl C A)).
exists (Or B (Excl C A)). auto. inversion H2. subst.
apply Ax. apply AxRule_I. apply RA11_I. exists C. exists A.
auto. inversion H3. inversion H1. subst. 2: inversion H2.
apply MP with (ps:=[(Empty_set _, ((Excl C A) → Or B (Excl C A)) → (Or A (Excl C A) → Or B (Excl C A)));
(Empty_set _, ((Excl C A) → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Empty_set _, (A → Or B (Excl C A)) → ((Excl C A) → Or B (Excl C A)) → (Or A (Excl C A) → Or B (Excl C A)));
(Empty_set _, (A → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists A. exists (Excl C A).
exists (Or B (Excl C A)). auto. inversion H4. subst.
apply MP with (ps:=[(Empty_set _, (B → Or B (Excl C A)) → (A → Or B (Excl C A)));
(Empty_set _, (B → Or B (Excl C A)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Empty_set _, (A → B) → (B → Or B (Excl C A)) → (A → Or B (Excl C A)));
(Empty_set _, (A → B))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists B.
exists (Or B (Excl C A)). auto. inversion H7. subst. assumption.
inversion H8. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists B. exists (Excl C A). auto.
inversion H7. inversion H5. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists B. exists (Excl C A). auto.
inversion H4.
Qed.

Lemma wOr_Neg : forall A B C Γ,
  (wBIH_rules (Γ, A → (Or B C))) ->
  (wBIH_rules (Γ, (And (Neg B) A) → C)).
Proof.
intros.
apply MP with (ps:=[(Γ, ((And (Neg B) (Or B C)) → C) → (And (Neg B) A → C));(Γ, And (Neg B) (Or B C) → C)]).
2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, ((And (Neg B) A) → (And (Neg B) (Or B C))) → ((And (Neg B) (Or B C)) → C) → (And (Neg B) A → C));
(Γ, ((And (Neg B) A) → (And (Neg B) (Or B C))))]).
2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (And (Neg B) A). exists (And (Neg B) (Or B C)).
exists C. auto. inversion H2. subst.
apply MP with (ps:=[(Γ, (And (Neg B) A → (Or B C)) → (And (Neg B) A → And (Neg B) (Or B C)));
(Γ, (And (Neg B) A → (Or B C)))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply MP with (ps:=[(Γ, (And (Neg B) A → (Neg B)) → (And (Neg B) A → (Or B C)) → (And (Neg B) A → And (Neg B) (Or B C)));
(Γ, (And (Neg B) A → (Neg B)))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists (And (Neg B) A). exists (Neg B).
exists (Or B C). auto. inversion H5. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists (Neg B). exists A. auto.
inversion H6. inversion H4. subst.
apply MP with (ps:=[(Γ, (A → Or B C) → (And (Neg B) A → Or B C));
(Γ, (A → Or B C))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, (And (Neg B) A → A) → (A → Or B C) → (And (Neg B) A → Or B C));
(Γ, (And (Neg B) A → A))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (And (Neg B) A). exists A.
exists (Or B C). auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists (Neg B). exists A. auto.
inversion H8. inversion H6. subst. assumption. inversion H7. inversion H5. inversion H3.
inversion H1. subst.
apply MP with (ps:=[(Γ, (And (Or B C) (Neg B) → C) → (And (Neg B) (Or B C) → C));
(Γ, (And (Or B C) (Neg B) → C))]).
2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, (And (Neg B) (Or B C) → And (Or B C) (Neg B)) → (And (Or B C) (Neg B) → C) → (And (Neg B) (Or B C) → C));
(Γ, And (Neg B) (Or B C) → And (Or B C) (Neg B))]).
2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (And (Neg B) (Or B C)). exists (And (Or B C) (Neg B)).
exists C. auto. inversion H4. subst.
apply MP with (ps:=[(Γ, (And (Neg B) (Or B C) → (Neg B)) → (And (Neg B) (Or B C) → And (Or B C) (Neg B)));
(Γ, (And (Neg B) (Or B C) → (Neg B)))]).
2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, (And (Neg B) (Or B C) → (Or B C)) → (And (Neg B) (Or B C) → (Neg B)) → (And (Neg B) (Or B C) → And (Or B C) (Neg B)));
(Γ, (And (Neg B) (Or B C) → (Or B C)))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA7_I. exists (And (Neg B) (Or B C)). exists (Or B C).
exists (Neg B). auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA6_I. exists (Neg B). exists (Or B C).
auto. inversion H8. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA5_I. exists (Neg B). exists (Or B C).
auto. inversion H7. inversion H5. inversion H3. subst.
apply MP with (ps:=[(Γ, ((Or B C) → (Neg B) → C) → (And (Or B C) (Neg B) → C));
(Γ, ((Or B C) → (Neg B) → C))]).
2: apply MPRule_I. intros. inversion H4. subst.
apply Ax. apply AxRule_I. apply RA8_I. exists (Or B C). exists (Neg B). exists C.
auto. inversion H5. subst.
apply MP with (ps:=[(Γ, (C → Neg B → C) → (Or B C → Neg B → C));
(Γ, (C → Neg B → C))]).
2: apply MPRule_I. intros. inversion H6. subst.
apply MP with (ps:=[(Γ, (B → Neg B → C) → (C → Neg B → C) → (Or B C → Neg B → C));
(Γ, (B → Neg B → C))]).
2: apply MPRule_I. intros. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (Neg B → C). auto. inversion H8. subst.
apply MP with (ps:=[(Γ, ((And B (Neg B)) → C) → (B → Neg B → C));
(Γ, ((And B (Neg B)) → C))]).
2: apply MPRule_I. intros. inversion H9. subst.
apply Ax. apply AxRule_I. apply RA9_I. exists B. exists (Neg B). exists C.
auto. inversion H10. subst.
apply MP with (ps:=[(Γ, (Bot V → C) → (And B (Neg B) → C));
(Γ, (Bot V → C))]).
2: apply MPRule_I. intros. inversion H11. subst.
apply MP with (ps:=[(Γ, (And B (Neg B) → Bot V) → (Bot V → C) → (And B (Neg B) → C));
(Γ, (And B (Neg B) → Bot V))]).
2: apply MPRule_I. intros. inversion H12. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (And B (Neg B)). exists (Bot V).
exists (C). auto. inversion H13. subst. apply wContr_Bot. inversion H14. inversion H12. subst.
apply wEFQ. inversion H13. inversion H11. inversion H9. inversion H7. subst.
apply wThm_irrel. inversion H8. inversion H6. inversion H4. inversion H2.
Qed.

Lemma wNeg_Top : forall A B Γ,
  (wBIH_rules (Γ, ((wNeg A) → B))) ->
  (wBIH_rules (Γ, (Excl (Top _) A) → B)).
Proof.
intros A B Γ D. apply MP with (ps:=[(Γ, (wNeg A → B) → (Excl (Top V) A → B));
(Γ, (wNeg A → B))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (Excl (Top V) A → wNeg A) → (wNeg A → B) → Excl (Top V) A → B);
(Γ, (Excl (Top V) A → wNeg A))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I.
apply RA1_I. exists (Excl (Top V) A). exists (wNeg A). exists B. auto.
inversion H1. subst. apply wimp_Id_gen.
inversion H2. inversion H0. subst. assumption. inversion H1.
Qed.

Lemma Top_wNeg : forall A B Γ,
  (wBIH_rules (Γ, (Excl (Top _) A) → B)) ->
  (wBIH_rules (Γ, ((wNeg A) → B))).
Proof.
intros A B Γ D. apply MP with (ps:=[(Γ, (Excl (Top V) A → B) → (wNeg A → B));
(Γ, (Excl (Top V) A → B))]). 2: apply MPRule_I. intros. inversion H. subst.
intros. apply MP with (ps:=[(Γ, (wNeg A → Excl (Top V) A) → (Excl (Top V) A → B) → wNeg A → B);
(Γ, (wNeg A → Excl (Top V) A))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I.
apply RA1_I. exists (wNeg A). exists (Excl (Top V) A). exists B. auto.
inversion H1. subst. apply wimp_Id_gen.
inversion H2. inversion H0. subst. assumption. inversion H1.
Qed.

Lemma Top_wNeg_cons : forall A B Γ,
  (wBIH_rules (Γ, A → (Excl (Top _) B))) ->
  (wBIH_rules (Γ, A → (wNeg B))).
Proof.
intros. apply MP with (ps:=[(Γ, (Excl (Top V) B → wNeg B) → (A → wNeg B));
(Γ, (Excl (Top V) B → wNeg B))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A → Excl (Top V) B) → (Excl (Top V) B → wNeg B) → (A → wNeg B));
(Γ, (A → Excl (Top V) B))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I.
apply RA1_I. exists A. exists (Excl (Top V) B). exists (wNeg B). auto.
inversion H2. subst. assumption. inversion H3. inversion H1. subst.
apply wimp_Id_gen. inversion H2.
Qed.

Lemma Or_imp_assoc : forall A B C D Γ,
  (wBIH_rules (Γ, A → (Or (Or B C) D))) ->
  (wBIH_rules (Γ, A → (Or B (Or C D)))).
Proof.
intros.
apply MP with (ps:=[(Γ, (Or (Or B C) D → Or B (Or C D)) → (A → Or B (Or C D)));
(Γ, (Or (Or B C) D → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply MP with (ps:=[(Γ, (A → Or (Or B C) D) → (Or (Or B C) D → Or B (Or C D)) → (A → Or B (Or C D)));
(Γ, (A → Or (Or B C) D))]). 2: apply MPRule_I. intros. inversion H1. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists A. exists (Or (Or B C) D).
exists (Or B (Or C D)). auto. inversion H2. subst.
assumption. inversion H3. inversion H1. subst.
apply MP with (ps:=[(Γ, (D → Or B (Or C D)) → (Or (Or B C) D → Or B (Or C D)));
(Γ, (D → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ, ((Or B C) → Or B (Or C D)) → (D → Or B (Or C D)) → (Or (Or B C) D → Or B (Or C D)));
(Γ, ((Or B C) → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists (Or B C).
exists D. exists (Or B (Or C D)). auto. inversion H4. subst.
apply MP with (ps:=[(Γ, (C → Or B (Or C D)) → (Or B C → Or B (Or C D)));
(Γ, C → Or B (Or C D))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply MP with (ps:=[(Γ, (B → Or B (Or C D)) → (C → Or B (Or C D)) → (Or B C → Or B (Or C D)));
(Γ, B → Or B (Or C D))]). 2: apply MPRule_I. intros. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA4_I. exists B. exists C.
exists (Or B (Or C D)). auto. inversion H7. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists B. exists (Or C D). auto.
inversion H8. inversion H6. subst.
apply MP with (ps:=[(Γ, ((Or C D) → Or B (Or C D)) → (C → Or B (Or C D)));
(Γ, (Or C D) → Or B (Or C D))]). 2: apply MPRule_I. intros. inversion H7. subst.
apply MP with (ps:=[(Γ, (C → (Or C D)) → ((Or C D) → Or B (Or C D)) → (C → Or B (Or C D)));
(Γ, (C → (Or C D)))]). 2: apply MPRule_I. intros. inversion H8. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists C. exists (Or C D).
exists (Or B (Or C D)). auto. inversion H9. subst.
apply Ax. apply AxRule_I. apply RA2_I. exists C. exists D. auto. inversion H10.
inversion H8. subst. apply Ax. apply AxRule_I.
apply RA3_I. exists B. exists (Or C D). auto. inversion H9. inversion H7. inversion H5.
inversion H3. subst.
apply MP with (ps:=[(Γ, ((Or C D) → Or B (Or C D)) → (D → Or B (Or C D)));
(Γ, ((Or C D) → Or B (Or C D)))]). 2: apply MPRule_I. intros. inversion H4. subst.
apply MP with (ps:=[(Γ, (D → (Or C D)) → ((Or C D) → Or B (Or C D)) → (D → Or B (Or C D)));
(Γ, (D → (Or C D)))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists D. exists (Or C D).
exists (Or B (Or C D)). auto. inversion H6. subst.
apply Ax. apply AxRule_I. apply RA3_I. exists C. exists D. auto. inversion H7.
inversion H5. subst. apply Ax. apply AxRule_I. apply RA3_I. exists B. exists (Or C D). auto.
inversion H6. inversion H4. inversion H2.
Qed.

Lemma wClaim1 : forall A B Γ,
    (wBIH_rules (Γ, (Neg (Excl A B)) → ((wNeg B) → (wNeg A)))).
Proof.
intros A B Γ.
pose (wBIH_monot (Empty_set _, Neg (Excl A B) → wNeg B → wNeg A)). apply w. clear w.
apply MP with (ps:=[(Empty_set _, ((And (Neg (Excl A B)) (wNeg B)) → wNeg A) → (Neg (Excl A B) → wNeg B → wNeg A));
(Empty_set _, (And (Neg (Excl A B)) (wNeg B)) → wNeg A)]). 2: apply MPRule_I. intros. inversion H. subst.
apply Ax. apply AxRule_I. apply RA9_I. exists (Neg (Excl A B)).
exists (wNeg B). exists (wNeg A). auto. inversion H0. subst.
apply MP with (ps:=[(Empty_set _, ((Excl (Top V) (Or B (Excl A B))) → wNeg A) → (And (Neg (Excl A B)) (wNeg B) → wNeg A));
(Empty_set _, (Excl (Top V) (Or B (Excl A B))) → wNeg A)]). 2: apply MPRule_I. intros. inversion H1. subst.
apply MP with (ps:=[(Empty_set _, (And (Neg (Excl A B)) (wNeg B) → (Excl (Top V) (Or B (Excl A B)))) → ((Excl (Top V) (Or B (Excl A B))) → wNeg A) → (And (Neg (Excl A B)) (wNeg B) → wNeg A));
(Empty_set _, (And (Neg (Excl A B)) (wNeg B) → (Excl (Top V) (Or B (Excl A B)))))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (And (Neg (Excl A B)) (wNeg B)).
exists (Excl (Top V) (Or B (Excl A B))). exists (wNeg A). auto. inversion H3. subst.
apply wOr_Neg. apply Top_wNeg. apply wdual_residuation.
apply Or_imp_assoc. apply wdual_residuation. apply wimp_Id_gen. inversion H4. inversion H2. subst.
apply Top_wNeg_cons. apply wmon_Excl. apply Ax. apply AxRule_I.
apply RA11_I. exists A. exists B. auto. inversion H3. inversion H1.
intro. simpl. intros. inversion H.
Qed.

Lemma wDN_dist_imp : forall A B Γ,
    (wBIH_rules (Γ, (Neg (wNeg (A → B))) → ((Neg (wNeg A)) → (Neg (wNeg B))))).
Proof.
intros A B Γ.
apply MP with (ps:=[(Γ, (((wNeg B) → wNeg A) → Neg (wNeg A) → Neg (wNeg B)) → (Neg (wNeg (A → B)) → Neg (wNeg A) → Neg (wNeg B)));
(Γ, (((wNeg B) → wNeg A) → Neg (wNeg A) → Neg (wNeg B)))]). 2: apply MPRule_I. intros. inversion H. subst.
apply MP with (ps:=[(Γ, (Neg (wNeg (A → B)) → ((wNeg B) → wNeg A)) → (((wNeg B) → wNeg A) → Neg (wNeg A) → Neg (wNeg B)) → (Neg (wNeg (A → B)) → Neg (wNeg A) → Neg (wNeg B)));
(Γ, (Neg (wNeg (A → B)) → ((wNeg B) → wNeg A)))]). 2: apply MPRule_I. intros. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (Neg (wNeg (A → B))).
exists (wNeg B → wNeg A). exists (Neg (wNeg A) → Neg (wNeg B)). auto. inversion H1. subst.
apply MP with (ps:=[(Γ,((Neg (Excl A B)) → (wNeg B → wNeg A)) → (Neg (wNeg (A → B)) → wNeg B → wNeg A));
(Γ, ((Neg (Excl A B)) → (wNeg B → wNeg A)))]). 2: apply MPRule_I. intros. inversion H2. subst.
apply MP with (ps:=[(Γ,(Neg (wNeg (A → B)) → (Neg (Excl A B))) → ((Neg (Excl A B)) → (wNeg B → wNeg A)) → (Neg (wNeg (A → B)) → wNeg B → wNeg A));
(Γ, (Neg (wNeg (A → B)) → (Neg (Excl A B))))]). 2: apply MPRule_I. intros. inversion H3. subst.
apply Ax. apply AxRule_I. apply RA1_I. exists (Neg (wNeg (A → B))).
exists (Neg (Excl A B)). exists (wNeg B → wNeg A). auto. inversion H4. subst.
apply MP with (ps:=[(Γ, ((Excl A B) → (wNeg (A → B))) → (Neg (wNeg (A → B)) → Neg (Excl A B)));
(Γ, (Excl A B) → (wNeg (A → B)))]). 2: apply MPRule_I. intros. inversion H5. subst.
apply Ax. apply AxRule_I. apply RA10_I. exists (Excl A B).
exists (wNeg (A → B)). auto. inversion H6. subst. apply Ax.
apply AxRule_I. apply RA12_I. exists A. exists B. auto. inversion H7. inversion H5.
inversion H3. subst. apply wClaim1. inversion H4. inversion H2. inversion H0. subst.
apply Ax. apply AxRule_I. apply RA10_I. exists (wNeg B).
exists (wNeg A). auto. inversion H1.
Qed.



