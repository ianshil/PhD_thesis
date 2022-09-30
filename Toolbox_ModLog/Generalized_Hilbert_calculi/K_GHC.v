Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Ensembles.
Require Import gen.
Require Import K_Syntax.

(* We define here the axioms. *)

Definition MA1 (A B C : MPropF) : MPropF := (A --> B) --> ((B --> C) --> (A --> C)).

Definition MA2 (A B : MPropF) : MPropF := A --> (B --> A).

Definition MA3 (A B : MPropF) : MPropF := ((A --> B) --> A) --> A.

Definition MA4 (A : MPropF) : MPropF := Bot --> A.

Definition MA5 (A B : MPropF) : MPropF := Box (A --> B) --> (Box A --> Box B).

Inductive KAxioms (A : MPropF) : Prop :=
 | MA1_I : (exists B C D, A = (MA1 B C D)) -> KAxioms A
 | MA2_I : (exists B C, A = (MA2 B C)) -> KAxioms A
 | MA3_I :  (exists B C, A = (MA3 B C)) -> KAxioms A
 | MA4_I :  (exists B, A = (MA4 B)) -> KAxioms A
 | MA5_I :  (exists B C, A = (MA5 B C)) -> KAxioms A.

(* Then, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later.

   We start by giving the rules common to both calculi. *)

Inductive IdRule : rls ((Ensemble MPropF) * MPropF) :=
  | IdRule_I : forall A (Γ : Ensemble _),
                  (In _ Γ A) -> IdRule [] (Γ , A).

Inductive AxRule : rls ((Ensemble MPropF) * MPropF) :=
  | AxRule_I : forall Γ (A : MPropF),
          (KAxioms A) -> AxRule [] (Γ , A).

Inductive MPRule : rls ((Ensemble MPropF) * MPropF) :=
  | MPRule_I : forall A B Γ,
          MPRule [(Γ , A --> B); (Γ , A)]
                    (Γ , B).

(* Then we turn to the distinctive rules of each calculus. *)

Inductive wNecRule : rls ((Ensemble MPropF) * MPropF) :=
  | wNecRule_I : forall (A : MPropF) Γ,
          wNecRule [(Empty_set MPropF , A)]
                    (Γ , Box A).

Inductive sNecRule : rls ((Ensemble MPropF) * MPropF) :=
  | sNecRule_I : forall (A : MPropF) Γ,
          sNecRule [(Γ , A)]
                    (Γ, Box A).

(* At last we can define our calculi wKH and sKH. *)

Inductive wKH_rules (s : ((Ensemble _) * MPropF)) : Prop :=
  | Id : IdRule [] s -> wKH_rules s
  | Ax : AxRule [] s -> wKH_rules s
  | MP : forall ps, (forall prem, List.In prem ps -> wKH_rules prem) -> MPRule ps s -> wKH_rules s
  | wNec : forall ps, (forall prem, List.In prem ps -> wKH_rules prem) -> wNecRule ps s -> wKH_rules s
.

Inductive sKH_rules (s : ((Ensemble _) * MPropF)) : Prop :=
  | Ids : IdRule [] s -> sKH_rules s
  | Axs : AxRule [] s -> sKH_rules s
  | MPs : forall ps, (forall prem, List.In prem ps -> sKH_rules prem) -> MPRule ps s -> sKH_rules s
  | sNec : forall ps, (forall prem, List.In prem ps -> sKH_rules prem) -> sNecRule ps s -> sKH_rules s
.

(* Then, we define macros for provability. *)

Definition wKH_prv s := wKH_rules s.
Definition sKH_prv s := sKH_rules s.
