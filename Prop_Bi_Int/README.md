# Propositional Bi-Intuitionistic Logics

Instructions for compiling files up to and including BiInt_sem_look_back.v.
=========================================================================================

1. Run "make general" which compiles all files found in ../general directory.

2. Run "make BiInt_sem_look_back.vo" which compiles all files in Prop_Bi_Int up to and including BiInt_sem_look_back.v.


NOTES
-----

In Prop_Bi_Int, each file has a specific role:

                    BiInt_GHC.v  ==>  defines the formal language, as well as the wKH and sKH calculi
                 BiInt_logics.v  ==>  shows that wBIH and sBIH define finitary logics
            BiInt_remove_list.v  ==>  states useful lemmas about the operation of removing elements from lists
    BiInt_extens_interactions.v  ==>  shows that wBIH is a subset of sBIH, but that they share the same theorems
       wBIH_meta_interactions.v  ==>  shows proof-theoretic propertis of wBIH
       sBIH_meta_interactions.v  ==>  shows proof-theoretic propertis of sBIH
                     wBIH_DMP.v  ==>  shows that wBIH admits the dual modus ponens rule
             BiInt_Kripke_sem.v  ==>  defines the Kripke semantics for the bi-intuitionistic language
           BiInt_bisimulation.v  ==>  defines the notion of bisimulation, and shows it entails logical equivalence
              BiInt_soundness.v  ==>  shows soundess of wBIH (resp. sBIH) w.r.t. the local (resp. global) semantic consequence relation
         BiInt_Lindenbaum_lem.v  ==>  shows a Lindenbaum lemma for wBIH
            wBIH_completeness.v  ==>  shows completeness of wBIH w.r.t. the local semantic consequence relation
            sBIH_completeness.v  ==>  shows completeness of sBIH w.r.t. the global semantic consequence relation
          BiInt_sem_look_back.v  ==>  shows the failure of properties of sKH using soundness
