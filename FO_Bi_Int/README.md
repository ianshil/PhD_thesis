# First-Order Bi-Intuitionistic Logics

Instructions for compiling files up to and including FO_BiInt_scompleteness.v.
=========================================================================================

1. Run "make general" which compiles all files found in ../general directory.

2. Run "make FO_BiInt_scompleteness.vo" which compiles all files in FO_Bi_Int up to and including FO_BiInt_scompleteness.v.


NOTES
-----

In FO_Bi_Int, each file has a specific role:

       FO_BiInt_strong_induction.v  ==>  proves a strong induction principle on natural numbers
                 FO_BiInt_Syntax.v  ==>  defines the first-order (bi-intuitionistic) languages
                    FO_BiInt_GHC.v  ==>  defines the FOwKH and FOsKH calculi
                 FO_BiInt_logics.v  ==>  shows that FOwKH and FOsKH define finitary logics
            FO_BiInt_remove_list.v  ==>  states useful lemmas about the operation of removing elements from lists
    FO_BiInt_extens_interactions.v  ==>  shows that FOwKH is a subset of FOsKH, but that they share the same theorems
       FOwBIH_meta_interactions.v  ==>  shows proof-theoretic propertis of FOwKH
       FOsBIH_meta_interactions.v  ==>  shows proof-theoretic propertis of FOsKH
             FO_BiInt_Kripke_sem.v  ==>  defines the Kripke semantics for the first-order bi-intuitionistic language
              FO_BiInt_soundness.v  ==>  shows soundess of FOwKH (resp. FOsKH) w.r.t. the local (resp. global) semantic consequence relation
         FO_BiInt_Lindenbaum_lem.v  ==>  shows a Lindenbaum lemma on closed pairs for FOwKH
          FO_BiInt_wcompleteness.v  ==>  explores completeness of FOwKH w.r.t. the local semantic consequence relation
          FO_BiInt_scompleteness.v  ==>  shows relative completeness of FOsKH w.r.t. the global semantic consequence relation
