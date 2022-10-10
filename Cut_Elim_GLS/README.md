# Cut-elimination for GLS

Instructions for compiling files up to and including GLS_extraction_theorem.v which extracts cut-elimination.
=========================================================================================

1. Run "make general" which compiles all files found in ../general directory.

2. Run "make GLS_cut_extraction_theorem.vo" which compiles all files in Cut_Elim_GLS up to and including GLS_cut_extraction_theorem.v.


NOTES
-----

In Cut_Elim_GLS, each file has a specific role:

              GLS_PSGLS_calcs.v  ==>  defines the formal language, as well as the GLS and PSGLS calculi
        GLS_PSGLS_remove_list.v  ==>  defines the operation remove_list on list of formulae
          GLS_PSGLS_list_lems.v  ==>  states useful lemmas about list of formulae
                GLS_PSGLS_dec.v  ==>  shows that the applicability of the rules of GLS and PSGLS is decidable
                     GLS_exch.v  ==>  shows that GLS admits exchange
                      GLS_wkn.v  ==>  shows that GLS admits weakening
            GLS_inv_ImpR_ImpL.v  ==>  shows that the rules ImpR and ImpL are invertible in GLS
                      GLS_ctr.v  ==>  shows that GLS admits contraction
    PSGLS_termination_measure.v  ==>  defines the measure to show the termination of PSGLS
            PSGLS_termination.v  ==>  shows the termination of PSGLS
                  GLS_prv_dec.v  ==>  shows that provability in PSGLS and GLS is decidable 
             GLS_additive_cut.v  ==>  shows that GLS admits cut
                 GLS_cut_elim.v  ==>  shows that cut is eliminable from GLS + cut
   GLS_cut_extraction_theorem.v  ==>  extract the Haskell program performing cut-elimination
