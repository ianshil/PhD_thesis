# Cut-elimination for wKS

Instructions for compiling files up to and including wKS_extraction_theorem.v which extracts cut-elimination.
=========================================================================================

1. Run "make general" which compiles all files found in ../../general directory.

2. Run "make Syntax" which compiles all files found in ../Syntax directory.

3. Run "make wKS_cut_extraction_theorem.vo" which compiles all files in Sequent_calculi up to and including wKS_cut_extraction_theorem.v.


NOTES
-----

In Sequent_calculi, each file has a specific role:

                   wKS_calc.v  ==>  defines the calculus wKS
            wKS_remove_list.v  ==>  defines the operation remove_list on list of formulae
              wKS_list_lems.v  ==>  states useful lemmas about list of formulae
                    wKS_dec.v  ==>  shows that the applicability of the rules of wKS is decidable
                   wKS_exch.v  ==>  shows that wKS admits exchange
                    wKS_wkn.v  ==>  shows that wKS admits weakening
          wKS_inv_ImpR_ImpL.v  ==>  shows that the rules ImpR and ImpL are invertible in wKS
                    wKS_ctr.v  ==>  shows that wKS admits contraction
    wKS_termination_measure.v  ==>  defines the measure to show the termination of wKS
            wKS_termination.v  ==>  shows the termination of wKS
                wKS_prv_dec.v  ==>  shows that provability in wKS is decidable 
           wKS_additive_cut.v  ==>  shows that wKS admits cut
               wKS_cut_elim.v  ==>  shows that cut is eliminable from wKS + cut
 wKS_cut_extraction_theorem.v  ==>  extract the Haskell program performing cut-elimination
