# Completeness wKH

Instructions for compiling all files in wKL.
=========================================================================================

1. Run "make Generalized_Hilbert_calculi" which compiles all files found in ../../Generalized_Hilbert_calculi directory.

2. Run "make KSPropositional" which compiles all files found in ../../Kripke_semantics/Propositional directory.

3. Run "make Syntax" which compiles all files found in ../../Syntax directory.

4. Run "make wKH_completeness.vo" which compiles all files in wKL.


NOTES
-----

In wKL, each file has a specific role:

            K_strong_induction.v  ==>  shows a strong induction principle on natural numbers
            wKH_Lindenbaum_lem.v  ==>  shows a Lindenbaum lemma for wKH
              wKH_completeness.v  ==>  shows completeness of wKH w.r.t. the local semantic consequence relation
