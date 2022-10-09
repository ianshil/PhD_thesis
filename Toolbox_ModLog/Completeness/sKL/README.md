# Completeness sKH

Instructions for compiling all files in sKL.
=========================================================================================

1. Run "make Generalized_Hilbert_calculi" which compiles all files found in ../../Generalized_Hilbert_calculi directory.

2. Run "make KSPropositional" which compiles all files found in ../../Kripke_semantics/Propositional directory.

3. Run "make Syntax" which compiles all files found in ../../Syntax directory.

4. Run "make wKL_compl" which compiles all files found in ../wKL directory.

5. Run "make sKH_completeness.vo" which compiles all files in sKL.


NOTES
-----

In sKL, each file has a specific role:

              sKH_completeness.v  ==>  shows completeness of sKH w.r.t. the global semantic consequence relation
