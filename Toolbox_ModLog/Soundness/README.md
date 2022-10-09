# Soundness Modal Logic

Instructions for compiling all files in Soundness.
=========================================================================================

1. Run "make Generalized_Hilbert_calculi" which compiles all files found in ../Generalized_Hilbert_calculi directory.

2. Run "make KSPropositional" which compiles all files found in ../Kripke_semantics/Propositional directory.

3. Run "make Syntax" which compiles all files found in ../Syntax directory.

4. Run "make wKH_sKH_soundness.vo" which compiles all files in Soundness.


NOTES
-----

In Prop_Bi_Int, each file has a specific role:

              wKH_sKH_soundness.v  ==>  shows soundess of wKH (resp. sKH) w.r.t. the local (resp. global) semantic consequence relation
