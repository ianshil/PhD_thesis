# Propositional Kripke Semantics

Instructions for compiling all files in Kripke_semantics.
=========================================================================================

1. Run "make Syntax" which compiles all files found in ../../Syntax directory.

2. Run "make KSPropositional_all" which compiles all files in Propositional.


NOTES
-----

In Propositional, each file has a specific role:

             K_Kripke_sem.v  ==>  defines the Kripke semantics for the propositional modal language
           K_bisimulation.v  ==>  defines the notion of bisimulation, and shows it entails logical equivalence
