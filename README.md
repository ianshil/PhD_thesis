# PhD_thesis

Coq formalisation of the PhD dissertation "New Foundations for the Proof Theory of Bi-Intuitionistic and Provability Logics Mechanized in Coq" (2022).

By Ian Shillito.

----

The general directory contains files for encoding derivability and provability in sequent calculus, and other generic results.

The Toolbox_ModLog directory corresponds to Part I of the dissertation. It contains encodings of foundational tools for modal logic.

The Prop_Bi_Int directory corresponds to Chapter 8 of the dissertation. It contains encodings of a generalized Hilbert calculi, Kripke semantics for propositional bi-intuitionistic logics wBIL and sBIL and their related proofs, e.g. deduction theorems, soundness and completeness.

The FO_Bi_Int directory corresponds to Chapter 9 of the dissertation. It contains encodings of a generalized Hilbert calculi, Kripke semantics for first-order bi-intuitionistic logics wBIL and sBIL and their related proofs, e.g. deduction theorems, soundness and relative completeness.

The Cut_Elim_GLS directory corresponds to Chapter 12 of the dissertation. It contains encodings of a sequent calculus for classical provability logic GL and its related proofs, e.g. cut-eliminiation.

The Cut_Elim_iGLS directory corresponds to Chapter 13 of the dissertation. It contains encodings of a sequent calculus for intuitionistic provability logic iGL and its related proofs, e.g. cut-eliminiation.

----

To use, see GL4ip/README.md.

Tested on Coq 8.14.0 (September, 2021)
