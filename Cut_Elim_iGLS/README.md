Instructions for compiling files up to and including GL4ip_cut_elim.v which contains cut-elimination.
=========================================================================================

1. Run "make general" which compiles all files found in ../general directory.

2. Run "make GL4ip_cut_elim.vo" which compiles all files in GL up to and including GL4ip_cut_elim.v.


NOTES
-----

In GL4ip, each file has a specific role:

                       DLW_WO_list_nat.v  ==>  defines the shortlex order << (authored by Dominique Larchey-Wendling)
                   GL4ip_PSGL4ip_calcs.v  ==>  defines the formal language, as well as the GL4ip and PSGL4ip calculus
             GL4ip_PSGL4ip_remove_list.v  ==>  defines the operation remove_list on list of formulae
               GL4ip_PSGL4ip_list_lems.v  ==>  states useful lemmas about list of formulae
                     GL4ip_PSGL4ip_dec.v  ==>  shows that the applicability of the rules of GL4ip and PSGL4ip is decidable
                            GL4ip_exch.v  ==>  shows that GL4ip admits exchange
                             GL4ip_wkn.v  ==>  shows that GL4ip admits weakening
                        GL4ip_inv_ImpR.v  ==>  shows that the rule (->R) is invertible in GL4ip
                              GL4ip_Id.v  ==>  shows that in GL4ip all identities are provable
                   GL4ip_inv_AndR_AndL.v  ==>  shows that the rules (/\R) and (/\L) are invertible in GL4ip
                         GL4ip_inv_OrL.v  ==>  shows that the rule (\/L) is invertible in GL4ip
                     GL4ip_inv_AndImpL.v  ==>  shows that the rule (/\->L) is invertible in GL4ip
                    GL4ip_inv_AtomImpL.v  ==>  shows that the rule (p->L) is invertible in GL4ip
                      GL4ip_inv_OrImpL.v  ==>  shows that the rule (\/->L) is invertible in GL4ip
                   GL4ip_inv_BoxImpL_R.v  ==>  shows that the rule ([]->L) is right-invertible in GL4ip
                   GL4ip_inv_ImpImpL_R.v  ==>  shows that the rule (->->L) is right-invertible in GL4ip
                        GL4ip_ImpL_adm.v  ==>  shows that GL4ip admits the rule (->L)
                 GL4ip_inv_A_ImpImpL_L.v  ==>  shows a lemma pertaining to the left-invertibility in GL4ip of the rule (->->L)
                             GL4ip_ctr.v  ==>  shows that GL4ip admits contraction
                      GL4ip_inv_ImpL_R.v  ==>  shows that the rule (->L) is right-invertible in GL4ip
           PSGL4ip_termination_measure.v  ==>  defines the measure to show the termination of PSGL4ip
                   PSGL4ip_termination.v  ==>  shows the termination of PSGL4ip
                    GL4ip_additive_cut.v  ==>  shows that GL4ip admits cut
                        GL4ip_cut_elim.v  ==>  shows that cut is eliminable from GL4ip + cut

Acknowledgement 
-----

The file DLW_WO_list_nat.v was authored by Dominique Larchey-Wendling and graciously shared with us.
