%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../general.
# Build those by "make general" in the current directory.

general :
	cd .. && make general && cd Cut_Elim_iGLS

DLW_WO_list_nat.vo : DLW_WO_list_nat.v

GL4ip_PSGL4ip_calcs.vo : GL4ip_PSGL4ip_calcs.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo

GL4ip_PSGL4ip_dec.vo : GL4ip_PSGL4ip_dec.v GL4ip_PSGL4ip_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_remove_list.vo

GL4ip_PSGL4ip_list_lems.vo : GL4ip_PSGL4ip_list_lems.v ../general/genT.vo ../general/gen_tacs.vo ../general/List_lemmasT.vo ../general/existsT.vo GL4ip_PSGL4ip_calcs.vo

GL4ip_PSGL4ip_remove_list.vo : GL4ip_PSGL4ip_remove_list.v GL4ip_PSGL4ip_calcs.vo ../general/existsT.vo

GL4ip_exch.vo : GL4ip_exch.v GL4ip_PSGL4ip_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GL4ip_PSGL4ip_list_lems.vo ../general/strong_inductionT.vo

GL4ip_wkn.vo : GL4ip_wkn.v GL4ip_PSGL4ip_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GL4ip_PSGL4ip_list_lems.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_dec.vo

GL4ip_inv_ImpR.vo : GL4ip_inv_ImpR.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_inv_OrL.vo : GL4ip_inv_OrL.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_inv_AndR_AndL.vo : GL4ip_inv_AndR_AndL.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_inv_AndImpL.vo : GL4ip_inv_AndImpL.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_inv_OrImpL.vo : GL4ip_inv_OrImpL.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_inv_AtomImpL.vo : GL4ip_inv_AtomImpL.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_inv_BoxImpL.vo : GL4ip_inv_BoxImpL.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_inv_ImpImpL_R.vo : GL4ip_inv_ImpImpL_R.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo

GL4ip_ImpL_adm.vo : GL4ip_ImpL_adm.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo GL4ip_inv_AndR_AndL.vo GL4ip_inv_OrL.vo GL4ip_inv_AtomImpL.vo GL4ip_inv_AndImpL.vo GL4ip_inv_OrImpL.vo GL4ip_inv_ImpImpL_R.vo GL4ip_inv_BoxImpL_R.vo

GL4ip_inv_ImpImpL_L.vo : GL4ip_inv_ImpImpL_L.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo GL4ip_ImpL_adm.vo GL4ip_inv_ImpR.vo

GL4ip_Id.vo : GL4ip_Id.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_calcs.vo GL4ip_exch.vo GL4ip_wkn.vo GL4ip_inv_ImpR.vo

GL4ip_ctr.vo : GL4ip_ctr.v GL4ip_PSGL4ip_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo GL4ip_PSGL4ip_list_lems.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo GL4ip_inv_AndR_AndL.vo GL4ip_inv_OrL.vo GL4ip_inv_AtomImpL.vo GL4ip_inv_AndImpL.vo GL4ip_inv_OrImpL.vo GL4ip_inv_ImpImpL_R.vo GL4ip_inv_ImpImpL_L.vo GL4ip_inv_ImpR.vo GL4ip_inv_BoxImpL_R.vo

GL4ip_inv_ImpL_R.vo : GL4ip_inv_ImpL_R.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_calcs.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo GL4ip_exch.vo GL4ip_wkn.vo GL4ip_inv_AndR_AndL.vo GL4ip_inv_OrL.vo GL4ip_inv_AtomImpL.vo GL4ip_inv_AndImpL.vo GL4ip_inv_OrImpL.vo GL4ip_inv_ImpImpL_R.vo GL4ip_inv_BoxImpL_R.vo GL4ip_ctr.vo

PSGL4ip_termination.vo : PSGL4ip_termination.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GL4ip_PSGL4ip_list_lems.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_dec.vo PSGL4ip_termination_measure.vo GL4ip_PSGL4ip_remove_list.vo

PSGL4ip_termination_measure.vo : PSGL4ip_termination_measure.v GL4ip_PSGL4ip_calcs.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GL4ip_PSGL4ip_list_lems.vo GL4ip_PSGL4ip_remove_list.vo ../general/List_lemmasT.vo DLW_WO_list_nat.vo GL4ip_PSGL4ip_dec.vo

GL4ip_prv_dec.vo : GL4ip_prv_dec.v GL4ip_PSGL4ip_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GL4ip_PSGL4ip_list_lems.vo ../general/strong_inductionT.vo PSGL4ip_termination_measure.vo PSGL4ip_termination.vo GL4ip_exch.vo GL4ip_wkn.vo GL4ip_Id.vo GL4ip_ctr.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo

GL4ip_additive_cut.vo : GL4ip_additive_cut.v GL4ip_PSGL4ip_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GL4ip_PSGL4ip_list_lems.vo ../general/strong_inductionT.vo PSGL4ip_termination_measure.vo PSGL4ip_termination.vo GL4ip_exch.vo GL4ip_wkn.vo GL4ip_Id.vo GL4ip_ctr.vo GL4ip_inv_ImpL_R.vo GL4ip_inv_AndImpL.vo GL4ip_inv_OrImpL.vo GL4ip_inv_AndR_AndL.vo GL4ip_inv_AtomImpL.vo GL4ip_inv_ImpImpL_R.vo GL4ip_inv_ImpImpL_L.vo GL4ip_inv_ImpR.vo GL4ip_inv_OrL.vo GL4ip_PSGL4ip_remove_list.vo GL4ip_PSGL4ip_dec.vo

GL4ip_cut_elim.vo : GL4ip_cut_elim.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GL4ip_PSGL4ip_calcs.vo GL4ip_additive_cut.vo

GL4ip_cut_extraction_theorem.vo : GL4ip_cut_extraction_theorem.v GL4ip_cut_elim.vo GL4ip_prv_dec.vo


clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../general && rm *.vo *.glob && cd ../GL4ip

clean_Cut_Elim_iGLS : clean_coq 

clean_all : clean_general clean_Cut_Elim_iGLS

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
