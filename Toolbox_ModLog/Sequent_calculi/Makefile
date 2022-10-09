%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../../general and ../Toolbox_ModLog/Syntax.
# Build those by "make general" and "make Syntax" in the current directory.

general :
	cd .. && cd .. && make general && cd Toolbox_ModLog/Sequent_calculi
  
Syntax :
	cd .. && cd Syntax && make Syntax_all && cd .. && cd Sequent_calculi

wKS_calcs.vo : wKS_calcs.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo

wKS_dec.vo : wKS_dec.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo wKS_remove_list.vo

wKS_list_lems.vo : wKS_list_lems.v ../general/genT.vo ../general/gen_tacs.vo ../general/List_lemmasT.vo ../general/existsT.vo wKS_calcs.vo

wKS_remove_list.vo : wKS_remove_list.v wKS_calcs.vo ../general/existsT.vo

wKS_additive_cut.vo : wKS_additive_cut.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo PSwKS_termination_measure.vo PSwKS_termination.vo wKS_exch.vo wKS_wkn.vo wKS_ctr.vo wKS_remove_list.vo wKS_dec.vo wKS_inv_ImpR_ImpL.vo

wKS_ctr.vo : wKS_ctr.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo wKS_list_lems.vo ../general/dd_fc.vo ../general/strong_inductionT.vo wKS_inv_ImpR_ImpL.vo

wKS_exch.vo : wKS_exch.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo

wKS_inv_ImpR_ImpL.vo : wKS_inv_ImpR_ImpL.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo wKS_exch.vo wKS_wkn.vo wKS_remove_list.vo wKS_dec.vo

wKS_wkn.vo : wKS_wkn.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo wKS_dec.vo

PSwKS_termination.vo : PSwKS_termination.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo wKS_dec.vo PSwKS_termination_measure.vo wKS_remove_list.vo

PSwKS_termination_measure.vo : PSwKS_termination_measure.v wKS_calcs.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo wKS_remove_list.vo ../general/List_lemmasT.vo

wKS_cut_elim.vo : wKS_cut_elim.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo PSwKS_termination_measure.vo PSwKS_termination.vo wKS_exch.vo wKS_wkn.vo wKS_ctr.vo wKS_remove_list.vo wKS_dec.vo wKS_inv_ImpR_ImpL.vo wKS_additive_cut.vo

wKS_cut_extraction_theorem.vo : wKS_cut_extraction_theorem.v wKS_cut_elim.vo wKS_prv_dec.vo

wKS_prv_dec.vo : wKS_prv_dec.v wKS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo wKS_list_lems.vo ../general/strong_inductionT.vo PSwKS_termination_measure.vo PSwKS_termination.vo wKS_exch.vo wKS_wkn.vo wKS_ctr.vo wKS_remove_list.vo wKS_dec.vo wKS_inv_ImpR_ImpL.vo



clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../general && rm *.vo *.glob && cd ../Cut_Elim_wKS

clean_Cut_Elim_wKS : clean_coq 

clean_all : clean_general clean_Cut_Elim_wKS

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
