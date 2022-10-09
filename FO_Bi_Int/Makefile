%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../general.
# Build those by "make general" in the current directory.

general :
	cd .. && make general && cd Prop_Bi_Int

BiInt_GHC.vo: BiInt_GHC.v gen.vo
BiInt_remove_list.vo: BiInt_remove_list.v existsT.vo BiInt_GHC.vo
BiInt_logics.vo: BiInt_logics.v BiInt_GHC.vo
BiInt_extens_interactions.vo: BiInt_extens_interactions.v BiInt_GHC.vo BiInt_logics.vo
wBIH_meta_interactions.vo: wBIH_meta_interactions.v genT.vo BiInt_GHC.vo BiInt_logics.vo BiInt_extens_interactions.vo
sBIH_meta_interactions.vo: sBIH_meta_interactions.v BiInt_GHC.vo BiInt_logics.vo BiInt_extens_interactions.vo wBIH_meta_interactions.vo
wBIH_DMP.vo: wBIH_DMP.v genT.vo BiInt_GHC.vo BiInt_remove_list.vo BiInt_logics.vo BiInt_extens_interactions.vo wBIH_meta_interactions.vo
BiInt_Lindenbaum_lem.vo: BiInt_Lindenbaum_lem.v BiInt_GHC.vo BiInt_remove_list.vo BiInt_logics.vo BiInt_extens_interactions.vo wBIH_meta_interactions.vo
BiInt_Kripke_sem.vo: BiInt_Kripke_sem.v BiInt_GHC.vo
BiInt_bisimulation.vo: BiInt_bisimulation.v BiInt_GHC.vo BiInt_Kripke_sem.vo
BiInt_soundness.vo: BiInt_soundness.v BiInt_GHC.vo BiInt_Kripke_sem.vo
BiInt_wcompleteness.vo: BiInt_wcompleteness.v BiInt_GHC.vo BiInt_logics.vo BiInt_extens_interactions.vo wBIH_meta_interactions.vo sBIH_meta_interactions.vo BiInt_Lindenbaum_lem.vo BiInt_Kripke_sem.vo
BiInt_scompleteness.vo: BiInt_scompleteness.v BiInt_GHC.vo BiInt_logics.vo BiInt_extens_interactions.vo wBIH_meta_interactions.vo sBIH_meta_interactions.vo BiInt_Lindenbaum_lem.vo BiInt_Kripke_sem.vo BiInt_bisimulation.vo BiInt_wcompleteness.vo
BiInt_sem_look_back.vo: BiInt_sem_look_back.v BiInt_GHC.vo BiInt_logics.vo BiInt_extens_interactions.vo wBIH_meta_interactions.vo sBIH_meta_interactions.vo BiInt_Kripke_sem.vo BiInt_soundness.vo BiInt_wcompleteness.vo BiInt_scompleteness.vo wBIH_DMP.vo



clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../general && rm *.vo *.glob && cd ../Prop_Bi_Int

clean_Prop_Bi_Int : clean_coq 

clean_all : clean_general clean_Prop_Bi_Int

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob

