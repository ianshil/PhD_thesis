%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../general.
# Build those by "make general" in the current directory.

general :
	cd .. && make general && cd FO_Bi_Int

FO_BiInt_strong_induction.vo: FO_BiInt_strong_induction.v
FO_BiInt_Syntax.vo: FO_BiInt_Syntax.v
FO_BiInt_GHC.vo: FO_BiInt_GHC.v gen.vo genT.vo FO_BiInt_Syntax.vo
FO_BiInt_remove_list.vo: FO_BiInt_remove_list.v existsT.vo FO_BiInt_Syntax.vo
FO_BiInt_logics.vo: FO_BiInt_logics.v FO_BiInt_Syntax.vo BiInt_GHC.vo
FO_BiInt_extens_interactions.vo: FO_BiInt_extens_interactions.v FO_BiInt_Syntax.vo FO_BiInt_GHC.vo FO_BiInt_logics.vo
FOwBIH_meta_interactions.vo: FOwBIH_meta_interactions.v gen.vo genT.vo FO_BiInt_Syntax.vo FO_BiInt_remove_list.vo FO_BiInt_GHC.vo FO_BiInt_logics.vo FO_BiInt_extens_interactions.vo
FOsBIH_meta_interactions.vo: FOsBIH_meta_interactions.v gen.vo genT.vo FO_BiInt_Syntax.vo FO_BiInt_remove_list.vo FO_BiInt_GHC.vo FO_BiInt_logics.vo FO_BiInt_extens_interactions.vo FOwBIH_meta_interactions.vo
FO_BiInt_Kripke_sem.vo: FO_BiInt_Kripke_sem.v FO_BiInt_Syntax.vo
FO_BiInt_soundness.vo: FO_BiInt_soundness.v FO_BiInt_Syntax.vo FO_BiInt_GHC.vo FO_BiInt_Kripke_sem.vo FO_BiInt_extens_interactions.vo FOwBIH_meta_interactions.vo
FO_BiInt_Lindenbaum_lem.vo: FO_BiInt_Lindenbaum_lem.v FO_BiInt_Syntax.vo FO_BiInt_remove_list.vo FO_BiInt_GHC.vo FO_BiInt_logics.vo FO_BiInt_extens_interactions.vo FOwBIH_meta_interactions.vo FOsBIH_meta_interactions.vo FO_BiInt_strong_induction.vo
FO_BiInt_wcompleteness.vo: FO_BiInt_wcompleteness.v FO_BiInt_Syntax.vo FO_BiInt_remove_list.vo FO_BiInt_GHC.vo FO_BiInt_logics.vo FO_BiInt_extens_interactions.vo FOwBIH_meta_interactions.vo FOsBIH_meta_interactions.vo FO_BiInt_strong_induction.vo FO_BiInt_Kripke_sem.vo FO_BiInt_Lindenbaum_lem.vo
FO_BiInt_scompleteness.vo: FO_BiInt_scompleteness.v FO_BiInt_Syntax.vo FO_BiInt_remove_list.vo FO_BiInt_GHC.vo FO_BiInt_logics.vo FO_BiInt_extens_interactions.vo FOwBIH_meta_interactions.vo FOsBIH_meta_interactions.vo FO_BiInt_strong_induction.vo FO_BiInt_Kripke_sem.vo FO_BiInt_Lindenbaum_lem.vo FO_BiInt_wcompleteness.vo FO_BiInt_soundness.vo



clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../general && rm *.vo *.glob && cd ../FO_Bi_Int

clean_FO_Bi_Int : clean_coq 

clean_all : clean_general clean_FO_Bi_Int

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob

