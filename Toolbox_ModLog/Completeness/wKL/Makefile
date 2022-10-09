%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../../Generalized_Hilbert_calculi and ../../Kripke_semantics/Propositional and ../../Syntax.
# Build those by "make Generalized_Hilbert_calculi" and "make KSPropositional" and "make Syntax" in the current directory.

Generalized_Hilbert_calculi :
	cd .. && cd .. && cd Generalized_Hilbert_calculi && make Generalized_Hilbert_calculi_all && cd .. && cd Completeness && cd wKL
  
KSPropositional :
	cd .. && cd .. && cd Kripke_semantics && cd Propositional && make KSPropositional_all && cd .. && cd .. && cd Completeness && cd wKL

Syntax :
	cd .. && cd .. && cd Syntax && make Syntax_all && cd .. && cd Completeness && cd wKL

K_strong_induction.vo: K_strong_induction.v
wKH_Lindenbaum_lem.vo: wKH_Lindenbaum_lem.v K_Syntax.vo K_GHC.vo K_logics.vo K_extens_interactions.vo K_wKH_meta_interactions.vo
wKH_completeness.vo: wKH_completeness.v K_Syntax.vo K_GHC.vo K_logics.vo K_extens_interactions.vo K_wKH_meta_interactions.vo K_sKH_meta_interactions.vo K_Kripke_sem.vo wKH_Lindenbaum_lem.vo
wKL_compl: wKH_completeness.vo


clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../../../general && rm *.vo *.glob && cd ../Toolbox_ModLog/Completeness/wKL

clean_wKL : clean_coq 

clean_all : clean_general clean_wKL

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
