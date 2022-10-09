%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../../Generalized_Hilbert_calculi and ../../Kripke_semantics/Propositional and ../../Syntax and ../wKL.
# Build those by "make Generalized_Hilbert_calculi" and "make KSPropositional" and "make Syntax" and "make wKL_compl" in the current directory.

Generalized_Hilbert_calculi :
	cd .. && cd .. && cd Generalized_Hilbert_calculi && make Generalized_Hilbert_calculi_all && cd .. && cd Completeness && cd sKL
  
KSPropositional :
	cd .. && cd .. && cd Kripke_semantics && cd Propositional && make KSPropositional_all && cd .. && cd .. && cd Completeness && cd sKL

Syntax :
	cd .. && cd .. && cd Syntax && make Syntax_all && cd .. && cd Completeness && cd sKL
  
wKL_compl :
	cd .. && cd wKL && make wKL_all && cd .. && cd sKL

sKH_completeness.vo: sKH_completeness.v K_Syntax.vo K_GHC.vo K_logics.vo K_extens_interactions.vo K_wKH_meta_interactions.vo K_sKH_meta_interactions.vo K_Kripke_sem.vo K_bisimulation.vo wKH_completeness.vo



clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../../../general && rm *.vo *.glob && cd ../Toolbox_ModLog/Completeness/sKL

clean_sKL : clean_coq 

clean_all : clean_general clean_sKL

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
