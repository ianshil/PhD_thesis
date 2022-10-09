%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../../general and ../Toolbox_ModLog/Syntax.
# Build those by "make general" and "make Syntax" in the current directory.

general :
	cd .. && cd .. && make general && cd Toolbox_ModLog/Generalized_Hilbert_calculi
  
Syntax :
	cd .. && cd Syntax && make Syntax_all && cd .. && cd Generalized_Hilbert_calculi

K_GHC.vo: K_GHC.v gen.vo K_Syntax.vo
K_logics.vo: K_logics.v K_Syntax.vo K_GHC.vo
K_extens_interactions.vo: K_extens_interactions.v K_Syntax.vo K_GHC.vo K_logics.vo
K_wKH_meta_interactions.vo: K_wKH_meta_interactions.v genT.vo K_Syntax.vo K_GHC.vo K_logics.vo K_extens_interactions.vo
K_sKH_meta_interactions.vo: K_sKH_meta_interactions.v K_Syntax.vo K_GHC.vo K_logics.vo K_extens_interactions.vo K_wKH_meta_interactions.vo
Generalized_Hilbert_calculi_all: K_GHC.vo K_logics.vo K_extens_interactions.vo K_wKH_meta_interactions.vo K_sKH_meta_interactions.vo



clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../../general && rm *.vo *.glob && cd ../Toolbox_ModLog/Generalized_Hilbert_calculi

clean_Generalized_Hilbert_calculi : clean_coq 

clean_all : clean_general clean_Generalized_Hilbert_calculi

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob

