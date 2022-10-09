%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../Generalized_Hilbert_calculi and ../Kripke_semantics/Propositional and ../Syntax.
# Build those by "make Generalized_Hilbert_calculi" and "make KSPropositional" and "make Syntax" in the current directory.

Generalized_Hilbert_calculi :
	cd .. && cd Generalized_Hilbert_calculi && make Generalized_Hilbert_calculi_all && cd .. && cd Soundness
  
KSPropositional :
	cd .. && cd Kripke_semantics && cd Propositional && make KSPropositional_all && cd .. && cd .. && cd Soundness

Syntax :
	cd .. && cd Syntax && make Syntax_all && cd .. && cd Generalized_Hilbert_calculi

wKH_sKH_soundness.vo: wKH_sKH_soundness.v K_Syntax.vo K_Kripke_sem.vo



clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../../general && rm *.vo *.glob && cd ../Toolbox_ModLog/Soundness

clean_Soundness : clean_coq 

clean_all : clean_general clean_Soundness

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
