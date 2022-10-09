%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../../Syntax.
# Build those by "make general" and "make Syntax" in the current directory.
  
Syntax :
	cd .. && cd .. && cd Syntax && make Syntax_all && cd .. && cd Kripke_semantics && cd Propositional

K_Kripke_sem.vo: K_Kripke_sem.v K_Syntax.vo
K_bisimulation.vo: K_bisimulation.v K_Syntax.vo K_Kripke_sem.vo
KSPropositional_all: K_Kripke_sem.vo K_bisimulation.vo


clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../../../general && rm *.vo *.glob && cd ../Toolbox_ModLog/Kripke_semantics/Propositional

clean_Propositional : clean_coq 

clean_all : clean_general clean_Propositional

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
