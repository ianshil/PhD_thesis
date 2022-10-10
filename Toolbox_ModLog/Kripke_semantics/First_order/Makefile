%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../../Syntax.
# Build those by "make Syntax" in the current directory.
  
Syntax :
	cd .. && cd .. && cd Syntax && make Syntax_all && cd .. && cd Kripke_semantics && cd First_order

K_FO_Kripke_sem.vo: K_FO_Kripke_sem.v K_FO_Syntax.vo


clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../../../general && rm *.vo *.glob && cd ../Toolbox_ModLog/Kripke_semantics/First_order

clean_First_order : clean_coq 

clean_all : clean_general clean_First_order

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
