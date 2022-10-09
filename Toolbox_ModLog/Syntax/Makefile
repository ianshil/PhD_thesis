%.vo : %.v
	coqc $*.v

K_Syntax.vo: K_Syntax.v
K_FO_Syntax.vo: K_FO_Syntax.v
Syntax_all: K_Syntax.vo K_FO_Syntax.vo

clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../../general && rm *.vo *.glob && cd ../Toolbox_ModLog/Syntax

clean_Syntax : clean_coq 

clean_all : clean_general clean_Syntax

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
