gen.vo: gen.v
existsT.vo: existsT.v
genT.vo: genT.v existsT.vo gen.vo
strong_induction.vo: strong_induction.v
Prop_Bi_Int_calcs.vo: Prop_Bi_Int_calcs.v gen.vo
Bi_Int_remove_list.vo: Bi_Int_remove_list.v existsT.vo Prop_Bi_Int_calcs.vo
Prop_Bi_Int_logics.vo: Prop_Bi_Int_logics.v Prop_Bi_Int_calcs.vo
Prop_Bi_Int_extens_interactions.vo: Prop_Bi_Int_extens_interactions.v Prop_Bi_Int_calcs.vo Prop_Bi_Int_logics.vo
Prop_wBi_Int_meta_interactions.vo: Prop_wBi_Int_meta_interactions.v genT.vo Prop_Bi_Int_calcs.vo Prop_Bi_Int_logics.vo Prop_Bi_Int_extens_interactions.vo
Prop_sBi_Int_meta_interactions.vo: Prop_sBi_Int_meta_interactions.v Prop_Bi_Int_calcs.vo Prop_Bi_Int_logics.vo Prop_Bi_Int_extens_interactions.vo Prop_wBi_Int_meta_interactions.vo
Prop_Bi_Int_Lindenbaum_lem.vo: Prop_Bi_Int_Lindenbaum_lem.v Prop_Bi_Int_calcs.vo Bi_Int_remove_list.vo Prop_Bi_Int_logics.vo Prop_Bi_Int_extens_interactions.vo Prop_wBi_Int_meta_interactions.vo Prop_sBi_Int_meta_interactions.vo strong_induction.vo
Prop_Bi_Int_Kripke_sem.vo: Prop_Bi_Int_Kripke_sem.v Prop_Bi_Int_calcs.vo
Prop_Bi_Int_bisimulation.vo: Prop_Bi_Int_bisimulation.v Prop_Bi_Int_calcs.vo Prop_Bi_Int_Kripke_sem.vo
Prop_Bi_Int_soundness.vo: Prop_Bi_Int_soundness.v Prop_Bi_Int_calcs.vo Prop_Bi_Int_Kripke_sem.vo
Prop_Bi_Int_wcompleteness.vo: Prop_Bi_Int_wcompleteness.v Prop_Bi_Int_calcs.vo Prop_Bi_Int_logics.vo Prop_Bi_Int_extens_interactions.vo Prop_wBi_Int_meta_interactions.vo Prop_sBi_Int_meta_interactions.vo Prop_Bi_Int_Lindenbaum_lem.vo Prop_Bi_Int_Kripke_sem.vo
Prop_Bi_Int_scompleteness.vo: Prop_Bi_Int_scompleteness.v Prop_Bi_Int_calcs.vo Prop_Bi_Int_logics.vo Prop_Bi_Int_extens_interactions.vo Prop_wBi_Int_meta_interactions.vo Prop_sBi_Int_meta_interactions.vo Prop_Bi_Int_Lindenbaum_lem.vo Prop_Bi_Int_Kripke_sem.vo Prop_Bi_Int_bisimulation.vo Prop_Bi_Int_wcompleteness.vo
Prop_Bi_Int_sem_look_back.vo: Prop_Bi_Int_sem_look_back.v Prop_Bi_Int_calcs.vo Prop_Bi_Int_logics.vo Prop_Bi_Int_extens_interactions.vo Prop_wBi_Int_meta_interactions.vo Prop_sBi_Int_meta_interactions.vo Prop_Bi_Int_Kripke_sem.vo Prop_Bi_Int_soundness.vo Prop_Bi_Int_wcompleteness.vo Prop_Bi_Int_scompleteness.vo


%.vo : %.v
	#echo doing $*.v >>log
	#dirname $* >>log
	(cd `dirname $*` ; pwd >> log ; coqc `basename $*.v`) 
	#pwd >> log
	# coqc -Q general "" -Q ll "" -Q modal "" -Q tense-lns "" $*.v

clean : 
	rm -rf  *.vo *.glob
