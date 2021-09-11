theory ETCS_Choice
  imports ETCS_Nat
begin

section \<open>Axiom 11: Axiom of Choice\<close>

definition section_of :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" (infix "sectionof" 90)
  where "s sectionof f \<longleftrightarrow> s : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c s = id (codomain(f))"

(*Definition 2.7.1*)
definition split_epimorphism :: "cfunc \<Rightarrow> bool"
  where "split_epimorphism(f)\<longleftrightarrow>(\<exists> s. f \<circ>\<^sub>c s = id (codomain f))"

axiomatization
  where
  axiom_of_choice :"epimorphism(f) \<longrightarrow> (\<exists> g . g sectionof f)"


lemma epis_give_monos:  
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_epi: "epimorphism(f)"
  shows "\<exists>g. (g: Y \<rightarrow> X \<and> monomorphism(g) )"
  using assms  
  by (typecheck_cfuncs_prems, metis axiom_of_choice cfunc_type_def comp_monic_imp_monic f_epi id_isomorphism iso_imp_epi_and_monic section_of_def)


lemma monos_give_epis:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_mono: "monomorphism(f)"
  shows "\<exists>g. (g: Y \<rightarrow> X \<and> epimorphism(g) )"
  using assms apply typecheck_cfuncs
  oops


end