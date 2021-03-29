theory ETCS_Choice
  imports ETCS_Nat
begin

section \<open>Axiom 11: Axiom of Choice\<close>

definition section_of :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" (infix "sectionof" 90)
  where "s sectionof f \<longleftrightarrow> s : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c s = id (codomain(f))"

definition split_epimorphism :: "cfunc \<Rightarrow> bool"
  where "split_epimorphism(f)\<longleftrightarrow>(\<exists> s. f \<circ>\<^sub>c s = id (codomain f))"

axiomatization
  where
  axiom_of_choice :"epimorphism(f) \<longrightarrow> (\<exists> g . g sectionof f)"

end