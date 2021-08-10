theory Countable
  imports ETCS_Axioms
begin

(* Definition 2.6.9 *)
definition epi_countable :: "cset \<Rightarrow> bool" where
  "epi_countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

lemma emptyset_is_not_epi_countable:
  "\<not> (epi_countable \<emptyset>)"
  using comp_type emptyset_is_empty epi_countable_def zero_type by blast


(* Definition 2.6.9 *)
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f)"



lemma emptyset_is_countable:
  "countable \<emptyset>"
  using countable_def empty_subset subobject_of_def2 by blast

lemma natural_numbers_are_countably_infinite:
  "(countable \<nat>\<^sub>c) \<and> (is_infinite \<nat>\<^sub>c)"
  by (meson CollectI Peano's_Axioms countable_def injective_imp_monomorphism is_infinite_def successor_type)


lemma smaller_than_countable_is_countable:
  assumes "X \<le>\<^sub>c Y" "countable Y"
  shows "countable X"
  by (smt assms cfunc_type_def comp_type composition_of_monic_pair_is_monic countable_def is_smaller_than_def)


lemma product_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  assumes "nonempty(X)" "nonempty(Y)"
  shows "is_finite(X \<times>\<^sub>c Y)"
  unfolding is_finite_def
proof-  
  fix xy
  assume xy_type: "xy:  X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c Y"
  assume xy_mono: "monomorphism(xy)"
  obtain m where m_def: "m :  X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism(m)"
    using assms(4) is_smaller_than_def smaller_than_product1 by blast
  obtain n where n_def: "n :  Y \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism(n)"
    using assms(3) is_smaller_than_def smaller_than_product2 by blast
  oops




lemma coproduct_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  shows "is_finite(X \<Coprod>  Y)"
  unfolding is_finite_def
  oops


lemma NxN_is_countable:
  "countable(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
  oops


(*Once we have this  result above we can generalize it to any countable sets*)
lemma product_of_countables_is_countable:
  assumes "countable X" "countable Y"
  assumes NxN_is_countable: "countable(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)" (*DELETE later*)
  shows "countable(X \<times>\<^sub>c Y)"
proof - 
  have "\<exists>f. f: X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(f)"
    using assms(1) countable_def by blast
  then obtain f where f_def: "f: X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(f)"
    by blast
  have "\<exists>g. g: Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(g)"
    using assms(2) countable_def by blast
  then obtain g where g_def: "g: Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(g)"
    by blast
  then have fg_type: "(f \<times>\<^sub>f g) : (X \<times>\<^sub>c Y) \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_cross_prod_type f_def)
  have fg_mono: "monomorphism(f \<times>\<^sub>f g)"
    using cfunc_cross_prod_mono f_def g_def by blast
  obtain \<phi> where \<phi>_def: "(\<phi> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c) \<and> monomorphism(\<phi>)"
    using NxN_is_countable countable_def by blast
  have "(\<phi> \<circ>\<^sub>c (f \<times>\<^sub>f g) : (X \<times>\<^sub>c Y) \<rightarrow> \<nat>\<^sub>c) \<and> monomorphism(\<phi> \<circ>\<^sub>c (f \<times>\<^sub>f g))"
    using \<phi>_def cfunc_type_def comp_type composition_of_monic_pair_is_monic fg_mono fg_type by auto
  then show "countable(X \<times>\<^sub>c Y)"
    using countable_def by blast
qed

      


lemma NuN_is_countable:
  "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  unfolding countable_def
  oops


(*Exercise 2.6.11*)
lemma coproduct_of_countables_is_countable:
  assumes "countable X" "countable Y"
  assumes NuN_is_countable: "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  shows "countable(X \<Coprod> Y)"
  unfolding countable_def
proof-
  obtain x where x_def:  "x : X  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism x"
    using assms(1) countable_def by blast
  obtain y where y_def:  "y : Y  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism y"
    using assms(2) countable_def by blast
  obtain n where n_def: " n : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> monomorphism n"
    using NuN_is_countable countable_def by blast
  have xy_type: "x \<bowtie>\<^sub>f y : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    using x_def y_def by (typecheck_cfuncs, auto)
  then have nxy_type: "n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y) : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c"
    using comp_type n_def by blast
  have "injective(x \<bowtie>\<^sub>f y)"
    using cfunc_bowtieprod_inj monomorphism_imp_injective x_def y_def by blast
  then have "monomorphism(x \<bowtie>\<^sub>f y)"
    using injective_imp_monomorphism by auto
  then have "monomorphism(n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y))"
    using cfunc_type_def composition_of_monic_pair_is_monic n_def xy_type by auto
  then show "\<exists>f. f : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f"
    using nxy_type by blast
qed

    
  
  


lemma finite_is_countable: 
  assumes "is_finite X"
  shows "countable X"
  oops

end