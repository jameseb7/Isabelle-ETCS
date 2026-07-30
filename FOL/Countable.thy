section \<open>Countable Sets\<close>

theory Countable
  imports Nats Axiom_Of_Choice Nat_Parity Cardinality
begin

text \<open>The definition below corresponds to Definition 2.6.9 in Halvorson.\<close>
definition epi_countable :: "cset \<Rightarrow> o" where
  "epi_countable(X) \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism(f))"

lemma emptyset_is_not_epi_countable:
  "\<not> epi_countable(\<emptyset>)"
proof
  assume "epi_countable(\<emptyset>)"
  then obtain f where f_type: "f : \<nat>\<^sub>c \<rightarrow> \<emptyset>" and f_epi: "epimorphism(f)"
    unfolding epi_countable_def by auto
  have fz_type: "f \<circ>\<^sub>c zero : \<one> \<rightarrow> \<emptyset>" using f_type zero_type comp_type by blast
  then show False using emptyset_is_empty by auto
qed

text \<open>The fact that the empty set is not countable according to the definition from Halvorson
  (@{thm epi_countable_def}) motivated the following definition.\<close>
definition countable :: "cset \<Rightarrow> o" where
  "countable(X) \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(f))"

lemma epi_countable_is_countable:
  assumes "epi_countable(X)"
  shows "countable(X)"
proof -
  obtain f where f_type: "f : \<nat>\<^sub>c \<rightarrow> X" and f_epi: "epimorphism(f)"
    using assms unfolding epi_countable_def by auto
  obtain g where g_type: "g : X \<rightarrow> \<nat>\<^sub>c" and g_mono: "monomorphism(g)" and g_eq: "f \<circ>\<^sub>c g = id(X)"
    using epis_give_monos[OF f_type f_epi] by auto
  show ?thesis unfolding countable_def using g_type g_mono by auto
qed

lemma emptyset_is_countable:
  "countable(\<emptyset>)"
proof -
  have "subobject_of(\<emptyset>, initial_func(\<nat>\<^sub>c), \<nat>\<^sub>c)" by (rule empty_subset)
  then have "initial_func(\<nat>\<^sub>c) : \<emptyset> \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(initial_func(\<nat>\<^sub>c))"
    unfolding subobject_of_def by auto
  then show ?thesis unfolding countable_def by auto
qed

lemma natural_numbers_are_countably_infinite:
  "countable(\<nat>\<^sub>c) \<and> is_infinite(\<nat>\<^sub>c)"
proof
  show "countable(\<nat>\<^sub>c)"
  proof -
    have id_mono: "monomorphism(id(\<nat>\<^sub>c))" using iso_imp_epi_and_monic[OF id_isomorphism] by (rule conjunct2)
    show ?thesis unfolding countable_def using id_type id_mono by auto
  qed
  show "is_infinite(\<nat>\<^sub>c)"
  proof -
    have peano: "injective(successor) \<and> \<not> surjective(successor)" by (rule Peano's_Axioms)
    have s_inj: "injective(successor)" using peano by (rule conjunct1)
    have s_mono: "monomorphism(successor)" using injective_imp_monomorphism[OF s_inj] .
    have s_not_surj: "\<not> surjective(successor)" using peano by (rule conjunct2)
    show ?thesis unfolding is_infinite_def using successor_type s_mono s_not_surj by auto
  qed
qed

lemma iso_to_N_is_countably_infinite:
  assumes "X \<cong> \<nat>\<^sub>c"
  shows "countable(X) \<and> is_infinite(X)"
proof -
  obtain f where f_type: "f : X \<rightarrow> \<nat>\<^sub>c" and f_iso: "isomorphism(f)"
    using assms unfolding is_isomorphic_def by auto
  have f_mono: "monomorphism(f)" using iso_imp_epi_and_monic[OF f_iso] by (rule conjunct2)
  have countable_X: "countable(X)" unfolding countable_def using f_type f_mono by auto
  have finv_type: "f\<^bold>\<inverse> : \<nat>\<^sub>c \<rightarrow> X" using inverse_type[OF f_iso f_type] .
  have finv_iso: "isomorphism(f\<^bold>\<inverse>)" using inv_iso[OF f_iso] .
  have finv_mono: "monomorphism(f\<^bold>\<inverse>)" using iso_imp_epi_and_monic[OF finv_iso] by (rule conjunct2)
  have le: "\<nat>\<^sub>c \<le>\<^sub>c X" unfolding is_smaller_than_def using finv_type finv_mono by auto
  have nat_inf: "is_infinite(\<nat>\<^sub>c)" using natural_numbers_are_countably_infinite by (rule conjunct2)
  have infinite_X: "is_infinite(X)" using larger_than_infinite_is_infinite[OF le nat_inf] .
  show ?thesis using countable_X infinite_X by auto
qed

lemma smaller_than_countable_is_countable:
  assumes "X \<le>\<^sub>c Y" and "countable(Y)"
  shows "countable(X)"
proof -
  obtain m where m_type: "m : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
    using assms(1) unfolding is_smaller_than_def by auto
  obtain g where g_type: "g : Y \<rightarrow> \<nat>\<^sub>c" and g_mono: "monomorphism(g)"
    using assms(2) unfolding countable_def by auto
  have cd: "codomain(m) = domain(g)" using m_type g_type unfolding cfunc_type_def by auto
  have gm_mono: "monomorphism(g \<circ>\<^sub>c m)" using composition_of_monic_pair_is_monic[OF cd m_mono g_mono] .
  have gm_type: "g \<circ>\<^sub>c m : X \<rightarrow> \<nat>\<^sub>c" using m_type g_type comp_type by blast
  show ?thesis unfolding countable_def using gm_type gm_mono by auto
qed

lemma iso_pres_countable:
  assumes "X \<cong> Y" and "countable(Y)"
  shows "countable(X)"
proof -
  obtain f where f_type: "f : X \<rightarrow> Y" and f_iso: "isomorphism(f)"
    using assms(1) unfolding is_isomorphic_def by auto
  have f_mono: "monomorphism(f)" using iso_imp_epi_and_monic[OF f_iso] by (rule conjunct2)
  have le: "X \<le>\<^sub>c Y" unfolding is_smaller_than_def using f_type f_mono by auto
  show ?thesis using smaller_than_countable_is_countable[OF le assms(2)] .
qed

lemma NuN_is_countable:
  "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
proof -
  have hwp_iso: "isomorphism(halve_with_parity)" by (rule halve_with_parity_iso)
  have hwp_type: "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by (rule halve_with_parity_type)
  have inv_type: "halve_with_parity\<^bold>\<inverse> : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" using inverse_type[OF hwp_iso hwp_type] .
  have inv_iso2: "isomorphism(halve_with_parity\<^bold>\<inverse>)" using inv_iso[OF hwp_iso] .
  have inv_mono: "monomorphism(halve_with_parity\<^bold>\<inverse>)" using iso_imp_epi_and_monic[OF inv_iso2] by (rule conjunct2)
  show ?thesis unfolding countable_def using inv_type inv_mono by auto
qed

text \<open>The lemma below corresponds to Exercise 2.6.11 in Halvorson.\<close>
lemma coproduct_of_countables_is_countable:
  assumes "countable(X)" and "countable(Y)"
  shows "countable(X \<Coprod> Y)"
proof -
  obtain x where x_type: "x : X \<rightarrow> \<nat>\<^sub>c" and x_mono: "monomorphism(x)"
    using assms(1) unfolding countable_def by auto
  obtain y where y_type: "y : Y \<rightarrow> \<nat>\<^sub>c" and y_mono: "monomorphism(y)"
    using assms(2) unfolding countable_def by auto
  obtain n where n_type: "n : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and n_mono: "monomorphism(n)"
    using NuN_is_countable unfolding countable_def by auto
  have x_inj: "injective(x)" using monomorphism_imp_injective[OF x_mono] .
  have y_inj: "injective(y)" using monomorphism_imp_injective[OF y_mono] .
  have xy_type: "x \<bowtie>\<^sub>f y : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" using cfunc_bowtie_prod_type[OF x_type y_type] .
  have xy_inj: "injective(x \<bowtie>\<^sub>f y)" using cfunc_bowtieprod_inj[OF x_type y_type x_inj y_inj] .
  have xy_mono: "monomorphism(x \<bowtie>\<^sub>f y)" using injective_imp_monomorphism[OF xy_inj] .
  have cd: "codomain(x \<bowtie>\<^sub>f y) = domain(n)" using xy_type n_type unfolding cfunc_type_def by auto
  have nxy_mono: "monomorphism(n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y))" using composition_of_monic_pair_is_monic[OF cd xy_mono n_mono] .
  have nxy_type: "n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y) : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c" using xy_type n_type comp_type by blast
  show ?thesis unfolding countable_def using nxy_type nxy_mono by auto
qed

end
