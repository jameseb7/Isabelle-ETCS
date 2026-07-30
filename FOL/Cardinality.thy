section \<open>Cardinality and Finiteness\<close>

theory Cardinality
  imports Exponential_Objects
begin

text \<open>The definitions below correspond to Definition 2.6.1 in Halvorson.\<close>
definition is_finite :: "cset \<Rightarrow> o" where
   "is_finite(X) \<longleftrightarrow> (\<forall>m. (m : X \<rightarrow> X \<and> monomorphism(m)) \<longrightarrow> isomorphism(m))"

definition is_infinite :: "cset \<Rightarrow> o" where
   "is_infinite(X) \<longleftrightarrow> (\<exists>m. m : X \<rightarrow> X \<and> monomorphism(m) \<and> \<not>surjective(m))"

lemma either_finite_or_infinite:
  "is_finite(X) \<or> is_infinite(X)"
proof (rule ccontr)
  assume "\<not> (is_finite(X) \<or> is_infinite(X))"
  then have not_fin: "\<not> is_finite(X)" and not_inf: "\<not> is_infinite(X)" by auto
  from not_fin obtain m where m_type: "m : X \<rightarrow> X" and m_mono: "monomorphism(m)"
      and m_not_iso: "\<not> isomorphism(m)"
    unfolding is_finite_def by auto
  have m_surj: "surjective(m)"
  proof (rule ccontr)
    assume "\<not> surjective(m)"
    then have "is_infinite(X)" unfolding is_infinite_def using m_type m_mono by auto
    then show False using not_inf by auto
  qed
  have "epimorphism(m)" using m_surj m_type surjective_is_epimorphism by auto
  then have "isomorphism(m)" using epi_mon_is_iso m_mono by auto
  then show False using m_not_iso by auto
qed

text \<open>The definition below corresponds to Definition 2.6.2 in Halvorson.\<close>
definition is_smaller_than :: "cset \<Rightarrow> cset \<Rightarrow> o" (infix "\<le>\<^sub>c" 50) where
   "X \<le>\<^sub>c Y \<longleftrightarrow> (\<exists>m. m : X \<rightarrow> Y \<and> monomorphism(m))"

text \<open>The purpose of the following lemma is simply to unify the two notations used in the book.\<close>
lemma subobject_iff_smaller_than:
  "(X \<le>\<^sub>c Y) \<longleftrightarrow> (\<exists>m. subobject_of(X, m, Y))"
  unfolding is_smaller_than_def subobject_of_def by auto

lemma set_card_transitive:
  assumes "A \<le>\<^sub>c B"
  assumes "B \<le>\<^sub>c C"
  shows   "A \<le>\<^sub>c C"
proof -
  obtain m where m_type[type_rule]: "m : A \<rightarrow> B" and m_mono: "monomorphism(m)"
    using assms(1) is_smaller_than_def by auto
  obtain n where n_type[type_rule]: "n : B \<rightarrow> C" and n_mono: "monomorphism(n)"
    using assms(2) is_smaller_than_def by auto
  have nm_type: "n \<circ>\<^sub>c m : A \<rightarrow> C"
    by typecheck_cfuncs
  have cod_dom: "codomain(m) = domain(n)"
    using m_type n_type unfolding cfunc_type_def by auto
  have nm_mono: "monomorphism(n \<circ>\<^sub>c m)"
    using composition_of_monic_pair_is_monic[OF cod_dom m_mono n_mono] .
  show "A \<le>\<^sub>c C"
    unfolding is_smaller_than_def using nm_type nm_mono by auto
qed

lemma all_emptysets_are_finite:
  assumes "is_empty(X)"
  shows "is_finite(X)"
  unfolding is_finite_def
proof (clarify)
  fix m
  assume m_type: "m : X \<rightarrow> X"
  assume m_mono: "monomorphism(m)"
  have vacuous: "\<And>f g. f : X \<rightarrow> X \<Longrightarrow> g : X \<rightarrow> X \<Longrightarrow> f = g"
  proof -
    fix f g
    assume f_type: "f : X \<rightarrow> X"
    assume g_type: "g : X \<rightarrow> X"
    show "f = g"
    proof (rule one_separator[OF f_type g_type])
      fix x
      assume "x : \<one> \<rightarrow> X"
      then have "x \<in>\<^sub>c X" by auto
      then have False using assms is_empty_def by auto
      then show "f \<circ>\<^sub>c x = g \<circ>\<^sub>c x" by auto
    qed
  qed
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have m_id: "m \<circ>\<^sub>c id(X) = id(X)"
    by (rule vacuous[OF comp_type[OF idX_type m_type] idX_type])
  have id_m: "id(X) \<circ>\<^sub>c m = id(X)"
    by (rule vacuous[OF comp_type[OF m_type idX_type] idX_type])
  show "isomorphism(m)"
    unfolding isomorphism_def3[OF m_type]
    using idX_type id_m m_id by auto
qed

lemma emptyset_is_smallest_set:
  "\<emptyset> \<le>\<^sub>c X"
  unfolding is_smaller_than_def
  using empty_subset unfolding subobject_of_def by auto

text \<open>The lemma below corresponds to Proposition 2.6.3's degenerate case: \<Omega> has no
  monic self-map that fails to be surjective, hence \<Omega> is finite.\<close>
lemma truth_set_is_finite:
  "is_finite(\<Omega>)"
  unfolding is_finite_def
proof (clarify)
  fix m
  assume m_type[type_rule]: "m : \<Omega> \<rightarrow> \<Omega>"
  assume m_mono: "monomorphism(m)"
  have "surjective(m)"
    unfolding surjective_def
  proof (clarify)
    fix y
    assume "y \<in>\<^sub>c codomain(m)"
    then have y_type[type_rule]: "y \<in>\<^sub>c \<Omega>"
      using cfunc_type_def m_type by auto
    have cases: "y = \<t> \<or> y = \<f>"
      using true_false_only_truth_values y_type by auto
    have m_inj: "injective(m)"
      using m_mono m_type monomorphism_imp_injective by auto
    have mt_type[type_rule]: "m \<circ>\<^sub>c \<t> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have mf_type[type_rule]: "m \<circ>\<^sub>c \<f> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have mt_mf_distinct: "m \<circ>\<^sub>c \<t> \<noteq> m \<circ>\<^sub>c \<f>"
    proof
      assume "m \<circ>\<^sub>c \<t> = m \<circ>\<^sub>c \<f>"
      then have "\<t> = \<f>"
        using injective_def2[OF m_type] m_inj true_func_type false_func_type by auto
      then show False using true_false_distinct by auto
    qed
    have mt_cases: "m \<circ>\<^sub>c \<t> = \<t> \<or> m \<circ>\<^sub>c \<t> = \<f>"
      using true_false_only_truth_values mt_type by auto
    have mf_cases: "m \<circ>\<^sub>c \<f> = \<t> \<or> m \<circ>\<^sub>c \<f> = \<f>"
      using true_false_only_truth_values mf_type by auto
    have both_cases: "(m \<circ>\<^sub>c \<t> = \<t> \<and> m \<circ>\<^sub>c \<f> = \<f>) \<or> (m \<circ>\<^sub>c \<t> = \<f> \<and> m \<circ>\<^sub>c \<f> = \<t>)"
      using mt_mf_distinct mt_cases mf_cases by auto
    have exists_witness: "\<exists>x. x \<in>\<^sub>c \<Omega> \<and> m \<circ>\<^sub>c x = y"
      using cases both_cases true_func_type false_func_type by auto
    then obtain x where x_type: "x \<in>\<^sub>c \<Omega>" and mx_eq: "m \<circ>\<^sub>c x = y"
      by auto
    show "\<exists>x. x \<in>\<^sub>c domain(m) \<and> m \<circ>\<^sub>c x = y"
      using x_type mx_eq m_type cfunc_type_def by auto
  qed
  then show "isomorphism(m)"
    by (simp add: epi_mon_is_iso m_mono surjective_is_epimorphism)
qed

lemma smaller_than_finite_is_finite:
  assumes "X \<le>\<^sub>c Y" "is_finite(Y)"
  shows "is_finite(X)"
  unfolding is_finite_def
proof (clarify)
  fix x
  assume x_type[type_rule]: "x : X \<rightarrow> X"
  assume x_mono: "monomorphism(x)"

  obtain m where m_type[type_rule]: "m : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
    using assms(1) is_smaller_than_def by auto

  have idc_type[type_rule]: "id(set_subtraction(m)) : set_subtraction(m) \<rightarrow> set_subtraction(m)"
    by (rule id_type)
  have bowtie_type[type_rule]: "x \<bowtie>\<^sub>f id(set_subtraction(m)) : X \<Coprod> set_subtraction(m) \<rightarrow> X \<Coprod> set_subtraction(m)"
    by typecheck_cfuncs
  have tc_type[type_rule]: "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)"
    using m_mono m_type by typecheck_cfuncs
  have is_type[type_rule]: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y"
    using m_mono m_type by typecheck_cfuncs

  define \<phi> where \<phi>_def: "\<phi> = into_super(m) \<circ>\<^sub>c (x \<bowtie>\<^sub>f id(set_subtraction(m))) \<circ>\<^sub>c try_cast(m)"
  have \<phi>_type: "\<phi> : Y \<rightarrow> Y"
    unfolding \<phi>_def by typecheck_cfuncs

  have x_inj: "injective(x)"
    using x_mono monomorphism_imp_injective by auto
  have id_inj: "injective(id(set_subtraction(m)))"
    using id_isomorphism iso_imp_epi_and_monic monomorphism_imp_injective by auto
  have bowtie_inj: "injective(x \<bowtie>\<^sub>f id(set_subtraction(m)))"
    using cfunc_bowtieprod_inj[OF x_type idc_type x_inj id_inj] by simp
  have mono1: "monomorphism(x \<bowtie>\<^sub>f id(set_subtraction(m)))"
    using bowtie_inj injective_imp_monomorphism by auto
  have mono2: "monomorphism(try_cast(m))"
    using m_mono m_type try_cast_mono by auto
  have cd1: "codomain(try_cast(m)) = domain(x \<bowtie>\<^sub>f id(set_subtraction(m)))"
    using bowtie_type tc_type unfolding cfunc_type_def by auto
  have mono3: "monomorphism((x \<bowtie>\<^sub>f id(set_subtraction(m))) \<circ>\<^sub>c try_cast(m))"
    using composition_of_monic_pair_is_monic[OF cd1 mono2 mono1] .
  have comp1_type: "(x \<bowtie>\<^sub>f id(set_subtraction(m))) \<circ>\<^sub>c try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)"
    by (rule comp_type[OF tc_type bowtie_type])
  have cd2: "codomain((x \<bowtie>\<^sub>f id(set_subtraction(m))) \<circ>\<^sub>c try_cast(m)) = domain(into_super(m))"
    using comp1_type is_type unfolding cfunc_type_def by auto
  have \<phi>_mono: "monomorphism(\<phi>)"
    unfolding \<phi>_def
    using composition_of_monic_pair_is_monic[OF cd2 mono3 into_super_mono[OF m_mono m_type]] .
  have \<phi>_iso: "isomorphism(\<phi>)"
    using \<phi>_type \<phi>_mono assms(2) is_finite_def by auto

  have is_iso: "isomorphism(into_super(m))"
    using into_super_iso[OF m_mono m_type] .
  have tc_iso: "isomorphism(try_cast(m))"
    using inv_iso[OF is_iso] unfolding try_cast_def .

  have iso_x_bowtie_id: "isomorphism(x \<bowtie>\<^sub>f id(set_subtraction(m)))"
    using isomorphism_sandwich[OF tc_type bowtie_type is_type tc_iso is_iso] \<phi>_iso
    unfolding \<phi>_def by auto

  have bowtie_epi: "epimorphism(x \<bowtie>\<^sub>f id(set_subtraction(m)))"
    using iso_imp_epi_and_monic iso_x_bowtie_id by auto
  have bowtie_surj: "surjective(x \<bowtie>\<^sub>f id(set_subtraction(m)))"
    using epi_is_surj[OF bowtie_type bowtie_epi] .
  have "surjective(x) \<and> surjective(id(set_subtraction(m)))"
    using cfunc_bowtieprod_surj_converse[OF x_type idc_type bowtie_surj] .
  then have x_surj: "surjective(x)" by auto
  then have "epimorphism(x)"
    using x_type surjective_is_epimorphism by auto
  then show "isomorphism(x)"
    using epi_mon_is_iso x_mono by auto
qed

lemma larger_than_infinite_is_infinite:
  assumes "X \<le>\<^sub>c Y" "is_infinite(X)"
  shows "is_infinite(Y)"
proof (rule ccontr)
  assume "\<not> is_infinite(Y)"
  then have "is_finite(Y)"
    using either_finite_or_infinite by auto
  then have "is_finite(X)"
    using assms(1) smaller_than_finite_is_finite by auto
  then obtain m where m_type: "m : X \<rightarrow> X" and m_mono: "monomorphism(m)"
      and m_not_surj: "\<not> surjective(m)"
    using assms(2) unfolding is_infinite_def by auto
  have "isomorphism(m)"
    using \<open>is_finite(X)\<close> m_type m_mono unfolding is_finite_def by auto
  then have "surjective(m)"
    using iso_imp_epi_and_monic epi_is_surj m_type by auto
  then show False using m_not_surj by auto
qed

lemma iso_pres_finite:
  assumes "X \<cong> Y"
  assumes "is_finite(X)"
  shows "is_finite(Y)"
proof -
  have "Y \<cong> X" using assms(1) isomorphic_is_symmetric by auto
  then obtain \<psi> where \<psi>_type: "\<psi> : Y \<rightarrow> X" and \<psi>_iso: "isomorphism(\<psi>)"
    using is_isomorphic_def by auto
  have "Y \<le>\<^sub>c X"
    unfolding is_smaller_than_def using \<psi>_type \<psi>_iso iso_imp_epi_and_monic by auto
  then show "is_finite(Y)"
    using assms(2) smaller_than_finite_is_finite by auto
qed

lemma not_finite_and_infinite:
  "\<not>(is_finite(X) \<and> is_infinite(X))"
proof
  assume "is_finite(X) \<and> is_infinite(X)"
  then have fin: "is_finite(X)" and inf: "is_infinite(X)" by auto
  obtain m where m_type: "m : X \<rightarrow> X" and m_mono: "monomorphism(m)" and m_not_surj: "\<not> surjective(m)"
    using inf unfolding is_infinite_def by auto
  have "isomorphism(m)" using fin m_type m_mono unfolding is_finite_def by auto
  then have "surjective(m)" using iso_imp_epi_and_monic epi_is_surj m_type by auto
  then show False using m_not_surj by auto
qed

lemma iso_pres_infinite:
  assumes "X \<cong> Y"
  assumes "is_infinite(X)"
  shows "is_infinite(Y)"
proof (rule ccontr)
  assume "\<not> is_infinite(Y)"
  then have "is_finite(Y)"
    using either_finite_or_infinite by auto
  then have "is_finite(X)"
    using assms(1) isomorphic_is_symmetric iso_pres_finite by auto
  then show False using assms(2) not_finite_and_infinite by auto
qed

lemma size_2_sets:
  "(X \<cong> \<Omega>) \<longleftrightarrow> (\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2))"
proof
  assume "X \<cong> \<Omega>"
  then obtain \<phi> where \<phi>_type[type_rule]: "\<phi> : X \<rightarrow> \<Omega>" and \<phi>_iso: "isomorphism(\<phi>)"
    using is_isomorphic_def by auto
  obtain \<phi>inv where \<phi>inv_type[type_rule]: "\<phi>inv : \<Omega> \<rightarrow> X"
      and \<phi>inv_\<phi>: "\<phi>inv \<circ>\<^sub>c \<phi> = id(X)" and \<phi>_\<phi>inv: "\<phi> \<circ>\<^sub>c \<phi>inv = id(\<Omega>)"
    using isomorphism_def3[OF \<phi>_type] \<phi>_iso by auto
  have \<phi>_mono: "monomorphism(\<phi>)"
    using \<phi>_iso iso_imp_epi_and_monic by auto
  have \<phi>_inj: "injective(\<phi>)"
    using \<phi>_mono monomorphism_imp_injective by auto
  define x1 where x1_def: "x1 = \<phi>inv \<circ>\<^sub>c \<t>"
  define x2 where x2_def: "x2 = \<phi>inv \<circ>\<^sub>c \<f>"
  have x1_type[type_rule]: "x1 \<in>\<^sub>c X" unfolding x1_def by typecheck_cfuncs
  have x2_type[type_rule]: "x2 \<in>\<^sub>c X" unfolding x2_def by typecheck_cfuncs
  have phi_x1: "\<phi> \<circ>\<^sub>c x1 = \<t>"
  proof -
    have "\<phi> \<circ>\<^sub>c x1 = \<phi> \<circ>\<^sub>c (\<phi>inv \<circ>\<^sub>c \<t>)" by (simp add: x1_def)
    also have "... = (\<phi> \<circ>\<^sub>c \<phi>inv) \<circ>\<^sub>c \<t>" by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = id(\<Omega>) \<circ>\<^sub>c \<t>" by (simp add: \<phi>_\<phi>inv)
    also have "... = \<t>" by (typecheck_cfuncs, simp add: id_left_unit2)
    finally show ?thesis .
  qed
  have phi_x2: "\<phi> \<circ>\<^sub>c x2 = \<f>"
  proof -
    have "\<phi> \<circ>\<^sub>c x2 = \<phi> \<circ>\<^sub>c (\<phi>inv \<circ>\<^sub>c \<f>)" by (simp add: x2_def)
    also have "... = (\<phi> \<circ>\<^sub>c \<phi>inv) \<circ>\<^sub>c \<f>" by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = id(\<Omega>) \<circ>\<^sub>c \<f>" by (simp add: \<phi>_\<phi>inv)
    also have "... = \<f>" by (typecheck_cfuncs, simp add: id_left_unit2)
    finally show ?thesis .
  qed
  have distinct: "x1 \<noteq> x2"
  proof
    assume "x1 = x2"
    then have "\<t> = \<f>" using phi_x1 phi_x2 by auto
    then show False using true_false_distinct by auto
  qed
  have every_x: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2"
  proof (intro allI impI)
    fix x assume x_type[type_rule]: "x \<in>\<^sub>c X"
    have phi_x_type: "\<phi> \<circ>\<^sub>c x \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have "\<phi> \<circ>\<^sub>c x = \<f> \<or> \<phi> \<circ>\<^sub>c x = \<t>"
      using true_false_only_truth_values[OF phi_x_type] .
    then show "x = x1 \<or> x = x2"
    proof (elim disjE)
      assume "\<phi> \<circ>\<^sub>c x = \<f>"
      then have "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c x2" using phi_x2 by auto
      then have "x = x2"
        using iffD1[OF injective_def2[OF \<phi>_type] \<phi>_inj, rule_format, where x=x and y=x2]
        by (typecheck_cfuncs, auto)
      then show ?thesis by auto
    next
      assume "\<phi> \<circ>\<^sub>c x = \<t>"
      then have "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c x1" using phi_x1 by auto
      then have "x = x1"
        using iffD1[OF injective_def2[OF \<phi>_type] \<phi>_inj, rule_format, where x=x and y=x1]
        by (typecheck_cfuncs, auto)
      then show ?thesis by auto
    qed
  qed
  show "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2)"
    using x1_type x2_type distinct every_x by auto
next
  assume exactly_two: "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2)"
  then obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X"
      and distinct: "x1 \<noteq> x2" and cover: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2"
    by auto
  have iso_type: "(x1 \<amalg> x2) \<circ>\<^sub>c case_bool : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have surj: "surjective((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    unfolding surjective_def2[OF iso_type]
  proof (intro allI impI)
    fix y assume y_type[type_rule]: "y \<in>\<^sub>c X"
    have "y = x1 \<or> y = x2" using cover y_type by auto
    then show "\<exists>x. x \<in>\<^sub>c \<Omega> \<and> ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c x = y"
    proof
      assume "y = x1"
      then show ?thesis using coprod_case_bool_true[OF x1_type x2_type] true_func_type by auto
    next
      assume "y = x2"
      then show ?thesis using coprod_case_bool_false[OF x1_type x2_type] false_func_type by auto
    qed
  qed
  have inj: "injective((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    unfolding injective_def2[OF iso_type]
  proof (clarify)
    fix a b
    assume a_type[type_rule]: "a \<in>\<^sub>c \<Omega>" and b_type[type_rule]: "b \<in>\<^sub>c \<Omega>"
    assume eq: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c a = ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c b"
    have cases_a: "a = \<t> \<or> a = \<f>" using true_false_only_truth_values a_type by auto
    have cases_b: "b = \<t> \<or> b = \<f>" using true_false_only_truth_values b_type by auto
    show "a = b"
    proof (rule disjE[OF cases_a])
      assume a_t: "a = \<t>"
      show "a = b"
      proof (rule disjE[OF cases_b])
        assume "b = \<t>"
        then show "a = b" using a_t by auto
      next
        assume "b = \<f>"
        have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c a = x1"
          using a_t coprod_case_bool_true[OF x1_type x2_type] by auto
        moreover have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c b = x2"
          using \<open>b = \<f>\<close> coprod_case_bool_false[OF x1_type x2_type] by auto
        ultimately have "x1 = x2" using eq by auto
        then show "a = b" using distinct by auto
      qed
    next
      assume a_f: "a = \<f>"
      show "a = b"
      proof (rule disjE[OF cases_b])
        assume "b = \<t>"
        have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c a = x2"
          using a_f coprod_case_bool_false[OF x1_type x2_type] by auto
        moreover have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c b = x1"
          using \<open>b = \<t>\<close> coprod_case_bool_true[OF x1_type x2_type] by auto
        ultimately have "x2 = x1" using eq by auto
        then show "a = b" using distinct by auto
      next
        assume "b = \<f>"
        then show "a = b" using a_f by auto
      qed
    qed
  qed
  then have "monomorphism((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    using injective_imp_monomorphism by auto
  then have "isomorphism((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    using surj epi_mon_is_iso iso_type surjective_is_epimorphism by auto
  then have "\<Omega> \<cong> X"
    using iso_type is_isomorphic_def by auto
  then show "X \<cong> \<Omega>"
    using isomorphic_is_symmetric by auto
qed

lemma size_2plus_sets:
  "(\<Omega> \<le>\<^sub>c X) \<longleftrightarrow> (\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2)"
proof
  assume "\<Omega> \<le>\<^sub>c X"
  then obtain m where m_type[type_rule]: "m : \<Omega> \<rightarrow> X" and m_mono: "monomorphism(m)"
    using is_smaller_than_def by auto
  have "m \<circ>\<^sub>c \<t> \<noteq> m \<circ>\<^sub>c \<f>"
  proof
    assume "m \<circ>\<^sub>c \<t> = m \<circ>\<^sub>c \<f>"
    then have "\<t> = \<f>"
      using injective_def2[OF m_type] m_mono monomorphism_imp_injective true_func_type false_func_type by auto
    then show False using true_false_distinct by auto
  qed
  then show "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2"
    using comp_type[OF true_func_type m_type] comp_type[OF false_func_type m_type] by auto
next
  assume "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2"
  then obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X"
      and distinct: "x1 \<noteq> x2"
    by auto
  have mono_type[type_rule]: "(x1 \<amalg> x2) \<circ>\<^sub>c case_bool : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have inj: "injective((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    unfolding injective_def2[OF mono_type]
  proof (clarify)
    fix a b
    assume a_type[type_rule]: "a \<in>\<^sub>c \<Omega>" and b_type[type_rule]: "b \<in>\<^sub>c \<Omega>"
    assume eq: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c a = ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c b"
    have cases_a: "a = \<t> \<or> a = \<f>" using true_false_only_truth_values a_type by auto
    have cases_b: "b = \<t> \<or> b = \<f>" using true_false_only_truth_values b_type by auto
    show "a = b"
    proof (rule disjE[OF cases_a])
      assume a_t: "a = \<t>"
      show "a = b"
      proof (rule disjE[OF cases_b])
        assume "b = \<t>"
        then show "a = b" using a_t by auto
      next
        assume "b = \<f>"
        have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c a = x1"
          using a_t coprod_case_bool_true[OF x1_type x2_type] by auto
        moreover have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c b = x2"
          using \<open>b = \<f>\<close> coprod_case_bool_false[OF x1_type x2_type] by auto
        ultimately have "x1 = x2" using eq by auto
        then show "a = b" using distinct by auto
      qed
    next
      assume a_f: "a = \<f>"
      show "a = b"
      proof (rule disjE[OF cases_b])
        assume "b = \<t>"
        have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c a = x2"
          using a_f coprod_case_bool_false[OF x1_type x2_type] by auto
        moreover have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c b = x1"
          using \<open>b = \<t>\<close> coprod_case_bool_true[OF x1_type x2_type] by auto
        ultimately have "x2 = x1" using eq by auto
        then show "a = b" using distinct by auto
      next
        assume "b = \<f>"
        then show "a = b" using a_f by auto
      qed
    qed
  qed
  then show "\<Omega> \<le>\<^sub>c X"
    unfolding is_smaller_than_def
    using mono_type injective_imp_monomorphism by auto
qed

lemma not_init_not_term:
  "(\<not>initial_object(X) \<and> \<not>terminal_object(X)) \<longleftrightarrow> (\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2)"
proof
  assume "\<not>initial_object(X) \<and> \<not>terminal_object(X)"
  then have not_init: "\<not>initial_object(X)" and not_term: "\<not>terminal_object(X)" by auto
  have not_empty: "\<not> is_empty(X)"
  proof
    assume "is_empty(X)"
    then have "X \<cong> \<emptyset>" using no_el_iff_iso_empty by auto
    then have "initial_object(X)" using iso_empty_initial by auto
    then show False using not_init by auto
  qed
  then obtain x1 where x1_type: "x1 \<in>\<^sub>c X"
    unfolding is_empty_def by auto
  have not_single: "\<not> (\<exists>! x. x \<in>\<^sub>c X)"
  proof
    assume "\<exists>! x. x \<in>\<^sub>c X"
    then have "X \<cong> \<one>" using single_elem_iso_one by auto
    then have "terminal_object(X)" using iso_to1_is_term by auto
    then show False using not_term by auto
  qed
  then obtain x2 where x2_type: "x2 \<in>\<^sub>c X" and x2_ne_x1: "x2 \<noteq> x1"
    using x1_type by blast
  show "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2"
    using x1_type x2_type x2_ne_x1 by auto
next
  assume "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2"
  then obtain x1 x2 where x1_type: "x1 \<in>\<^sub>c X" and x2_type: "x2 \<in>\<^sub>c X" and distinct: "x1 \<noteq> x2"
    by auto
  have not_init: "\<not> initial_object(X)"
  proof
    assume "initial_object(X)"
    then have "X \<cong> \<emptyset>" using initial_iso_empty by auto
    then have "is_empty(X)" using no_el_iff_iso_empty isomorphic_is_symmetric by auto
    then show False using x1_type is_empty_def by auto
  qed
  have not_term: "\<not> terminal_object(X)"
  proof
    assume "terminal_object(X)"
    then have "X \<cong> \<one>" using terminal_objects_isomorphic one_terminal_object by auto
    then have "\<exists>! x. x \<in>\<^sub>c X" using single_elem_iso_one by auto
    then show False using x1_type x2_type distinct by auto
  qed
  show "\<not>initial_object(X) \<and> \<not>terminal_object(X)"
    using not_init not_term by auto
qed

lemma sets_size_3_plus:
  "(\<not>initial_object(X) \<and> \<not>terminal_object(X) \<and> \<not>(X \<cong> \<Omega>)) \<longleftrightarrow>
   (\<exists>x1 x2 x3. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x3 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> x2 \<noteq> x3 \<and> x1 \<noteq> x3)"
proof
  assume asm: "\<not>initial_object(X) \<and> \<not>terminal_object(X) \<and> \<not>(X \<cong> \<Omega>)"
  then have not_init: "\<not>initial_object(X)" and not_term: "\<not>terminal_object(X)" and not_omega: "\<not>(X \<cong> \<Omega>)"
    by auto
  obtain x1 x2 where x1_type: "x1 \<in>\<^sub>c X" and x2_type: "x2 \<in>\<^sub>c X" and distinct12: "x1 \<noteq> x2"
    using not_init_not_term not_init not_term by blast
  have not_exactly_two: "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2)"
  proof
    assume "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2"
    then have "\<exists>y1 y2. y1 \<in>\<^sub>c X \<and> y2 \<in>\<^sub>c X \<and> y1 \<noteq> y2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = y1 \<or> x = y2)"
      using x1_type x2_type distinct12 by auto
    then have "X \<cong> \<Omega>" using size_2_sets by auto
    then show False using not_omega by auto
  qed
  then obtain x3 where x3_type: "x3 \<in>\<^sub>c X" and x3_ne_x1: "x3 \<noteq> x1" and x3_ne_x2: "x3 \<noteq> x2"
    by auto
  show "\<exists>x1 x2 x3. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x3 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> x2 \<noteq> x3 \<and> x1 \<noteq> x3"
    using x1_type x2_type x3_type distinct12 x3_ne_x1 x3_ne_x2 by auto
next
  assume "\<exists>x1 x2 x3. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x3 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> x2 \<noteq> x3 \<and> x1 \<noteq> x3"
  then obtain x1 x2 x3 where x1_type: "x1 \<in>\<^sub>c X" and x2_type: "x2 \<in>\<^sub>c X" and x3_type: "x3 \<in>\<^sub>c X"
      and d12: "x1 \<noteq> x2" and d23: "x2 \<noteq> x3" and d13: "x1 \<noteq> x3"
    by auto
  have both_not: "\<not>initial_object(X) \<and> \<not>terminal_object(X)"
    using not_init_not_term x1_type x2_type d12 by blast
  have not_init: "\<not> initial_object(X)" using both_not by auto
  have not_term: "\<not> terminal_object(X)" using both_not by auto
  have not_omega: "\<not> (X \<cong> \<Omega>)"
  proof
    assume "X \<cong> \<Omega>"
    then have "\<exists>y1 y2. y1 \<in>\<^sub>c X \<and> y2 \<in>\<^sub>c X \<and> y1 \<noteq> y2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = y1 \<or> x = y2)"
      using size_2_sets by auto
    then obtain y1 y2 where y1_type: "y1 \<in>\<^sub>c X" and y2_type: "y2 \<in>\<^sub>c X" and y_distinct: "y1 \<noteq> y2"
        and cover: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = y1 \<or> x = y2"
      by auto
    have "x1 = y1 \<or> x1 = y2" using cover x1_type by auto
    moreover have "x2 = y1 \<or> x2 = y2" using cover x2_type by auto
    moreover have "x3 = y1 \<or> x3 = y2" using cover x3_type by auto
    ultimately show False using d12 d23 d13 by auto
  qed
  show "\<not>initial_object(X) \<and> \<not>terminal_object(X) \<and> \<not>(X \<cong> \<Omega>)"
    using not_init not_term not_omega by auto
qed

text \<open>The next two lemmas below correspond to Proposition 2.6.3 in Halvorson.\<close>
lemma smaller_than_coproduct1:
  "X \<le>\<^sub>c X \<Coprod> Y"
  unfolding is_smaller_than_def
  by (rule exI[where x="left_coproj(X, Y)"],
      intro conjI, rule left_proj_type, rule left_coproj_are_monomorphisms)

lemma smaller_than_coproduct2:
  "X \<le>\<^sub>c Y \<Coprod> X"
  unfolding is_smaller_than_def
  by (rule exI[where x="right_coproj(Y, X)"],
      intro conjI, rule right_proj_type, rule right_coproj_are_monomorphisms)

text \<open>The next two lemmas below correspond to Proposition 2.6.4 in Halvorson.\<close>
lemma smaller_than_product1:
  assumes "nonempty(Y)"
  shows "X \<le>\<^sub>c X \<times>\<^sub>c Y"
  unfolding is_smaller_than_def
proof -
  obtain y where y_type[type_rule]: "y \<in>\<^sub>c Y"
    using assms nonempty_def by auto
  have map_type: "\<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c Y"
    by typecheck_cfuncs
  have mono: "monomorphism(\<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"
    unfolding monomorphism_def3[OF map_type]
  proof (clarify)
    fix g h A
    assume g_type[type_rule]: "g : A \<rightarrow> X"
    assume h_type[type_rule]: "h : A \<rightarrow> X"
    assume eq: "\<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g = \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c h"
    have s1: "\<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g = \<langle>id(X) \<circ>\<^sub>c g, (y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c g\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have s2: "\<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c h = \<langle>id(X) \<circ>\<^sub>c h, (y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have pair_eq: "\<langle>id(X) \<circ>\<^sub>c g, (y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c g\<rangle> = \<langle>id(X) \<circ>\<^sub>c h, (y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h\<rangle>"
      using eq s1 s2 by simp
    have idXg_type: "id(X) \<circ>\<^sub>c g : A \<rightarrow> X" by typecheck_cfuncs
    have idXh_type: "id(X) \<circ>\<^sub>c h : A \<rightarrow> X" by typecheck_cfuncs
    have ybg_type: "(y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c g : A \<rightarrow> Y" by typecheck_cfuncs
    have ybh_type: "(y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h : A \<rightarrow> Y" by typecheck_cfuncs
    have "id(X) \<circ>\<^sub>c g = id(X) \<circ>\<^sub>c h"
      using iffD1[OF cart_prod_eq2[OF idXg_type ybg_type idXh_type ybh_type] pair_eq] by auto
    then show "g = h"
      using id_left_unit2[OF g_type] id_left_unit2[OF h_type] by auto
  qed
  show "\<exists>m. m : X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism(m)"
    using map_type mono by auto
qed

lemma smaller_than_product2:
  assumes "nonempty(Y)"
  shows "X \<le>\<^sub>c Y \<times>\<^sub>c X"
  unfolding is_smaller_than_def
proof -
  have "X \<le>\<^sub>c X \<times>\<^sub>c Y"
    using assms smaller_than_product1 by auto
  then obtain m where m_type[type_rule]: "m : X \<rightarrow> X \<times>\<^sub>c Y" and m_mono: "monomorphism(m)"
    using is_smaller_than_def by auto
  have "X \<times>\<^sub>c Y \<cong> Y \<times>\<^sub>c X" using product_commutes by auto
  then obtain i where i_type[type_rule]: "i : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c X" and i_iso: "isomorphism(i)"
    using is_isomorphic_def by auto
  have i_mono: "monomorphism(i)" using i_iso iso_imp_epi_and_monic by auto
  have im_type: "i \<circ>\<^sub>c m : X \<rightarrow> Y \<times>\<^sub>c X"
    by typecheck_cfuncs
  have cd: "codomain(m) = domain(i)"
    using m_type i_type unfolding cfunc_type_def by auto
  have im_mono: "monomorphism(i \<circ>\<^sub>c m)"
    using composition_of_monic_pair_is_monic[OF cd m_mono i_mono] .
  show "\<exists>m. m : X \<rightarrow> Y \<times>\<^sub>c X \<and> monomorphism(m)"
    using im_type im_mono by auto
qed

lemma Y_nonempty_then_X_le_XtoY:
  assumes "nonempty(Y)"
  shows "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
proof -
  define f where f_def: "f = (right_cart_proj(Y, X))\<^sup>\<sharp>"
  have f_type[type_rule]: "f : X \<rightarrow> X\<^bsup>Y\<^esup>"
    unfolding f_def by typecheck_cfuncs
  have mono_f: "injective(f)"
    unfolding injective_def2[OF f_type]
  proof (clarify)
    fix x y
    assume x_type[type_rule]: "x \<in>\<^sub>c X"
    assume y_type[type_rule]: "y \<in>\<^sub>c X"
    assume equals: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    have s1: "x \<circ>\<^sub>c right_cart_proj(Y, \<one>) = right_cart_proj(Y, X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_cross_prod)
    have s2: "right_cart_proj(Y, X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x) = (eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    have s3: "(eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x) = eval_func(X, Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x))"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have s4: "eval_func(X, Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)) = eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c x))"
      by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
    have s5: "eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c x)) = eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c y))"
      using equals by simp
    have s6: "eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c y)) = eval_func(X, Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y))"
      by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
    have s7: "eval_func(X, Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)) = (eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have s8: "(eval_func(X, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y) = right_cart_proj(Y, X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    have s9: "right_cart_proj(Y, X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y) = y \<circ>\<^sub>c right_cart_proj(Y, \<one>)"
      by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_cross_prod)
    have chain: "x \<circ>\<^sub>c right_cart_proj(Y, \<one>) = y \<circ>\<^sub>c right_cart_proj(Y, \<one>)"
      using s1 s2 s3 s4 s5 s6 s7 s8 s9 by simp
    have rp_epi: "epimorphism(right_cart_proj(Y, \<one>))"
      using assms nonempty_left_imp_right_proj_epimorphism by auto
    have rp_type: "right_cart_proj(Y, \<one>) : Y \<times>\<^sub>c \<one> \<rightarrow> \<one>"
      by (rule right_cart_proj_type)
    have epi_rule: "\<forall>g' h' A'. g':\<one>\<rightarrow>A' \<and> h':\<one>\<rightarrow>A' \<longrightarrow> (g'\<circ>\<^sub>cright_cart_proj(Y, \<one>)=h'\<circ>\<^sub>cright_cart_proj(Y, \<one>)\<longrightarrow>g'=h')"
      using iffD1[OF epimorphism_def3[OF rp_type] rp_epi] .
    show "x = y"
      using epi_rule[rule_format, where g'=x and h'=y and A'=X] x_type y_type chain by auto
  qed
  then show "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
    unfolding is_smaller_than_def using f_type injective_imp_monomorphism by auto
qed

lemma non_init_non_ter_sets:
  assumes "\<not>(terminal_object(X))"
  assumes "\<not>(initial_object(X))"
  shows "\<Omega> \<le>\<^sub>c X"
proof -
  have both_not: "\<not>initial_object(X) \<and> \<not>terminal_object(X)"
    using assms by auto
  then obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X"
      and distinct: "x1 \<noteq> x2"
    using not_init_not_term by auto
  have map_type: "(x1 \<amalg> x2) \<circ>\<^sub>c case_bool : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have inj: "injective((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    unfolding injective_def2[OF map_type]
  proof (clarify)
    fix \<omega>1 \<omega>2
    assume \<omega>1_type[type_rule]: "\<omega>1 \<in>\<^sub>c \<Omega>"
    assume \<omega>2_type[type_rule]: "\<omega>2 \<in>\<^sub>c \<Omega>"
    assume equals: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2"
    have cases1: "\<omega>1 = \<t> \<or> \<omega>1 = \<f>" using true_false_only_truth_values \<omega>1_type by auto
    have cases2: "\<omega>2 = \<t> \<or> \<omega>2 = \<f>" using true_false_only_truth_values \<omega>2_type by auto
    show "\<omega>1 = \<omega>2"
    proof (rule disjE[OF cases1])
      assume w1_t: "\<omega>1 = \<t>"
      show "\<omega>1 = \<omega>2"
      proof (rule disjE[OF cases2])
        assume "\<omega>2 = \<t>"
        then show "\<omega>1 = \<omega>2" using w1_t by auto
      next
        assume "\<omega>2 = \<f>"
        have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x1"
          using w1_t coprod_case_bool_true[OF x1_type x2_type] by auto
        moreover have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x2"
          using \<open>\<omega>2 = \<f>\<close> coprod_case_bool_false[OF x1_type x2_type] by auto
        ultimately have "x1 = x2" using equals by auto
        then show "\<omega>1 = \<omega>2" using distinct by auto
      qed
    next
      assume w1_f: "\<omega>1 = \<f>"
      show "\<omega>1 = \<omega>2"
      proof (rule disjE[OF cases2])
        assume "\<omega>2 = \<t>"
        have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x2"
          using w1_f coprod_case_bool_false[OF x1_type x2_type] by auto
        moreover have "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x1"
          using \<open>\<omega>2 = \<t>\<close> coprod_case_bool_true[OF x1_type x2_type] by auto
        ultimately have "x2 = x1" using equals by auto
        then show "\<omega>1 = \<omega>2" using distinct by auto
      next
        assume "\<omega>2 = \<f>"
        then show "\<omega>1 = \<omega>2" using w1_f by auto
      qed
    qed
  qed
  then show "\<Omega> \<le>\<^sub>c X"
    unfolding is_smaller_than_def using map_type injective_imp_monomorphism by auto
qed

lemma exp_preserves_card2:
  assumes "A \<le>\<^sub>c B"
  shows "A\<^bsup>X\<^esup> \<le>\<^sub>c B\<^bsup>X\<^esup>"
proof -
  obtain m where m_type[type_rule]: "m : A \<rightarrow> B" and m_mono: "monomorphism(m)"
    using assms is_smaller_than_def by auto
  have me_type: "m \<circ>\<^sub>c eval_func(A, X) : X \<times>\<^sub>c A\<^bsup>X\<^esup> \<rightarrow> B"
    by typecheck_cfuncs
  have msharp_type[type_rule]: "(m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> : A\<^bsup>X\<^esup> \<rightarrow> B\<^bsup>X\<^esup>"
    by typecheck_cfuncs
  have msharp_mono: "monomorphism((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>)"
    unfolding monomorphism_def3[OF msharp_type]
  proof (clarify)
    fix g h Z
    assume g_type[type_rule]: "g : Z \<rightarrow> A\<^bsup>X\<^esup>"
    assume h_type[type_rule]: "h : Z \<rightarrow> A\<^bsup>X\<^esup>"
    assume eq: "(m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c g = (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c h"
    have s1: "((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c g)\<^sup>\<flat> = ((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat>"
      using eq by simp
    have s2: "((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c g)\<^sup>\<flat> = eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f ((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c g))"
      by (rule inv_transpose_func_def3[OF comp_type[OF g_type msharp_type]])
    have s3: "((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat> = eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f ((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c h))"
      by (rule inv_transpose_func_def3[OF comp_type[OF h_type msharp_type]])
    have s4: "eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f ((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c g)) = eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f ((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c h))"
      using s1 s2 s3 by simp
    have idg_type: "id(X) \<times>\<^sub>f g : X \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c A\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    have idh_type: "id(X) \<times>\<^sub>f h : X \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c A\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    have s5: "id(X) \<times>\<^sub>f ((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c g) = (id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)"
      using identity_distributes_across_composition[OF g_type msharp_type] by simp
    have s6: "id(X) \<times>\<^sub>f ((m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> \<circ>\<^sub>c h) = (id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)"
      using identity_distributes_across_composition[OF h_type msharp_type] by simp
    have s7: "eval_func(B, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g))
            = eval_func(B, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h))"
      using s4 s5 s6 by simp
    have cross_type: "id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp> : X \<times>\<^sub>c A\<^bsup>X\<^esup> \<rightarrow> X \<times>\<^sub>c B\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    have evalBX_type: "eval_func(B, X) : X \<times>\<^sub>c B\<^bsup>X\<^esup> \<rightarrow> B"
      by (rule eval_func_type)
    have s8: "eval_func(B, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g))
            = (eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)"
      by (rule comp_associative2[OF idg_type cross_type evalBX_type])
    have s9: "eval_func(B, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h))
            = (eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)"
      by (rule comp_associative2[OF idh_type cross_type evalBX_type])
    have s10: "(eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)
            = (eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)"
      using s7 s8 s9 by simp
    have s11: "eval_func(B, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (m \<circ>\<^sub>c eval_func(A, X))\<^sup>\<sharp>) = m \<circ>\<^sub>c eval_func(A, X)"
      by (rule transpose_func_def[OF me_type])
    have s12: "(m \<circ>\<^sub>c eval_func(A, X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) = (m \<circ>\<^sub>c eval_func(A, X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)"
      using s10 s11 by simp
    have s13: "m \<circ>\<^sub>c (eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)) = (m \<circ>\<^sub>c eval_func(A, X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)"
      by (rule comp_associative2[OF idg_type eval_func_type m_type])
    have s14: "m \<circ>\<^sub>c (eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)) = (m \<circ>\<^sub>c eval_func(A, X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)"
      by (rule comp_associative2[OF idh_type eval_func_type m_type])
    have s15: "m \<circ>\<^sub>c (eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)) = m \<circ>\<^sub>c (eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h))"
      using s12 s13 s14 by simp
    have evalAXg_type: "eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) : X \<times>\<^sub>c Z \<rightarrow> A"
      by typecheck_cfuncs
    have evalAXh_type: "eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h) : X \<times>\<^sub>c Z \<rightarrow> A"
      by typecheck_cfuncs
    have mono_rule: "\<forall>g' h' A'. g':A'\<rightarrow>A \<and> h':A'\<rightarrow>A \<longrightarrow> (m\<circ>\<^sub>cg'=m\<circ>\<^sub>ch'\<longrightarrow>g'=h')"
      using iffD1[OF monomorphism_def3[OF m_type] m_mono] .
    have s16: "eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) = eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)"
      using mono_rule[rule_format, where g'="eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)"
                         and h'="eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f h)" and A'="X \<times>\<^sub>c Z"]
        evalAXg_type evalAXh_type s15 by auto
    show "g = h"
      using same_evals_equal[OF g_type h_type] s16 by auto
  qed
  show "A\<^bsup>X\<^esup> \<le>\<^sub>c B\<^bsup>X\<^esup>"
    unfolding is_smaller_than_def using msharp_type msharp_mono by auto
qed

lemma exp_preserves_card1:
  assumes "A \<le>\<^sub>c B"
  assumes "nonempty(X)"
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
proof -
  obtain x where x_type[type_rule]: "x \<in>\<^sub>c X"
    using assms(2) nonempty_def by auto
  obtain m where m_type[type_rule]: "m : A \<rightarrow> B" and m_mono[type_rule]: "monomorphism(m)"
    using assms(1) is_smaller_than_def by auto

  define C where C_def: "C = set_subtraction(m)"
  have tc_type[type_rule]: "try_cast(m) : B \<rightarrow> A \<Coprod> C"
    unfolding C_def using try_cast_type[OF m_mono m_type] by simp
  have tcm_eq: "try_cast(m) \<circ>\<^sub>c m = left_coproj(A, C)"
    unfolding C_def using try_cast_m_m[OF m_mono m_type] by simp

  define p1 where p1_def: "p1 = eval_func(X, A) \<circ>\<^sub>c swap(X\<^bsup>A\<^esup>, A)"
  have p1_type[type_rule]: "p1 : X\<^bsup>A\<^esup> \<times>\<^sub>c A \<rightarrow> X"
    unfolding p1_def by typecheck_cfuncs
  define p2 where p2_def: "p2 = x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c C\<^esub>"
  have p2_type[type_rule]: "p2 : X\<^bsup>A\<^esup> \<times>\<^sub>c C \<rightarrow> X"
    unfolding p2_def by typecheck_cfuncs
  define co where co_def: "co = p1 \<amalg> p2"
  have co_type[type_rule]: "co : (X\<^bsup>A\<^esup> \<times>\<^sub>c A) \<Coprod> (X\<^bsup>A\<^esup> \<times>\<^sub>c C) \<rightarrow> X"
    unfolding co_def by typecheck_cfuncs
  define dpcl where dpcl_def: "dpcl = dist_prod_coprod_left(X\<^bsup>A\<^esup>, A, C)"
  have dpcl_type[type_rule]: "dpcl : X\<^bsup>A\<^esup> \<times>\<^sub>c (A \<Coprod> C) \<rightarrow> (X\<^bsup>A\<^esup> \<times>\<^sub>c A) \<Coprod> (X\<^bsup>A\<^esup> \<times>\<^sub>c C)"
    unfolding dpcl_def by typecheck_cfuncs
  define sw where sw_def: "sw = swap(A \<Coprod> C, X\<^bsup>A\<^esup>)"
  have sw_type[type_rule]: "sw : (A \<Coprod> C) \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>A\<^esup> \<times>\<^sub>c (A \<Coprod> C)"
    unfolding sw_def by typecheck_cfuncs
  define tcid where tcid_def: "tcid = try_cast(m) \<times>\<^sub>f id(X\<^bsup>A\<^esup>)"
  have tcid_type[type_rule]: "tcid : B \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> (A \<Coprod> C) \<times>\<^sub>c X\<^bsup>A\<^esup>"
    unfolding tcid_def by (rule cfunc_cross_prod_type[OF tc_type id_type])
  define whole where whole_def: "whole = co \<circ>\<^sub>c dpcl \<circ>\<^sub>c sw \<circ>\<^sub>c tcid"
  have whole_type[type_rule]: "whole : B \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X"
    unfolding whole_def by typecheck_cfuncs
  define w where w_def: "w = whole\<^sup>\<sharp>"
  have w_type[type_rule]: "w : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup>"
    unfolding w_def by typecheck_cfuncs

  have whole_eq: "whole = eval_func(X, B) \<circ>\<^sub>c (id(B) \<times>\<^sub>f w)"
  proof -
    have e1: "w\<^sup>\<flat> = whole" using w_def flat_cancels_sharp[OF whole_type] by simp
    have e2: "w\<^sup>\<flat> = eval_func(X, B) \<circ>\<^sub>c (id(B) \<times>\<^sub>f w)" by (rule inv_transpose_func_def3[OF w_type])
    show ?thesis using e1 e2 by simp
  qed

  have reduce: "\<And>a y. a \<in>\<^sub>c A \<Longrightarrow> y \<in>\<^sub>c X\<^bsup>A\<^esup> \<Longrightarrow> whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle> = eval_func(X, A) \<circ>\<^sub>c \<langle>a, y\<rangle>"
  proof -
    fix a y
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    assume y_type[type_rule]: "y \<in>\<^sub>c X\<^bsup>A\<^esup>"
    have ma_type[type_rule]: "m \<circ>\<^sub>c a \<in>\<^sub>c B" by typecheck_cfuncs
    have t1: "tcid \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle> = \<langle>try_cast(m) \<circ>\<^sub>c (m \<circ>\<^sub>c a), id(X\<^bsup>A\<^esup>) \<circ>\<^sub>c y\<rangle>"
      unfolding tcid_def by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
    have t2: "try_cast(m) \<circ>\<^sub>c (m \<circ>\<^sub>c a) = (try_cast(m) \<circ>\<^sub>c m) \<circ>\<^sub>c a"
      by (rule comp_associative2[OF a_type m_type tc_type])
    have t3: "(try_cast(m) \<circ>\<^sub>c m) \<circ>\<^sub>c a = left_coproj(A, C) \<circ>\<^sub>c a"
      using tcm_eq by simp
    have t4: "id(X\<^bsup>A\<^esup>) \<circ>\<^sub>c y = y" by (rule id_left_unit2[OF y_type])
    have t5: "tcid \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle> = \<langle>left_coproj(A, C) \<circ>\<^sub>c a, y\<rangle>"
      using t1 t2 t3 t4 by simp
    have lca_type[type_rule]: "left_coproj(A, C) \<circ>\<^sub>c a \<in>\<^sub>c A \<Coprod> C" by typecheck_cfuncs
    have t6: "sw \<circ>\<^sub>c \<langle>left_coproj(A, C) \<circ>\<^sub>c a, y\<rangle> = \<langle>y, left_coproj(A, C) \<circ>\<^sub>c a\<rangle>"
      unfolding sw_def by (typecheck_cfuncs, simp add: swap_ap)
    have t7: "sw \<circ>\<^sub>c (tcid \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle>) = \<langle>y, left_coproj(A, C) \<circ>\<^sub>c a\<rangle>"
      using t5 t6 by simp
    have t8: "dpcl \<circ>\<^sub>c \<langle>y, left_coproj(A, C) \<circ>\<^sub>c a\<rangle> = left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>y, a\<rangle>"
      unfolding dpcl_def using dist_prod_coprod_left_ap_left[OF y_type a_type] by simp
    have t9: "dpcl \<circ>\<^sub>c (sw \<circ>\<^sub>c (tcid \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle>)) = left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>y, a\<rangle>"
      using t7 t8 by simp
    have lya_type[type_rule]: "left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>y, a\<rangle> \<in>\<^sub>c (X\<^bsup>A\<^esup> \<times>\<^sub>c A) \<Coprod> (X\<^bsup>A\<^esup> \<times>\<^sub>c C)"
      by typecheck_cfuncs
    have lc_type: "left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C) : X\<^bsup>A\<^esup> \<times>\<^sub>c A \<rightarrow> (X\<^bsup>A\<^esup> \<times>\<^sub>c A) \<Coprod> (X\<^bsup>A\<^esup> \<times>\<^sub>c C)"
      by (rule left_proj_type)
    have ya_type[type_rule]: "\<langle>y, a\<rangle> \<in>\<^sub>c X\<^bsup>A\<^esup> \<times>\<^sub>c A" by typecheck_cfuncs
    have t10a: "co \<circ>\<^sub>c (left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>y, a\<rangle>)
              = (co \<circ>\<^sub>c left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>y, a\<rangle>"
      by (rule comp_associative2[OF ya_type lc_type co_type])
    have t10b: "co \<circ>\<^sub>c left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C) = p1"
      unfolding co_def by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    have t10: "co \<circ>\<^sub>c (left_coproj(X\<^bsup>A\<^esup> \<times>\<^sub>c A, X\<^bsup>A\<^esup> \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>y, a\<rangle>) = p1 \<circ>\<^sub>c \<langle>y, a\<rangle>"
      using t10a t10b by simp
    have t11: "p1 \<circ>\<^sub>c \<langle>y, a\<rangle> = eval_func(X, A) \<circ>\<^sub>c (swap(X\<^bsup>A\<^esup>, A) \<circ>\<^sub>c \<langle>y, a\<rangle>)"
      unfolding p1_def by (typecheck_cfuncs, simp add: comp_associative2)
    have t12: "swap(X\<^bsup>A\<^esup>, A) \<circ>\<^sub>c \<langle>y, a\<rangle> = \<langle>a, y\<rangle>"
      by (typecheck_cfuncs, simp add: swap_ap)
    have t13: "whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle> = co \<circ>\<^sub>c (dpcl \<circ>\<^sub>c (sw \<circ>\<^sub>c (tcid \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle>)))"
      unfolding whole_def by (typecheck_cfuncs, simp add: comp_associative2)
    show "whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, y\<rangle> = eval_func(X, A) \<circ>\<^sub>c \<langle>a, y\<rangle>"
      using t9 t10 t11 t12 t13 by simp
  qed

  have w_mono: "monomorphism(w)"
    unfolding monomorphism_def3[OF w_type]
  proof (clarify)
    fix g h Z
    assume g_type[type_rule]: "g : Z \<rightarrow> X\<^bsup>A\<^esup>"
    assume h_type[type_rule]: "h : Z \<rightarrow> X\<^bsup>A\<^esup>"
    assume eq: "w \<circ>\<^sub>c g = w \<circ>\<^sub>c h"

    have bridge: "\<And>a z. a \<in>\<^sub>c A \<Longrightarrow> z \<in>\<^sub>c Z \<Longrightarrow> whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle> = whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
    proof -
      fix a z
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume z_type[type_rule]: "z \<in>\<^sub>c Z"
      have ma_type[type_rule]: "m \<circ>\<^sub>c a \<in>\<^sub>c B" by typecheck_cfuncs
      have gz_type[type_rule]: "g \<circ>\<^sub>c z \<in>\<^sub>c X\<^bsup>A\<^esup>" by typecheck_cfuncs
      have hz_type[type_rule]: "h \<circ>\<^sub>c z \<in>\<^sub>c X\<^bsup>A\<^esup>" by typecheck_cfuncs
      have b1: "whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle> = (eval_func(X, B) \<circ>\<^sub>c (id(B) \<times>\<^sub>f w)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>"
        using whole_eq by simp
      have b2: "(eval_func(X, B) \<circ>\<^sub>c (id(B) \<times>\<^sub>f w)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
              = eval_func(X, B) \<circ>\<^sub>c ((id(B) \<times>\<^sub>f w) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>)"
        by (typecheck_cfuncs, simp add: comp_associative2)
      have b3: "(id(B) \<times>\<^sub>f w) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle> = \<langle>id(B) \<circ>\<^sub>c (m \<circ>\<^sub>c a), w \<circ>\<^sub>c (g \<circ>\<^sub>c z)\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      have b4: "id(B) \<circ>\<^sub>c (m \<circ>\<^sub>c a) = m \<circ>\<^sub>c a" by (rule id_left_unit2[OF ma_type])
      have b5: "w \<circ>\<^sub>c (g \<circ>\<^sub>c z) = (w \<circ>\<^sub>c g) \<circ>\<^sub>c z" by (rule comp_associative2[OF z_type g_type w_type])
      have b6: "(w \<circ>\<^sub>c g) \<circ>\<^sub>c z = (w \<circ>\<^sub>c h) \<circ>\<^sub>c z" using eq by simp
      have b7: "(w \<circ>\<^sub>c h) \<circ>\<^sub>c z = w \<circ>\<^sub>c (h \<circ>\<^sub>c z)" by (rule sym[OF comp_associative2[OF z_type h_type w_type]])
      have b8: "\<langle>id(B) \<circ>\<^sub>c (m \<circ>\<^sub>c a), w \<circ>\<^sub>c (g \<circ>\<^sub>c z)\<rangle> = \<langle>m \<circ>\<^sub>c a, w \<circ>\<^sub>c (h \<circ>\<^sub>c z)\<rangle>"
        using b4 b5 b6 b7 by simp
      have b9: "\<langle>m \<circ>\<^sub>c a, w \<circ>\<^sub>c (h \<circ>\<^sub>c z)\<rangle> = (id(B) \<times>\<^sub>f w) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
      proof -
        have "(id(B) \<times>\<^sub>f w) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle> = \<langle>id(B) \<circ>\<^sub>c (m \<circ>\<^sub>c a), w \<circ>\<^sub>c (h \<circ>\<^sub>c z)\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
        then show ?thesis using b4 by simp
      qed
      have b10: "eval_func(X, B) \<circ>\<^sub>c ((id(B) \<times>\<^sub>f w) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>)
              = eval_func(X, B) \<circ>\<^sub>c ((id(B) \<times>\<^sub>f w) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>)"
        using b3 b8 b9 by simp
      have b11: "eval_func(X, B) \<circ>\<^sub>c ((id(B) \<times>\<^sub>f w) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>)
              = (eval_func(X, B) \<circ>\<^sub>c (id(B) \<times>\<^sub>f w)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      have b12: "(eval_func(X, B) \<circ>\<^sub>c (id(B) \<times>\<^sub>f w)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle> = whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
        using whole_eq by simp
      show "whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle> = whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
        using b1 b2 b10 b11 b12 by simp
    qed

    have goalA: "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) = eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)"
    proof (etcs_rule one_separator[where X="A \<times>\<^sub>c Z", where Y=X])
      fix az
      assume az_type[type_rule]: "az \<in>\<^sub>c A \<times>\<^sub>c Z"
      obtain a z where a_type[type_rule]: "a \<in>\<^sub>c A" and z_type[type_rule]: "z \<in>\<^sub>c Z"
          and az_def: "az = \<langle>a, z\<rangle>"
        using cart_prod_decomp[OF az_type] by auto
      have gz_type[type_rule]: "g \<circ>\<^sub>c z \<in>\<^sub>c X\<^bsup>A\<^esup>" by typecheck_cfuncs
      have hz_type[type_rule]: "h \<circ>\<^sub>c z \<in>\<^sub>c X\<^bsup>A\<^esup>" by typecheck_cfuncs
      have az_pair_type[type_rule]: "\<langle>a, z\<rangle> \<in>\<^sub>c A \<times>\<^sub>c Z" by typecheck_cfuncs
      have idg_type: "id(A) \<times>\<^sub>f g : A \<times>\<^sub>c Z \<rightarrow> A \<times>\<^sub>c X\<^bsup>A\<^esup>" by typecheck_cfuncs
      have idh_type: "id(A) \<times>\<^sub>f h : A \<times>\<^sub>c Z \<rightarrow> A \<times>\<^sub>c X\<^bsup>A\<^esup>" by typecheck_cfuncs
      have evalA_type: "eval_func(X, A) : A \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X" by (rule eval_func_type)
      have assoc_g: "(eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>a, z\<rangle> = eval_func(X, A) \<circ>\<^sub>c ((id(A) \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, z\<rangle>)"
        by (rule sym[OF comp_associative2[OF az_pair_type idg_type evalA_type]])
      have assoc_h: "(eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>a, z\<rangle> = eval_func(X, A) \<circ>\<^sub>c ((id(A) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>a, z\<rangle>)"
        by (rule sym[OF comp_associative2[OF az_pair_type idh_type evalA_type]])
      have r1: "eval_func(X, A) \<circ>\<^sub>c ((id(A) \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, z\<rangle>) = eval_func(X, A) \<circ>\<^sub>c \<langle>id(A) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      have r2: "eval_func(X, A) \<circ>\<^sub>c \<langle>id(A) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle> = eval_func(X, A) \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c z\<rangle>"
        using id_left_unit2[OF a_type] by simp
      have r3: "eval_func(X, A) \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c z\<rangle> = whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>"
        using reduce[OF a_type gz_type] by simp
      have r4: "whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle> = whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
        using bridge[OF a_type z_type] by simp
      have r5: "whole \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle> = eval_func(X, A) \<circ>\<^sub>c \<langle>a, h \<circ>\<^sub>c z\<rangle>"
        using reduce[OF a_type hz_type] by simp
      have r6: "eval_func(X, A) \<circ>\<^sub>c \<langle>a, h \<circ>\<^sub>c z\<rangle> = eval_func(X, A) \<circ>\<^sub>c \<langle>id(A) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
        using id_left_unit2[OF a_type] by simp
      have r7: "eval_func(X, A) \<circ>\<^sub>c \<langle>id(A) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle> = eval_func(X, A) \<circ>\<^sub>c ((id(A) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>a, z\<rangle>)"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      show "(eval_func(X, A) \<circ>\<^sub>c id(A) \<times>\<^sub>f g) \<circ>\<^sub>c az = (eval_func(X, A) \<circ>\<^sub>c id(A) \<times>\<^sub>f h) \<circ>\<^sub>c az"
        unfolding az_def
        using assoc_g assoc_h r1 r2 r3 r4 r5 r6 r7 by simp
    qed
    show "g = h"
      using same_evals_equal[OF g_type h_type] goalA by auto
  qed
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
    unfolding is_smaller_than_def using w_type w_mono by auto
qed

lemma coprod_leq_product:
  assumes X_not_init: "\<not>(initial_object(X))"
  assumes Y_not_init: "\<not>(initial_object(Y))"
  assumes X_not_term: "\<not>(terminal_object(X))"
  assumes Y_not_term: "\<not>(terminal_object(Y))"
  shows "X \<Coprod> Y \<le>\<^sub>c X \<times>\<^sub>c Y"
proof -
  obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X"
    and x_distinct: "x1 \<noteq> x2"
    using iffD1[OF not_init_not_term conjI[OF X_not_init X_not_term]] by auto
  obtain y1 y2 where y1_type[type_rule]: "y1 \<in>\<^sub>c Y" and y2_type[type_rule]: "y2 \<in>\<^sub>c Y"
    and y_distinct: "y1 \<noteq> y2"
    using iffD1[OF not_init_not_term conjI[OF Y_not_init Y_not_term]] by auto
  define q where q_def: "q = \<langle>x2 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>"
  have q_type[type_rule]: "q : Y \<rightarrow> X \<times>\<^sub>c Y"
    unfolding q_def by typecheck_cfuncs
  define eqX2 where eqX2_def: "eqX2 = eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
  have eqX2_type[type_rule]: "eqX2 : X \<rightarrow> \<Omega>"
    unfolding eqX2_def by typecheck_cfuncs
  define cb where cb_def: "cb = case_bool \<circ>\<^sub>c eqX2"
  have cb_type[type_rule]: "cb : X \<rightarrow> \<one> \<Coprod> \<one>"
    unfolding cb_def by typecheck_cfuncs
  define idcb where idcb_def: "idcb = \<langle>id(X), cb\<rangle>"
  have idcb_type[type_rule]: "idcb : X \<rightarrow> X \<times>\<^sub>c (\<one> \<Coprod> \<one>)"
    unfolding idcb_def by typecheck_cfuncs
  define dpcl where dpcl_def: "dpcl = dist_prod_coprod_left(X, \<one>, \<one>)"
  have dpcl_type[type_rule]: "dpcl : X \<times>\<^sub>c (\<one> \<Coprod> \<one>) \<rightarrow> (X \<times>\<^sub>c \<one>) \<Coprod> (X \<times>\<^sub>c \<one>)"
    unfolding dpcl_def by typecheck_cfuncs
  define p_true where p_true_def: "p_true = \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>, y2 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>\<rangle>"
  have p_true_type[type_rule]: "p_true : X \<times>\<^sub>c \<one> \<rightarrow> X \<times>\<^sub>c Y"
    unfolding p_true_def by typecheck_cfuncs
  define p_false where p_false_def: "p_false = \<langle>left_cart_proj(X, \<one>), y1 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>\<rangle>"
  have p_false_type[type_rule]: "p_false : X \<times>\<^sub>c \<one> \<rightarrow> X \<times>\<^sub>c Y"
    unfolding p_false_def by typecheck_cfuncs
  define pc where pc_def: "pc = p_true \<amalg> p_false"
  have pc_type[type_rule]: "pc : (X \<times>\<^sub>c \<one>) \<Coprod> (X \<times>\<^sub>c \<one>) \<rightarrow> X \<times>\<^sub>c Y"
    unfolding pc_def by typecheck_cfuncs
  define p where p_def: "p = pc \<circ>\<^sub>c dpcl \<circ>\<^sub>c idcb"
  have p_type[type_rule]: "p : X \<rightarrow> X \<times>\<^sub>c Y"
    unfolding p_def by typecheck_cfuncs
  have id1_type[type_rule]: "id(\<one>) : \<one> \<rightarrow> \<one>" by typecheck_cfuncs

  have p_eq2: "p \<circ>\<^sub>c x2 = \<langle>x1, y2\<rangle>"
  proof -
    have a1: "eqX2 \<circ>\<^sub>c x2 = eq_pred(X) \<circ>\<^sub>c (\<langle>id(X), x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x2)"
      unfolding eqX2_def by (typecheck_cfuncs, simp add: comp_associative2)
    have a2: "\<langle>id(X), x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x2 = \<langle>id(X) \<circ>\<^sub>c x2, (x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x2\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have a3: "(x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x2 = x2 \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x2)"
      by (rule sym[OF comp_associative2[OF x2_type terminal_func_type x2_type]])
    have a4: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x2 = id(\<one>)" by (rule terminal_func_comp_elem[OF x2_type])
    have a5: "eqX2 \<circ>\<^sub>c x2 = eq_pred(X) \<circ>\<^sub>c \<langle>x2, x2\<rangle>"
      using a1 a2 a3 a4 id_left_unit2[OF x2_type] id_right_unit2[OF x2_type] by simp
    have a6: "eqX2 \<circ>\<^sub>c x2 = \<t>"
      using a5 eq_pred_iff_eq[OF x2_type x2_type] by auto
    have b1: "cb \<circ>\<^sub>c x2 = case_bool \<circ>\<^sub>c (eqX2 \<circ>\<^sub>c x2)"
      unfolding cb_def by (typecheck_cfuncs, simp add: comp_associative2)
    have b2: "cb \<circ>\<^sub>c x2 = left_coproj(\<one>, \<one>)"
      using b1 a6 case_bool_true by simp
    have c1: "idcb \<circ>\<^sub>c x2 = \<langle>id(X) \<circ>\<^sub>c x2, cb \<circ>\<^sub>c x2\<rangle>"
      unfolding idcb_def by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have c2: "idcb \<circ>\<^sub>c x2 = \<langle>x2, left_coproj(\<one>, \<one>) \<circ>\<^sub>c id(\<one>)\<rangle>"
      using c1 b2 id_left_unit2[OF x2_type] id_right_unit2[OF left_proj_type] by simp
    have d1: "dpcl \<circ>\<^sub>c (idcb \<circ>\<^sub>c x2) = left_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>"
      unfolding dpcl_def using c2 dist_prod_coprod_left_ap_left[OF x2_type id1_type] by simp
    have e1: "p \<circ>\<^sub>c x2 = pc \<circ>\<^sub>c (dpcl \<circ>\<^sub>c (idcb \<circ>\<^sub>c x2))"
      unfolding p_def by (typecheck_cfuncs, simp add: comp_associative2)
    have e2: "p \<circ>\<^sub>c x2 = pc \<circ>\<^sub>c (left_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>)"
      using e1 d1 by simp
    have x2id1_type[type_rule]: "\<langle>x2, id(\<one>)\<rangle> \<in>\<^sub>c X \<times>\<^sub>c \<one>" by typecheck_cfuncs
    have e3: "pc \<circ>\<^sub>c (left_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>)
             = (pc \<circ>\<^sub>c left_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have e4: "pc \<circ>\<^sub>c left_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) = p_true"
      unfolding pc_def by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    have e5: "p \<circ>\<^sub>c x2 = p_true \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>"
      using e2 e3 e4 by simp
    have f1: "p_true \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>
             = \<langle>(x1 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>, (y2 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>\<rangle>"
      unfolding p_true_def by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have f2: "(x1 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle> = x1 \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>)"
      by (rule sym[OF comp_associative2[OF x2id1_type terminal_func_type x1_type]])
    have f3: "(y2 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle> = y2 \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle>)"
      by (rule sym[OF comp_associative2[OF x2id1_type terminal_func_type y2_type]])
    have f4: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x2, id(\<one>)\<rangle> = id(\<one>)"
      by (rule terminal_func_comp_elem[OF x2id1_type])
    show "p \<circ>\<^sub>c x2 = \<langle>x1, y2\<rangle>"
      using e5 f1 f2 f3 f4 id_right_unit2[OF x1_type] id_right_unit2[OF y2_type] by simp
  qed

  have p_ne2: "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> x \<noteq> x2 \<Longrightarrow> p \<circ>\<^sub>c x = \<langle>x, y1\<rangle>"
  proof -
    fix x
    assume x_type[type_rule]: "x \<in>\<^sub>c X"
    assume x_ne2: "x \<noteq> x2"
    have a1: "eqX2 \<circ>\<^sub>c x = eq_pred(X) \<circ>\<^sub>c (\<langle>id(X), x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x)"
      unfolding eqX2_def by (typecheck_cfuncs, simp add: comp_associative2)
    have a2: "\<langle>id(X), x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = \<langle>id(X) \<circ>\<^sub>c x, (x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have a3: "(x2 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = x2 \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)"
      by (rule sym[OF comp_associative2[OF x_type terminal_func_type x2_type]])
    have a4: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = id(\<one>)" by (rule terminal_func_comp_elem[OF x_type])
    have a5: "eqX2 \<circ>\<^sub>c x = eq_pred(X) \<circ>\<^sub>c \<langle>x, x2\<rangle>"
      using a1 a2 a3 a4 id_left_unit2[OF x_type] id_right_unit2[OF x2_type] by simp
    have a6: "eqX2 \<circ>\<^sub>c x = \<f>"
      using a5 iffD1[OF eq_pred_iff_eq_conv[OF x_type x2_type] x_ne2] by simp
    have b1: "cb \<circ>\<^sub>c x = case_bool \<circ>\<^sub>c (eqX2 \<circ>\<^sub>c x)"
      unfolding cb_def by (typecheck_cfuncs, simp add: comp_associative2)
    have b2: "cb \<circ>\<^sub>c x = right_coproj(\<one>, \<one>)"
      using b1 a6 case_bool_false by simp
    have c1: "idcb \<circ>\<^sub>c x = \<langle>id(X) \<circ>\<^sub>c x, cb \<circ>\<^sub>c x\<rangle>"
      unfolding idcb_def by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have c2: "idcb \<circ>\<^sub>c x = \<langle>x, right_coproj(\<one>, \<one>) \<circ>\<^sub>c id(\<one>)\<rangle>"
      using c1 b2 id_left_unit2[OF x_type] id_right_unit2[OF right_proj_type] by simp
    have d1: "dpcl \<circ>\<^sub>c (idcb \<circ>\<^sub>c x) = right_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
      unfolding dpcl_def using c2 dist_prod_coprod_left_ap_right[OF x_type id1_type] by simp
    have e1: "p \<circ>\<^sub>c x = pc \<circ>\<^sub>c (dpcl \<circ>\<^sub>c (idcb \<circ>\<^sub>c x))"
      unfolding p_def by (typecheck_cfuncs, simp add: comp_associative2)
    have e2: "p \<circ>\<^sub>c x = pc \<circ>\<^sub>c (right_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>)"
      using e1 d1 by simp
    have xid1_type[type_rule]: "\<langle>x, id(\<one>)\<rangle> \<in>\<^sub>c X \<times>\<^sub>c \<one>" by typecheck_cfuncs
    have e3: "pc \<circ>\<^sub>c (right_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>)
             = (pc \<circ>\<^sub>c right_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have e4: "pc \<circ>\<^sub>c right_coproj(X \<times>\<^sub>c \<one>, X \<times>\<^sub>c \<one>) = p_false"
      unfolding pc_def by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
    have e5: "p \<circ>\<^sub>c x = p_false \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
      using e2 e3 e4 by simp
    have f1: "p_false \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>
             = \<langle>left_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>, (y1 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>\<rangle>"
      unfolding p_false_def by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have f2: "left_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = x"
      by (rule left_cart_proj_cfunc_prod[OF x_type id1_type])
    have f3: "(y1 \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = y1 \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>)"
      by (rule sym[OF comp_associative2[OF xid1_type terminal_func_type y1_type]])
    have f4: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = id(\<one>)"
      by (rule terminal_func_comp_elem[OF xid1_type])
    show "p \<circ>\<^sub>c x = \<langle>x, y1\<rangle>"
      using e5 f1 f2 f3 f4 id_right_unit2[OF y1_type] by simp
  qed

  have q_eq: "\<And>y. y \<in>\<^sub>c Y \<Longrightarrow> q \<circ>\<^sub>c y = \<langle>x2, y\<rangle>"
  proof -
    fix y
    assume y_type[type_rule]: "y \<in>\<^sub>c Y"
    have g1: "q \<circ>\<^sub>c y = \<langle>(x2 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y, id(Y) \<circ>\<^sub>c y\<rangle>"
      unfolding q_def by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have g2: "(x2 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y = x2 \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y)"
      by (rule sym[OF comp_associative2[OF y_type terminal_func_type x2_type]])
    have g3: "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y = id(\<one>)" by (rule terminal_func_comp_elem[OF y_type])
    show "q \<circ>\<^sub>c y = \<langle>x2, y\<rangle>"
      using g1 g2 g3 id_right_unit2[OF x2_type] id_left_unit2[OF y_type] by simp
  qed

  define m where m_def: "m = p \<amalg> q"
  have m_type[type_rule]: "m : X \<Coprod> Y \<rightarrow> X \<times>\<^sub>c Y"
    unfolding m_def by typecheck_cfuncs

  have m_left: "\<And>xx. xx \<in>\<^sub>c X \<Longrightarrow> m \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c xx) = p \<circ>\<^sub>c xx"
  proof -
    fix xx assume xx_type[type_rule]: "xx \<in>\<^sub>c X"
    have "m \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c xx) = (m \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c xx"
      by (rule comp_associative2[OF xx_type left_proj_type m_type])
    also have "... = p \<circ>\<^sub>c xx"
      unfolding m_def by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    finally show "m \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c xx) = p \<circ>\<^sub>c xx" .
  qed
  have m_right: "\<And>yy. yy \<in>\<^sub>c Y \<Longrightarrow> m \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c yy) = q \<circ>\<^sub>c yy"
  proof -
    fix yy assume yy_type[type_rule]: "yy \<in>\<^sub>c Y"
    have "m \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c yy) = (m \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c yy"
      by (rule comp_associative2[OF yy_type right_proj_type m_type])
    also have "... = q \<circ>\<^sub>c yy"
      unfolding m_def by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
    finally show "m \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c yy) = q \<circ>\<^sub>c yy" .
  qed

  have m_inj: "injective(m)"
    unfolding injective_def2[OF m_type]
  proof (clarify)
    fix a b
    assume a_type[type_rule]: "a \<in>\<^sub>c X \<Coprod> Y"
    assume b_type[type_rule]: "b \<in>\<^sub>c X \<Coprod> Y"
    assume eq: "m \<circ>\<^sub>c a = m \<circ>\<^sub>c b"
    have a_cases: "(\<exists>xa. xa \<in>\<^sub>c X \<and> a = left_coproj(X, Y) \<circ>\<^sub>c xa) \<or> (\<exists>ya. ya \<in>\<^sub>c Y \<and> a = right_coproj(X, Y) \<circ>\<^sub>c ya)"
      using coprojs_jointly_surj[OF a_type] by simp
    have b_cases: "(\<exists>xb. xb \<in>\<^sub>c X \<and> b = left_coproj(X, Y) \<circ>\<^sub>c xb) \<or> (\<exists>yb. yb \<in>\<^sub>c Y \<and> b = right_coproj(X, Y) \<circ>\<^sub>c yb)"
      using coprojs_jointly_surj[OF b_type] by simp
    show "a = b"
    proof (rule disjE[OF a_cases])
      assume "\<exists>xa. xa \<in>\<^sub>c X \<and> a = left_coproj(X, Y) \<circ>\<^sub>c xa"
      then obtain xa where xa_type[type_rule]: "xa \<in>\<^sub>c X" and a_def: "a = left_coproj(X, Y) \<circ>\<^sub>c xa" by auto
      show "a = b"
      proof (rule disjE[OF b_cases])
        assume "\<exists>xb. xb \<in>\<^sub>c X \<and> b = left_coproj(X, Y) \<circ>\<^sub>c xb"
        then obtain xb where xb_type[type_rule]: "xb \<in>\<^sub>c X" and b_def: "b = left_coproj(X, Y) \<circ>\<^sub>c xb" by auto
        have pxa_pxb: "p \<circ>\<^sub>c xa = p \<circ>\<^sub>c xb"
          using eq a_def b_def m_left[OF xa_type] m_left[OF xb_type] by simp
        show "a = b"
        proof (cases "xa = x2")
          case True
          show "a = b"
          proof (cases "xb = x2")
            case True
            then show "a = b" using a_def b_def \<open>xa = x2\<close> by simp
          next
            case False
            have v1: "p \<circ>\<^sub>c xa = \<langle>x1, y2\<rangle>" using p_eq2 \<open>xa = x2\<close> by simp
            have v2: "p \<circ>\<^sub>c xb = \<langle>xb, y1\<rangle>" using p_ne2[OF xb_type False] .
            have v3: "\<langle>x1,y2\<rangle> = \<langle>xb,y1\<rangle>" using pxa_pxb v1 v2 by simp
            have v4: "x1 = xb \<and> y2 = y1" using iffD1[OF cart_prod_eq2[OF x1_type y2_type xb_type y1_type] v3] .
            then show "a = b" using y_distinct by auto
          qed
        next
          case False
          show "a = b"
          proof (cases "xb = x2")
            case True
            have v1: "p \<circ>\<^sub>c xa = \<langle>xa, y1\<rangle>" using p_ne2[OF xa_type False] .
            have v2: "p \<circ>\<^sub>c xb = \<langle>x1, y2\<rangle>" using p_eq2 \<open>xb = x2\<close> by simp
            have v3: "\<langle>xa,y1\<rangle> = \<langle>x1,y2\<rangle>" using pxa_pxb v1 v2 by simp
            have v4: "xa = x1 \<and> y1 = y2" using iffD1[OF cart_prod_eq2[OF xa_type y1_type x1_type y2_type] v3] .
            then show "a = b" using y_distinct by auto
          next
            case False
            have v1: "p \<circ>\<^sub>c xa = \<langle>xa, y1\<rangle>" using p_ne2[OF xa_type \<open>xa \<noteq> x2\<close>] .
            have v2: "p \<circ>\<^sub>c xb = \<langle>xb, y1\<rangle>" using p_ne2[OF xb_type False] .
            have v3: "\<langle>xa,y1\<rangle> = \<langle>xb,y1\<rangle>" using pxa_pxb v1 v2 by simp
            have v4: "xa = xb" using iffD1[OF cart_prod_eq2[OF xa_type y1_type xb_type y1_type] v3] by auto
            then show "a = b" using a_def b_def by simp
          qed
        qed
      next
        assume "\<exists>yb. yb \<in>\<^sub>c Y \<and> b = right_coproj(X, Y) \<circ>\<^sub>c yb"
        then obtain yb where yb_type[type_rule]: "yb \<in>\<^sub>c Y" and b_def: "b = right_coproj(X, Y) \<circ>\<^sub>c yb" by auto
        have pxa_qyb: "p \<circ>\<^sub>c xa = q \<circ>\<^sub>c yb"
          using eq a_def b_def m_left[OF xa_type] m_right[OF yb_type] by simp
        have qyb_eq: "q \<circ>\<^sub>c yb = \<langle>x2, yb\<rangle>" using q_eq[OF yb_type] .
        show "a = b"
        proof (cases "xa = x2")
          case True
          have v1: "p \<circ>\<^sub>c xa = \<langle>x1, y2\<rangle>" using p_eq2 \<open>xa = x2\<close> by simp
          have v3: "\<langle>x1,y2\<rangle> = \<langle>x2,yb\<rangle>" using pxa_qyb qyb_eq v1 by simp
          have v4: "x1 = x2 \<and> y2 = yb" using iffD1[OF cart_prod_eq2[OF x1_type y2_type x2_type yb_type] v3] .
          then show "a = b" using x_distinct by auto
        next
          case False
          have v1: "p \<circ>\<^sub>c xa = \<langle>xa, y1\<rangle>" using p_ne2[OF xa_type False] .
          have v3: "\<langle>xa,y1\<rangle> = \<langle>x2,yb\<rangle>" using pxa_qyb qyb_eq v1 by simp
          have v4: "xa = x2 \<and> y1 = yb" using iffD1[OF cart_prod_eq2[OF xa_type y1_type x2_type yb_type] v3] .
          then show "a = b" using \<open>xa \<noteq> x2\<close> by auto
        qed
      qed
    next
      assume "\<exists>ya. ya \<in>\<^sub>c Y \<and> a = right_coproj(X, Y) \<circ>\<^sub>c ya"
      then obtain ya where ya_type[type_rule]: "ya \<in>\<^sub>c Y" and a_def: "a = right_coproj(X, Y) \<circ>\<^sub>c ya" by auto
      show "a = b"
      proof (rule disjE[OF b_cases])
        assume "\<exists>xb. xb \<in>\<^sub>c X \<and> b = left_coproj(X, Y) \<circ>\<^sub>c xb"
        then obtain xb where xb_type[type_rule]: "xb \<in>\<^sub>c X" and b_def: "b = left_coproj(X, Y) \<circ>\<^sub>c xb" by auto
        have qya_pxb: "q \<circ>\<^sub>c ya = p \<circ>\<^sub>c xb"
          using eq a_def b_def m_right[OF ya_type] m_left[OF xb_type] by simp
        have qya_eq: "q \<circ>\<^sub>c ya = \<langle>x2, ya\<rangle>" using q_eq[OF ya_type] .
        show "a = b"
        proof (cases "xb = x2")
          case True
          have v1: "p \<circ>\<^sub>c xb = \<langle>x1, y2\<rangle>" using p_eq2 \<open>xb = x2\<close> by simp
          have v3: "\<langle>x2,ya\<rangle> = \<langle>x1,y2\<rangle>" using qya_pxb qya_eq v1 by simp
          have v4: "x2 = x1 \<and> ya = y2" using iffD1[OF cart_prod_eq2[OF x2_type ya_type x1_type y2_type] v3] .
          then show "a = b" using x_distinct by auto
        next
          case False
          have v1: "p \<circ>\<^sub>c xb = \<langle>xb, y1\<rangle>" using p_ne2[OF xb_type False] .
          have v3: "\<langle>x2,ya\<rangle> = \<langle>xb,y1\<rangle>" using qya_pxb qya_eq v1 by simp
          have v4: "x2 = xb \<and> ya = y1" using iffD1[OF cart_prod_eq2[OF x2_type ya_type xb_type y1_type] v3] .
          then show "a = b" using \<open>xb \<noteq> x2\<close> by auto
        qed
      next
        assume "\<exists>yb. yb \<in>\<^sub>c Y \<and> b = right_coproj(X, Y) \<circ>\<^sub>c yb"
        then obtain yb where yb_type[type_rule]: "yb \<in>\<^sub>c Y" and b_def: "b = right_coproj(X, Y) \<circ>\<^sub>c yb" by auto
        have qya_qyb: "q \<circ>\<^sub>c ya = q \<circ>\<^sub>c yb"
          using eq a_def b_def m_right[OF ya_type] m_right[OF yb_type] by simp
        have "\<langle>x2, ya\<rangle> = \<langle>x2, yb\<rangle>" using qya_qyb q_eq[OF ya_type] q_eq[OF yb_type] by simp
        then have "ya = yb" using iffD1[OF cart_prod_eq2[OF x2_type ya_type x2_type yb_type]] by auto
        then show "a = b" using a_def b_def by simp
      qed
    qed
  qed

  have m_mono: "monomorphism(m)" using injective_imp_monomorphism[OF m_inj] .
  show "X \<Coprod> Y \<le>\<^sub>c X \<times>\<^sub>c Y"
    unfolding is_smaller_than_def using m_type m_mono by auto
qed

lemma prod_leq_exp:
  assumes Y_not_term: "\<not> terminal_object(Y)"
  shows "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
proof (cases "initial_object(Y)")
  assume Y_init: "initial_object(Y)"
  have Y_iso_empty: "Y \<cong> \<emptyset>" using initial_iso_empty[OF Y_init] .
  have X_iso_X: "X \<cong> X" by (rule isomorphic_is_reflexive)
  have XY_iso_Xempty: "X \<times>\<^sub>c Y \<cong> X \<times>\<^sub>c \<emptyset>" using prod_pres_iso[OF X_iso_X Y_iso_empty] .
  have Xempty_iso_empty: "X \<times>\<^sub>c \<emptyset> \<cong> \<emptyset>" using X_prod_empty .
  have XY_iso_empty: "X \<times>\<^sub>c Y \<cong> \<emptyset>" using XY_iso_Xempty Xempty_iso_empty isomorphic_is_transitive by blast
  have XY_init: "initial_object(X \<times>\<^sub>c Y)" using iso_empty_initial[OF XY_iso_empty] .
  have all_f: "\<forall>Z. \<exists>!f. f : (X \<times>\<^sub>c Y) \<rightarrow> Z" using iffD1[OF initial_object_def XY_init] .
  have ex_f: "\<exists>f. f : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>" using all_f by blast
  obtain f where f_type: "f : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>" using ex_f by auto
  have f_mono: "monomorphism(f)" using initial_maps_mono[OF XY_init f_type] .
  show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
    unfolding is_smaller_than_def using f_type f_mono by auto
next
  assume Y_not_init: "\<not> initial_object(Y)"
  obtain y1 y2 where y1_type[type_rule]: "y1 \<in>\<^sub>c Y" and y2_type[type_rule]: "y2 \<in>\<^sub>c Y"
    and y1_ne_y2: "y1 \<noteq> y2"
    using iffD1[OF not_init_not_term conjI[OF Y_not_init Y_not_term]] by auto
  show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
  proof (cases "X \<cong> \<Omega>")
    assume X_iso_Omega: "X \<cong> \<Omega>"
    have exists_omega_facts: "\<exists>x1 x2. x1 \<in>\<^sub>c Y \<and> x2 \<in>\<^sub>c Y \<and> x1 \<noteq> x2"
      using iffD1[OF not_init_not_term conjI[OF Y_not_init Y_not_term]] .
    have Omega_leq_Y: "\<Omega> \<le>\<^sub>c Y" using iffD2[OF size_2plus_sets] exists_omega_facts by auto
    obtain m where m_type[type_rule]: "m : \<Omega> \<rightarrow> Y" and m_mono: "monomorphism(m)"
      using Omega_leq_Y is_smaller_than_def by auto
    have idY_type[type_rule]: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
    have id_Y_mono: "monomorphism(id(Y))" using id_isomorphism iso_imp_epi_and_monic by auto
    have m_id_type[type_rule]: "m \<times>\<^sub>f id(Y) : \<Omega> \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c Y" by typecheck_cfuncs
    have m_id_mono: "monomorphism(m \<times>\<^sub>f id(Y))"
      using cfunc_cross_prod_mono[OF m_type idY_type m_mono id_Y_mono] by simp
    have YxY_iso_YtoOmega: "Y \<times>\<^sub>c Y \<cong> Y\<^bsup>\<Omega>\<^esup>" using sets_squared isomorphic_is_symmetric by auto
    obtain n where n_type[type_rule]: "n : Y \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>\<Omega>\<^esup>" and n_mono: "monomorphism(n)"
      using YxY_iso_YtoOmega is_isomorphic_def iso_imp_epi_and_monic by auto
    have Omega_iso_X: "\<Omega> \<cong> X" using X_iso_Omega isomorphic_is_symmetric by auto
    have YtoOmega_iso_YtoX: "Y\<^bsup>\<Omega>\<^esup> \<cong> Y\<^bsup>X\<^esup>" using exp_pres_iso_right[OF Omega_iso_X] .
    obtain r where r_type[type_rule]: "r : Y\<^bsup>\<Omega>\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>" and r_mono: "monomorphism(r)"
      using YtoOmega_iso_YtoX is_isomorphic_def iso_imp_epi_and_monic by auto
    have Y_iso_Y: "Y \<cong> Y" by (rule isomorphic_is_reflexive)
    have XY_iso_OmegaY: "X \<times>\<^sub>c Y \<cong> \<Omega> \<times>\<^sub>c Y" using prod_pres_iso[OF X_iso_Omega Y_iso_Y] .
    obtain q where q_type[type_rule]: "q : X \<times>\<^sub>c Y \<rightarrow> \<Omega> \<times>\<^sub>c Y" and q_mono: "monomorphism(q)"
      using XY_iso_OmegaY is_isomorphic_def iso_imp_epi_and_monic by auto
    have cod_dom1: "codomain(q) = domain(m \<times>\<^sub>f id(Y))" using q_type m_id_type unfolding cfunc_type_def by auto
    have step1_mono: "monomorphism((m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q)"
      using composition_of_monic_pair_is_monic[OF cod_dom1 q_mono m_id_mono] by simp
    have step1_type[type_rule]: "(m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c Y" by typecheck_cfuncs
    have cod_dom2: "codomain((m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q) = domain(n)" using step1_type n_type unfolding cfunc_type_def by auto
    have step2_mono: "monomorphism(n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q)"
      using composition_of_monic_pair_is_monic[OF cod_dom2 step1_mono n_mono] by simp
    have step2_type[type_rule]: "n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>\<Omega>\<^esup>" by typecheck_cfuncs
    have cod_dom3: "codomain(n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q) = domain(r)" using step2_type r_type unfolding cfunc_type_def by auto
    have final_mono: "monomorphism(r \<circ>\<^sub>c n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q)"
      using composition_of_monic_pair_is_monic[OF cod_dom3 step2_mono r_mono] by simp
    have final_type[type_rule]: "r \<circ>\<^sub>c n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>" by typecheck_cfuncs
    show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
      unfolding is_smaller_than_def using final_type final_mono by auto
  next
    assume X_not_Omega: "\<not> (X \<cong> \<Omega>)"
    show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
    proof (cases "initial_object(X)")
      assume X_init: "initial_object(X)"
      have X_iso_empty: "X \<cong> \<emptyset>" using initial_iso_empty[OF X_init] .
      have X_empty: "is_empty(X)" using no_el_iff_iso_empty X_iso_empty by auto
      have XY_empty: "is_empty(X \<times>\<^sub>c Y)" using prod_with_empty_is_empty1[OF X_empty] .
      have XY_iso_empty: "X \<times>\<^sub>c Y \<cong> \<emptyset>" using no_el_iff_iso_empty XY_empty by auto
      have XY_init: "initial_object(X \<times>\<^sub>c Y)" using iso_empty_initial[OF XY_iso_empty] .
      have all_f: "\<forall>Z. \<exists>!f. f : (X \<times>\<^sub>c Y) \<rightarrow> Z" using iffD1[OF initial_object_def XY_init] .
      have ex_f: "\<exists>f. f : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>" using all_f by blast
      obtain f where f_type: "f : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>" using ex_f by auto
      have f_mono: "monomorphism(f)" using initial_maps_mono[OF XY_init f_type] .
      show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
        unfolding is_smaller_than_def using f_type f_mono by auto
    next
      assume X_not_init: "\<not> initial_object(X)"
      show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
      proof (cases "terminal_object(X)")
        assume X_term: "terminal_object(X)"
        have X_iso_one: "X \<cong> \<one>" using terminal_objects_isomorphic[OF X_term one_terminal_object] .
        have XY_iso_Y: "X \<times>\<^sub>c Y \<cong> Y" using prod_with_term_obj1[OF X_term] .
        have Y_iso_YtoOne: "Y \<cong> Y\<^bsup>\<one>\<^esup>" using exp_one isomorphic_is_symmetric by auto
        have one_iso_X: "\<one> \<cong> X" using X_iso_one isomorphic_is_symmetric by auto
        have YtoOne_iso_YtoX: "Y\<^bsup>\<one>\<^esup> \<cong> Y\<^bsup>X\<^esup>" using exp_pres_iso_right[OF one_iso_X] .
        have XY_iso_YtoX1: "X \<times>\<^sub>c Y \<cong> Y\<^bsup>\<one>\<^esup>" using XY_iso_Y Y_iso_YtoOne isomorphic_is_transitive by blast
        have XY_iso_YtoX: "X \<times>\<^sub>c Y \<cong> Y\<^bsup>X\<^esup>" using XY_iso_YtoX1 YtoOne_iso_YtoX isomorphic_is_transitive by blast
        obtain g where g_type: "g : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>" and g_iso: "isomorphism(g)"
          using XY_iso_YtoX is_isomorphic_def by auto
        have g_mono: "monomorphism(g)" using g_iso iso_imp_epi_and_monic by auto
        show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
          unfolding is_smaller_than_def using g_type g_mono by auto
      next
        assume X_not_term: "\<not> terminal_object(X)"

        define into where into_def: "into =
           (left_cart_proj(Y, \<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
           \<circ>\<^sub>c dist_prod_coprod_left(Y, \<one>, \<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f eq_pred(X))"
        have into_type[type_rule]: "into : Y \<times>\<^sub>c (X \<times>\<^sub>c X) \<rightarrow> Y"
          unfolding into_def by typecheck_cfuncs

        have id1_type[type_rule]: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)

        define \<Theta> where \<Theta>_def: "\<Theta> = (into \<circ>\<^sub>c associate_right(Y, X, X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X))\<^sup>\<sharp> \<circ>\<^sub>c swap(X, Y)"
        have base_type[type_rule]: "into \<circ>\<^sub>c associate_right(Y, X, X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X) : X \<times>\<^sub>c (Y \<times>\<^sub>c X) \<rightarrow> Y"
          by typecheck_cfuncs
        have sharp_type[type_rule]: "(into \<circ>\<^sub>c associate_right(Y, X, X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X))\<^sup>\<sharp> : Y \<times>\<^sub>c X \<rightarrow> Y\<^bsup>X\<^esup>"
          by typecheck_cfuncs
        have \<Theta>_type[type_rule]: "\<Theta> : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>"
          unfolding \<Theta>_def by typecheck_cfuncs

        have f0: "\<And>x y z. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> z \<in>\<^sub>c X \<Longrightarrow>
            (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c \<langle>y, \<langle>x, z\<rangle>\<rangle>"
        proof -
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          have xy_type[type_rule]: "\<langle>x, y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" by typecheck_cfuncs
          have g1: "\<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = \<langle>id(X) \<circ>\<^sub>c z, \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp)
          have g2: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c z = id(\<one>)" by (rule terminal_func_comp_elem[OF z_type])
          have g3: "\<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = \<langle>z, id(\<one>)\<rangle>"
            using g1 g2 id_left_unit2[OF z_type] by simp
          have g4: "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = (\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>z, id(\<one>)\<rangle>"
            using g3 by simp
          have g5: "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>x,y\<rangle>)"
            using inv_transpose_of_composition[OF xy_type \<Theta>_type] by simp
          have g6: "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>z, id(\<one>)\<rangle> = (\<Theta>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>x,y\<rangle>)) \<circ>\<^sub>c \<langle>z, id(\<one>)\<rangle>"
            using g5 by simp
          have zid1_type[type_rule]: "\<langle>z, id(\<one>)\<rangle> \<in>\<^sub>c X \<times>\<^sub>c \<one>" by typecheck_cfuncs
          have g7: "(\<Theta>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>x,y\<rangle>)) \<circ>\<^sub>c \<langle>z, id(\<one>)\<rangle> = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c ((id(X) \<times>\<^sub>f \<langle>x,y\<rangle>) \<circ>\<^sub>c \<langle>z, id(\<one>)\<rangle>)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have g8: "(id(X) \<times>\<^sub>f \<langle>x,y\<rangle>) \<circ>\<^sub>c \<langle>z, id(\<one>)\<rangle> = \<langle>id(X) \<circ>\<^sub>c z, \<langle>x,y\<rangle> \<circ>\<^sub>c id(\<one>)\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have g9: "(id(X) \<times>\<^sub>f \<langle>x,y\<rangle>) \<circ>\<^sub>c \<langle>z, id(\<one>)\<rangle> = \<langle>z, \<langle>x,y\<rangle>\<rangle>"
            using g8 id_left_unit2[OF z_type] id_right_unit2[OF xy_type] by simp
          have g10: "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle>"
            using g4 g6 g7 g9 by simp
          have swapXY_type[type_rule]: "swap(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c X" by typecheck_cfuncs
          have h1: "\<Theta>\<^sup>\<flat> = (into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X))\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f swap(X, Y))"
            unfolding \<Theta>_def using inv_transpose_of_composition[OF swapXY_type sharp_type] by simp
          have h2: "(into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X))\<^sup>\<sharp>\<^sup>\<flat> = into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)"
            by (rule flat_cancels_sharp[OF base_type])
          have h3: "\<Theta>\<^sup>\<flat> = (into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f swap(X, Y))"
            using h1 h2 by simp
          have h4: "\<Theta>\<^sup>\<flat> \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle> = ((into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f swap(X, Y))) \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle>"
            using h3 by simp
          have zxy_type[type_rule]: "\<langle>z, \<langle>x,y\<rangle>\<rangle> \<in>\<^sub>c X \<times>\<^sub>c (X \<times>\<^sub>c Y)" by typecheck_cfuncs
          have h5: "(id(X) \<times>\<^sub>f swap(X, Y)) \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle> = \<langle>id(X) \<circ>\<^sub>c z, swap(X,Y) \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have h6: "swap(X,Y) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<langle>y,x\<rangle>" by (rule swap_ap[OF x_type y_type])
          have h7: "(id(X) \<times>\<^sub>f swap(X, Y)) \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle> = \<langle>z, \<langle>y,x\<rangle>\<rangle>"
            using h5 h6 id_left_unit2[OF z_type] by simp
          have h8: "((into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f swap(X, Y))) \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle>
                   = (into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f swap(X, Y)) \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle>)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have h9: "(into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f swap(X, Y)) \<circ>\<^sub>c \<langle>z, \<langle>x,y\<rangle>\<rangle>)
                   = (into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c \<langle>z, \<langle>y,x\<rangle>\<rangle>"
            using h7 by simp
          have yx_type[type_rule]: "\<langle>y,x\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c X" by typecheck_cfuncs
          have zyx_type[type_rule]: "\<langle>z, \<langle>y,x\<rangle>\<rangle> \<in>\<^sub>c X \<times>\<^sub>c (Y \<times>\<^sub>c X)" by typecheck_cfuncs
          have h10: "(into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c \<langle>z, \<langle>y,x\<rangle>\<rangle>
                   = into \<circ>\<^sub>c (associate_right(Y,X,X) \<circ>\<^sub>c (swap(X, Y \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>z, \<langle>y,x\<rangle>\<rangle>))"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have h11: "swap(X, Y \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>z, \<langle>y,x\<rangle>\<rangle> = \<langle>\<langle>y,x\<rangle>, z\<rangle>"
            by (rule swap_ap[OF z_type yx_type])
          have h12: "associate_right(Y,X,X) \<circ>\<^sub>c \<langle>\<langle>y,x\<rangle>, z\<rangle> = \<langle>y, \<langle>x,z\<rangle>\<rangle>"
            by (rule associate_right_ap[OF y_type x_type z_type])
          have h13: "(into \<circ>\<^sub>c associate_right(Y,X,X) \<circ>\<^sub>c swap(X, Y \<times>\<^sub>c X)) \<circ>\<^sub>c \<langle>z, \<langle>y,x\<rangle>\<rangle> = into \<circ>\<^sub>c \<langle>y, \<langle>x,z\<rangle>\<rangle>"
            using h10 h11 h12 by simp
          show "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c \<langle>y, \<langle>x, z\<rangle>\<rangle>"
            using g10 h4 h8 h9 h13 by simp
        qed

        have into_ap: "\<And>y' x' z'. y' \<in>\<^sub>c Y \<Longrightarrow> x' \<in>\<^sub>c X \<Longrightarrow> z' \<in>\<^sub>c X \<Longrightarrow>
            into \<circ>\<^sub>c \<langle>y', \<langle>x', z'\<rangle>\<rangle> =
            (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
              \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>"
        proof -
          fix y' x' z'
          assume y'_type[type_rule]: "y' \<in>\<^sub>c Y"
          assume x'_type[type_rule]: "x' \<in>\<^sub>c X"
          assume z'_type[type_rule]: "z' \<in>\<^sub>c X"
          have xz_type[type_rule]: "\<langle>x',z'\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" by typecheck_cfuncs
          have yxz_type[type_rule]: "\<langle>y', \<langle>x',z'\<rangle>\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c (X \<times>\<^sub>c X)" by typecheck_cfuncs
          have yeq_type[type_rule]: "\<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
          have bigA_type[type_rule]:
            "left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1))
               : (Y \<times>\<^sub>c \<one>) \<Coprod> (Y \<times>\<^sub>c \<one>) \<rightarrow> Y"
            by typecheck_cfuncs
          have bigB_type[type_rule]: "dist_prod_coprod_left(Y,\<one>,\<one>) : Y \<times>\<^sub>c (\<one> \<Coprod> \<one>) \<rightarrow> (Y \<times>\<^sub>c \<one>) \<Coprod> (Y \<times>\<^sub>c \<one>)"
            by typecheck_cfuncs
          have bigC_type[type_rule]: "id(Y) \<times>\<^sub>f case_bool : Y \<times>\<^sub>c \<Omega> \<rightarrow> Y \<times>\<^sub>c (\<one> \<Coprod> \<one>)" by typecheck_cfuncs
          have k1: "into \<circ>\<^sub>c \<langle>y', \<langle>x',z'\<rangle>\<rangle> =
              ((left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool)) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f eq_pred(X)) \<circ>\<^sub>c \<langle>y', \<langle>x',z'\<rangle>\<rangle>)"
            unfolding into_def by (typecheck_cfuncs, simp add: comp_associative2)
          have k2: "(id(Y) \<times>\<^sub>f eq_pred(X)) \<circ>\<^sub>c \<langle>y', \<langle>x',z'\<rangle>\<rangle> = \<langle>id(Y) \<circ>\<^sub>c y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have k3: "(id(Y) \<times>\<^sub>f eq_pred(X)) \<circ>\<^sub>c \<langle>y', \<langle>x',z'\<rangle>\<rangle> = \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>"
            using k2 id_left_unit2[OF y'_type] by simp
          have k4: "into \<circ>\<^sub>c \<langle>y', \<langle>x',z'\<rangle>\<rangle> =
              ((left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool)) \<circ>\<^sub>c \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>"
            using k1 k3 by simp
          have bigBC_type[type_rule]: "dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool) : Y \<times>\<^sub>c \<Omega> \<rightarrow> (Y \<times>\<^sub>c \<one>) \<Coprod> (Y \<times>\<^sub>c \<one>)"
            by typecheck_cfuncs
          have step1: "((left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool)) \<circ>\<^sub>c \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>
              = (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c ((dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool)) \<circ>\<^sub>c \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>)"
            by (rule sym[OF comp_associative2[OF yeq_type bigBC_type bigA_type]])
          have step2: "(dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool)) \<circ>\<^sub>c \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>
              = dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>)"
            by (rule sym[OF comp_associative2[OF yeq_type bigC_type bigB_type]])
          show "into \<circ>\<^sub>c \<langle>y', \<langle>x',z'\<rangle>\<rangle> =
              (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y', eq_pred(X) \<circ>\<^sub>c \<langle>x',z'\<rangle>\<rangle>"
            using k4 step1 step2 by simp
        qed

        have f1: "\<And>x y. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y"
        proof -
          fix x y
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          have m1: "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = into \<circ>\<^sub>c \<langle>y, \<langle>x, x\<rangle>\<rangle>"
            using f0[OF x_type y_type x_type] .
          have m2: "eq_pred(X) \<circ>\<^sub>c \<langle>x,x\<rangle> = \<t>" using iffD1[OF eq_pred_iff_eq[OF x_type x_type]] by simp
          have m3: "into \<circ>\<^sub>c \<langle>y, \<langle>x,x\<rangle>\<rangle> =
              (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y, \<t>\<rangle>"
            using into_ap[OF y_type x_type x_type] m2 by simp
          have m4: "(id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y, \<t>\<rangle> = \<langle>id(Y) \<circ>\<^sub>c y, case_bool \<circ>\<^sub>c \<t>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have m5: "case_bool \<circ>\<^sub>c \<t> = left_coproj(\<one>,\<one>)" by (rule case_bool_true)
          have m6: "(id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y, \<t>\<rangle> = \<langle>y, left_coproj(\<one>,\<one>)\<rangle>"
            using m4 m5 id_left_unit2[OF y_type] by simp
          have m7: "\<langle>y, left_coproj(\<one>,\<one>)\<rangle> = \<langle>y, left_coproj(\<one>,\<one>) \<circ>\<^sub>c id(\<one>)\<rangle>"
            using id_right_unit2[OF left_proj_type] by simp
          have m8: "dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c \<langle>y, left_coproj(\<one>,\<one>) \<circ>\<^sub>c id(\<one>)\<rangle> = left_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>"
            by (rule dist_prod_coprod_left_ap_left[OF y_type id1_type])
          have m9: "into \<circ>\<^sub>c \<langle>y, \<langle>x,x\<rangle>\<rangle> =
              (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c (left_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>)"
            using m3 m6 m7 m8 by simp
          have yid1_type[type_rule]: "\<langle>y,id(\<one>)\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c \<one>" by typecheck_cfuncs
          have m10: "(left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c (left_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>)
              = ((left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c left_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have m11: "(left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c left_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) = left_cart_proj(Y,\<one>)"
            by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
          have m12: "into \<circ>\<^sub>c \<langle>y, \<langle>x,x\<rangle>\<rangle> = left_cart_proj(Y,\<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>"
            using m9 m10 m11 by simp
          have m13: "left_cart_proj(Y,\<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle> = y"
            by (rule left_cart_proj_cfunc_prod[OF y_type id1_type])
          show "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y"
            using m1 m12 m13 by simp
        qed

        have f2: "\<And>x y z. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> z \<in>\<^sub>c X \<Longrightarrow> z \<noteq> x \<Longrightarrow> y \<noteq> y1 \<Longrightarrow>
            (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
        proof -
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          assume z_ne_x: "z \<noteq> x"
          assume y_ne_y1: "y \<noteq> y1"
          have n1: "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c \<langle>y, \<langle>x, z\<rangle>\<rangle>"
            using f0[OF x_type y_type z_type] .
          have x_ne_z: "x \<noteq> z" using z_ne_x by auto
          have n2: "eq_pred(X) \<circ>\<^sub>c \<langle>x,z\<rangle> = \<f>"
            using iffD1[OF eq_pred_iff_eq_conv[OF x_type z_type] x_ne_z] .
          have n3: "into \<circ>\<^sub>c \<langle>y, \<langle>x,z\<rangle>\<rangle> =
              (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y, \<f>\<rangle>"
            using into_ap[OF y_type x_type z_type] n2 by simp
          have n4: "(id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y, \<f>\<rangle> = \<langle>id(Y) \<circ>\<^sub>c y, case_bool \<circ>\<^sub>c \<f>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have n5: "case_bool \<circ>\<^sub>c \<f> = right_coproj(\<one>,\<one>)" by (rule case_bool_false)
          have n6: "(id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y, \<f>\<rangle> = \<langle>y, right_coproj(\<one>,\<one>)\<rangle>"
            using n4 n5 id_left_unit2[OF y_type] by simp
          have n7: "\<langle>y, right_coproj(\<one>,\<one>)\<rangle> = \<langle>y, right_coproj(\<one>,\<one>) \<circ>\<^sub>c id(\<one>)\<rangle>"
            using id_right_unit2[OF right_proj_type] by simp
          have n8: "dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c \<langle>y, right_coproj(\<one>,\<one>) \<circ>\<^sub>c id(\<one>)\<rangle> = right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>"
            by (rule dist_prod_coprod_left_ap_right[OF y_type id1_type])
          have n9: "into \<circ>\<^sub>c \<langle>y, \<langle>x,z\<rangle>\<rangle> =
              (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c (right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>)"
            using n3 n6 n7 n8 by simp
          have yid1_type[type_rule]: "\<langle>y,id(\<one>)\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c \<one>" by typecheck_cfuncs
          have n10: "(left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c (right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>)
              = ((left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have n11: "(left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)"
            by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
          have n12: "into \<circ>\<^sub>c \<langle>y, \<langle>x,z\<rangle>\<rangle> = ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>"
            using n9 n10 n11 by simp
          have n13: "((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>
                   = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle>)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have n14: "(id(Y) \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle> = \<langle>id(Y) \<circ>\<^sub>c y, y1 \<circ>\<^sub>c id(\<one>)\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have n15: "(id(Y) \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y,id(\<one>)\<rangle> = \<langle>y, y1\<rangle>"
            using n14 id_left_unit2[OF y_type] id_right_unit2[OF y1_type] by simp
          have n16: "into \<circ>\<^sub>c \<langle>y, \<langle>x,z\<rangle>\<rangle> = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c \<langle>y, y1\<rangle>"
            using n12 n13 n15 by simp
          have n17: "eq_pred(Y) \<circ>\<^sub>c \<langle>y, y1\<rangle> = \<f>"
            using iffD1[OF eq_pred_iff_eq_conv[OF y_type y1_type] y_ne_y1] .
          have n18: "into \<circ>\<^sub>c \<langle>y, \<langle>x,z\<rangle>\<rangle> = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<f>"
            using n16 n17 by simp
          have n19: "case_bool \<circ>\<^sub>c \<f> = right_coproj(\<one>,\<one>)" by (rule case_bool_false)
          have n20: "into \<circ>\<^sub>c \<langle>y, \<langle>x,z\<rangle>\<rangle> = (y2 \<amalg> y1) \<circ>\<^sub>c right_coproj(\<one>,\<one>)"
            using n18 n19 by simp
          have n21: "(y2 \<amalg> y1) \<circ>\<^sub>c right_coproj(\<one>,\<one>) = y1"
            by (rule right_coproj_cfunc_coprod[OF y2_type y1_type])
          show "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
            using n1 n20 n21 by simp
        qed

        have f3: "\<And>x z. x \<in>\<^sub>c X \<Longrightarrow> z \<in>\<^sub>c X \<Longrightarrow> z \<noteq> x \<Longrightarrow>
            (\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
        proof -
          fix x z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          assume z_ne_x: "z \<noteq> x"
          have p1: "(\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c \<langle>y1, \<langle>x, z\<rangle>\<rangle>"
            using f0[OF x_type y1_type z_type] .
          have x_ne_z: "x \<noteq> z" using z_ne_x by auto
          have p2: "eq_pred(X) \<circ>\<^sub>c \<langle>x,z\<rangle> = \<f>"
            using iffD1[OF eq_pred_iff_eq_conv[OF x_type z_type] x_ne_z] .
          have p3: "into \<circ>\<^sub>c \<langle>y1, \<langle>x,z\<rangle>\<rangle> =
              (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y1, \<f>\<rangle>"
            using into_ap[OF y1_type x_type z_type] p2 by simp
          have p4: "(id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y1, \<f>\<rangle> = \<langle>id(Y) \<circ>\<^sub>c y1, case_bool \<circ>\<^sub>c \<f>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have p5: "case_bool \<circ>\<^sub>c \<f> = right_coproj(\<one>,\<one>)" by (rule case_bool_false)
          have p6: "(id(Y) \<times>\<^sub>f case_bool) \<circ>\<^sub>c \<langle>y1, \<f>\<rangle> = \<langle>y1, right_coproj(\<one>,\<one>)\<rangle>"
            using p4 p5 id_left_unit2[OF y1_type] by simp
          have p7: "\<langle>y1, right_coproj(\<one>,\<one>)\<rangle> = \<langle>y1, right_coproj(\<one>,\<one>) \<circ>\<^sub>c id(\<one>)\<rangle>"
            using id_right_unit2[OF right_proj_type] by simp
          have p8: "dist_prod_coprod_left(Y,\<one>,\<one>) \<circ>\<^sub>c \<langle>y1, right_coproj(\<one>,\<one>) \<circ>\<^sub>c id(\<one>)\<rangle> = right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle>"
            by (rule dist_prod_coprod_left_ap_right[OF y1_type id1_type])
          have p9: "into \<circ>\<^sub>c \<langle>y1, \<langle>x,z\<rangle>\<rangle> =
              (left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c (right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle>)"
            using p3 p6 p7 p8 by simp
          have y1id1_type[type_rule]: "\<langle>y1,id(\<one>)\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c \<one>" by typecheck_cfuncs
          have p10: "(left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c (right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle>)
              = ((left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have p11: "(left_cart_proj(Y,\<one>) \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)))
                \<circ>\<^sub>c right_coproj(Y \<times>\<^sub>c \<one>, Y \<times>\<^sub>c \<one>) = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)"
            by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
          have p12: "into \<circ>\<^sub>c \<langle>y1, \<langle>x,z\<rangle>\<rangle> = ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle>"
            using p9 p10 p11 by simp
          have p13: "((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle>
                   = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle>)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          have p14: "(id(Y) \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle> = \<langle>id(Y) \<circ>\<^sub>c y1, y1 \<circ>\<^sub>c id(\<one>)\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          have p15: "(id(Y) \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y1,id(\<one>)\<rangle> = \<langle>y1, y1\<rangle>"
            using p14 id_left_unit2[OF y1_type] id_right_unit2[OF y1_type] by simp
          have p16: "into \<circ>\<^sub>c \<langle>y1, \<langle>x,z\<rangle>\<rangle> = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred(Y) \<circ>\<^sub>c \<langle>y1, y1\<rangle>"
            using p12 p13 p15 by simp
          have p17: "eq_pred(Y) \<circ>\<^sub>c \<langle>y1, y1\<rangle> = \<t>"
            using iffD1[OF eq_pred_iff_eq[OF y1_type y1_type]] by simp
          have p18: "into \<circ>\<^sub>c \<langle>y1, \<langle>x,z\<rangle>\<rangle> = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<t>"
            using p16 p17 by simp
          have p19: "case_bool \<circ>\<^sub>c \<t> = left_coproj(\<one>,\<one>)" by (rule case_bool_true)
          have p20: "into \<circ>\<^sub>c \<langle>y1, \<langle>x,z\<rangle>\<rangle> = (y2 \<amalg> y1) \<circ>\<^sub>c left_coproj(\<one>,\<one>)"
            using p18 p19 by simp
          have p21: "(y2 \<amalg> y1) \<circ>\<^sub>c left_coproj(\<one>,\<one>) = y2"
            by (rule left_coproj_cfunc_coprod[OF y2_type y1_type])
          show "(\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
            using p1 p20 p21 by simp
        qed

        have third_point: "\<And>p q. p \<in>\<^sub>c X \<Longrightarrow> q \<in>\<^sub>c X \<Longrightarrow> \<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q"
        proof -
          fix p q
          assume p_type[type_rule]: "p \<in>\<^sub>c X"
          assume q_type[type_rule]: "q \<in>\<^sub>c X"
          obtain a b c where a_type[type_rule]: "a \<in>\<^sub>c X" and b_type[type_rule]: "b \<in>\<^sub>c X" and c_type[type_rule]: "c \<in>\<^sub>c X"
            and ab: "a \<noteq> b" and bc: "b \<noteq> c" and ac: "a \<noteq> c"
            using iffD1[OF sets_size_3_plus conjI[OF X_not_init conjI[OF X_not_term X_not_Omega]]] by auto
          have case_a: "a = p \<or> a \<noteq> p" by auto
          show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q"
          proof (rule disjE[OF case_a])
            assume a_eq: "a = p"
            have case_b: "b = q \<or> b \<noteq> q" by auto
            show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q"
            proof (rule disjE[OF case_b])
              assume "b = q"
              show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q" using ac bc a_eq \<open>b = q\<close> c_type by auto
            next
              assume "b \<noteq> q"
              show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q" using ab a_eq \<open>b \<noteq> q\<close> b_type by auto
            qed
          next
            assume a_ne: "a \<noteq> p"
            have case_as: "a = q \<or> a \<noteq> q" by auto
            show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q"
            proof (rule disjE[OF case_as])
              assume a_eq_q: "a = q"
              have case_b2: "b = p \<or> b \<noteq> p" by auto
              show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q"
              proof (rule disjE[OF case_b2])
                assume "b = p"
                show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q" using ac bc a_eq_q \<open>b = p\<close> c_type by auto
              next
                assume "b \<noteq> p"
                show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q" using ab a_eq_q \<open>b \<noteq> p\<close> b_type by auto
              qed
            next
              assume "a \<noteq> q"
              show "\<exists>z. z \<in>\<^sub>c X \<and> z \<noteq> p \<and> z \<noteq> q" using a_ne \<open>a \<noteq> q\<close> a_type by auto
            qed
          qed
        qed

        have \<Theta>_injective: "injective(\<Theta>)"
          unfolding injective_def2[OF \<Theta>_type]
        proof (clarify)
          fix xy st
          assume xy_type[type_rule]: "xy \<in>\<^sub>c X \<times>\<^sub>c Y"
          assume st_type[type_rule]: "st \<in>\<^sub>c X \<times>\<^sub>c Y"
          assume equals: "\<Theta> \<circ>\<^sub>c xy = \<Theta> \<circ>\<^sub>c st"
          obtain x y where x_type[type_rule]: "x \<in>\<^sub>c X" and y_type[type_rule]: "y \<in>\<^sub>c Y" and xy_def: "xy = \<langle>x,y\<rangle>"
            using cart_prod_decomp[OF xy_type] by auto
          obtain s t where s_type[type_rule]: "s \<in>\<^sub>c X" and t_type[type_rule]: "t \<in>\<^sub>c Y" and st_def: "st = \<langle>s,t\<rangle>"
            using cart_prod_decomp[OF st_type] by auto
          have equals2: "\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>" using equals xy_def st_def by simp
          have case_y1: "y = y1 \<or> y \<noteq> y1" by auto
          have main: "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
          proof (rule disjE[OF case_y1])
            assume y_eq_y1: "y = y1"
            have case_t1: "t = y1 \<or> t \<noteq> y1" by auto
            show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
            proof (rule disjE[OF case_t1])
              assume t_eq_y1: "t = y1"
              have case_xs: "x = s \<or> x \<noteq> s" by auto
              show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
              proof (rule disjE[OF case_xs])
                assume "x = s"
                then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" using y_eq_y1 t_eq_y1 by simp
              next
                assume x_ne_s: "x \<noteq> s"
                have eq_xy1_sy1: "\<Theta> \<circ>\<^sub>c \<langle>x,y1\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,y1\<rangle>" using equals2 y_eq_y1 t_eq_y1 by simp
                have val1: "(\<Theta> \<circ>\<^sub>c \<langle>s, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y1" using f1[OF s_type y1_type] .
                have s_ne_x: "s \<noteq> x" using x_ne_s by auto
                have val2: "(\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y2" using f3[OF x_type s_type s_ne_x] .
                have val2': "(\<Theta> \<circ>\<^sub>c \<langle>s, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y2" using val2[unfolded eq_xy1_sy1] .
                have "y1 = y2" by (rule trans[OF val1[symmetric] val2'])
                then have False using y1_ne_y2 by simp
                then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" by simp
              qed
            next
              assume t_ne_y1: "t \<noteq> y1"
              have case_sx: "s = x \<or> s \<noteq> x" by auto
              show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
              proof (rule disjE[OF case_sx])
                assume s_eq_x: "s = x"
                have val_y: "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y" using f1[OF x_type y_type] .
                have val_t: "(\<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = t" using f1[OF s_type t_type] .
                have val_t': "(\<Theta> \<circ>\<^sub>c \<langle>x,t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = t" using val_t[unfolded s_eq_x] .
                have eq_xy_xt: "\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>x,t\<rangle>" using equals2[unfolded s_eq_x] .
                have "y = t" by (rule trans[OF val_y[unfolded eq_xy_xt, symmetric] val_t'])
                then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" using s_eq_x by simp
              next
                assume s_ne_x: "s \<noteq> x"
                obtain z where z_type[type_rule]: "z \<in>\<^sub>c X" and z_ne_x: "z \<noteq> x" and z_ne_s: "z \<noteq> s"
                  using third_point[OF x_type s_type] by auto
                have t_sz: "(\<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
                  using f2[OF s_type t_type z_type z_ne_s t_ne_y1] .
                have y_xz: "(\<Theta> \<circ>\<^sub>c \<langle>x,y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
                  using f3[OF x_type z_type z_ne_x] .
                have eq_xy1: "\<Theta> \<circ>\<^sub>c \<langle>x,y1\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>" using equals2 y_eq_y1 by simp
                have y_xz': "(\<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2" using y_xz[unfolded eq_xy1] .
                have "y1 = y2" by (rule trans[OF t_sz[symmetric] y_xz'])
                then have False using y1_ne_y2 by simp
                then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" by simp
              qed
            qed
          next
            assume y_ne_y1: "y \<noteq> y1"
            have case_y2: "y = y2 \<or> y \<noteq> y2" by auto
            show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
            proof (rule disjE[OF case_y2])
              assume y_eq_y2: "y = y2"
              have case_t2: "t = y2 \<or> t \<noteq> y2" by auto
              show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
              proof (rule disjE[OF case_t2])
                assume t_eq_y2: "t = y2"
                have case_xs2: "x = s \<or> x \<noteq> s" by auto
                show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
                proof (rule disjE[OF case_xs2])
                  assume "x = s"
                  then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" using y_eq_y2 t_eq_y2 by simp
                next
                  assume x_ne_s: "x \<noteq> s"
                  have eq_xy2_sy2: "\<Theta> \<circ>\<^sub>c \<langle>x,y2\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,y2\<rangle>" using equals2 y_eq_y2 t_eq_y2 by simp
                  have val1: "(\<Theta> \<circ>\<^sub>c \<langle>x, y2\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y2" using f1[OF x_type y2_type] .
                  have y2_ne_y1: "y2 \<noteq> y1" using y1_ne_y2 by auto
                  have val2: "(\<Theta> \<circ>\<^sub>c \<langle>s, y2\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y1"
                    using f2[OF s_type y2_type x_type x_ne_s y2_ne_y1] .
                  have val1': "(\<Theta> \<circ>\<^sub>c \<langle>s, y2\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y2" using val1[unfolded eq_xy2_sy2] .
                  have "y2 = y1" by (rule trans[OF val1'[symmetric] val2])
                  then have False using y1_ne_y2 by simp
                  then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" by simp
                qed
              next
                assume t_ne_y2: "t \<noteq> y2"
                have case_xs3: "x = s \<or> x \<noteq> s" by auto
                show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
                proof (rule disjE[OF case_xs3])
                  assume x_eq_s: "x = s"
                  have val_y: "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y" using f1[OF x_type y_type] .
                  have val_t: "(\<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = t" using f1[OF s_type t_type] .
                  have val_y': "(\<Theta> \<circ>\<^sub>c \<langle>s,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y" using val_y[unfolded x_eq_s] .
                  have eq_sy_st: "\<Theta> \<circ>\<^sub>c \<langle>s,y\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>" using equals2[unfolded x_eq_s] .
                  have "y = t" by (rule trans[OF val_y'[unfolded eq_sy_st, symmetric] val_t])
                  then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" using x_eq_s by simp
                next
                  assume x_ne_s: "x \<noteq> s"
                  have case_t1b: "t = y1 \<or> t \<noteq> y1" by auto
                  show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
                  proof (rule disjE[OF case_t1b])
                    assume t_eq_y1: "t = y1"
                    obtain z where z_type[type_rule]: "z \<in>\<^sub>c X" and z_ne_x: "z \<noteq> x" and z_ne_s: "z \<noteq> s"
                      using third_point[OF x_type s_type] by auto
                    have y2_ne_y1: "y2 \<noteq> y1" using y1_ne_y2 by auto
                    have val1: "(\<Theta> \<circ>\<^sub>c \<langle>x, y2\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
                      using f2[OF x_type y2_type z_type z_ne_x y2_ne_y1] .
                    have val2: "(\<Theta> \<circ>\<^sub>c \<langle>s, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
                      using f3[OF s_type z_type z_ne_s] .
                    have eq_xy2_sy1: "\<Theta> \<circ>\<^sub>c \<langle>x,y2\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,y1\<rangle>" using equals2 y_eq_y2 t_eq_y1 by simp
                    have val1': "(\<Theta> \<circ>\<^sub>c \<langle>s, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1" using val1[unfolded eq_xy2_sy1] .
                    have "y1 = y2" by (rule trans[OF val1'[symmetric] val2])
                    then have False using y1_ne_y2 by simp
                    then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" by simp
                  next
                    assume t_ne_y1: "t \<noteq> y1"
                    have s_ne_x: "s \<noteq> x" using x_ne_s by auto
                    have val1: "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y1"
                      using f2[OF x_type y_type s_type s_ne_x y_ne_y1] .
                    have val2: "(\<Theta> \<circ>\<^sub>c \<langle>s, t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = t"
                      using f1[OF s_type t_type] .
                    have val1': "(\<Theta> \<circ>\<^sub>c \<langle>s, t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y1" using val1[unfolded equals2] .
                    have "t = y1" by (rule trans[OF val2[symmetric] val1'])
                    then have False using t_ne_y1 by simp
                    then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" by simp
                  qed
                qed
              qed
            next
              assume y_ne_y2: "y \<noteq> y2"
              have case_sx4: "s = x \<or> s \<noteq> x" by auto
              show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
              proof (rule disjE[OF case_sx4])
                assume s_eq_x: "s = x"
                have val_y: "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y" using f1[OF x_type y_type] .
                have val_t: "(\<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = t" using f1[OF s_type t_type] .
                have val_t': "(\<Theta> \<circ>\<^sub>c \<langle>x,t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = t" using val_t[unfolded s_eq_x] .
                have eq_xy_xt: "\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>x,t\<rangle>" using equals2[unfolded s_eq_x] .
                have "y = t" by (rule trans[OF val_y[unfolded eq_xy_xt, symmetric] val_t'])
                then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" using s_eq_x by simp
              next
                assume s_ne_x: "s \<noteq> x"
                have x_ne_s: "x \<noteq> s" using s_ne_x by auto
                have val_s1: "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y1"
                  using f2[OF x_type y_type s_type s_ne_x y_ne_y1] .
                have val_s2: "(\<Theta> \<circ>\<^sub>c \<langle>s, t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = t"
                  using f1[OF s_type t_type] .
                have val_s1': "(\<Theta> \<circ>\<^sub>c \<langle>s, t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c s = y1" using val_s1[unfolded equals2] .
                have t_eq_y1: "t = y1" by (rule trans[OF val_s2[symmetric] val_s1'])
                have eq_xy_sy1: "\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,y1\<rangle>" using equals2 t_eq_y1 by simp
                have val_x1: "(\<Theta> \<circ>\<^sub>c \<langle>s, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y2"
                  using f3[OF s_type x_type x_ne_s] .
                have val_x2: "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y"
                  using f1[OF x_type y_type] .
                have val_x2': "(\<Theta> \<circ>\<^sub>c \<langle>s, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X), \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y" using val_x2[unfolded eq_xy_sy1] .
                have "y = y2" by (rule trans[OF val_x2'[symmetric] val_x1])
                then have False using y_ne_y2 by simp
                then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>" by simp
              qed
            qed
          qed
          then show "xy = st" using xy_def st_def by simp
        qed

        have \<Theta>_mono: "monomorphism(\<Theta>)" using injective_imp_monomorphism[OF \<Theta>_injective] .
        show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
          unfolding is_smaller_than_def using \<Theta>_type \<Theta>_mono by auto
      qed
    qed
  qed
qed

lemma exp_preserves_card3:
  assumes "A \<le>\<^sub>c B"
  assumes "X \<le>\<^sub>c Y"
  assumes "nonempty(X)"
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
proof -
  have leq1: "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
    using assms(1) assms(3) exp_preserves_card1 by auto
  have leq2: "X\<^bsup>B\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    using assms(2) exp_preserves_card2 by auto
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    using leq1 leq2 set_card_transitive by auto
qed

end
