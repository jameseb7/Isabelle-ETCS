section \<open>Fixed Points and Cantor's Theorems\<close>

theory Fixed_Points
  imports Axiom_Of_Choice Pred_Logic Cardinality
begin

text \<open>The definitions below correspond to Definition 2.6.12 in Halvorson.\<close>
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> o" where
  "fixed_point(a,g) \<longleftrightarrow> (\<exists>A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = a)"

definition has_fixed_point :: "cfunc \<Rightarrow> o" where
  "has_fixed_point(g) \<longleftrightarrow> (\<exists>a. fixed_point(a,g))"

definition fixed_point_property :: "cset \<Rightarrow> o" where
  "fixed_point_property(A) \<longleftrightarrow> (\<forall>g. g : A \<rightarrow> A \<longrightarrow> has_fixed_point(g))"

lemma fixed_point_def2:
  assumes "g : A \<rightarrow> A" "a \<in>\<^sub>c A"
  shows "fixed_point(a,g) \<longleftrightarrow> (g \<circ>\<^sub>c a = a)"
  unfolding fixed_point_def using assms by blast

text \<open>The lemma below corresponds to Theorem 2.6.13 in Halvorson.\<close>
lemma Lawveres_fixed_point_theorem:
  assumes p_type[type_rule]: "p : X \<rightarrow> A\<^bsup>X\<^esup>"
  assumes p_surj: "surjective(p)"
  shows "fixed_point_property(A)"
  unfolding fixed_point_property_def has_fixed_point_def
proof (clarify)
  fix g
  assume g_type[type_rule]: "g : A \<rightarrow> A"
  define \<phi> where \<phi>_def: "\<phi> = p\<^sup>\<flat>"
  have \<phi>_type[type_rule]: "\<phi> : X \<times>\<^sub>c X \<rightarrow> A" unfolding \<phi>_def by typecheck_cfuncs
  define f where f_def: "f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X)"
  have f_type[type_rule]: "f : X \<rightarrow> A" unfolding f_def by typecheck_cfuncs

  have mf_type[type_rule]: "metafunc(f) \<in>\<^sub>c A\<^bsup>X\<^esup>" by typecheck_cfuncs
  have surj_iff: "surjective(p) \<longleftrightarrow> (\<forall>y. y \<in>\<^sub>c A\<^bsup>X\<^esup> \<longrightarrow> (\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y))"
    using surjective_def2[OF p_type] .
  have ex_xf: "\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = metafunc(f)"
    using surj_iff p_surj mf_type by auto
  obtain x_f where x_f_type[type_rule]: "x_f \<in>\<^sub>c X" and x_f: "p \<circ>\<^sub>c x_f = metafunc(f)"
    using ex_xf by auto

  have main: "\<phi>\<^bsub>[-,x_f]\<^esub> = f"
  proof (etcs_rule one_separator)
    fix x
    assume x_type[type_rule]: "x \<in>\<^sub>c X"
    have s1: "\<phi>\<^bsub>[-,x_f]\<^esub> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
      by (rule right_param_on_el[OF \<phi>_type x_type x_f_type])
    have s2: "\<phi> = eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f p)"
      unfolding \<phi>_def by (rule inv_transpose_func_def3[OF p_type])
    have idXp_type[type_rule]: "id(X) \<times>\<^sub>f p : X \<times>\<^sub>c X \<rightarrow> X \<times>\<^sub>c A\<^bsup>X\<^esup>" by typecheck_cfuncs
    have eval_type[type_rule]: "eval_func(A, X) : X \<times>\<^sub>c A\<^bsup>X\<^esup> \<rightarrow> A" by typecheck_cfuncs
    have xxf_type[type_rule]: "\<langle>x,x_f\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" by typecheck_cfuncs
    have s3: "\<phi> \<circ>\<^sub>c \<langle>x, x_f\<rangle> = (eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f p)) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
      using s2 by simp
    have s4: "(eval_func(A, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f p)) \<circ>\<^sub>c \<langle>x, x_f\<rangle> = eval_func(A, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f p) \<circ>\<^sub>c \<langle>x, x_f\<rangle>)"
      by (rule sym[OF comp_associative2[OF xxf_type idXp_type eval_type]])
    have s5: "(id(X) \<times>\<^sub>f p) \<circ>\<^sub>c \<langle>x, x_f\<rangle> = \<langle>id(X) \<circ>\<^sub>c x, p \<circ>\<^sub>c x_f\<rangle>"
      by (rule cfunc_cross_prod_comp_cfunc_prod[OF x_type x_f_type id_type p_type])
    have s6: "id(X) \<circ>\<^sub>c x = x" using id_left_unit2[OF x_type] .
    have s7: "(id(X) \<times>\<^sub>f p) \<circ>\<^sub>c \<langle>x, x_f\<rangle> = \<langle>x, metafunc(f)\<rangle>"
      using s5 s6 x_f by simp
    have s8: "\<phi> \<circ>\<^sub>c \<langle>x, x_f\<rangle> = eval_func(A, X) \<circ>\<^sub>c \<langle>x, metafunc(f)\<rangle>"
      using s3 s4 s7 by simp
    have s9: "eval_func(A, X) \<circ>\<^sub>c \<langle>x, metafunc(f)\<rangle> = f \<circ>\<^sub>c x"
      using eval_lemma[OF f_type x_type] .
    show "\<phi>\<^bsub>[-,x_f]\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x" using s1 s8 s9 by simp
  qed

  have s10: "\<phi>\<^bsub>[-,x_f]\<^esub> \<circ>\<^sub>c x_f = f \<circ>\<^sub>c x_f" using main by simp
  have diagX_type[type_rule]: "diagonal(X) : X \<rightarrow> X \<times>\<^sub>c X" by typecheck_cfuncs
  have phidiag_type[type_rule]: "\<phi> \<circ>\<^sub>c diagonal(X) : X \<rightarrow> A" by typecheck_cfuncs
  have t1: "f \<circ>\<^sub>c x_f = (g \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c diagonal(X))) \<circ>\<^sub>c x_f"
    unfolding f_def by simp
  have t2: "(g \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c diagonal(X))) \<circ>\<^sub>c x_f = g \<circ>\<^sub>c ((\<phi> \<circ>\<^sub>c diagonal(X)) \<circ>\<^sub>c x_f)"
    by (rule sym[OF comp_associative2[OF x_f_type phidiag_type g_type]])
  have t3: "(\<phi> \<circ>\<^sub>c diagonal(X)) \<circ>\<^sub>c x_f = \<phi> \<circ>\<^sub>c (diagonal(X) \<circ>\<^sub>c x_f)"
    by (rule sym[OF comp_associative2[OF x_f_type diagX_type \<phi>_type]])
  have t4: "diagonal(X) \<circ>\<^sub>c x_f = \<langle>x_f,x_f\<rangle>" using diag_on_elements[OF x_f_type] .
  have t5: "f \<circ>\<^sub>c x_f = g \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle>)"
    using t1 t2 t3 t4 by simp
  have t6: "\<phi>\<^bsub>[-,x_f]\<^esub> \<circ>\<^sub>c x_f = \<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>"
    by (rule right_param_on_el[OF \<phi>_type x_f_type x_f_type])
  have t7: "\<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle> = g \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle>)"
    using s10 t5 t6 by simp

  have witness_type[type_rule]: "\<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle> \<in>\<^sub>c A" by typecheck_cfuncs
  have fp: "fixed_point(\<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle>, g)"
    unfolding fixed_point_def
  proof (rule exI[where x=A], intro conjI)
    show "g : A \<rightarrow> A" by (rule g_type)
    show "\<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle> \<in>\<^sub>c A" by (rule witness_type)
    show "g \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle>) = \<phi> \<circ>\<^sub>c \<langle>x_f,x_f\<rangle>" using t7 by simp
  qed
  show "\<exists>a. fixed_point(a, g)" using fp by auto
qed

text \<open>The theorem below corresponds to Theorem 2.6.14 in Halvorson.\<close>
theorem Cantors_Negative_Theorem:
  "\<not> (\<exists>s. s : X \<rightarrow> powerset(X) \<and> surjective(s))"
proof (rule ccontr)
  assume "\<not> \<not> (\<exists>s. s : X \<rightarrow> powerset(X) \<and> surjective(s))"
  then obtain s where s_type: "s : X \<rightarrow> powerset(X)" and s_surj: "surjective(s)" by auto
  have s_type2: "s : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>" using s_type by (simp add: powerset_def)
  have Omega_has_ffp: "fixed_point_property(\<Omega>)"
    using Lawveres_fixed_point_theorem[OF s_type2 s_surj] .
  have Omega_doesnt_have_ffp: "\<not> fixed_point_property(\<Omega>)"
    unfolding fixed_point_property_def has_fixed_point_def fixed_point_def
  proof
    assume BWOC: "\<forall>g. g : \<Omega> \<rightarrow> \<Omega> \<longrightarrow> (\<exists>a. \<exists>A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = a)"
    have ex_fp: "\<exists>a. \<exists>A. NOT : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> NOT \<circ>\<^sub>c a = a"
      using BWOC NOT_type by auto
    then obtain a A where a_type[type_rule]: "a \<in>\<^sub>c A" and notA_type: "NOT : A \<rightarrow> A" and not_a_eq_a: "NOT \<circ>\<^sub>c a = a"
      by auto
    have A_eq_Omega: "A = \<Omega>" using notA_type NOT_type unfolding cfunc_type_def by auto
    then have a_type2[type_rule]: "a \<in>\<^sub>c \<Omega>" using a_type by simp
    show False
    proof (cases "a = \<t>")
      case True
      then have "NOT \<circ>\<^sub>c a = \<f>" using NOT_true_is_false by simp
      then show False using not_a_eq_a True true_false_distinct by simp
    next
      case False
      then have a_eq_f: "a = \<f>" using a_type2 true_false_only_truth_values by auto
      then have "NOT \<circ>\<^sub>c a = \<t>" using NOT_false_is_true by simp
      then show False using not_a_eq_a a_eq_f true_false_distinct by simp
    qed
  qed
  show False using Omega_has_ffp Omega_doesnt_have_ffp by simp
qed

text \<open>The theorem below corresponds to Exercise 2.6.15 in Halvorson.\<close>
theorem Cantors_Positive_Theorem:
  "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective(m)"
proof -
  have eq_pred_sharp_type[type_rule]: "(eq_pred(X))\<^sup>\<sharp> : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have inj: "injective((eq_pred(X))\<^sup>\<sharp>)"
    unfolding injective_def
  proof (clarify)
    fix x y
    assume "x \<in>\<^sub>c domain((eq_pred(X))\<^sup>\<sharp>)"
    then have x_type[type_rule]: "x \<in>\<^sub>c X" using eq_pred_sharp_type unfolding cfunc_type_def by auto
    assume "y \<in>\<^sub>c domain((eq_pred(X))\<^sup>\<sharp>)"
    then have y_type[type_rule]: "y \<in>\<^sub>c X" using eq_pred_sharp_type unfolding cfunc_type_def by auto
    assume eq: "(eq_pred(X))\<^sup>\<sharp> \<circ>\<^sub>c x = (eq_pred(X))\<^sup>\<sharp> \<circ>\<^sub>c y"
    have xx_type[type_rule]: "\<langle>x,x\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" by typecheck_cfuncs
    have xy_type[type_rule]: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" by typecheck_cfuncs
    have idXeq_type[type_rule]: "id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp> : X \<times>\<^sub>c X \<rightarrow> X \<times>\<^sub>c \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
    have eval_type[type_rule]: "eval_func(\<Omega>, X) : X \<times>\<^sub>c \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>" by typecheck_cfuncs
    have s1: "eval_func(\<Omega>, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) = eq_pred(X)"
      by (rule transpose_func_def[OF eq_pred_type])
    have s2: "eq_pred(X) \<circ>\<^sub>c \<langle>x,x\<rangle> = (eval_func(\<Omega>, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,x\<rangle>"
      using s1 by simp
    have s3: "(eval_func(\<Omega>, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,x\<rangle>
        = eval_func(\<Omega>, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,x\<rangle>)"
      by (rule sym[OF comp_associative2[OF xx_type idXeq_type eval_type]])
    have s4: "(id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,x\<rangle> = \<langle>id(X) \<circ>\<^sub>c x, (eq_pred(X))\<^sup>\<sharp> \<circ>\<^sub>c x\<rangle>"
      by (rule cfunc_cross_prod_comp_cfunc_prod[OF x_type x_type id_type eq_pred_sharp_type])
    have s5: "id(X) \<circ>\<^sub>c x = x" using id_left_unit2[OF x_type] .
    have s7: "(id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,x\<rangle> = \<langle>x, (eq_pred(X))\<^sup>\<sharp> \<circ>\<^sub>c y\<rangle>"
      using s4 s5 eq by simp
    have s8: "\<langle>x, (eq_pred(X))\<^sup>\<sharp> \<circ>\<^sub>c y\<rangle> = (id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,y\<rangle>"
    proof -
      have "(id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<langle>id(X) \<circ>\<^sub>c x, (eq_pred(X))\<^sup>\<sharp> \<circ>\<^sub>c y\<rangle>"
        by (rule cfunc_cross_prod_comp_cfunc_prod[OF x_type y_type id_type eq_pred_sharp_type])
      then show ?thesis using s5 by simp
    qed
    have s9: "eval_func(\<Omega>, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,x\<rangle>)
            = eval_func(\<Omega>, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,y\<rangle>)"
      using s7 s8 by simp
    have s10: "eval_func(\<Omega>, X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,y\<rangle>)
            = (eval_func(\<Omega>, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,y\<rangle>"
      by (rule comp_associative2[OF xy_type idXeq_type eval_type])
    have s11: "(eval_func(\<Omega>, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (eq_pred(X))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,y\<rangle> = eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle>"
      using s1 by simp
    have eqxx_eqxy: "eq_pred(X) \<circ>\<^sub>c \<langle>x,x\<rangle> = eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle>"
      using s2 s3 s9 s10 s11 by simp
    show "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      then have "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<f>" using eq_pred_iff_eq_conv[OF x_type y_type] by simp
      moreover have "eq_pred(X) \<circ>\<^sub>c \<langle>x,x\<rangle> = \<t>" using eq_pred_iff_eq[OF x_type x_type] by simp
      ultimately show False using eqxx_eqxy true_false_distinct by simp
    qed
  qed
  show "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective(m)"
    using eq_pred_sharp_type inj by auto
qed

text \<open>The corollary below corresponds to Corollary 2.6.16 in Halvorson.\<close>
corollary Cantor_X_leq_PX_and_not_iso:
  "X \<le>\<^sub>c powerset(X) \<and> \<not> (X \<cong> powerset(X))"
proof
  obtain m where m_type[type_rule]: "m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>" and m_inj: "injective(m)"
    using Cantors_Positive_Theorem by auto
  have m_type2: "m : X \<rightarrow> powerset(X)" using m_type by (simp add: powerset_def)
  show "X \<le>\<^sub>c powerset(X)"
    unfolding is_smaller_than_def using m_type2 injective_imp_monomorphism[OF m_inj] by auto
  show "\<not> (X \<cong> powerset(X))"
  proof
    assume "X \<cong> powerset(X)"
    then obtain h where h_type: "h : X \<rightarrow> powerset(X)" and h_iso: "isomorphism(h)"
      unfolding is_isomorphic_def by auto
    have h_epi: "epimorphism(h)" using h_iso iso_imp_epi_and_monic by auto
    have h_surj: "surjective(h)" using epi_is_surj[OF h_type h_epi] .
    show False using Cantors_Negative_Theorem h_type h_surj by auto
  qed
qed

corollary Generalized_Cantors_Positive_Theorem:
  assumes Y_not_term: "\<not> terminal_object(Y)"
  assumes Y_not_init: "\<not> initial_object(Y)"
  shows "X \<le>\<^sub>c Y\<^bsup>X\<^esup>"
proof -
  have Omega_leq_Y: "\<Omega> \<le>\<^sub>c Y" using non_init_non_ter_sets[OF Y_not_term Y_not_init] .
  have fact: "\<Omega>\<^bsup>X\<^esup> \<le>\<^sub>c Y\<^bsup>X\<^esup>" using exp_preserves_card2[OF Omega_leq_Y] .
  obtain m where m_type[type_rule]: "m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>" and m_inj: "injective(m)"
    using Cantors_Positive_Theorem by auto
  have X_leq_OmegaX: "X \<le>\<^sub>c \<Omega>\<^bsup>X\<^esup>"
    unfolding is_smaller_than_def using m_type injective_imp_monomorphism[OF m_inj] by auto
  show ?thesis using set_card_transitive[OF X_leq_OmegaX fact] .
qed

corollary Generalized_Cantors_Negative_Theorem:
  assumes X_not_init: "\<not> initial_object(X)"
  assumes Y_not_term: "\<not> terminal_object(Y)"
  shows "\<not> (\<exists>s. s : X \<rightarrow> Y\<^bsup>X\<^esup> \<and> surjective(s))"
proof (rule ccontr)
  assume "\<not> \<not> (\<exists>s. s : X \<rightarrow> Y\<^bsup>X\<^esup> \<and> surjective(s))"
  then obtain s where s_type[type_rule]: "s : X \<rightarrow> Y\<^bsup>X\<^esup>" and s_surj: "surjective(s)" by auto
  have s_epi: "epimorphism(s)" using surjective_is_epimorphism[OF s_surj] .
  obtain m where m_type[type_rule]: "m : Y\<^bsup>X\<^esup> \<rightarrow> X" and m_mono: "monomorphism(m)"
    using epis_give_monos[OF s_type s_epi] by auto

  have X_nonempty: "nonempty(X)"
  proof (rule ccontr)
    assume "\<not> nonempty(X)"
    then have "is_empty(X)" unfolding is_empty_def nonempty_def by auto
    then have "X \<cong> \<emptyset>" using no_el_iff_iso_empty by simp
    then have "initial_object(X)" using iso_empty_initial by simp
    then show False using X_not_init by simp
  qed
  have Omega_nonempty: "nonempty(\<Omega>)" unfolding nonempty_def using true_func_type by auto
  have nonempty_OmegaX: "nonempty(\<Omega>\<^bsup>X\<^esup>)"
    using nonempty_to_nonempty[OF X_nonempty Omega_nonempty] .

  show False
  proof (cases "initial_object(Y)")
    case True
    then have Y_empty: "is_empty(Y)" using no_el_iff_iso_empty initial_iso_empty by auto
    have YX_empty: "Y\<^bsup>X\<^esup> \<cong> \<emptyset>" using empty_to_nonempty[OF X_nonempty Y_empty] .
    then obtain h where h_type[type_rule]: "h : Y\<^bsup>X\<^esup> \<rightarrow> \<emptyset>" and h_iso: "isomorphism(h)"
      unfolding is_isomorphic_def by auto
    have X_empty: "is_empty(X)"
    proof (rule ccontr)
      assume "\<not> is_empty(X)"
      then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" unfolding is_empty_def nonempty_def by auto
      have hs_type[type_rule]: "h \<circ>\<^sub>c s : X \<rightarrow> \<emptyset>" using comp_type[OF s_type h_type] .
      have "(h \<circ>\<^sub>c s) \<circ>\<^sub>c x \<in>\<^sub>c \<emptyset>" by typecheck_cfuncs
      then show False using emptyset_is_empty by auto
    qed
    then have "X \<cong> \<emptyset>" using no_el_iff_iso_empty by simp
    then have "initial_object(X)" using iso_empty_initial by simp
    then show False using X_not_init by simp
  next
    case False
    then have Omega_leq_Y: "\<Omega> \<le>\<^sub>c Y" using non_init_non_ter_sets[OF Y_not_term] by simp
    obtain n where n_type[type_rule]: "n : \<Omega>\<^bsup>X\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>" and n_mono: "monomorphism(n)"
      using exp_preserves_card2[OF Omega_leq_Y] unfolding is_smaller_than_def by auto
    have mn_type[type_rule]: "m \<circ>\<^sub>c n : \<Omega>\<^bsup>X\<^esup> \<rightarrow> X" using comp_type[OF n_type m_type] .
    have codom_dom: "codomain(n) = domain(m)" using n_type m_type unfolding cfunc_type_def by auto
    have mn_mono: "monomorphism(m \<circ>\<^sub>c n)"
      using composition_of_monic_pair_is_monic[OF codom_dom n_mono m_mono] .
    obtain h where h_type[type_rule]: "h : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>" and h_epi: "epimorphism(h)" and h_mn_id: "h \<circ>\<^sub>c (m \<circ>\<^sub>c n) = id(\<Omega>\<^bsup>X\<^esup>)"
      using monos_give_epis[OF mn_type mn_mono nonempty_OmegaX] by auto
    have h_surj: "surjective(h)" using epi_is_surj[OF h_type h_epi] .
    have h_type2: "h : X \<rightarrow> powerset(X)" using h_type by (simp add: powerset_def)
    show False using Cantors_Negative_Theorem h_type2 h_surj by auto
  qed
qed

end
