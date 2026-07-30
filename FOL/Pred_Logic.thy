section \<open>Predicate Logic Functions\<close>

theory Pred_Logic
  imports Nats
begin

subsection \<open>NOT\<close>

text \<open>HOL's @{text THE}-based definition is replaced by reusing @{text characteristic_func}
  directly: the defining pullback square for @{text NOT} is exactly the characteristic-function
  pullback of the monic element @{text "\<f> : \<one> \<rightarrow> \<Omega>"}.\<close>
definition NOT :: "cfunc" where
  "NOT = characteristic_func(\<f>)"

lemma NOT_is_pullback:
  "is_pullback(\<one>, \<one>, \<Omega>, \<Omega>, \<beta>\<^bsub>\<one>\<^esub>, \<t>, \<f>, NOT)"
  unfolding NOT_def
  using characteristic_func_is_pullback[OF false_func_type element_monomorphism[OF false_func_type]] .

lemma NOT_type[type_rule]:
  "NOT : \<Omega> \<rightarrow> \<Omega>"
  using NOT_is_pullback unfolding is_pullback_def by auto

lemma NOT_false_is_true:
  "NOT \<circ>\<^sub>c \<f> = \<t>"
proof -
  have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = NOT \<circ>\<^sub>c \<f>"
    using NOT_is_pullback unfolding is_pullback_def by auto
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = \<t> \<circ>\<^sub>c id(\<one>)" using b1_id by simp
  also have "... = \<t>" using id_right_unit2[OF true_func_type] .
  finally show ?thesis using comm by simp
qed

lemma NOT_true_is_false:
  "NOT \<circ>\<^sub>c \<t> = \<f>"
proof (rule ccontr)
  assume contra: "NOT \<circ>\<^sub>c \<t> \<noteq> \<f>"
  have nt_type[type_rule]: "NOT \<circ>\<^sub>c \<t> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nt_eq_t: "NOT \<circ>\<^sub>c \<t> = \<t>"
    using true_false_only_truth_values[OF nt_type] contra by auto
  have comm_eq: "\<t> \<circ>\<^sub>c id(\<one>) = NOT \<circ>\<^sub>c \<t>"
    using nt_eq_t id_right_unit2[OF true_func_type] by simp
  have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega> \<and> \<t> \<circ>\<^sub>c k = NOT \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> \<f> \<circ>\<^sub>c j = h)"
    using NOT_is_pullback unfolding is_pullback_def by auto
  have spec_case: "id(\<one>) : \<one> \<rightarrow> \<one> \<and> \<t> : \<one> \<rightarrow> \<Omega> \<and> \<t> \<circ>\<^sub>c id(\<one>) = NOT \<circ>\<^sub>c \<t>"
    using comm_eq by (typecheck_cfuncs, auto)
  have ex_j: "\<exists>! j. j : \<one> \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> \<f> \<circ>\<^sub>c j = \<t>"
    using uniq spec_case by blast
  obtain j where j_type: "j : \<one> \<rightarrow> \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>)" and f_j_eq_t: "\<f> \<circ>\<^sub>c j = \<t>"
    using ex_j by auto
  have j_eq: "j = id(\<one>)" using element_of_1[OF j_type] .
  have "\<f> = \<t>" using f_j_eq_t j_eq id_right_unit2[OF false_func_type] by simp
  then show False using true_false_distinct by auto
qed

lemma NOT_is_true_implies_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c p = \<t> \<Longrightarrow> p = \<f>"
  using NOT_true_is_false assms true_false_only_truth_values by fastforce

lemma NOT_is_false_implies_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c p = \<f> \<Longrightarrow> p = \<t>"
  using NOT_false_is_true assms true_false_only_truth_values by fastforce

lemma double_negation:
  "NOT \<circ>\<^sub>c NOT = id(\<Omega>)"
proof (etcs_rule one_separator)
  fix p
  assume p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  show "(NOT \<circ>\<^sub>c NOT) \<circ>\<^sub>c p = id(\<Omega>) \<circ>\<^sub>c p"
  proof (cases "p = \<t>")
    case True
    have s1: "(NOT \<circ>\<^sub>c NOT) \<circ>\<^sub>c p = NOT \<circ>\<^sub>c (NOT \<circ>\<^sub>c p)"
      by (rule sym[OF comp_associative2[OF p_type NOT_type NOT_type]])
    have s2: "NOT \<circ>\<^sub>c p = \<f>" using True NOT_true_is_false by simp
    have s3: "NOT \<circ>\<^sub>c (NOT \<circ>\<^sub>c p) = NOT \<circ>\<^sub>c \<f>" using s2 by simp
    have s4: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
    have s5: "id(\<Omega>) \<circ>\<^sub>c p = p" using id_left_unit2[OF p_type] .
    show ?thesis using s1 s3 s4 s5 True by simp
  next
    case False
    have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values False by auto
    have s1: "(NOT \<circ>\<^sub>c NOT) \<circ>\<^sub>c p = NOT \<circ>\<^sub>c (NOT \<circ>\<^sub>c p)"
      by (rule sym[OF comp_associative2[OF p_type NOT_type NOT_type]])
    have s2: "NOT \<circ>\<^sub>c p = \<t>" using p_eq_f NOT_false_is_true by simp
    have s3: "NOT \<circ>\<^sub>c (NOT \<circ>\<^sub>c p) = NOT \<circ>\<^sub>c \<t>" using s2 by simp
    have s4: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
    have s5: "id(\<Omega>) \<circ>\<^sub>c p = p" using id_left_unit2[OF p_type] .
    show ?thesis using s1 s3 s4 s5 p_eq_f by simp
  qed
qed

subsection \<open>AND\<close>

text \<open>Reuses @{text characteristic_func} on the monic element @{text "\<langle>\<t>,\<t>\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>"},
  exactly as for @{text NOT}.\<close>
definition AND :: "cfunc" where
  "AND = characteristic_func(\<langle>\<t>,\<t>\<rangle>)"

lemma tt_type[type_rule]: "\<langle>\<t>,\<t>\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs

lemma AND_is_pullback:
  "is_pullback(\<one>, \<one>, \<Omega> \<times>\<^sub>c \<Omega>, \<Omega>, \<beta>\<^bsub>\<one>\<^esub>, \<t>, \<langle>\<t>,\<t>\<rangle>, AND)"
  unfolding AND_def
  using characteristic_func_is_pullback[OF tt_type element_monomorphism[OF tt_type]] .

lemma AND_type[type_rule]:
  "AND : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  using AND_is_pullback unfolding is_pullback_def by auto

lemma AND_true_true_is_true:
  "AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
proof -
  have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>"
    using AND_is_pullback unfolding is_pullback_def by auto
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = \<t> \<circ>\<^sub>c id(\<one>)" using b1_id by simp
  also have "... = \<t>" using id_right_unit2[OF true_func_type] .
  finally show ?thesis using comm by simp
qed

lemma AND_false_left_is_false:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<f>"
proof (rule ccontr)
  assume contra: "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> \<noteq> \<f>"
  have fp_type[type_rule]: "\<langle>\<f>,p\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have and_type[type_rule]: "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have and_eq_t: "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<t>"
    using true_false_only_truth_values[OF and_type] contra by auto
  have comm_eq: "\<t> \<circ>\<^sub>c id(\<one>) = AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle>"
    using and_eq_t id_right_unit2[OF true_func_type] by simp
  have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c k = AND \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> \<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = h)"
    using AND_is_pullback unfolding is_pullback_def by auto
  have spec_case: "id(\<one>) : \<one> \<rightarrow> \<one> \<and> \<langle>\<f>,p\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c id(\<one>) = AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle>"
    using comm_eq by (typecheck_cfuncs, auto)
  have ex_j: "\<exists>! j. j : \<one> \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> \<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>\<f>,p\<rangle>"
    using uniq spec_case by blast
  obtain j where j_type: "j : \<one> \<rightarrow> \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>)" and tt_j_eq_fp: "\<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>\<f>,p\<rangle>"
    using ex_j by auto
  have j_eq: "j = id(\<one>)" using element_of_1[OF j_type] .
  have tt_eq_fp: "\<langle>\<t>,\<t>\<rangle> = \<langle>\<f>,p\<rangle>" using tt_j_eq_fp j_eq id_right_unit2[OF tt_type] by simp
  have "\<t> = \<f>" using tt_eq_fp cart_prod_eq2[OF true_func_type true_func_type false_func_type p_type] by auto
  then show False using true_false_distinct by auto
qed

lemma AND_false_right_is_false:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<f>"
proof (rule ccontr)
  assume contra: "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> \<noteq> \<f>"
  have pf_type[type_rule]: "\<langle>p,\<f>\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have and_type[type_rule]: "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have and_eq_t: "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<t>"
    using true_false_only_truth_values[OF and_type] contra by auto
  have comm_eq: "\<t> \<circ>\<^sub>c id(\<one>) = AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle>"
    using and_eq_t id_right_unit2[OF true_func_type] by simp
  have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c k = AND \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> \<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = h)"
    using AND_is_pullback unfolding is_pullback_def by auto
  have spec_case: "id(\<one>) : \<one> \<rightarrow> \<one> \<and> \<langle>p,\<f>\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c id(\<one>) = AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle>"
    using comm_eq by (typecheck_cfuncs, auto)
  have ex_j: "\<exists>! j. j : \<one> \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> \<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<f>\<rangle>"
    using uniq spec_case by blast
  obtain j where j_type: "j : \<one> \<rightarrow> \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>)" and tt_j_eq_pf: "\<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<f>\<rangle>"
    using ex_j by auto
  have j_eq: "j = id(\<one>)" using element_of_1[OF j_type] .
  have tt_eq_pf: "\<langle>\<t>,\<t>\<rangle> = \<langle>p,\<f>\<rangle>" using tt_j_eq_pf j_eq id_right_unit2[OF tt_type] by simp
  have "\<t> = \<f>" using tt_eq_pf cart_prod_eq2[OF true_func_type true_func_type p_type false_func_type] by auto
  then show False using true_false_distinct by auto
qed

lemma AND_commutative:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = AND \<circ>\<^sub>c \<langle>q,p\<rangle>"
proof (cases "p = \<t>")
  case True
  show ?thesis
  proof (cases "q = \<t>")
    case True
    show ?thesis using \<open>p = \<t>\<close> True by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    have "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using \<open>p = \<t>\<close> q_eq_f AND_false_right_is_false[OF true_func_type] by simp
    moreover have "AND \<circ>\<^sub>c \<langle>q,p\<rangle> = \<f>" using \<open>p = \<t>\<close> q_eq_f AND_false_left_is_false[OF true_func_type] by simp
    ultimately show ?thesis by simp
  qed
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  show ?thesis
  proof (cases "q = \<t>")
    case True
    have "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using p_eq_f True AND_false_left_is_false[OF true_func_type] by simp
    moreover have "AND \<circ>\<^sub>c \<langle>q,p\<rangle> = \<f>" using p_eq_f True AND_false_right_is_false[OF true_func_type] by simp
    ultimately show ?thesis by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    show ?thesis using p_eq_f q_eq_f by simp
  qed
qed

lemma AND_idempotent:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p,p\<rangle> = p"
proof (cases "p = \<t>")
  case True
  then show ?thesis using AND_true_true_is_true by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  then show ?thesis using AND_false_right_is_false[OF false_func_type] by simp
qed

lemma AND_associative:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>" and r_type[type_rule]: "r \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = AND \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>"
proof (cases "p = \<t>")
  case p_true: True
  show ?thesis
  proof (cases "q = \<t>")
    case q_true: True
    show ?thesis
    proof (cases "r = \<t>")
      case True
      show ?thesis using p_true q_true True AND_true_true_is_true by simp
    next
      case False
      then have r_eq_f: "r = \<f>" using r_type true_false_only_truth_values by auto
      have lhs: "AND \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = \<f>"
        using p_true q_true r_eq_f AND_true_true_is_true AND_false_right_is_false[OF true_func_type] by simp
      have rhs: "AND \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<f>"
        using p_true q_true r_eq_f AND_false_right_is_false[OF true_func_type] by simp
      show ?thesis using lhs rhs by simp
    qed
  next
    case q_false: False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    have lhs: "AND \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = \<f>"
      using p_true q_eq_f AND_false_right_is_false[OF true_func_type] AND_false_left_is_false[OF r_type] by simp
    have rhs: "AND \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<f>"
      using p_true q_eq_f AND_false_left_is_false[OF r_type] AND_false_right_is_false[OF true_func_type] by simp
    show ?thesis using lhs rhs by simp
  qed
next
  case p_false: False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  have qr_type[type_rule]: "AND \<circ>\<^sub>c \<langle>q,r\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have lhs: "AND \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = \<f>"
    using p_eq_f AND_false_left_is_false[OF q_type] AND_false_left_is_false[OF r_type] by simp
  have rhs: "AND \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<f>"
    using p_eq_f AND_false_left_is_false[OF qr_type] by simp
  show ?thesis using lhs rhs by simp
qed

lemma AND_complementary:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p, NOT \<circ>\<^sub>c p\<rangle> = \<f>"
proof (cases "p = \<t>")
  case True
  then show ?thesis using NOT_true_is_false AND_false_right_is_false[OF true_func_type] by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  then show ?thesis using NOT_false_is_true AND_false_left_is_false[OF true_func_type] by simp
qed

lemma AND_true_imp_both_true:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  assumes and_true: "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>"
  shows "p = \<t> \<and> q = \<t>"
proof (cases "p = \<t>")
  case True
  show ?thesis
  proof (cases "q = \<t>")
    case True
    show ?thesis using \<open>p = \<t>\<close> True by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    have "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using \<open>p = \<t>\<close> q_eq_f AND_false_right_is_false[OF true_func_type] by simp
    then show ?thesis using and_true true_false_distinct by simp
  qed
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  then have "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using AND_false_left_is_false[OF q_type] by simp
  then show ?thesis using and_true true_false_distinct by simp
qed

subsection \<open>NOR\<close>

definition NOR :: "cfunc" where
  "NOR = characteristic_func(\<langle>\<f>,\<f>\<rangle>)"

lemma ff_type[type_rule]: "\<langle>\<f>,\<f>\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs

lemma NOR_is_pullback:
  "is_pullback(\<one>, \<one>, \<Omega> \<times>\<^sub>c \<Omega>, \<Omega>, \<beta>\<^bsub>\<one>\<^esub>, \<t>, \<langle>\<f>,\<f>\<rangle>, NOR)"
  unfolding NOR_def
  using characteristic_func_is_pullback[OF ff_type element_monomorphism[OF ff_type]] .

lemma NOR_type[type_rule]:
  "NOR : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  using NOR_is_pullback unfolding is_pullback_def by auto

lemma NOR_false_false_is_true:
  "NOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>"
proof -
  have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = NOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>"
    using NOR_is_pullback unfolding is_pullback_def by auto
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = \<t> \<circ>\<^sub>c id(\<one>)" using b1_id by simp
  also have "... = \<t>" using id_right_unit2[OF true_func_type] .
  finally show ?thesis using comm by simp
qed

lemma NOR_left_true_is_false:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<f>"
proof (rule ccontr)
  assume contra: "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> \<noteq> \<f>"
  have tp_type[type_rule]: "\<langle>\<t>,p\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nor_type[type_rule]: "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nor_eq_t: "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t>"
    using true_false_only_truth_values[OF nor_type] contra by auto
  have comm_eq: "\<t> \<circ>\<^sub>c id(\<one>) = NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle>"
    using nor_eq_t id_right_unit2[OF true_func_type] by simp
  have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c k = NOR \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = h)"
    using NOR_is_pullback unfolding is_pullback_def by auto
  have spec_case: "id(\<one>) : \<one> \<rightarrow> \<one> \<and> \<langle>\<t>,p\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c id(\<one>) = NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle>"
    using comm_eq by (typecheck_cfuncs, auto)
  have ex_j: "\<exists>! j. j : \<one> \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>\<t>,p\<rangle>"
    using uniq spec_case by blast
  obtain j where j_type: "j : \<one> \<rightarrow> \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>)" and ff_j_eq_tp: "\<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>\<t>,p\<rangle>"
    using ex_j by auto
  have j_eq: "j = id(\<one>)" using element_of_1[OF j_type] .
  have ff_eq_tp: "\<langle>\<f>,\<f>\<rangle> = \<langle>\<t>,p\<rangle>" using ff_j_eq_tp j_eq id_right_unit2[OF ff_type] by simp
  have "\<f> = \<t>" using ff_eq_tp cart_prod_eq2[OF false_func_type false_func_type true_func_type p_type] by auto
  then show False using true_false_distinct by auto
qed

lemma NOR_right_true_is_false:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<f>"
proof (rule ccontr)
  assume contra: "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> \<noteq> \<f>"
  have pt_type[type_rule]: "\<langle>p,\<t>\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nor_type[type_rule]: "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nor_eq_t: "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t>"
    using true_false_only_truth_values[OF nor_type] contra by auto
  have comm_eq: "\<t> \<circ>\<^sub>c id(\<one>) = NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle>"
    using nor_eq_t id_right_unit2[OF true_func_type] by simp
  have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c k = NOR \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = h)"
    using NOR_is_pullback unfolding is_pullback_def by auto
  have spec_case: "id(\<one>) : \<one> \<rightarrow> \<one> \<and> \<langle>p,\<t>\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c id(\<one>) = NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle>"
    using comm_eq by (typecheck_cfuncs, auto)
  have ex_j: "\<exists>! j. j : \<one> \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<t>\<rangle>"
    using uniq spec_case by blast
  obtain j where j_type: "j : \<one> \<rightarrow> \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>)" and ff_j_eq_pt: "\<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<t>\<rangle>"
    using ex_j by auto
  have j_eq: "j = id(\<one>)" using element_of_1[OF j_type] .
  have ff_eq_pt: "\<langle>\<f>,\<f>\<rangle> = \<langle>p,\<t>\<rangle>" using ff_j_eq_pt j_eq id_right_unit2[OF ff_type] by simp
  have "\<f> = \<t>" using ff_eq_pt cart_prod_eq2[OF false_func_type false_func_type p_type true_func_type] by auto
  then show False using true_false_distinct by auto
qed

lemma NOR_true_implies_both_false:
  assumes X_nonempty: "nonempty(X)" and Y_nonempty: "nonempty(Y)"
  assumes P_type[type_rule]: "P : X \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : Y \<rightarrow> \<Omega>"
  assumes NOR_true: "NOR \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<and> Q = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
proof -
  have pq_type[type_rule]: "P \<times>\<^sub>f Q : X \<times>\<^sub>c Y \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have bxy_type[type_rule]: "\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> : X \<times>\<^sub>c Y \<rightarrow> \<one>" by typecheck_cfuncs
  have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c k = NOR \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = h)"
    using NOR_is_pullback unfolding is_pullback_def by auto
  have spec_case: "\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> : X \<times>\<^sub>c Y \<rightarrow> \<one> \<and> P \<times>\<^sub>f Q : X \<times>\<^sub>c Y \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega> \<and> \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> = NOR \<circ>\<^sub>c (P \<times>\<^sub>f Q)"
    using NOR_true by (typecheck_cfuncs, auto)
  have ex_j: "\<exists>! j. j : X \<times>\<^sub>c Y \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<and> \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = P \<times>\<^sub>f Q"
    using uniq spec_case by blast
  obtain z where z_type[type_rule]: "z : X \<times>\<^sub>c Y \<rightarrow> \<one>" and z_pq: "\<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c z = P \<times>\<^sub>f Q"
    using ex_j by auto
  have z_eq_b: "z = \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>" using z_type terminal_func_unique by auto
  have pq_eq: "P \<times>\<^sub>f Q = \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
    using z_pq z_eq_b by simp
  have pq_eq2: "P \<times>\<^sub>f Q = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>\<rangle>"
    using pq_eq by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have fb_eq1: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj(X, Y)"
  proof -
    have e1: "\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, Y)"
      using terminal_func_comp[OF left_cart_proj_type] by (rule sym)
    have e2: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, Y))" using e1 by simp
    show ?thesis
      using e2 comp_associative2[OF left_cart_proj_type terminal_func_type false_func_type] by simp
  qed
  have fb_eq2: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c right_cart_proj(X, Y)"
  proof -
    have e1: "\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> = \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c right_cart_proj(X, Y)"
      using terminal_func_comp[OF right_cart_proj_type] by (rule sym)
    have e2: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c right_cart_proj(X, Y))" using e1 by simp
    show ?thesis
      using e2 comp_associative2[OF right_cart_proj_type terminal_func_type false_func_type] by simp
  qed
  have pq_eq3: "P \<times>\<^sub>f Q = \<langle>(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj(X, Y), (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c right_cart_proj(X, Y)\<rangle>"
    using pq_eq2 fb_eq1 fb_eq2 by simp
  have pq_eq4: "\<langle>P \<circ>\<^sub>c left_cart_proj(X, Y), Q \<circ>\<^sub>c right_cart_proj(X, Y)\<rangle>
      = \<langle>(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj(X, Y), (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c right_cart_proj(X, Y)\<rangle>"
    using pq_eq3 cfunc_cross_prod_def2[OF P_type Q_type] by simp
  have a_type[type_rule]: "P \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" by typecheck_cfuncs
  have b_type[type_rule]: "Q \<circ>\<^sub>c right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" by typecheck_cfuncs
  have c_type[type_rule]: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" by typecheck_cfuncs
  have d_type[type_rule]: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" by typecheck_cfuncs
  have peq_qeq: "P \<circ>\<^sub>c left_cart_proj(X, Y) = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj(X, Y)
      \<and> Q \<circ>\<^sub>c right_cart_proj(X, Y) = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c right_cart_proj(X, Y)"
    using pq_eq4 cart_prod_eq2[OF a_type b_type c_type d_type] by simp
  have lp_epi: "epimorphism(left_cart_proj(X,Y))" using nonempty_right_imp_left_proj_epimorphism[OF Y_nonempty] .
  have rp_epi: "epimorphism(right_cart_proj(X,Y))" using nonempty_left_imp_right_proj_epimorphism[OF X_nonempty] .
  have fb_x_type[type_rule]: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" by typecheck_cfuncs
  have fb_y_type[type_rule]: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<Omega>" by typecheck_cfuncs
  have lp_forall: "\<forall> g h A. g : X \<rightarrow> A \<and> h : X \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c left_cart_proj(X,Y) = h \<circ>\<^sub>c left_cart_proj(X,Y) \<longrightarrow> g = h)"
    using epimorphism_def3[OF left_cart_proj_type] lp_epi by simp
  have rp_forall: "\<forall> g h A. g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c right_cart_proj(X,Y) = h \<circ>\<^sub>c right_cart_proj(X,Y) \<longrightarrow> g = h)"
    using epimorphism_def3[OF right_cart_proj_type] rp_epi by simp
  have p_eq: "P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
    using lp_forall P_type fb_x_type peq_qeq by blast
  have q_eq: "Q = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using rp_forall Q_type fb_y_type peq_qeq by blast
  show ?thesis using p_eq q_eq by simp
qed

lemma NOR_true_implies_neither_true:
  assumes X_nonempty: "nonempty(X)" and Y_nonempty: "nonempty(Y)"
  assumes P_type[type_rule]: "P : X \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : Y \<rightarrow> \<Omega>"
  assumes NOR_true: "NOR \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "\<not> (P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<or> Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
proof -
  have both_false: "P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<and> Q = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using NOR_true_implies_both_false[OF X_nonempty Y_nonempty P_type Q_type NOR_true] .
  have p_eq: "P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>" using both_false by simp
  have q_eq: "Q = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" using both_false by simp
  show ?thesis
  proof
    assume "P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<or> Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    then show False
    proof
      assume p_true: "P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
      obtain x where x_type: "x : \<one> \<rightarrow> X" using X_nonempty nonempty_def by auto
      have fb_eq: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>" using p_eq p_true by simp
      have step0: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x" using fb_eq by simp
      have s1: "\<f> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)"
        using step0 comp_associative2[OF x_type terminal_func_type false_func_type]
              comp_associative2[OF x_type terminal_func_type true_func_type] by simp
      have bx_eq: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = id(\<one>)" using terminal_func_comp_elem[OF x_type] .
      have s2: "\<f> \<circ>\<^sub>c id(\<one>) = \<t> \<circ>\<^sub>c id(\<one>)" using s1 bx_eq by simp
      have "\<f> = \<t>" using s2 id_right_unit2[OF false_func_type] id_right_unit2[OF true_func_type] by simp
      then show False using true_false_distinct by auto
    next
      assume q_true: "Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
      obtain y where y_type: "y : \<one> \<rightarrow> Y" using Y_nonempty nonempty_def by auto
      have fb_eq: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" using q_eq q_true by simp
      have step0: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y" using fb_eq by simp
      have s1: "\<f> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y)"
        using step0 comp_associative2[OF y_type terminal_func_type false_func_type]
              comp_associative2[OF y_type terminal_func_type true_func_type] by simp
      have by_eq: "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y = id(\<one>)" using terminal_func_comp_elem[OF y_type] .
      have s2: "\<f> \<circ>\<^sub>c id(\<one>) = \<t> \<circ>\<^sub>c id(\<one>)" using s1 by_eq by simp
      have "\<f> = \<t>" using s2 id_right_unit2[OF false_func_type] id_right_unit2[OF true_func_type] by simp
      then show False using true_false_distinct by auto
    qed
  qed
qed

subsection \<open>OR\<close>

text \<open>HOL defines @{text OR} via a fresh pullback over the 3-element coproduct
  @{text "\<one> \<Coprod> (\<one> \<Coprod> \<one>)"}, requiring a lengthy injective-witness case-bash
  (@{text pre_OR_injective}, @{text set_three}). Since HOL itself proves @{text NOT_NOR_is_OR}
  (@{text "OR = NOT \<circ>\<^sub>c NOR"}) as a corollary, we instead take that identity as the DEFINITION,
  reusing the already-established @{text NOT}/@{text NOR}, and recover every HOL lemma about
  @{text OR} directly from the already-proven @{text NOT}/@{text NOR} facts -- entirely avoiding
  the coproduct injective-witness construction. This pattern (compositional definition instead of
  a fresh pullback, matching an identity HOL itself proves as a corollary) is used again below for
  @{text XOR}, @{text NAND}, @{text IFF}, and @{text IMPLIES}.\<close>
definition OR :: "cfunc" where
  "OR = NOT \<circ>\<^sub>c NOR"

lemma OR_type[type_rule]:
  "OR : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding OR_def by typecheck_cfuncs

lemma NOT_NOR_is_OR:
  "OR = NOT \<circ>\<^sub>c NOR"
  unfolding OR_def by simp

lemma OR_true_left_is_true:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t>"
proof -
  have tp_type[type_rule]: "\<langle>\<t>,p\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s1: "OR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = NOT \<circ>\<^sub>c (NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle>)"
    unfolding OR_def by (rule sym[OF comp_associative2[OF tp_type NOR_type NOT_type]])
  have s2: "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<f>" using NOR_left_true_is_false[OF p_type] .
  show ?thesis using s1 s2 NOT_false_is_true by simp
qed

lemma OR_true_right_is_true:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t>"
proof -
  have pt_type[type_rule]: "\<langle>p,\<t>\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s1: "OR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = NOT \<circ>\<^sub>c (NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle>)"
    unfolding OR_def by (rule sym[OF comp_associative2[OF pt_type NOR_type NOT_type]])
  have s2: "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<f>" using NOR_right_true_is_false[OF p_type] .
  show ?thesis using s1 s2 NOT_false_is_true by simp
qed

lemma OR_false_false_is_false:
  "OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<f>"
proof -
  have s1: "OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = NOT \<circ>\<^sub>c (NOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>)"
    unfolding OR_def by (rule sym[OF comp_associative2[OF ff_type NOR_type NOT_type]])
  have s2: "NOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>" using NOR_false_false_is_true .
  show ?thesis using s1 s2 NOT_true_is_false by simp
qed

lemma OR_true_implies_one_is_true:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  assumes or_true: "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>"
  shows "p = \<t> \<or> q = \<t>"
proof (rule ccontr)
  assume "\<not> (p = \<t> \<or> q = \<t>)"
  then have p_eq_f: "p = \<f>" and q_eq_f: "q = \<f>"
    using p_type q_type true_false_only_truth_values by auto
  then have "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using OR_false_false_is_false by simp
  then show False using or_true true_false_distinct by simp
qed

lemma OR_commutative:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = OR \<circ>\<^sub>c \<langle>q,p\<rangle>"
proof (cases "p = \<t>")
  case True
  show ?thesis
  proof (cases "q = \<t>")
    case True
    show ?thesis using \<open>p = \<t>\<close> True by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    show ?thesis using \<open>p = \<t>\<close> q_eq_f OR_true_left_is_true[OF false_func_type] OR_true_right_is_true[OF false_func_type] by simp
  qed
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  show ?thesis
  proof (cases "q = \<t>")
    case True
    show ?thesis using p_eq_f True OR_true_right_is_true[OF false_func_type] OR_true_left_is_true[OF false_func_type] by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    show ?thesis using p_eq_f q_eq_f by simp
  qed
qed

lemma OR_idempotent:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p,p\<rangle> = p"
proof (cases "p = \<t>")
  case True
  then show ?thesis using OR_true_left_is_true[OF true_func_type] by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  then show ?thesis using OR_false_false_is_false by simp
qed

lemma OR_associative:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>" and r_type[type_rule]: "r \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = OR \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>"
proof (cases "p = \<t>")
  case p_true: True
  have qr_type[type_rule]: "OR \<circ>\<^sub>c \<langle>q,r\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have lhs: "OR \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = \<t>"
    using p_true OR_true_left_is_true[OF q_type] OR_true_left_is_true[OF r_type] by simp
  have rhs: "OR \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<t>"
    using p_true OR_true_left_is_true[OF qr_type] by simp
  show ?thesis using lhs rhs by simp
next
  case p_false: False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  show ?thesis
  proof (cases "q = \<t>")
    case q_true: True
    have lhs: "OR \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = \<t>"
      using p_eq_f q_true OR_true_right_is_true[OF false_func_type] OR_true_left_is_true[OF r_type] by simp
    have rhs: "OR \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<t>"
      using p_eq_f q_true OR_true_left_is_true[OF r_type] OR_true_right_is_true[OF false_func_type] by simp
    show ?thesis using lhs rhs by simp
  next
    case q_false: False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    show ?thesis
    proof (cases "r = \<t>")
      case True
      have lhs: "OR \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle> = \<t>"
        using p_eq_f q_eq_f True OR_false_false_is_false OR_true_right_is_true[OF false_func_type] by simp
      have rhs: "OR \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<t>"
        using p_eq_f q_eq_f True OR_true_right_is_true[OF false_func_type] by simp
      show ?thesis using lhs rhs by simp
    next
      case False
      then have r_eq_f: "r = \<f>" using r_type true_false_only_truth_values by auto
      show ?thesis using p_eq_f q_eq_f r_eq_f OR_false_false_is_false by simp
    qed
  qed
qed

lemma OR_complementary:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p, NOT \<circ>\<^sub>c p\<rangle> = \<t>"
proof (cases "p = \<t>")
  case True
  then have "NOT \<circ>\<^sub>c p = \<f>" using NOT_true_is_false by simp
  then show ?thesis using True OR_true_left_is_true[OF false_func_type] by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  then have "NOT \<circ>\<^sub>c p = \<t>" using NOT_false_is_true by simp
  then show ?thesis using p_eq_f OR_true_right_is_true[OF false_func_type] by simp
qed

subsection \<open>XOR\<close>

text \<open>Compositional definition (matching @{text "p XOR q = (p OR q) AND NOT(p AND q)"}), again
  avoiding a fresh pullback over @{text "\<one> \<Coprod> \<one>"} and its injective-witness case-bash.\<close>
definition XOR :: "cfunc" where
  "XOR = AND \<circ>\<^sub>c \<langle>OR, NOT \<circ>\<^sub>c AND\<rangle>"

lemma XOR_type[type_rule]:
  "XOR : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding XOR_def by typecheck_cfuncs

lemma XOR_eval:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "XOR \<circ>\<^sub>c \<langle>p,q\<rangle> = AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>p,q\<rangle>)\<rangle>"
proof -
  have pq_type[type_rule]: "\<langle>p,q\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have or_notand_type[type_rule]: "\<langle>OR, NOT \<circ>\<^sub>c AND\<rangle> : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s1: "XOR \<circ>\<^sub>c \<langle>p,q\<rangle> = AND \<circ>\<^sub>c (\<langle>OR, NOT \<circ>\<^sub>c AND\<rangle> \<circ>\<^sub>c \<langle>p,q\<rangle>)"
    unfolding XOR_def by (rule sym[OF comp_associative2[OF pq_type or_notand_type AND_type]])
  have s2: "\<langle>OR, NOT \<circ>\<^sub>c AND\<rangle> \<circ>\<^sub>c \<langle>p,q\<rangle> = \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, (NOT \<circ>\<^sub>c AND) \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have s3: "(NOT \<circ>\<^sub>c AND) \<circ>\<^sub>c \<langle>p,q\<rangle> = NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>p,q\<rangle>)"
    by (rule sym[OF comp_associative2[OF pq_type AND_type NOT_type]])
  show ?thesis using s1 s2 s3 by simp
qed

lemma XOR_only_true_left_is_true:
  "XOR \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<t>"
proof -
  have s1: "XOR \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle>, NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle>)\<rangle>"
    using XOR_eval[OF true_func_type false_func_type] .
  have s2: "OR \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<t>" using OR_true_left_is_true[OF false_func_type] .
  have s3: "AND \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<f>" using AND_false_right_is_false[OF true_func_type] .
  have s4: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
  show ?thesis using s1 s2 s3 s4 AND_true_true_is_true by simp
qed

lemma XOR_only_true_right_is_true:
  "XOR \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<t>"
proof -
  have s1: "XOR \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle>, NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle>)\<rangle>"
    using XOR_eval[OF false_func_type true_func_type] .
  have s2: "OR \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<t>" using OR_true_right_is_true[OF false_func_type] .
  have s3: "AND \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<f>" using AND_false_left_is_false[OF true_func_type] .
  have s4: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
  show ?thesis using s1 s2 s3 s4 AND_true_true_is_true by simp
qed

lemma XOR_false_false_is_false:
  "XOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<f>"
proof -
  have s1: "XOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>, NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>)\<rangle>"
    using XOR_eval[OF false_func_type false_func_type] .
  have s2: "OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<f>" using OR_false_false_is_false .
  have nt_type[type_rule]: "NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>) \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  show ?thesis using s1 s2 AND_false_left_is_false[OF nt_type] by simp
qed

lemma XOR_true_true_is_false:
  "XOR \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<f>"
proof -
  have s1: "XOR \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>, NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>)\<rangle>"
    using XOR_eval[OF true_func_type true_func_type] .
  have s2: "AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>" using AND_true_true_is_true .
  have s3: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
  have or_tt_type[type_rule]: "OR \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  show ?thesis using s1 s2 s3 AND_false_right_is_false[OF or_tt_type] by simp
qed

subsection \<open>NAND\<close>

text \<open>Compositional definition (@{text "NAND = NOT \<circ>\<^sub>c AND"}), matching HOL's own
  @{text NOT_AND_is_NAND} identity.\<close>
definition NAND :: "cfunc" where
  "NAND = NOT \<circ>\<^sub>c AND"

lemma NAND_type[type_rule]:
  "NAND : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding NAND_def by typecheck_cfuncs

lemma NOT_AND_is_NAND:
  "NAND = NOT \<circ>\<^sub>c AND"
  unfolding NAND_def by simp

lemma NAND_eval:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "NAND \<circ>\<^sub>c \<langle>p,q\<rangle> = NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>p,q\<rangle>)"
proof -
  have pq_type[type_rule]: "\<langle>p,q\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  show ?thesis unfolding NAND_def by (rule sym[OF comp_associative2[OF pq_type AND_type NOT_type]])
qed

lemma NAND_left_false_is_true:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "NAND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<t>"
proof -
  have s1: "NAND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle>)" using NAND_eval[OF false_func_type p_type] .
  have s2: "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<f>" using AND_false_left_is_false[OF p_type] .
  show ?thesis using s1 s2 NOT_false_is_true by simp
qed

lemma NAND_right_false_is_true:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "NAND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<t>"
proof -
  have s1: "NAND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle>)" using NAND_eval[OF p_type false_func_type] .
  have s2: "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<f>" using AND_false_right_is_false[OF p_type] .
  show ?thesis using s1 s2 NOT_false_is_true by simp
qed

lemma NAND_true_true_is_false:
  "NAND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<f>"
proof -
  have s1: "NAND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>)" using NAND_eval[OF true_func_type true_func_type] .
  have s2: "AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>" using AND_true_true_is_true .
  show ?thesis using s1 s2 NOT_true_is_false by simp
qed

lemma NAND_true_implies_one_is_false:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  assumes nand_true: "NAND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>"
  shows "p = \<f> \<or> q = \<f>"
proof (rule ccontr)
  assume "\<not> (p = \<f> \<or> q = \<f>)"
  then have p_eq_t: "p = \<t>" and q_eq_t: "q = \<t>"
    using p_type q_type true_false_only_truth_values by auto
  then have "NAND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using NAND_true_true_is_false by simp
  then show False using nand_true true_false_distinct by simp
qed

lemma NAND_not_idempotent:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>"
  shows "NAND \<circ>\<^sub>c \<langle>p,p\<rangle> = NOT \<circ>\<^sub>c p"
proof (cases "p = \<t>")
  case True
  then show ?thesis using NAND_true_true_is_false NOT_true_is_false by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  then show ?thesis using NAND_right_false_is_true[OF false_func_type] NOT_false_is_true by simp
qed

subsection \<open>IFF\<close>

text \<open>Compositional definition (@{text "p IFF q = (p AND q) OR (NOT p AND NOT q)"}), avoiding a
  fresh pullback over @{text "\<one> \<Coprod> \<one>"}.\<close>
definition IFF :: "cfunc" where
  "IFF = OR \<circ>\<^sub>c \<langle>AND, AND \<circ>\<^sub>c (NOT \<times>\<^sub>f NOT)\<rangle>"

lemma IFF_type[type_rule]:
  "IFF : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding IFF_def by typecheck_cfuncs

lemma IFF_eval:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "IFF \<circ>\<^sub>c \<langle>p,q\<rangle> = OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle>\<rangle>"
proof -
  have pq_type[type_rule]: "\<langle>p,q\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have and_nn_type[type_rule]: "\<langle>AND, AND \<circ>\<^sub>c (NOT \<times>\<^sub>f NOT)\<rangle> : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nn_type[type_rule]: "NOT \<times>\<^sub>f NOT : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s1: "IFF \<circ>\<^sub>c \<langle>p,q\<rangle> = OR \<circ>\<^sub>c (\<langle>AND, AND \<circ>\<^sub>c (NOT \<times>\<^sub>f NOT)\<rangle> \<circ>\<^sub>c \<langle>p,q\<rangle>)"
    unfolding IFF_def by (rule sym[OF comp_associative2[OF pq_type and_nn_type OR_type]])
  have s2: "\<langle>AND, AND \<circ>\<^sub>c (NOT \<times>\<^sub>f NOT)\<rangle> \<circ>\<^sub>c \<langle>p,q\<rangle> = \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, (AND \<circ>\<^sub>c (NOT \<times>\<^sub>f NOT)) \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have s3: "(AND \<circ>\<^sub>c (NOT \<times>\<^sub>f NOT)) \<circ>\<^sub>c \<langle>p,q\<rangle> = AND \<circ>\<^sub>c ((NOT \<times>\<^sub>f NOT) \<circ>\<^sub>c \<langle>p,q\<rangle>)"
    by (rule sym[OF comp_associative2[OF pq_type nn_type AND_type]])
  have s4: "(NOT \<times>\<^sub>f NOT) \<circ>\<^sub>c \<langle>p,q\<rangle> = \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle>"
    by (rule cfunc_cross_prod_comp_cfunc_prod[OF p_type q_type NOT_type NOT_type])
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma IFF_true_true_is_true:
  "IFF \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
proof -
  have s1: "IFF \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle>, AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, NOT \<circ>\<^sub>c \<t>\<rangle>\<rangle>"
    using IFF_eval[OF true_func_type true_func_type] .
  have s2: "AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>" using AND_true_true_is_true .
  have and_nt_type[type_rule]: "AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, NOT \<circ>\<^sub>c \<t>\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  show ?thesis using s1 s2 OR_true_left_is_true[OF and_nt_type] by simp
qed

lemma IFF_false_false_is_true:
  "IFF \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>"
proof -
  have s1: "IFF \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle>, AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, NOT \<circ>\<^sub>c \<f>\<rangle>\<rangle>"
    using IFF_eval[OF false_func_type false_func_type] .
  have s2: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
  have s3: "AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, NOT \<circ>\<^sub>c \<f>\<rangle> = \<t>" using s2 AND_true_true_is_true by simp
  have and_ff_type[type_rule]: "AND \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  show ?thesis using s1 s3 OR_true_right_is_true[OF and_ff_type] by simp
qed

lemma IFF_true_false_is_false:
  "IFF \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<f>"
proof -
  have s1: "IFF \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle>, AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, NOT \<circ>\<^sub>c \<f>\<rangle>\<rangle>"
    using IFF_eval[OF true_func_type false_func_type] .
  have s2: "AND \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<f>" using AND_false_right_is_false[OF true_func_type] .
  have s3: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
  have nf_type[type_rule]: "NOT \<circ>\<^sub>c \<f> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s4: "AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, NOT \<circ>\<^sub>c \<f>\<rangle> = \<f>" using s3 AND_false_left_is_false[OF nf_type] by simp
  show ?thesis using s1 s2 s4 OR_false_false_is_false by simp
qed

lemma IFF_false_true_is_false:
  "IFF \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<f>"
proof -
  have s1: "IFF \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle>, AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, NOT \<circ>\<^sub>c \<t>\<rangle>\<rangle>"
    using IFF_eval[OF false_func_type true_func_type] .
  have s2: "AND \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<f>" using AND_false_left_is_false[OF true_func_type] .
  have s3: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
  have nf_type[type_rule]: "NOT \<circ>\<^sub>c \<f> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s4: "AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, NOT \<circ>\<^sub>c \<t>\<rangle> = \<f>" using s3 AND_false_right_is_false[OF nf_type] by simp
  show ?thesis using s1 s2 s4 OR_false_false_is_false by simp
qed

lemma NOT_IFF_is_XOR:
  "NOT \<circ>\<^sub>c IFF = XOR"
proof (etcs_rule one_separator)
  fix x
  assume x_type[type_rule]: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>"
  obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>" and x_def: "x = \<langle>p,q\<rangle>"
    using cart_prod_decomp[OF x_type] by blast
  have s1: "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = NOT \<circ>\<^sub>c (IFF \<circ>\<^sub>c x)"
    by (rule sym[OF comp_associative2[OF x_type IFF_type NOT_type]])
  show "(NOT \<circ>\<^sub>c IFF) \<circ>\<^sub>c x = XOR \<circ>\<^sub>c x"
  proof (cases "p = \<t>")
    case p_true: True
    show ?thesis
    proof (cases "q = \<t>")
      case True
      have s2: "IFF \<circ>\<^sub>c x = \<t>" using p_true True IFF_true_true_is_true x_def by simp
      have s4: "XOR \<circ>\<^sub>c x = \<f>" using p_true True XOR_true_true_is_false x_def by simp
      show ?thesis using s1 s2 s4 NOT_true_is_false by simp
    next
      case False
      then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
      have s2: "IFF \<circ>\<^sub>c x = \<f>" using p_true q_eq_f IFF_true_false_is_false x_def by simp
      have s4: "XOR \<circ>\<^sub>c x = \<t>" using p_true q_eq_f XOR_only_true_left_is_true x_def by simp
      show ?thesis using s1 s2 s4 NOT_false_is_true by simp
    qed
  next
    case False
    then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
    show ?thesis
    proof (cases "q = \<t>")
      case True
      have s2: "IFF \<circ>\<^sub>c x = \<f>" using p_eq_f True IFF_false_true_is_false x_def by simp
      have s4: "XOR \<circ>\<^sub>c x = \<t>" using p_eq_f True XOR_only_true_right_is_true x_def by simp
      show ?thesis using s1 s2 s4 NOT_false_is_true by simp
    next
      case False
      then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
      have s2: "IFF \<circ>\<^sub>c x = \<t>" using p_eq_f q_eq_f IFF_false_false_is_true x_def by simp
      have s4: "XOR \<circ>\<^sub>c x = \<f>" using p_eq_f q_eq_f XOR_false_false_is_false x_def by simp
      show ?thesis using s1 s2 s4 NOT_true_is_false by simp
    qed
  qed
qed

subsection \<open>IMPLIES\<close>

text \<open>Compositional definition (@{text "p IMPLIES q = NOT(p) OR q"}), matching HOL's own
  @{text IMPLIES_is_OR_NOT_id} identity and avoiding a fresh pullback over
  @{text "\<one> \<Coprod> (\<one> \<Coprod> \<one>)"}.\<close>
definition IMPLIES :: "cfunc" where
  "IMPLIES = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id(\<Omega>))"

lemma IMPLIES_type[type_rule]:
  "IMPLIES : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  unfolding IMPLIES_def by typecheck_cfuncs

lemma IMPLIES_is_OR_NOT_id:
  "IMPLIES = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id(\<Omega>))"
  unfolding IMPLIES_def by simp

lemma IMPLIES_eval:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "IMPLIES \<circ>\<^sub>c \<langle>p,q\<rangle> = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, q\<rangle>"
proof -
  have pq_type[type_rule]: "\<langle>p,q\<rangle> \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nid_type[type_rule]: "NOT \<times>\<^sub>f id(\<Omega>) : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s1: "IMPLIES \<circ>\<^sub>c \<langle>p,q\<rangle> = OR \<circ>\<^sub>c ((NOT \<times>\<^sub>f id(\<Omega>)) \<circ>\<^sub>c \<langle>p,q\<rangle>)"
    unfolding IMPLIES_def by (rule sym[OF comp_associative2[OF pq_type nid_type OR_type]])
  have s2: "(NOT \<times>\<^sub>f id(\<Omega>)) \<circ>\<^sub>c \<langle>p,q\<rangle> = \<langle>NOT \<circ>\<^sub>c p, id(\<Omega>) \<circ>\<^sub>c q\<rangle>"
    by (rule cfunc_cross_prod_comp_cfunc_prod[OF p_type q_type NOT_type id_type])
  have s3: "id(\<Omega>) \<circ>\<^sub>c q = q" using id_left_unit2[OF q_type] .
  show ?thesis using s1 s2 s3 by simp
qed

lemma IMPLIES_true_true_is_true:
  "IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
proof -
  have s1: "IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, \<t>\<rangle>" using IMPLIES_eval[OF true_func_type true_func_type] .
  have s2: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
  show ?thesis using s1 s2 OR_true_right_is_true[OF false_func_type] by simp
qed

lemma IMPLIES_false_true_is_true:
  "IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = \<t>"
proof -
  have s1: "IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<t>\<rangle> = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, \<t>\<rangle>" using IMPLIES_eval[OF false_func_type true_func_type] .
  have s2: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
  show ?thesis using s1 s2 OR_true_left_is_true[OF true_func_type] by simp
qed

lemma IMPLIES_false_false_is_true:
  "IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>"
proof -
  have s1: "IMPLIES \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<f>, \<f>\<rangle>" using IMPLIES_eval[OF false_func_type false_func_type] .
  have s2: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
  show ?thesis using s1 s2 OR_true_left_is_true[OF false_func_type] by simp
qed

lemma IMPLIES_true_false_is_false:
  "IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = \<f>"
proof -
  have s1: "IMPLIES \<circ>\<^sub>c \<langle>\<t>,\<f>\<rangle> = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c \<t>, \<f>\<rangle>" using IMPLIES_eval[OF true_func_type false_func_type] .
  have s2: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
  show ?thesis using s1 s2 OR_false_false_is_false by simp
qed

lemma IMPLIES_false_is_true_false:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  assumes implies_false: "IMPLIES \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>"
  shows "p = \<t> \<and> q = \<f>"
proof (cases "p = \<t>")
  case True
  show ?thesis
  proof (cases "q = \<f>")
    case True
    show ?thesis using \<open>p = \<t>\<close> True by simp
  next
    case False
    then have q_eq_t: "q = \<t>" using q_type true_false_only_truth_values by auto
    then have "IMPLIES \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>" using \<open>p = \<t>\<close> IMPLIES_true_true_is_true by simp
    then show ?thesis using implies_false true_false_distinct by simp
  qed
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  show ?thesis
  proof (cases "q = \<t>")
    case True
    then have "IMPLIES \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>" using p_eq_f IMPLIES_false_true_is_true by simp
    then show ?thesis using implies_false true_false_distinct by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    then have "IMPLIES \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>" using p_eq_f IMPLIES_false_false_is_true by simp
    then show ?thesis using implies_false true_false_distinct by simp
  qed
qed

lemma iff_is_and_implies_implies_swap:
  "IFF = AND \<circ>\<^sub>c \<langle>IMPLIES, IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)\<rangle>"
proof (etcs_rule one_separator)
  fix x
  assume x_type[type_rule]: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>"
  obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>" and x_def: "x = \<langle>p,q\<rangle>"
    using cart_prod_decomp[OF x_type] by blast
  have rhs_type[type_rule]: "\<langle>IMPLIES, IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)\<rangle> : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have rhs_s1: "(AND \<circ>\<^sub>c \<langle>IMPLIES, IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)\<rangle>) \<circ>\<^sub>c x
      = AND \<circ>\<^sub>c (\<langle>IMPLIES, IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)\<rangle> \<circ>\<^sub>c x)"
    by (rule sym[OF comp_associative2[OF x_type rhs_type AND_type]])
  have rhs_s2: "\<langle>IMPLIES, IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)\<rangle> \<circ>\<^sub>c x = \<langle>IMPLIES \<circ>\<^sub>c x, (IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)) \<circ>\<^sub>c x\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have swap_type[type_rule]: "swap(\<Omega>,\<Omega>) : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have rhs_s3: "(IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)) \<circ>\<^sub>c x = IMPLIES \<circ>\<^sub>c (swap(\<Omega>,\<Omega>) \<circ>\<^sub>c x)"
    by (rule sym[OF comp_associative2[OF x_type swap_type IMPLIES_type]])
  have rhs_s4: "swap(\<Omega>,\<Omega>) \<circ>\<^sub>c x = \<langle>q,p\<rangle>" using x_def swap_ap[OF p_type q_type] by simp
  have rhs_s5: "(AND \<circ>\<^sub>c \<langle>IMPLIES, IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)\<rangle>) \<circ>\<^sub>c x = AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x, IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle>\<rangle>"
    using rhs_s1 rhs_s2 rhs_s3 rhs_s4 by simp
  show "IFF \<circ>\<^sub>c x = (AND \<circ>\<^sub>c \<langle>IMPLIES, IMPLIES \<circ>\<^sub>c swap(\<Omega>,\<Omega>)\<rangle>) \<circ>\<^sub>c x"
  proof (cases "p = \<t>")
    case p_true: True
    show ?thesis
    proof (cases "q = \<t>")
      case True
      have lhs: "IFF \<circ>\<^sub>c x = \<t>" using p_true True IFF_true_true_is_true x_def by simp
      have rhs: "AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x, IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle>\<rangle> = \<t>"
        using p_true True x_def IMPLIES_true_true_is_true AND_true_true_is_true by simp
      show ?thesis using rhs_s5 lhs rhs by simp
    next
      case False
      then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
      have lhs: "IFF \<circ>\<^sub>c x = \<f>" using p_true q_eq_f IFF_true_false_is_false x_def by simp
      have implies_x: "IMPLIES \<circ>\<^sub>c x = \<f>" using p_true q_eq_f IMPLIES_true_false_is_false x_def by simp
      have implies_qp: "IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle> = \<t>" using p_true q_eq_f IMPLIES_false_true_is_true by simp
      have rhs: "AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x, IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle>\<rangle> = \<f>"
        using implies_x implies_qp AND_false_left_is_false[OF true_func_type] by simp
      show ?thesis using rhs_s5 lhs rhs by simp
    qed
  next
    case False
    then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
    show ?thesis
    proof (cases "q = \<t>")
      case True
      have lhs: "IFF \<circ>\<^sub>c x = \<f>" using p_eq_f True IFF_false_true_is_false x_def by simp
      have implies_x: "IMPLIES \<circ>\<^sub>c x = \<t>" using p_eq_f True IMPLIES_false_true_is_true x_def by simp
      have implies_qp: "IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle> = \<f>" using p_eq_f True IMPLIES_true_false_is_false by simp
      have rhs: "AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x, IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle>\<rangle> = \<f>"
        using implies_x implies_qp AND_false_right_is_false[OF true_func_type] by simp
      show ?thesis using rhs_s5 lhs rhs by simp
    next
      case False
      then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
      have lhs: "IFF \<circ>\<^sub>c x = \<t>" using p_eq_f q_eq_f IFF_false_false_is_true x_def by simp
      have implies_x: "IMPLIES \<circ>\<^sub>c x = \<t>" using p_eq_f q_eq_f IMPLIES_false_false_is_true x_def by simp
      have implies_qp: "IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle> = \<t>" using p_eq_f q_eq_f IMPLIES_false_false_is_true by simp
      have rhs: "AND \<circ>\<^sub>c \<langle>IMPLIES \<circ>\<^sub>c x, IMPLIES \<circ>\<^sub>c \<langle>q,p\<rangle>\<rangle> = \<t>"
        using implies_x implies_qp AND_true_true_is_true by simp
      show ?thesis using rhs_s5 lhs rhs by simp
    qed
  qed
qed

lemma IMPLIES_cross_eval:
  assumes P_type[type_rule]: "P : X \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : Y \<rightarrow> \<Omega>"
  shows "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = OR \<circ>\<^sub>c ((NOT \<circ>\<^sub>c P) \<times>\<^sub>f Q)"
proof -
  have pq_type[type_rule]: "P \<times>\<^sub>f Q : X \<times>\<^sub>c Y \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have nid_type[type_rule]: "NOT \<times>\<^sub>f id(\<Omega>) : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s1: "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = (OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id(\<Omega>))) \<circ>\<^sub>c (P \<times>\<^sub>f Q)"
    unfolding IMPLIES_def by simp
  have s2: "(OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id(\<Omega>))) \<circ>\<^sub>c (P \<times>\<^sub>f Q) = OR \<circ>\<^sub>c ((NOT \<times>\<^sub>f id(\<Omega>)) \<circ>\<^sub>c (P \<times>\<^sub>f Q))"
    by (rule sym[OF comp_associative2[OF pq_type nid_type OR_type]])
  have s3: "(NOT \<times>\<^sub>f id(\<Omega>)) \<circ>\<^sub>c (P \<times>\<^sub>f Q) = (NOT \<circ>\<^sub>c P) \<times>\<^sub>f (id(\<Omega>) \<circ>\<^sub>c Q)"
    using cfunc_cross_prod_comp_cfunc_cross_prod[OF P_type Q_type NOT_type id_type] .
  have s4: "id(\<Omega>) \<circ>\<^sub>c Q = Q" using id_left_unit2[OF Q_type] .
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma IMPLIES_implies_implies:
  assumes P_type[type_rule]: "P : X \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : Y \<rightarrow> \<Omega>"
  assumes X_nonempty: "\<exists>x. x \<in>\<^sub>c X"
  assumes IMPLIES_true: "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<Longrightarrow> Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
proof -
  assume P_true: "P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
  have np_type[type_rule]: "NOT \<circ>\<^sub>c P : X \<rightarrow> \<Omega>" by typecheck_cfuncs
  have np_eq: "NOT \<circ>\<^sub>c P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
  proof -
    have "NOT \<circ>\<^sub>c P = NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)" using P_true by simp
    also have "... = (NOT \<circ>\<^sub>c \<t>) \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>" by (rule comp_associative2[OF terminal_func_type true_func_type NOT_type])
    also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>" using NOT_true_is_false by simp
    finally show ?thesis .
  qed
  have or_eq: "OR \<circ>\<^sub>c ((NOT \<circ>\<^sub>c P) \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
    using IMPLIES_true IMPLIES_cross_eval[OF P_type Q_type] by simp
  show "Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  proof (etcs_rule one_separator)
    fix y
    assume y_type[type_rule]: "y \<in>\<^sub>c Y"
    obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" using X_nonempty by blast
    have xy_type[type_rule]: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" by typecheck_cfuncs
    have npq_type[type_rule]: "(NOT \<circ>\<^sub>c P) \<times>\<^sub>f Q : X \<times>\<^sub>c Y \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>" by typecheck_cfuncs
    have s1: "(OR \<circ>\<^sub>c ((NOT \<circ>\<^sub>c P) \<times>\<^sub>f Q)) \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c \<langle>x,y\<rangle>"
      using or_eq by simp
    have s2: "OR \<circ>\<^sub>c (((NOT \<circ>\<^sub>c P) \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle>) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c \<langle>x,y\<rangle>)"
      using s1 comp_associative2[OF xy_type npq_type OR_type] comp_associative2[OF xy_type terminal_func_type true_func_type] by simp
    have s3: "((NOT \<circ>\<^sub>c P) \<times>\<^sub>f Q) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<langle>(NOT \<circ>\<^sub>c P) \<circ>\<^sub>c x, Q \<circ>\<^sub>c y\<rangle>"
      by (rule cfunc_cross_prod_comp_cfunc_prod[OF x_type y_type np_type Q_type])
    have s4: "(NOT \<circ>\<^sub>c P) \<circ>\<^sub>c x = NOT \<circ>\<^sub>c (P \<circ>\<^sub>c x)"
      by (rule sym[OF comp_associative2[OF x_type P_type NOT_type]])
    have s5: "P \<circ>\<^sub>c x = \<t>"
    proof -
      have "P \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x" using P_true by simp
      also have "... = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)" by (rule sym[OF comp_associative2[OF x_type terminal_func_type true_func_type]])
      also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF x_type] by simp
      also have "... = \<t>" using id_right_unit2[OF true_func_type] .
      finally show ?thesis .
    qed
    have s6: "(NOT \<circ>\<^sub>c P) \<circ>\<^sub>c x = \<f>" using s4 s5 NOT_true_is_false by simp
    have s7: "\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c \<langle>x,y\<rangle> = id(\<one>)" using terminal_func_comp_elem[OF xy_type] .
    have s8: "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c \<langle>x,y\<rangle>) = \<t>" using s7 id_right_unit2[OF true_func_type] by simp
    have s9: "OR \<circ>\<^sub>c \<langle>\<f>, Q \<circ>\<^sub>c y\<rangle> = \<t>" using s2 s3 s6 s8 by simp
    have qy_type[type_rule]: "Q \<circ>\<^sub>c y \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have s10: "Q \<circ>\<^sub>c y = \<t>"
    proof (rule ccontr)
      assume "Q \<circ>\<^sub>c y \<noteq> \<t>"
      then have "Q \<circ>\<^sub>c y = \<f>" using true_false_only_truth_values[OF qy_type] by auto
      then have "OR \<circ>\<^sub>c \<langle>\<f>, Q \<circ>\<^sub>c y\<rangle> = \<f>" using OR_false_false_is_false by simp
      then show False using s9 true_false_distinct by simp
    qed
    have s11: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y = \<t>"
    proof -
      have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y)" by (rule sym[OF comp_associative2[OF y_type terminal_func_type true_func_type]])
      also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF y_type] by simp
      also have "... = \<t>" using id_right_unit2[OF true_func_type] .
      finally show ?thesis .
    qed
    show "Q \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y" using s10 s11 by simp
  qed
qed

lemma IMPLIES_elim:
  assumes IMPLIES_true: "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  assumes P_type[type_rule]: "P : X \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : Y \<rightarrow> \<Omega>"
  assumes X_nonempty: "\<exists>x. x \<in>\<^sub>c X"
  shows "(P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<Longrightarrow> ((Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<Longrightarrow> R) \<Longrightarrow> R"
  using IMPLIES_implies_implies assms by blast

lemma IMPLIES_elim':
  assumes IMPLIES_true: "IMPLIES \<circ>\<^sub>c \<langle>P, Q\<rangle> = \<t>"
  assumes P_type[type_rule]: "P : \<one> \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : \<one> \<rightarrow> \<Omega>"
  shows "(P = \<t>) \<Longrightarrow> ((Q = \<t>) \<Longrightarrow> R) \<Longrightarrow> R"
proof -
  assume p_true: "P = \<t>"
  assume qr: "(Q = \<t>) \<Longrightarrow> R"
  have "Q = \<t>"
  proof (rule ccontr)
    assume "Q \<noteq> \<t>"
    then have q_eq_f: "Q = \<f>" using Q_type true_false_only_truth_values by auto
    then have "IMPLIES \<circ>\<^sub>c \<langle>P,Q\<rangle> = \<f>" using p_true IMPLIES_true_false_is_false by simp
    then show False using IMPLIES_true true_false_distinct by simp
  qed
  then show R using qr by simp
qed

text \<open>HOL's @{text IMPLIES_elim''} (stated with @{text "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t>"} for
  @{text "P Q : \<one> \<rightarrow> \<Omega>"}) is omitted here: as stated it is only well-typed if
  @{text "\<one> \<times>\<^sub>c \<one>"} and @{text "\<one>"} coincide as literal terms (not merely up to isomorphism), a
  coincidence HOL's specific choice-based product construction happens to provide but which plain
  FOL's abstractly-axiomatized @{text cart_prod} gives no way to reproduce. Confirmed via grep that
  @{text IMPLIES_elim''} is never referenced anywhere else in the whole HOL repo (only
  @{text IMPLIES_elim'}, using the sensible @{text "\<langle>P,Q\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<Omega>"} pairing, is used
  downstream), so nothing is lost by dropping it.\<close>

lemma implies_implies_IMPLIES:
  assumes P_type[type_rule]: "P : \<one> \<rightarrow> \<Omega>" and Q_type[type_rule]: "Q : \<one> \<rightarrow> \<Omega>"
  shows "(P = \<t> \<Longrightarrow> Q = \<t>) \<Longrightarrow> IMPLIES \<circ>\<^sub>c \<langle>P, Q\<rangle> = \<t>"
proof -
  assume impl: "P = \<t> \<Longrightarrow> Q = \<t>"
  show "IMPLIES \<circ>\<^sub>c \<langle>P,Q\<rangle> = \<t>"
  proof (cases "P = \<t>")
    case True
    then have "Q = \<t>" using impl by simp
    then show ?thesis using True IMPLIES_true_true_is_true by simp
  next
    case False
    then have p_eq_f: "P = \<f>" using P_type true_false_only_truth_values by auto
    show ?thesis
    proof (cases "Q = \<t>")
      case True
      then show ?thesis using p_eq_f IMPLIES_false_true_is_true by simp
    next
      case False
      then have q_eq_f: "Q = \<f>" using Q_type true_false_only_truth_values by auto
      then show ?thesis using p_eq_f IMPLIES_false_false_is_true by simp
    qed
  qed
qed

subsection \<open>Other Boolean Identities\<close>

lemma AND_OR_distributive:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>" and r_type[type_rule]: "r \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, AND \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle>"
proof (cases "p = \<t>")
  case p_true: True
  show ?thesis
  proof (cases "q = \<t>")
    case True
    have and_pr_type[type_rule]: "AND \<circ>\<^sub>c \<langle>p,r\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have lhs: "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<t>"
      using p_true True OR_true_left_is_true[OF r_type] AND_true_true_is_true by simp
    have rhs: "OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, AND \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<t>"
      using p_true True AND_true_true_is_true OR_true_left_is_true[OF and_pr_type] by simp
    show ?thesis using lhs rhs by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    show ?thesis
    proof (cases "r = \<t>")
      case True
      have lhs: "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<t>"
        using p_true q_eq_f True OR_true_right_is_true[OF false_func_type] AND_true_true_is_true by simp
      have rhs: "OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, AND \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<t>"
        using p_true q_eq_f True AND_false_right_is_false[OF true_func_type] AND_true_true_is_true OR_true_right_is_true[OF false_func_type] by simp
      show ?thesis using lhs rhs by simp
    next
      case False
      then have r_eq_f: "r = \<f>" using r_type true_false_only_truth_values by auto
      have lhs: "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<f>"
        using p_true q_eq_f r_eq_f OR_false_false_is_false AND_false_right_is_false[OF true_func_type] by simp
      have rhs: "OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, AND \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<f>"
        using p_true q_eq_f r_eq_f AND_false_right_is_false[OF true_func_type] OR_false_false_is_false by simp
      show ?thesis using lhs rhs by simp
    qed
  qed
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  have or_qr_type[type_rule]: "OR \<circ>\<^sub>c \<langle>q,r\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have lhs: "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<f>"
    using p_eq_f AND_false_left_is_false[OF or_qr_type] by simp
  have rhs: "OR \<circ>\<^sub>c \<langle>AND \<circ>\<^sub>c \<langle>p,q\<rangle>, AND \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<f>"
    using p_eq_f AND_false_left_is_false[OF q_type] AND_false_left_is_false[OF r_type] OR_false_false_is_false by simp
  show ?thesis using lhs rhs by simp
qed

lemma OR_AND_distributive:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>" and r_type[type_rule]: "r \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, OR \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle>"
proof (cases "p = \<t>")
  case p_true: True
  have and_qr_type[type_rule]: "AND \<circ>\<^sub>c \<langle>q,r\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have lhs: "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<t>" using p_true OR_true_left_is_true[OF and_qr_type] by simp
  have rhs: "AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, OR \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<t>"
    using p_true OR_true_left_is_true[OF q_type] OR_true_left_is_true[OF r_type] AND_true_true_is_true by simp
  show ?thesis using lhs rhs by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  show ?thesis
  proof (cases "q = \<t>")
    case q_true: True
    show ?thesis
    proof (cases "r = \<t>")
      case True
      have lhs: "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<t>"
        using p_eq_f q_true True AND_true_true_is_true OR_true_right_is_true[OF false_func_type] by simp
      have rhs: "AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, OR \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<t>"
        using p_eq_f q_true True OR_true_right_is_true[OF false_func_type] AND_true_true_is_true by simp
      show ?thesis using lhs rhs by simp
    next
      case False
      then have r_eq_f: "r = \<f>" using r_type true_false_only_truth_values by auto
      have lhs: "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<f>"
        using p_eq_f q_true r_eq_f AND_false_right_is_false[OF true_func_type] OR_false_false_is_false by simp
      have rhs: "AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, OR \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<f>"
        using p_eq_f q_true r_eq_f OR_true_right_is_true[OF false_func_type] OR_false_false_is_false AND_false_right_is_false[OF true_func_type] by simp
      show ?thesis using lhs rhs by simp
    qed
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    have or_pr_type[type_rule]: "OR \<circ>\<^sub>c \<langle>p,r\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have lhs: "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle> = \<f>"
      using p_eq_f q_eq_f AND_false_left_is_false[OF r_type] OR_false_false_is_false by simp
    have rhs: "AND \<circ>\<^sub>c \<langle>OR \<circ>\<^sub>c \<langle>p,q\<rangle>, OR \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> = \<f>"
      using p_eq_f q_eq_f OR_false_false_is_false AND_false_left_is_false[OF or_pr_type] by simp
    show ?thesis using lhs rhs by simp
  qed
qed

lemma OR_AND_absorption:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p, AND \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle> = p"
proof (cases "p = \<t>")
  case True
  have apq_type[type_rule]: "AND \<circ>\<^sub>c \<langle>p,q\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  then show ?thesis using True OR_true_left_is_true[OF apq_type] by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  then show ?thesis using AND_false_left_is_false[OF q_type] OR_false_false_is_false by simp
qed

lemma AND_OR_absorption:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p, OR \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle> = p"
proof (cases "p = \<t>")
  case True
  then show ?thesis using AND_true_true_is_true OR_true_left_is_true[OF q_type] by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  have opq_type[type_rule]: "OR \<circ>\<^sub>c \<langle>p,q\<rangle> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  then show ?thesis using p_eq_f AND_false_left_is_false[OF opq_type] by simp
qed

lemma deMorgan_Law1:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>p,q\<rangle>) = AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle>"
proof (cases "p = \<t>")
  case True
  have s1: "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>" using True OR_true_left_is_true[OF q_type] by simp
  have s2: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
  have nq_type[type_rule]: "NOT \<circ>\<^sub>c q \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s3: "AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle> = \<f>" using True s2 AND_false_left_is_false[OF nq_type] by simp
  show ?thesis using s1 s2 s3 by simp
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  show ?thesis
  proof (cases "q = \<t>")
    case True
    have s1: "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>" using p_eq_f True OR_true_right_is_true[OF false_func_type] by simp
    have s2: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
    have np_type[type_rule]: "NOT \<circ>\<^sub>c p \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have s3: "AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle> = \<f>" using p_eq_f True s2 AND_false_right_is_false[OF np_type] by simp
    show ?thesis using s1 s2 s3 by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    have s1: "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using p_eq_f q_eq_f OR_false_false_is_false by simp
    have s2: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
    have s3: "AND \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle> = \<t>" using p_eq_f q_eq_f s2 AND_true_true_is_true by simp
    show ?thesis using s1 s2 s3 by simp
  qed
qed

lemma deMorgan_Law2:
  assumes p_type[type_rule]: "p \<in>\<^sub>c \<Omega>" and q_type[type_rule]: "q \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c (AND \<circ>\<^sub>c \<langle>p,q\<rangle>) = OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle>"
proof (cases "p = \<t>")
  case True
  show ?thesis
  proof (cases "q = \<t>")
    case True
    have s1: "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>" using \<open>p = \<t>\<close> True AND_true_true_is_true by simp
    have s2: "NOT \<circ>\<^sub>c \<t> = \<f>" using NOT_true_is_false .
    have s3: "OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle> = \<f>" using \<open>p = \<t>\<close> True s2 OR_false_false_is_false by simp
    show ?thesis using s1 s2 s3 by simp
  next
    case False
    then have q_eq_f: "q = \<f>" using q_type true_false_only_truth_values by auto
    have s1: "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using \<open>p = \<t>\<close> q_eq_f AND_false_right_is_false[OF true_func_type] by simp
    have s2: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
    have np_type[type_rule]: "NOT \<circ>\<^sub>c p \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    have s3: "OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle> = \<t>" using \<open>p = \<t>\<close> q_eq_f s2 OR_true_right_is_true[OF np_type] by simp
    show ?thesis using s1 s2 s3 by simp
  qed
next
  case False
  then have p_eq_f: "p = \<f>" using p_type true_false_only_truth_values by auto
  have s1: "AND \<circ>\<^sub>c \<langle>p,q\<rangle> = \<f>" using p_eq_f AND_false_left_is_false[OF q_type] by simp
  have s2: "NOT \<circ>\<^sub>c \<f> = \<t>" using NOT_false_is_true .
  have nq_type[type_rule]: "NOT \<circ>\<^sub>c q \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s3: "OR \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c p, NOT \<circ>\<^sub>c q\<rangle> = \<t>" using p_eq_f s2 OR_true_left_is_true[OF nq_type] by simp
  show ?thesis using s1 s2 s3 by simp
qed

end
