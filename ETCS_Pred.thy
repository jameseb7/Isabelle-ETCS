theory ETCS_Pred
  imports ETCS_Truth
begin

section \<open>Predicate logic functions\<close>

subsection \<open>NOT\<close>

definition NOT :: "cfunc" where
  "NOT = (THE \<chi>. is_pullback one one \<Omega> \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> \<f> \<chi>)"

lemma NOT_is_pullback:
  "is_pullback one one \<Omega> \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> \<f> NOT"
  unfolding NOT_def
  using characteristic_function_exists false_func_type element_monomorphism
  by (rule_tac the1I2, auto)

lemma NOT_type[type_rule]:
  "NOT : \<Omega> \<rightarrow> \<Omega>"
  using NOT_is_pullback unfolding is_pullback_def square_commutes_def by auto

lemma NOT_false_is_true:
  "NOT \<circ>\<^sub>c \<f> = \<t>"
  using NOT_is_pullback unfolding is_pullback_def square_commutes_def
  by (metis cfunc_type_def id_right_unit id_type one_unique_element)

lemma NOT_true_is_false:
  "NOT \<circ>\<^sub>c \<t> = \<f>"
proof (rule ccontr)
  assume "NOT \<circ>\<^sub>c \<t> \<noteq> \<f>"
  then have "NOT \<circ>\<^sub>c \<t> = \<t>"
    using true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "\<t> \<circ>\<^sub>c id\<^sub>c one = NOT \<circ>\<^sub>c \<t>"
    using id_right_unit2 true_func_type by auto
  then obtain j where j_type: "j \<in>\<^sub>c one" and j_id: "\<beta>\<^bsub>one\<^esub> \<circ>\<^sub>c j = id\<^sub>c one" and f_j_eq_t: "\<f> \<circ>\<^sub>c j = \<t>"
    using NOT_is_pullback unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id\<^sub>c one"
    using id_type one_unique_element by blast
  then have "\<f> = \<t>"
    using f_j_eq_t false_func_type id_right_unit2 by auto
  then show False
    using true_false_distinct by auto
qed
    

lemma NOT_is_true_implies_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c p = \<t> \<Longrightarrow> p = \<f>"
  using NOT_true_is_false assms true_false_only_truth_values by fastforce

lemma NOT_is_false_implies_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOT \<circ>\<^sub>c p = \<f> \<Longrightarrow> p = \<t>"
  using NOT_false_is_true assms true_false_only_truth_values by fastforce

subsection \<open>AND\<close>

definition AND :: "cfunc" where
  "AND = (THE \<chi>. is_pullback one one (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> \<langle>\<t>,\<t>\<rangle> \<chi>)"

lemma AND_is_pullback:
  "is_pullback one one (\<Omega> \<times>\<^sub>c \<Omega>) \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> \<langle>\<t>,\<t>\<rangle> AND"
  unfolding AND_def
  using element_monomorphism characteristic_function_exists
  by (typecheck_cfuncs, rule_tac the1I2, auto)

lemma AND_type[type_rule]:
  "AND : \<Omega> \<times>\<^sub>c \<Omega> \<rightarrow> \<Omega>"
  using AND_is_pullback unfolding is_pullback_def square_commutes_def by auto

lemma AND_true_true_is_true:
  "AND \<circ>\<^sub>c \<langle>\<t>,\<t>\<rangle> = \<t>"
  using AND_is_pullback unfolding is_pullback_def square_commutes_def
  by (metis cfunc_type_def id_right_unit id_type one_unique_element)

lemma AND_false_left_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<f>"
proof (rule ccontr)
  assume "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> \<noteq> \<f>"
  then have "AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "\<t> \<circ>\<^sub>c id one = AND \<circ>\<^sub>c \<langle>\<f>,p\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_right_unit2)
  then obtain j where j_type: "j \<in>\<^sub>c one" and j_id: "\<beta>\<^bsub>one\<^esub> \<circ>\<^sub>c j = id\<^sub>c one" and tt_j_eq_fp: "\<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>\<f>,p\<rangle>"
    using AND_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id\<^sub>c one"
    using id_type one_unique_element by auto
  then have "\<langle>\<t>,\<t>\<rangle> = \<langle>\<f>,p\<rangle>"
    by (typecheck_cfuncs, metis tt_j_eq_fp id_right_unit2)
  then have "\<t> = \<f>"
    using assms cart_prod_eq2 by (typecheck_cfuncs, auto)
  then show "False"
    using true_false_distinct by auto
qed

lemma AND_false_right_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<f>"
proof (rule ccontr)
  assume "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> \<noteq> \<f>"
  then have "AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "\<t> \<circ>\<^sub>c id one = AND \<circ>\<^sub>c \<langle>p,\<f>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_right_unit2)
  then obtain j where j_type: "j \<in>\<^sub>c one" and j_id: "\<beta>\<^bsub>one\<^esub> \<circ>\<^sub>c j = id\<^sub>c one" and tt_j_eq_fp: "\<langle>\<t>,\<t>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<f>\<rangle>"
    using AND_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id\<^sub>c one"
    using id_type one_unique_element by auto
  then have "\<langle>\<t>,\<t>\<rangle> = \<langle>p,\<f>\<rangle>"
    by (typecheck_cfuncs, metis tt_j_eq_fp id_right_unit2)
  then have "\<t> = \<f>"
    using assms cart_prod_eq2 by (typecheck_cfuncs, auto)
  then show "False"
    using true_false_distinct by auto
qed


subsection \<open>NOR\<close>

definition NOR :: "cfunc" where
  "NOR = (THE \<chi>. is_pullback  one one (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> \<langle>\<f>, \<f>\<rangle> \<chi>)"

lemma NOR_is_pullback:
  "is_pullback  one one (\<Omega>\<times>\<^sub>c\<Omega>) \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> \<langle>\<f>, \<f>\<rangle> NOR"
  unfolding NOR_def
  using characteristic_function_exists element_monomorphism
  by (typecheck_cfuncs, rule_tac the1I2, simp_all)

lemma NOR_type[type_rule]:
  "NOR : (\<Omega>\<times>\<^sub>c\<Omega>) \<rightarrow> \<Omega>"
  using NOR_is_pullback unfolding is_pullback_def square_commutes_def by auto

lemma NOR_false_false_is_true:
  "NOR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<t>"
  using NOR_is_pullback unfolding is_pullback_def square_commutes_def
  by (auto, metis cfunc_type_def id_right_unit id_type one_unique_element)

lemma NOR_left_true_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<f>"
proof (rule ccontr)
  assume "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> \<noteq> \<f>"
  then have "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "NOR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t> \<circ>\<^sub>c id one"
    using id_right_unit2 true_func_type by auto
  then obtain j where j_type: "j \<in>\<^sub>c one" and j_id: "\<beta>\<^bsub>one\<^esub> \<circ>\<^sub>c j = id one" and ff_j_eq_tp: "\<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>\<t>,p\<rangle>"
    using NOR_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, metis)
  then have "j = id one"
    using id_type one_unique_element by blast
  then have "\<langle>\<f>,\<f>\<rangle> = \<langle>\<t>,p\<rangle>"
    using cfunc_prod_comp false_func_type ff_j_eq_tp id_right_unit2 j_type by auto
  then have "\<f> = \<t>"
    using assms cart_prod_eq2 false_func_type true_func_type by auto
  then show False
    using true_false_distinct by auto
qed

lemma NOR_right_true_is_false:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<f>"
proof (rule ccontr)
  assume "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> \<noteq> \<f>"
  then have "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t>"
    using assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have "NOR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t> \<circ>\<^sub>c id one"
    using id_right_unit2 true_func_type by auto
  then obtain j where j_type: "j \<in>\<^sub>c one" and j_id: "\<beta>\<^bsub>one\<^esub> \<circ>\<^sub>c j = id one" and ff_j_eq_tp: "\<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c j = \<langle>p,\<t>\<rangle>"
    using NOR_is_pullback assms unfolding is_pullback_def by (typecheck_cfuncs, metis)
  then have "j = id one"
    using id_type one_unique_element by blast
  then have "\<langle>\<f>,\<f>\<rangle> = \<langle>p,\<t>\<rangle>"
    using cfunc_prod_comp false_func_type ff_j_eq_tp id_right_unit2 j_type by auto
  then have "\<f> = \<t>"
    using assms cart_prod_eq2 false_func_type true_func_type by auto
  then show False
    using true_false_distinct by auto
qed

lemma
  assumes X_nonempty: "nonempty X" and Y_nonempty: "nonempty Y"
  assumes P_Q_types[type_rule]: "P : X \<rightarrow> \<Omega>" "Q : Y \<rightarrow> \<Omega>"
  assumes NOR_true: "NOR \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "\<not> ((P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<or> (Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>))"
proof -

  obtain z where z_type[type_rule]: "z : X \<times>\<^sub>c Y \<rightarrow> one"
    and "P \<times>\<^sub>f Q = \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c z"
    using NOR_is_pullback NOR_true unfolding is_pullback_def
    by (metis P_Q_types cfunc_cross_prod_type terminal_func_type) 
  then have "P \<times>\<^sub>f Q = \<langle>\<f>,\<f>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
    using terminal_func_unique by auto
  then have "P \<times>\<^sub>f Q = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  then have "P \<times>\<^sub>f Q = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj X Y, \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c right_cart_proj X Y\<rangle>"
    by (typecheck_cfuncs_prems, metis left_cart_proj_type right_cart_proj_type terminal_func_comp)
  then have "\<langle>P \<circ>\<^sub>c left_cart_proj X Y, Q \<circ>\<^sub>c right_cart_proj X Y\<rangle>
      = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj X Y, \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c right_cart_proj X Y\<rangle>"
    by (typecheck_cfuncs, unfold cfunc_cross_prod_def2, auto)
  then have "(P \<circ>\<^sub>c left_cart_proj X Y = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj X Y)
      \<and> (Q \<circ>\<^sub>c right_cart_proj X Y = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c right_cart_proj X Y)"
    using  cart_prod_eq2 by (typecheck_cfuncs, auto simp add: comp_associative2)
  then have "(P = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<and> (Q = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    using assms epimorphism_def3 nonempty_left_imp_right_proj_epimorphism nonempty_right_imp_left_proj_epimorphism
    by (typecheck_cfuncs_prems, blast)
  then have "(P \<noteq> \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<and> (Q \<noteq> \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
  proof auto
    show "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<Longrightarrow> False"
      by (typecheck_cfuncs_prems, smt X_nonempty comp_associative2 nonempty_def one_separator_contrapos terminal_func_comp terminal_func_unique true_false_distinct)
    show "\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<Longrightarrow> False"
      by (typecheck_cfuncs_prems, smt Y_nonempty comp_associative2 nonempty_def one_separator_contrapos terminal_func_comp terminal_func_unique true_false_distinct)
  qed
  then show "\<not> (P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<or> Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    by blast
qed

subsection \<open>OR\<close>

definition OR :: "cfunc" where
  "OR = NOT \<circ>\<^sub>c NOR"
 
lemma OR_type[type_rule]:
  "OR : (\<Omega>\<times>\<^sub>c\<Omega>) \<rightarrow> \<Omega>"
  unfolding OR_def by typecheck_cfuncs

lemma OR_false_false_is_false:
  "OR \<circ>\<^sub>c \<langle>\<f>,\<f>\<rangle> = \<f>"
  unfolding OR_def 
  using NOR_false_false_is_true NOT_true_is_false comp_associative2 
  by (typecheck_cfuncs, force)

lemma OR_true_left_is_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>\<t>,p\<rangle> = \<t>"
  unfolding OR_def 
  using assms NOR_left_true_is_false NOT_false_is_true comp_associative2
  by (typecheck_cfuncs, force)

lemma OR_true_right_is_true:
  assumes "p \<in>\<^sub>c \<Omega>"
  shows "OR \<circ>\<^sub>c \<langle>p,\<t>\<rangle> = \<t>"
  unfolding OR_def 
  using assms NOR_right_true_is_false NOT_false_is_true comp_associative2
  by (typecheck_cfuncs, force)


lemma OR_true_implies_one_is_true:
  assumes "p \<in>\<^sub>c \<Omega>" 
  assumes "q \<in>\<^sub>c \<Omega>"
  assumes "OR \<circ>\<^sub>c \<langle>p,q\<rangle> = \<t>"
  shows "(p = \<t>) \<or> (q = \<t>)"
  by (metis OR_false_false_is_false assms true_false_only_truth_values)


subsection \<open>IMPLIES\<close>

definition IMPLIES :: "cfunc" where
  "IMPLIES = OR \<circ>\<^sub>c (NOT \<times>\<^sub>f id \<Omega>)"

lemma IMPLIES_type[type_rule]:
  "IMPLIES : \<Omega> \<times>\<^sub>c \<Omega>  \<rightarrow> \<Omega>"
  unfolding IMPLIES_def by typecheck_cfuncs

lemma
  assumes "P : X \<rightarrow> \<Omega>" "Q : Y \<rightarrow> \<Omega>"
  assumes "IMPLIES \<circ>\<^sub>c (P \<times>\<^sub>f Q) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  shows "(P = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<Longrightarrow> (Q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
  using assms unfolding IMPLIES_def apply (typecheck_cfuncs_prems, typecheck_cfuncs)
  oops

end