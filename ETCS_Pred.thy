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

end