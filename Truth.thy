theory Truth
  imports Equalizer
begin

section \<open>Truth Values and Characteristic Functions\<close>

axiomatization
  true_func :: "cfunc" ("\<t>") and
  false_func  :: "cfunc" ("\<f>") and
  truth_value_set :: "cset" ("\<Omega>")
where
  true_func_type[type_rule]: "\<t> \<in>\<^sub>c \<Omega>" and
  false_func_type[type_rule]: "\<f> \<in>\<^sub>c \<Omega>" and
  true_false_distinct: "\<t> \<noteq> \<f>" and
  true_false_only_truth_values: "x \<in>\<^sub>c \<Omega> \<Longrightarrow> x = \<f> \<or> x = \<t>" and
  characteristic_function_exists:
    "m : B \<rightarrow> X \<Longrightarrow> monomorphism m \<Longrightarrow> \<exists>! \<chi>. is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi>"

definition characteristic_func :: "cfunc \<Rightarrow> cfunc" where
  "characteristic_func m =
    (THE \<chi>. monomorphism m \<longrightarrow> is_pullback (domain m) one (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m \<chi>)"

lemma characteristic_func_is_pullback:
  assumes "m : B \<rightarrow> X" "monomorphism m"
  shows "is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
proof -
  obtain \<chi> where chi_is_pullback: "is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi>"
    using assms characteristic_function_exists by blast

  have "monomorphism m \<longrightarrow> is_pullback (domain m) one (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m (characteristic_func m)"
  proof (unfold characteristic_func_def, rule theI', rule_tac a=\<chi> in ex1I, clarify)
    show "is_pullback (domain m) one (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m \<chi>"
      using assms(1) cfunc_type_def chi_is_pullback by auto
    show "\<And>x. monomorphism m \<longrightarrow> is_pullback (domain m) one (codomain m) \<Omega> (\<beta>\<^bsub>domain m\<^esub>) \<t> m x \<Longrightarrow> x = \<chi>"
      using assms(1,2) cfunc_type_def characteristic_function_exists chi_is_pullback by fastforce
  qed
  then show "is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    using assms cfunc_type_def by auto
qed

lemma characteristic_func_type[type_rule]:
  assumes "m : B \<rightarrow> X" "monomorphism m"
  shows "characteristic_func m : X \<rightarrow> \<Omega>"
proof -
  have "is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    using assms by (rule characteristic_func_is_pullback)
  then show "characteristic_func m : X \<rightarrow> \<Omega>"
    unfolding is_pullback_def by auto
qed

lemma characteristic_func_eq:
  assumes "m : B \<rightarrow> X" "monomorphism m"
  shows "characteristic_func m \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>"
  using assms characteristic_func_is_pullback unfolding is_pullback_def by auto

lemma monomorphism_equalizes_char_func:
  assumes m_type[type_rule]: "m : B \<rightarrow> X" and m_mono[type_rule]: "monomorphism m"
  shows "equalizer B m (characteristic_func m) (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
  unfolding equalizer_def
proof (typecheck_cfuncs, rule_tac x="X" in exI, rule_tac x="\<Omega>" in exI, auto)
  have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub> = characteristic_func m \<circ>\<^sub>c m"
    using characteristic_func_eq m_mono m_type by auto
  then have "\<beta>\<^bsub>B\<^esub> = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c m"
    using m_type terminal_func_comp by auto
  then show "characteristic_func m \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m"
    using comm comp_associative2 by (typecheck_cfuncs, auto)
next
  fix h F
  assume  "h : F \<rightarrow> X" "characteristic_func m \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h"
  then show "\<exists>k. k : F \<rightarrow> B \<and> m \<circ>\<^sub>c k = h"
    (*by (smt (verit) assms cfunc_type_def characteristic_func_is_pullback comp_associative is_pullback_def terminal_func_comp terminal_func_type true_func_type)*)
next
  fix F k y
  assume "k : F \<rightarrow> B" "y : F \<rightarrow> B"
  then show "m \<circ>\<^sub>c y = m \<circ>\<^sub>c k \<Longrightarrow> k = y"
    using m_mono m_type monomorphism_def3 by blast 
qed

lemma characteristic_func_true_relative_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_true: "characteristic_func m \<circ>\<^sub>c x = \<t>"
  shows "x \<in>\<^bsub>X\<^esub> (B,m)"
proof (insert assms, unfold relative_member_def2 factors_through_def, auto)
  have "is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    by (simp add: assms characteristic_func_is_pullback)
  then have "\<exists>j. j : one \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j = id one \<and> m \<circ>\<^sub>c j = x"
    unfolding is_pullback_def using assms by (metis id_right_unit2 id_type true_func_type)
  then show "\<exists>j. j : domain x \<rightarrow> domain m \<and> m \<circ>\<^sub>c j = x"
    using assms(1,3) cfunc_type_def by auto
qed

lemma characteristic_func_false_not_relative_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_true: "characteristic_func m \<circ>\<^sub>c x = \<f>"
  shows "\<not> (x \<in>\<^bsub>X\<^esub> (B,m))"
proof (insert assms, unfold relative_member_def2 factors_through_def, auto)
  fix h
  assume x_def: "x = m \<circ>\<^sub>c h"

  assume "h : domain (m \<circ>\<^sub>c h) \<rightarrow> domain m"
  then have h_type: "h \<in>\<^sub>c B"
    using assms(1,3) cfunc_type_def x_def by auto

  have "is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m (characteristic_func m)"
    by (simp add: assms characteristic_func_is_pullback)
  then have char_m_true: "characteristic_func m \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>"
    unfolding is_pullback_def by auto

  then have "characteristic_func m \<circ>\<^sub>c m \<circ>\<^sub>c h = \<f>"
    using x_def characteristic_func_true by auto
  then have "(characteristic_func m \<circ>\<^sub>c m) \<circ>\<^sub>c h = \<f>"
    using assms h_type by (typecheck_cfuncs, simp add: comp_associative2)
  then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c h = \<f>"    
    using char_m_true by auto
  then have "\<t> = \<f>"
    by (metis cfunc_type_def comp_associative h_type id_right_unit2 id_type one_unique_element
        terminal_func_comp terminal_func_type true_func_type)
  then show "False"
    using true_false_distinct by auto
qed

lemma rel_mem_char_func_true:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes "x \<in>\<^bsub>X\<^esub> (B,m)"
  shows "characteristic_func m \<circ>\<^sub>c x = \<t>"
  by (meson assms(4) characteristic_func_false_not_relative_member characteristic_func_type comp_type relative_member_def2 true_false_only_truth_values)

lemma not_rel_mem_char_func_false:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes "\<not> (x \<in>\<^bsub>X\<^esub> (B,m))"
  shows "characteristic_func m \<circ>\<^sub>c x = \<f>"
  by (meson assms characteristic_func_true_relative_member characteristic_func_type comp_type true_false_only_truth_values)

text \<open>The lemma below corresponds to Proposition 2.2.2 in Halvorson.\<close>
lemma "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
proof -
  have "{x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = {\<langle>\<t>,\<t>\<rangle>, \<langle>\<t>,\<f>\<rangle>, \<langle>\<f>,\<t>\<rangle>, \<langle>\<f>,\<f>\<rangle>}"
    by (auto simp add: cfunc_prod_type true_func_type false_func_type,
        smt cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type true_false_only_truth_values)
  then show "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
    using element_pair_eq false_func_type true_false_distinct true_func_type by auto
qed

(* Exercise 2.2.3 *)
lemma regmono_is_mono: "regular_monomorphism(m) \<Longrightarrow> monomorphism(m)"
  using equalizer_is_monomorphism regular_monomorphism_def by blast

(* Proposition 2.2.4 *)
lemma mono_is_regmono:
  shows "monomorphism(m) \<Longrightarrow> regular_monomorphism(m)"
  unfolding monomorphism_def regular_monomorphism_def
  using cfunc_type_def characteristic_func_type monomorphism_def domain_comp terminal_func_type true_func_type monomorphism_equalizes_char_func
  by (rule_tac x="characteristic_func m" in exI, rule_tac x="\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub>" in exI, auto)

subsection \<open>Equality Predicate\<close>

definition eq_pred :: "cset \<Rightarrow> cfunc" where
  "eq_pred X = (THE \<chi>. is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> (diagonal X) \<chi>)"

lemma eq_pred_pullback: "is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> (diagonal X) (eq_pred X)"
  unfolding eq_pred_def
  by (rule the1I2, simp_all add: characteristic_function_exists diag_mono diagonal_type)

lemma eq_pred_type[type_rule]:
  "eq_pred X : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
  using eq_pred_pullback unfolding is_pullback_def square_commutes_def by auto

lemma eq_pred_square: "eq_pred X \<circ>\<^sub>c diagonal X = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
  using eq_pred_pullback unfolding is_pullback_def square_commutes_def by auto

lemma eq_pred_iff_eq:
  assumes "x : one \<rightarrow> X" "y : one \<rightarrow> X"
  shows "(x = y) = (eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>)"
proof auto
  assume x_eq_y: "x = y"

  have "(eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,id\<^sub>c X\<rangle>) \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using eq_pred_square unfolding diagonal_def by auto
  then have "eq_pred X \<circ>\<^sub>c \<langle>y, y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using assms diagonal_type id_type
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 diagonal_def id_left_unit2)
  then show "eq_pred X \<circ>\<^sub>c \<langle>y, y\<rangle> = \<t>"
    using assms id_type
    by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp terminal_func_type terminal_func_unique id_right_unit2)
next
  assume "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>"
  then have "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t> \<circ>\<^sub>c id one"
    using id_right_unit2 true_func_type by auto
  then obtain j  where j_type: "j : one \<rightarrow> X" and "diagonal X \<circ>\<^sub>c j = \<langle>x,y\<rangle>"
    using eq_pred_pullback assms unfolding is_pullback_def by (metis cfunc_prod_type id_type)
  then have "\<langle>j,j\<rangle> = \<langle>x,y\<rangle>"
    using diag_on_elements by auto
  then show "x = y"
    using assms element_pair_eq j_type by auto
qed

lemma eq_pred_iff_eq_conv:
  assumes "x : one \<rightarrow> X" "y : one \<rightarrow> X"
  shows "(x \<noteq> y) = (eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle> = \<f>)"
proof(auto)
  assume "x \<noteq> y"
  show "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<f>"
    using assms \<open>x \<noteq> y\<close> eq_pred_iff_eq true_false_only_truth_values by (typecheck_cfuncs, blast)
next
  show "eq_pred X \<circ>\<^sub>c \<langle>y,y\<rangle> = \<f> \<Longrightarrow> x = y \<Longrightarrow> False"
    by (metis assms(1) eq_pred_iff_eq true_false_distinct)
qed

lemma eq_pred_iff_eq_conv2:
  assumes "x : one \<rightarrow> X" "y : one \<rightarrow> X"
  shows "(x \<noteq> y) = (eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle> \<noteq> \<t>)"
  using assms eq_pred_iff_eq by presburger

lemma eq_pred_of_monomorphism:
  assumes m_type[type_rule]: "m : X \<rightarrow> Y" and m_mono: "monomorphism m"
  shows "eq_pred Y \<circ>\<^sub>c (m \<times>\<^sub>f m) = eq_pred X"
proof (rule one_separator[where X="X \<times>\<^sub>c X", where Y=\<Omega>])
  show "eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "eq_pred X : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
    by typecheck_cfuncs
next
  fix x
  assume "x \<in>\<^sub>c X \<times>\<^sub>c X"
  then obtain x1 x2 where x_def: "x = \<langle>x1, x2\<rangle>" and x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X"
    using cart_prod_decomp by blast
  show "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c x = eq_pred X \<circ>\<^sub>c x"
  proof (unfold x_def, cases "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>")
    assume LHS: "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>"
    then have "eq_pred Y \<circ>\<^sub>c (m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then have "eq_pred Y \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle> = \<t>"
      by (typecheck_cfuncs, auto simp add: cfunc_cross_prod_comp_cfunc_prod)
    then have "m \<circ>\<^sub>c x1 = m \<circ>\<^sub>c x2"
      by (typecheck_cfuncs_prems, simp add: eq_pred_iff_eq)
    then have "x1 = x2"
      using m_mono m_type monomorphism_def3 x1_type x2_type by blast
    then have RHS: "eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>"
      by (typecheck_cfuncs, insert eq_pred_iff_eq, blast)

    show "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle>"
      using LHS RHS by auto
  next
    assume "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> \<noteq> \<t>"
    then have LHS: "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>"
      by (typecheck_cfuncs, meson true_false_only_truth_values)
    then have "eq_pred Y \<circ>\<^sub>c (m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then have "eq_pred Y \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle> = \<f>"
      by (typecheck_cfuncs, auto simp add: cfunc_cross_prod_comp_cfunc_prod)
    then have "m \<circ>\<^sub>c x1 \<noteq> m \<circ>\<^sub>c x2"
      using eq_pred_iff_eq_conv by (typecheck_cfuncs_prems, blast)
    then have "x1 \<noteq> x2"
      by auto
    then have RHS: "eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>"
      using eq_pred_iff_eq_conv by (typecheck_cfuncs, blast)

    show "(eq_pred Y \<circ>\<^sub>c m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x1,x2\<rangle>"
      using LHS RHS by auto
  qed
qed

