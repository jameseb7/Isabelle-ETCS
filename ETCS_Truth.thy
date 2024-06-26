theory ETCS_Truth
  imports ETCS_Equalizer
begin

section  \<open>Axiom 5: Truth-Value Object\<close>

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
    unfolding is_pullback_def square_commutes_def by auto
qed

lemma characteristic_func_eq:
  assumes "m : B \<rightarrow> X" "monomorphism m"
  shows "characteristic_func m \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>"
  using assms characteristic_func_is_pullback unfolding is_pullback_def square_commutes_def by auto

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
    by (smt (verit) assms cfunc_type_def characteristic_func_is_pullback comp_associative is_pullback_def terminal_func_comp terminal_func_type true_func_type)
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
    using assms(1) assms(3) cfunc_type_def by auto
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
    unfolding is_pullback_def square_commutes_def by auto

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

lemma relative_member_characteristic_func_true:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes "x \<in>\<^bsub>X\<^esub> (B,m)"
  shows "characteristic_func m \<circ>\<^sub>c x = \<t>"
  by (meson assms(4) characteristic_func_false_not_relative_member characteristic_func_type comp_type relative_member_def2 true_false_only_truth_values)



lemma not_relative_member_characteristic_func_false:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes "\<not> (x \<in>\<^bsub>X\<^esub> (B,m))"
  shows "characteristic_func m \<circ>\<^sub>c x = \<f>"
  by (meson assms characteristic_func_true_relative_member characteristic_func_type comp_type true_false_only_truth_values)



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




(* Proposition 2.2.1: see under Axiom 8 *)

(* Proposition 2.2.2 *)
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

(*Proposition 2.2.5*)
lemma epi_mon_is_iso:
  assumes "epimorphism(f)" "monomorphism(f)"
  shows "isomorphism(f)"
  using assms epi_regmon_is_iso mono_is_regmono by auto

(* Definition 2.2.6 *)
definition fiber :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1{_}" [100,100]100) where
  "f\<^sup>-\<^sup>1{y} = (f\<^sup>-\<^sup>1[one]\<^bsub>y\<^esub>)"

definition fiber_morphism :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "fiber_morphism f y = left_cart_proj (domain f) one \<circ>\<^sub>c inverse_image_mapping f one y"

lemma fiber_morphism_type[type_rule]:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "fiber_morphism f y : f\<^sup>-\<^sup>1{y} \<rightarrow> X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject subobject_of_def2
  by (typecheck_cfuncs, auto)

lemma fiber_subset: 
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "(f\<^sup>-\<^sup>1{y}, fiber_morphism f y) \<subseteq>\<^sub>c X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject inverse_image_subobject_mapping_def
  by (typecheck_cfuncs, auto)

lemma fiber_morphism_monomorphism:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "monomorphism (fiber_morphism f y)"
  using assms cfunc_type_def element_monomorphism fiber_morphism_def inverse_image_monomorphism by auto

lemma fiber_morphism_eq:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "f \<circ>\<^sub>c fiber_morphism f y  = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
proof -
  have "f \<circ>\<^sub>c fiber_morphism f y = f \<circ>\<^sub>c left_cart_proj (domain f) one \<circ>\<^sub>c inverse_image_mapping f one y"
    unfolding fiber_morphism_def by auto
  also have "... = y \<circ>\<^sub>c right_cart_proj X one \<circ>\<^sub>c inverse_image_mapping f one y"
    using assms cfunc_type_def element_monomorphism inverse_image_mapping_eq by auto
  also have "... = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1[one]\<^bsub>y\<^esub>\<^esub>"
    using assms by (typecheck_cfuncs, metis element_monomorphism terminal_func_unique)
  also have "... = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
    unfolding fiber_def by auto
  then show ?thesis
    using calculation by auto
qed

(* Proposition 2.2.7 *)
lemma not_surjective_has_some_empty_preimage:
  assumes p_type[type_rule]: "p: X \<rightarrow> Y" and p_not_surj: "\<not>surjective(p)"
  shows "\<exists> y. (y\<in>\<^sub>c Y \<and>  \<not>nonempty(p\<^sup>-\<^sup>1{y}))"
proof -
  have nonempty: "nonempty(Y)"
    using assms(1) assms(2) cfunc_type_def nonempty_def surjective_def by auto
  obtain y0 where y0_type[type_rule]: "y0 \<in>\<^sub>c Y" "\<forall> x. x \<in>\<^sub>c X \<longrightarrow> p\<circ>\<^sub>c x \<noteq> y0"
    using assms cfunc_type_def surjective_def by auto

  have "\<not>nonempty(p\<^sup>-\<^sup>1{y0})"
  proof (rule ccontr,auto)
    assume a1: "nonempty(p\<^sup>-\<^sup>1{y0})"
    obtain z where z_type[type_rule]: "z \<in>\<^sub>c p\<^sup>-\<^sup>1{y0}"
      using a1 nonempty_def by blast
    have fiber_z_type: "fiber_morphism p y0 \<circ>\<^sub>c z \<in>\<^sub>c X"
      using assms(1) comp_type fiber_morphism_type y0_type z_type by auto
    have contradiction: "p \<circ>\<^sub>c (fiber_morphism p y0 \<circ>\<^sub>c z) = y0"
      by (typecheck_cfuncs, smt (z3) comp_associative2 fiber_morphism_eq id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
    have "p \<circ>\<^sub>c (fiber_morphism p y0 \<circ>\<^sub>c z) \<noteq> y0"
      by (simp add: fiber_z_type y0_type)
    then show False
      using contradiction by blast
  qed
  then show ?thesis
    using y0_type by blast
qed

lemma char_of_singleton1: 
    assumes "x \<in>\<^sub>c X" 
    shows  "eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id X\<rangle> \<circ>\<^sub>c x = \<t>"
    using assms cart_prod_extract_right eq_pred_iff_eq by fastforce

lemma char_of_singleton2: 
    assumes "x \<in>\<^sub>c X"  "y \<in>\<^sub>c X" "x \<noteq> y"
    shows  "eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id X\<rangle> \<circ>\<^sub>c y = \<f>"
    using assms cart_prod_extract_right eq_pred_iff_eq true_false_only_truth_values  by (typecheck_cfuncs, fastforce)




(* Proposition 2.2.8 *)
lemma epi_is_surj:
  assumes "p: X \<rightarrow> Y" "epimorphism(p)"
  shows "surjective(p)"
  unfolding surjective_def
proof(rule ccontr)
  assume a1: "\<not> (\<forall>y. y \<in>\<^sub>c codomain p \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain p \<and> p \<circ>\<^sub>c x = y))"
  have "\<exists>y. y \<in>\<^sub>c Y \<and> \<not>(\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y)"
    using a1 assms(1) cfunc_type_def by auto
  then obtain y0 where y_def: "y0 \<in>\<^sub>c Y \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> y0)"
    by auto
  have mono: "monomorphism(y0)"
    using element_monomorphism y_def by blast
  obtain g where g_def: "g = eq_pred Y \<circ>\<^sub>c \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle>"
    by simp
  have g_right_arg_type: "\<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> : Y \<rightarrow> (Y\<times>\<^sub>cY)"
    by (meson cfunc_prod_type comp_type id_type terminal_func_type y_def)
  then have g_type[type_rule]: "g: Y \<rightarrow> \<Omega>"
    using comp_type eq_pred_type g_def by blast

  have gpx_Eqs_f: "\<forall>x. (x \<in>\<^sub>c X \<longrightarrow> g \<circ>\<^sub>c p \<circ>\<^sub>c x = \<f>)"
  proof(rule ccontr, auto)
    fix x
    assume x_type: "x \<in>\<^sub>c X" 
    assume bwoc: "g \<circ>\<^sub>c p \<circ>\<^sub>c x \<noteq> \<f>"
   (* have contradiction: "\<exists>s. s \<in>\<^sub>c p\<^sup>-\<^sup>1{y0}" *)
    show False  
      by (smt assms(1) bwoc cfunc_type_def char_of_singleton2 comp_associative comp_type eq_pred_type g_def g_right_arg_type x_type y_def)
  qed
  obtain h where h_def: "h = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" and h_type[type_rule]:"h: Y \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  have hpx_eqs_f: "\<forall>x. (x \<in>\<^sub>c X \<longrightarrow> h \<circ>\<^sub>c p \<circ>\<^sub>c x = \<f>)"
    by (smt assms(1) cfunc_type_def codomain_comp comp_associative false_func_type h_def id_right_unit2 id_type terminal_func_comp terminal_func_type terminal_func_unique)
  have gp_eqs_hp: "g \<circ>\<^sub>c p = h \<circ>\<^sub>c p"
  proof(rule one_separator[where X=X,where Y=\<Omega>])
    show "g \<circ>\<^sub>c p : X \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "h \<circ>\<^sub>c p : X \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> (g \<circ>\<^sub>c p) \<circ>\<^sub>c x = (h \<circ>\<^sub>c p) \<circ>\<^sub>c x"
      using assms(1) comp_associative2 g_type gpx_Eqs_f h_type hpx_eqs_f by auto
  qed
  have g_not_h: "g \<noteq> h"
  proof -
   have f1: "\<forall>c. \<beta>\<^bsub>codomain c\<^esub> \<circ>\<^sub>c c = \<beta>\<^bsub>domain c\<^esub>"
    by (simp add: cfunc_type_def terminal_func_comp)
   have f2: "domain \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>,id\<^sub>c Y\<rangle> = Y"
    using cfunc_type_def g_right_arg_type by blast
  have f3: "codomain \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>,id\<^sub>c Y\<rangle> = Y \<times>\<^sub>c Y"
    using cfunc_type_def g_right_arg_type by blast
  have f4: "codomain y0 = Y"
    using cfunc_type_def y_def by presburger
  have "\<forall>c. domain (eq_pred c) = c \<times>\<^sub>c c"
    using cfunc_type_def eq_pred_type by auto
  then have "g \<circ>\<^sub>c y0 \<noteq> \<f>"
    using f4 f3 f2 by (metis (no_types) char_of_singleton1 comp_associative g_def true_false_distinct y_def)
  then show ?thesis
    using f1 by (metis (no_types) cfunc_type_def comp_associative false_func_type h_def id_right_unit2 id_type one_unique_element terminal_func_type y_def)
qed
  then show False
    using gp_eqs_hp assms(1,2) cfunc_type_def epimorphism_def g_type h_type by auto
qed




(* Proposition 2.2.9 *)
lemma pullback_of_epi_is_epi1:
assumes "f: Y \<rightarrow> Z" "epimorphism f" "is_pullback A Y X Z (q1) f (q0) g "
shows "epimorphism (q0)" 
proof - 
  have surj_f: "surjective f"
    using assms(1) assms(2) epi_is_surj by auto
  have "surjective (q0)"
    unfolding surjective_def
  proof(auto)
    fix y
    assume y_type: "y \<in>\<^sub>c codomain q0"
    then have codomain_gy: "g \<circ>\<^sub>c y \<in>\<^sub>c Z"
      using assms(3) cfunc_type_def is_pullback_def square_commutes_def by (typecheck_cfuncs, auto)
    then have z_exists: "\<exists> z. z \<in>\<^sub>c Y \<and> f \<circ>\<^sub>c z = g \<circ>\<^sub>c y"
      using assms(1) cfunc_type_def surj_f surjective_def by auto
    then obtain z where z_def: "z \<in>\<^sub>c Y \<and> f \<circ>\<^sub>c z = g \<circ>\<^sub>c y"
      by blast
    then have "\<exists>! k. k: one \<rightarrow> A \<and> q0 \<circ>\<^sub>c k = y \<and> q1 \<circ>\<^sub>c k =z"
      by (smt (verit) assms(3) cfunc_type_def is_pullback_def square_commutes_def y_type z_def)
    then show "\<exists>x. x \<in>\<^sub>c domain q0 \<and> q0 \<circ>\<^sub>c x = y"
      using assms(3) cfunc_type_def is_pullback_def square_commutes_def by auto
  qed 
  then show ?thesis
    using surjective_is_epimorphism by blast
qed



(* Proposition 2.2.9b *)
lemma pullback_of_epi_is_epi2:
assumes "g: X \<rightarrow> Z" "epimorphism g" "is_pullback A Y X Z (q1) f (q0) g "
shows "epimorphism (q1)" 
proof - 
  have surj_g: "surjective g"
    using assms(1) assms(2) epi_is_surj by auto
  have "surjective (q1)"
    unfolding surjective_def
  proof(auto)
    fix y
    assume y_type: "y \<in>\<^sub>c codomain q1"
    then have codomain_gy: "f \<circ>\<^sub>c y \<in>\<^sub>c Z"
      using assms(3) cfunc_type_def comp_type is_pullback_def square_commutes_def by auto
    then have z_exists: "\<exists> z. z \<in>\<^sub>c X \<and> g \<circ>\<^sub>c z = f \<circ>\<^sub>c y"
      using assms(1) cfunc_type_def surj_g surjective_def by auto
    then obtain z where z_def: "z \<in>\<^sub>c X \<and> g \<circ>\<^sub>c z = f \<circ>\<^sub>c y"
      by blast
    then have "\<exists>! k. k: one \<rightarrow> A \<and> q0 \<circ>\<^sub>c k = z \<and> q1 \<circ>\<^sub>c k =y"
      by (smt (verit, ccfv_threshold) assms(3) cfunc_type_def is_pullback_def square_commutes_def y_type)      
    then show "\<exists>x. x \<in>\<^sub>c domain q1 \<and> q1 \<circ>\<^sub>c x = y"
      using assms(3) cfunc_type_def is_pullback_def square_commutes_def by auto
  qed
  then show ?thesis
    using surjective_is_epimorphism by blast
qed


(* Proposition 2.2.9c *)
lemma pullback_of_mono_is_mono1:
assumes "g: X \<rightarrow> Z" "monomorphism f" "is_pullback A Y X Z (q1) f (q0) g "
shows "monomorphism (q0)" 
proof(unfold monomorphism_def2, auto)
  fix u v Q a x
  assume u_type: "u : Q \<rightarrow> a"  (*Q is arbitrary while "a" is actually just A, and we will establish this soon.*)
  assume v_type: "v : Q \<rightarrow> a"
  assume q0_type: "q0 :  a \<rightarrow> x"    (*x is actually just X*)
  assume equals: "q0 \<circ>\<^sub>c u = q0 \<circ>\<^sub>c v" 

  have a_is_A: "a = A"
    using assms(3) cfunc_type_def is_pullback_def q0_type square_commutes_def by force
  have x_is_X: "x = X"
    using assms(3) cfunc_type_def is_pullback_def q0_type square_commutes_def by fastforce
  have u_type2[type_rule]: "u : Q \<rightarrow> A"
    using a_is_A u_type by blast
  have v_type2[type_rule]: "v : Q \<rightarrow> A"
    using a_is_A v_type by blast
  have q1_type2[type_rule]: "q0 : A \<rightarrow> X"
    using a_is_A q0_type x_is_X by blast

  have eqn1: "g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u) = f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v)"
  proof - 
    have "g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u) = g \<circ>\<^sub>c q0 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v)"
      using assms(3) cfunc_type_def comp_associative is_pullback_def square_commutes_def by (typecheck_cfuncs, force)
    then show ?thesis
      by (simp add: calculation)
  qed 

  have eqn2: "q1 \<circ>\<^sub>c u =  q1  \<circ>\<^sub>c v"
  proof - 
    have f1: "f \<circ>\<^sub>c q1 \<circ>\<^sub>c u = g \<circ>\<^sub>c q0 \<circ>\<^sub>c u"
      using assms(3) comp_associative2 is_pullback_def square_commutes_def by (typecheck_cfuncs, auto)
    also have "... = g \<circ>\<^sub>c q0 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = f \<circ>\<^sub>c q1 \<circ>\<^sub>c v"
      using eqn1 equals by fastforce
    then show ?thesis
      by (typecheck_cfuncs, smt (verit, ccfv_threshold) f1 assms(2) assms(3) eqn1 is_pullback_def monomorphism_def3 square_commutes_def)
  qed

  have uniqueness: "\<exists>! j. (j : Q \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = q1 \<circ>\<^sub>c v \<and> q0 \<circ>\<^sub>c j = q0 \<circ>\<^sub>c u)"
   by (typecheck_cfuncs, smt (verit, ccfv_threshold) assms(3) eqn1 is_pullback_def square_commutes_def)
  then show "u = v"
    using eqn2 equals uniqueness by (typecheck_cfuncs, auto)
qed


(* Proposition 2.2.9d *)
lemma pullback_of_mono_is_mono2:
assumes "g: X \<rightarrow> Z" "monomorphism g" "is_pullback A Y X Z (q1) f (q0) g "
shows "monomorphism (q1)" 
proof(unfold monomorphism_def2, auto)
  fix u v Q a y
  assume u_type: "u : Q \<rightarrow> a"  (*Q is arbitrary while "a" is actually just A, and we will establish this soon.*)
  assume v_type: "v : Q \<rightarrow> a"
  assume q1_type: "q1 :  a \<rightarrow> y" (* y is actually just Y*)
  assume equals: "q1 \<circ>\<^sub>c u = q1 \<circ>\<^sub>c v" 

  have a_is_A: "a = A"
    using assms(3) cfunc_type_def is_pullback_def q1_type square_commutes_def by force
  have y_is_Y: "y = Y"
    using assms(3) cfunc_type_def is_pullback_def q1_type square_commutes_def by fastforce
  have u_type2[type_rule]: "u : Q \<rightarrow> A"
    using a_is_A u_type by blast
  have v_type2[type_rule]: "v : Q \<rightarrow> A"
    using a_is_A v_type by blast
  have q1_type2[type_rule]: "q1 : A \<rightarrow> Y"
    using a_is_A q1_type y_is_Y by blast

  have eqn1: "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)"
  proof - 
    have "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = f \<circ>\<^sub>c q1 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)"
      using assms(3) cfunc_type_def comp_associative is_pullback_def square_commutes_def by (typecheck_cfuncs, force)
    then show ?thesis
      by (simp add: calculation)
  qed 


  have eqn2: "q0 \<circ>\<^sub>c u =  q0  \<circ>\<^sub>c v"
  proof - 
    have f1: "g \<circ>\<^sub>c q0 \<circ>\<^sub>c u = f \<circ>\<^sub>c q1 \<circ>\<^sub>c u"
      using assms(3) comp_associative2 is_pullback_def square_commutes_def by (typecheck_cfuncs, auto)
    also have "... = f \<circ>\<^sub>c q1 \<circ>\<^sub>c v"
      by (simp add: equals)
    also have "... = g \<circ>\<^sub>c q0 \<circ>\<^sub>c v"
      using eqn1 equals by fastforce
    then show ?thesis
      by (typecheck_cfuncs, smt (verit, ccfv_threshold) f1 assms(2) assms(3) eqn1 is_pullback_def monomorphism_def3 square_commutes_def)
  qed
  have uniqueness: "\<exists>! j. (j : Q \<rightarrow> A \<and> q0 \<circ>\<^sub>c j = q0 \<circ>\<^sub>c v \<and> q1 \<circ>\<^sub>c j = q1 \<circ>\<^sub>c u)"
   by (typecheck_cfuncs, smt (verit, ccfv_threshold) assms(3) eqn1 is_pullback_def square_commutes_def)
  then show "u = v"
    using eqn2 equals uniqueness by (typecheck_cfuncs, auto)
qed



lemma fib_prod_left_id_iso:
  assumes "g : Y \<rightarrow> X"
  shows  "(X \<^bsub>id(X)\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<cong> Y"
proof - 
  have is_pullback: "is_pullback (X \<^bsub>id(X)\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) Y X X (fibered_product_right_proj X (id(X)) g Y) g (fibered_product_left_proj X (id(X)) g Y) (id(X)) "
    using assms fibered_product_is_pullback by (typecheck_cfuncs, blast)
  then have mono: "monomorphism(fibered_product_right_proj X (id(X)) g Y)"
    using assms by (typecheck_cfuncs, meson id_isomorphism iso_imp_epi_and_monic pullback_of_mono_is_mono2)
  have "epimorphism(fibered_product_right_proj X (id(X)) g Y)"
    by (meson id_isomorphism id_type is_pullback iso_imp_epi_and_monic pullback_of_epi_is_epi2)
  then have "isomorphism(fibered_product_right_proj X (id(X)) g Y)"
    by (simp add: epi_mon_is_iso mono)
  then show ?thesis
    using assms fibered_product_right_proj_type id_type is_isomorphic_def by blast
qed



lemma fib_prod_right_id_iso:
  assumes "f : X \<rightarrow> Y"
  shows  "(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>id(Y)\<^esub> Y) \<cong> X"
proof - 
  have is_pullback: "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>id(Y)\<^esub> Y) Y X Y (fibered_product_right_proj X f (id(Y)) Y) (id(Y)) (fibered_product_left_proj X f (id(Y)) Y) f "
    using assms fibered_product_is_pullback by (typecheck_cfuncs, blast)
    
  then have mono: "monomorphism(fibered_product_left_proj X f (id(Y)) Y)"
    using assms by (typecheck_cfuncs, meson id_isomorphism is_pullback iso_imp_epi_and_monic pullback_of_mono_is_mono1)
  have "epimorphism(fibered_product_left_proj X f (id(Y)) Y)"
    by (meson id_isomorphism id_type is_pullback iso_imp_epi_and_monic pullback_of_epi_is_epi1)
  then have "isomorphism(fibered_product_left_proj X f (id(Y)) Y)"
    by (simp add: epi_mon_is_iso mono)
  then show ?thesis
    using assms fibered_product_left_proj_type id_type is_isomorphic_def by blast
qed




(*Can we give this a better name?*)
lemma pullback_iff_product:
  assumes "terminal_object(T)"
  assumes f_type: "f : Y \<rightarrow> T" 
  assumes g_type: "g : X \<rightarrow> T"
  shows "(is_pullback P Y X T (pY) f (pX) g) = (is_cart_prod P pX pY X Y)"
proof(auto)
  assume pullback: "is_pullback P Y X T pY f pX g"
  have f_type[type_rule]: "f : Y \<rightarrow> T"
    using is_pullback_def pullback square_commutes_def by force
  have g_type[type_rule]: "g : X \<rightarrow> T"
    using is_pullback_def pullback square_commutes_def by force
  show "is_cart_prod P pX pY X Y"
  proof(unfold is_cart_prod_def, auto)
    show pX_type[type_rule]: "pX : P \<rightarrow> X"
      using pullback is_pullback_def square_commutes_def by force
    show pY_type[type_rule]: "pY : P \<rightarrow> Y"
      using pullback is_pullback_def square_commutes_def by force
    show "\<And>x y Z.
       x : Z \<rightarrow> X \<Longrightarrow>
       y : Z \<rightarrow> Y \<Longrightarrow>
       \<exists>h. h : Z \<rightarrow> P \<and>
           pX \<circ>\<^sub>c h = x \<and> pY \<circ>\<^sub>c h = y \<and> (\<forall>h2. h2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h2 = x \<and> pY \<circ>\<^sub>c h2 = y \<longrightarrow> h2 = h)"
    proof - 
      fix x y Z
      assume x_type[type_rule]: "x : Z \<rightarrow> X"
      assume y_type[type_rule]: "y : Z \<rightarrow> Y"
      have  "\<And>Z k h. k : Z \<rightarrow> Y \<Longrightarrow> h : Z \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h \<Longrightarrow> \<exists>j. j : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j = k \<and> pX \<circ>\<^sub>c j = h"
        using is_pullback_def pullback by blast
      then have "\<exists>h. h : Z \<rightarrow> P \<and>
           pX \<circ>\<^sub>c h = x \<and> pY \<circ>\<^sub>c h = y"
        by (smt (verit, ccfv_threshold) assms cfunc_type_def codomain_comp domain_comp f_type g_type terminal_object_def x_type y_type)
      then show "\<exists>h. h : Z \<rightarrow> P \<and>
           pX \<circ>\<^sub>c h = x \<and> pY \<circ>\<^sub>c h = y \<and> (\<forall>h2. h2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h2 = x \<and> pY \<circ>\<^sub>c h2 = y \<longrightarrow> h2 = h)"
        by (typecheck_cfuncs, smt (verit, ccfv_threshold) comp_associative2 is_pullback_def pullback square_commutes_def)
    qed
  qed
next
  assume prod: "is_cart_prod P pX pY X Y"
  show "is_pullback P Y X T pY f pX g"
  proof(unfold is_pullback_def, auto)
    show "square_commutes P Y X T pY f pX g"
      using prod assms  
      by (typecheck_cfuncs, metis assms(1) comp_type is_cart_prod_def prod square_commutes_def terminal_object_def)
    show "\<And>Z k h. k : Z \<rightarrow> Y \<Longrightarrow> h : Z \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h \<Longrightarrow> \<exists>j. j : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j = k \<and> pX \<circ>\<^sub>c j = h"
      using is_cart_prod_def prod by blast
    show "\<And>Z j y.
       pY \<circ>\<^sub>c j : Z \<rightarrow> Y \<Longrightarrow>
       pX \<circ>\<^sub>c j : Z \<rightarrow> X \<Longrightarrow>
       f \<circ>\<^sub>c pY \<circ>\<^sub>c j = g \<circ>\<^sub>c pX \<circ>\<^sub>c j \<Longrightarrow> j : Z \<rightarrow> P \<Longrightarrow> y : Z \<rightarrow> P \<Longrightarrow> pY \<circ>\<^sub>c y = pY \<circ>\<^sub>c j \<Longrightarrow> pX \<circ>\<^sub>c y = pX \<circ>\<^sub>c j \<Longrightarrow> j = y"
      using is_cart_prod_def prod by blast
  qed
qed





lemma terminal_fib_prod_iso:
  "(X \<^bsub>\<beta>\<^bsub>X\<^esub>\<^esub>\<times>\<^sub>c\<^bsub>\<beta>\<^bsub>Y\<^esub>\<^esub> Y) \<cong> X \<times>\<^sub>c Y"
proof - 
  have "(is_pullback (X \<^bsub>\<beta>\<^bsub>X\<^esub>\<^esub>\<times>\<^sub>c\<^bsub>\<beta>\<^bsub>Y\<^esub>\<^esub> Y) Y X one (fibered_product_right_proj X (\<beta>\<^bsub>X\<^esub>) (\<beta>\<^bsub>Y\<^esub>) Y) (\<beta>\<^bsub>Y\<^esub>) (fibered_product_left_proj X (\<beta>\<^bsub>X\<^esub>) (\<beta>\<^bsub>Y\<^esub>) Y) (\<beta>\<^bsub>X\<^esub>))"
    using pullback_iff_product  
    by (typecheck_cfuncs, simp add: fibered_product_is_pullback)
  then  have "(is_cart_prod (X \<^bsub>\<beta>\<^bsub>X\<^esub>\<^esub>\<times>\<^sub>c\<^bsub>\<beta>\<^bsub>Y\<^esub>\<^esub> Y) (fibered_product_left_proj X (\<beta>\<^bsub>X\<^esub>) (\<beta>\<^bsub>Y\<^esub>) Y) (fibered_product_right_proj X (\<beta>\<^bsub>X\<^esub>) (\<beta>\<^bsub>Y\<^esub>) Y)  X Y)"
    by (meson one_terminal_object pullback_iff_product terminal_func_type)
  then show ?thesis
    by (metis canonical_cart_prod_is_cart_prod cart_prods_isomorphic fst_conv is_isomorphic_def snd_conv)
qed

(*The generalization of the previous lemma.*)
lemma terminal_fib_prod_iso2:
  assumes "terminal_object(T)"
  assumes f_type: "f : Y \<rightarrow> T" 
  assumes g_type: "g : X \<rightarrow> T"
  shows "(X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) \<cong> X \<times>\<^sub>c Y"
proof - 
  have "(is_pullback (X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) Y X T (fibered_product_right_proj X g f Y) f (fibered_product_left_proj X g f Y) g)"
    using assms pullback_iff_product fibered_product_is_pullback by (typecheck_cfuncs, force)
  then have "(is_cart_prod (X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) (fibered_product_left_proj X g f Y) (fibered_product_right_proj X g f Y)  X Y)"
    using assms by (meson one_terminal_object pullback_iff_product terminal_func_type)
  then show ?thesis
    using assms by (metis canonical_cart_prod_is_cart_prod cart_prods_isomorphic fst_conv is_isomorphic_def snd_conv)
qed






(*This is essentially a duplicate of cfunc_cross_prod_surj from the Terminal
Theory file.  If differs in style by proving the product of epis is epi rather
than proving the products of surjective maps is surjective.  It makes use of 
pullbacks, but ultimately it's a duplicate. However, I think we should leave it 
because it offers different insights into proof style.*)

(* Proposition 2.2.10 *)
lemma product_of_epis_is_epi:
  assumes f_type: "f: X \<rightarrow> Y" and f_epi: "epimorphism(f)"
  assumes g_type: "g: W \<rightarrow> Z" and g_epi: "epimorphism(g)"
  shows "epimorphism(f\<times>\<^sub>f g)"
proof - (*there are serious errors in the diagram in the book!*)
   have decompose_fxg: "f\<times>\<^sub>f g = (f\<times>\<^sub>f id(Z)) \<circ>\<^sub>c (id(X)\<times>\<^sub>f g)"
     using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  
 (*First half proving (f\<times>\<^sub>f id(Z)) is an epimorphism.*)

   have pullback: "is_pullback (X\<times>\<^sub>cZ) X (Y\<times>\<^sub>cZ) Y (left_cart_proj X Z) f (f\<times>\<^sub>f id(Z)) (left_cart_proj Y Z)"
     unfolding is_pullback_def
   proof(auto)
     show "square_commutes (X \<times>\<^sub>c Z) X (Y \<times>\<^sub>c Z) Y (left_cart_proj X Z) f
     (f \<times>\<^sub>f id\<^sub>c Z) (left_cart_proj Y Z)"
       using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_cross_prod square_commutes_def)
     show "\<And>Za k h. k : Za \<rightarrow> X \<Longrightarrow> h : Za \<rightarrow> Y \<times>\<^sub>c Z \<Longrightarrow> f \<circ>\<^sub>c k = left_cart_proj Y Z \<circ>\<^sub>c h \<Longrightarrow>
       \<exists>j. j : Za \<rightarrow> X \<times>\<^sub>c Z \<and> left_cart_proj X Z \<circ>\<^sub>c j = k \<and> (f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c j = h"
     proof-
       fix Za k h
       assume k_type:  "k : Za \<rightarrow> X"
       assume h_type: "h : Za \<rightarrow> Y \<times>\<^sub>c Z"
       assume outer_square: "f \<circ>\<^sub>c k = left_cart_proj Y Z \<circ>\<^sub>c h"
       obtain j where j_def: "j = \<langle>k,right_cart_proj Y Z \<circ>\<^sub>c h\<rangle>"
         by simp
       then have j_type: "j: Za \<rightarrow> X \<times>\<^sub>c Z"
         using cfunc_prod_type comp_type h_type k_type right_cart_proj_type by auto
       have top_triangle: "left_cart_proj X Z \<circ>\<^sub>c j = k"
         using comp_type h_type j_def k_type left_cart_proj_cfunc_prod right_cart_proj_type by auto
       have bottom_triangle: "(f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c j = h"
       proof - 
         have "(f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c j = \<langle>f \<circ>\<^sub>c k,id\<^sub>c Z \<circ>\<^sub>c right_cart_proj Y Z \<circ>\<^sub>c h\<rangle>"
           by (smt cfunc_cross_prod_comp_cfunc_prod comp_type f_type h_type id_type j_def k_type right_cart_proj_type)
         also have "... = \<langle>left_cart_proj Y Z \<circ>\<^sub>c h,right_cart_proj Y Z \<circ>\<^sub>c h\<rangle>"
           by (metis cart_prod_decomp h_type id_left_unit2 outer_square right_cart_proj_cfunc_prod)
         also have "... = h"
           by (metis cfunc_prod_unique comp_type f_type h_type k_type outer_square right_cart_proj_type)
       then show ?thesis
         by (simp add: calculation) 
     qed
     then show "\<exists>j. j : Za \<rightarrow> X \<times>\<^sub>c Z \<and> left_cart_proj X Z \<circ>\<^sub>c j = k \<and> (f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c j = h"
       using j_type top_triangle by blast
   qed
     show "\<And>Za j y.
       left_cart_proj X Z \<circ>\<^sub>c j : Za \<rightarrow> X \<Longrightarrow>
       (f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c j : Za \<rightarrow> Y \<times>\<^sub>c Z \<Longrightarrow>
       f \<circ>\<^sub>c left_cart_proj X Z \<circ>\<^sub>c j =
       left_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c j \<Longrightarrow>
       j : Za \<rightarrow> X \<times>\<^sub>c Z \<Longrightarrow>
       y : Za \<rightarrow> X \<times>\<^sub>c Z \<Longrightarrow>
       left_cart_proj X Z \<circ>\<^sub>c y = left_cart_proj X Z \<circ>\<^sub>c j \<Longrightarrow>
       (f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c y = (f \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c j \<Longrightarrow> j = y"
         by (smt cart_prod_decomp cart_prod_eq2 cfunc_cross_prod_comp_cfunc_prod f_type id_left_unit2 id_type left_cart_proj_cfunc_prod)
     qed
     then have fid_epi: "epimorphism(f\<times>\<^sub>f id(Z))"
       using f_epi f_type pullback_of_epi_is_epi1 by blast

(*Second half proving (id(X)\<times>\<^sub>f g) is an epimorphism.*)

    have pullback2: "is_pullback (X\<times>\<^sub>cW) W (X\<times>\<^sub>cZ) Z (right_cart_proj X W) g (id(X)\<times>\<^sub>f g) (right_cart_proj X Z)"
         unfolding is_pullback_def
    proof(auto)
      show "square_commutes (X \<times>\<^sub>c W) W (X \<times>\<^sub>c Z) Z (right_cart_proj X W) g
     (id\<^sub>c X \<times>\<^sub>f g) (right_cart_proj X Z)"
        using assms by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_cross_prod square_commutes_def)
      show "\<And>Za k h. 
       k : Za \<rightarrow> W \<Longrightarrow>
       h : Za \<rightarrow> X \<times>\<^sub>c Z \<Longrightarrow>
       g \<circ>\<^sub>c k = right_cart_proj X Z \<circ>\<^sub>c h \<Longrightarrow>
       \<exists>j. j : Za \<rightarrow> X \<times>\<^sub>c W \<and>
           right_cart_proj X W \<circ>\<^sub>c j = k \<and> (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c j = h"
 proof-
       fix Za k h
       assume k_type:  "k : Za \<rightarrow> W"
       assume h_type: "h : Za \<rightarrow> X \<times>\<^sub>c Z"
       assume outer_square: "g \<circ>\<^sub>c k = right_cart_proj X Z \<circ>\<^sub>c h"
       obtain j where j_def: "j = \<langle>left_cart_proj X Z \<circ>\<^sub>c h,k\<rangle>"
         by simp
       then have j_type: "j : Za \<rightarrow> X \<times>\<^sub>c W"
         using cfunc_prod_type comp_type h_type k_type left_cart_proj_type by auto
       have top_triangle: "right_cart_proj X W \<circ>\<^sub>c j = k"
         using comp_type h_type j_def k_type left_cart_proj_type right_cart_proj_cfunc_prod by blast
       have bottom_triangle: "(id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c j = h"
       proof - 
         have "(id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c j = \<langle>id\<^sub>c X \<circ>\<^sub>c left_cart_proj X Z \<circ>\<^sub>c h,g \<circ>\<^sub>c k\<rangle>"
           by (smt cfunc_cross_prod_comp_cfunc_prod comp_type g_type h_type id_type j_def k_type left_cart_proj_type)
         also have "... = \<langle>left_cart_proj X Z \<circ>\<^sub>c h,right_cart_proj X Z \<circ>\<^sub>c h\<rangle>"
           by (metis cart_prod_decomp h_type id_left_unit2 left_cart_proj_cfunc_prod outer_square)
         also have "... = h"
           by (metis cfunc_prod_unique comp_type g_type h_type k_type left_cart_proj_type outer_square)
         then show ?thesis
           by (simp add: calculation)
       qed
       then show "\<exists>j. j : Za \<rightarrow> X \<times>\<^sub>c W \<and>
           right_cart_proj X W \<circ>\<^sub>c j = k \<and> (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c j = h"
         using j_type top_triangle by blast
     qed
     show "\<And>Za j y.
       right_cart_proj X W \<circ>\<^sub>c j : Za \<rightarrow> W \<Longrightarrow>
       (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c j : Za \<rightarrow> X \<times>\<^sub>c Z \<Longrightarrow>
       g \<circ>\<^sub>c right_cart_proj X W \<circ>\<^sub>c j =
       right_cart_proj X Z \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c j \<Longrightarrow>
       j : Za \<rightarrow> X \<times>\<^sub>c W \<Longrightarrow>
       y : Za \<rightarrow> X \<times>\<^sub>c W \<Longrightarrow>
       right_cart_proj X W \<circ>\<^sub>c y = right_cart_proj X W \<circ>\<^sub>c j \<Longrightarrow>
       (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c y = (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c j \<Longrightarrow> j = y"
       by (smt cart_prod_decomp cart_prod_eq2 cfunc_cross_prod_comp_cfunc_prod g_type id_left_unit2 id_type right_cart_proj_cfunc_prod)
   qed
   then have "epimorphism(id(X)\<times>\<^sub>f g)"
     using g_epi g_type pullback_of_epi_is_epi1 by blast
   then show ?thesis
     using fid_epi cfunc_type_def composition_of_epi_pair_is_epi decompose_fxg is_pullback_def pullback pullback2 square_commutes_def by auto
qed

definition set_subtraction :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> cset" (infix "\<setminus>" 60) where
  "Y \<setminus> X = (SOME E. \<exists> m'.  equalizer E m' (characteristic_func (snd X)) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>))"

lemma set_subtraction_equalizer:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "\<exists> m'.  equalizer (Y \<setminus> (X,m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
proof -
  have "\<exists> E m'. equalizer E m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    using assms equalizer_exists by (typecheck_cfuncs, auto)
  then have "\<exists> m'.  equalizer (Y \<setminus> (X,m)) m' (characteristic_func (snd (X,m))) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    by (unfold set_subtraction_def, rule_tac someI_ex, auto)
  then show "\<exists> m'.  equalizer (Y \<setminus> (X,m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    by auto
qed

definition complement_morphism :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>c" [1000]) where
  "m\<^sup>c = (SOME m'.  equalizer (codomain m \<setminus> (domain m, m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>))"

lemma complement_morphism_equalizer:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "equalizer (Y \<setminus> (X,m)) m\<^sup>c (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
proof -
  have "\<exists> m'. equalizer (codomain m \<setminus> (domain m, m)) m' (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>)"
    by (simp add: assms cfunc_type_def set_subtraction_equalizer)
  then have "equalizer (codomain m \<setminus> (domain m, m)) m\<^sup>c (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>)"
    by (unfold complement_morphism_def, rule_tac someI_ex, auto)
  then show "equalizer (Y \<setminus> (X, m)) m\<^sup>c (characteristic_func m) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    using assms unfolding cfunc_type_def by auto
qed

lemma complement_morphism_type[type_rule]:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "m\<^sup>c : Y \<setminus> (X,m) \<rightarrow> Y"
  using assms cfunc_type_def characteristic_func_type complement_morphism_equalizer equalizer_def by auto

lemma complement_morphism_mono:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "monomorphism m\<^sup>c"
  using assms complement_morphism_equalizer equalizer_is_monomorphism by blast

lemma complement_morphism_eq:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  shows "characteristic_func m \<circ>\<^sub>c m\<^sup>c  = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c m\<^sup>c"
  using assms complement_morphism_equalizer unfolding equalizer_def by auto

lemma characteristic_func_true_not_complement_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_true: "characteristic_func m \<circ>\<^sub>c x = \<t>"
  shows "\<not> x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m),m\<^sup>c)"
proof
  assume in_complement: "x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m), m\<^sup>c)"
  then obtain x' where x'_type: "x' \<in>\<^sub>c X \<setminus> (B,m)" and x'_def: "m\<^sup>c \<circ>\<^sub>c x' = x"
    using assms cfunc_type_def complement_morphism_type factors_through_def relative_member_def2
    by auto
  then have "characteristic_func m \<circ>\<^sub>c m\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m\<^sup>c"
    using assms complement_morphism_equalizer equalizer_def by blast
  then have "characteristic_func m \<circ>\<^sub>c x = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x"
    using assms x'_type complement_morphism_type
    by (typecheck_cfuncs, smt x'_def assms cfunc_type_def comp_associative domain_comp)
  then have "characteristic_func m \<circ>\<^sub>c x = \<f>"
    using assms by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  then show False
    using characteristic_func_true true_false_distinct by auto
qed

lemma characteristic_func_false_complement_member:
  assumes "m : B \<rightarrow> X" "monomorphism m" "x \<in>\<^sub>c X"
  assumes characteristic_func_false: "characteristic_func m \<circ>\<^sub>c x = \<f>"
  shows "x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m),m\<^sup>c)"
proof -
  have x_equalizes: "characteristic_func m \<circ>\<^sub>c x = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x"
    by (metis assms(3) characteristic_func_false false_func_type id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  have "\<And>h F. h : F \<rightarrow> X \<and> characteristic_func m \<circ>\<^sub>c h = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h \<longrightarrow>
                  (\<exists>!k. k : F \<rightarrow> X \<setminus> (B, m) \<and> m\<^sup>c \<circ>\<^sub>c k = h)"
    using assms complement_morphism_equalizer unfolding equalizer_def
    by (smt cfunc_type_def characteristic_func_type) 
  then obtain x' where x'_type: "x' \<in>\<^sub>c X \<setminus> (B, m)" and x'_def: "m\<^sup>c \<circ>\<^sub>c x' = x"
    by (metis assms(3) cfunc_type_def comp_associative false_func_type terminal_func_type x_equalizes)
  then show "x \<in>\<^bsub>X\<^esub> (X \<setminus> (B, m),m\<^sup>c)"
    unfolding relative_member_def factors_through_def
    using assms complement_morphism_mono complement_morphism_type cfunc_type_def by auto
qed

lemma in_complement_not_in_subset:
  assumes "m : X \<rightarrow> Y" "monomorphism m" "x \<in>\<^sub>c Y"
  assumes "x \<in>\<^bsub>Y\<^esub> (Y \<setminus> (X,m), m\<^sup>c)"
  shows "\<not> x \<in>\<^bsub>Y\<^esub> (X, m)"
  using assms characteristic_func_false_not_relative_member
    characteristic_func_true_not_complement_member characteristic_func_type comp_type
    true_false_only_truth_values by blast

lemma not_in_subset_in_complement:
  assumes "m : X \<rightarrow> Y" "monomorphism m" "x \<in>\<^sub>c Y"
  assumes "\<not> x \<in>\<^bsub>Y\<^esub> (X, m)"
  shows "x \<in>\<^bsub>Y\<^esub> (Y \<setminus> (X,m), m\<^sup>c)"
  using assms characteristic_func_false_complement_member characteristic_func_true_relative_member
    characteristic_func_type comp_type true_false_only_truth_values by blast

lemma complement_disjoint:
  assumes "m : X \<rightarrow> Y" "monomorphism m"
  assumes "x \<in>\<^sub>c X" "x' \<in>\<^sub>c Y \<setminus> (X,m)"
  shows "m \<circ>\<^sub>c x \<noteq> m\<^sup>c \<circ>\<^sub>c x'"
proof 
  assume "m \<circ>\<^sub>c x = m\<^sup>c \<circ>\<^sub>c x'"
  then have "characteristic_func m \<circ>\<^sub>c m \<circ>\<^sub>c x = characteristic_func m \<circ>\<^sub>c m\<^sup>c \<circ>\<^sub>c x'"
    by auto
  then have "(characteristic_func m \<circ>\<^sub>c m) \<circ>\<^sub>c x = (characteristic_func m \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
    using assms characteristic_func_eq complement_morphism_eq by auto
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c m\<^sup>c \<circ>\<^sub>c x'"
    using assms comp_associative2 by (typecheck_cfuncs, smt terminal_func_comp terminal_func_type)
  then have "\<t> \<circ>\<^sub>c id one = \<f> \<circ>\<^sub>c id one"
    using assms by (smt cfunc_type_def comp_associative complement_morphism_type id_type one_unique_element terminal_func_comp terminal_func_type)
  then have "\<t> = \<f>"
    using false_func_type id_right_unit2 true_func_type by auto
  then show False
    using true_false_distinct by auto
qed

lemma set_subtraction_right_cong:
  assumes m_type[type_rule]: "m : A \<rightarrow> C" and m_mono[type_rule]: "monomorphism m"
  assumes i_type[type_rule]: "i : B \<rightarrow> A" and i_iso: "isomorphism i"
  shows "C \<setminus> (A,m) \<cong> C \<setminus> (B, m \<circ>\<^sub>c i)"
proof -
  have mi_mono[type_rule]: "monomorphism (m \<circ>\<^sub>c i)"
    using cfunc_type_def composition_of_monic_pair_is_monic i_iso i_type iso_imp_epi_and_monic m_mono m_type by presburger
  obtain \<chi>m where \<chi>m_type[type_rule]: "\<chi>m : C \<rightarrow> \<Omega>" and \<chi>m_def: "\<chi>m = characteristic_func m"
    using characteristic_func_type m_mono m_type by blast
  obtain \<chi>mi where \<chi>mi_type[type_rule]: "\<chi>mi : C \<rightarrow> \<Omega>" and \<chi>mi_def: "\<chi>mi = characteristic_func (m \<circ>\<^sub>c i)"
    by (typecheck_cfuncs)
  have "\<And> c. c \<in>\<^sub>c C \<Longrightarrow> (\<chi>m \<circ>\<^sub>c c = \<t>) = (\<chi>mi \<circ>\<^sub>c c = \<t>)"
  proof -
    fix c
    assume c_type[type_rule]: "c \<in>\<^sub>c C"
    have "(\<chi>m \<circ>\<^sub>c c = \<t>) = (c \<in>\<^bsub>C\<^esub> (A,m))"
      unfolding \<chi>m_def by (typecheck_cfuncs, meson characteristic_func_true_relative_member m_mono relative_member_characteristic_func_true)
    also have "... = (\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a)"
      using cfunc_type_def factors_through_def m_mono relative_member_def2 by (typecheck_cfuncs, auto)
    also have "... = (\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c i \<circ>\<^sub>c b)"
      by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_type epi_is_surj i_iso iso_imp_epi_and_monic surjective_def)
    also have "... = (c \<in>\<^bsub>C\<^esub> (B,m \<circ>\<^sub>c i))"
      using cfunc_type_def comp_associative2 composition_of_monic_pair_is_monic factors_through_def2 i_iso iso_imp_epi_and_monic m_mono relative_member_def2
      by (typecheck_cfuncs, auto)
    also have "... = (\<chi>mi \<circ>\<^sub>c c = \<t>)"
      unfolding \<chi>mi_def by (typecheck_cfuncs, metis cfunc_type_def composition_of_monic_pair_is_monic i_iso iso_imp_epi_and_monic m_mono not_relative_member_characteristic_func_false relative_member_characteristic_func_true true_false_distinct)
    then show "(\<chi>m \<circ>\<^sub>c c = \<t>) = (\<chi>mi \<circ>\<^sub>c c = \<t>)"
      using calculation by auto
  qed
  then have "\<And> c. c \<in>\<^sub>c C \<Longrightarrow> (\<chi>m \<circ>\<^sub>c c = \<f>) = (\<chi>mi \<circ>\<^sub>c c = \<f>)"
    using \<chi>m_type \<chi>mi_type comp_type true_false_only_truth_values by fastforce
  then have \<chi>m_\<chi>mi_conv: "\<And> c. c \<in>\<^sub>c C \<Longrightarrow> (\<chi>m \<circ>\<^sub>c c = \<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub> \<circ>\<^sub>c c) = (\<chi>mi \<circ>\<^sub>c c = \<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub> \<circ>\<^sub>c c)"
    by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  have "(\<chi>m \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c) = (\<chi>mi \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c)"
  proof(auto)
    show "\<chi>m \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c \<Longrightarrow> \<chi>mi \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c"
      using assms  by (typecheck_cfuncs, simp add: \<chi>mi_def complement_morphism_eq mi_mono)
(*   using \<chi>m_\<chi>mi_conv apply typecheck_cfuncs*)
    show "\<chi>mi \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c \<Longrightarrow> \<chi>m \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c"
      using assms apply typecheck_cfuncs

  (*thm complement_morphism_eq
  have "characteristic_func (m \<circ>\<^sub>c i) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c"
    using complement_morphism_eq mi_mono by (typecheck_cfuncs, blast)
  then have "characteristic_func m \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c"
    using \<chi>m_\<chi>mi_conv unfolding \<chi>m_def \<chi>mi_def 
  
  then have "(characteristic_func m \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c (m \<circ>\<^sub>c i)\<^sup>c) \<and> (characteristic_func (m \<circ>\<^sub>c i) \<circ>\<^sub>c m\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>) \<circ>\<^sub>c m\<^sup>c)"
    unfolding \<chi>m_def \<chi>mi_def apply (typecheck_cfuncs)
    
  then show "C \<setminus> (A,m) \<cong> C \<setminus> (B, m \<circ>\<^sub>c i)"*)
    oops

lemma set_subtraction_left_cong:
  assumes m_type[type_rule]: "m : C \<rightarrow> A" and m_mono[type_rule]: "monomorphism m"
  assumes i_type[type_rule]: "i : A \<rightarrow> B" and i_iso: "isomorphism i"
  shows "A \<setminus> (C,m) \<cong> B \<setminus> (C, i \<circ>\<^sub>c m)"
  oops

end





