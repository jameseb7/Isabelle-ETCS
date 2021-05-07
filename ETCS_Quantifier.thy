theory ETCS_Quantifier
  imports ETCS_Pred ETCS_Func
begin

definition FORALL :: "cset \<Rightarrow> cfunc" where
  "FORALL X = (THE \<chi>. is_pullback one one (\<Omega>\<^bsup>X\<^esup>) \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<chi>)"

lemma FORALL_is_pullback:
  "is_pullback one one (\<Omega>\<^bsup>X\<^esup>) \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) (FORALL X)"
  unfolding FORALL_def
  using characteristic_function_exists element_monomorphism
  by (typecheck_cfuncs, rule_tac the1I2, auto)

lemma FORALL_type[type_rule]:
  "FORALL X : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>"
  using FORALL_is_pullback unfolding is_pullback_def square_commutes_def by auto

lemma all_true_implies_FORALL_true:
  assumes p_type: "p : X \<rightarrow> \<Omega>" and all_p_true: "\<And> x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t>"
  shows "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp> = \<t>"
proof -
  have "p \<circ>\<^sub>c left_cart_proj X one = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>"
  proof (rule one_separator[where X="X \<times>\<^sub>c one", where Y="\<Omega>"])
    show "p \<circ>\<^sub>c left_cart_proj X one : X \<times>\<^sub>c one \<rightarrow> \<Omega>"
      using p_type by typecheck_cfuncs
    show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub> : X \<times>\<^sub>c one \<rightarrow> \<Omega>"
      by typecheck_cfuncs
  next
    fix x
    assume x_type: "x \<in>\<^sub>c X \<times>\<^sub>c one"

    have "(p \<circ>\<^sub>c left_cart_proj X one) \<circ>\<^sub>c x = p \<circ>\<^sub>c (left_cart_proj X one \<circ>\<^sub>c x)"
      using x_type p_type comp_associative2 by (typecheck_cfuncs, auto)
    also have "... = \<t>"
      using x_type all_p_true by (typecheck_cfuncs, auto)
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub> \<circ>\<^sub>c x "
      using x_type by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>) \<circ>\<^sub>c x"
      using x_type comp_associative2 by (typecheck_cfuncs, auto)
    
    then show "(p \<circ>\<^sub>c left_cart_proj X one) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>) \<circ>\<^sub>c x"
      using calculation by auto
  qed
  then have "(p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
    by simp
  then have "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>one\<^esub>"
    using FORALL_is_pullback unfolding is_pullback_def square_commutes_def by auto
  then show "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp> = \<t>"
    using NOT_false_is_true NOT_is_pullback is_pullback_def square_commutes_def by auto
qed

lemma FORALL_true_implies_all_true:
  assumes p_type: "p : X \<rightarrow> \<Omega>" and FORALL_p_true: "FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp> = \<t>"
  shows "\<And> x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t>"
proof (rule ccontr)
  fix x
  assume x_type: "x \<in>\<^sub>c X"

  assume "p \<circ>\<^sub>c x \<noteq> \<t>"
  then have "p \<circ>\<^sub>c x = \<f>"
    using comp_type p_type true_false_only_truth_values x_type by blast
  then have "p \<circ>\<^sub>c left_cart_proj X one \<circ>\<^sub>c \<langle>x, id one\<rangle> = \<f>"
    using id_type left_cart_proj_cfunc_prod x_type by auto
  then have p_left_proj_false: "p \<circ>\<^sub>c left_cart_proj X one \<circ>\<^sub>c \<langle>x, id one\<rangle> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub> \<circ>\<^sub>c \<langle>x, id one\<rangle>"
    using x_type by (typecheck_cfuncs, metis id_right_unit2 one_unique_element)

  have "\<t> \<circ>\<^sub>c id one = FORALL X \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp>"
    using FORALL_p_true id_right_unit2 true_func_type by auto
  then obtain j where 
      j_type: "j \<in>\<^sub>c one" and 
      j_id: "\<beta>\<^bsub>one\<^esub> \<circ>\<^sub>c j = id one" and
      t_j_eq_p_left_proj: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = (p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp>"
    using FORALL_is_pullback p_type unfolding is_pullback_def by (typecheck_cfuncs, blast)
  then have "j = id one"
    using id_type one_unique_element by blast
  then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> = (p \<circ>\<^sub>c left_cart_proj X one)\<^sup>\<sharp>"
    using id_right_unit2 t_j_eq_p_left_proj p_type by (typecheck_cfuncs, auto)
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub> = p \<circ>\<^sub>c left_cart_proj X one"
    using p_type by (typecheck_cfuncs, metis flat_cancels_sharp)
  then have p_left_proj_true: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub> \<circ>\<^sub>c \<langle>x, id one\<rangle> = p \<circ>\<^sub>c left_cart_proj X one \<circ>\<^sub>c \<langle>x, id one\<rangle>"
    using p_type x_type comp_associative2 by (typecheck_cfuncs, auto)

  have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub> \<circ>\<^sub>c \<langle>x, id one\<rangle> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub> \<circ>\<^sub>c \<langle>x, id one\<rangle>"
    using p_left_proj_false p_left_proj_true by auto
  then have "\<t> \<circ>\<^sub>c id one = \<f> \<circ>\<^sub>c id one"
    by (metis id_type right_cart_proj_cfunc_prod right_cart_proj_type terminal_func_unique x_type)
  then have "\<t> = \<f>"
    using true_func_type false_func_type id_right_unit2 by auto
  then show False
    using true_false_distinct by auto
qed

end