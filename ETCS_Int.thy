theory ETCS_Int
  imports ETCS_Add
begin

definition add_outers :: "cfunc" where
  "add_outers = add_uncurried \<circ>\<^sub>c \<langle>
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle>"

lemma add_outers_type[type_rule]: "add_outers : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_outers_def by typecheck_cfuncs

lemma add_outers_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_outers \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>a,d\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = add_uncurried \<circ>\<^sub>c \<langle>
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding add_outers_def using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>a, d\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed

definition add_inners :: "cfunc" where
  "add_inners = add_uncurried \<circ>\<^sub>c \<langle>
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle>"

lemma add_inners_type[type_rule]: "add_inners : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_inners_def by typecheck_cfuncs
    
lemma add_inners_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_inners \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = add_uncurried \<circ>\<^sub>c \<langle>
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding add_inners_def using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>b, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed

definition int_equiv_set :: "cset" where
  "int_equiv_set = (SOME E. \<exists>m. equalizer E m add_outers add_inners)"

definition int_equiv_morphism :: "cfunc" where
  "int_equiv_morphism = (SOME m. equalizer int_equiv_set m add_outers add_inners)"

lemma int_equiv_equalizer: "equalizer int_equiv_set int_equiv_morphism add_outers add_inners"
  unfolding int_equiv_morphism_def
proof (rule someI_ex)
  show "\<exists>x. equalizer int_equiv_set x add_outers add_inners"
    unfolding int_equiv_set_def
  proof (rule someI_ex)
    show "\<exists>x xa. equalizer x xa add_outers add_inners"
      using add_inners_type add_outers_type equalizer_exists by auto
  qed
qed
    