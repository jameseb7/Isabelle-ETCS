theory ETCS_Summation
  imports ETCS_Add
begin

definition indexed_sum :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "indexed_sum f low = (THE u. u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c 
    \<and> u \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle> 
    \<and> \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma indexed_sum_def2:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c 
    \<and> (indexed_sum f low) \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle> 
    \<and> \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low = (indexed_sum f low) \<circ>\<^sub>c successor"
  unfolding indexed_sum_def
  by (rule theI', typecheck_cfuncs, simp add: natural_number_object_property2)

lemma indexed_sum_type[type_rule]:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  using indexed_sum_def2 assms by auto

lemma indexed_sum_zero:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(indexed_sum f low) \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle>"
  using indexed_sum_def2 assms by auto

lemma indexed_sum_successor:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  shows "indexed_sum f low \<circ>\<^sub>c successor 
    = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low"
  using indexed_sum_def2 assms by auto

lemma 
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low = (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f=successor])
  show "left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "(add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c zero = ((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
  proof - 
    have "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c zero = left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>low, f \<circ>\<^sub>c low\<rangle>"
      using  indexed_sum_zero comp_associative2 by (typecheck_cfuncs, force)
    also have "... = low"
      using comp_type f_type left_cart_proj_cfunc_prod low_type by auto
    also have "... = add2 \<circ>\<^sub>c \<langle>zero, low\<rangle>"
      using add_def add_respects_zero_on_left low_type by presburger
    also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f add1 \<circ>\<^sub>c low) \<circ>\<^sub>c \<langle>zero, id one\<rangle>"
      by (typecheck_cfuncs, simp add: add2_apply cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
    also have "... = (add1 \<circ>\<^sub>c low)\<^sup>\<flat>  \<circ>\<^sub>c \<langle>zero, id one\<rangle>"
      using comp_associative2 inv_transpose_func_def2 by (typecheck_cfuncs, auto)
    also have "... = ((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis id_left_unit2 right_param_def2 right_param_on_el)
    then show ?thesis
      by (simp add: calculation)
  qed

  show "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low"
  proof - 
    have "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c successor =  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (\<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low)"
      by (typecheck_cfuncs, metis comp_associative2 indexed_sum_successor)
    also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low"
      using left_cart_proj_cfunc_prod by (etcs_assocl, typecheck_cfuncs, presburger)
    then show ?thesis
      using calculation by presburger
  qed

  show "((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
  proof - 
    have "((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor = ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f add1 \<circ>\<^sub>c low) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2)
    also have "... =  (((eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f add1))  \<circ>\<^sub>c ((id \<nat>\<^sub>c \<times>\<^sub>f low) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)) \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, smt (z3) comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition)
    also have "... =  (add2   \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, low \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor"
      using add2_def cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by (typecheck_cfuncs, force)
    also have "... =  add2   \<circ>\<^sub>c \<langle>successor, low \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
    also have "... = successor \<circ>\<^sub>c (add2   \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c , low \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
      by (typecheck_cfuncs, metis add2_commutes_succ add2_respects_succ_right id_right_unit2)
    also have "... = successor \<circ>\<^sub>c (eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f (add1 \<circ>\<^sub>c low)) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c ,  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
      using add2_apply cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_right_unit2 by (typecheck_cfuncs, force)
    also have "... = successor \<circ>\<^sub>c (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      using comp_associative2 inv_transpose_func_def2 by (typecheck_cfuncs, force)
    then show ?thesis
      using calculation by presburger
  qed
qed



lemma add_indexed_sum:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n1_type[type_rule]: "n1 \<in>\<^sub>c \<nat>\<^sub>c" and n2_type[type_rule]: "n2 \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (indexed_sum f low) \<circ>\<^sub>c n1)
          +\<^sub>\<nat> (right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(indexed_sum f (successor \<circ>\<^sub>c (low +\<^sub>\<nat> n1))) \<circ>\<^sub>c n2)
      = right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (indexed_sum f low) \<circ>\<^sub>c (n1 +\<^sub>\<nat> n2)"
proof(cases "n1 = zero")
  assume "n1 = zero"
  show ?thesis
  proof(cases "n2 = zero")
    assume "n2 = zero"
    
    have LHS:  "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (indexed_sum f low) \<circ>\<^sub>c n1) +\<^sub>\<nat> (right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(indexed_sum f (successor \<circ>\<^sub>c (low +\<^sub>\<nat> n1))) \<circ>\<^sub>c n2) =
               (f \<circ>\<^sub>c low) +\<^sub>\<nat> (f \<circ>\<^sub>c (successor \<circ>\<^sub>c low))"
      using \<open>n1 = zero\<close> \<open>n2 = zero\<close> add_respects_zero_on_right indexed_sum_zero right_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)

    have RHS: "right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low \<circ>\<^sub>c (n1 +\<^sub>\<nat> n2) = (f \<circ>\<^sub>c low)"
      by (typecheck_cfuncs, simp add: \<open>n1 = zero\<close> \<open>n2 = zero\<close> add_respects_zero_on_right indexed_sum_zero right_cart_proj_cfunc_prod)






end