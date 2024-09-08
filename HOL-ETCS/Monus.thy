theory Monus
  imports Inequality
begin

definition monus1 :: "cfunc" 
  where "monus1 = (THE u. u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and> 
  u \<circ>\<^sub>c zero = (left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> \<and> 
  u \<circ>\<^sub>c successor = predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c u)"

lemma monus1_property: "monus1 : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and> 
  monus1 \<circ>\<^sub>c zero = (left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> \<and> 
  monus1 \<circ>\<^sub>c successor = predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c monus1"
  unfolding monus1_def
  by (rule theI', typecheck_cfuncs, smt (verit, best) natural_number_object_property2)
  
lemma monus1_type[type_rule]: "monus1: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: monus1_property)

lemma monus1_0_eq: "monus1 \<circ>\<^sub>c zero = left_cart_proj \<nat>\<^sub>c \<one>\<^sup>\<sharp>"
  by (simp add: monus1_property)
  
lemma monus1_succ_eq: "monus1 \<circ>\<^sub>c successor = predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c monus1"
  by (simp add: monus1_property)

definition monus2 :: "cfunc" 
  where "monus2 = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f monus1)"

lemma monus2[type_rule]: "monus2: \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding monus2_def
  using flat_type inv_transpose_func_def3 monus1_type by force

lemma monus2_apply:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "monus2 \<circ>\<^sub>c \<langle>m, n\<rangle> = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, monus1 \<circ>\<^sub>c n\<rangle>"
  unfolding monus2_def using assms 
  by (etcs_assocr, typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2)

definition monus :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "\<midarrow>\<^sub>\<nat>" 65)
  where "m \<midarrow>\<^sub>\<nat> n = monus2 \<circ>\<^sub>c \<langle>m, n\<rangle>"

lemma  monus_type[type_rule]:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "m \<midarrow>\<^sub>\<nat> n : X \<rightarrow> \<nat>\<^sub>c"
  unfolding monus_def using assms by typecheck_cfuncs

lemma monus_def2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m \<midarrow>\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, monus1 \<circ>\<^sub>c n\<rangle>"
  unfolding monus_def using assms by (typecheck_cfuncs, simp add: monus2_apply)

lemma monus_zero:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "n \<midarrow>\<^sub>\<nat> zero = n"
proof - 
  have "n \<midarrow>\<^sub>\<nat> zero = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, left_cart_proj \<nat>\<^sub>c \<one>\<^sup>\<sharp>\<rangle>"
    using monus1_0_eq monus_def2 by (typecheck_cfuncs, presburger)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c n, left_cart_proj \<nat>\<^sub>c \<one>\<^sup>\<sharp> \<circ>\<^sub>c id \<one>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f  left_cart_proj \<nat>\<^sub>c \<one>\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n, id \<one>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... =  left_cart_proj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<langle>n,id \<one>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = n"
    using assms id_type left_cart_proj_cfunc_prod by blast
  then show "n \<midarrow>\<^sub>\<nat> zero = n"
    using calculation by auto
qed

lemma NAME_ME_PLEASE:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows  "(monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
      predecessor \<circ>\<^sub>c monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
proof -
  have "(monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
       monus2 \<circ>\<^sub>c (\<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor) "
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... =  monus2 \<circ>\<^sub>c \<langle>(n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... =  monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,  successor\<rangle>"
    by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
  also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f monus1) \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
    unfolding monus2_def by auto
  also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  monus1 \<circ>\<^sub>c successor\<rangle>"
    using monus2_apply monus2_def by (typecheck_cfuncs, auto)
  also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c monus1\<rangle>"
    by (typecheck_cfuncs, simp add: monus1_property)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, monus1\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = (predecessor  \<circ>\<^sub>c  eval_func \<nat>\<^sub>c \<nat>\<^sub>c ) \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, monus1\<rangle>"
    by (typecheck_cfuncs, smt comp_associative2 exp_func_def2 flat_cancels_sharp inv_transpose_func_def3)
  also have "... = predecessor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f monus1) \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2)
  also have "... = predecessor \<circ>\<^sub>c monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    by (typecheck_cfuncs, simp add: monus2_def comp_associative2)
  then show ?thesis using calculation by auto
qed

lemma NAME_ME_PLEASE':
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "n \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c m) =  predecessor \<circ>\<^sub>c (n \<midarrow>\<^sub>\<nat> m)"
proof - 
  have "n \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c m) = (monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c m" 
    by (etcs_assocr, typecheck_cfuncs, smt cart_prod_extract_right monus_def)
  also have "... = predecessor \<circ>\<^sub>c monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m"
    by (typecheck_cfuncs, simp add: NAME_ME_PLEASE comp_associative2)
  also have "... = predecessor \<circ>\<^sub>c (n \<midarrow>\<^sub>\<nat> m)"
    by (typecheck_cfuncs, metis cart_prod_extract_right monus_def)
  then show ?thesis
    using calculation by auto
qed

lemma zero_monus:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "zero \<midarrow>\<^sub>\<nat> n = zero"
proof - 
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c n = \<t>"
  proof(etcs_rule nat_induction)
    show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
      by (typecheck_cfuncs, smt (z3) cart_prod_extract_right cfunc_prod_comp comp_associative2
          eq_pred_iff_eq_conv2 monus_def monus_zero terminal_func_comp zero_betaN_type)
  next
    fix m 
    assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    assume eq_pred_ind_hyp: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m = \<t>"
    have induction_hypothesis: "monus2 \<circ>\<^sub>c \<langle>zero, m\<rangle> = zero"
    proof - 
      have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
        using eq_pred_ind_hyp comp_associative2 by (typecheck_cfuncs, force)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>zero, m\<rangle>, zero\<rangle>"
        by (typecheck_cfuncs, smt (verit, best) cart_prod_extract_right cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      then show ?thesis
        by (typecheck_cfuncs, simp add: calculation eq_pred_iff_eq)
    qed
    have induction_conclusion: "monus2 \<circ>\<^sub>c \<langle>zero, successor \<circ>\<^sub>c m\<rangle> = zero"
      using NAME_ME_PLEASE' induction_hypothesis monus_def predecessor_zero by (typecheck_cfuncs, force)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c m = \<t>"
      by (typecheck_cfuncs,
      smt (z3) cart_prod_extract_right cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv2 
      induction_conclusion terminal_func_comp zero_betaN_type)
  qed
  then show ?thesis
    by (-, typecheck_cfuncs,
        smt (verit, best) cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv2 id_right_unit2 left_param_def2 left_param_on_el monus2_apply monus_def2 terminal_func_comp_elem)
qed

lemma monus_of_succs:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(successor \<circ>\<^sub>c n) \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c m) = n \<midarrow>\<^sub>\<nat> m"
proof - 
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>, monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c m = \<t>"
  proof(etcs_rule nat_induction)
    have "(successor \<circ>\<^sub>c n) \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n \<midarrow>\<^sub>\<nat> zero"
    proof - 
      have "(successor \<circ>\<^sub>c n) \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = predecessor \<circ>\<^sub>c  (successor \<circ>\<^sub>c n  \<midarrow>\<^sub>\<nat> zero)"
        using NAME_ME_PLEASE' monus_zero by (typecheck_cfuncs, presburger)
      also have "... = predecessor \<circ>\<^sub>c  successor \<circ>\<^sub>c n"
        by (simp add: monus_zero n_type)
      also have "... =  n"
        by (etcs_assocl, typecheck_cfuncs, simp add: id_left_unit2 predecessor_successor)
      also have "... = n \<midarrow>\<^sub>\<nat> zero"
        by (simp add: monus_zero n_type)
      then show ?thesis 
        using calculation by auto
    qed
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t>"
      by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv2 
          id_right_unit2 left_param_def2 left_param_on_el monus_def monus_zero terminal_func_comp_elem)
  next
    fix k 
    assume k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
    assume eq_pred_ind_hyp: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c k = \<t>"
    have induction_hypothesis: "monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n, successor \<circ>\<^sub>c k\<rangle> = monus2 \<circ>\<^sub>c \<langle>n, k\<rangle>"
    proof - 
      have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c k"
        using comp_associative2 eq_pred_ind_hyp by (typecheck_cfuncs, force)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c k,monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c k\<rangle>"
        by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n, successor \<circ>\<^sub>c k\<rangle>,monus2 \<circ>\<^sub>c \<langle>n, k\<rangle>\<rangle>"
        by (typecheck_cfuncs, smt (z3) cart_prod_extract_right cfunc_prod_comp  comp_associative2 id_right_unit2 terminal_func_comp_elem)
      then show ?thesis 
        using calculation eq_pred_iff_eq by (typecheck_cfuncs, presburger)
    qed
    have induction_conclusion: "monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n, successor \<circ>\<^sub>c successor \<circ>\<^sub>c k\<rangle> = monus2 \<circ>\<^sub>c \<langle>n, successor \<circ>\<^sub>c k\<rangle>"
      using NAME_ME_PLEASE' induction_hypothesis monus_def by (typecheck_cfuncs, fastforce)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c k = \<t>"
      by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 comp_type eq_pred_iff_eq id_left_unit2 id_right_unit2 induction_conclusion terminal_func_comp_elem)
  qed
  then have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>, monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c m"
    using comp_associative2 by (typecheck_cfuncs, force)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle> \<circ>\<^sub>c m, monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m\<rangle>"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n, successor \<circ>\<^sub>c m\<rangle>, monus2 \<circ>\<^sub>c \<langle>n, m\<rangle>\<rangle>"
    by (typecheck_cfuncs, smt (verit, best) cart_prod_extract_right cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
  then show ?thesis
    by (metis calculation eq_pred_iff_eq m_type monus_def monus_type n_type succ_n_type)
qed

lemma monus_self:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "n \<midarrow>\<^sub>\<nat> n = zero"
proof -
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, id \<nat>\<^sub>c\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c n = \<t>"
  proof(etcs_rule nat_induction)
    show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv2 id_left_unit2 id_right_unit2 monus_def monus_zero terminal_func_comp_elem)
   next
      fix m 
      assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
      assume eq_pred_ind_hyp: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m = \<t>"
      have induction_hypothesis: "monus2 \<circ>\<^sub>c \<langle>m, m\<rangle> = zero"
      proof - 
        have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
          using eq_pred_ind_hyp comp_associative2 by (typecheck_cfuncs, force)
        also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>m, m\<rangle>,zero\<rangle>"
          by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
        then show ?thesis
          by (metis calculation eq_pred_iff_eq_conv2 m_type monus_def monus_type zero_type)
      qed
      then have induction_conclusion: "monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, successor \<circ>\<^sub>c m\<rangle> = zero" 
        using  monus_def monus_of_succs by (typecheck_cfuncs, presburger)
      then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c m = \<t>"
        by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 
            eq_pred_true_extract_right id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  qed
  then have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, id \<nat>\<^sub>c\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c n"
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n, n\<rangle>, zero\<rangle>"
    by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem) 
  then show ?thesis
    by (metis calculation eq_pred_iff_eq monus_def monus_type n_type zero_type)
qed

lemma smaller_monus_bigger:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n_leq_m: "n \<le>\<^sub>\<nat> m"
  shows "n \<midarrow>\<^sub>\<nat> m = zero"
proof - 
  obtain c where c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c" and c_def: "n +\<^sub>\<nat> c = m"
    by (typecheck_cfuncs, metis add_commutes leq_infix_def leq_true_implies_exists n_leq_m)
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c \<rangle>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c c = \<t>"
  proof(etcs_rule nat_induction)
    show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
    proof - 
      have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = 
             eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c zero, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero\<rangle>"
        by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp cfunc_type_def comp_associative)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n, add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero\<rangle>, zero\<rangle>"
        by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n, add2 \<circ>\<^sub>c \<langle>n, zero\<rangle>\<rangle>, zero\<rangle>"
        by (typecheck_cfuncs, metis add_apply1 add_def)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n, n\<rangle>, zero\<rangle>"
        using add_def add_respects_zero_on_right by (typecheck_cfuncs, presburger)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero, zero\<rangle>"
        using monus_def monus_self n_type by force
      also have "... = \<t>"
        using eq_pred_iff_eq by (typecheck_cfuncs, blast)
      then show ?thesis
        using calculation by auto
    qed
  next
    fix k
    assume k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
    assume eq_pred_ind_hyp: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    have induction_hypothesis: "n \<midarrow>\<^sub>\<nat> (n +\<^sub>\<nat> k) = zero"
    proof - 
      have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c k"
        using comp_associative2 eq_pred_ind_hyp by (typecheck_cfuncs, force)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c k, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c k\<rangle>"
        by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n, add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c k\<rangle>, zero\<rangle>"
        by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n, add2 \<circ>\<^sub>c \<langle>n, k\<rangle>\<rangle>, zero\<rangle>"
        by (typecheck_cfuncs, metis cart_prod_extract_right)
      then show ?thesis
        by (typecheck_cfuncs, simp add: add_def calculation eq_pred_iff_eq monus_def)
    qed
    then have induction_conclusion: "n \<midarrow>\<^sub>\<nat> (n +\<^sub>\<nat> (successor \<circ>\<^sub>c k)) = zero"
      by (typecheck_cfuncs, metis NAME_ME_PLEASE' add_respects_succ1 add_type zero_monus)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c k = \<t>"
      by (typecheck_cfuncs, smt (verit, best) add_apply1_left beta_N_succ_nEqs_Id1 cart_prod_extract_left cfunc_prod_comp
          comp_associative2 eq_pred_iff_eq_conv2 id_right_unit2 left_param_def2 left_param_on_el monus_def)
  qed
  then have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c \<rangle>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c"
    by (typecheck_cfuncs, simp add:  comp_associative2)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c c\<rangle>"
    by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>n, add2 \<circ>\<^sub>c \<langle>n, c\<rangle>\<rangle>, zero\<rangle>"
    by (typecheck_cfuncs, smt (z3) cart_prod_extract_right cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)    
  then show ?thesis
    by (typecheck_cfuncs, smt c_def calculation add_def eq_pred_iff_eq monus_def)
qed

lemma bigger_monus_smaller:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(n +\<^sub>\<nat> m) \<midarrow>\<^sub>\<nat> n = m"
proof -
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle>, id \<nat>\<^sub>c\<rangle>, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c n = \<t>"
  proof(etcs_rule nat_induction)
    show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, id\<^sub>c \<nat>\<^sub>c\<rangle>,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
    proof - 
      have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, id\<^sub>c \<nat>\<^sub>c\<rangle>,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero =
             eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero\<rangle>"
        by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp  comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>zero, m\<rangle>, zero\<rangle>, m\<rangle>"
        by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
      also have "... = \<t>"
        by (typecheck_cfuncs, metis add_def add_respects_zero_on_left eq_pred_iff_eq monus_def monus_zero)
      then show ?thesis
        using calculation by fastforce
    qed
  next
    fix k 
    assume k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
    assume eq_pred_ind_hyp: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, id\<^sub>c \<nat>\<^sub>c\<rangle>,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    have induction_hypothesis: "(k +\<^sub>\<nat> m) \<midarrow>\<^sub>\<nat> k = m"
    proof - 
      have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, id\<^sub>c \<nat>\<^sub>c\<rangle>,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c k"
        by (typecheck_cfuncs, simp add: comp_associative2 eq_pred_ind_hyp)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c k, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c k\<rangle>"
        by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>k, m\<rangle>, k\<rangle>, m\<rangle>"
        by (typecheck_cfuncs, smt (verit, best) cart_prod_extract_left cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv id_left_unit2)
      then show ?thesis
        by (metis add_def add_type calculation eq_pred_iff_eq_conv k_type m_type monus_def monus_type true_false_distinct)
    qed
    then have induction_conclusion: "((successor \<circ>\<^sub>c k) +\<^sub>\<nat> m) \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c k) = m"
      using add_respects_succ3 add_type induction_hypothesis monus_of_succs by (typecheck_cfuncs, presburger)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,id\<^sub>c \<nat>\<^sub>c\<rangle>,m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c k = \<t>"
      by (typecheck_cfuncs, smt (verit, ccfv_SIG) add_apply1_left beta_N_succ_nEqs_Id1 cfunc_prod_comp 
          comp_associative2 eq_pred_iff_eq_conv2 id_left_unit2 id_right_unit2 induction_conclusion monus_def)
  qed
  then have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle>, id \<nat>\<^sub>c\<rangle>, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c n"
    by (typecheck_cfuncs, etcs_assocl, force)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n, m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n\<rangle>"
    by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>n, m\<rangle>, n\<rangle>, m\<rangle>"
    by (typecheck_cfuncs, smt (z3) cart_prod_extract_left cfunc_prod_comp 
        comp_associative2 id_left_unit2 id_type one_unique_element)
  then show ?thesis
    using  add_def calculation eq_pred_iff_eq_conv2 monus_def by (typecheck_cfuncs, auto)
qed

lemma RENAME_Part1:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "n +\<^sub>\<nat> (m \<midarrow>\<^sub>\<nat> n) = m +\<^sub>\<nat> (n \<midarrow>\<^sub>\<nat> m)"
proof(cases "n \<le>\<^sub>\<nat> m")
  show "n \<le>\<^sub>\<nat> m \<Longrightarrow> n +\<^sub>\<nat> (m \<midarrow>\<^sub>\<nat> n) = m +\<^sub>\<nat> (n \<midarrow>\<^sub>\<nat> m)"
    by (typecheck_cfuncs, metis add_commutes bigger_monus_smaller leq_infix_def leq_true_implies_exists monus_zero smaller_monus_bigger)
  show "\<not> n \<le>\<^sub>\<nat> m \<Longrightarrow> n +\<^sub>\<nat> (m \<midarrow>\<^sub>\<nat> n) = m +\<^sub>\<nat> (n \<midarrow>\<^sub>\<nat> m)"
    by (typecheck_cfuncs, metis lqe_connexity add_commutes bigger_monus_smaller leq_infix_def leq_true_implies_exists smaller_monus_bigger)
qed

lemma monus_monotonic:
  assumes m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and u_type[type_rule]: "u \<in>\<^sub>c \<nat>\<^sub>c" and v_type[type_rule]: "v \<in>\<^sub>c \<nat>\<^sub>c"
  assumes m_leq_n: "m \<le>\<^sub>\<nat> n" 
  assumes u_leq_v: "u \<le>\<^sub>\<nat> v"
  shows "(m \<midarrow>\<^sub>\<nat> v) \<le>\<^sub>\<nat> (n \<midarrow>\<^sub>\<nat> u)" 
proof(cases "m \<le>\<^sub>\<nat> v")
  show "m \<le>\<^sub>\<nat> v \<Longrightarrow> m \<midarrow>\<^sub>\<nat> v \<le>\<^sub>\<nat> n \<midarrow>\<^sub>\<nat> u"
    by (typecheck_cfuncs, metis leq_infix_def smaller_monus_bigger zero_is_smallest)
next
  show "\<not> m \<le>\<^sub>\<nat> v \<Longrightarrow> m \<midarrow>\<^sub>\<nat> v \<le>\<^sub>\<nat> n \<midarrow>\<^sub>\<nat> u"
    by (typecheck_cfuncs, smt (z3) RENAME_Part1 add_associates add_commutes add_type 
        bigger_monus_smaller fewer_is_less leq_infix_def leq_true_implies_exists 
        lqe_connexity m_leq_n monus_def u_leq_v)
qed

lemma RENAME_Part2:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(n \<midarrow>\<^sub>\<nat> m) \<midarrow>\<^sub>\<nat> k = n \<midarrow>\<^sub>\<nat> (m +\<^sub>\<nat> k)"
proof(cases "n \<le>\<^sub>\<nat> m +\<^sub>\<nat> k")
  assume Case1: "n \<le>\<^sub>\<nat> m +\<^sub>\<nat> k"
  show ?thesis
  proof(cases "n \<le>\<^sub>\<nat> m")
    show "n \<le>\<^sub>\<nat> m \<Longrightarrow> n \<midarrow>\<^sub>\<nat> m \<midarrow>\<^sub>\<nat> k = n \<midarrow>\<^sub>\<nat> (m +\<^sub>\<nat> k)"
      using Case1 smaller_monus_bigger zero_monus by (typecheck_cfuncs, presburger)
  next
    show "\<not> n \<le>\<^sub>\<nat> m \<Longrightarrow> n \<midarrow>\<^sub>\<nat> m \<midarrow>\<^sub>\<nat> k = n \<midarrow>\<^sub>\<nat> (m +\<^sub>\<nat> k)"
      by (typecheck_cfuncs, metis Case1 bigger_monus_smaller leq_infix_def
          lqe_connexity monus_monotonic smaller_monus_bigger)
  qed
next
  assume "\<not> n \<le>\<^sub>\<nat> m +\<^sub>\<nat> k"
  then have Case2: "m +\<^sub>\<nat> k \<le>\<^sub>\<nat> n"
    using leq_infix_def lqe_connexity by (typecheck_cfuncs, auto)
  show "n \<midarrow>\<^sub>\<nat> m \<midarrow>\<^sub>\<nat> k = n \<midarrow>\<^sub>\<nat> (m +\<^sub>\<nat> k)"
    by (typecheck_cfuncs, smt (verit, del_insts) Case2 RENAME_Part1 add_associates 
        add_respects_zero_on_right add_type bigger_monus_smaller smaller_monus_bigger)
qed

end