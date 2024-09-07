theory Monus
  imports Add Inequality
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
  shows  "(monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
      predecessor \<circ>\<^sub>c monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
proof -
  have "(monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
       monus2 \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor) "
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... =  monus2 \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... =  monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,  successor\<rangle>"
    by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
  also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f monus1) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
    unfolding monus2_def
    by auto
  also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  monus1 \<circ>\<^sub>c successor\<rangle>"
    using monus2_apply monus2_def by (typecheck_cfuncs, auto)
  also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c monus1\<rangle>"
    by (typecheck_cfuncs, simp add: monus1_property)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, monus1\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = (predecessor  \<circ>\<^sub>c  eval_func \<nat>\<^sub>c \<nat>\<^sub>c ) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, monus1\<rangle>"
    by (typecheck_cfuncs, smt comp_associative2 exp_func_def2 flat_cancels_sharp inv_transpose_func_def3)
  also have "... = predecessor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f monus1) \<circ>\<^sub>c \<langle>zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2)
  also have "... = predecessor \<circ>\<^sub>c monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    by (typecheck_cfuncs, simp add: monus2_def comp_associative2)
  then show ?thesis using calculation by auto
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
    proof - 
      have "monus2 \<circ>\<^sub>c \<langle>zero, successor \<circ>\<^sub>c m\<rangle> = monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c m"
        using cart_prod_extract_right by (typecheck_cfuncs, auto)
      also have "... = predecessor \<circ>\<^sub>c monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m"
        using NAME_ME_PLEASE cfunc_type_def comp_associative comp_type by (typecheck_cfuncs, auto)
      also have "... = predecessor \<circ>\<^sub>c monus2 \<circ>\<^sub>c \<langle>zero, m\<rangle>"
        by (typecheck_cfuncs, metis cart_prod_extract_right)
      also have "... = predecessor \<circ>\<^sub>c zero"
        by (simp add: induction_hypothesis)
      also have "... = zero"
        by (simp add: predecessor_zero)
      then show ?thesis
        using calculation by auto
    qed
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>monus2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c m = \<t>"
      by (typecheck_cfuncs,
      smt (z3) cart_prod_extract_right cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv2 
      induction_conclusion terminal_func_comp zero_betaN_type)
  qed
  then show ?thesis
    by (-, typecheck_cfuncs,
        smt (verit, best) cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv2 id_right_unit2 left_param_def2 left_param_on_el monus2_apply monus_def2 terminal_func_comp_elem)
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
      have induction_conclusion: "monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, successor \<circ>\<^sub>c m\<rangle> = zero" 
      proof - 
        have "monus2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, successor \<circ>\<^sub>c m\<rangle> = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, monus1 \<circ>\<^sub>c successor \<circ>\<^sub>c m\<rangle>"  
          using monus2_apply by (typecheck_cfuncs, blast)
        also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c monus1 \<circ>\<^sub>c m\<rangle>"
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative monus1_property)
        also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, (predecessor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c monus1 \<circ>\<^sub>c m\<rangle>"
          using exp_func_def2 by (typecheck_cfuncs, force)
        also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f (predecessor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> )) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, monus1 \<circ>\<^sub>c m\<rangle>"
          by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = predecessor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, monus1 \<circ>\<^sub>c m\<rangle>"
          by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
        oops

        
(*
(*Restate as "smallest such solution"*)
lemma monus_def3: 
  assumes m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m \<le>\<^sub>\<nat> n +\<^sub>\<nat> (n \<midarrow>\<^sub>\<nat> m)"
  apply typecheck_cfuncs
*)


(*
lemma monus_succ_is_pred_monus:
  assumes m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = predecessor \<circ>\<^sub>c (m \<midarrow>\<^sub>\<nat> n)"
proof(cases "m = zero")
  show "m = zero \<Longrightarrow> m \<midarrow>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = predecessor \<circ>\<^sub>c m \<midarrow>\<^sub>\<nat> n"
    apply typecheck_cfuncs
*)



end