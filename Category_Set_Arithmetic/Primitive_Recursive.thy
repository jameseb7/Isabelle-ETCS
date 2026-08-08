theory Primitive_Recursive
  imports Mult
  keywords "iteration_qf" :: thy_decl
    and "iteration_script" :: thy_decl
begin

theorem nat_eq_induction:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> X"  and g_type[type_rule]: "g : \<nat>\<^sub>c \<rightarrow> X"
  assumes base_case: "f \<circ>\<^sub>c zero = g \<circ>\<^sub>c zero"
  assumes induction_case: "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> f \<circ>\<^sub>c n = g \<circ>\<^sub>c n \<Longrightarrow> f \<circ>\<^sub>c successor \<circ>\<^sub>c n = g \<circ>\<^sub>c successor \<circ>\<^sub>c n"
  shows "f \<circ>\<^sub>c n = g \<circ>\<^sub>c n"
proof -
  have "(eq_pred X \<circ>\<^sub>c \<langle>f, g\<rangle>) \<circ>\<^sub>c n = \<t>"
  proof (etcs_rule nat_induction)
    show "(eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c zero = \<t>"
      by (etcs_assocr, typecheck_cfuncs, smt base_case cfunc_prod_comp comp_type eq_pred_iff_eq)
  next
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume "(eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c n = \<t>"
    then have "f \<circ>\<^sub>c n = g \<circ>\<^sub>c n"
      by (typecheck_cfuncs_prems, smt cfunc_prod_comp comp_associative2 comp_type eq_pred_iff_eq)
    then have "f \<circ>\<^sub>c successor \<circ>\<^sub>c n = g \<circ>\<^sub>c successor \<circ>\<^sub>c n"
      by (simp add: induction_case n_type)
    then show "(eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
      by (typecheck_cfuncs_prems, typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 eq_pred_iff_eq)
  qed
  then show "f \<circ>\<^sub>c n = g \<circ>\<^sub>c n"
    by (typecheck_cfuncs_prems, smt cfunc_prod_comp comp_associative2 comp_type eq_pred_iff_eq)
qed
     
theorem primitive_recursion:
  assumes f0_type[type_rule]: "f0 : A \<rightarrow> B"
  assumes f_type[type_rule]: "f : A \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c B) \<rightarrow> B"
  shows "\<exists>!u. u : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B \<and> (\<forall> a n. (a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    u \<circ>\<^sub>c \<langle>a, zero\<rangle> = f0 \<circ>\<^sub>c a \<and>
    u \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a, \<langle>n, u \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>\<rangle>)"
proof -

  obtain y where y_type[type_rule]: "y : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)"
    and y_zero: "y \<circ>\<^sub>c zero = \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle>\<^sup>\<sharp>"
    and y_succ: "y \<circ>\<^sub>c successor = (\<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c y"
    by (typecheck_cfuncs, smt natural_number_object_property2)

  have yb_zero: "y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c (id A \<times>\<^sub>f zero) = \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle>"
    by (typecheck_cfuncs, metis flat_cancels_sharp inv_transpose_of_composition y_zero)

  have yb_succ: "y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c (id A \<times>\<^sub>f successor) = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y)"
    by (etcs_assocl, typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_of_composition sharp_comp y_succ)    

  have yb_preserves_nat: "\<And>a. a \<in>\<^sub>c A \<Longrightarrow> left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> = id \<nat>\<^sub>c"
  proof (etcs_rule natural_number_object_func_unique[where f="successor"])
    fix a
    assume a_type[type_rule]: "a \<in>\<^sub>c A"

    show "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    proof -
      have "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a, zero\<rangle>"
        by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c (id A \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>,  f0 \<circ>\<^sub>c left_cart_proj A \<one> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>\<rangle>"
        by (etcs_assocl, typecheck_cfuncs, smt (verit, best) comp_associative2 left_cart_proj_cfunc_prod yb_zero)
      also have "... = zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
        using left_cart_proj_cfunc_prod by (typecheck_cfuncs, simp)
      also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 one_unique_element)
      finally show ?thesis.
    qed
     

    show "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
         successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof -
      have "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c  successor =
                 left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
        by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c (id A \<times>\<^sub>f successor)) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        using cfunc_type_def comp_associative comp_type yb_succ by (typecheck_cfuncs, auto)
      also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        using comp_associative2 left_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
      also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c  eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        by (typecheck_cfuncs, smt (verit, ccfv_threshold) comp_associative2 right_cart_proj_cfunc_prod)
      also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"          
        by (typecheck_cfuncs, smt (verit, best) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2 inv_transpose_func_def3)
      finally show ?thesis.
    qed

    show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
      by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  qed

  show ?thesis
  proof (intro ex1I[where a="right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)"], safe)
    show "right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
      by typecheck_cfuncs
    show g1: "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a"
    proof -
      fix a n
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      show "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a"
      proof -
        have "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,zero\<rangle> = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c (id A \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
        also have "... = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c (id A \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
          by (etcs_assocr, simp)
        also have "... = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
          by (subst yb_zero, simp)
        also have "... = f0 \<circ>\<^sub>c a"
          by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
        finally show ?thesis.
      qed
    qed
    show g2: "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
    proof -
      fix a n
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      show "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
      proof -
        have "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c (id A \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
        also have "... = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c (id A \<times>\<^sub>f successor)) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (etcs_assocr, simp)
        also have "... = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle>) \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (subst yb_succ, etcs_assocl, simp)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (etcs_subst right_cart_proj_cfunc_prod, simp)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)) \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>, eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"
          by (etcs_subst cfunc_prod_comp, simp)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)) \<circ>\<^sub>c \<langle>a, y \<circ>\<^sub>c n\<rangle>, y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 inv_transpose_func_def3)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>(A)) \<circ>\<^sub>c \<langle>a, y \<circ>\<^sub>c n\<rangle>, \<langle>left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a,n\<rangle>, right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, metis cfunc_prod_unique)
        also have "... = f \<circ>\<^sub>c \<langle>a, \<langle>left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a,n\<rangle>, right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (etcs_subst left_cart_proj_cfunc_prod, simp)
        also have "... = f \<circ>\<^sub>c \<langle>a, \<langle>(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n, right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
        also have "... = f \<circ>\<^sub>c \<langle>a,\<langle>n,(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt id_left_unit2 yb_preserves_nat comp_associative2)
        finally show ?thesis.
      qed
    qed
    fix u
    assume u_type[type_rule]: "u : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
    assume u_property: "\<forall>a n. a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> u \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a \<and> u \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,u \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"

    show "u = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)"
    proof(rule one_separator[where X = "A \<times>\<^sub>c \<nat>\<^sub>c", where Y = B])
      show "u : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs
      show "right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>) : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c A \<times>\<^sub>c \<nat>\<^sub>c"
      obtain a m where a_type[type_rule]: "a \<in>\<^sub>c A" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
        and x_def: "x = \<langle>a, m\<rangle>"
        using cart_prod_decomp x_type by blast

      have "u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs

      have "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c \<rangle>: \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs

      have "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m"
      proof(etcs_rule nat_eq_induction)
        show "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
          by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2 g1 u_property)
      next
        fix n
        assume  n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
        assume "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
        then have induction_hypothesis: "u \<circ>\<^sub>c \<langle>a ,n\<rangle> = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a, n\<rangle>"
          by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2)
        have "u \<circ>\<^sub>c \<langle>a ,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a, \<langle>n, u \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          using u_property by (typecheck_cfuncs, blast)
        also have "... = f \<circ>\<^sub>c \<langle>a, \<langle>n, (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>\<rangle>"
          by (simp add: induction_hypothesis)
        also have "... = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a ,successor \<circ>\<^sub>c n\<rangle>"
          by (simp add: a_type g2 n_type)
        finally show "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
          by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
      qed
      then show "u \<circ>\<^sub>c x = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>\<^sup>(\<^sup>(\<nat>\<^sub>c \<times>\<^sub>c B)\<^sup>,\<^sup>A\<^sup>)) \<circ>\<^sub>c x"
        by (typecheck_cfuncs_prems, smt  cart_prod_extract_right comp_associative2 x_def)
    qed
  qed
qed

theorem minimisation:
  assumes f_type[type_rule]: "f : (\<nat>\<^sub>c \<times>\<^sub>c A) \<rightarrow> \<nat>\<^sub>c"
  shows
    "\<exists>! \<mu>. \<mu> : A \<rightarrow> (\<nat>\<^sub>c \<Coprod> \<one>) \<and>
      (\<forall>a n. (a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
        (\<mu> \<circ>\<^sub>c a = (left_coproj \<nat>\<^sub>c \<one>) \<circ>\<^sub>c n \<longleftrightarrow>
          (f \<circ>\<^sub>c \<langle>n, a\<rangle> = zero \<and>
           (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> (m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m, a\<rangle> \<noteq> zero))))) \<and>
      (\<forall>a. a \<in>\<^sub>c A \<longrightarrow>
        (\<mu> \<circ>\<^sub>c a = (right_coproj \<nat>\<^sub>c \<one>) \<circ>\<^sub>c id\<^sub>c \<one> \<longleftrightarrow>
          (\<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n, a\<rangle> \<noteq> zero)))"
proof -

  define zero_NA :: cfunc where
    "zero_NA = zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c A\<^esub>"
  have zero_NA_type[type_rule]: "zero_NA : (\<nat>\<^sub>c \<times>\<^sub>c A) \<rightarrow> \<nat>\<^sub>c"
    unfolding zero_NA_def by typecheck_cfuncs

  (*  Zf(n,a) :\<equiv> f(n,a)=0 --- *)
  define Zf :: cfunc where
    "Zf = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f, zero_NA\<rangle>"
  have Zf_type[type_rule]: "Zf : (\<nat>\<^sub>c \<times>\<^sub>c A) \<rightarrow> \<Omega>"
    unfolding Zf_def by typecheck_cfuncs

  (*  Pf(n,a) :\<equiv> f(n,a)\<noteq>0 --- *)
  define Pf :: cfunc where
    "Pf = NOT \<circ>\<^sub>c Zf"
  have Pf_type[type_rule]: "Pf : (\<nat>\<^sub>c \<times>\<^sub>c A) \<rightarrow> \<Omega>"
    unfolding Pf_def by typecheck_cfuncs

  (*  P(m,(n,a)) :\<equiv> (m<n \<Rightarrow> Pf(m,a)) --- *)
  obtain P  where
    P_def: "P =
      IMPLIES \<circ>\<^sub>c
        \<langle> lt \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
              left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle>,
          Pf \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
              right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<rangle>"  
    by blast
  then have P_type[type_rule]: "P : (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A)) \<rightarrow> \<Omega>"
    unfolding P_def  
    by (typecheck_cfuncs,
        smt (verit, ccfv_SIG) NOT_type comp_type leq_type lt_def swap_def swap_type)

  (*  \<chi>_f(n,a) :\<equiv> Zf(n,a) \<and> \<forall>m. P(m,n,a) --- *)
  obtain chi_f where
    chi_f_def: "chi_f = AND \<circ>\<^sub>c \<langle> Zf, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp>\<rangle>"
    by blast
  then have chi_f_type[type_rule]: "chi_f : (\<nat>\<^sub>c \<times>\<^sub>c A) \<rightarrow> \<Omega>"
    unfolding chi_f_def
    by typecheck_cfuncs

  obtain exists_f where
    exists_f_def: "exists_f = (EXISTS \<nat>\<^sub>c) \<circ>\<^sub>c (chi_f\<^sup>\<sharp>)"
    by blast
  then have exists_f_type[type_rule]: "exists_f : A \<rightarrow> \<Omega>"
    unfolding exists_f_def
    by typecheck_cfuncs

  have chi_f_sharp_type[type_rule]: "chi_f\<^sup>\<sharp> : A \<rightarrow> \<Omega>\<^sup>(\<nat>\<^sub>c)"
    by (simp add: chi_f_type transpose_func_type)

  have curry_id:
  "\<And>n a. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
     P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n,a\<rangle> =
       ((P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c, (\<langle>n,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
  by (typecheck_cfuncs,
      smt (verit, best) cfunc_cross_prod_right_terminal_decomp cfunc_prod_type 
        comp_associative2 comp_type sharp_comp)

  have P_pair_unfold:
  "\<And>m n a. m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> a \<in>\<^sub>c A \<Longrightarrow>
     P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> =
       IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>m,n\<rangle>, Pf \<circ>\<^sub>c \<langle>m,a\<rangle> \<rangle>"
  proof -
    fix m n a
    assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
  
    have "P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> =
          (IMPLIES \<circ>\<^sub>c
            \<langle> lt \<circ>\<^sub>c
                \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                  left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle>,
              Pf \<circ>\<^sub>c
                \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                  right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<rangle>) \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle>"
      unfolding P_def
      by typecheck_cfuncs
    also have "... =
          IMPLIES \<circ>\<^sub>c
            \<langle> lt \<circ>\<^sub>c
                \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                  left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle>,
              Pf \<circ>\<^sub>c
                \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                  right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> \<rangle>"
      by (typecheck_cfuncs,
          smt (verit) NOT_type cfunc_prod_comp cfunc_type_def comp_associative comp_type leq_type lt_def swap_def swap_type)
    also have "... =
          IMPLIES \<circ>\<^sub>c
            \<langle> lt \<circ>\<^sub>c
                \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle>,
                  left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle>\<rangle>,
              Pf \<circ>\<^sub>c
                \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle>,
                  right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> \<rangle> \<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    also have "... =
          IMPLIES \<circ>\<^sub>c
            \<langle> lt \<circ>\<^sub>c \<langle> m, left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c \<langle>n,a\<rangle> \<rangle>,
              Pf \<circ>\<^sub>c \<langle> m, right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c \<langle>n,a\<rangle> \<rangle> \<rangle>"
      by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
    also have "... =
          IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>m,n\<rangle>, Pf \<circ>\<^sub>c \<langle>m,a\<rangle> \<rangle>"
      by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
    finally show
      "P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> =
        IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>m,n\<rangle>, Pf \<circ>\<^sub>c \<langle>m,a\<rangle> \<rangle>".
  qed

  have chi_f_semantics:
  "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
     chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>
       \<longleftrightarrow> (Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t> \<and>
           (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>))"
  proof -
    fix a n
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  
    let ?p = "P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c, (\<langle>n,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<rangle>"
    have p_type[type_rule]: "?p : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
  
    have curry_id:
      "P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n,a\<rangle> = (?p \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
      by (simp add: a_type curry_id n_type)
   
    have P_pair_unfold:
      "\<And>m. m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> = IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>m,n\<rangle>, Pf \<circ>\<^sub>c \<langle>m,a\<rangle> \<rangle>"
      using P_pair_unfold a_type n_type by blast
    
  
    show
      "chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>
         \<longleftrightarrow> (Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t> \<and>
             (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>))"
    proof
      assume chi: "chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
  
      have chi_unfold:
        "(AND \<circ>\<^sub>c \<langle>Zf, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        using chi chi_f_def by simp
  
      then have and_pair:
        "AND \<circ>\<^sub>c
           \<langle> Zf \<circ>\<^sub>c \<langle>n,a\<rangle>,
             ((FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,a\<rangle> \<rangle> = \<t>"
        by (typecheck_cfuncs, smt (verit, ccfv_SIG)  cfunc_prod_comp cfunc_prod_type comp_associative2)


      have Zf_na: "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t> \<and> (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        using and_pair
        by (typecheck_cfuncs, simp add: AND_true_imp_both_true and_pair comp_associative2)
  
      have forall_imp:
        "\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>"
      proof (intro allI impI)
        fix m
        assume mN[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
        assume mn_lt: "m <\<^sub>\<nat> n"
  
        have For':
          "(FORALL \<nat>\<^sub>c) \<circ>\<^sub>c (?p \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> = \<t>"
          using Zf_na curry_id by argo


        have p_m: "?p \<circ>\<^sub>c m = \<t>"
          using FORALL_true_implies_all_true[OF p_type For'] mN by blast
  
        have P_m: "P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> = \<t>"
          using p_m
          by (typecheck_cfuncs, metis right_param_def2 right_param_on_el)
  
        have impl_true:
          "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>m,n\<rangle>, Pf \<circ>\<^sub>c \<langle>m,a\<rangle> \<rangle> = \<t>"
          using P_m P_pair_unfold[OF mN] by simp
  
        have lt_true: "lt \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
          using mn_lt unfolding lt_infix_def by simp
  
        have Pf_cases: "Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t> \<or> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<f>"
          using true_false_only_truth_values by (typecheck_cfuncs, blast)
  
        show "Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>"
        proof (rule disjE[OF Pf_cases])
          assume "Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>"
          then show ?thesis.
        next
          assume Pf_false: "Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<f>"
          have "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>m,n\<rangle>, Pf \<circ>\<^sub>c \<langle>m,a\<rangle> \<rangle> = \<f>"
            using lt_true Pf_false IMPLIES_true_false_is_false by simp
          with impl_true show ?thesis
            using true_false_distinct by auto
        qed
      qed
  
      show "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t> \<and> (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>)"
        using Zf_na forall_imp by blast  
    next
      assume rhs:
        "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t> \<and> (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>)"
  
      have Zf_na: "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        and H: "\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>"
        using rhs by auto
      have all_p_true: "\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> ?p \<circ>\<^sub>c m = \<t>"
      proof (intro allI impI)
        fix m
        assume mN[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  
        have p_m_eq: "?p \<circ>\<^sub>c m = P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle>"
          by (typecheck_cfuncs, metis right_param_def2 right_param_on_el)
  
        have lt_cases: "lt \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t> \<or> lt \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>"
          by (typecheck_cfuncs, metis NOT_type comp_type leq_type lt_def 
              swap_def swap_type true_false_only_truth_values)
  
        show "?p \<circ>\<^sub>c m = \<t>"
        proof (cases "m <\<^sub>\<nat> n")
          case True
          then have lt_true: "lt \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
            unfolding lt_infix_def by simp
          have Pf_true: "Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>"
            using H mN True by blast
          have "P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> = \<t>"
            using lt_true Pf_true P_pair_unfold[OF mN] IMPLIES_true_true_is_true by simp
          thus ?thesis using p_m_eq by simp
        next
          case False
          then have lt_not_true: "lt \<circ>\<^sub>c \<langle>m,n\<rangle> \<noteq> \<t>"
            unfolding lt_infix_def by simp
  
          from lt_cases show ?thesis
          proof
            assume lt_true: "lt \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
            with lt_not_true show ?thesis by contradiction
          next
            assume lt_false: "lt \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>"
            have "P \<circ>\<^sub>c \<langle>m, \<langle>n,a\<rangle>\<rangle> = \<t>"
              by (typecheck_cfuncs, metis IMPLIES_false_is_true_false P_pair_unfold Pf_type
                  cfunc_prod_type comp_type lt_false true_false_only_truth_values)
            thus ?thesis using p_m_eq by simp
          qed
        qed
      qed
  
      then have ALL_p:
        "(FORALL \<nat>\<^sub>c) \<circ>\<^sub>c (?p \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> = \<t>"
        using all_true_implies_FORALL_true p_type by blast

      then have For_na: "(FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        using curry_id by simp
  
      show "chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        unfolding chi_f_def
        using Zf_na For_na
        by (typecheck_cfuncs, smt AND_true_true_is_true For_na Zf_na cfunc_prod_comp comp_associative2)
    qed
  qed

  have exists_f_semantics:
  "\<And>a. a \<in>\<^sub>c A \<Longrightarrow>
     exists_f \<circ>\<^sub>c a = \<t> \<longleftrightarrow> (\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> chi_f \<circ>\<^sub>c \<langle>n, a\<rangle> = \<t>)"
  proof safe
    fix a
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    assume LHS: "exists_f \<circ>\<^sub>c a = \<t>"
    then have exists: "(EXISTS \<nat>\<^sub>c) \<circ>\<^sub>c  chi_f\<^sup>\<sharp> \<circ>\<^sub>c a = \<t>"
      using comp_associative2 exists_f_def by (typecheck_cfuncs, auto)
    have "(chi_f\<^sup>\<sharp> \<circ>\<^sub>c a) = (chi_f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
      by (metis a_type cfunc_cross_prod_right_terminal_decomp chi_f_type id_type sharp_comp)    
    then have "(EXISTS \<nat>\<^sub>c) \<circ>\<^sub>c  (chi_f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> = \<t>"
      using exists by argo
    then have "\<exists> n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> (chi_f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c n = \<t>"
      by (typecheck_cfuncs,
          smt (verit, best) EXISTS_true_implies_exists_true comp_associative2 left_cart_proj_type)
    then show "\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
      using right_param_def2 right_param_on_el by (typecheck_cfuncs, auto)
  next
    fix a n
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume RHS: "chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"

    let ?p = "chi_f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    have p_type[type_rule]: "?p : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs

    have p_at_n: "?p \<circ>\<^sub>c n = \<t>"
      using RHS
      by (typecheck_cfuncs, metis right_param_def2 right_param_on_el)

    have ex_p_true: "\<exists>x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> ?p \<circ>\<^sub>c x = \<t>"
      using n_type p_at_n by blast

    have EXISTS_p_true:
      "(EXISTS \<nat>\<^sub>c) \<circ>\<^sub>c (?p \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> = \<t>"
      using exists_true_implies_EXISTS_true[OF p_type ex_p_true].

    have chi_sharp_a:
      "chi_f\<^sup>\<sharp> \<circ>\<^sub>c a = (?p \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
      by (typecheck_cfuncs, smt (verit, ccfv_SIG)
          cfunc_cross_prod_right_terminal_decomp comp_associative2 sharp_comp)
   
    then have EXISTS_chi_true:
      "(EXISTS \<nat>\<^sub>c) \<circ>\<^sub>c (chi_f\<^sup>\<sharp> \<circ>\<^sub>c a) = \<t>"
      using EXISTS_p_true by simp

    show "exists_f \<circ>\<^sub>c a = \<t>"
      unfolding exists_f_def
      using EXISTS_chi_true
      by (typecheck_cfuncs, simp add: comp_associative2)
  qed
 
  have chi_f_functional:
    "\<And>a n1 n2. a \<in>\<^sub>c A \<Longrightarrow> n1 \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> n2 \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
      chi_f \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t> \<Longrightarrow> chi_f \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t> \<Longrightarrow> n1 = n2"
  proof -
    fix a n1 n2
    assume aA[type_rule]: "a \<in>\<^sub>c A"
     assume n1N[type_rule]: "n1 \<in>\<^sub>c \<nat>\<^sub>c"
     assume n2N[type_rule]: "n2 \<in>\<^sub>c \<nat>\<^sub>c"
     assume chi1: "chi_f \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t>"
     assume chi2: "chi_f \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t>"
     
     (* --- unpack chi_f at (n1,a)  --- *)
     have f1: "Zf \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t> \<and> (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t>"
     proof -
       have "(AND \<circ>\<^sub>c \<langle>Zf, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t>"
         using chi1 chi_f_def by auto
       then have "AND \<circ>\<^sub>c \<langle>Zf \<circ>\<^sub>c \<langle>n1,a\<rangle>, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n1,a\<rangle>\<rangle>  = \<t>"
         by (typecheck_cfuncs, smt (z3) cfunc_prod_comp cfunc_prod_type comp_associative2 comp_type)
       then show ?thesis
         by (typecheck_cfuncs, meson AND_true_imp_both_true)
     qed
  
     (* --- unpack chi_f at (n2,a)  --- *)
     have f2: "Zf \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t> \<and> (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t>"
     proof -
       have "(AND \<circ>\<^sub>c \<langle>Zf, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t>"
         using chi2 chi_f_def by auto
       then have "AND \<circ>\<^sub>c \<langle>Zf \<circ>\<^sub>c \<langle>n2,a\<rangle>, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n2,a\<rangle>\<rangle>  = \<t>"
         by (etcs_assocl, typecheck_cfuncs, smt (verit, ccfv_SIG)  cfunc_prod_comp cfunc_prod_type
             comp_associative2)
       then show ?thesis
         by (typecheck_cfuncs, meson AND_true_imp_both_true)
     qed
  
     have "(leq \<circ>\<^sub>c \<langle>n1, n2\<rangle> = \<t>) \<or> (leq \<circ>\<^sub>c \<langle>n2, n1\<rangle> = \<t>)"
       by (simp add: lqe_connexity n1N n2N)
      (* --- trichotomy on n1,n2 --- *)
     then have tri: "n1 = n2 \<or> n1 <\<^sub>\<nat> n2 \<or> n2 <\<^sub>\<nat> n1"
       by (simp add: lt_trichotomy n1N n2N)
     show "n1 = n2"
     proof (rule disjE[OF tri])
       assume "n1 = n2"
       then show "n1 = n2".
     next
       assume dichotomy: "n1 <\<^sub>\<nat> n2 \<or> n2 <\<^sub>\<nat> n1"
       show "n1 = n2"
       proof(cases "n1 <\<^sub>\<nat> n2")
          assume lt12: "n1 <\<^sub>\<nat> n2"
          (* From For2 we will extract P(n1,(n2,a)) = \<t>, i.e. (n1<n2 \<Rightarrow> Pf(n1,a)) *)
          define p2 :: cfunc where
            "p2 = P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c, (\<langle>n2,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<rangle>"
          have p2_type[type_rule]: "p2 : \<nat>\<^sub>c \<rightarrow> \<Omega>"
            unfolding p2_def by typecheck_cfuncs
     
          have curry_id:
            "P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n2,a\<rangle> = (p2 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
            using aA curry_id n2N p2_def by blast       
          show ?thesis
            by (typecheck_cfuncs, smt (verit, best) NOT_true_is_false NOT_type Pf_def Zf_type aA
               cfunc_prod_type chi1 chi2 chi_f_semantics comp_associative2 lt12 true_false_distinct)
      next
        assume "\<not> n1 <\<^sub>\<nat> n2"
        then have lt21: "n2 <\<^sub>\<nat> n1"
          using dichotomy by blast
  
        (* symmetric to the previous case: swap (n1,n2) and use For1 instead of For2 *)
        define p1 :: cfunc where
          "p1 = P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c, (\<langle>n1,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<rangle>"
        have p1_type[type_rule]: "p1 : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          unfolding p1_def by typecheck_cfuncs
  
        have curry_id':
          "P\<^sup>\<sharp> \<circ>\<^sub>c \<langle>n1,a\<rangle> = (p1 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
          by (simp add: aA curry_id n1N p1_def)
       
        have For1': "(FORALL \<nat>\<^sub>c) \<circ>\<^sub>c (p1 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> = \<t>"
            using curry_id' f1 by presburger
   
        have P_at_n2: "p1 \<circ>\<^sub>c n2 = \<t>"
          using FORALL_true_implies_all_true For1' n2N p1_type by blast
  
        have P_pair': "P \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle> = \<t>"
          using P_at_n2 P_type aA cfunc_prod_type n1N n2N p1_def
                right_param_def2 right_param_on_el by auto
        have lt_comp': "lt \<circ>\<^sub>c \<langle>n2,n1\<rangle> = \<t>"
          using lt21 unfolding lt_infix_def by simp
   
        have Pf2: "Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<f>"
        proof -
          have "Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> = (NOT \<circ>\<^sub>c Zf) \<circ>\<^sub>c \<langle>n2,a\<rangle>"
            by (simp add: Pf_def)    
          also have "... = NOT \<circ>\<^sub>c (Zf \<circ>\<^sub>c \<langle>n2,a\<rangle>)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = NOT \<circ>\<^sub>c \<t>"
            using f2 by auto              
          also have "... = \<f>"
            using NOT_true_is_false by blast
          finally show ?thesis.
        qed
  
                  (* Unfold P at \<langle>n2,\<langle>n1,a\<rangle>\<rangle> to expose the IMPLIES structure *)
        have P_pair_unfold:
          "P \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle>
           = IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>n2,n1\<rangle>, Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle>"
          by (simp add: P_pair_unfold aA n1N n2N)
       
  
        have IMPL_t:
          "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>n2,n1\<rangle>, Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle> = \<t>"
          using P_pair' P_pair_unfold by simp
  
        have IMPL_f:
          "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>n2,n1\<rangle>, Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle> = \<f>"
        proof -
          have "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>n2,n1\<rangle>, Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle> = IMPLIES \<circ>\<^sub>c \<langle>\<t>, \<f>\<rangle>"
            using lt_comp' Pf2 by simp
          also have "... = \<f>"
            using IMPLIES_true_false_is_false by simp
          finally show ?thesis.
        qed
  
        have False
          using IMPL_f IMPL_t true_false_distinct by argo
  
        thus "n1 = n2"
          by blast        
      qed
    qed
  qed

  obtain M m where
    m_equalizer: "equalizer M m chi_f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c A\<^esub>)"
    using equalizer_exists by (typecheck_cfuncs, blast)
  
  have m_type[type_rule]: "m : M \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c A"
    using cfunc_type_def chi_f_type equalizer_def m_equalizer
    by presburger

  have m_eq: "chi_f \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>M\<^esub>"
    using m_equalizer unfolding equalizer_def
    by (-, typecheck_cfuncs, metis cfunc_type_def comp_associative
        terminal_func_comp terminal_func_type true_func_type)

  obtain D d where
    d_equalizer: "equalizer D d exists_f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>)"
    using equalizer_exists by (typecheck_cfuncs, blast)

  have d_type[type_rule]: "d : D \<rightarrow> A"
    using cfunc_type_def exists_f_type equalizer_def d_equalizer
    by presburger

  have d_monomorphism: "monomorphism d"
    using d_equalizer equalizer_is_monomorphism by auto
    
  have d_eq: "exists_f \<circ>\<^sub>c d = \<t> \<circ>\<^sub>c \<beta>\<^bsub>D\<^esub>"
    using d_equalizer unfolding equalizer_def
    by (-, typecheck_cfuncs, metis cfunc_type_def comp_associative
        terminal_func_comp terminal_func_type true_func_type)

  have "exists_f \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m"
  proof(rule one_separator[where X = M and Y = \<Omega> ])
    show "exists_f \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m : M \<rightarrow> \<Omega>"
      by typecheck_cfuncs 
    show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m : M \<rightarrow> \<Omega>"
      by typecheck_cfuncs
  next
    fix x  
    assume x_type[type_rule]: "x \<in>\<^sub>c M"

    then have mx_type[type_rule]: "m \<circ>\<^sub>c x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c A"
      by typecheck_cfuncs
    then obtain n a where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" 
                     and a_type[type_rule]: "a \<in>\<^sub>c A"
                     and mx_eq: "m \<circ>\<^sub>c x = \<langle>n,a\<rangle>"
      using cart_prod_decomp by blast

    have RHS: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m) \<circ>\<^sub>c x = \<t>"
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative id_right_unit2 id_type 
                            terminal_func_comp terminal_func_unique)
    have LHS: "(exists_f \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m) \<circ>\<^sub>c x = \<t>"
      by (typecheck_cfuncs, smt RHS a_type chi_f_type comp_associative2 exists_f_semantics 
          m_eq mx_eq n_type right_cart_proj_cfunc_prod terminal_func_comp)
    show "(exists_f \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m) \<circ>\<^sub>c x"
      by (simp add: LHS RHS)
  qed

  then obtain e where
    e_type[type_rule]: "e: M \<rightarrow> D" and
    e_d_eq: "d \<circ>\<^sub>c e = right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m"
    using d_equalizer unfolding equalizer_def
    by (-, typecheck_cfuncs, metis cfunc_type_def comp_associative)

  have e_injective: "injective e"
  proof(subst injective_def2[where X = M and Y = D])
    show "e : M \<rightarrow> D"
      by typecheck_cfuncs
    show "\<forall>x y. x \<in>\<^sub>c M \<and> y \<in>\<^sub>c M \<and> e \<circ>\<^sub>c x = e \<circ>\<^sub>c y \<longrightarrow> x = y"
    proof safe
      fix u v 
      assume x_type[type_rule]: "u \<in>\<^sub>c M"
      assume y_type[type_rule]: "v \<in>\<^sub>c M"
      assume eu_eq_ev: "e \<circ>\<^sub>c u = e \<circ>\<^sub>c v"

      then have deu_eq_dev: "(right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m) \<circ>\<^sub>c u = (right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m) \<circ>\<^sub>c v"
        by (typecheck_cfuncs, metis cfunc_type_def comp_associative d_type e_d_eq e_type eu_eq_ev)

      obtain nu and au where mu_eqs: "m \<circ>\<^sub>c u = \<langle>nu, au\<rangle>" 
                         and nu_type[type_rule]: "nu \<in>\<^sub>c \<nat>\<^sub>c"
                         and au_type[type_rule]: "au \<in>\<^sub>c A"
        by (meson cart_prod_decomp comp_type m_type x_type)
  
      obtain nv and av where mv_eqs: "m \<circ>\<^sub>c v = \<langle>nv, av\<rangle>" 
                   and nv_type[type_rule]: "nv \<in>\<^sub>c \<nat>\<^sub>c"
                   and av_type[type_rule]: "av \<in>\<^sub>c A"
        by (meson cart_prod_decomp comp_type m_type y_type)
      
      have au_eqs_av:  "au = av"
        by (typecheck_cfuncs, metis cfunc_type_def comp_associative deu_eq_dev m_type mu_eqs mv_eqs 
            nu_type nv_type right_cart_proj_cfunc_prod right_cart_proj_type x_type y_type)
      with chi_f_functional have "nu = nv"
        by (smt (verit, best) AND_is_pullback AND_true_true_is_true av_type 
            chi_f_type comp_associative2 is_pullback_def m_eq m_type mu_eqs mv_eqs
            nu_type nv_type terminal_func_comp terminal_func_type x_type y_type)
      then show "u = v"
        by (typecheck_cfuncs, metis au_eqs_av equalizer_is_monomorphism 
                              m_equalizer m_type monomorphism_def3 mu_eqs mv_eqs)
    qed
  qed

  have e_surjective: "surjective e"
  proof(subst surjective_def2[where X = M and Y = D])
    show "e : M \<rightarrow> D"
      by typecheck_cfuncs
    show "\<forall>y. y \<in>\<^sub>c D \<longrightarrow> (\<exists>x. x \<in>\<^sub>c M \<and> e \<circ>\<^sub>c x = y)"
    proof safe      
      fix y 
      assume y_type[type_rule]: "y \<in>\<^sub>c D"
      
      have "exists_f \<circ>\<^sub>c (d \<circ>\<^sub>c y) = \<t>"      
        by (typecheck_cfuncs, smt (verit, ccfv_SIG) comp_associative2 d_eq 
            one_separator terminal_func_comp terminal_func_type terminal_func_unique)
      then obtain n where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
                      and n_prop:  "chi_f \<circ>\<^sub>c \<langle>n, d \<circ>\<^sub>c y\<rangle> = \<t>"
        using comp_type d_type exists_f_semantics y_type by blast 
  
      then obtain x where x_type[type_rule]: "x \<in>\<^sub>c M"
                      and mx_eqs: "m \<circ>\<^sub>c x = \<langle>n, d \<circ>\<^sub>c y\<rangle>"
        by (typecheck_cfuncs, smt (verit, ccfv_threshold) AND_is_pullback AND_true_true_is_true 
            cfunc_type_def comp_associative2 equalizer_def is_pullback_def m_equalizer n_prop
            terminal_func_comp terminal_func_type)
      have "d \<circ>\<^sub>c (e \<circ>\<^sub>c x) =  d \<circ>\<^sub>c y"
        by (typecheck_cfuncs, metis cfunc_type_def chi_f_type comp_associative e_d_eq equalizer_def
              m_equalizer mx_eqs n_type right_cart_proj_cfunc_prod right_cart_proj_type)
      then have "e \<circ>\<^sub>c x = y"
        using d_monomorphism d_type monomorphism_def3 by (typecheck_cfuncs, blast)
      then show "(\<exists>x. x \<in>\<^sub>c M \<and> e \<circ>\<^sub>c x = y)"
        using x_type by blast
    qed
  qed

  have e_isomorphism: "isomorphism e"
    by (simp add: e_injective e_surjective epi_mon_is_iso injective_imp_monomorphism surjective_is_epimorphism)

  define nu_f where "nu_f = left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m \<circ>\<^sub>c e\<^bold>\<inverse>"
  have nu_f_type[type_rule]: "nu_f : D \<rightarrow> \<nat>\<^sub>c"
    unfolding nu_f_def using e_isomorphism by typecheck_cfuncs

  define mu_f where "mu_f = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D, d)\<^esub>) \<circ>\<^sub>c try_cast d"

  have try_cast_cases:
  "\<And>a. a \<in>\<^sub>c A \<Longrightarrow>
     (\<exists>x. x \<in>\<^sub>c D \<and> (try_cast d \<circ>\<^sub>c a) = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)
   \<or> (\<exists>y. y \<in>\<^sub>c (A \<setminus> (D,d)) \<and> (try_cast d \<circ>\<^sub>c a) = right_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c y)"
    using d_monomorphism d_type try_cast_in_X try_cast_not_in_X by blast

  have mu_f_unfold:
    "mu_f =
       ((left_coproj \<nat>\<^sub>c \<one>) \<circ>\<^sub>c nu_f) \<amalg>
       ((right_coproj \<nat>\<^sub>c \<one>) \<circ>\<^sub>c \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>)  \<circ>\<^sub>c try_cast d"
    unfolding mu_f_def by (typecheck_cfuncs, simp add: cfunc_bowtie_prod_def2 comp_associative2)

  have mu_f_left_obtain:
  "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
     mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n \<Longrightarrow>
     (\<exists>x. x \<in>\<^sub>c D
        \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x
        \<and> n = nu_f \<circ>\<^sub>c x
        \<and> a = d \<circ>\<^sub>c x)"
  proof -
    fix a n
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume mu_left: "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"   
    show "\<exists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x
                \<and> n = nu_f \<circ>\<^sub>c x \<and> a = d \<circ>\<^sub>c x"
    proof (cases "\<exists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x")
      assume "\<exists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x"
      then obtain x where x_type[type_rule]: "x \<in>\<^sub>c D"
        and tcx: "try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x"
        by blast
  
      (* compute mu_f a via bowtie on the left injection *)
      have mu_on_x:
        "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
      proof -
        have "mu_f \<circ>\<^sub>c a = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (try_cast d \<circ>\<^sub>c a)"
          using comp_associative2 d_monomorphism mu_f_def by (typecheck_cfuncs, force)
        also have "... = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)"
          using tcx by simp
        also have "... = ((nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c left_coproj D (A \<setminus> (D,d))) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = (left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c nu_f) \<circ>\<^sub>c x"
          using left_coproj_cfunc_bowtie_prod by (typecheck_cfuncs, presburger)
        also have "... = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        finally show ?thesis.
      qed
  
      (* cancel left_coproj to get n = nu_f x *)
      have n_eq: "n = nu_f \<circ>\<^sub>c x"
        by (typecheck_cfuncs, metis left_coproj_are_monomorphisms left_proj_type monomorphism_def2 mu_left mu_on_x)

      have a_eq: "a = d \<circ>\<^sub>c x"
      proof -
        have "a = into_super d \<circ>\<^sub>c (try_cast d \<circ>\<^sub>c a)"
          by (typecheck_cfuncs, simp add: comp_associative2 d_monomorphism id_left_unit2 into_super_try_cast)
        also have "... = into_super d \<circ>\<^sub>c (left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)"
          using tcx by simp
        also have "... = d \<circ>\<^sub>c x"
          by (typecheck_cfuncs,
              smt (verit, ccfv_threshold) cfunc_type_def comp_associative2 d_monomorphism id_left_unit2
                  try_cast_def2 try_cast_m_m)
        finally show ?thesis.
      qed
      show ?thesis
        using x_type tcx n_eq a_eq by blast
  
    next
      assume "\<nexists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
      then obtain y where y_type[type_rule]: "y \<in>\<^sub>c (A \<setminus> (D,d))"
        and tcy: "try_cast d \<circ>\<^sub>c a =
                  right_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c y"
        using a_type try_cast_cases by blast

      (* compute mu_f a via bowtie on the right injection -> contradiction with mu_left *)
      have mu_right:
        "mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (\<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y)"
      proof -
        have "mu_f \<circ>\<^sub>c a = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (try_cast d \<circ>\<^sub>c a)"
          unfolding mu_f_def by (typecheck_cfuncs, simp add: comp_associative2 d_monomorphism)
        also have "... = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (right_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c y)"
          using tcy by simp
        also have "... = ((nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c right_coproj D (A \<setminus> (D,d))) \<circ>\<^sub>c y"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = (right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c y"
          using right_coproj_cfunc_bowtie_prod
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (\<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        finally show ?thesis.
      qed
  
      then have False
        by (metis coproducts_disjoint mu_left n_type terminal_func_comp terminal_func_type y_type)
      thus ?thesis by blast
    qed
  qed

  have chi_f_nu_d_true:
  "\<And>x. x \<in>\<^sub>c D \<Longrightarrow> chi_f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, d \<circ>\<^sub>c x\<rangle> = \<t>"
  proof -
    fix x
    assume x_type[type_rule]: "x \<in>\<^sub>c D"
  
    have ex: "chi_f \<circ>\<^sub>c m \<circ>\<^sub>c (e\<^bold>\<inverse> \<circ>\<^sub>c x) = \<t>"
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative e_isomorphism id_right_unit2 
            m_eq terminal_func_comp_elem terminal_func_type)
     
    have m_pair: "m \<circ>\<^sub>c (e\<^bold>\<inverse> \<circ>\<^sub>c x) = \<langle>nu_f \<circ>\<^sub>c x, d \<circ>\<^sub>c x\<rangle>"
    proof -
      have proj0:
        "left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c (m \<circ>\<^sub>c (e\<^bold>\<inverse> \<circ>\<^sub>c x)) = nu_f \<circ>\<^sub>c x"
        unfolding nu_f_def
        by (typecheck_cfuncs, metis cfunc_type_def comp_associative e_isomorphism)
      have proj1:
        "right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c (m \<circ>\<^sub>c (e\<^bold>\<inverse> \<circ>\<^sub>c x)) = d \<circ>\<^sub>c x"
        by (typecheck_cfuncs, metis cfunc_type_def comp_associative e_d_eq e_isomorphism id_left_unit2 inverse_def2)
      show ?thesis
        using cfunc_prod_unique cfunc_type_def comp_type d_type e_isomorphism e_type inverse_def2 
              m_type nu_f_type proj0 proj1 x_type by presburger
    qed

    show "chi_f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, d \<circ>\<^sub>c x\<rangle> = \<t>"
      using ex m_pair by simp
  qed

  have Zf_true_iff_f_zero:
  "\<And>n a. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> a \<in>\<^sub>c A \<Longrightarrow>
     (Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t> \<longleftrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero)"
  proof -
    fix n a
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
  
    have Zf_expand: "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> f \<circ>\<^sub>c \<langle>n,a\<rangle>, zero_NA \<circ>\<^sub>c \<langle>n,a\<rangle> \<rangle>"
      unfolding Zf_def by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
  
    show "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t> \<longleftrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero"
      by (typecheck_cfuncs, smt (verit, best) Zf_expand comp_associative2 eq_pred_iff_eq
            id_right_unit2 terminal_func_comp_elem terminal_func_type zero_NA_def)
  qed

  have f_zero_imp_Pf_false:
  "\<And>n a. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> a \<in>\<^sub>c A \<Longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<Longrightarrow> Pf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<f>"
    unfolding Pf_def by (typecheck_cfuncs,
        metis NOT_true_is_false Zf_true_iff_f_zero cfunc_prod_type comp_associative2)

  show ?thesis
  proof (rule ex1I[where a="mu_f"], safe)
    show mu_f_type[type_rule]: "mu_f : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one>"
      unfolding mu_f_def using d_monomorphism by typecheck_cfuncs

    show g2:
    "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
       mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n \<Longrightarrow>
       f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero"
    proof -
      fix a n
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      assume mu_eq: "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"    
      show "f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero"  (* we show that exists_f(a) = t as a \<in>\<^sub>A D *)        
      proof(cases "(\<exists>x. x \<in>\<^sub>c D \<and> (try_cast d \<circ>\<^sub>c a) = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)")
        assume "\<exists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
        then obtain x where x_type[type_rule]: " x \<in>\<^sub>c D" 
                      and left_case: "try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
          by blast
        from mu_f_left_obtain have mu_f_a_eqs: "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
          by (metis a_type left_case left_coproj_are_monomorphisms 
                left_proj_type monomorphism_def3 mu_eq  n_type x_type)       
        then have "left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
          using mu_eq by argo
        then have n_eqs: "n = nu_f \<circ>\<^sub>c x"
          using left_coproj_are_monomorphisms monomorphism_def3 by (-,typecheck_cfuncs, blast)
        from mu_f_left_obtain have a_eq: "a = d \<circ>\<^sub>c x"
          by (metis mu_f_a_eqs a_type left_case left_coproj_are_monomorphisms left_proj_type 
              monomorphism_def2 n_eqs n_type x_type)
        
        have chi_dx: "chi_f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, d \<circ>\<^sub>c x\<rangle> = \<t>"
          using chi_f_nu_d_true by (typecheck_cfuncs, blast)
        
        have Zf_na: "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
          using n_eqs a_eq chi_dx chi_f_semantics by (typecheck_cfuncs, blast)
        have eq_pred_true: "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> f \<circ>\<^sub>c \<langle>n,a\<rangle> , zero_NA \<circ>\<^sub>c \<langle>n,a\<rangle> \<rangle> = \<t>"
          by (typecheck_cfuncs, smt (verit, ccfv_SIG)  Zf_def Zf_na 
                                cfunc_prod_comp cfunc_prod_type comp_associative2)
        have "f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero_NA \<circ>\<^sub>c \<langle>n,a\<rangle>"
          using eq_pred_iff_eq eq_pred_true by (typecheck_cfuncs, blast)
        also have "... = zero"
          unfolding zero_NA_def
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative id_right_unit2 terminal_func_comp_elem)          
        finally show ?thesis.       
      next  (*Here we cover the impossible case.*)
        assume a1: "\<nexists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
        then obtain y where y_type[type_rule]: "y \<in>\<^sub>c (A \<setminus> (D,d))" 
                        and right_case: "(try_cast d \<circ>\<^sub>c a) = right_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c y"
          using try_cast_cases by (typecheck_cfuncs, blast)
        from mu_f_left_obtain have "mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y"
          using a1 a_type mu_eq n_type by blast        
        then have "left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y"
          using mu_eq by argo
        then have False
          using coproducts_disjoint n_type terminal_func_comp terminal_func_type y_type by force
        then show ?thesis
          by simp
      qed
    qed
    show "\<And>a n k. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
       mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n \<Longrightarrow>
       k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k <\<^sub>\<nat> n \<Longrightarrow> f \<circ>\<^sub>c \<langle>k,a\<rangle> = zero \<Longrightarrow> False"
    proof - 
      fix a n k 
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      assume left: "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
      assume m_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
      assume m_lt_n: "k <\<^sub>\<nat> n"
      assume fma_eq: "f \<circ>\<^sub>c \<langle>k,a\<rangle> = zero"

      have "f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero"
        using g2 left by (typecheck_cfuncs, blast)

      show False
      proof(cases "(\<exists>x. x \<in>\<^sub>c D \<and> (try_cast d \<circ>\<^sub>c a) = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)")
        assume "\<exists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
        then obtain x where x_type[type_rule]: " x \<in>\<^sub>c D" 
                      and left_case: "try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
          by blast
        from mu_f_left_obtain have "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"          
          by (typecheck_cfuncs, metis left left_case 
                left_coproj_are_monomorphisms left_proj_type monomorphism_def3  n_type)        
        then have "left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
          using left by argo
        then have n_eqs:  "n = nu_f \<circ>\<^sub>c x"
          using left_coproj_are_monomorphisms left_proj_type 
                monomorphism_def2 by (typecheck_cfuncs, blast)

        have a_eq: "a = d \<circ>\<^sub>c x"  
          by (typecheck_cfuncs, smt (verit, ccfv_SIG) comp_associative2 d_monomorphism 
                d_type left_case monomorphism_def2 try_cast_m_m try_cast_mono try_cast_type x_type)       
        from mu_f_left_obtain have chi_dx: "chi_f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, d \<circ>\<^sub>c x\<rangle> = \<t>"  
          using chi_f_nu_d_true by (typecheck_cfuncs, blast)

        have chi_na: "chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
          using chi_dx n_eqs a_eq by simp

        have Pf_lt: "\<And>k. k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k <\<^sub>\<nat> n \<Longrightarrow> Pf \<circ>\<^sub>c \<langle>k,a\<rangle> = \<t>"
          using chi_f_semantics[OF a_type n_type] chi_na by blast

        have Pf_ma_true: "Pf \<circ>\<^sub>c \<langle>k,a\<rangle> = \<t>"
          using Pf_lt m_type m_lt_n by blast

        (* from f(m,a)=0 we get Zf(m,a)=t, hence Pf(m,a)=f *)
        have zeroNA_ma: "zero_NA \<circ>\<^sub>c \<langle>k,a\<rangle> = zero"
          unfolding zero_NA_def
          by (typecheck_cfuncs,
              metis cfunc_type_def comp_associative id_right_unit2 terminal_func_comp_elem)
                                                 
        have Zf_ma: "Zf \<circ>\<^sub>c \<langle>k,a\<rangle> = \<t>"      
          by (typecheck_cfuncs, simp add: Zf_true_iff_f_zero fma_eq)
       

        have Pf_ma_false: "Pf \<circ>\<^sub>c \<langle>k,a\<rangle> = \<f>"
          using f_zero_imp_Pf_false fma_eq by (typecheck_cfuncs, blast)             
        show False
          using Pf_ma_false Pf_ma_true true_false_distinct by auto
      next
        assume "\<nexists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
        then obtain y where y_type[type_rule]: "y \<in>\<^sub>c (A \<setminus> (D,d))" 
                        and right_case: "(try_cast d \<circ>\<^sub>c a) = right_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c y"
          using try_cast_cases by (typecheck_cfuncs, blast)
        have "mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y"
          by (typecheck_cfuncs, metis coproducts_disjoint left mu_f_left_obtain n_type right_case)        
        then have "left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y"
          using left by argo
        then have False
          using coproducts_disjoint n_type terminal_func_comp terminal_func_type y_type by force
        then show ?thesis
          by simp
      qed
    qed
        
    show "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
           f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<Longrightarrow>
           (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero) \<Longrightarrow>
           mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
    proof -
      fix a n
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      assume fn0: "f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero"
      assume min: "\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero"
    
      have Zf_na: "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        using Zf_true_iff_f_zero a_type fn0 n_type by blast


      have Pf_lt: "\<And>m. m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> m <\<^sub>\<nat> n \<Longrightarrow> Pf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>"
        by (typecheck_cfuncs, smt (verit, ccfv_SIG) NOT_is_false_implies_true NOT_type Pf_def 
            Zf_true_iff_f_zero Zf_type cfunc_prod_type comp_associative2 comp_type min
            true_false_only_truth_values)

      have chi_na: "chi_f \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        using Pf_lt Zf_na chi_f_semantics by (typecheck_cfuncs, blast)

      with exists_f_semantics have exa: "exists_f \<circ>\<^sub>c a = \<t>"
        using n_type by (typecheck_cfuncs, blast)

      then have exa_eq:
        "exists_f \<circ>\<^sub>c a = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c a"
        by (metis a_type cfunc_type_def comp_associative 
            id_right_unit2 terminal_func_comp_elem terminal_func_type true_func_type)
      have 
          "\<forall>h F. ((h : F \<rightarrow> A) \<and> (exists_f \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c h))
              \<longrightarrow> (\<exists>!k. (k : F \<rightarrow> D) \<and> d \<circ>\<^sub>c k = h)"
        by (typecheck_cfuncs, simp add: d_equalizer similar_equalizers)    
      then obtain x where x_type[type_rule]: "x \<in>\<^sub>c D" and dx: "d \<circ>\<^sub>c x = a"
        using a_type exa_eq by blast
      have tc_left: "try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x"
        using comp_associative2 d_monomorphism dx try_cast_m_m by (typecheck_cfuncs, force)

      have chi_nu: "chi_f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, d \<circ>\<^sub>c x\<rangle> = \<t>"
        by (simp add: chi_f_nu_d_true x_type)
      then have chi_nu_a: "chi_f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, a\<rangle> = \<t>"
        using dx by simp
    
      then have nu_eq: "nu_f \<circ>\<^sub>c x = n"
        using a_type chi_f_functional chi_na comp_type n_type nu_f_type x_type by blast

      show "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
      proof - 
        have "mu_f \<circ>\<^sub>c a = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (try_cast d \<circ>\<^sub>c a)"
          unfolding mu_f_def  
          by (typecheck_cfuncs, simp add: comp_associative2 d_monomorphism)
        also have "... = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)"
          using tc_left by simp
        also have "...  = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
          using comp_associative2 left_coproj_cfunc_bowtie_prod by (typecheck_cfuncs, force)
        also have "... = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
          using nu_eq by auto
        finally show ?thesis.
      qed
    qed

    show "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow>
           mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one> \<Longrightarrow>
           n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<Longrightarrow> False"        
    proof -
      fix a n
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume mu_right: "mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      assume fn0: "f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero"

      have Zf_na: "Zf \<circ>\<^sub>c \<langle>n,a\<rangle> = \<t>"
        using Zf_true_iff_f_zero fn0 by (typecheck_cfuncs, blast)

      have exa: "exists_f \<circ>\<^sub>c a = \<t>"
      proof -
        have exZ: "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> Zf \<circ>\<^sub>c \<langle>m,a\<rangle> = \<t>"
          using n_type Zf_na by blast
      
        (* Predicate on \<nat>: “Zf(m,a) = t” *)
        define Za where
          "Za = Zf \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c, a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle>"
      
        have Za_type[type_rule]: "Za : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          unfolding Za_def by typecheck_cfuncs
      
        have Za_at:
          "\<And>m. m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> Za \<circ>\<^sub>c m = Zf \<circ>\<^sub>c \<langle>m,a\<rangle>"
          unfolding Za_def
          by (typecheck_cfuncs, metis right_param_def2 right_param_on_el)


        
        have t\<beta>_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          by typecheck_cfuncs

        (* Build the subobject of \<nat> classified by Za *)
        obtain S m where
          m_eq: "equalizer S m Za (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)"
          using equalizer_exists[OF Za_type t\<beta>_type] 
          by blast 

        have m_type[type_rule]: "m : S \<rightarrow> \<nat>\<^sub>c"
          using Za_type cfunc_type_def equalizer_def m_eq by auto
        then have m_mono: "monomorphism m"
          using equalizer_is_monomorphism m_eq by auto
        then have Sm_sub: "(S,m) \<subseteq>\<^sub>c \<nat>\<^sub>c"
          by (simp add: m_type subobject_of_def2)   
        
        have char_m: "characteristic_func m = Za"
          using characteristic_func_unique_from_equalizer m_eq m_mono by (typecheck_cfuncs, blast)
 
        (* Show S is nonempty, using witness from exZ *)
        have nonemptyS: "nonempty S"
        proof -
          obtain t where tN[type_rule]: "t \<in>\<^sub>c \<nat>\<^sub>c" and Zf_ta: "Zf \<circ>\<^sub>c \<langle>t,a\<rangle> = \<t>"
            using exZ by blast
          have Za_t: "Za \<circ>\<^sub>c t = \<t>"
            using Zf_ta Za_at[OF tN] by simp
          have mem_t: "t \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S,m)"
          proof -
            (* Za(t)=t means “t is in the subobject classified by characteristic_func m” *)
            have cf_t: "characteristic_func m \<circ>\<^sub>c t = \<t>"
              using Za_t char_m by simp
            show ?thesis
              by (typecheck_cfuncs, metis cf_t m_mono not_rel_mem_char_func_false true_false_distinct)

          qed
            (* nonempty S follows from having a relative element of (S,m) *)
          show "nonempty S"
            unfolding nonempty_def using mem_t m_mono m_type try_cast_in_X by blast
        qed
      
        (* Apply the required well-ordering principle to get a least element k of this subobject *)
        obtain k where
          k_mem: "k \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S,m)"
          and k_le: "\<forall>s. s \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S,m) \<longrightarrow> k \<le>\<^sub>\<nat> s"
          using well_ordering_principle[OF nonemptyS Sm_sub] by blast
      
        have kN[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
          using k_mem by (typecheck_cfuncs, metis relative_member_def2)
      
        have Za_k_true: "Za \<circ>\<^sub>c k = \<t>"
        proof -
          (* membership gives characteristic_func m (k) = t, hence Za(k)=t *)
          have cf_k: "characteristic_func m \<circ>\<^sub>c k = \<t>"
            using k_mem kN
            by (typecheck_cfuncs, metis rel_mem_char_func_true Sm_sub subobject_of_def2)
          show ?thesis
            using cf_k char_m by simp
        qed
      
        have Zf_ka: "Zf \<circ>\<^sub>c \<langle>k,a\<rangle> = \<t>"
          using Za_k_true Za_at[OF kN] by simp
      
        (* Now: for all m<k, Zf(m,a) must be false, hence Pf(m,a)=t.
           This is the “minimality” you need to build chi_f(k,a). *)
        have Pf_lt: "\<forall>m0. m0 \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m0 <\<^sub>\<nat> k \<longrightarrow> Pf \<circ>\<^sub>c \<langle>m0,a\<rangle> = \<t>"
        proof (intro allI impI)
          fix m0
          assume m0N[type_rule]: "m0 \<in>\<^sub>c \<nat>\<^sub>c"
          assume m0_lt: "m0 <\<^sub>\<nat> k"
      
          have not_mem_m0: "\<not>(m0 \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S,m))"
          proof
            assume mem_m0: "m0 \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S,m)"
            have k_le_m0: "k \<le>\<^sub>\<nat> m0"
              using k_le mem_m0 by blast
            (* But m0 < k contradicts k \<le> m0 *)
            have "k <\<^sub>\<nat> k"
              using kN k_le_m0 leq_lt_trans m0N m0_lt by blast
            then show False
              by (simp add: kN lt_irrefl)
            qed

          have Za_m0_ne_true: "Za \<circ>\<^sub>c m0 \<noteq> \<t>"
          proof
            assume Za_m0: "Za \<circ>\<^sub>c m0 = \<t>"
            have cf_m0: "characteristic_func m \<circ>\<^sub>c m0 = \<t>"
              using Za_m0 char_m by simp
            have mem_m0: "m0 \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S,m)"
              by (typecheck_cfuncs, 
                  simp add: Za_m0 char_m characteristic_func_true_relative_member m_mono)
            show False
              using not_mem_m0 mem_m0 by blast
          qed
      
          have Za_m0_false: "Za \<circ>\<^sub>c m0 = \<f>"
            using Za_m0_ne_true true_false_only_truth_values
            by (typecheck_cfuncs, blast)
      
          have Zf_m0_false: "Zf \<circ>\<^sub>c \<langle>m0,a\<rangle> \<noteq> zero"
            by (typecheck_cfuncs, metis cfunc_type_def n_neq_succ_n succ_n_type 
                true_false_only_truth_values zero_is_not_successor)
          
          (* Conclude Pf(m0,a)=t from Za(m0)=f i.e. Zf(m0,a) not true *)
          show "Pf \<circ>\<^sub>c \<langle>m0,a\<rangle> = \<t>"
            unfolding Pf_def
            by (typecheck_cfuncs, metis NOT_false_is_true Za_at Za_m0_false comp_associative2)
        qed

        have chi_k: "chi_f \<circ>\<^sub>c \<langle>k,a\<rangle> = \<t>"
          using chi_f_semantics[OF a_type kN] Zf_ka Pf_lt by blast
      
        show "exists_f \<circ>\<^sub>c a = \<t>"
          using exists_f_semantics[OF a_type] kN chi_k by blast
      qed

      have exa_eq:
        "exists_f \<circ>\<^sub>c a = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c a"
        using exa a_type
        by (metis cfunc_type_def comp_associative id_right_unit2
                  terminal_func_comp_elem terminal_func_type true_func_type)

      (* equalizer gives the unique x with d\<circ>x = a *)
      have ex1_dx: "(\<exists>!x. (x : \<one> \<rightarrow> D) \<and> d \<circ>\<^sub>c x = a)"
      proof -
        have H:
          "\<forall>h F. ((h : F \<rightarrow> A) \<and> (exists_f \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c h))
                \<longrightarrow> (\<exists>!k. (k : F \<rightarrow> D) \<and> d \<circ>\<^sub>c k = h)"
          by (typecheck_cfuncs, simp add: d_equalizer similar_equalizers)
        show ?thesis
          using H a_type exa_eq by blast
      qed

      then obtain x where x_type[type_rule]: "x \<in>\<^sub>c D" and dx: "d \<circ>\<^sub>c x = a"
        by blast

      have tc_left: "try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x"
        using dx
        by (typecheck_cfuncs,
            metis comp_associative2 d_monomorphism try_cast_m_m)

      have mu_left:
        "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
      proof -
        have "mu_f \<circ>\<^sub>c a = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (try_cast d \<circ>\<^sub>c a)"
          unfolding mu_f_def
          by (typecheck_cfuncs, simp add: comp_associative2 d_monomorphism)
        also have "... = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c (left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)"
          using tc_left by simp
        also have "... = ((nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D,d)\<^esub>) \<circ>\<^sub>c left_coproj D (A \<setminus> (D,d))) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = (left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c nu_f) \<circ>\<^sub>c x"
          using left_coproj_cfunc_bowtie_prod
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (nu_f \<circ>\<^sub>c x)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        finally show ?thesis.
      qed

      show False
        using coproducts_disjoint mu_left mu_right x_type nu_f_type
        by (metis comp_type coproducts_disjoint id_type mu_left mu_right nu_f_type x_type)
    qed

    show "\<And>a. a \<in>\<^sub>c A \<Longrightarrow>
       \<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero \<Longrightarrow>
       mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>"   
    proof -
      fix a
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume allnz: "\<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero"
    
      have not_left_tc:
        "\<not> (\<exists>x. x \<in>\<^sub>c D \<and> try_cast d \<circ>\<^sub>c a =
                left_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c x)"
      proof (rule ccontr, safe) 
        fix x 
        assume x_type[type_rule]: "x \<in>\<^sub>c D"
        assume left_coproj: "try_cast d \<circ>\<^sub>c a = left_coproj D (A \<setminus> (D, d)) \<circ>\<^sub>c x"
    
        have a_eq: "a = d \<circ>\<^sub>c x"
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative d_monomorphism 
              left_coproj monomorphism_def3 try_cast_m_m try_cast_mono try_cast_type)
    
        have chi: "chi_f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, a\<rangle> = \<t>"
          using chi_f_nu_d_true[OF x_type] a_eq by simp
    
        have Zf0: "Zf \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, a\<rangle> = \<t>"
          using chi chi_f_semantics by (typecheck_cfuncs, blast)
    
        have f0: "f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, a\<rangle> = zero"
          using Zf_true_iff_f_zero Zf0
          by (typecheck_cfuncs, blast)
    
        have fneq: "f \<circ>\<^sub>c \<langle>nu_f \<circ>\<^sub>c x, a\<rangle> \<noteq> zero"
          using allnz by (typecheck_cfuncs, blast)
    
        show False 
          using f0 fneq by simp
      qed
    
      have tc_right_ex:
        "\<exists>y. y \<in>\<^sub>c (A \<setminus> (D,d)) \<and>
             try_cast d \<circ>\<^sub>c a = right_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c y"
        using try_cast_cases not_left_tc by (typecheck_cfuncs, blast)
    
      then obtain y where y_type[type_rule]: "y \<in>\<^sub>c (A \<setminus> (D,d))"
        and tcy: "try_cast d \<circ>\<^sub>c a =
                  right_coproj D (A \<setminus> (D,d)) \<circ>\<^sub>c y"
        by blast
    
      have mu_on_y:
        "mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c (\<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y)"
        by (typecheck_cfuncs, metis coproducts_disjoint coprojs_jointly_surj
            mu_f_left_obtain tcy terminal_func_unique)
      
      have beta_y: "\<beta>\<^bsub>A\<setminus>(D,d)\<^esub> \<circ>\<^sub>c y = id\<^sub>c \<one>"
        by (typecheck_cfuncs, metis cfunc_type_def terminal_func_comp_elem y_type)
    
      show "mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>"
        using mu_on_y beta_y by simp
    qed

    show "\<And>\<mu>. \<mu> : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one> \<Longrightarrow>
         \<forall>a n. a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow>
               (\<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n) =
               (f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<and>
                (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero)) \<Longrightarrow>
         \<forall>a. a \<in>\<^sub>c A \<longrightarrow>
             (\<mu> \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>) =
             (\<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero) \<Longrightarrow>
         \<mu> = mu_f"
    proof -
      fix \<mu>
      assume \<mu>_type[type_rule]: "\<mu> : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one>"
      assume \<mu>_left_spec:
        "\<forall>a n. a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow>
          (\<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n) =
          (f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<and> (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero))"
      assume \<mu>_right_spec:
        "\<forall>a. a \<in>\<^sub>c A \<longrightarrow>
          (\<mu> \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>) =
          (\<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero)"           
      show "\<mu> = mu_f"
      proof (rule one_separator[where X = A and Y = "\<nat>\<^sub>c \<Coprod> \<one>"])
        show "\<mu> : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one>" by (rule \<mu>_type)
        show "mu_f : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one>" by (rule mu_f_type)
      next
        fix a
        assume a_type[type_rule]: "a \<in>\<^sub>c A"
    
        have \<mu>a_cases:
          "(\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> \<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n) \<or>
          (\<exists>t. t \<in>\<^sub>c \<one>   \<and> \<mu> \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c t)"
          using coprojs_jointly_surj by (typecheck_cfuncs,blast)
    
        show "\<mu> \<circ>\<^sub>c a = mu_f \<circ>\<^sub>c a"
        proof (cases "(\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> \<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n)")
          assume "\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> \<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
          then obtain n where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
            and \<mu>_left: "\<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n" by blast

          have minprop:
            "f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<and> (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero)"
            using \<mu>_left \<mu>_left_spec a_type n_type by blast

          have mu_f_left: "mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
            using \<open>\<And>n a. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<Longrightarrow> 
                  \<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero \<Longrightarrow> mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n\<close>
              minprop by (typecheck_cfuncs, blast)      
          show ?thesis 
            using \<mu>_left mu_f_left by simp
        next
          assume "\<nexists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> \<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
          then have right_coproj: "(\<exists>t. t \<in>\<^sub>c \<one>   \<and> \<mu> \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c t)"
            using \<mu>a_cases by blast  
          then have \<mu>_right: "\<mu> \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>"
            using one_unique_element by (typecheck_cfuncs, auto)
    
          have allnz: "\<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero"
            using \<mu>_right \<mu>_right_spec a_type by blast

          have mu_f_right: "mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>"
            by (typecheck_cfuncs, metis \<mu>_right_spec 
                \<open>\<And>a. a \<in>\<^sub>c A \<Longrightarrow> \<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero \<Longrightarrow> 
                 mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>\<close>
                right_coproj one_unique_element)
          show ?thesis using \<mu>_right mu_f_right by simp
        qed
      qed
    qed
  qed
qed

(* How to build a two-argument recursive function by hand, step by step -- and what an
   automated tool would need to do instead.

   The raw natural number object axiom (natural_number_object_property2 in Nats.thy) only ever
   hands you a ONE-argument function u : N --> X, built from two ingredients:
     q : 1 --> X    (a chosen starting point of X)
     f : X --> X    (a chosen "step" endomorphism of X)
   and it guarantees u(zero) = q and f(u(n)) = u(succ n), i.e. u(n) = f applied n times to q.

   To define something like m +N n (add1/add2 in Add.thy) or m *N n (mult1/mult2 in Mult.thy),
   the desired function has TWO arguments, not one, and X = N is the wrong space to recurse in --
   what actually needs to be built up step by step, as n counts 0,1,2,..., is not a number but a
   whole FUNCTION of the other argument ("add n more", "multiply by n more"). That function
   lives in an exponential object. So the recipe used by hand in Add.thy/Mult.thy is:

   Step 1. Pick the space to recurse in: X = B^A, functions from the OTHER argument's type A
     into the result type B. (For add2 and mult2, A = B = N.)

   Step 2. Turn the desired base case f0 : A --> B into a POINT of X, by first extending it to a
     map A x 1 --> B (compose with left_cart_proj A 1, which just discards the dummy 1 factor)
     and then transposing:
        q := (f0 o left_cart_proj A 1) sharp  : 1 --> B^A

   Step 3. Turn the desired step behaviour step : A x B --> B into an ENDOMORPHISM of X. Given the
     current function h : A --> B (a point of X), we want the next function a |-> step(a, h(a)).
     Evaluation does exactly this: eval_func B A : A x B^A --> B sends (a,h) to h(a). So pair a
     with the evaluation, feed the result through step, and transpose again:
        f := (step o <left_cart_proj A (B^A), eval_func B A>) sharp  : B^A --> B^A

   Step 4. Feed q and f from Steps 2-3 into natural_number_object_property2 to get the unique
     u : N --> B^A -- this is the raw axiom's output, still a function INTO an exponential object,
     still awkward to use directly (this is the "indirect and unnatural" step).

   Step 5. Undo the currying: evaluate u against its A argument to land back on an ordinary
     two-argument function g : A x N --> B:
        g := eval_func B A o (id A x_f u)
     (this is exactly what add2/mult2's own definitions do to add1/mult1).

   The theorem below packages Steps 1-5 into a single existence-and-uniqueness statement, so that
   from now on nobody has to re-derive q, f, or the eval_func uncurrying step by hand: supply f0
   and step, and g (satisfying the ordinary recursive equations) drops out. An ML tool built on
   top of this would only need to parse a user's equations into f0/step and call this theorem --
   none of the sharp/eval_func bookkeeping above would need to be re-invented or even seen by the
   user. Compare with primitive_recursion above, which additionally lets step see the recursion
   index n itself (at the cost of recursing in (N x B)^A instead of the smaller B^A) --
   use iteration_recursion below whenever the step rule does not need to know n. *)

(* Note: iteration_recursion below would follow as a quick corollary of primitive_recursion
   above -- just pad step : A x B --> B out to a step' : A x (N x B) --> B that ignores its N
   component (e.g. step' = step o <left_cart_proj A (N x B), right_cart_proj N B o right_cart_proj
   A (N x B)>), feed that into primitive_recursion, and the resulting u already satisfies
   iteration_recursion's equations verbatim. We prove it directly from the raw NNO axiom instead,
   because the point of this theorem is didactic: the direct proof is exactly Steps 1-5 above
   made rigorous, and it is that q/f construction -- not the shorter derivation via
   primitive_recursion -- that mirrors what add1/mult1 do by hand and that the ML tool below
   needs to mechanize. *)
theorem iteration_recursion:
  assumes f0_type[type_rule]: "f0 : A \<rightarrow> B"
  assumes step_type[type_rule]: "step : A \<times>\<^sub>c B \<rightarrow> B"
  shows "\<exists>!g. g : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B \<and> (\<forall> a n. (a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    g \<circ>\<^sub>c \<langle>a, zero\<rangle> = f0 \<circ>\<^sub>c a \<and>
    g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = step \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>)"
proof -

  define q :: cfunc where
    "q = (f0 \<circ>\<^sub>c left_cart_proj A \<one>)\<^sup>\<sharp>"
  have q_type[type_rule]: "q : \<one> \<rightarrow> B\<^sup>(A)"
    unfolding q_def by typecheck_cfuncs

  define f :: cfunc where
    "f = (step \<circ>\<^sub>c \<langle>left_cart_proj A (B\<^sup>(A)), eval_func B A\<rangle>)\<^sup>\<sharp>"
  have f_type[type_rule]: "f : B\<^sup>(A) \<rightarrow> B\<^sup>(A)"
    unfolding f_def by typecheck_cfuncs

  obtain u where u_type[type_rule]: "u : \<nat>\<^sub>c \<rightarrow> B\<^sup>(A)"
    and u_zero: "u \<circ>\<^sub>c zero = q"
    and u_succ: "f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    using natural_number_object_property2[OF q_type f_type] by blast

  define g :: cfunc where
    "g = eval_func B A \<circ>\<^sub>c (id A \<times>\<^sub>f u)"
  have g_type[type_rule]: "g : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
    unfolding g_def by typecheck_cfuncs

  have g_zero: "\<And>a. a \<in>\<^sub>c A \<Longrightarrow> g \<circ>\<^sub>c \<langle>a, zero\<rangle> = f0 \<circ>\<^sub>c a"
  proof -
    fix a
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    have "g \<circ>\<^sub>c \<langle>a, zero\<rangle> = eval_func B A \<circ>\<^sub>c \<langle>id A \<circ>\<^sub>c a, u \<circ>\<^sub>c zero\<rangle>"
      unfolding g_def
      by (smt (verit, best) a_type cfunc_cross_prod_comp_cfunc_prod cfunc_cross_prod_type 
          cfunc_prod_type comp_associative2 eval_func_type id_type u_type zero_type)    
    also have "... = eval_func B A \<circ>\<^sub>c \<langle>a, q\<rangle>"
      using a_type id_left_unit2 u_zero by force
    also have "... = eval_func B A \<circ>\<^sub>c ((id A \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>)"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
    also have "... = (eval_func B A \<circ>\<^sub>c (id A \<times>\<^sub>f q)) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (f0 \<circ>\<^sub>c left_cart_proj A \<one>) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
      unfolding q_def by (typecheck_cfuncs, simp add: transpose_func_def)
    also have "... = f0 \<circ>\<^sub>c (left_cart_proj A \<one> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = f0 \<circ>\<^sub>c a"
      by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
    finally show "g \<circ>\<^sub>c \<langle>a, zero\<rangle> = f0 \<circ>\<^sub>c a".
  qed

  have g_succ: "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
      g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = step \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>"
  proof -
    fix a n
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    have "g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = eval_func B A \<circ>\<^sub>c \<langle>id A \<circ>\<^sub>c a, u \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>"
      unfolding g_def
      by (smt (verit, ccfv_SIG) a_type cfunc_cross_prod_comp_cfunc_prod cfunc_cross_prod_type 
          cfunc_prod_type comp_associative2 eval_func_type id_type n_type succ_n_type u_type)
    also have "... = eval_func B A \<circ>\<^sub>c \<langle>a, (u \<circ>\<^sub>c successor) \<circ>\<^sub>c n\<rangle>"
      by (typecheck_cfuncs, simp add: id_left_unit2 comp_associative2)
    also have "... = eval_func B A \<circ>\<^sub>c \<langle>a, (f \<circ>\<^sub>c u) \<circ>\<^sub>c n\<rangle>"
      by (simp add: u_succ)
    also have "... = eval_func B A \<circ>\<^sub>c \<langle>id A \<circ>\<^sub>c a, f \<circ>\<^sub>c (u \<circ>\<^sub>c n)\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2)
    also have "... = eval_func B A \<circ>\<^sub>c ((id A \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>a, u \<circ>\<^sub>c n\<rangle>)"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
    also have "... = (eval_func B A \<circ>\<^sub>c (id A \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>a, u \<circ>\<^sub>c n\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (step \<circ>\<^sub>c \<langle>left_cart_proj A (B\<^sup>(A)), eval_func B A\<rangle>) \<circ>\<^sub>c \<langle>a, u \<circ>\<^sub>c n\<rangle>"
      unfolding f_def by (typecheck_cfuncs, simp add: transpose_func_def)
    also have "... = step \<circ>\<^sub>c (\<langle>left_cart_proj A (B\<^sup>(A)), eval_func B A\<rangle> \<circ>\<^sub>c \<langle>a, u \<circ>\<^sub>c n\<rangle>)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = step \<circ>\<^sub>c \<langle>left_cart_proj A (B\<^sup>(A)) \<circ>\<^sub>c \<langle>a, u \<circ>\<^sub>c n\<rangle>, eval_func B A \<circ>\<^sub>c \<langle>a, u \<circ>\<^sub>c n\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have "... = step \<circ>\<^sub>c \<langle>a, eval_func B A \<circ>\<^sub>c \<langle>a, u \<circ>\<^sub>c n\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
    also have "... = step \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>"
      unfolding g_def by (typecheck_cfuncs, 
          smt (verit, ccfv_SIG) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)
    finally show "g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = step \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>".
  qed

  show ?thesis
  proof (intro ex1I[where a=g], safe)
    show "g : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
      by (rule g_type)
    show "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> g \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a"
      using g_zero by blast
    show "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> g \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = step \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"
      using g_succ by blast

    fix g'
    assume g'_type[type_rule]: "g' : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
    assume g'_property: "\<forall>a n. a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow>
       g' \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a \<and> g' \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = step \<circ>\<^sub>c \<langle>a, g' \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"

    show "g' = g"
    proof(rule one_separator[where X = "A \<times>\<^sub>c \<nat>\<^sub>c", where Y = B])
      show "g' : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs
      show "g : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c A \<times>\<^sub>c \<nat>\<^sub>c"
      obtain a m where a_type[type_rule]: "a \<in>\<^sub>c A" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
        and x_def: "x = \<langle>a, m\<rangle>"
        using cart_prod_decomp x_type by blast

      have "(g' \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m = (g \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m"
      proof(etcs_rule nat_eq_induction)
        show "(g' \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = (g \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
          using g'_property g_zero by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
      next
        fix n
        assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
        assume "(g' \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n = (g \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
        then have IH: "g' \<circ>\<^sub>c \<langle>a, n\<rangle> = g \<circ>\<^sub>c \<langle>a, n\<rangle>"
          by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2)
        have "g' \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = step \<circ>\<^sub>c \<langle>a, g' \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"
          using g'_property by (typecheck_cfuncs, blast)
        also have "... = step \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"
          by (simp add: IH)
        also have "... = g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle>"
          by (simp add: a_type g_succ n_type)
        finally show "(g' \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = (g \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
          by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
      qed
      then show "g' \<circ>\<^sub>c x = g \<circ>\<^sub>c x"
        by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2 x_def)
    qed
  qed
qed

(* Tier 1 tool: given the base case f0 and step function you intend to feed into
   iteration_recursion above, print the q and f terms that would have to be built by hand to
   invoke the raw natural_number_object_property2 axiom (Nats.thy) directly. This performs no
   proof -- it only builds and displays the two terms (unsimplified, exactly as
   iteration_recursion's own q_def/f_def would construct them). Use iteration_recursion itself,
   or a later Tier 2 tool, to actually define a function.

   SYNTAX:

     iteration_qf "A" "B" "f0" "step"

   Exactly four arguments, each written as an ordinary double-quoted Isabelle string (the
   quotes are required -- this is plain text that gets re-parsed as a term, not a term you type
   directly). They are positional and must appear in this order:

     "A"    -- the OTHER argument's type, as a cset term. This is whatever you are recursing
               alongside n (e.g. "\<nat>\<^sub>c" if the function you want has type N x N --> _, or
               "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" if it has type (N x N) x N --> _, and so on).

     "B"    -- the RESULT type, as a cset term (e.g. "\<nat>\<^sub>c").

     "f0"   -- the base case, as a cfunc term of type A --> B. This is g(a,0) written as a
               function of a alone. If the base case is "return a unchanged" use "id \<nat>\<^sub>c" (or
               "id A" for whatever A is); if it is "always return some fixed constant c" use
               something like "c \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>" (the constant map, using the terminal
               projection \<beta> to first collapse A down to a point, then land on c).

     "step" -- the recursive step, as a cfunc term of type A \<times>\<^sub>c B --> B. This describes how to
               get g(a, succ n) out of a and the ALREADY-COMPUTED g(a,n) -- but you write it as
               an ordinary two-argument cfunc, where the first slot of the product stands for a
               and the second slot stands for the current value g(a,n); you never write n, succ,
               or g itself here, only how to combine a with "the value so far". Two common
               shapes: if the step ignores a and just transforms the current value, use
               "h \<circ>\<^sub>c right_cart_proj A B" for whatever h : B --> B does the transforming
               (e.g. "successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c" below, which just applies
               successor to the current value and ignores a); if the step combines a with the
               current value via some binary operation "op", use "op" directly if op already has
               type A \<times>\<^sub>c B --> B (e.g. "add2" below, since add2 : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c --> \<nat>\<^sub>c already
               takes (a, current value) and adds them).

   The command does NOT check that f0/step actually have the types you claimed for A/B -- it
   just splices your four strings into the q/f formulas from Steps 2-3 above and asks Isabelle
   to parse the result. If you got a type wrong, you will see an ordinary type-mismatch error
   from that parse, pointing at the offending piece. *)

ML \<open>
structure Iteration_QF =
struct

fun print_qf ctxt a_src b_src f0_src step_src =
  let
    val q_src =
      "(" ^ f0_src ^ " \<circ>\<^sub>c left_cart_proj (" ^ a_src ^ ") \<one>)\<^sup>\<sharp>"
    val f_src =
      "(" ^ step_src ^ " \<circ>\<^sub>c \<langle>left_cart_proj (" ^ a_src ^ ") ((" ^ b_src ^ ")\<^sup>((" ^ a_src ^ "))), " ^
      "eval_func (" ^ b_src ^ ") (" ^ a_src ^ ")\<rangle>)\<^sup>\<sharp>"

    val q = Syntax.read_term ctxt q_src
    val f = Syntax.read_term ctxt f_src
  in
    writeln ("q : \<one> \<rightarrow> " ^ b_src ^ "^" ^ a_src ^ "  (the base point) =");
    writeln (Syntax.string_of_term ctxt q);
    writeln "";
    writeln ("f : " ^ b_src ^ "^" ^ a_src ^ " \<rightarrow> " ^ b_src ^ "^" ^ a_src ^
      "  (the step endomorphism) =");
    writeln (Syntax.string_of_term ctxt f)
  end

end
\<close>

ML \<open>
Outer_Syntax.command \<^command_keyword>\<open>iteration_qf\<close>
  "print the q and f terms needed to define a recursive function via iteration_recursion"
  (Parse.string -- Parse.string -- Parse.string -- Parse.string >>
    (fn (((a, b), f0), step) =>
      Toplevel.keep (fn state =>
        Iteration_QF.print_qf (Toplevel.context_of state) a b f0 step)))
\<close>

(* Worked example: reproduce add1/add2's q and f from Add.thy (add's base case is the identity,
   since m + 0 = m; add's step ignores its A-argument entirely and just applies successor to
   the current value). *)
iteration_qf "\<nat>\<^sub>c" "\<nat>\<^sub>c" "id \<nat>\<^sub>c" "successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c"

(* Worked example: reproduce mult1/mult2's q and f from Mult.thy (mult's base case is the
   constant zero map, since m \<cdot> 0 = 0; mult's step adds the A-argument to the current value). *)
iteration_qf "\<nat>\<^sub>c" "\<nat>\<^sub>c" "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" "add2"

(* Tier 2 tool: given a name plus the same base case f0 and step function as iteration_qf, print
   the ready-to-paste Isabelle source -- a definition plus four lemmas -- that defines a function
   with exactly those properties via iteration_recursion. This does NOT define anything itself
   and proves nothing on its own; it only writes out the text you would otherwise have to type by
   hand, for you to copy out of the Output window and paste into your theory. q and f never
   appear anywhere in the printed text, because iteration_recursion has already absorbed that
   bookkeeping -- what gets printed is exactly the same shape of definition + lemmas that
   add1/add2/add_respects_zero_on_right (Add.thy) or mult1/mult2 (Mult.thy) build by hand:

     definition NAME :: "cfunc" where "NAME = (THE g. ...)"
     lemma NAME_property: "NAME : A x N --> B \<and> (\<forall> a n. ...)"
     lemma NAME_type[type_rule]: "NAME : A x N --> B"
     lemma NAME_zero: "a \<in>\<^sub>c A \<Longrightarrow> NAME \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a"
     lemma NAME_succ: "a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
       NAME \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = step \<circ>\<^sub>c \<langle>a, NAME \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"

   SYNTAX:

     iteration_script name "A" "B" "f0" "step"

   Five arguments. "name" is a plain (unquoted) new constant name of your choosing -- it must
   not already be in use once pasted. The remaining four are exactly as in iteration_qf above
   (see that comment for how to write A, B, f0, and step); consult it first if you are unsure
   what to supply. Once pasted into your theory, the generated proof of NAME_property will fail
   with an ordinary typechecking error if f0/step do not actually typecheck at A/B as claimed --
   exactly as it would if you had written the definition by hand. *)

ML \<open>
structure Iteration_Script =
struct

fun generate_source name aT bT f0 step =
  cat_lines
    ["definition " ^ name ^ " :: \"cfunc\" where",
     "  \"" ^ name ^ " = (THE g. g : (" ^ aT ^ ") \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (" ^ bT ^ ") \<and> (\<forall> a n. " ^
       "(a \<in>\<^sub>c (" ^ aT ^ ") \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>",
     "    g \<circ>\<^sub>c \<langle>a, zero\<rangle> = (" ^ f0 ^ ") \<circ>\<^sub>c a \<and>",
     "    g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (" ^ step ^ ") \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>))\"",
     "",
     "lemma " ^ name ^ "_property:",
     "  \"" ^ name ^ " : (" ^ aT ^ ") \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (" ^ bT ^ ") \<and> (\<forall> a n. " ^
       "(a \<in>\<^sub>c (" ^ aT ^ ") \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>",
     "    " ^ name ^ " \<circ>\<^sub>c \<langle>a, zero\<rangle> = (" ^ f0 ^ ") \<circ>\<^sub>c a \<and>",
     "    " ^ name ^ " \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (" ^ step ^ ") \<circ>\<^sub>c " ^
       "\<langle>a, " ^ name ^ " \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>)\"",
     "  unfolding " ^ name ^ "_def",
     "  by (rule theI', rule iteration_recursion, typecheck_cfuncs+)",
     "",
     "lemma " ^ name ^ "_type[type_rule]: \"" ^ name ^ " : (" ^ aT ^ ") \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (" ^ bT ^ ")\"",
     "  using " ^ name ^ "_property by blast",
     "",
     "lemma " ^ name ^ "_zero:",
     "  assumes \"a \<in>\<^sub>c (" ^ aT ^ ")\"",
     "  shows \"" ^ name ^ " \<circ>\<^sub>c \<langle>a, zero\<rangle> = (" ^ f0 ^ ") \<circ>\<^sub>c a\"",
     "  using assms " ^ name ^ "_property by blast",
     "",
     "lemma " ^ name ^ "_succ:",
     "  assumes \"a \<in>\<^sub>c (" ^ aT ^ ")\" \"n \<in>\<^sub>c \<nat>\<^sub>c\"",
     "  shows \"" ^ name ^ " \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (" ^ step ^ ") \<circ>\<^sub>c " ^
       "\<langle>a, " ^ name ^ " \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>\"",
     "  using assms " ^ name ^ "_property by blast"]

fun print_script name aT bT f0 step =
  writeln (generate_source name aT bT f0 step)

end
\<close>

ML \<open>
Outer_Syntax.command \<^command_keyword>\<open>iteration_script\<close>
  "print ready-to-paste Isabelle source defining a recursive function via iteration_recursion"
  (Parse.name -- Parse.string -- Parse.string -- Parse.string -- Parse.string >>
    (fn ((((name, aT), bT), f0), step) =>
      Toplevel.keep (fn _ =>
        Iteration_Script.print_script name aT bT f0 step)))
\<close>

(* Worked example: print the paste-ready definition of addition. Copy the printed text out of
   the Output window into a theory to get add2 / add2_type / add2_zero / add2_succ
   matching add1/add2's behaviour, without ever building add1 or the exponential object
   \<nat>\<^sub>c\<^sup>(\<nat>\<^sub>c) by hand. *)
iteration_script autogenerated_add2 "\<nat>\<^sub>c" "\<nat>\<^sub>c" "id \<nat>\<^sub>c" "successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c"

(* The printed text pasted verbatim, followed by a proof that this really is the same function
   as the hand-built add2 -- not just something that looks superficially similar. *)

definition autogenerated_add2 :: "cfunc" where
  "autogenerated_add2 = (THE g. g : (\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c) \<and> (\<forall> a n. (a \<in>\<^sub>c (\<nat>\<^sub>c) \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    g \<circ>\<^sub>c \<langle>a, zero\<rangle> = (id \<nat>\<^sub>c) \<circ>\<^sub>c a \<and>
    g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>))"

lemma autogenerated_add2_property:
  "autogenerated_add2 : (\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c) \<and> (\<forall> a n. (a \<in>\<^sub>c (\<nat>\<^sub>c) \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    autogenerated_add2 \<circ>\<^sub>c \<langle>a, zero\<rangle> = (id \<nat>\<^sub>c) \<circ>\<^sub>c a \<and>
    autogenerated_add2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a, autogenerated_add2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>)"
  unfolding autogenerated_add2_def
  by (rule theI', rule iteration_recursion, typecheck_cfuncs+)

lemma autogenerated_add2_type[type_rule]: "autogenerated_add2 : (\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c)"
  using autogenerated_add2_property by blast

lemma autogenerated_add2_zero:
  assumes "a \<in>\<^sub>c (\<nat>\<^sub>c)"
  shows "autogenerated_add2 \<circ>\<^sub>c \<langle>a, zero\<rangle> = (id \<nat>\<^sub>c) \<circ>\<^sub>c a"
  using assms autogenerated_add2_property by blast

lemma autogenerated_add2_succ:
  assumes "a \<in>\<^sub>c (\<nat>\<^sub>c)" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "autogenerated_add2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a, autogenerated_add2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>"
  using assms autogenerated_add2_property by blast

theorem autogenerated_add2_is_add2: "autogenerated_add2 = add2"
proof (rule one_separator[where X = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
  show "autogenerated_add2 : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "add2 : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  fix x
  assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  obtain a m where a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    and x_def: "x = \<langle>a, m\<rangle>"
    using cart_prod_decomp x_type by blast

  have "(autogenerated_add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m = (add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m"
  proof (etcs_rule nat_eq_induction)
    show "(autogenerated_add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = (add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
    proof -
      have "(autogenerated_add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero
          = autogenerated_add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
      also have "... = autogenerated_add2 \<circ>\<^sub>c \<langle>a, zero\<rangle>"
        using a_type id_left_unit2 id_right_unit2 terminal_func_comp_elem zero_type by auto
      also have "... = id \<nat>\<^sub>c \<circ>\<^sub>c a"
        by (simp add: autogenerated_add2_zero a_type)
      also have "... = a"
        using a_type id_left_unit2 by auto
      also have "... = add2 \<circ>\<^sub>c \<langle>a, zero\<rangle>"
        using add_respects_zero_on_right[OF a_type] by (simp add: add_def)
      also have "... = (add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
      finally show ?thesis .
    qed
  next
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume "(autogenerated_add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n = (add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
    then have IH: "autogenerated_add2 \<circ>\<^sub>c \<langle>a, n\<rangle> = add2 \<circ>\<^sub>c \<langle>a, n\<rangle>"
      by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2)
    have "autogenerated_add2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle>
        = (successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a, autogenerated_add2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>"
      using autogenerated_add2_succ by (typecheck_cfuncs, blast)
    also have "... = successor \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a, autogenerated_add2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c (autogenerated_add2 \<circ>\<^sub>c \<langle>a, n\<rangle>)"
      by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_prod)
    also have "... = successor \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>a, n\<rangle>)"
      by (simp add: IH)
    also have "... = add2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle>"
      using add2_respects_succ_right[OF a_type n_type] by simp
    finally show "(autogenerated_add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n
        = (add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
      by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
  qed
  then show "autogenerated_add2 \<circ>\<^sub>c x = add2 \<circ>\<^sub>c x"
    by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2 x_def)
qed

(* Now we try this for multiplication.

   f0 = zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>: "multiply anything by 0 and you get 0" -- the constant-zero map.

   step = add2: g \<langle>a, successor m\<rangle> = step \<langle>a, g \<langle>a, m\<rangle>\<rangle>, and step only ever sees "a" and the
   current value "g \<langle>a,m\<rangle>", never m itself. Writing n for a, we know g \<langle>n,m\<rangle> = n \<sqdot> m, and we want
   g \<langle>n, m+1\<rangle> = n \<sqdot> (m+1). Since n \<sqdot> (m+1) = n\<sqdot>m + n = n + n\<sqdot>m, step just needs to add its two
   inputs together -- so step = add2 works directly, with no need to reorder the pair first. *)
iteration_script autogenerated_mult2 "\<nat>\<^sub>c" "\<nat>\<^sub>c" "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" "add2"

definition autogenerated_mult2 :: "cfunc" where
  "autogenerated_mult2 = (THE g. g : (\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c) \<and> (\<forall> a n. (a \<in>\<^sub>c (\<nat>\<^sub>c) \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    g \<circ>\<^sub>c \<langle>a, zero\<rangle> = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c a \<and>
    g \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (add2) \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>))"

lemma autogenerated_mult2_property:
  "autogenerated_mult2 : (\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c) \<and> (\<forall> a n. (a \<in>\<^sub>c (\<nat>\<^sub>c) \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    autogenerated_mult2 \<circ>\<^sub>c \<langle>a, zero\<rangle> = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c a \<and>
    autogenerated_mult2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (add2) \<circ>\<^sub>c \<langle>a, autogenerated_mult2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>)"
  unfolding autogenerated_mult2_def
  by (rule theI', rule iteration_recursion, typecheck_cfuncs+)

lemma autogenerated_mult2_type[type_rule]: "autogenerated_mult2 : (\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c)"
  using autogenerated_mult2_property by blast

lemma autogenerated_mult2_zero:
  assumes "a \<in>\<^sub>c (\<nat>\<^sub>c)"
  shows "autogenerated_mult2 \<circ>\<^sub>c \<langle>a, zero\<rangle> = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c a"
  using assms autogenerated_mult2_property by blast

lemma autogenerated_mult2_succ:
  assumes "a \<in>\<^sub>c (\<nat>\<^sub>c)" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "autogenerated_mult2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = (add2) \<circ>\<^sub>c \<langle>a, autogenerated_mult2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>"
  using assms autogenerated_mult2_property by blast

(* And, as with add2, a proof that this really is the same function as the hand-built mult2 --
   using mult_respects_zero_right and mult_respects_succ_right (Mult.thy) to identify mult2's
   own base/step behaviour with autogenerated_mult2's. *)

theorem autogenerated_mult2_is_mult2: "autogenerated_mult2 = mult2"
proof (rule one_separator[where X = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
  show "autogenerated_mult2 : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "mult2 : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  fix x
  assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  obtain a m where a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    and x_def: "x = \<langle>a, m\<rangle>"
    using cart_prod_decomp x_type by blast

  have "(autogenerated_mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m = (mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m"
  proof (etcs_rule nat_eq_induction)
    show "(autogenerated_mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = (mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
    proof -
      have "(autogenerated_mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero
          = autogenerated_mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
      also have "... = autogenerated_mult2 \<circ>\<^sub>c \<langle>a, zero\<rangle>"
        using a_type id_left_unit2 id_right_unit2 terminal_func_comp_elem zero_type by auto
      also have "... = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c a"
        by (simp add: autogenerated_mult2_zero a_type)
      also have "... = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c a)"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = zero"
        using a_type by (typecheck_cfuncs, metis id_right_unit2 terminal_func_comp_elem)
      also have "... = a \<cdot>\<^sub>\<nat> zero"
        using mult_respects_zero_right[OF a_type] by simp
      also have "... = mult2 \<circ>\<^sub>c \<langle>a, zero\<rangle>"
        by (simp add: mult_def)
      also have "... = (mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
      finally show ?thesis .
    qed
  next
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume "(autogenerated_mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n = (mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
    then have IH: "autogenerated_mult2 \<circ>\<^sub>c \<langle>a, n\<rangle> = mult2 \<circ>\<^sub>c \<langle>a, n\<rangle>"
      by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2)
    have "autogenerated_mult2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = add2 \<circ>\<^sub>c \<langle>a, autogenerated_mult2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>"
      using autogenerated_mult2_succ by (typecheck_cfuncs, blast)
    also have "... = add2 \<circ>\<^sub>c \<langle>a, mult2 \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>"
      by (simp add: IH)
    also have "... = a +\<^sub>\<nat> (a \<cdot>\<^sub>\<nat> n)"
      by (simp add: add_def mult_def)
    also have "... = a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n)"
      using mult_respects_succ_right[OF a_type n_type] by simp
    also have "... = mult2 \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle>"
      by (simp add: mult_def)
    finally show "(autogenerated_mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n
        = (mult2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
      by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
  qed
  then show "autogenerated_mult2 \<circ>\<^sub>c x = mult2 \<circ>\<^sub>c x"
    by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2 x_def)
qed

end