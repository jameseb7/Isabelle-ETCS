theory Primitive_Recursive 
  imports Comparison
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

  obtain y where y_type[type_rule]: "y : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>"
    and y_zero: "y \<circ>\<^sub>c zero = \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle>\<^sup>\<sharp>"
    and y_succ: "y \<circ>\<^sub>c successor = (\<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c y"
    by (typecheck_cfuncs, smt natural_number_object_property2)

  have yb_zero: "y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f zero) = \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle>"
    by (typecheck_cfuncs, metis flat_cancels_sharp inv_transpose_of_composition y_zero)

  have yb_succ: "y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f successor) = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y)"
    by (etcs_assocl, typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_of_composition sharp_comp y_succ)    

  have yb_preserves_nat: "\<And>a. a \<in>\<^sub>c A \<Longrightarrow> left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> = id \<nat>\<^sub>c"
  proof (etcs_rule natural_number_object_func_unique[where f="successor"])
    fix a
    assume a_type[type_rule]: "a \<in>\<^sub>c A"

    show "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    proof -
      have "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a, zero\<rangle>"
        by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>,  f0 \<circ>\<^sub>c left_cart_proj A \<one> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>\<rangle>"
        by (etcs_assocl, typecheck_cfuncs, smt (verit, best) comp_associative2 left_cart_proj_cfunc_prod yb_zero)
      also have "... = zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
        using left_cart_proj_cfunc_prod by (typecheck_cfuncs, simp)
      also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 one_unique_element)
      finally show ?thesis.
    qed
     

    show "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
         successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof -
      have "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c  successor =
                 left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
        by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f successor)) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
      also have "... = left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        using cfunc_type_def comp_associative comp_type yb_succ by (typecheck_cfuncs, auto)
      also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        using comp_associative2 left_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
      also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c  eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        by (typecheck_cfuncs, smt (verit, ccfv_threshold) comp_associative2 right_cart_proj_cfunc_prod)
      also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"          
        by (typecheck_cfuncs, smt (verit, best) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2 inv_transpose_func_def3)
      finally show ?thesis.
    qed

    show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
      by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  qed

  show ?thesis
  proof (intro ex1I[where a="right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>"], safe)
    show "right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
      by typecheck_cfuncs
    show g1: "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a"
    proof -
      fix a n
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      show "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a"
      proof -
        have "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,zero\<rangle> = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c (id A \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
        also have "... = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
          by (etcs_assocr, simp)
        also have "... = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle> \<circ>\<^sub>c \<langle>a, id \<one>\<rangle>"
          by (subst yb_zero, simp)
        also have "... = f0 \<circ>\<^sub>c a"
          by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
        finally show ?thesis.
      qed
    qed
    show g2: "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
    proof -
      fix a n
      assume a_type[type_rule]: "a \<in>\<^sub>c A"
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      show "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
      proof -
        have "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c (id A \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
        also have "... = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f successor)) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (etcs_assocr, simp)
        also have "... = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle>) \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (subst yb_succ, etcs_assocl, simp)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>"
          by (etcs_subst right_cart_proj_cfunc_prod, simp)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>) \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>, eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"
          by (etcs_subst cfunc_prod_comp, simp)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>a, y \<circ>\<^sub>c n\<rangle>, y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 inv_transpose_func_def3)
        also have "... = f \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>a, y \<circ>\<^sub>c n\<rangle>, \<langle>left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a,n\<rangle>, right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, metis cfunc_prod_unique)
        also have "... = f \<circ>\<^sub>c \<langle>a, \<langle>left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a,n\<rangle>, right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (etcs_subst left_cart_proj_cfunc_prod, simp)
        also have "... = f \<circ>\<^sub>c \<langle>a, \<langle>(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n, right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
        also have "... = f \<circ>\<^sub>c \<langle>a,\<langle>n,(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt id_left_unit2 yb_preserves_nat comp_associative2)
        finally show ?thesis.
      qed
    qed
    fix u
    assume u_type[type_rule]: "u : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
    assume u_property: "\<forall>a n. a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> u \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a \<and> u \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,u \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"

    show "u = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>"
    proof(rule one_separator[where X = "A \<times>\<^sub>c \<nat>\<^sub>c", where Y = B])
      show "u : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs
      show "right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c A \<times>\<^sub>c \<nat>\<^sub>c"
      obtain a m where a_type[type_rule]: "a \<in>\<^sub>c A" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
        and x_def: "x = \<langle>a, m\<rangle>"
        using cart_prod_decomp x_type by blast

      have "u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs

      have "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c \<rangle>: \<nat>\<^sub>c \<rightarrow> B"
        by typecheck_cfuncs

      have "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m"
      proof(etcs_rule nat_eq_induction)
        show "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
          by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2 g1 u_property)
      next
        fix n
        assume  n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
        assume "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
        then have induction_hypothesis: "u \<circ>\<^sub>c \<langle>a ,n\<rangle> = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a, n\<rangle>"
          by (typecheck_cfuncs_prems, smt cart_prod_extract_right comp_associative2)
        have "u \<circ>\<^sub>c \<langle>a ,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a, \<langle>n, u \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
          using u_property by (typecheck_cfuncs, blast)
        also have "... = f \<circ>\<^sub>c \<langle>a, \<langle>n, (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>\<rangle>"
          by (simp add: induction_hypothesis)
        also have "... = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a ,successor \<circ>\<^sub>c n\<rangle>"
          by (simp add: a_type g2 n_type)
        finally show "(u \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = ((right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
          by (typecheck_cfuncs, smt cart_prod_extract_right comp_associative2)
      qed
      then show "u \<circ>\<^sub>c x = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c x"
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

  have chi_f_sharp_type[type_rule]: "chi_f\<^sup>\<sharp> : A \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
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

end