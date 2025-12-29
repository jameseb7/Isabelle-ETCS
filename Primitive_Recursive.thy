theory Primitive_Recursive 
  imports "Category_Set_Arithmetic/Inequality"
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
      finally show ?thesis .
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
        finally show ?thesis .
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

 
    (*  Curry in m to get Psharp : (\<nat>\<times>A) \<rightarrow> \<Omega>^\<nat> --- *)
  obtain Psharp where
    Psharp_def: "Psharp = P\<^sup>\<sharp>"
    by blast
  then have Psharp_type[type_rule]: "Psharp : (\<nat>\<^sub>c \<times>\<^sub>c A) \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
    unfolding Psharp_def
    by typecheck_cfuncs

  (*  \<chi>_f(n,a) :\<equiv> Zf(n,a) \<and> \<forall>m. P(m,n,a) --- *)
  obtain chi_f where
    chi_f_def: "chi_f = AND \<circ>\<^sub>c \<langle> Zf, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c Psharp \<rangle>"
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
    proof -  
      have "(chi_f\<^sup>\<sharp> \<circ>\<^sub>c a)\<^sup>\<flat>  = ((chi_f\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f a))"
        by (typecheck_cfuncs, simp add: inv_transpose_of_composition)
      also have "... = (chi_f \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f a))"
        using chi_f_type flat_cancels_sharp by auto
      also have "... = chi_f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>, a \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_def2)
      also have "... = chi_f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>, (a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>\<rangle>"        
        by (etcs_assocr, typecheck_cfuncs, metis terminal_func_unique)
      also have "... = (chi_f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>"
        by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
      finally show ?thesis
        using cfunc_cross_prod_right_terminal_decomp sharp_comp by (typecheck_cfuncs, force)
    qed
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
     have f1: "Zf \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t> \<and> (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c Psharp \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t>"
     proof -
       have "(AND \<circ>\<^sub>c \<langle>Zf, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c Psharp\<rangle>) \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t>"
         using chi1 chi_f_def by auto
       then have "AND \<circ>\<^sub>c \<langle>Zf \<circ>\<^sub>c \<langle>n1,a\<rangle>, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c Psharp \<circ>\<^sub>c \<langle>n1,a\<rangle>\<rangle>  = \<t>"
         by (typecheck_cfuncs, smt (z3) cfunc_prod_comp cfunc_prod_type comp_associative2 comp_type)
       then show ?thesis
         by (typecheck_cfuncs, meson AND_true_imp_both_true)
     qed
  
     (* --- unpack chi_f at (n2,a)  --- *)
     have f2: "Zf \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t> \<and> (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c Psharp \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t>"
     proof -
       have "(AND \<circ>\<^sub>c \<langle>Zf, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c Psharp\<rangle>) \<circ>\<^sub>c \<langle>n2,a\<rangle> = \<t>"
         using chi2 chi_f_def by auto
       then have "AND \<circ>\<^sub>c \<langle>Zf \<circ>\<^sub>c \<langle>n2,a\<rangle>, (FORALL \<nat>\<^sub>c) \<circ>\<^sub>c Psharp \<circ>\<^sub>c \<langle>n2,a\<rangle>\<rangle>  = \<t>"
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
     
          (* Key typing/transpose fact: Psharp \<circ> \<langle>n2,a\<rangle> is the curry of p2\<circ>\<pi>0 *)
          have curry_id:
            "Psharp \<circ>\<^sub>c \<langle>n2,a\<rangle> = (p2 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
          proof -
            (* prove by showing their flats are equal *)
            have flat_eq:
              "(Psharp \<circ>\<^sub>c \<langle>n2,a\<rangle>)\<^sup>\<flat> = p2 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>"
            proof -
              have "(Psharp \<circ>\<^sub>c \<langle>n2,a\<rangle>)\<^sup>\<flat> = Psharp\<^sup>\<flat> \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>n2,a\<rangle>)"
                by (typecheck_cfuncs, simp add: inv_transpose_of_composition)
              also have "... = P \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>n2,a\<rangle>)"
                using P_type Psharp_def flat_cancels_sharp by moura
  
              also have "... = P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>,
                                     \<langle>n2,a\<rangle> \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one> \<rangle>"
                by (typecheck_cfuncs, simp add: cfunc_cross_prod_def2)
              also have "... = P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>,
                                     (\<langle>n2,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one> \<rangle>"
                by (etcs_assocr, typecheck_cfuncs, metis terminal_func_unique)
              also have "... = (P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c, (\<langle>n2,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>"
                by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
              also have "... = p2 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>"
                unfolding p2_def by simp
              finally show ?thesis .
            qed
            show ?thesis
              by (metis Psharp_type aA cfunc_prod_type comp_type flat_eq n2N sharp_cancels_flat)
          qed
  
          have For2': "(FORALL \<nat>\<^sub>c) \<circ>\<^sub>c (p2 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp> = \<t>"
            using curry_id f2 by presburger
  
  
          have P_at_n1: "p2 \<circ>\<^sub>c n1 = \<t>"
            using FORALL_true_implies_all_true curry_id f2 n1N p2_type by presburger
  
          have P_pair: "P \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle> = \<t>"
            using P_at_n1
            unfolding p2_def
            by (smt (verit, ccfv_SIG) P_type aA cart_prod_extract_left cfunc_prod_type
                comp_associative2 comp_type id_type n1N n2N terminal_func_type)
  
  
         (* Unfold P: with lt(n1,n2)=\<t>, IMPLIES forces Pf(n1,a)=\<t> *)
          have lt_comp: "lt \<circ>\<^sub>c \<langle>n1,n2\<rangle> = \<t>"
            using lt12 unfolding lt_infix_def by simp
  
          have Zf1: "Zf \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t>"
            using f1 by simp
  
          have Pf1_false: "Pf \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<f>"
          proof -
            have "Pf \<circ>\<^sub>c \<langle>n1,a\<rangle> = (NOT \<circ>\<^sub>c Zf) \<circ>\<^sub>c \<langle>n1,a\<rangle>"
              using Pf_def by fastforce
            also have "... = NOT \<circ>\<^sub>c (Zf \<circ>\<^sub>c \<langle>n1,a\<rangle>)"
              by (typecheck_cfuncs, simp add: comp_associative2)
            also have "... = NOT \<circ>\<^sub>c \<t>"
              using Zf1 by simp
            also have "... = \<f>"
              using NOT_true_is_false by blast
            finally show ?thesis.
          qed
  
          then have "NOT \<circ>\<^sub>c Pf = Zf"
            using NOT_type Pf_def Zf_type comp_associative2 double_negation id_left_unit2 by auto
  
          have Pf1_true: "Pf \<circ>\<^sub>c \<langle>n1,a\<rangle> = \<t>"
          proof -
            have P_pair_unfold:
              "P \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>
               =
               IMPLIES \<circ>\<^sub>c
        \<langle> lt \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
              left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle>,
          Pf \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
              right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<rangle> \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>"
              unfolding P_def
              by (typecheck_cfuncs, smt (verit) NOT_type comp_associative2
                    comp_type leq_type lt_def swap_def swap_type)
            also have " ... = IMPLIES \<circ>\<^sub>c
        \<langle> lt \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
              left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>,
          Pf \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
              right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle> \<rangle>"
              by (typecheck_cfuncs, smt (verit) NOT_type cfunc_prod_comp cfunc_type_def
                    comp_associative comp_type leq_type lt_def swap_def swap_type)
            also have " ... = IMPLIES \<circ>\<^sub>c
        \<langle> lt \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>,
              left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>\<rangle>,
          Pf \<circ>\<^sub>c
            \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>,
              right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle> \<rangle> \<rangle>"
              using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
            also have " ... = IMPLIES \<circ>\<^sub>c
          \<langle> lt \<circ>\<^sub>c
              \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>,
                left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c \<langle>n2,a\<rangle>\<rangle>,
            Pf \<circ>\<^sub>c
              \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n1, \<langle>n2,a\<rangle>\<rangle>,
                right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle> \<rangle>"
              by (typecheck_cfuncs, metis right_cart_proj_cfunc_prod)
            also have " ... = IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle> n1, n2\<rangle>, Pf \<circ>\<^sub>c \<langle> n1, a\<rangle>\<rangle>"
              by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
            also have " ... = IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle> n1, n2\<rangle>, \<t>\<rangle>"
              by (typecheck_cfuncs, metis IMPLIES_true_true_is_true P_pair calculation lt12 lt_infix_def)
            also have "... = \<t>"
              using P_pair calculation by argo
            finally show ?thesis
              using IMPLIES_true_false_is_false IMPLIES_true_true_is_true Pf1_false
                \<open>IMPLIES \<circ>\<^sub>c \<langle>lt \<circ>\<^sub>c \<langle>n1,n2\<rangle>,Pf \<circ>\<^sub>c \<langle>n1,a\<rangle>\<rangle> = IMPLIES \<circ>\<^sub>c \<langle>lt \<circ>\<^sub>c \<langle>n1,n2\<rangle>,\<t>\<rangle>\<close> lt_comp by argo              
          qed
  
          then show "n1 = n2"
            using Pf1_false true_false_distinct by auto          
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
          "Psharp \<circ>\<^sub>c \<langle>n1,a\<rangle> = (p1 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>"
        proof -
          (* prove by showing their flats are equal *)
          have flat_eq:
            "(Psharp \<circ>\<^sub>c \<langle>n1,a\<rangle>)\<^sup>\<flat> = p1 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>"
          proof -
            have "(Psharp \<circ>\<^sub>c \<langle>n1,a\<rangle>)\<^sup>\<flat> = Psharp\<^sup>\<flat> \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>n1,a\<rangle>)"
              by (typecheck_cfuncs, simp add: inv_transpose_of_composition)
            also have "... = P \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>n1,a\<rangle>)"
              using P_type Psharp_def flat_cancels_sharp by moura
  
            also have "... = P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>,
                                   \<langle>n1,a\<rangle> \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one> \<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_def2)
            also have "... = P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>,
                                   (\<langle>n1,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one> \<rangle>"
              by (etcs_assocr, typecheck_cfuncs, metis terminal_func_unique)
            also have "... = (P \<circ>\<^sub>c \<langle> id \<nat>\<^sub>c, (\<langle>n1,a\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>"
              by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
            also have "... = p1 \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<one>"
              unfolding p1_def by simp
            finally show ?thesis.
          qed
          show ?thesis
            by (metis Psharp_type aA cfunc_prod_type comp_type flat_eq n1N sharp_cancels_flat)
        qed
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
        proof -
          have "P \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle> =
          IMPLIES \<circ>\<^sub>c
                  \<langle> lt \<circ>\<^sub>c
                      \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                        left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle>,
                    Pf \<circ>\<^sub>c
                      \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                        right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<rangle> \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt (verit, ccfv_SIG) NOT_type P_def cfunc_type_def
                comp_associative comp_type leq_type lt_def swap_def swap_type)
          also have "... =  IMPLIES \<circ>\<^sub>c
                  \<langle> lt \<circ>\<^sub>c
                      \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                        left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle>\<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle>,
                    Pf \<circ>\<^sub>c
                      \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A),
                        right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<rangle> \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt (verit) NOT_type cfunc_prod_comp cfunc_type_def
                                  comp_associative comp_type leq_type lt_def swap_def swap_type)                
          also have "... =  IMPLIES \<circ>\<^sub>c
                  \<langle> lt \<circ>\<^sub>c
                      \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle>,
                        left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle>\<rangle>,
                    Pf \<circ>\<^sub>c
                      \<langle> left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A) \<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle> ,
                        right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c A)\<circ>\<^sub>c \<langle>n2, \<langle>n1,a\<rangle>\<rangle> \<rangle> \<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
          also have "... =  IMPLIES \<circ>\<^sub>c
                  \<langle> lt \<circ>\<^sub>c \<langle> n2, left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c \<langle>n1,a\<rangle>\<rangle>,
                    Pf \<circ>\<^sub>c \<langle> n2, right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c \<langle>n1,a\<rangle> \<rangle> \<rangle>"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
          also have "... =  IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle> n2, n1\<rangle>, Pf \<circ>\<^sub>c \<langle> n2, a \<rangle> \<rangle>"
            using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
          finally show ?thesis.
        qed
  
        have IMPL_t:
          "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>n2,n1\<rangle>, Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle> = \<t>"
          using P_pair' P_pair_unfold by simp
  
        have IMPL_f:
          "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>n2,n1\<rangle>, Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle> = \<f>"
        proof -
          have "IMPLIES \<circ>\<^sub>c \<langle> lt \<circ>\<^sub>c \<langle>n2,n1\<rangle>, Pf \<circ>\<^sub>c \<langle>n2,a\<rangle> \<rangle>
                = IMPLIES \<circ>\<^sub>c \<langle>\<t>, \<f>\<rangle>"
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

  thm equalizer_def

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
    sorry
  then obtain e where 
    e_type[type_rule]: "e: M \<rightarrow> D" and
    e_d_eq: "d \<circ>\<^sub>c e = right_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m"
    using d_equalizer unfolding equalizer_def
    by (-, typecheck_cfuncs, metis cfunc_type_def comp_associative)

  have e_injective: "injective e"
    sorry
  have e_surjective: "surjective e"
    sorry
  have e_isomorphism: "isomorphism e"
    sorry

  define nu_f where "nu_f = left_cart_proj \<nat>\<^sub>c A \<circ>\<^sub>c m \<circ>\<^sub>c e\<^bold>\<inverse>"
  have nu_f_type[type_rule]: "nu_f : D \<rightarrow> \<nat>\<^sub>c"
    unfolding nu_f_def using e_isomorphism by typecheck_cfuncs

  define mu_f where "mu_f = (nu_f \<bowtie>\<^sub>f \<beta>\<^bsub>A\<setminus>(D, d)\<^esub>) \<circ>\<^sub>c try_cast d"
 
  show ?thesis
  proof (rule ex1I[where a="mu_f"], safe)
    show mu_f_type[type_rule]: "mu_f : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one>"
      unfolding mu_f_def using d_monomorphism by typecheck_cfuncs

    show "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
           mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n \<Longrightarrow>
           f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero"
      sorry

    show "\<And>a n m. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
       mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n \<Longrightarrow>
       m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> m <\<^sub>\<nat> n \<Longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> = zero \<Longrightarrow> False"
      sorry

    show "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
           f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<Longrightarrow>
           \<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero \<Longrightarrow>
           mu_f \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n"
      sorry

    show "\<And>a n. a \<in>\<^sub>c A \<Longrightarrow>
           mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one> \<Longrightarrow>
           n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<Longrightarrow> False"
      sorry

    show "\<And>a. a \<in>\<^sub>c A \<Longrightarrow>
         \<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero \<Longrightarrow>
         mu_f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>"
      sorry

    show "\<And>\<mu>. \<mu> : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one> \<Longrightarrow>
         \<forall>a n. a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow>
               (\<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n) =
               (f \<circ>\<^sub>c \<langle>n,a\<rangle> = zero \<and>
                (\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow>
                     m <\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m,a\<rangle> \<noteq> zero)) \<Longrightarrow>
         \<forall>a. a \<in>\<^sub>c A \<longrightarrow>
             (\<mu> \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id\<^sub>c \<one>) =
             (\<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> f \<circ>\<^sub>c \<langle>n,a\<rangle> \<noteq> zero) \<Longrightarrow>
         \<mu> = mu_f"
      sorry
  qed
end