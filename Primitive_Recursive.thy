theory Primitive_Recursive
  imports Category_Set.ETCS
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
      

lemma primitive_recursion:
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
  
      
              












