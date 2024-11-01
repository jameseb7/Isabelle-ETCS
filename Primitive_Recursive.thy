theory Primitive_Recursive
  imports Category_Set.ETCS
begin

lemma primitive_recursion:
  assumes f0_type[type_rule]: "f0 : A \<rightarrow> B"
  assumes f_type[type_rule]: "f : A \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c B) \<rightarrow> B"
  shows "\<exists>!u. u : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B \<and> (\<forall> a n. (a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    u \<circ>\<^sub>c \<langle>a, zero\<rangle> = f0 \<circ>\<^sub>c a \<and>
    u \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a, \<langle>n, u \<circ>\<^sub>c \<langle>a, n\<rangle>\<rangle>\<rangle>)"
proof -

  obtain y where y_type[type_rule]: "y : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>"
    and y_zero: "y \<circ>\<^sub>c zero = \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle>\<^sup>\<sharp>"
    and y_succ: "y \<circ>\<^sub>c successor = (\<langle>left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c y"
    by (typecheck_cfuncs, smt natural_number_object_property2)

  have yb_zero: "y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f zero) = \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A \<times>\<^sub>c \<one>\<^esub>,  f0 \<circ>\<^sub>c left_cart_proj A \<one>\<rangle>"
    by (typecheck_cfuncs, metis flat_cancels_sharp inv_transpose_of_composition y_zero)

  have yb_succ: "y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f successor) = \<langle>left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle> \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y)"
    by (etcs_assocl, typecheck_cfuncs, metis flat_cancels_sharp inv_transpose_of_composition transpose_func_type y_succ)

  have yb_preserves_nat: "\<And>a. a \<in>\<^sub>c A \<Longrightarrow> left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> = id \<nat>\<^sub>c"
  proof (etcs_rule natural_number_object_func_unique[where f="successor"])
    fix a
    assume a_type[type_rule]: "a \<in>\<^sub>c A"

    show "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      sorry

    show "(left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
         successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      sorry

    show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
      by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  qed

  show ?thesis
  proof (intro ex1I[where a="right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>"], safe)
    show "right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat> : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
      by (typecheck_cfuncs)
  next
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
      finally show ?thesis .
    qed

    show "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"
    proof -
      have "(right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c (id A \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>a,n\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
      also have "... = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c (y\<^sup>\<flat> \<circ>\<^sub>c (id A \<times>\<^sub>f successor)) \<circ>\<^sub>c \<langle>a,n\<rangle>"
        by (etcs_assocr, simp)
      also have "... = (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c right_cart_proj A (\<nat>\<^sub>c \<times>\<^sub>c B), f\<rangle>) \<circ>\<^sub>c \<langle>left_cart_proj A ((\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup>), eval_func (\<nat>\<^sub>c \<times>\<^sub>c B) A\<rangle> \<circ>\<^sub>c (id A \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a,n\<rangle>"
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
  next
    fix u
    assume u_type[type_rule]: "u : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> B"
    assume u_property: "\<forall>a n. a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> u \<circ>\<^sub>c \<langle>a,zero\<rangle> = f0 \<circ>\<^sub>c a \<and> u \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle> = f \<circ>\<^sub>c \<langle>a,\<langle>n,u \<circ>\<^sub>c \<langle>a,n\<rangle>\<rangle>\<rangle>"

    show "u = right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>"
    proof (rule ccontr)
      assume "u \<noteq> right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>"
      then obtain m where m_type[type_rule]: "m \<in>\<^sub>c A \<times>\<^sub>c \<nat>\<^sub>c"
        and m_separates: "u \<circ>\<^sub>c m \<noteq> (right_cart_proj \<nat>\<^sub>c B \<circ>\<^sub>c y\<^sup>\<flat>) \<circ>\<^sub>c m"
        using one_separator by (typecheck_cfuncs, blast)

      obtain a n where a_type[type_rule]: "a \<in>\<^sub>c A" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
        and m_def: "m = \<langle>a, n\<rangle>"
        using cart_prod_decomp m_type by blast
        

      show False
      proof (cases "n = zero")
        assume "n = zero"
        then show ?thesis sorry
      next
        assume "n \<noteq> zero"
        then show ?thesis sorry
      qed
    qed
  qed
qed
