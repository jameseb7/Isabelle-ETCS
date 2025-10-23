theory Recursive
  imports "./Category_Set_Arithmetic/Inequality"
begin

term "(\<le>\<^sub>\<nat>)"

theorem minimisation:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<times>\<^sub>c A \<rightarrow> \<nat>\<^sub>c"
  shows "\<exists>\<mu>. \<mu> : A \<rightarrow> \<nat>\<^sub>c \<Coprod> \<one> \<and> 
    (\<forall>a. a \<in>\<^sub>c A \<longrightarrow> 
      (\<forall>n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> \<mu> \<circ>\<^sub>c a = left_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c n \<longleftrightarrow> 
        f \<circ>\<^sub>c \<langle>n, a\<rangle> = zero \<and> (\<forall>i. i \<in>\<^sub>c \<nat>\<^sub>c \<and> successor \<circ>\<^sub>c i \<le>\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>i, a\<rangle> \<noteq> zero))
      \<and> (\<mu> \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c \<one> \<circ>\<^sub>c id \<one> \<longleftrightarrow> (\<nexists> n. f \<circ>\<^sub>c \<langle>n, a\<rangle> = zero)))"
proof -

  (* checking if f(\<langle>zero, a\<rangle>) is zero *)
  define zero_case where
    "zero_case = 
      ((zero \<bowtie>\<^sub>f left_coproj \<one> \<one>)
       \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c
       \<circ>\<^sub>c (f \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>, id A\<rangle>) \<times>\<^sub>f zero)\<^sup>\<sharp>"
  have zero_case_type[type_rule]: "zero_case : \<one> \<rightarrow> (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>))\<^bsup>A\<^esup>"
    unfolding zero_case_def by typecheck_cfuncs

  (* checking if f(\<langle>successor \<circ>\<^sub>c n, a\<rangle>) is zero when a zero has not already been found *)
  define succ_subcase where
    "succ_subcase =
      (left_cart_proj \<nat>\<^sub>c \<one> \<bowtie>\<^sub>f left_coproj \<one> \<one> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>)
       \<circ>\<^sub>c dist_prod_coprod_left \<nat>\<^sub>c \<one> \<one>
       \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c A, case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c A\<^esub>\<rangle>\<rangle>
       \<circ>\<^sub>c (successor \<times>\<^sub>f id A)"
  have succ_subcase_type[type_rule]: "succ_subcase : \<nat>\<^sub>c \<times>\<^sub>c A \<rightarrow> \<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>)"
    unfolding succ_subcase_def by typecheck_cfuncs

  (* applying succ_subcase if zero has not already been found and ignoring otherwise *)
  define succ_case where
    "succ_case =
      ((succ_subcase \<amalg> (right_coproj \<nat>\<^sub>c (\<one> \<Coprod> \<one>) \<circ>\<^sub>c right_coproj \<one> \<one> \<circ>\<^sub>c \<beta>\<^bsub>(\<one> \<Coprod> \<one>) \<times>\<^sub>c A\<^esub>))
      \<circ>\<^sub>c dist_prod_coprod_right \<nat>\<^sub>c (\<one> \<Coprod> \<one>) A
      \<circ>\<^sub>c \<langle>eval_func (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>)) A, left_cart_proj A ((\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>))\<^bsup>A\<^esup>)\<rangle>)\<^sup>\<sharp>"
  have succ_case_type[type_rule]: "succ_case : (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>))\<^bsup>A\<^esup> \<rightarrow> (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>))\<^bsup>A\<^esup>"
    unfolding succ_case_def by typecheck_cfuncs

  obtain is_first_zero' where is_first_zero'_type [type_rule]: "is_first_zero' : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>))\<^bsup>A\<^esup>"
    and is_first_zero'_zero: "is_first_zero' \<circ>\<^sub>c zero = zero_case"
    and is_first_zero'_succ: "is_first_zero' \<circ>\<^sub>c successor = succ_case \<circ>\<^sub>c is_first_zero'"
    using natural_number_object_property by (metis succ_case_type zero_case_type) 

  define is_first_zero where
    "is_first_zero = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<amalg> \<f>)) \<circ>\<^sub>c is_first_zero'\<^sup>\<flat>"
  have is_first_zero_type[type_rule]: "is_first_zero : A \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
    unfolding is_first_zero_def by typecheck_cfuncs

  have is_first_zero_property:
    "is_first_zero \<circ>\<^sub>c \<langle>a, n\<rangle> = \<t> \<longleftrightarrow> (f \<circ>\<^sub>c \<langle>n, a\<rangle> = zero \<and> (\<forall>m. successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n \<longrightarrow> f \<circ>\<^sub>c \<langle>m, a\<rangle> = zero))"
    if a_type[type_rule]: "a \<in>\<^sub>c A" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" for a n
  proof - 
    have "(IFF \<circ>\<^sub>c \<langle>
        eq_pred \<Omega> \<circ>\<^sub>c \<langle>is_first_zero \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, 
        AND \<circ>\<^sub>c \<langle>
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
          FORALL \<nat>\<^sub>c \<circ>\<^sub>c (
            IMPLIES \<circ>\<^sub>c \<langle>
              leq \<circ>\<^sub>c (successor \<times>\<^sub>f id \<nat>\<^sub>c), 
              eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>\<rangle>
            \<rangle>
          )\<^sup>\<sharp>
        \<rangle>
      \<rangle>) \<circ>\<^sub>c n = \<t>"
    proof (etcs_rule nat_induction)
      have "is_first_zero \<circ>\<^sub>c \<langle>a, zero\<rangle> = \<t> \<longleftrightarrow> (f \<circ>\<^sub>c \<langle>n, a\<rangle> = zero \<and> (\<forall>m. successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> zero \<longrightarrow> f \<circ>\<^sub>c \<langle>m, a\<rangle> = zero))"
      proof
        assume "is_first_zero \<circ>\<^sub>c \<langle>a,zero\<rangle> = \<t>"
        then have "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c is_first_zero'\<^sup>\<flat>) \<circ>\<^sub>c \<langle>a,zero\<rangle> = \<t>"
          unfolding is_first_zero_def .
        then have "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c eval_func (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>)) A \<circ>\<^sub>c (id A \<times>\<^sub>f is_first_zero')) \<circ>\<^sub>c \<langle>a,zero\<rangle> = \<t>"
          by (etcs_subst sym[OF inv_transpose_func_def3], simp)
        then have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c eval_func (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>)) A \<circ>\<^sub>c \<langle>a, is_first_zero' \<circ>\<^sub>c zero\<rangle> = \<t>"
          by (-, etcs_assocr_asm, typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        then have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c eval_func (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>)) A \<circ>\<^sub>c \<langle>a, ((zero \<bowtie>\<^sub>f left_coproj \<one> \<one>) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (f \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>, id A\<rangle>) \<times>\<^sub>f zero)\<^sup>\<sharp>\<rangle> = \<t>"
          unfolding is_first_zero'_zero zero_case_def .
        then have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c (eval_func (\<nat>\<^sub>c \<Coprod> (\<one> \<Coprod> \<one>)) A \<circ>\<^sub>c (id A \<times>\<^sub>f ((zero \<bowtie>\<^sub>f left_coproj \<one> \<one>) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (f \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>, id A\<rangle>) \<times>\<^sub>f zero)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle> = \<t>"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2)
        then have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c ((zero \<bowtie>\<^sub>f left_coproj \<one> \<one>) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (f \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>, id A\<rangle>) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>a, id \<one>\<rangle> = \<t>"
          by (typecheck_cfuncs, metis transpose_func_def)
        then have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c (zero \<bowtie>\<^sub>f left_coproj \<one> \<one>) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>(f \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>, id A\<rangle>) \<circ>\<^sub>c a, zero \<circ>\<^sub>c id \<one>\<rangle> = \<t>"
          by (-, etcs_assocr_asm, etcs_subst sym[OF cfunc_cross_prod_comp_cfunc_prod], simp)
        then have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c (zero \<bowtie>\<^sub>f left_coproj \<one> \<one>) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>zero, a\<rangle>, zero\<rangle> = \<t>"
          by (-, etcs_assocr_asm, typecheck_cfuncs, metis cart_prod_extract_right id_right_unit2)
        then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>zero, a\<rangle>, zero\<rangle> = \<t>"
        proof (subst ccontr) apply (insert true_false_only_truth_values, typecheck_cfuncs)
          thm ccontr[where P="eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>zero, a\<rangle>, zero\<rangle> = \<t>"]
          case True
          then show ?thesis .
        next
          case False
          then have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> \<t> \<amalg> \<f> \<circ>\<^sub>c (zero \<bowtie>\<^sub>f left_coproj \<one> \<one>) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>zero,a\<rangle>,zero\<rangle> = \<t> \<and> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>zero,a\<rangle>,zero\<rangle> = \<f>"
            using  apply (typecheck_cfuncs, auto)
          then show ?thesis 
        qed

      show "(IFF \<circ>\<^sub>c \<langle>
        eq_pred \<Omega> \<circ>\<^sub>c \<langle>is_first_zero \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, 
        AND \<circ>\<^sub>c \<langle>
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
          FORALL \<nat>\<^sub>c \<circ>\<^sub>c (
            IMPLIES \<circ>\<^sub>c \<langle>
              leq \<circ>\<^sub>c (successor \<times>\<^sub>f id \<nat>\<^sub>c), 
              eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>\<rangle>, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>\<rangle>
            \<rangle>
          )\<^sup>\<sharp>
        \<rangle>
      \<rangle>) \<circ>\<^sub>c zero = \<t>"
 