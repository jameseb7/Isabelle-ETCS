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
