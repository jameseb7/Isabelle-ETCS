theory ETCS_Wellordering
  imports ETCS_Axioms ETCS_Comparison
begin

theorem well_ordering_principle:
  assumes "nonempty A" "(A, m) \<subseteq>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists> a. a \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<and> (\<forall> b. b \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<longrightarrow> (leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t>))" (* a \<le>\<^sub>\<nat> b*)
proof(cases "zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m)")
  show "zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<Longrightarrow> \<exists>a. a \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<and> (\<forall>b. b \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<longrightarrow> leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t>)"
    using relative_member_def zero_is_smallest by blast
next
  assume no_zero: " \<not> zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m)"
  obtain \<chi>\<^sub>A where \<chi>\<^sub>A_def: "\<chi>\<^sub>A = characteristic_func m"
    by simp
  have \<chi>\<^sub>A_type[type_rule]: "\<chi>\<^sub>A : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    using assms unfolding \<chi>\<^sub>A_def subobject_of_def2 by (auto, typecheck_cfuncs)

  obtain q where q_def: "q = (right_coproj \<Omega> \<nat>\<^sub>c) \<circ>\<^sub>c zero"    (*I redefined q because we only need the special case when 0 is not an element of the set!*)
    by simp
  have q_type[type_rule]: "q : one \<rightarrow> \<Omega> \<Coprod> \<nat>\<^sub>c"
    unfolding q_def by typecheck_cfuncs

  obtain f where f_def: "f = (left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<amalg>
    (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>) \<bowtie>\<^sub>f left_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c
  dist_prod_coprod_inv \<nat>\<^sub>c one one \<circ>\<^sub>c \<langle>successor, case_bool \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c successor\<rangle>)"
    by simp
  have f_type[type_rule]: "f : \<Omega> \<Coprod> \<nat>\<^sub>c \<rightarrow> \<Omega> \<Coprod> \<nat>\<^sub>c"
    unfolding f_def by typecheck_cfuncs

  obtain u where u_type[type_rule]: "u: \<nat>\<^sub>c \<rightarrow> \<Omega> \<Coprod> \<nat>\<^sub>c" 
            and  u_zero: "u \<circ>\<^sub>c zero = q" 
            and  u_successor: "f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    using natural_number_object_property2 by (typecheck_cfuncs, blast)

  obtain q' where q'_def: "q' = \<langle>\<f>, zero\<rangle>"   (*I redefined q' because we only need the special case when 0 is not an element of the set!*)
    by simp
  have q'_type[type_rule]: "q' : one \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding q'_def by typecheck_cfuncs


  
  obtain f' where f'_def: "f' = \<langle>
        AND \<circ>\<^sub>c \<langle>left_cart_proj \<Omega> \<nat>\<^sub>c, \<chi>\<^sub>A \<circ>\<^sub>c successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c\<rangle>, 
        successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c
      \<rangle>"
    by simp
  have f'_type[type_rule]: "f' : \<Omega> \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding f'_def by typecheck_cfuncs

  obtain v1 where v1_def: "v1 = \<langle>FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>, id \<nat>\<^sub>c\<rangle>"
    by simp
  have v1_type[type_rule]: "v1 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding v1_def by typecheck_cfuncs

   
  have v10_eqs_q': "v1 \<circ>\<^sub>c zero = q'"
  proof - 
    have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = \<f>"
      apply typecheck_cfuncs


  obtain v2 where v2_def: "v2 = \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u, right_coproj \<Omega> \<nat>\<^sub>c\<rangle>, id \<nat>\<^sub>c \<rangle>"
    by simp
  have v2_type[type_rule]: "v2 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding v2_def by typecheck_cfuncs

  have "v1 = v2"
  proof (rule natural_number_object_func_unique[where X="\<Omega> \<times>\<^sub>c \<nat>\<^sub>c", where f=f'])
    show "v1 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" "v2 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" "f' : \<Omega> \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
      by (typecheck_cfuncs, presburger)

    show "v1 \<circ>\<^sub>c zero = v2 \<circ>\<^sub>c zero"
      sorry

    show "v1 \<circ>\<^sub>c successor = f' \<circ>\<^sub>c v1"
      sorry

    show "v2 \<circ>\<^sub>c successor = f' \<circ>\<^sub>c v2"
      sorry
  qed
  then have "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> u \<circ>\<^sub>c n = left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n \<equiv> (\<forall>n'. n' \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> n' \<le>\<^sub>\<nat> n \<longrightarrow> \<not> n' \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m))"
  proof -
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"

    have "\<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u,right_coproj \<Omega> \<nat>\<^sub>c\<rangle>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<equiv> u \<circ>\<^sub>c n = left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n"
      sorry

    have "\<langle>FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> 
          \<equiv> 
        (\<forall>n'. n' \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> n' \<le>\<^sub>\<nat> n \<longrightarrow> \<not> n' \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m))"
      sorry

    assume "v1 = v2"
    then have "\<langle>FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> 
          \<equiv>
        \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u,right_coproj \<Omega> \<nat>\<^sub>c\<rangle>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      unfolding v1_def v2_def by auto
    
end