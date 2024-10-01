theory NN_is_countable
  imports Exp
begin

lemma RENAME_ME:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c"  
  assumes "a \<noteq> successor \<circ>\<^sub>c zero"
  shows "(b =  zero) = (a ^\<^sub>\<nat> b = successor \<circ>\<^sub>c zero)"
proof 
  show "b = zero \<Longrightarrow> a ^\<^sub>\<nat> b = successor \<circ>\<^sub>c zero"
    by (simp add: assms(1) exp_respects_Zero_Left)
  show "a ^\<^sub>\<nat> b = successor \<circ>\<^sub>c zero \<Longrightarrow> b = zero"
    by (metis assms exp_order_preserving' exp_respects_one_left succ_n_type zero_type)
qed

lemma exp_cancellative:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" 
  assumes "a \<noteq> zero"
  assumes "a \<noteq> successor \<circ>\<^sub>c zero"
  shows  "(a ^\<^sub>\<nat> b = a ^\<^sub>\<nat> c) = (b = c)"
proof(safe)
  assume "a ^\<^sub>\<nat> b = a ^\<^sub>\<nat> c"
  have "a ^\<^sub>\<nat> b \<noteq> zero"
    by (simp add: assms(1,2,4) nonzero_to_k_nonzero)

  show "b = c"
  proof(cases "leq \<circ>\<^sub>c \<langle>b, c\<rangle> = \<t>")
    assume "leq \<circ>\<^sub>c \<langle>b, c\<rangle> = \<t>"
    then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "k +\<^sub>\<nat> b = c"
      by (meson  assms(2, 3) leq_true_implies_exists)
    then have "a ^\<^sub>\<nat> b = (a ^\<^sub>\<nat> k) \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> b)"
      using \<open>a ^\<^sub>\<nat> b = a ^\<^sub>\<nat> c\<close> assms(1,2) exp_right_dist by force
    then have "successor \<circ>\<^sub>c zero = a ^\<^sub>\<nat> k"
      by (typecheck_cfuncs, metis \<open>a ^\<^sub>\<nat> b = a ^\<^sub>\<nat> c\<close> \<open>a ^\<^sub>\<nat> b \<noteq> zero\<close> assms(1,3) exp_closure l_mult_cancellative mult_commutative s0_is_right_id)
    then have "k = zero"
      using  assms(1,5) k_type RENAME_ME by force
    then show "b = c"
      using add_respects_zero_on_left assms(2) k_def by presburger
  next
    assume "leq \<circ>\<^sub>c \<langle>b,c\<rangle> \<noteq> \<t>"
    then have "leq \<circ>\<^sub>c \<langle>c,b\<rangle> = \<t>"
      using \<open>leq \<circ>\<^sub>c \<langle>b,c\<rangle> \<noteq> \<t>\<close> assms(2,3) lqe_connexity by blast
    then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "k +\<^sub>\<nat> c = b"
      by (meson  assms(2,3) leq_true_implies_exists)
    then have "a ^\<^sub>\<nat> b = (a ^\<^sub>\<nat> k) \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c)"
      using assms(1,3) exp_right_dist by force
    then have "successor \<circ>\<^sub>c zero = a ^\<^sub>\<nat> k"
      by (typecheck_cfuncs, metis \<open>a ^\<^sub>\<nat> b = a ^\<^sub>\<nat> c\<close> \<open>a ^\<^sub>\<nat> b \<noteq> zero\<close> assms(1) assms(3) exp_closure l_mult_cancellative mult_commutative s0_is_right_id)
    then have "k = zero"
      using  assms(1,5) k_type RENAME_ME by force
    then show "b = c"
      using add_respects_zero_on_left assms(3) k_def by force
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.6.10 in Halvorson.\<close>
lemma NxN_is_countable:
  "countable (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
proof -
  obtain \<phi> where \<phi>_def: " \<phi> = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub>, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>       ,
                                   exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub>, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>   \<rangle>"
            and \<phi>_type[type_rule]: "\<phi> : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (typecheck_cfuncs, blast)

  have \<phi>_injective: "injective \<phi>"
  proof(unfold injective_def, clarify)
    fix mn st
    assume mn_type: "mn \<in>\<^sub>c domain \<phi>"   
    assume st_type: "st \<in>\<^sub>c domain \<phi>"
    assume equals: "\<phi> \<circ>\<^sub>c mn = \<phi> \<circ>\<^sub>c st"
    

    have mn_type2: "mn \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
      using \<phi>_type cfunc_type_def mn_type by force
    have st_type2: "st \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
      using \<phi>_type cfunc_type_def st_type by force

    obtain m and n where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and mn_def: "mn = \<langle>m,n\<rangle>"
      using cart_prod_decomp mn_type2 by blast
    obtain s and t where s_type[type_rule]: "s \<in>\<^sub>c \<nat>\<^sub>c" and t_type[type_rule]: "t \<in>\<^sub>c \<nat>\<^sub>c" and st_def: "st = \<langle>s,t\<rangle>"
      using cart_prod_decomp st_type2 by blast

    have simplify: "\<And> u v. u \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> v \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> \<phi> \<circ>\<^sub>c \<langle>u,v\<rangle> = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> u) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> v)"
    proof(unfold \<phi>_def)
      fix u v 
      assume u_type[type_rule]: "u \<in>\<^sub>c \<nat>\<^sub>c"
      assume v_type[type_rule]: "v \<in>\<^sub>c \<nat>\<^sub>c"
      have "(mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                      exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>u,v\<rangle> = 
             mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c   \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                      exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>u,v\<rangle>"
        by (typecheck_cfuncs, smt (z3) comp_associative2)
      also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c   \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>u,v\<rangle>,
                      exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>u,v\<rangle>\<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c   (\<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c \<langle>u,v\<rangle>),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>u,v\<rangle>\<rangle> ,
                      exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c \<langle>u,v\<rangle>),right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>u,v\<rangle> \<rangle>  \<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c   (id \<one>),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>u,v\<rangle>\<rangle> ,
                      exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c (id \<one>),right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>u,v\<rangle>\<rangle>  \<rangle>"
        by (typecheck_cfuncs, metis (full_types)  one_unique_element)
      also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>u,v\<rangle>\<rangle> ,
                      exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>u,v\<rangle>\<rangle>  \<rangle>"
        by (typecheck_cfuncs, metis id_right_unit2)
      also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) , u \<rangle> ,
                      exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,v\<rangle>  \<rangle>"
        using left_cart_proj_cfunc_prod mn_def right_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
      also have "... =((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> u) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> v)"
        by (metis exp_def mult_def)
      then show "(mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c\<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  \<langle>u,v\<rangle> =
                 (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> u \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> v"
        by (metis calculation)
    qed

      
    have equals2: "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> m) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> n) = 
              ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> s) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> t)"
      using equals m_type mn_def n_type s_type simplify st_def t_type by force
    show "mn = st"
    proof(cases "leq \<circ>\<^sub>c \<langle>m, s\<rangle> = \<t>")
      assume "leq \<circ>\<^sub>c \<langle>m,s\<rangle> = \<t>"
      then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "k +\<^sub>\<nat> m = s"
        by (meson leq_true_implies_exists m_type s_type)
      then have "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> m) \<cdot>\<^sub>\<nat>  ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  n) = 
                ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c  zero)^\<^sub>\<nat> m) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c  zero)^\<^sub>\<nat> k) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  t)"
        by (typecheck_cfuncs, metis add_commutes equals2 exp_right_dist k_def)
      then have f1: "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  n) = 
                     ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c  zero)^\<^sub>\<nat> k) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  t)"
        by (typecheck_cfuncs, metis  exp_closure l_mult_cancellative m_type mult_associative nonzero_to_k_nonzero zero_is_not_successor)
      show ?thesis
      proof(cases "k = zero")
        assume "k = zero"
        then have "n=t"
          by (metis exp_cancellative exp_closure exp_respects_Zero_Left f1 n_type s0_is_left_id succ_inject succ_n_type t_type zero_is_not_successor zero_type)
        then show ?thesis
          using \<open>k = zero\<close> add_respects_zero_on_left k_def m_type mn_def st_def by auto
      next
        assume "k \<noteq> zero"
        then have even: "is_even \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  n) = \<t>"
          using exp_closure exp_def f1 k_type mult_evens_is_even2 powers_of_two_are_even succ_n_type t_type zero_type by force
        have "is_odd \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  n) = \<t>"
          by (metis  exp_def n_type powers_of_three_are_odd)
        then have False
          using even exp_closure n_type not_even_and_odd succ_n_type zero_type by auto
        then show ?thesis
          by simp
      qed
    next
      assume "leq \<circ>\<^sub>c \<langle>m,s\<rangle> \<noteq> \<t>"
      then have "leq \<circ>\<^sub>c \<langle>s,m\<rangle> = \<t>"
        using lqe_connexity m_type s_type by blast
      then  obtain p where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and p_def: "m = p +\<^sub>\<nat> s"
        using leq_true_implies_exists m_type s_type by blast
      then have "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> p) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> s) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  n) = 
                ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c  zero)^\<^sub>\<nat> s) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  t)"
        by (typecheck_cfuncs, metis equals2 exp_right_dist p_def)
      then have "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> s) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> p) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  n) = 
                ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c  zero)^\<^sub>\<nat> s) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  t)"
        by (typecheck_cfuncs, metis mult_commutative)
      then have f1: "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat> p) \<cdot>\<^sub>\<nat>  ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  n) =
                                                               ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  t)"
        by (typecheck_cfuncs, metis  exp_closure l_mult_cancellative mult_associative nonzero_to_k_nonzero s_type zero_is_not_successor)
      show ?thesis
      proof(cases "p = zero")
        assume "p = zero"
        then have "n = t"
          using \<open>leq \<circ>\<^sub>c \<langle>m,s\<rangle> \<noteq> \<t>\<close> \<open>leq \<circ>\<^sub>c \<langle>s,m\<rangle> = \<t>\<close> add_respects_zero_on_left p_def s_type by auto
        then show ?thesis
          by (simp add: \<open>p = zero\<close> add_respects_zero_on_left mn_def p_def s_type st_def)
      next
        assume "p \<noteq> zero"
        then have even: "is_even \<circ>\<^sub>c  ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  t) = \<t>"
          by (metis exp_closure exp_def f1 mult_evens_is_even2 n_type p_type powers_of_two_are_even succ_n_type zero_type)
        have "is_odd \<circ>\<^sub>c  ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)^\<^sub>\<nat>  t) = \<t>"
          by (typecheck_cfuncs, metis exp_def  powers_of_three_are_odd)
        then have False
          using even exp_closure not_even_and_odd succ_n_type t_type zero_type by auto
        then show ?thesis
          by simp
      qed
    qed
  qed
  then show ?thesis
    using \<phi>_type countable_def injective_imp_monomorphism by blast
qed

end