theory ETCS_Comparison
  imports ETCS_Quantifier ETCS_Add 
begin

definition leq :: "cfunc" where
  "leq = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"

definition leq_infix :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" (infix "\<le>\<^sub>\<nat>" 50) where
  "a \<le>\<^sub>\<nat> b = (leq \<circ>\<^sub>c \<langle>a, b\<rangle> = \<t>)"

lemma leq_type[type_rule]:
  "leq : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
  unfolding leq_def by typecheck_cfuncs

lemma leq_true_implies_exists:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes leq_true: "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>"
  shows "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> m = n"
proof -
  have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>"
    using m_type n_type leq_true comp_associative2 unfolding leq_def by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>))\<^sup>\<sharp> = \<t>"
    using m_type n_type sharp_comp by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c id (\<nat>\<^sub>c \<times>\<^sub>c one))\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, simp add: id_right_unit2)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c one, \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, metis cfunc_cross_prod_def id_cross_prod
        id_domain id_left_unit2 right_cart_proj_type terminal_func_unique)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, simp add: cfunc_prod_comp id_left_unit2 terminal_func_comp)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          ((id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c
          left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, smt cfunc_type_def comp_associative domain_comp)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
     using m_type n_type EXISTS_true_implies_exists_true by (typecheck_cfuncs, blast)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c ((add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c (associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>k, \<langle>m, n\<rangle>\<rangle> = \<t>"
    using m_type n_type cart_prod_extract_left by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>k, m\<rangle>, n\<rangle> = \<t>"
    using associate_left_ap m_type n_type by auto
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>(add2  \<circ>\<^sub>c \<langle>k, m\<rangle>), (id \<nat>\<^sub>c \<circ>\<^sub>c n)\<rangle> = \<t>"
  proof (rule ex_forward, auto)
    fix k
    assume k_type: "k \<in>\<^sub>c \<nat>\<^sub>c"
    assume "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>k,m\<rangle>,n\<rangle> = \<t>"
    then show "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>k,m\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle> = \<t>"
      using k_type assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  qed
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>k, m\<rangle>, n\<rangle> = \<t>"
    using id_left_unit2 n_type by auto
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> add2 \<circ>\<^sub>c \<langle>k, m\<rangle> = n"
    by (metis add_def add_type eq_pred_iff_eq m_type n_type)
  then show "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> m = n"
    by (simp add: add_def)
qed

lemma exists_implies_leq_true:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes leq_eqn: "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> m = n"
  shows "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>"
proof - 
  have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> add2 \<circ>\<^sub>c \<langle>k, m\<rangle> = n"
    using add_def leq_eqn by auto
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>k, m\<rangle>, n\<rangle> = \<t>"
    using eq_pred_iff_eq n_type by auto
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>(add2  \<circ>\<^sub>c \<langle>k, m\<rangle>), (id \<nat>\<^sub>c \<circ>\<^sub>c n)\<rangle> = \<t>"
    using id_left_unit2 n_type by auto
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>k, m\<rangle>, n\<rangle> = \<t>"
     proof (rule ex_forward, auto)
       fix k ka
       assume k_type: "k \<in>\<^sub>c \<nat>\<^sub>c"
       assume  "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>k,m\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle> = \<t>"
       then show "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>k,m\<rangle>,n\<rangle> = \<t>"
         using k_type assms by (typecheck_cfuncs, simp add:  cfunc_cross_prod_comp_cfunc_prod)
     qed
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>k, \<langle>m, n\<rangle>\<rangle> = \<t>"
    using associate_left_ap m_type n_type by auto
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c k = \<t>"
    using m_type n_type cart_prod_extract_left by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c (associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c ((add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> 
      (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c
          left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type exists_true_implies_EXISTS_true by (typecheck_cfuncs, blast)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_right_unit2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c one, \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, smt  cfunc_prod_comp id_left_unit2 terminal_func_comp terminal_func_type)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c id (\<nat>\<^sub>c \<times>\<^sub>c one))\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, metis  cfunc_cross_prod_def id_cross_prod id_domain id_left_unit2 left_cart_proj_type right_cart_proj_type terminal_func_unique)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c 
      ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>))\<^sup>\<sharp> = \<t>"
    using m_type n_type id_right_unit2 by (typecheck_cfuncs, force)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>"
    using m_type n_type by (typecheck_cfuncs, simp add:  sharp_comp)
  then show "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>"
    using m_type n_type comp_associative2 unfolding leq_def by (typecheck_cfuncs, auto)
qed

lemma add_monotonic:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c" and u_type: "u \<in>\<^sub>c \<nat>\<^sub>c" and v_type: "v \<in>\<^sub>c \<nat>\<^sub>c"
  assumes m_leq_n: "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>" 
  assumes u_leq_v: "leq \<circ>\<^sub>c \<langle>u, v\<rangle> = \<t>" 
  shows "leq \<circ>\<^sub>c \<langle>m +\<^sub>\<nat> u, n +\<^sub>\<nat> v\<rangle> = \<t>" 
proof - 
  have m_leq_n_Eqn: "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> m = n"
    by (simp add: leq_true_implies_exists m_leq_n m_type n_type)
  have u_leq_v_Eqn: "\<exists> j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> u = v"
    by (simp add: leq_true_implies_exists u_leq_v u_type v_type)
  have combined_Eqns: "\<exists> l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> l +\<^sub>\<nat> (m +\<^sub>\<nat> u) = n +\<^sub>\<nat> v"
    by (smt add_associates add_commutes add_type m_leq_n_Eqn m_type u_leq_v_Eqn u_type)
  show "leq \<circ>\<^sub>c \<langle>m +\<^sub>\<nat> u, n +\<^sub>\<nat> v\<rangle> = \<t>"
    by (metis add_type combined_Eqns exists_implies_leq_true m_type u_type)
qed

lemma leq_transitivity:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c" and p_type: "p \<in>\<^sub>c \<nat>\<^sub>c"
  assumes m_leq_n: "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>" 
  assumes n_leq_p: "leq \<circ>\<^sub>c \<langle>n, p\<rangle> = \<t>" 
  shows "leq \<circ>\<^sub>c \<langle>m, p\<rangle> = \<t>" 
proof - 
   have m_leq_n_Eqn: "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> m = n"
     by (simp add: leq_true_implies_exists m_leq_n m_type n_type)
   obtain k where k_num: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> m = n"
     using m_leq_n_Eqn by blast
   have n_leq_p_Eqn: "\<exists> j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> n = p"
     by (simp add: leq_true_implies_exists n_leq_p n_type p_type)
   obtain j where j_num: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> n = p"
     using n_leq_p_Eqn by blast
   have combined_Eqn: "(k +\<^sub>\<nat> j) +\<^sub>\<nat> m = p"
     using add_associates add_commutes j_num k_num m_type by auto
   have combined_Exists: "\<exists> l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> l +\<^sub>\<nat> m = p"
     using add_type combined_Eqn j_num k_num by blast
   then show "leq \<circ>\<^sub>c \<langle>m, p\<rangle> = \<t>"
     by (simp add: exists_implies_leq_true m_type p_type)
 qed

  



lemma lqe_antisymmetry:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes m_leq_n: "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>" 
  assumes n_leq_m: "leq \<circ>\<^sub>c \<langle>n, m\<rangle> = \<t>" 
  shows "m = n"
proof - 
  have k_exists: "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> n = m"
    by (simp add: leq_true_implies_exists m_type n_leq_m n_type)
  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> n = m"
    using k_exists by blast
  have j_exists: "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> m = n"
    by (simp add: leq_true_implies_exists m_leq_n m_type n_type)
  obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> m = n"
    using j_exists by blast
  have "zero +\<^sub>\<nat> m = k +\<^sub>\<nat> n"
    by (simp add: add_respects_zero_on_left k_def m_type)
  also have "... = (k +\<^sub>\<nat> j) +\<^sub>\<nat> m"
    using add_associates j_def k_def m_type by blast
  then have zero_is_kplsj: "zero = k +\<^sub>\<nat> j"
    by (metis  add_cancellative add_type calculation j_def k_def n_type zero_type)
  have "k = zero"
  proof(rule ccontr)
    assume bwoc: "k \<noteq> zero"
    have k_is_succ: "\<exists>a. (a \<in>\<^sub>c \<nat>\<^sub>c \<and> k = successor \<circ>\<^sub>c a)"
      by (simp add: bwoc k_def nonzero_is_succ)
    obtain a where a_def: "a \<in>\<^sub>c \<nat>\<^sub>c \<and> k = successor \<circ>\<^sub>c a"
      using k_is_succ by blast
    have "zero = successor \<circ>\<^sub>c (a +\<^sub>\<nat> j)"
      by (simp add: a_def add_respects_succ3 j_def zero_is_kplsj)
    then show False
      using a_def add_type  j_def zero_is_not_successor by auto
  qed
  then show ?thesis
    using add_respects_zero_on_left k_def n_type by blast
qed

lemma zero_is_smallest:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "leq \<circ>\<^sub>c\<langle>zero ,n\<rangle> = \<t>"
  using add_respects_zero_on_right assms exists_implies_leq_true zero_type by blast

lemma lqe_connexity:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(leq \<circ>\<^sub>c \<langle>n, m\<rangle> = \<t>) \<or> (leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>)"
proof-

  have main_result: "(OR \<circ>\<^sub>c \<langle>
leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
\<rangle>)\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>"
  proof(rule natural_number_object_func_unique[where X="\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>", where f = "id (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>)" ])
    show type_fact1: "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
      by (meson OR_type cfunc_prod_type comp_type left_cart_proj_type leq_type right_cart_proj_type transpose_func_type)
    show type_fact2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
      using comp_type terminal_func_type transpose_func_type true_func_type by blast
    have type_fact3: "id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero : \<nat>\<^sub>c\<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
      using cfunc_cross_prod_type comp_type id_type type_fact2 zero_type by auto
    show type_fact3: "id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) : \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup> \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
      by (simp add: id_type)
    show eqn_1: "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
            (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule same_evals_equal[where Z = "one", where X=\<Omega>, where A="\<nat>\<^sub>c"])
      show type_fact5: "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                   leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
        by (meson comp_type type_fact1 zero_type)
      show type_fact6: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
        by (meson comp_type type_fact2 zero_type)
      show eqn_2: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
            eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(rule one_separator[where X="\<nat>\<^sub>c\<times>\<^sub>c one", where Y = \<Omega>])
        show type_fact7: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f 
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                 leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
            zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
          using flat_type inv_transpose_func_def2 type_fact5 by force
        show type_fact8: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
          using flat_type inv_transpose_func_def2 type_fact6 by force
        show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
             (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c
             \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
              leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
           (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
          have x_form: "\<exists>j. (j\<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>j,id one\<rangle>)"
            by (metis (no_types) x_type cart_prod_decomp id_type one_unique_element)
          obtain j where j_def: "j\<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>j,id one\<rangle>"
            using x_form by blast
          have eqn_RHS: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = \<t>"
          proof - 
            have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = 
                  (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c x"
              by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition x_type)
            also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>j,id one\<rangle>"
              by (typecheck_cfuncs, simp add: j_def transpose_func_def)
            also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c j,zero \<circ>\<^sub>c id one\<rangle>"
              using cfunc_cross_prod_comp_cfunc_prod j_def by (typecheck_cfuncs, force)
            also have "... = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c j,zero \<circ>\<^sub>c id one\<rangle>)"
              by (typecheck_cfuncs, metis comp_associative2 j_def)
            also have "... =  \<t>"
              by (typecheck_cfuncs, metis id_right_unit2 j_def terminal_func_unique)
            then show ?thesis
              by (simp add: calculation)
          qed
          
          have eqn_LHS: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
            (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = \<t>"
            proof - 
              have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
            (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = 
                    (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
            (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c
                 (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c x"
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition x_type)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c
                 (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c x"
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative transpose_func_def x_type)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c
                 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c j,zero \<circ>\<^sub>c id one\<rangle>"
                using cfunc_cross_prod_comp_cfunc_prod j_def by (typecheck_cfuncs, auto)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c
                 \<langle>j,zero\<rangle>"
                using id_left_unit2 id_right_unit2 j_def zero_type by force
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle>  ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle> \<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle> \<rangle>\<rangle>"
                by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 j_def)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>j ,zero \<rangle>, leq \<circ>\<^sub>c\<langle>zero ,j \<rangle>\<rangle>"
                by (typecheck_cfuncs, metis j_def left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>j ,zero \<rangle>, \<t>\<rangle>"
                by (simp add: j_def zero_is_smallest)
              also have "... = \<t>"
                by (typecheck_cfuncs, simp add: OR_true_right_is_true j_def)
              then show ?thesis
                by (simp add: calculation)
            qed
            show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
            (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
              by (simp add: eqn_LHS eqn_RHS)
          qed
        qed
      qed
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>"
      proof(rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = \<Omega>,where A = "\<nat>\<^sub>c"])
        show type_fact9: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
          by (meson comp_type successor_type type_fact2)
        show type_fact10: "id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
          by (meson comp_type type_fact2 type_fact3)
        show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>"
        proof(rule one_separator[where X="\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c", where Y = \<Omega>])
          show type_fact11: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
            using type_fact9 flat_type inv_transpose_func_def2 by auto
          show type_fact12: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
            using flat_type inv_transpose_func_def2 type_fact10 by auto
          show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  x =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>cx"
          proof -
            fix x
            assume x_def: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"

            
            
            
            show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  x =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>cx"
            

            proof - 
              have calc1: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  x =
                    (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  x"
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition x_def)     
              also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  x"
                using transpose_func_def by (typecheck_cfuncs, auto)
              also have "... = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  x)"
                by (typecheck_cfuncs, metis cfunc_type_def comp_associative x_def)
              also have "... = \<t>"
                by (typecheck_cfuncs, metis id_right_unit2 id_type terminal_func_unique x_def)
              then have eqsT1: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  x =  \<t>"
                by (simp add: calculation)
              have calc2: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>cx = \<t>"
              proof -
                have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>cx = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>) \<circ>\<^sub>cx"
                  by (typecheck_cfuncs, simp add: id_left_unit2 transpose_func_def)
                also have "... = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x)"
                  using comp_associative2 x_def by (typecheck_cfuncs, auto)
                also have "... = \<t>"
                  by (metis id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type true_func_type x_def)
                then show ?thesis
                  using calculation by auto
              qed
              then have eqsT2: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>cx =  \<t>"
                by (simp add:  calc2)
              then show ?thesis
                using eqsT1 by auto
            qed
          qed
        qed
      qed

      

      show "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                   leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor =
    id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                          leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
        proof(rule same_evals_equal[where Z="\<nat>\<^sub>c", where X=\<Omega>, where A ="\<nat>\<^sub>c" ])
          show type_fact13: "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            using comp_type successor_type type_fact1 by blast

          show type_fact14: "id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
    (OR \<circ>\<^sub>c
     \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
      leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            using comp_type type_fact1 type_fact3 by auto

          show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
            leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor =
    eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
    (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
           leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
          proof(rule one_separator[where X = "\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c", where Y = \<Omega>])
            show type_fact15: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
            leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
              using flat_type inv_transpose_func_def2 type_fact13 by force
            show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
    (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
           leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
              using flat_type inv_transpose_func_def2 type_fact14 by force
            show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          successor) \<circ>\<^sub>c x =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            proof -
              fix x 
              assume x_is: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
              have x_cart: "\<exists>n m. n \<in>\<^sub>c \<nat>\<^sub>c \<and> m \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>n,m\<rangle>"
                using cart_prod_decomp x_is by blast
              obtain n where n_def: "\<exists>m. n \<in>\<^sub>c \<nat>\<^sub>c \<and> m \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>n,m\<rangle>"
                using x_cart by blast
              obtain m where m_def: "n \<in>\<^sub>c \<nat>\<^sub>c \<and> m \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>n,m\<rangle>"
                using n_def by blast

              
              



              have nsm_type: "\<langle>n,successor \<circ>\<^sub>c m\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
                by (simp add: cfunc_prod_type m_def succ_n_type)
              have smn_type: "\<langle>successor \<circ>\<^sub>c m,n\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
                by (simp add: cfunc_prod_type m_def succ_n_type)

              have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          successor) \<circ>\<^sub>c \<langle>n,m\<rangle> =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle>"
              proof(cases "leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<f> \<and>  leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>", auto)  
                assume "leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<f>"
                assume "leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>"

                have "(leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> = \<f>)  \<and> (leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,n\<rangle> = \<f>)"
                 proof(rule ccontr,auto)
                   assume  "leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> \<noteq> \<f>"
                   then have "leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> = \<t>"
                     using  comp_type leq_type nsm_type true_false_only_truth_values by blast
                   then have j_exists: "\<exists> j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> n +\<^sub>\<nat> j = successor \<circ>\<^sub>c m"
                     by (metis add_commutes leq_true_implies_exists m_def succ_n_type)
                   obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> n +\<^sub>\<nat> j = successor \<circ>\<^sub>c m"
                     using j_exists by blast
                   have "n +\<^sub>\<nat> j =  m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
                     by (simp add: add_respects_succ1 add_respects_zero_on_right j_def m_def zero_type)
                   have "leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
                   proof (cases "j = zero")
                     assume "j = zero"  
                     have "n = m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
                       using \<open>j = zero\<close> \<open>n +\<^sub>\<nat> j = m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)\<close> add_respects_zero_on_right m_def by auto
                     then have "n = (successor \<circ>\<^sub>c zero) +\<^sub>\<nat> m"
                       using add_commutes m_def succ_n_type zero_type by blast
                     then have "\<exists>p. p \<in>\<^sub>c \<nat>\<^sub>c \<and> n = p +\<^sub>\<nat> m"
                       using succ_n_type zero_type by blast
                     then show ?thesis
                       using exists_implies_leq_true m_def by blast
                   next
                     assume "j \<noteq> zero"
                     then have "\<exists> p. (p \<in>\<^sub>c \<nat>\<^sub>c \<and> j = successor \<circ>\<^sub>c p) "
                       using  j_def nonzero_is_succ by auto
                     then obtain p where p_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> j = successor \<circ>\<^sub>c p"
                       by blast
                     have "successor \<circ>\<^sub>c m = n +\<^sub>\<nat> j"
                       by (simp add: j_def)
                     also have "... = n +\<^sub>\<nat> (successor \<circ>\<^sub>c p)"
                       by (simp add: p_def)
                     also have "... = successor \<circ>\<^sub>c (n +\<^sub>\<nat> p)"
                       by (simp add: add_respects_succ1 m_def p_def)
                     then  have "successor \<circ>\<^sub>c m = successor \<circ>\<^sub>c (n +\<^sub>\<nat> p)"
                       using calculation by auto
                     then have "m = n +\<^sub>\<nat> p"
                       by (simp add: add_type m_def p_def succ_inject)
                     then have "... = p +\<^sub>\<nat> n"
                       using add_commutes m_def p_def by blast
                     then have "\<exists>p. (p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = p +\<^sub>\<nat> n)"
                       using \<open>m = n +\<^sub>\<nat> p\<close> p_def by blast
                     then show ?thesis
                       using \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>\<close> \<open>leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<f>\<close> exists_implies_leq_true m_def by force
                   qed
                   then show False
                     using \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>\<close> true_false_distinct by auto
                 
                 next
                   assume "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,n\<rangle> \<noteq> \<f>"
                   then have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,n\<rangle> = \<t>"
                     using  comp_type leq_type smn_type true_false_only_truth_values by blast
                   then show False
                     by (metis \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>\<close>  add_respects_succ2 exists_implies_leq_true leq_true_implies_exists m_def succ_n_type true_false_distinct)
                 qed
                 




              have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          successor) \<circ>\<^sub>c \<langle>n,m\<rangle>= 
                  (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                            (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
                           (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition m_def)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                           (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>" 
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative m_def transpose_func_def)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                            \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n,successor \<circ>\<^sub>c m\<rangle>" 
                  using cfunc_cross_prod_comp_cfunc_prod m_def by (typecheck_cfuncs, auto)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                            \<langle>n,successor \<circ>\<^sub>c m\<rangle>"
                  using id_left_unit2 m_def by auto 
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle>  ,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>   ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>  \<rangle>  \<rangle>"
                  using nsm_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
               also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c m\<rangle>  ,  leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m  ,n  \<rangle>\<rangle>"
                 using left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod succ_n_type by auto     
               also have "... =  \<f>"
                 by (simp add: OR_false_false_is_false \<open>leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> = \<f> \<and> leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,n\<rangle> = \<f>\<close>)

               have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle> = \<f>"
               proof -
                 have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
                  (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                      leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle> = 
                    OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                      leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>n,m\<rangle>"
                   by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 m_def transpose_func_def x_is)
                 also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>  ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle> \<rangle>,
                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle> \<rangle>\<rangle> "
                   by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2 m_def x_is)
                 also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n  ,m  \<rangle>, leq \<circ>\<^sub>c \<langle>m ,n \<rangle>\<rangle> "
                    by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod)                             
                 also have "... =  \<f>"
                    by (simp add: OR_false_false_is_false \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<f>\<close> \<open>leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<f>\<close>)
                 then show ?thesis
                   using calculation by auto
               qed

               then show ?thesis
                 using \<open>OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>,leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,n\<rangle>\<rangle> = \<f>\<close> calculation by presburger
              
              next
                assume "leq \<circ>\<^sub>c \<langle>n,m\<rangle> \<noteq> \<f>"
                then have "leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>"
                  using  m_def true_false_only_truth_values by (typecheck_cfuncs, blast)

                then have "leq \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c m\<rangle> = \<t>"
                  by (metis add_respects_succ3 exists_implies_leq_true leq_true_implies_exists m_def succ_n_type)
                
                
                have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          successor) \<circ>\<^sub>c \<langle>n,m\<rangle>= 
                  (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                            (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
                           (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition m_def)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                           (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>" 
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative m_def transpose_func_def)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                            \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n,successor \<circ>\<^sub>c m\<rangle>" 
                  using cfunc_cross_prod_comp_cfunc_prod m_def by (typecheck_cfuncs, auto)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                            \<langle>n,successor \<circ>\<^sub>c m\<rangle>"
                  using id_left_unit2 m_def by auto 
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle>  ,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>   ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>  \<rangle>  \<rangle>"
                  using nsm_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
               also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c m\<rangle>  ,  leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m  ,n  \<rangle>\<rangle>"
                 using left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod succ_n_type by auto     
               also have "... =  \<t>"
                 using OR_true_left_is_true \<open>leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> = \<t>\<close> comp_type leq_type smn_type by auto

              have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>"
              proof -
               have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle> = 
                OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>n,m\<rangle>"
                 by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 m_def transpose_func_def x_is)
               also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>  ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle> \<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle> \<rangle>\<rangle> "
                 by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2 m_def x_is)
               also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n  ,m  \<rangle>, leq \<circ>\<^sub>c \<langle>m ,n \<rangle>\<rangle> "
                 by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod)                             
               also have "... =  \<t>"
                 by (typecheck_cfuncs, simp add: OR_true_left_is_true \<open>leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>\<close> m_def)

                then show ?thesis
                  by (simp add: \<open>(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle> = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>n,m\<rangle>\<close> \<open>OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>\<rangle> = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n,m\<rangle>,leq \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>\<close> \<open>OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>n,m\<rangle> = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>\<rangle>\<close> \<open>OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>,leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,n\<rangle>\<rangle> = \<t>\<close> calculation)

              next
                assume "leq \<circ>\<^sub>c \<langle>m,n\<rangle> \<noteq> \<f>"
                then have "leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
                  using  m_def true_false_only_truth_values by (typecheck_cfuncs, blast)

   then have "leq \<circ>\<^sub>c \<langle>m ,successor \<circ>\<^sub>c n\<rangle> = \<t>"
                  by (metis add_respects_succ3 exists_implies_leq_true leq_true_implies_exists m_def succ_n_type)
                
                
                have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          successor) \<circ>\<^sub>c \<langle>n,m\<rangle>= 
                  (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                            (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
                           (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition m_def)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                           (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>" 
                by (typecheck_cfuncs, smt cfunc_type_def comp_associative m_def transpose_func_def)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                            \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n,successor \<circ>\<^sub>c m\<rangle>" 
                  using cfunc_cross_prod_comp_cfunc_prod m_def by (typecheck_cfuncs, auto)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<circ>\<^sub>c
                            \<langle>n,successor \<circ>\<^sub>c m\<rangle>"
                  using id_left_unit2 m_def by auto 
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle>  ,
                                    leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>   ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>  \<rangle>  \<rangle>"
                  using nsm_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
               also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c m\<rangle>  ,  leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m  ,n  \<rangle>\<rangle>"
                 using left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod succ_n_type by auto     
               also have "... =  \<t>"
                 using OR_true_left_is_true \<open>leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> = \<t>\<close> comp_type leq_type smn_type by auto

              have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>"
              proof -
                have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle> = 
                OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>n,m\<rangle>"
                 by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 m_def transpose_func_def x_is)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle>  ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle> \<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,m\<rangle> \<rangle>\<rangle> "
                 by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2 m_def x_is)
                also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n  ,m  \<rangle>, leq \<circ>\<^sub>c \<langle>m ,n \<rangle>\<rangle> "
                  by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod)                             
                also have "... =  \<t>"
                  using OR_true_right_is_true \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>\<close> comp_type leq_type m_def x_is by auto
                then show ?thesis
                  using calculation by auto
              qed
            qed
            then show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
     id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
     (OR \<circ>\<^sub>c
      \<langle>leq \<circ>\<^sub>c
       \<langle>left_cart_proj \<nat>\<^sub>c
         \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
     successor) \<circ>\<^sub>c
    \<langle>n,m\<rangle> =
    (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
     id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
     id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
     (OR \<circ>\<^sub>c
      \<langle>leq \<circ>\<^sub>c
       \<langle>left_cart_proj \<nat>\<^sub>c
         \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
    \<langle>n,m\<rangle>"
              by (simp add: \<open>OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>,leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,n\<rangle>\<rangle> = \<t>\<close> calculation)
          next
            assume "leq \<circ>\<^sub>c \<langle>m,n\<rangle> \<noteq> \<f>"
            then have m_leq_n: "leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
              by (meson cfunc_prod_type comp_type leq_type m_def true_false_only_truth_values)
            then have main_inequality: "OR \<circ>\<^sub>c \<langle>  leq \<circ>\<^sub>c \<langle>n, successor \<circ>\<^sub>c m\<rangle>, leq \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c m, n\<rangle>\<rangle>= \<t>"
            proof(cases "m = n")
              assume "m = n"
              then have "leq \<circ>\<^sub>c \<langle>n, successor \<circ>\<^sub>c m\<rangle> = \<t>"
                by (typecheck_cfuncs, metis add_respects_succ3 add_respects_zero_on_left exists_implies_leq_true m_def succ_n_type zero_type)
              then show ?thesis
                using OR_true_left_is_true comp_type leq_type smn_type by presburger
            next 
              assume "m \<noteq> n"
              then obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> n = m +\<^sub>\<nat> k \<and> k \<noteq> zero"
                by (metis m_leq_n add_commutes add_respects_zero_on_right leq_true_implies_exists m_def)
              then have "leq \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c m, n\<rangle> = \<t>"
              proof - 
                have "leq \<circ>\<^sub>c  \<langle>m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero), n \<rangle> = \<t>"
                  by (smt (verit, ccfv_SIG) add_commutes add_respects_succ3 add_respects_zero_on_left exists_implies_leq_true k_def m_def nonzero_is_succ succ_n_type zero_type)
                then show ?thesis
                  by (simp add: add_respects_succ1 add_respects_zero_on_right m_def zero_type)
              qed
              then show ?thesis
                using OR_true_right_is_true comp_type leq_type nsm_type by presburger
            qed
            




             show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
     id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
     (OR \<circ>\<^sub>c
      \<langle>leq \<circ>\<^sub>c
       \<langle>left_cart_proj \<nat>\<^sub>c
         \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
     successor) \<circ>\<^sub>c
    \<langle>n,m\<rangle> = 
    (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
     id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
     id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
     (OR \<circ>\<^sub>c
      \<langle>leq \<circ>\<^sub>c
       \<langle>left_cart_proj \<nat>\<^sub>c
         \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
    \<langle>n,m\<rangle>"
             
          proof - 
                            have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
                   id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                   (OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
                   successor) \<circ>\<^sub>c
                  \<langle>n,m\<rangle> = ((eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
                   id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                   (OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
                  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c
                  \<langle>n,m\<rangle>"
                              using sharp_comp transpose_func_def by (typecheck_cfuncs,force)
                            also have "... = (OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<circ>\<^sub>c
                  ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c
                  \<langle>n,m\<rangle>)"
                              by (typecheck_cfuncs, smt (verit, best) comp_associative2 m_def transpose_func_def)
              also have "... = (OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<circ>\<^sub>c
                  \<langle>n,successor \<circ>\<^sub>c m\<rangle>"
                using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 m_def by (typecheck_cfuncs, force)
                also have "... = OR \<circ>\<^sub>c \<langle>
              leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>,
              leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>
              \<rangle>"
                  by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 nsm_type)
              also have "... = OR \<circ>\<^sub>c \<langle>
              leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle> ,
              leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle> 
              \<rangle>"
                using cfunc_prod_comp nsm_type by (typecheck_cfuncs, force)
              also have "... =  OR \<circ>\<^sub>c \<langle>  leq \<circ>\<^sub>c \<langle>n, successor \<circ>\<^sub>c m\<rangle>, leq \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c m, n\<rangle>\<rangle>"
                using left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod by (typecheck_cfuncs, force)
              also have "... = OR \<circ>\<^sub>c \<langle>  leq \<circ>\<^sub>c \<langle>n,  m\<rangle>, leq \<circ>\<^sub>c \<langle>  m, n\<rangle>\<rangle>"
                using OR_true_right_is_true main_inequality comp_type leq_type m_def m_leq_n x_is by presburger
               also have "... = OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>\<rangle>"
                 by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod)
               also have "... = OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>n,m\<rangle>"
                 by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 m_def x_is)
               also have "... = (OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                 by (typecheck_cfuncs, meson comp_associative2 m_def)
              
              
               also have "... = (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
                   id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                   (OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
                  \<langle>n,m\<rangle>"
                 using transpose_func_def by (typecheck_cfuncs, presburger)
              
               also have "... = (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
                   id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                   id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
                   (OR \<circ>\<^sub>c
                    \<langle>leq \<circ>\<^sub>c
                     \<langle>left_cart_proj \<nat>\<^sub>c
                       \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
                  \<langle>n,m\<rangle>"
                 using id_left_unit2 by (typecheck_cfuncs, presburger)
                then show ?thesis
                  by (simp add: calculation)
              qed
            qed



 


              show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          successor) \<circ>\<^sub>c x =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
                using \<open>(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c \<langle>n,m\<rangle> = (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle>\<close> m_def by force
           
            qed

          qed

        qed
      qed

have flat_main_result: "(OR \<circ>\<^sub>c \<langle>
leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
\<rangle>) = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c\<^esub>)"
  by (typecheck_cfuncs, metis main_result transpose_func_def)


  have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"  
    using assms by (typecheck_cfuncs,  smt comp_associative2 id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  then  have "(OR \<circ>\<^sub>c \<langle>
leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
\<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
    by (simp add: flat_main_result)  
  have "(OR \<circ>\<^sub>c \<langle>
leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
\<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle> = 
OR \<circ>\<^sub>c \<langle>
leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>m,n\<rangle> , right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c   \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>,
leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>
\<rangle>"
    using assms by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2)
  also have "... = OR \<circ>\<^sub>c \<langle> leq \<circ>\<^sub>c \<langle>m , n\<rangle>, leq \<circ>\<^sub>c \<langle>n, m\<rangle>\<rangle>"
    using left_cart_proj_cfunc_prod m_type n_type right_cart_proj_cfunc_prod by auto

  then  have "OR \<circ>\<^sub>c \<langle> leq \<circ>\<^sub>c \<langle>m , n\<rangle>, leq \<circ>\<^sub>c \<langle>n, m\<rangle>\<rangle> = \<t>"
    using \<open>(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>\<close> \<open>OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>\<rangle> = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>m,n\<rangle>,leq \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>\<close> calculation by presburger

  then show ?thesis
    using OR_true_implies_one_is_true cfunc_prod_type comp_type leq_type m_type n_type by blast
qed





end