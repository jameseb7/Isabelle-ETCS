theory ETCS_Comparison
  imports ETCS_Quantifier ETCS_Add
begin

definition leq :: "cfunc" where
  "leq = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"

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


end