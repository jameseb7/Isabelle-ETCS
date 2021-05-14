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
    by (metis add_associates add_commutes add_type m_leq_n_Eqn m_type u_leq_v_Eqn u_type)
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

   

lemma nonzero_is_succ:
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "k \<noteq> zero"
  shows "\<exists>n. k = successor \<circ>\<^sub>c n"

end