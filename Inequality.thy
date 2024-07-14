theory Inequality
  imports  Quant_Logic Add 
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
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c id (\<nat>\<^sub>c \<times>\<^sub>c one))\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, simp add: id_right_unit2)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c one, \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, metis cfunc_cross_prod_def id_cross_prod id_domain id_left_unit2 right_cart_proj_type terminal_func_unique)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, simp add: cfunc_prod_comp id_left_unit2 terminal_func_comp)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c((id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c\<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>cleft_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, smt cfunc_type_def comp_associative domain_comp)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
     using m_type n_type EXISTS_true_implies_exists_true by (typecheck_cfuncs, blast)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c ((add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c (associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>k, \<langle>m, n\<rangle>\<rangle> = \<t>"
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
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>k, \<langle>m, n\<rangle>\<rangle> = \<t>"
    using associate_left_ap m_type n_type by auto
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c k = \<t>"
    using m_type n_type cart_prod_extract_left by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c (associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and>  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c ((add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "\<exists> k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c k = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c(add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type exists_true_implies_EXISTS_true by (typecheck_cfuncs, blast)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<langle>m, n\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type comp_associative2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
    using m_type n_type cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_right_unit2 by (typecheck_cfuncs, auto)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c one, \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, smt  cfunc_prod_comp id_left_unit2 terminal_func_comp terminal_func_type)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>) \<circ>\<^sub>c id (\<nat>\<^sub>c \<times>\<^sub>c one))\<^sup>\<sharp> = \<t>"
    using m_type n_type by (typecheck_cfuncs, metis  cfunc_cross_prod_def id_cross_prod id_domain id_left_unit2 left_cart_proj_type right_cart_proj_type terminal_func_unique)
  then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (add2 \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c associate_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f \<langle>m, n\<rangle>))\<^sup>\<sharp> = \<t>"
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
  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> n = m"
    using leq_true_implies_exists m_type n_leq_m n_type by presburger
  obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> m = n"
    using leq_true_implies_exists m_leq_n m_type n_type by presburger
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

lemma fewer_is_less: 
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" 
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m +\<^sub>\<nat> k \<le>\<^sub>\<nat> n"
  shows "m \<le>\<^sub>\<nat> n"
  using assms unfolding leq_infix_def by (typecheck_cfuncs, metis add_commutes add_type assms(3) exists_implies_leq_true leq_infix_def leq_transitivity)

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
      by typecheck_cfuncs
    show type_fact2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
      by typecheck_cfuncs
    have type_fact3: "id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero : \<nat>\<^sub>c\<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
      by typecheck_cfuncs
    show type_fact3: "id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) : \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup> \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
      by typecheck_cfuncs
    show eqn_1: "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
            (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule same_evals_equal[where Z = "one", where X=\<Omega>, where A="\<nat>\<^sub>c"])
      show type_fact5: "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>, leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
        by typecheck_cfuncs
      show type_fact6: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
        by typecheck_cfuncs
      show eqn_2: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
            eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(rule one_separator[where X="\<nat>\<^sub>c\<times>\<^sub>c one", where Y = \<Omega>])
        show type_fact7: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>, leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c            zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show type_fact8: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
             (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c
             \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
              leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
           (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
          obtain j where j_type[type_rule]: "j\<in>\<^sub>c \<nat>\<^sub>c" and j_def: "x = \<langle>j,id one\<rangle>"
            using cart_prod_decomp one_unique_element by (typecheck_cfuncs, blast)
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
              by (typecheck_cfuncs, metis comp_associative2)
            also have "... =  \<t>"
              by (typecheck_cfuncs, metis id_right_unit2 terminal_func_unique)
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
                by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle>  ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle> \<rangle>,
                    leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>j,zero\<rangle> \<rangle>\<rangle>"
                by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 j_def)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>j ,zero \<rangle>, leq \<circ>\<^sub>c\<langle>zero ,j \<rangle>\<rangle>"
                by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>j ,zero \<rangle>, \<t>\<rangle>"
                using zero_is_smallest by (typecheck_cfuncs, presburger)
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
          by typecheck_cfuncs
        show type_fact10: "id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
          by typecheck_cfuncs
        show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>"
        proof(rule one_separator[where X="\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c", where Y = \<Omega>])
          show type_fact11: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
            by typecheck_cfuncs
          show type_fact12: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
            by typecheck_cfuncs
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
                   leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  successor =
    id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                          leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
        proof(rule same_evals_equal[where Z="\<nat>\<^sub>c", where X=\<Omega>, where A ="\<nat>\<^sub>c" ])
          show type_fact13: "(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>, leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c    successor : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs
          show type_fact14: "id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>, leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs
          show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
            leq \<circ>\<^sub>c\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor =
    eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
    (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
           leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
          proof(rule one_separator[where X = "\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c", where Y = \<Omega>])
            show type_fact15: "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>, leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>, leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
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
                           leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c \<langle>n,m\<rangle> =
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
          then show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                      leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c \<langle>n,m\<rangle> =
                      (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,
                      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c\<langle>n,m\<rangle>"
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

            show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                   (OR \<circ>\<^sub>c      \<langle>leq \<circ>\<^sub>c  \<langle>left_cart_proj \<nat>\<^sub>c  \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  successor) \<circ>\<^sub>c \<langle>n,m\<rangle> = 
    (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
                   (OR \<circ>\<^sub>c      \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c  \<langle>n,m\<rangle>"             
            proof - 
              have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                   (OR \<circ>\<^sub>c      \<langle>leq \<circ>\<^sub>c  \<langle>left_cart_proj \<nat>\<^sub>c  \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  successor) \<circ>\<^sub>c \<langle>n,m\<rangle> =
                     ((eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
                   (OR \<circ>\<^sub>c      \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c  \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                               leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                              using sharp_comp transpose_func_def by (typecheck_cfuncs,force)
              also have "... = (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                      leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>n,m\<rangle>)"
                              by (typecheck_cfuncs, smt (verit, best) comp_associative2 m_def transpose_func_def)
              also have "... = (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                      leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>"
                using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 m_def by (typecheck_cfuncs, force)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>,
                                     leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle>"
                by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 nsm_type)
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle> ,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle> ,
                                     leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c m\<rangle>\<rangle> \<rangle>"
                using cfunc_prod_comp nsm_type by (typecheck_cfuncs, force)
              also have "... =  OR \<circ>\<^sub>c \<langle>  leq \<circ>\<^sub>c \<langle>n, successor \<circ>\<^sub>c m\<rangle>, leq \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c m, n\<rangle>\<rangle>"
                using left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod by (typecheck_cfuncs, force)
              also have "... = OR \<circ>\<^sub>c \<langle>  leq \<circ>\<^sub>c \<langle>n,  m\<rangle>, leq \<circ>\<^sub>c \<langle>  m, n\<rangle>\<rangle>"
                using OR_true_right_is_true main_inequality comp_type leq_type m_def m_leq_n x_is by presburger
              also have "... = OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>,
                                     leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>n,m\<rangle>\<rangle>\<rangle>"
                by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod m_def right_cart_proj_cfunc_prod)
              also have "... = OR \<circ>\<^sub>c\<langle>leq \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                     leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>n,m\<rangle>"
                by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 m_def x_is)
              also have "... = (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                       leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                by (typecheck_cfuncs, meson comp_associative2 m_def)                           
              also have "... = (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                                                     leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                using transpose_func_def by (typecheck_cfuncs, presburger)
              also have "... = (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c(OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                                                         leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>n,m\<rangle>"
                using id_left_unit2 by (typecheck_cfuncs, presburger)
              then show ?thesis
                by (simp add: calculation)
              qed
         qed

              then show "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  successor) \<circ>\<^sub>c x =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c
          (OR \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                  leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
                using  m_def by force           
        qed
      qed
    qed
  qed

  have flat_main_result: "(OR \<circ>\<^sub>c \<langle>
                        leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                        leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<rangle>) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c\<^esub>"
    by (typecheck_cfuncs, metis main_result transpose_func_def)

  have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"  
    using assms by (typecheck_cfuncs,  smt comp_associative2 id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  then  have calc1: "(OR \<circ>\<^sub>c \<langle>
                        leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                        leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
    by (simp add: flat_main_result)  
  have "(OR \<circ>\<^sub>c \<langle>
                leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle> = 
         OR \<circ>\<^sub>c \<langle>
                leq \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>m,n\<rangle> , right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c   \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>,
                leq \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle> \<rangle>"
    using assms by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2)
  also have "... = OR \<circ>\<^sub>c \<langle> leq \<circ>\<^sub>c \<langle>m , n\<rangle>, leq \<circ>\<^sub>c \<langle>n, m\<rangle>\<rangle>"
    using left_cart_proj_cfunc_prod m_type n_type right_cart_proj_cfunc_prod by auto
  then  have "OR \<circ>\<^sub>c \<langle> leq \<circ>\<^sub>c \<langle>m , n\<rangle>, leq \<circ>\<^sub>c \<langle>n, m\<rangle>\<rangle> = \<t>"
    using assms calc1  calculation by presburger
  then show ?thesis
    using OR_true_implies_one_is_true cfunc_prod_type comp_type leq_type m_type n_type by blast
qed

lemma nat_strict_total_order:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(n \<le>\<^sub>\<nat> m) = (\<not>(successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n))"
proof(auto)
  show "n \<le>\<^sub>\<nat> m \<Longrightarrow> successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n \<Longrightarrow> False"
    by (metis add_respects_succ2 add_respects_zero_on_left exists_implies_leq_true leq_infix_def
        leq_transitivity lqe_antisymmetry n_neq_succ_n succ_n_type zero_type assms)
next
  assume "\<not> successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n"
  then have "(n \<le>\<^sub>\<nat> successor \<circ>\<^sub>c m) \<and> (n \<noteq> successor \<circ>\<^sub>c m)"
    using assms by (meson comp_type leq_infix_def lqe_connexity successor_type) 
  then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "successor \<circ>\<^sub>c m = n +\<^sub>\<nat> k"  and k_nonzero: "k \<noteq> zero"
    using assms by (typecheck_cfuncs, metis add_commutes add_respects_zero_on_right leq_infix_def leq_true_implies_exists)
  then show "n \<le>\<^sub>\<nat> m"
    using assms by (smt (verit, best) add_commutes add_respects_succ3 add_type exists_implies_leq_true leq_infix_def nonzero_is_succ succ_inject)
qed

lemma Succession_Principle:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "k \<in>\<^sub>c \<nat>\<^sub>c \<and>  n \<le>\<^sub>\<nat> k \<and> k \<le>\<^sub>\<nat> successor \<circ>\<^sub>c n \<Longrightarrow> k = n \<or> k = successor \<circ>\<^sub>c n"
proof(unfold leq_infix_def, rule ccontr, auto)
  assume k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
  assume k_not_n: "k \<noteq> n"
  assume k_not_sn: "k \<noteq> successor \<circ>\<^sub>c n"
  assume n_lt_k: "leq \<circ>\<^sub>c \<langle>n,k\<rangle> = \<t>"
  assume k_lt_sn: "leq \<circ>\<^sub>c \<langle>k,successor \<circ>\<^sub>c n\<rangle> = \<t>"
  
  obtain p where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and p_def:  "k = p +\<^sub>\<nat> n" and p_nonzero: "p \<noteq> zero"
    by (typecheck_cfuncs, metis add_respects_zero_on_left k_not_n leq_true_implies_exists n_lt_k)
  obtain i where i_type[type_rule]: "i \<in>\<^sub>c \<nat>\<^sub>c" and i_def:  "p = successor \<circ>\<^sub>c i"
    using nonzero_is_succ p_nonzero by (typecheck_cfuncs, blast)
  obtain q where q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and q_def:  "successor \<circ>\<^sub>c n = q +\<^sub>\<nat> k"  and q_nonzero: "q \<noteq> zero"
    by (typecheck_cfuncs, metis add_respects_zero_on_left k_lt_sn k_not_sn leq_true_implies_exists)
  obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and j_def:  "q = successor \<circ>\<^sub>c j"
    using nonzero_is_succ q_nonzero by (typecheck_cfuncs, blast)
  
  have "successor \<circ>\<^sub>c k = successor \<circ>\<^sub>c (p +\<^sub>\<nat> n)"
    using p_def by blast
  then have "successor \<circ>\<^sub>c k = p +\<^sub>\<nat> (successor \<circ>\<^sub>c n)"
    by (typecheck_cfuncs, simp add: add2_respects_succ_right add_def p_def)
  then have "successor \<circ>\<^sub>c k = p +\<^sub>\<nat> (q +\<^sub>\<nat> k)" 
    by (simp add: q_def)
  then have "successor \<circ>\<^sub>c zero = p +\<^sub>\<nat> q"
    by (typecheck_cfuncs, metis add_associates add_cancellative add_commutes add_respects_succ3 add_respects_zero_on_left n_type p_def q_def)
  then have "(successor \<circ>\<^sub>c zero) +\<^sub>\<nat> zero = ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> i) +\<^sub>\<nat> (successor \<circ>\<^sub>c j)"
    by (typecheck_cfuncs, metis add_respects_succ3 add_respects_zero_on_left i_def j_def)
  then have "zero = successor \<circ>\<^sub>c (i +\<^sub>\<nat> j)"
    using \<open>successor \<circ>\<^sub>c zero = p +\<^sub>\<nat> q\<close> add_respects_succ1 add_respects_succ3 i_def j_def p_type succ_inject by (typecheck_cfuncs, presburger)
  then show False
    using add_type i_type j_type zero_is_not_successor by force
qed
  
theorem strong_induction:
  assumes P_type[type_rule]: "P : \<nat>\<^sub>c \<rightarrow> \<Omega>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes base_case: "P \<circ>\<^sub>c zero = \<t>"
  assumes induction_case: "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (\<And>k. k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k \<le>\<^sub>\<nat> n \<Longrightarrow> P \<circ>\<^sub>c k = \<t>) \<Longrightarrow>   P \<circ>\<^sub>c (successor \<circ>\<^sub>c n) = \<t>"
  shows "P \<circ>\<^sub>c n = \<t>"
proof - 
  obtain Q where Q_type[type_rule]: "Q : \<nat>\<^sub>c \<rightarrow> \<Omega>" 
      and Q_def: "Q = FORALL \<nat>\<^sub>c  \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq , P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
    by typecheck_cfuncs
  have Qn_true_eqs: "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>(( Q \<circ>\<^sub>c n = \<t>) = (\<forall> k. k \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> k \<le>\<^sub>\<nat> n \<longrightarrow> P \<circ>\<^sub>c k = \<t>))"
  proof(auto)
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume "Q \<circ>\<^sub>c n = \<t>"
    then have "(FORALL \<nat>\<^sub>c ) \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq , P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c n = \<t>"
      unfolding Q_def by (etcs_assocl, blast)
    then have "(FORALL \<nat>\<^sub>c ) \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>leq , P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id  \<nat>\<^sub>c \<times>\<^sub>f n))\<^sup>\<sharp> = \<t>"
      using  sharp_comp by (typecheck_cfuncs, force) 
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>leq , P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c( (id  \<nat>\<^sub>c \<times>\<^sub>f n) \<circ>\<^sub>c \<langle>k, id one\<rangle>) = \<t>"
      by(etcs_assocl, typecheck_cfuncs, smt FORALL_elim)
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> IMPLIES \<circ>\<^sub>c (\<langle>leq , P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>k,n\<rangle>) = \<t>"
      by(etcs_assocl, typecheck_cfuncs, smt (z3)  cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type)
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> IMPLIES \<circ>\<^sub>c (\<langle>leq \<circ>\<^sub>c \<langle>k, n\<rangle>, (P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>k, n\<rangle>\<rangle>) = \<t>"
      by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp cfunc_prod_type)
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> IMPLIES \<circ>\<^sub>c (\<langle>leq \<circ>\<^sub>c \<langle>k, n\<rangle>, P \<circ>\<^sub>c k\<rangle>) = \<t>"
      by (typecheck_cfuncs, metis cfunc_prod_type cfunc_type_def comp_associative left_cart_proj_cfunc_prod left_cart_proj_type)
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> leq \<circ>\<^sub>c \<langle>k, n\<rangle> = \<t> \<Longrightarrow> P \<circ>\<^sub>c k = \<t>"
      by (typecheck_cfuncs, metis IMPLIES_elim' comp_type)
    then show "\<And> k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k \<le>\<^sub>\<nat> n \<Longrightarrow> P \<circ>\<^sub>c k = \<t>"
      by(simp add: leq_infix_def)
  next 
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume "\<forall>k. k \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> k \<le>\<^sub>\<nat> n \<longrightarrow> P \<circ>\<^sub>c k = \<t>"
    then have "\<And> k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> leq \<circ>\<^sub>c \<langle>k, n\<rangle> = \<t> \<Longrightarrow> P \<circ>\<^sub>c k = \<t>"
      using leq_infix_def by blast
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> IMPLIES \<circ>\<^sub>c (\<langle>leq \<circ>\<^sub>c \<langle>k, n\<rangle>, P \<circ>\<^sub>c k\<rangle>) = \<t>"
      by (typecheck_cfuncs, smt (verit, ccfv_SIG)  cfunc_prod_type comp_type implies_implies_IMPLIES)
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> IMPLIES \<circ>\<^sub>c (\<langle>leq \<circ>\<^sub>c \<langle>k, n\<rangle>, (P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>k, n\<rangle>\<rangle>) = \<t>"
      by(etcs_assocr, typecheck_cfuncs, simp add:  left_cart_proj_cfunc_prod)
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>leq, P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>k, n\<rangle> = \<t>"
      by (etcs_assocr, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp cfunc_prod_type)
    then have "\<And>k.  k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> ((IMPLIES \<circ>\<^sub>c \<langle>leq, P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id  \<nat>\<^sub>c \<times>\<^sub>f n)) \<circ>\<^sub>c \<langle>k   ,id one  \<rangle> = \<t>"
      by (typecheck_cfuncs, smt (verit, best)  cfunc_cross_prod_comp_cfunc_prod cfunc_prod_type comp_associative2 id_left_unit2 id_right_unit2)
    then have "(FORALL \<nat>\<^sub>c ) \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>leq, P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id  \<nat>\<^sub>c \<times>\<^sub>f n))\<^sup>\<sharp> = \<t>"
      using all_true_implies_FORALL_true3 by (typecheck_cfuncs, blast)
    then have "(FORALL \<nat>\<^sub>c ) \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, P \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c n = \<t>"
      by (typecheck_cfuncs, simp add: sharp_comp)
    then show "Q \<circ>\<^sub>c n = \<t>"
      unfolding Q_def by (etcs_assocr, blast)
  qed
  have "Q \<circ>\<^sub>c n = \<t>"
  proof(etcs_rule nat_induction)
    show "Q \<circ>\<^sub>c zero = \<t>"
      using Q_def Qn_true_eqs base_case leq_infix_def lqe_antisymmetry true_false_distinct zero_is_smallest by (typecheck_cfuncs, blast)
  next
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume Qn_true:  "Q \<circ>\<^sub>c n = \<t>"
    then show " Q \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
       by (typecheck_cfuncs, metis Qn_true Qn_true_eqs induction_case leq_infix_def lqe_antisymmetry nat_strict_total_order)
  qed
  then show "P \<circ>\<^sub>c n = \<t>"
    using Qn_true_eqs leq_infix_def lqe_connexity by (typecheck_cfuncs, blast)
qed

theorem well_ordering_principle:
  assumes nonempty_set: "nonempty S"  
  assumes subset_nat: "(S,m) \<subseteq>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists> min. min \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m) \<and> (\<forall> s. s \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m) \<longrightarrow> min  \<le>\<^sub>\<nat> s)"
proof(rule ccontr) 
  assume no_min: "\<nexists>min. min \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m) \<and> (\<forall>s. s \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m) \<longrightarrow> min \<le>\<^sub>\<nat> s)"
  obtain P where P_type[type_rule]: "P : \<nat>\<^sub>c \<rightarrow> \<Omega>" and P_def: "P = NOT \<circ>\<^sub>c characteristic_func m"
    by (metis NOT_type characteristic_func_type comp_type subobject_of_def2 subset_nat)
  have P_eq_t: "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> P \<circ>\<^sub>c n  = \<t>"
  proof(auto)
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    show "P \<circ>\<^sub>c n  = \<t>"
    proof(etcs_rule strong_induction)
      show "P \<circ>\<^sub>c zero = \<t>"
      proof(rule ccontr)
        assume "P \<circ>\<^sub>c zero \<noteq> \<t>"
        then have "zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m)"
          by (typecheck_cfuncs, metis NOT_false_is_true NOT_type P_def  characteristic_func_type comp_associative2 not_rel_mem_char_func_false subobject_of_def2 subset_nat)
        have "\<forall> s. s \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m) \<longrightarrow>  zero \<le>\<^sub>\<nat>  s"
          by (simp add: leq_infix_def relative_member_def zero_is_smallest)
        then show False
          using no_min \<open>zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m)\<close> by blast
      qed
      show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (\<And>k. k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k \<le>\<^sub>\<nat> n \<Longrightarrow> P \<circ>\<^sub>c k = \<t>) \<Longrightarrow> P \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
      proof - 
        fix n 
        assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
        assume "(\<And>k. k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k \<le>\<^sub>\<nat> n \<Longrightarrow> P \<circ>\<^sub>c k = \<t>)"
        then have induction_hypothesis: "\<And>k. k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k \<le>\<^sub>\<nat> n \<Longrightarrow> \<not>k \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m)"
          by (metis NOT_true_is_false NOT_type P_def  characteristic_func_false_not_relative_member
              characteristic_func_type comp_associative2 rel_mem_char_func_true subobject_of_def2 subset_nat)
        have "\<not>successor \<circ>\<^sub>c n  \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m)"
        proof(rule ccontr, auto)
          assume BWOC: "successor \<circ>\<^sub>c n  \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m)"
          then have "\<forall> s. s \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m) \<longrightarrow> successor \<circ>\<^sub>c n  \<le>\<^sub>\<nat> s "
            by (typecheck_cfuncs, metis Succession_Principle induction_hypothesis leq_infix_def lqe_connexity relative_member_def2)
          then show False
            using BWOC no_min by blast
        qed
        then show "P \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
          by (typecheck_cfuncs, metis NOT_false_is_true NOT_type P_def  characteristic_func_type 
              comp_associative2 not_rel_mem_char_func_false subobject_of_def2 subset_nat)
      qed
    qed
  qed
  have "\<not>nonempty S"
  proof(rule ccontr, auto, unfold nonempty_def)
    assume "\<exists>s. s \<in>\<^sub>c S"
    then obtain s where s_type[type_rule]: "s \<in>\<^sub>c S"
      by blast
    then have "P \<circ>\<^sub>c m  \<circ>\<^sub>c s = \<t>"
      using P_eq_t comp_type subobject_of_def2 subset_nat by blast
    then have "\<not> m  \<circ>\<^sub>c s  \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (S, m)"
      by (metis NOT_true_is_false NOT_type P_def characteristic_func_type comp_associative2
          rel_mem_char_func_true relative_member_def2 true_false_distinct)
    then have "\<nexists>h. m \<circ>\<^sub>c h = m \<circ>\<^sub>c s"
      by (typecheck_cfuncs, meson factors_through_def2 relative_member_def2 subobject_of_def2 subset_nat)
    then show False
      by blast
  qed
  then show False
    using nonempty_set by auto
qed




end


