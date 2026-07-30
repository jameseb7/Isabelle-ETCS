section \<open>Quantifiers\<close>

theory Quant_Logic
  imports Pred_Logic Exponential_Objects
begin

subsection \<open>Universal Quantification\<close>

text \<open>HOL's @{text THE}-based definition is replaced by reusing @{text characteristic_func}
  directly, exactly as for @{text NOT}/@{text AND}/@{text NOR}: the defining pullback square for
  @{text FORALL} is exactly the characteristic-function pullback of the monic point
  @{text "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> : \<one> \<rightarrow> \<Omega>\<^bsup>X\<^esup>"}.\<close>
definition FORALL :: "cset \<Rightarrow> cfunc" where
  "FORALL(X) = characteristic_func((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>)"

lemma tbeta_sharp_type[type_rule]: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs

lemma FORALL_is_pullback:
  "is_pullback(\<one>, \<one>, \<Omega>\<^bsup>X\<^esup>, \<Omega>, \<beta>\<^bsub>\<one>\<^esub>, \<t>, (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>, FORALL(X))"
  unfolding FORALL_def
  using characteristic_func_is_pullback[OF tbeta_sharp_type element_monomorphism[OF tbeta_sharp_type]] .

lemma FORALL_type[type_rule]:
  "FORALL(X) : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>"
  using FORALL_is_pullback unfolding is_pullback_def by auto

lemma all_true_implies_FORALL_true:
  assumes p_type[type_rule]: "p : X \<rightarrow> \<Omega>" and all_p_true: "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t>"
  shows "FORALL(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
proof -
  have eq1: "p \<circ>\<^sub>c left_cart_proj(X, \<one>) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>"
  proof (etcs_rule one_separator)
    fix x
    assume x_type[type_rule]: "x \<in>\<^sub>c X \<times>\<^sub>c \<one>"
    have s1: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c x = p \<circ>\<^sub>c (left_cart_proj(X, \<one>) \<circ>\<^sub>c x)"
      by (rule sym[OF comp_associative2[OF x_type left_cart_proj_type p_type]])
    have lpx_type[type_rule]: "left_cart_proj(X, \<one>) \<circ>\<^sub>c x \<in>\<^sub>c X" by typecheck_cfuncs
    have s2: "p \<circ>\<^sub>c (left_cart_proj(X, \<one>) \<circ>\<^sub>c x) = \<t>" using all_p_true[OF lpx_type] .
    have s3: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c x = id(\<one>)" using terminal_func_comp_elem[OF x_type] .
    have s4: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c x = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c x)"
      by (rule sym[OF comp_associative2[OF x_type terminal_func_type true_func_type]])
    have s5: "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c x) = \<t> \<circ>\<^sub>c id(\<one>)" using s3 by simp
    have s6: "\<t> \<circ>\<^sub>c id(\<one>) = \<t>" using id_right_unit2[OF true_func_type] .
    show "(p \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c x"
      using s1 s2 s4 s5 s6 by simp
  qed
  have eq2: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>" using eq1 by simp
  have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = FORALL(X) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>"
    using FORALL_is_pullback unfolding is_pullback_def by auto
  have s7: "FORALL(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>"
    using eq2 comm by simp
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  show "FORALL(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
    using s7 b1_id id_right_unit2[OF true_func_type] by simp
qed

lemma all_true_implies_FORALL_true2:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" and all_p_true: "\<And>xy. xy \<in>\<^sub>c X \<times>\<^sub>c Y \<Longrightarrow> p \<circ>\<^sub>c xy = \<t>"
  shows "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
proof -
  have eq1: "p = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  proof (etcs_rule one_separator)
    fix xy
    assume xy_type[type_rule]: "xy \<in>\<^sub>c X \<times>\<^sub>c Y"
    have s1: "p \<circ>\<^sub>c xy = \<t>" using all_p_true[OF xy_type] .
    have s2: "\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c xy = id(\<one>)" using terminal_func_comp_elem[OF xy_type] .
    have s3: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c xy = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c xy)"
      by (rule sym[OF comp_associative2[OF xy_type terminal_func_type true_func_type]])
    have s4: "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c xy) = \<t> \<circ>\<^sub>c id(\<one>)" using s2 by simp
    have s5: "\<t> \<circ>\<^sub>c id(\<one>) = \<t>" using id_right_unit2[OF true_func_type] .
    show "p \<circ>\<^sub>c xy = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c xy" using s1 s3 s4 s5 by simp
  qed
  have eq2: "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>)\<^sup>\<sharp>" using eq1 by simp

  have tX1_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have betaY_type[type_rule]: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by typecheck_cfuncs
  have comp_type1[type_rule]: "id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub> : X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c \<one>" by typecheck_cfuncs
  have comp_type1b[type_rule]: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) : X \<times>\<^sub>c Y \<rightarrow> \<one>" by typecheck_cfuncs
  have beta_eq: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) = \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
    using terminal_func_unique[OF comp_type1b] by simp
  have tb_eq: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  proof -
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>))"
      by (rule sym[OF comp_associative2[OF comp_type1 terminal_func_type true_func_type]])
    then show ?thesis using beta_eq by simp
  qed
  have sc: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>))\<^sup>\<sharp>"
    by (rule sharp_comp[OF tX1_type betaY_type])
  have eq3: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>)\<^sup>\<sharp>"
    using sc tb_eq by simp
  have eq4: "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using eq2 eq3 by simp

  have tX1sharp_type[type_rule]: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have eq5: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = FORALL(X) \<circ>\<^sub>c ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"
    using eq4 by simp
  have eq6: "FORALL(X) \<circ>\<^sub>c ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) = (FORALL(X) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    by (rule comp_associative2[OF betaY_type tX1sharp_type FORALL_type])
  have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = FORALL(X) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>"
    using FORALL_is_pullback unfolding is_pullback_def by auto
  have eq7: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>) \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using eq5 eq6 comm by simp
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  show "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  proof -
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>) \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = (\<t> \<circ>\<^sub>c id(\<one>)) \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" using b1_id by simp
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" using id_right_unit2[OF true_func_type] by simp
    finally show ?thesis using eq7 by simp
  qed
qed

lemma all_true_implies_FORALL_true3:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" and all_p_true: "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<t>"
  shows "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>"
proof -
  have all_p_true2: "\<And>xy. xy \<in>\<^sub>c X \<times>\<^sub>c \<one> \<Longrightarrow> p \<circ>\<^sub>c xy = \<t>"
  proof -
    fix xy assume xy_type[type_rule]: "xy \<in>\<^sub>c X \<times>\<^sub>c \<one>"
    obtain x1 y1 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and y1_type[type_rule]: "y1 \<in>\<^sub>c \<one>" and xy_def: "xy = \<langle>x1,y1\<rangle>"
      using cart_prod_decomp[OF xy_type] by blast
    have y1_eq: "y1 = id(\<one>)" using element_of_1[OF y1_type] .
    have xy_def2: "xy = \<langle>x1, id(\<one>)\<rangle>" using xy_def y1_eq by simp
    show "p \<circ>\<^sub>c xy = \<t>" using xy_def2 all_p_true[OF x1_type] by simp
  qed
  have step: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>"
    using all_true_implies_FORALL_true2[OF p_type all_p_true2] .
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  show ?thesis using step b1_id id_right_unit2[OF true_func_type] by simp
qed

lemma FORALL_true_implies_all_true:
  assumes p_type[type_rule]: "p : X \<rightarrow> \<Omega>" and FORALL_p_true: "FORALL(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
  assumes x_type[type_rule]: "x \<in>\<^sub>c X"
  shows "p \<circ>\<^sub>c x = \<t>"
proof (rule ccontr)
  assume contra: "p \<circ>\<^sub>c x \<noteq> \<t>"
  have px_type[type_rule]: "p \<circ>\<^sub>c x \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have px_eq_f: "p \<circ>\<^sub>c x = \<f>" using true_false_only_truth_values[OF px_type] contra by auto

  have xid_type[type_rule]: "\<langle>x, id(\<one>)\<rangle> \<in>\<^sub>c X \<times>\<^sub>c \<one>" by typecheck_cfuncs
  have lp_x: "left_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = x"
    using left_cart_proj_cfunc_prod[OF x_type id_type] .
  have s1: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = p \<circ>\<^sub>c (left_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>)"
    by (rule sym[OF comp_associative2[OF xid_type left_cart_proj_type p_type]])
  have s2: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<f>"
    using s1 lp_x px_eq_f by simp
  have bx_type: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = id(\<one>)"
    using terminal_func_comp_elem[OF xid_type] .
  have s3: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<f>"
  proof -
    have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>)"
      by (rule sym[OF comp_associative2[OF xid_type terminal_func_type false_func_type]])
    also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using bx_type by simp
    also have "... = \<f>" using id_right_unit2[OF false_func_type] .
    finally show ?thesis .
  qed
  have p_left_proj_false: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
    using s2 s3 by simp

  have comm_eq: "\<t> \<circ>\<^sub>c id(\<one>) = FORALL(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    using FORALL_p_true id_right_unit2[OF true_func_type] by simp
  have plp_sharp_type[type_rule]: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> \<t> \<circ>\<^sub>c k = FORALL(X) \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = h)"
    using FORALL_is_pullback unfolding is_pullback_def by auto
  have spec_case: "id(\<one>) : \<one> \<rightarrow> \<one> \<and> (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> : \<one> \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> \<t> \<circ>\<^sub>c id(\<one>) = FORALL(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    using comm_eq by (typecheck_cfuncs, auto)
  have ex_j: "\<exists>! j. j : \<one> \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    using uniq spec_case by blast
  obtain j where j_type: "j : \<one> \<rightarrow> \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = id(\<one>)" and t_j_eq: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    using ex_j by auto
  have j_eq: "j = id(\<one>)" using element_of_1[OF j_type] .
  have t_eq: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> = (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    using t_j_eq j_eq id_right_unit2[OF tbeta_sharp_type] by simp
  have tX1_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have plp_type[type_rule]: "p \<circ>\<^sub>c left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have flat_eq: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> = p \<circ>\<^sub>c left_cart_proj(X, \<one>)"
  proof -
    have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>)\<^sup>\<flat>" using sym[OF flat_cancels_sharp[OF tX1_type]] .
    also have "... = ((p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>)\<^sup>\<flat>" using t_eq by simp
    also have "... = p \<circ>\<^sub>c left_cart_proj(X, \<one>)" using flat_cancels_sharp[OF plp_type] .
    finally show ?thesis .
  qed
  have p_left_proj_true: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = (p \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
    using flat_eq by simp
  have tb_x: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<t>"
  proof -
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>)"
      by (rule sym[OF comp_associative2[OF xid_type terminal_func_type true_func_type]])
    also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using bx_type by simp
    also have "... = \<t>" using id_right_unit2[OF true_func_type] .
    finally show ?thesis .
  qed
  have "\<t> = \<f>"
  proof -
    have "\<t> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>" using tb_x by (rule sym)
    also have "... = (p \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>" using p_left_proj_true .
    also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>" using p_left_proj_false .
    also have "... = \<f>" using s3 .
    finally show ?thesis .
  qed
  then show False using true_false_distinct by auto
qed

lemma FORALL_true_implies_all_true2:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" and FORALL_p_true: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  assumes x_type[type_rule]: "x \<in>\<^sub>c X" and y_type[type_rule]: "y \<in>\<^sub>c Y"
  shows "p \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>"
proof -
  have tX1_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have betaY_type[type_rule]: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by typecheck_cfuncs
  have psharp_eq: "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  proof -
    have uniq: "\<forall> Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> \<t> \<circ>\<^sub>c k = FORALL(X) \<circ>\<^sub>c h)  \<longrightarrow>
        (\<exists>! j. j : Z \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = k \<and> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = h)"
      using FORALL_is_pullback unfolding is_pullback_def by auto
    have psharp_type[type_rule]: "p\<^sup>\<sharp> : Y \<rightarrow> \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
    have spec_case: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one> \<and> p\<^sup>\<sharp> : Y \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> \<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp>"
      using FORALL_p_true by (typecheck_cfuncs, auto)
    have ex_j: "\<exists>! j. j : Y \<rightarrow> \<one> \<and> \<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = \<beta>\<^bsub>Y\<^esub> \<and> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = p\<^sup>\<sharp>"
      using uniq spec_case by blast
    obtain j where j_type: "j : Y \<rightarrow> \<one>" and j_id: "\<beta>\<^bsub>\<one>\<^esub> \<circ>\<^sub>c j = \<beta>\<^bsub>Y\<^esub>" and t_j_eq: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c j = p\<^sup>\<sharp>"
      using ex_j by auto
    have j_eq: "j = \<beta>\<^bsub>Y\<^esub>" using terminal_func_unique[OF j_type] .
    show ?thesis using t_j_eq j_eq by simp
  qed
  have comp_type1[type_rule]: "id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub> : X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c \<one>" by typecheck_cfuncs
  have comp_type1b[type_rule]: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) : X \<times>\<^sub>c Y \<rightarrow> \<one>" by typecheck_cfuncs
  have tX1_beta_eq: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>))\<^sup>\<sharp>"
    by (rule sharp_comp[OF tX1_type betaY_type])
  have beta_eq: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) = \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
    using terminal_func_unique[OF comp_type1b] by simp
  have tb_eq: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  proof -
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<beta>\<^bsub>Y\<^esub>))"
      by (rule sym[OF comp_associative2[OF comp_type1 terminal_func_type true_func_type]])
    then show ?thesis using beta_eq by simp
  qed
  have psharp_eq2: "p\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>)\<^sup>\<sharp>"
    using psharp_eq tX1_beta_eq tb_eq by simp
  have tXY_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> : X \<times>\<^sub>c Y \<rightarrow> \<Omega>" by typecheck_cfuncs
  have p_eq: "p = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>"
  proof -
    have "p = (p\<^sup>\<sharp>)\<^sup>\<flat>" using sym[OF flat_cancels_sharp[OF p_type]] .
    also have "... = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>)\<^sup>\<sharp>)\<^sup>\<flat>" using psharp_eq2 by simp
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>" using flat_cancels_sharp[OF tXY_type] .
    finally show ?thesis .
  qed
  have xy_type[type_rule]: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" by typecheck_cfuncs
  have s1: "p \<circ>\<^sub>c \<langle>x,y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c \<langle>x,y\<rangle>" using p_eq by simp
  have s2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub>) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c \<langle>x,y\<rangle>)"
    by (rule sym[OF comp_associative2[OF xy_type terminal_func_type true_func_type]])
  have s3: "\<beta>\<^bsub>X \<times>\<^sub>c Y\<^esub> \<circ>\<^sub>c \<langle>x,y\<rangle> = id(\<one>)" using terminal_func_comp_elem[OF xy_type] .
  have s4: "\<t> \<circ>\<^sub>c id(\<one>) = \<t>" using id_right_unit2[OF true_func_type] .
  show "p \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>" using s1 s2 s3 s4 by simp
qed

lemma FORALL_true_implies_all_true3:
  assumes p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" and FORALL_p_true: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>"
  assumes x_type[type_rule]: "x \<in>\<^sub>c X"
  shows "p \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<t>"
proof -
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  have FORALL_p_true2: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>"
    using FORALL_p_true b1_id id_right_unit2[OF true_func_type] by simp
  show ?thesis
    using FORALL_true_implies_all_true2[OF p_type FORALL_p_true2 x_type id_type] .
qed

lemma FORALL_elim:
  assumes FORALL_p_true: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>" and p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>"
  assumes x_type[type_rule]: "x \<in>\<^sub>c X"
  shows "(p \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<t> \<Longrightarrow> P) \<Longrightarrow> P"
  using FORALL_true_implies_all_true3[OF p_type FORALL_p_true x_type] by auto

lemma FORALL_elim':
  assumes FORALL_p_true: "FORALL(X) \<circ>\<^sub>c p\<^sup>\<sharp> = \<t>" and p_type[type_rule]: "p : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>"
  shows "((\<And>x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> = \<t>) \<Longrightarrow> P) \<Longrightarrow> P"
  using FORALL_true_implies_all_true3[OF p_type FORALL_p_true] by auto

subsection \<open>Existential Quantification\<close>

definition EXISTS :: "cset \<Rightarrow> cfunc" where
  "EXISTS(X) = NOT \<circ>\<^sub>c FORALL(X) \<circ>\<^sub>c exp_func(NOT, X)"

lemma EXISTS_type[type_rule]:
  "EXISTS(X) : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>"
  unfolding EXISTS_def by typecheck_cfuncs

lemma EXISTS_true_implies_exists_true:
  assumes p_type[type_rule]: "p : X \<rightarrow> \<Omega>" and EXISTS_p_true: "EXISTS(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
  shows "\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = \<t>"
proof -
  have lp_type[type_rule]: "left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X" by typecheck_cfuncs
  have plp_type[type_rule]: "p \<circ>\<^sub>c left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have plp_sharp_type[type_rule]: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have expNOTX_type[type_rule]: "exp_func(NOT, X) : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have FNOT_type[type_rule]: "FORALL(X) \<circ>\<^sub>c exp_func(NOT, X) : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have s1: "EXISTS(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>
      = (NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c exp_func(NOT, X))) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    unfolding EXISTS_def by simp
  have s2: "(NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c exp_func(NOT, X))) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>
      = NOT \<circ>\<^sub>c ((FORALL(X) \<circ>\<^sub>c exp_func(NOT, X)) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>)"
    by (rule sym[OF comp_associative2[OF plp_sharp_type FNOT_type NOT_type]])
  have s3: "(FORALL(X) \<circ>\<^sub>c exp_func(NOT, X)) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>
      = FORALL(X) \<circ>\<^sub>c (exp_func(NOT, X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>)"
    by (rule sym[OF comp_associative2[OF plp_sharp_type expNOTX_type FORALL_type]])
  have s4: "(NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> = exp_func(NOT, X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    using transpose_of_comp[OF plp_type NOT_type] plp_type NOT_type by simp
  have s5: "EXISTS(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>
      = NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp>)"
    using s1 s2 s3 s4 by simp
  have s6: "EXISTS(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>" using EXISTS_p_true .
  have not_p_lp_type[type_rule]: "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)) : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have notplp_sharp_type[type_rule]: "(NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have s7: "NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp>) = \<t>" using s5 s6 by simp
  have FNOTp_type[type_rule]: "FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have s8: "FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> = \<f>"
    using NOT_is_true_implies_false[OF FNOTp_type s7] .

  have not_all: "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>)"
  proof
    assume all_true: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>"
    have notp_type[type_rule]: "NOT \<circ>\<^sub>c p : X \<rightarrow> \<Omega>" by typecheck_cfuncs
    have all_true_meta: "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>" using all_true by auto
    have F1: "FORALL(X) \<circ>\<^sub>c ((NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
      using all_true_implies_FORALL_true[OF notp_type all_true_meta] .
    have assoc: "(NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj(X, \<one>) = NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))"
      by (rule sym[OF comp_associative2[OF lp_type p_type NOT_type]])
    have F2: "((NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp>"
      using assoc by simp
    have F3: "FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> = \<t>" using F1 F2 by simp
    then show False using s8 true_false_distinct by simp
  qed

  have not_all2: "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>)"
  proof
    assume assump: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>"
    have "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>"
    proof (intro allI impI)
      fix x assume x_type[type_rule]: "x \<in>\<^sub>c X"
      have "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>" using assump x_type by auto
      moreover have "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x"
        by (rule comp_associative2[OF x_type p_type NOT_type])
      ultimately show "(NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>" by simp
    qed
    then show False using not_all by simp
  qed

  have not_all3: "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> \<t>)"
  proof
    assume all_ne: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> \<t>"
    have "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>"
    proof (intro allI impI)
      fix x assume x_type[type_rule]: "x \<in>\<^sub>c X"
      have px_type[type_rule]: "p \<circ>\<^sub>c x \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
      have "p \<circ>\<^sub>c x \<noteq> \<t>" using all_ne x_type by auto
      then have "p \<circ>\<^sub>c x = \<f>" using true_false_only_truth_values[OF px_type] by auto
      then show "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>" using NOT_false_is_true by simp
    qed
    then show False using not_all2 by simp
  qed
  then show "\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = \<t>" by blast
qed

lemma EXISTS_elim:
  assumes EXISTS_p_true: "EXISTS(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>" and p_type: "p : X \<rightarrow> \<Omega>"
  shows "(\<And>x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t> \<Longrightarrow> Q) \<Longrightarrow> Q"
proof -
  assume elim: "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> p \<circ>\<^sub>c x = \<t> \<Longrightarrow> Q"
  obtain x where x_type: "x \<in>\<^sub>c X" and px_true: "p \<circ>\<^sub>c x = \<t>"
    using EXISTS_true_implies_exists_true[OF p_type EXISTS_p_true] by auto
  show Q using elim[OF x_type px_true] .
qed

lemma exists_true_implies_EXISTS_true:
  assumes p_type[type_rule]: "p : X \<rightarrow> \<Omega>" and exists_p_true: "\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = \<t>"
  shows "EXISTS(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
proof -
  obtain x0 where x0_type[type_rule]: "x0 \<in>\<^sub>c X" and px0_true: "p \<circ>\<^sub>c x0 = \<t>"
    using exists_p_true by auto
  have not_all: "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> \<t>)"
    using x0_type px0_true by auto
  have not_all2: "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>)"
  proof
    assume all_true: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>"
    have "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x0) = \<t>" using all_true x0_type by auto
    then have "NOT \<circ>\<^sub>c \<t> = \<t>" using px0_true by simp
    then have "\<f> = \<t>" using NOT_true_is_false by simp
    then show False using true_false_distinct by simp
  qed
  have lp_type[type_rule]: "left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X" by typecheck_cfuncs
  have notp_type[type_rule]: "NOT \<circ>\<^sub>c p : X \<rightarrow> \<Omega>" by typecheck_cfuncs
  have not_all3: "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>)"
  proof
    assume all_true: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>"
    have "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>"
    proof (intro allI impI)
      fix x assume x_type[type_rule]: "x \<in>\<^sub>c X"
      have "(NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>" using all_true x_type by auto
      moreover have "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x"
        by (rule comp_associative2[OF x_type p_type NOT_type])
      ultimately show "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<t>" by simp
    qed
    then show False using not_all2 by simp
  qed
  have FORALL_notp_ne: "FORALL(X) \<circ>\<^sub>c ((NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> \<noteq> \<t>"
  proof
    assume F_eq_t: "FORALL(X) \<circ>\<^sub>c ((NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
    have all_true2: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>"
    proof (intro allI impI)
      fix x assume x_type: "x \<in>\<^sub>c X"
      show "(NOT \<circ>\<^sub>c p) \<circ>\<^sub>c x = \<t>"
        using FORALL_true_implies_all_true[OF notp_type F_eq_t x_type] .
    qed
    then show False using not_all3 by simp
  qed
  have s1: "(NOT \<circ>\<^sub>c p) \<circ>\<^sub>c left_cart_proj(X, \<one>) = NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))"
    by (rule sym[OF comp_associative2[OF lp_type p_type NOT_type]])
  have FORALL_notplp_ne: "FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> \<noteq> \<t>"
    using FORALL_notp_ne s1 by simp
  have plp_type[type_rule]: "p \<circ>\<^sub>c left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have notNOTplp_type[type_rule]: "NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)) : X \<times>\<^sub>c \<one> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have FNOTplp_type[type_rule]: "FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have F_eq_f: "FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> = \<f>"
    using true_false_only_truth_values[OF FNOTplp_type] FORALL_notplp_ne by auto
  have NOT_F_true: "NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c (NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp>) = \<t>"
    using F_eq_f NOT_false_is_true by simp

  have s2: "(NOT \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>)))\<^sup>\<sharp> = exp_func(NOT, X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    using transpose_of_comp[OF plp_type NOT_type] plp_type NOT_type by simp
  have s3: "NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c (exp_func(NOT, X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>)) = \<t>"
    using NOT_F_true s2 by simp
  have plp_sharp_type[type_rule]: "(p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have expNOTX_type[type_rule]: "exp_func(NOT, X) : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>\<^bsup>X\<^esup>" by typecheck_cfuncs
  have s4: "FORALL(X) \<circ>\<^sub>c (exp_func(NOT, X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>)
      = (FORALL(X) \<circ>\<^sub>c exp_func(NOT, X)) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    by (rule comp_associative2[OF plp_sharp_type expNOTX_type FORALL_type])
  have FNOTX_type[type_rule]: "FORALL(X) \<circ>\<^sub>c exp_func(NOT, X) : \<Omega>\<^bsup>X\<^esup> \<rightarrow> \<Omega>" by typecheck_cfuncs
  have s5: "NOT \<circ>\<^sub>c ((FORALL(X) \<circ>\<^sub>c exp_func(NOT, X)) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>) = \<t>"
    using s3 s4 by simp
  have s6: "NOT \<circ>\<^sub>c ((FORALL(X) \<circ>\<^sub>c exp_func(NOT, X)) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>)
      = (NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c exp_func(NOT, X))) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp>"
    by (rule comp_associative2[OF plp_sharp_type FNOTX_type NOT_type])
  have s7: "(NOT \<circ>\<^sub>c (FORALL(X) \<circ>\<^sub>c exp_func(NOT, X))) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
    using s5 s6 by simp
  show "EXISTS(X) \<circ>\<^sub>c (p \<circ>\<^sub>c left_cart_proj(X, \<one>))\<^sup>\<sharp> = \<t>"
    unfolding EXISTS_def using s7 by simp
qed

end
