section \<open>Equivalence Classes and Coequalizers\<close>

theory Equivalence
  imports Truth
begin

text \<open>HOL bundles a relation's underlying set and monomorphism into a @{text "cset \<times> cfunc"} pair
  for @{text reflexive_on}/@{text symmetric_on}/@{text transitive_on}/@{text equiv_rel_on}/@{text
  const_on_rel}; flattened here to separate arguments, matching @{text subobject_of}'s convention
  throughout this port.\<close>
definition reflexive_on :: "cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> o" where
  "reflexive_on(X, R, m) \<longleftrightarrow> (subobject_of(R, m, X \<times>\<^sub>c X) \<and>
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> relative_member(\<langle>x,x\<rangle>, X \<times>\<^sub>c X, R, m)))"

definition symmetric_on :: "cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> o" where
  "symmetric_on(X, R, m) \<longleftrightarrow> (subobject_of(R, m, X \<times>\<^sub>c X) \<and>
    (\<forall>x y. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<longrightarrow>
      (relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, R, m) \<longrightarrow> relative_member(\<langle>y,x\<rangle>, X \<times>\<^sub>c X, R, m))))"

definition transitive_on :: "cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> o" where
  "transitive_on(X, R, m) \<longleftrightarrow> (subobject_of(R, m, X \<times>\<^sub>c X) \<and>
    (\<forall>x y z. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> z \<in>\<^sub>c X \<longrightarrow>
      (relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, R, m) \<and> relative_member(\<langle>y,z\<rangle>, X \<times>\<^sub>c X, R, m)
        \<longrightarrow> relative_member(\<langle>x,z\<rangle>, X \<times>\<^sub>c X, R, m))))"

definition equiv_rel_on :: "cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> o" where
  "equiv_rel_on(X, R, m) \<longleftrightarrow> (reflexive_on(X, R, m) \<and> symmetric_on(X, R, m) \<and> transitive_on(X, R, m))"

definition const_on_rel :: "cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> o" where
  "const_on_rel(X, R, m, f) \<longleftrightarrow>
    (\<forall>x y. x \<in>\<^sub>c X \<longrightarrow> y \<in>\<^sub>c X \<longrightarrow> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, R, m) \<longrightarrow> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y)"

lemma reflexive_def2:
  assumes reflexive_Y: "reflexive_on(X, Y, m)"
  assumes x_type: "x \<in>\<^sub>c X"
  shows "\<exists>y. y \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c y = \<langle>x,x\<rangle>"
proof -
  have Y_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using reflexive_Y unfolding reflexive_on_def subobject_of_def by auto
  have xx_type: "\<langle>x,x\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using x_type cfunc_prod_type by auto
  have xx_mem: "relative_member(\<langle>x,x\<rangle>, X \<times>\<^sub>c X, Y, m)"
    using reflexive_Y x_type unfolding reflexive_on_def by auto
  have xx_factorsthru: "\<langle>x,x\<rangle> factorsthru m" using xx_mem unfolding relative_member_def by auto
  obtain y where y_type: "y : \<one> \<rightarrow> Y" and y_eq: "m \<circ>\<^sub>c y = \<langle>x,x\<rangle>"
    using factors_through_def2[OF xx_type Y_type] xx_factorsthru by auto
  show ?thesis using y_type y_eq by auto
qed

lemma symmetric_def2:
  assumes symmetric_Y: "symmetric_on(X, Y, m)"
  assumes x_type: "x \<in>\<^sub>c X"
  assumes y_type: "y \<in>\<^sub>c X"
  assumes relation: "\<exists>v. v \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c v = \<langle>x,y\<rangle>"
  shows "\<exists>w. w \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c w = \<langle>y,x\<rangle>"
proof -
  obtain v where v_type: "v \<in>\<^sub>c Y" and v_eq: "m \<circ>\<^sub>c v = \<langle>x,y\<rangle>" using relation by auto
  have Y_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using symmetric_Y unfolding symmetric_on_def subobject_of_def by auto
  have Y_mono: "monomorphism(m)" using symmetric_Y unfolding symmetric_on_def subobject_of_def by auto
  have xy_type: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using x_type y_type cfunc_prod_type by auto
  have xy_factorsthru: "\<langle>x,y\<rangle> factorsthru m" using factors_through_def2[OF xy_type Y_type] v_type v_eq by auto
  have xy_mem: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, Y, m)"
    unfolding relative_member_def using xy_type Y_mono Y_type xy_factorsthru by auto
  have symmetric_prop: "\<forall>x y. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<longrightarrow>
      (relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, Y, m) \<longrightarrow> relative_member(\<langle>y,x\<rangle>, X \<times>\<^sub>c X, Y, m))"
    using symmetric_Y unfolding symmetric_on_def by auto
  have yx_mem: "relative_member(\<langle>y,x\<rangle>, X \<times>\<^sub>c X, Y, m)"
    using symmetric_prop[rule_format, where x=x and y=y] x_type y_type xy_mem by auto
  have yx_factorsthru: "\<langle>y,x\<rangle> factorsthru m" using yx_mem unfolding relative_member_def by auto
  have yx_type: "\<langle>y,x\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using x_type y_type cfunc_prod_type by auto
  obtain w where w_type: "w : \<one> \<rightarrow> Y" and w_eq: "m \<circ>\<^sub>c w = \<langle>y,x\<rangle>"
    using factors_through_def2[OF yx_type Y_type] yx_factorsthru by auto
  show ?thesis using w_type w_eq by auto
qed

lemma transitive_def2:
  assumes transitive_Y: "transitive_on(X, Y, m)"
  assumes x_type: "x \<in>\<^sub>c X"
  assumes y_type: "y \<in>\<^sub>c X"
  assumes z_type: "z \<in>\<^sub>c X"
  assumes relation1: "\<exists>v. v \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c v = \<langle>x,y\<rangle>"
  assumes relation2: "\<exists>w. w \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c w = \<langle>y,z\<rangle>"
  shows "\<exists>u. u \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c u = \<langle>x,z\<rangle>"
proof -
  obtain v where v_type: "v \<in>\<^sub>c Y" and v_eq: "m \<circ>\<^sub>c v = \<langle>x,y\<rangle>" using relation1 by auto
  obtain w where w_type: "w \<in>\<^sub>c Y" and w_eq: "m \<circ>\<^sub>c w = \<langle>y,z\<rangle>" using relation2 by auto
  have Y_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using transitive_Y unfolding transitive_on_def subobject_of_def by auto
  have Y_mono: "monomorphism(m)" using transitive_Y unfolding transitive_on_def subobject_of_def by auto
  have xy_type: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using x_type y_type cfunc_prod_type by auto
  have yz_type: "\<langle>y,z\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using y_type z_type cfunc_prod_type by auto
  have xy_factorsthru: "\<langle>x,y\<rangle> factorsthru m" using factors_through_def2[OF xy_type Y_type] v_type v_eq by auto
  have yz_factorsthru: "\<langle>y,z\<rangle> factorsthru m" using factors_through_def2[OF yz_type Y_type] w_type w_eq by auto
  have xy_mem: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, Y, m)"
    unfolding relative_member_def using xy_type Y_mono Y_type xy_factorsthru by auto
  have yz_mem: "relative_member(\<langle>y,z\<rangle>, X \<times>\<^sub>c X, Y, m)"
    unfolding relative_member_def using yz_type Y_mono Y_type yz_factorsthru by auto
  have transitive_prop: "\<forall>x y z. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> z \<in>\<^sub>c X \<longrightarrow>
      (relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, Y, m) \<and> relative_member(\<langle>y,z\<rangle>, X \<times>\<^sub>c X, Y, m)
        \<longrightarrow> relative_member(\<langle>x,z\<rangle>, X \<times>\<^sub>c X, Y, m))"
    using transitive_Y unfolding transitive_on_def by auto
  have xz_mem: "relative_member(\<langle>x,z\<rangle>, X \<times>\<^sub>c X, Y, m)"
    using transitive_prop[rule_format, where x=x and y=y and z=z] x_type y_type z_type xy_mem yz_mem by auto
  have xz_factorsthru: "\<langle>x,z\<rangle> factorsthru m" using xz_mem unfolding relative_member_def by auto
  have xz_type: "\<langle>x,z\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using x_type z_type cfunc_prod_type by auto
  obtain u where u_type: "u : \<one> \<rightarrow> Y" and u_eq: "m \<circ>\<^sub>c u = \<langle>x,z\<rangle>"
    using factors_through_def2[OF xz_type Y_type] xz_factorsthru by auto
  show ?thesis using u_type u_eq by auto
qed

text \<open>The lemma below corresponds to Exercise 2.3.3 in Halvorson.\<close>
lemma kernel_pair_equiv_rel:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "equiv_rel_on(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
  unfolding equiv_rel_on_def
proof (intro conjI)
  show "reflexive_on(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
    unfolding reflexive_on_def
  proof (intro conjI allI impI)
    show "subobject_of(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X), X \<times>\<^sub>c X)"
      using kernel_pair_subset[OF f_type] by simp
  next
    fix x assume x_type: "x \<in>\<^sub>c X"
    show "relative_member(\<langle>x,x\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
      using fibered_product_pair_member[OF f_type f_type x_type x_type] by simp
  qed
next
  show "symmetric_on(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
    unfolding symmetric_on_def
  proof (intro conjI allI impI)
    show "subobject_of(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X), X \<times>\<^sub>c X)"
      using kernel_pair_subset[OF f_type] by simp
  next
    fix x y
    assume "x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X"
    then have x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X" by auto
    assume xy_in: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
    have "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
      using fibered_product_pair_member[OF f_type f_type x_type y_type] xy_in by simp
    then show "relative_member(\<langle>y,x\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
      using fibered_product_pair_member[OF f_type f_type y_type x_type] by simp
  qed
next
  show "transitive_on(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
    unfolding transitive_on_def
  proof (intro conjI allI impI)
    show "subobject_of(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X), X \<times>\<^sub>c X)"
      using kernel_pair_subset[OF f_type] by simp
  next
    fix x y z
    assume "x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> z \<in>\<^sub>c X"
    then have x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X" and z_type: "z \<in>\<^sub>c X" by auto
    assume "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X)) \<and>
        relative_member(\<langle>y,z\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
    then have xy_in: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
        and yz_in: "relative_member(\<langle>y,z\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))" by auto
    have eqn1: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y" using fibered_product_pair_member[OF f_type f_type x_type y_type] xy_in by simp
    have eqn2: "f \<circ>\<^sub>c y = f \<circ>\<^sub>c z" using fibered_product_pair_member[OF f_type f_type y_type z_type] yz_in by simp
    show "relative_member(\<langle>x,z\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
      using fibered_product_pair_member[OF f_type f_type x_type z_type] eqn1 eqn2 by simp
  qed
qed

text \<open>The axiomatization below corresponds to Axiom 6 (Equivalence Classes) in Halvorson. HOL
  bundles the equivalence relation's underlying set and monomorphism into a @{text "cset \<times> cfunc"}
  pair here too; flattened to separate arguments as throughout this port. No custom mixfix is
  attempted to preserve HOL's infix @{text "X \<sslash> R"} surface syntax, matching the established
  convention (@{text subobject_of} etc. in @{text Equalizer.thy}).\<close>
axiomatization
  quotient_set :: "cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cset" and
  equiv_class :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc" and
  quotient_func :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc"
where
  equiv_class_type[type_rule]: "equiv_rel_on(X, R, m) \<Longrightarrow> equiv_class(R, m) : X \<rightarrow> quotient_set(X, R, m)" and
  equiv_class_eq: "equiv_rel_on(X, R, m) \<Longrightarrow> \<langle>x, y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X \<Longrightarrow>
    relative_member(\<langle>x, y\<rangle>, X \<times>\<^sub>c X, R, m) \<longleftrightarrow> equiv_class(R, m) \<circ>\<^sub>c x = equiv_class(R, m) \<circ>\<^sub>c y" and
  quotient_func_type[type_rule]:
    "equiv_rel_on(X, R, m) \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> const_on_rel(X, R, m, f) \<Longrightarrow>
      quotient_func(f, R, m) : quotient_set(X, R, m) \<rightarrow> Y" and
  quotient_func_eq: "equiv_rel_on(X, R, m) \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> const_on_rel(X, R, m, f) \<Longrightarrow>
     quotient_func(f, R, m) \<circ>\<^sub>c equiv_class(R, m) = f" and
  quotient_func_unique: "equiv_rel_on(X, R, m) \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> const_on_rel(X, R, m, f) \<Longrightarrow>
    h : quotient_set(X, R, m) \<rightarrow> Y \<Longrightarrow> h \<circ>\<^sub>c equiv_class(R, m) = f \<Longrightarrow> h = quotient_func(f, R, m)"
text \<open>Note that @{const quotient_set} corresponds to $X/R$, @{const equiv_class} corresponds to the
  canonical quotient mapping $q$, and @{const quotient_func} corresponds to $\bar{f}$ in Halvorson's
  formulation of this axiom.\<close>

abbreviation equiv_class_ap :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "equiv_class_ap(x, R, m) \<equiv> equiv_class(R, m) \<circ>\<^sub>c x"

subsection \<open>Coequalizers\<close>

text \<open>The definition below corresponds to a comment after Axiom 6 (Equivalence Classes) in Halvorson.\<close>
definition coequalizer :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> o" where
  "coequalizer(E, m, f, g) \<longleftrightarrow> (\<exists> X Y. (f : Y \<rightarrow> X) \<and> (g : Y \<rightarrow> X) \<and> (m : X \<rightarrow> E)
    \<and> (m \<circ>\<^sub>c f = m \<circ>\<^sub>c g)
    \<and> (\<forall> h F. ((h : X \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h)))"

lemma coequalizer_def2:
  assumes f_type: "f : Y \<rightarrow> X" and g_type: "g : Y \<rightarrow> X" and m_type: "m : X \<rightarrow> E"
  shows "coequalizer(E, m, f, g) \<longleftrightarrow>
    (m \<circ>\<^sub>c f = m \<circ>\<^sub>c g)
      \<and> (\<forall> h F. ((h : X \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h))"
proof (rule iffI)
  assume "coequalizer(E, m, f, g)"
  then obtain X' Y' where f_type': "f : Y' \<rightarrow> X'" and g_type': "g : Y' \<rightarrow> X'" and m_type': "m : X' \<rightarrow> E"
      and mf_mg: "m \<circ>\<^sub>c f = m \<circ>\<^sub>c g"
      and uniq: "\<forall> h F. ((h : X' \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h)"
    unfolding coequalizer_def by auto
  have XX': "X = X'" using f_type f_type' unfolding cfunc_type_def by auto
  show "(m \<circ>\<^sub>c f = m \<circ>\<^sub>c g) \<and> (\<forall> h F. ((h : X \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h))"
    using mf_mg uniq XX' by simp
next
  assume rhs: "(m \<circ>\<^sub>c f = m \<circ>\<^sub>c g) \<and> (\<forall> h F. ((h : X \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h))"
  show "coequalizer(E, m, f, g)"
    unfolding coequalizer_def
    using f_type g_type m_type rhs by auto
qed

text \<open>The lemma below corresponds to Exercise 2.3.1 in Halvorson.\<close>
lemma coequalizer_unique:
  assumes eq1: "coequalizer(E, m, f, g)" and eq2: "coequalizer(F, n, f, g)"
  shows "E \<cong> F"
proof -
  obtain X Y where f_type: "f : Y \<rightarrow> X" and g_type: "g : Y \<rightarrow> X" and m_type: "m : X \<rightarrow> E"
      and mf_mg: "m \<circ>\<^sub>c f = m \<circ>\<^sub>c g"
      and m_uniq: "\<forall> h F'. ((h : X \<rightarrow> F') \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F') \<and> k \<circ>\<^sub>c m = h)"
    using eq1 unfolding coequalizer_def by auto
  obtain X' Y' where f_type': "f : Y' \<rightarrow> X'" and g_type': "g : Y' \<rightarrow> X'" and n_type: "n : X' \<rightarrow> F"
      and nf_ng: "n \<circ>\<^sub>c f = n \<circ>\<^sub>c g"
      and n_uniq: "\<forall> h F'. ((h : X' \<rightarrow> F') \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> F') \<and> k \<circ>\<^sub>c n = h)"
    using eq2 unfolding coequalizer_def by auto
  have XX': "X = X'" using f_type f_type' unfolding cfunc_type_def by auto
  have n_type': "n : X \<rightarrow> F" using n_type XX' by simp
  have nf_ng': "n \<circ>\<^sub>c f = n \<circ>\<^sub>c g" using nf_ng by simp
  have n_uniq': "\<forall> h F'. ((h : X \<rightarrow> F') \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> F') \<and> k \<circ>\<^sub>c n = h)"
    using n_uniq XX' by simp

  have ex1k: "\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = n"
    using m_uniq[rule_format, where h=n and F'=F] n_type' nf_ng' by auto
  then obtain k where k_type: "k : E \<rightarrow> F" and k_eq: "k \<circ>\<^sub>c m = n" by auto

  have ex1k': "\<exists>! k'. (k' : F \<rightarrow> E) \<and> k' \<circ>\<^sub>c n = m"
    using n_uniq'[rule_format, where h=m and F'=E] m_type mf_mg by auto
  then obtain k' where k'_type: "k' : F \<rightarrow> E" and k'_eq: "k' \<circ>\<^sub>c n = m" by auto

  have idF_type: "id(F) : F \<rightarrow> F" by (rule id_type)
  have idF_eq: "id(F) \<circ>\<^sub>c n = n" using id_left_unit2[OF n_type'] by simp
  have kk'_type: "(k \<circ>\<^sub>c k') : F \<rightarrow> F" using k'_type k_type comp_type by blast
  have kk'_eq: "(k \<circ>\<^sub>c k') \<circ>\<^sub>c n = n"
  proof -
    have "(k \<circ>\<^sub>c k') \<circ>\<^sub>c n = k \<circ>\<^sub>c (k' \<circ>\<^sub>c n)" using comp_associative2[OF n_type' k'_type k_type] by simp
    also have "... = k \<circ>\<^sub>c m" using k'_eq by simp
    also have "... = n" using k_eq by simp
    finally show ?thesis by simp
  qed
  have ex1kk: "\<exists>! kk. (kk : F \<rightarrow> F) \<and> kk \<circ>\<^sub>c n = n"
    using n_uniq'[rule_format, where h=n and F'=F] n_type' nf_ng' by auto
  then obtain kk where kk_unique: "\<forall>kkX. (kkX : F \<rightarrow> F \<and> kkX \<circ>\<^sub>c n = n) \<longrightarrow> kkX = kk" by auto
  have e1: "k \<circ>\<^sub>c k' = kk" using kk_unique[rule_format, where kkX="k \<circ>\<^sub>c k'"] kk'_type kk'_eq by auto
  have e2: "id(F) = kk" using kk_unique[rule_format, where kkX="id(F)"] idF_type idF_eq by auto
  have kk'_eq_id: "k \<circ>\<^sub>c k' = id(F)" using e1 e2 by simp

  have idE_type: "id(E) : E \<rightarrow> E" by (rule id_type)
  have idE_eq: "id(E) \<circ>\<^sub>c m = m" using id_left_unit2[OF m_type] by simp
  have k'k_type: "(k' \<circ>\<^sub>c k) : E \<rightarrow> E" using k_type k'_type comp_type by blast
  have k'k_eq: "(k' \<circ>\<^sub>c k) \<circ>\<^sub>c m = m"
  proof -
    have "(k' \<circ>\<^sub>c k) \<circ>\<^sub>c m = k' \<circ>\<^sub>c (k \<circ>\<^sub>c m)" using comp_associative2[OF m_type k_type k'_type] by simp
    also have "... = k' \<circ>\<^sub>c n" using k_eq by simp
    also have "... = m" using k'_eq by simp
    finally show ?thesis by simp
  qed
  have ex1jj: "\<exists>! jj. (jj : E \<rightarrow> E) \<and> jj \<circ>\<^sub>c m = m"
    using m_uniq[rule_format, where h=m and F'=E] m_type mf_mg by auto
  then obtain jj where jj_unique: "\<forall>jjX. (jjX : E \<rightarrow> E \<and> jjX \<circ>\<^sub>c m = m) \<longrightarrow> jjX = jj" by auto
  have e3: "k' \<circ>\<^sub>c k = jj" using jj_unique[rule_format, where jjX="k' \<circ>\<^sub>c k"] k'k_type k'k_eq by auto
  have e4: "id(E) = jj" using jj_unique[rule_format, where jjX="id(E)"] idE_type idE_eq by auto
  have k'k_eq_id: "k' \<circ>\<^sub>c k = id(E)" using e3 e4 by simp

  have k_iso: "isomorphism(k)"
    using isomorphism_def3[OF k_type] k'_type k'k_eq_id kk'_eq_id by auto
  show "E \<cong> F" unfolding is_isomorphic_def using k_type k_iso by auto
qed

text \<open>The lemma below corresponds to Exercise 2.3.2 in Halvorson.\<close>
lemma coequalizer_is_epimorphism:
  assumes ce: "coequalizer(E, m, f, g)"
  shows "epimorphism(m)"
proof -
  obtain X Y where f_type: "f : Y \<rightarrow> X" and g_type: "g : Y \<rightarrow> X" and m_type: "m : X \<rightarrow> E"
      and mf_mg: "m \<circ>\<^sub>c f = m \<circ>\<^sub>c g"
      and uniq: "\<forall> h F. ((h : X \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h)"
    using ce unfolding coequalizer_def by auto
  show ?thesis
    unfolding epimorphism_def3[OF m_type]
  proof (intro allI impI)
    fix k h A
    assume "k : E \<rightarrow> A \<and> h : E \<rightarrow> A"
    then have k_type: "k : E \<rightarrow> A" and h_type: "h : E \<rightarrow> A" by auto
    assume km_hm: "k \<circ>\<^sub>c m = h \<circ>\<^sub>c m"

    have km_type: "k \<circ>\<^sub>c m : X \<rightarrow> A" using m_type k_type comp_type by blast
    have kmf_eq_kmg: "(k \<circ>\<^sub>c m) \<circ>\<^sub>c f = (k \<circ>\<^sub>c m) \<circ>\<^sub>c g"
    proof -
      have "(k \<circ>\<^sub>c m) \<circ>\<^sub>c f = k \<circ>\<^sub>c (m \<circ>\<^sub>c f)" using comp_associative2[OF f_type m_type k_type] by simp
      also have "... = k \<circ>\<^sub>c (m \<circ>\<^sub>c g)" using mf_mg by simp
      also have "... = (k \<circ>\<^sub>c m) \<circ>\<^sub>c g" using comp_associative2[OF g_type m_type k_type] by simp
      finally show ?thesis by simp
    qed

    have ex1l: "\<exists>! l. (l : E \<rightarrow> A) \<and> l \<circ>\<^sub>c m = k \<circ>\<^sub>c m"
      using uniq[rule_format, where h="k \<circ>\<^sub>c m" and F=A] km_type kmf_eq_kmg by auto
    then obtain l where l_unique: "\<forall>lX. (lX : E \<rightarrow> A \<and> lX \<circ>\<^sub>c m = k \<circ>\<^sub>c m) \<longrightarrow> lX = l" by auto

    have k_eq_l: "k = l" using l_unique[rule_format, where lX=k] k_type by auto
    have h_eq_l: "h = l" using l_unique[rule_format, where lX=h] h_type km_hm by auto
    show "k = h" using k_eq_l h_eq_l by simp
  qed
qed

lemma canonical_quotient_map_is_coequalizer:
  assumes equiv_XRm: "equiv_rel_on(X, R, m)"
  shows "coequalizer(quotient_set(X, R, m), equiv_class(R, m),
                     left_cart_proj(X, X) \<circ>\<^sub>c m, right_cart_proj(X, X) \<circ>\<^sub>c m)"
proof -
  have m_type: "m : R \<rightarrow> X \<times>\<^sub>c X"
    using equiv_XRm unfolding equiv_rel_on_def reflexive_on_def subobject_of_def by auto
  have m_mono: "monomorphism(m)"
    using equiv_XRm unfolding equiv_rel_on_def reflexive_on_def subobject_of_def by auto
  have lp_type: "left_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)
  have lpm_type: "left_cart_proj(X, X) \<circ>\<^sub>c m : R \<rightarrow> X" using m_type lp_type comp_type by blast
  have rpm_type: "right_cart_proj(X, X) \<circ>\<^sub>c m : R \<rightarrow> X" using m_type rp_type comp_type by blast
  have ec_type: "equiv_class(R, m) : X \<rightarrow> quotient_set(X, R, m)" using equiv_class_type[OF equiv_XRm] by simp

  show ?thesis
    unfolding coequalizer_def2[OF lpm_type rpm_type ec_type]
  proof (intro conjI)
    show "equiv_class(R, m) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m) = equiv_class(R, m) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)"
    proof (rule one_separator[where X=R and Y="quotient_set(X, R, m)"])
      show "equiv_class(R, m) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m) : R \<rightarrow> quotient_set(X, R, m)"
        using lpm_type ec_type comp_type by blast
      show "equiv_class(R, m) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m) : R \<rightarrow> quotient_set(X, R, m)"
        using rpm_type ec_type comp_type by blast
      fix x assume x_type: "x : \<one> \<rightarrow> R"
      have mx_type: "m \<circ>\<^sub>c x \<in>\<^sub>c X \<times>\<^sub>c X" using x_type m_type comp_type by blast
      obtain a b where a_type: "a \<in>\<^sub>c X" and b_type: "b \<in>\<^sub>c X" and mx_eq: "m \<circ>\<^sub>c x = \<langle>a,b\<rangle>"
        using cart_prod_decomp[OF mx_type] by auto
      have ab_type: "\<langle>a,b\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using a_type b_type cfunc_prod_type by auto
      have ab_factorsthru: "\<langle>a,b\<rangle> factorsthru m" using factors_through_def2[OF ab_type m_type] x_type mx_eq by auto
      have ab_mem: "relative_member(\<langle>a,b\<rangle>, X \<times>\<^sub>c X, R, m)"
        unfolding relative_member_def using ab_type m_mono m_type ab_factorsthru by auto
      have ec_ab_eq: "equiv_class(R, m) \<circ>\<^sub>c a = equiv_class(R, m) \<circ>\<^sub>c b"
        using equiv_class_eq[OF equiv_XRm ab_type] ab_mem by simp
      show "(equiv_class(R, m) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c x =
          (equiv_class(R, m) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c x"
      proof -
        have "(equiv_class(R, m) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c x
            = equiv_class(R, m) \<circ>\<^sub>c ((left_cart_proj(X, X) \<circ>\<^sub>c m) \<circ>\<^sub>c x)"
          using comp_associative2[OF x_type lpm_type ec_type] by simp
        also have "... = equiv_class(R, m) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c (m \<circ>\<^sub>c x))"
          using comp_associative2[OF x_type m_type lp_type] by simp
        also have "... = equiv_class(R, m) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c \<langle>a,b\<rangle>)" using mx_eq by simp
        also have "... = equiv_class(R, m) \<circ>\<^sub>c a" using left_cart_proj_cfunc_prod[OF a_type b_type] by simp
        also have "... = equiv_class(R, m) \<circ>\<^sub>c b" using ec_ab_eq by simp
        also have "... = equiv_class(R, m) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c \<langle>a,b\<rangle>)"
          using right_cart_proj_cfunc_prod[OF a_type b_type] by simp
        also have "... = equiv_class(R, m) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c (m \<circ>\<^sub>c x))" using mx_eq by simp
        also have "... = equiv_class(R, m) \<circ>\<^sub>c ((right_cart_proj(X, X) \<circ>\<^sub>c m) \<circ>\<^sub>c x)"
          using comp_associative2[OF x_type m_type rp_type] by simp
        also have "... = (equiv_class(R, m) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c x"
          using comp_associative2[OF x_type rpm_type ec_type] by simp
        finally show ?thesis by simp
      qed
    qed
  next
    show "\<forall> h F. (h : X \<rightarrow> F \<and> h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m) = h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)) \<longrightarrow>
        (\<exists>! k. k : quotient_set(X, R, m) \<rightarrow> F \<and> k \<circ>\<^sub>c equiv_class(R, m) = h)"
    proof (intro allI impI)
      fix h F
      assume "h : X \<rightarrow> F \<and> h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m) = h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)"
      then have h_type: "h : X \<rightarrow> F"
          and h_eq: "h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m) = h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)" by auto

      have const_h: "const_on_rel(X, R, m, h)"
        unfolding const_on_rel_def
      proof (intro allI impI)
        fix x y assume x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X"
        assume xy_mem: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, R, m)"
        have xy_type: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using x_type y_type cfunc_prod_type by auto
        have "\<langle>x,y\<rangle> factorsthru m" using xy_mem unfolding relative_member_def by auto
        then obtain xy where xy_R_type: "xy \<in>\<^sub>c R" and m_xy_eq: "m \<circ>\<^sub>c xy = \<langle>x,y\<rangle>"
          using factors_through_def2[OF xy_type m_type] by auto
        have step: "(h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c xy = (h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c xy"
          using h_eq by simp
        have lhs_eq: "(h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c xy = h \<circ>\<^sub>c x"
        proof -
          have "(h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c xy = h \<circ>\<^sub>c ((left_cart_proj(X, X) \<circ>\<^sub>c m) \<circ>\<^sub>c xy)"
            using comp_associative2[OF xy_R_type lpm_type h_type] by simp
          also have "... = h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c (m \<circ>\<^sub>c xy))"
            using comp_associative2[OF xy_R_type m_type lp_type] by simp
          also have "... = h \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,y\<rangle>)" using m_xy_eq by simp
          also have "... = h \<circ>\<^sub>c x" using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
          finally show ?thesis by simp
        qed
        have rhs_eq: "(h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c xy = h \<circ>\<^sub>c y"
        proof -
          have "(h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c m)) \<circ>\<^sub>c xy = h \<circ>\<^sub>c ((right_cart_proj(X, X) \<circ>\<^sub>c m) \<circ>\<^sub>c xy)"
            using comp_associative2[OF xy_R_type rpm_type h_type] by simp
          also have "... = h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c (m \<circ>\<^sub>c xy))"
            using comp_associative2[OF xy_R_type m_type rp_type] by simp
          also have "... = h \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,y\<rangle>)" using m_xy_eq by simp
          also have "... = h \<circ>\<^sub>c y" using right_cart_proj_cfunc_prod[OF x_type y_type] by simp
          finally show ?thesis by simp
        qed
        show "h \<circ>\<^sub>c x = h \<circ>\<^sub>c y" using step lhs_eq rhs_eq by simp
      qed

      have qf_type: "quotient_func(h, R, m) : quotient_set(X, R, m) \<rightarrow> F"
        using quotient_func_type[OF equiv_XRm h_type const_h] by simp
      have qf_eq: "quotient_func(h, R, m) \<circ>\<^sub>c equiv_class(R, m) = h"
        using quotient_func_eq[OF equiv_XRm h_type const_h] by simp

      show "\<exists>! k. k : quotient_set(X, R, m) \<rightarrow> F \<and> k \<circ>\<^sub>c equiv_class(R, m) = h"
      proof (rule ex1I[where a="quotient_func(h, R, m)"])
        show "quotient_func(h, R, m) : quotient_set(X, R, m) \<rightarrow> F \<and> quotient_func(h, R, m) \<circ>\<^sub>c equiv_class(R, m) = h"
          using qf_type qf_eq by simp
      next
        fix k assume "k : quotient_set(X, R, m) \<rightarrow> F \<and> k \<circ>\<^sub>c equiv_class(R, m) = h"
        then have k_type: "k : quotient_set(X, R, m) \<rightarrow> F" and k_eq: "k \<circ>\<^sub>c equiv_class(R, m) = h" by auto
        show "k = quotient_func(h, R, m)"
          using quotient_func_unique[OF equiv_XRm h_type const_h k_type k_eq] by simp
      qed
    qed
  qed
qed

lemma canonical_quot_map_is_epi:
  assumes equiv_XRm: "equiv_rel_on(X, R, m)"
  shows "epimorphism(equiv_class(R, m))"
  using coequalizer_is_epimorphism[OF canonical_quotient_map_is_coequalizer[OF equiv_XRm]] by simp

subsection \<open>Regular Epimorphisms\<close>

text \<open>The definition below corresponds to Definition 2.3.4 in Halvorson.\<close>
definition regular_epimorphism :: "cfunc \<Rightarrow> o" where
  "regular_epimorphism(f) \<longleftrightarrow> (\<exists> g h. coequalizer(codomain(f), f, g, h))"

text \<open>The lemma below corresponds to Exercise 2.3.5 in Halvorson.\<close>
lemma reg_epi_and_mono_is_iso:
  assumes f_type: "f : X \<rightarrow> Y" and f_reg_epi: "regular_epimorphism(f)" and f_mono: "monomorphism(f)"
  shows "isomorphism(f)"
proof -
  obtain g h where gh_def: "coequalizer(codomain(f), f, g, h)"
    using f_reg_epi unfolding regular_epimorphism_def by auto
  have cod_f: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  have gh_coeq: "coequalizer(Y, f, g, h)" using gh_def cod_f by simp
  obtain X' W where g_type': "g : W \<rightarrow> X'" and h_type': "h : W \<rightarrow> X'" and f_type': "f : X' \<rightarrow> Y"
      and fg_eq_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
      and coeq_uniq': "\<forall> h' F. ((h' : X' \<rightarrow> F) \<and> (h' \<circ>\<^sub>c g = h' \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : Y \<rightarrow> F) \<and> k \<circ>\<^sub>c f = h')"
    using gh_coeq unfolding coequalizer_def by auto
  have XX': "X' = X" using f_type f_type' unfolding cfunc_type_def by auto
  have g_type: "g : W \<rightarrow> X" using g_type' XX' by simp
  have h_type: "h : W \<rightarrow> X" using h_type' XX' by simp
  have coeq_uniq: "\<forall> h' F. ((h' : X \<rightarrow> F) \<and> (h' \<circ>\<^sub>c g = h' \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : Y \<rightarrow> F) \<and> k \<circ>\<^sub>c f = h')"
    using coeq_uniq' XX' by simp

  have f_mono_rule: "\<forall> g' h' A. g' : A \<rightarrow> X \<and> h' : A \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c g' = f \<circ>\<^sub>c h' \<longrightarrow> g' = h')"
    using monomorphism_def3[OF f_type] f_mono by simp
  have g_eq_h: "g = h" using f_mono_rule[rule_format, where g'=g and h'=h and A=W] g_type h_type fg_eq_fh by auto

  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have idX_g_eq_idX_h: "id(X) \<circ>\<^sub>c g = id(X) \<circ>\<^sub>c h" using g_eq_h by simp

  have ex1j: "\<exists>! j. (j : Y \<rightarrow> X) \<and> j \<circ>\<^sub>c f = id(X)"
    using coeq_uniq[rule_format, where h'="id(X)" and F=X] idX_type idX_g_eq_idX_h by auto
  then obtain j where j_type: "j : Y \<rightarrow> X" and j_eq: "j \<circ>\<^sub>c f = id(X)" by auto

  have f_epi: "epimorphism(f)" using coequalizer_is_epimorphism[OF gh_coeq] by simp

  have idY_f_eq: "id(Y) \<circ>\<^sub>c f = (f \<circ>\<^sub>c j) \<circ>\<^sub>c f"
  proof -
    have "id(Y) \<circ>\<^sub>c f = f" using id_left_unit2[OF f_type] by simp
    also have "... = f \<circ>\<^sub>c id(X)" using id_right_unit2[OF f_type] by simp
    also have "... = f \<circ>\<^sub>c (j \<circ>\<^sub>c f)" using j_eq by simp
    also have "... = (f \<circ>\<^sub>c j) \<circ>\<^sub>c f" using comp_associative2[OF f_type j_type f_type] by simp
    finally show ?thesis by simp
  qed

  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have fj_type: "f \<circ>\<^sub>c j : Y \<rightarrow> Y" using j_type f_type comp_type by blast
  have f_epi_rule: "\<forall> g' h' A. g' : Y \<rightarrow> A \<and> h' : Y \<rightarrow> A \<longrightarrow> (g' \<circ>\<^sub>c f = h' \<circ>\<^sub>c f \<longrightarrow> g' = h')"
    using epimorphism_def3[OF f_type] f_epi by simp
  have idY_eq_fj: "id(Y) = f \<circ>\<^sub>c j"
    using f_epi_rule[rule_format, where g'="id(Y)" and h'="f \<circ>\<^sub>c j" and A=Y] idY_type fj_type idY_f_eq by auto
  have fj_eq_idY: "f \<circ>\<^sub>c j = id(Y)" using idY_eq_fj by simp

  show ?thesis
    using isomorphism_def3[OF f_type] j_type j_eq fj_eq_idY by auto
qed

text \<open>The two lemmas below correspond to Proposition 2.3.6 in Halvorson.\<close>
lemma epimorphism_coequalizer_kernel_pair:
  assumes f_type: "f : X \<rightarrow> Y" and f_epi: "epimorphism(f)"
  shows "coequalizer(Y, f, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
proof -
  have lp_type: "fibered_product_left_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type f_type] by simp
  have rp_type: "fibered_product_right_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_right_proj_type[OF f_type f_type] by simp

  show ?thesis
    unfolding coequalizer_def2[OF lp_type rp_type f_type]
  proof (intro conjI)
    show "f \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = f \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
      using fibered_product_proj_eq[OF f_type f_type] by simp
  next
    show "\<forall> h F. (h : X \<rightarrow> F \<and> h \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = h \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)) \<longrightarrow>
        (\<exists>! k. k : Y \<rightarrow> F \<and> k \<circ>\<^sub>c f = h)"
    proof (intro allI impI)
      fix g E
      assume "g : X \<rightarrow> E \<and> g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
      then have g_type: "g : X \<rightarrow> E"
          and g_eq: "g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)" by auto

      have equiv_kp: "equiv_rel_on(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
        using kernel_pair_equiv_rel[OF f_type] by simp

      define q where "q = equiv_class(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
      define Q where "Q = quotient_set(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
      have q_type: "q : X \<rightarrow> Q" unfolding q_def Q_def using equiv_class_type[OF equiv_kp] by simp

      have f_const: "const_on_rel(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X), f)"
        unfolding const_on_rel_def
      proof (intro allI impI)
        fix x y assume x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X"
        assume "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
        then show "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
          using fibered_product_pair_member[OF f_type f_type x_type y_type] by simp
      qed

      define f_bar where "f_bar = quotient_func(f, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
      have f_bar_type: "f_bar : Q \<rightarrow> Y"
        unfolding f_bar_def Q_def using quotient_func_type[OF equiv_kp f_type f_const] by simp
      have f_eqs: "f_bar \<circ>\<^sub>c q = f"
        unfolding f_bar_def q_def using quotient_func_eq[OF equiv_kp f_type f_const] by simp

      have q_coequalizer: "coequalizer(Q, q, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
      proof -
        have raw: "coequalizer(quotient_set(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X)),
            equiv_class(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X)),
            fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
          using canonical_quotient_map_is_coequalizer[OF equiv_kp]
          unfolding fibered_product_left_proj_def fibered_product_right_proj_def by simp
        show ?thesis using raw unfolding q_def Q_def by simp
      qed
      have q_epi: "epimorphism(q)" using coequalizer_is_epimorphism[OF q_coequalizer] by simp
      have q_eq: "q \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = q \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
        using q_coequalizer coequalizer_def2[OF lp_type rp_type q_type] by simp

      have kpc: "\<exists>! b. b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (Q \<^bsub>f_bar\<^esub>\<times>\<^sub>c\<^bsub>f_bar\<^esub> Q) \<and>
          fibered_product_left_proj(Q, f_bar, f_bar, Q) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) \<and>
          fibered_product_right_proj(Q, f_bar, f_bar, Q) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) \<and>
          epimorphism(b)"
        using kernel_pair_connection[OF f_type q_type q_epi f_eqs q_eq f_bar_type] by simp
      then obtain b where b_type: "b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (Q \<^bsub>f_bar\<^esub>\<times>\<^sub>c\<^bsub>f_bar\<^esub> Q)"
          and left_b_eq: "fibered_product_left_proj(Q, f_bar, f_bar, Q) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)"
          and right_b_eq: "fibered_product_right_proj(Q, f_bar, f_bar, Q) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
          and b_epi: "epimorphism(b)" by auto

      have lpQ_type: "fibered_product_left_proj(Q, f_bar, f_bar, Q) : (Q \<^bsub>f_bar\<^esub>\<times>\<^sub>c\<^bsub>f_bar\<^esub> Q) \<rightarrow> Q"
        using fibered_product_left_proj_type[OF f_bar_type f_bar_type] by simp
      have rpQ_type: "fibered_product_right_proj(Q, f_bar, f_bar, Q) : (Q \<^bsub>f_bar\<^esub>\<times>\<^sub>c\<^bsub>f_bar\<^esub> Q) \<rightarrow> Q"
        using fibered_product_right_proj_type[OF f_bar_type f_bar_type] by simp

      have eq_projs: "fibered_product_left_proj(Q, f_bar, f_bar, Q) = fibered_product_right_proj(Q, f_bar, f_bar, Q)"
      proof -
        have "fibered_product_left_proj(Q, f_bar, f_bar, Q) \<circ>\<^sub>c b = fibered_product_right_proj(Q, f_bar, f_bar, Q) \<circ>\<^sub>c b"
          using left_b_eq right_b_eq q_eq by simp
        then show ?thesis
          using b_epi epimorphism_def3[OF b_type] lpQ_type rpQ_type by auto
      qed

      have mono_fbar: "monomorphism(f_bar)"
        using kern_pair_proj_iso_TFAE2[OF f_bar_type eq_projs] by simp

      have dom_cod: "domain(f_bar) = codomain(q)" using f_bar_type q_type unfolding cfunc_type_def by auto
      have fbarq_epi: "epimorphism(f_bar \<circ>\<^sub>c q)" using f_eqs f_epi by simp
      have f_bar_epi: "epimorphism(f_bar)" using comp_epi_imp_epi[OF dom_cod fbarq_epi] by simp

      have f_bar_iso: "isomorphism(f_bar)" using epi_mon_is_iso[OF f_bar_epi mono_fbar] by simp
      obtain f_bar_inv where f_bar_inv_type: "f_bar_inv : Y \<rightarrow> Q"
          and f_bar_inv_eq1: "f_bar_inv \<circ>\<^sub>c f_bar = id(Q)" and f_bar_inv_eq2: "f_bar \<circ>\<^sub>c f_bar_inv = id(Y)"
        using isomorphism_def3[OF f_bar_type] f_bar_iso by auto

      have g_const: "const_on_rel(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X), g)"
        unfolding const_on_rel_def
        using fibered_product_pair_member2[OF f_type g_type g_eq] by simp

      define g_bar where "g_bar = quotient_func(g, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
      have g_bar_type: "g_bar : Q \<rightarrow> E"
        unfolding g_bar_def Q_def using quotient_func_type[OF equiv_kp g_type g_const] by simp
      have g_bar_eq: "g_bar \<circ>\<^sub>c q = g"
        unfolding g_bar_def q_def using quotient_func_eq[OF equiv_kp g_type g_const] by simp

      define k where "k = g_bar \<circ>\<^sub>c f_bar_inv"
      have k_type: "k : Y \<rightarrow> E" unfolding k_def using f_bar_inv_type g_bar_type comp_type by blast

      have finv_f_eq_q: "f_bar_inv \<circ>\<^sub>c f = q"
      proof -
        have "f_bar_inv \<circ>\<^sub>c f = f_bar_inv \<circ>\<^sub>c (f_bar \<circ>\<^sub>c q)" using f_eqs by simp
        also have "... = (f_bar_inv \<circ>\<^sub>c f_bar) \<circ>\<^sub>c q" using comp_associative2[OF q_type f_bar_type f_bar_inv_type] by simp
        also have "... = id(Q) \<circ>\<^sub>c q" using f_bar_inv_eq1 by simp
        also have "... = q" using id_left_unit2[OF q_type] by simp
        finally show ?thesis by simp
      qed
      have kf_eq_g: "k \<circ>\<^sub>c f = g"
      proof -
        have "k \<circ>\<^sub>c f = (g_bar \<circ>\<^sub>c f_bar_inv) \<circ>\<^sub>c f" unfolding k_def by simp
        also have "... = g_bar \<circ>\<^sub>c (f_bar_inv \<circ>\<^sub>c f)" using comp_associative2[OF f_type f_bar_inv_type g_bar_type] by simp
        also have "... = g_bar \<circ>\<^sub>c q" using finv_f_eq_q by simp
        also have "... = g" using g_bar_eq by simp
        finally show ?thesis by simp
      qed

      show "\<exists>! k. k : Y \<rightarrow> E \<and> k \<circ>\<^sub>c f = g"
      proof (rule ex1I[where a=k])
        show "k : Y \<rightarrow> E \<and> k \<circ>\<^sub>c f = g" using k_type kf_eq_g by simp
      next
        fix y assume "y : Y \<rightarrow> E \<and> y \<circ>\<^sub>c f = g"
        then have y_type: "y : Y \<rightarrow> E" and y_eq: "y \<circ>\<^sub>c f = g" by auto
        have f_epi_rule: "\<forall> g' h' A. g' : Y \<rightarrow> A \<and> h' : Y \<rightarrow> A \<longrightarrow> (g' \<circ>\<^sub>c f = h' \<circ>\<^sub>c f \<longrightarrow> g' = h')"
          using epimorphism_def3[OF f_type] f_epi by simp
        show "y = k" using f_epi_rule[rule_format, where g'=y and h'=k and A=E] y_type k_type y_eq kf_eq_g by auto
      qed
    qed
  qed
qed

lemma epimorphisms_are_regular:
  assumes f_type: "f : X \<rightarrow> Y" and f_epi: "epimorphism(f)"
  shows "regular_epimorphism(f)"
proof -
  have cod_f: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  have "coequalizer(codomain(f), f, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
    using epimorphism_coequalizer_kernel_pair[OF f_type f_epi] cod_f by simp
  then show ?thesis unfolding regular_epimorphism_def by auto
qed

subsection \<open>Epi-monic Factorization\<close>

lemma epi_monic_factorization:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "\<exists> g m E. g : X \<rightarrow> E \<and> m : E \<rightarrow> Y
    \<and> coequalizer(E, g, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))
    \<and> monomorphism(m) \<and> f = m \<circ>\<^sub>c g
    \<and> (\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
proof -
  have equiv_kp: "equiv_rel_on(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
    using kernel_pair_equiv_rel[OF f_type] by simp

  define q where "q = equiv_class(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
  define E where "E = quotient_set(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
  have q_type: "q : X \<rightarrow> E" unfolding q_def E_def using equiv_class_type[OF equiv_kp] by simp

  have f_const: "const_on_rel(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X), f)"
    unfolding const_on_rel_def
  proof (intro allI impI)
    fix x y assume x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X"
    assume "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
    then show "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
      using fibered_product_pair_member[OF f_type f_type x_type y_type] by simp
  qed

  define m where "m = quotient_func(f, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
  have m_type: "m : E \<rightarrow> Y" unfolding m_def E_def using quotient_func_type[OF equiv_kp f_type f_const] by simp
  have f_eq_m_q: "f = m \<circ>\<^sub>c q"
    unfolding m_def q_def using quotient_func_eq[OF equiv_kp f_type f_const] by simp

  have lp_type: "fibered_product_left_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type f_type] by simp
  have rp_type: "fibered_product_right_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_right_proj_type[OF f_type f_type] by simp

  have q_coequalizer: "coequalizer(E, q, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
  proof -
    have raw: "coequalizer(quotient_set(X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X)),
        equiv_class(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X)),
        fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
      using canonical_quotient_map_is_coequalizer[OF equiv_kp]
      unfolding fibered_product_left_proj_def fibered_product_right_proj_def by simp
    show ?thesis using raw unfolding q_def E_def by simp
  qed
  have q_epi: "epimorphism(q)" using coequalizer_is_epimorphism[OF q_coequalizer] by simp
  have q_eq: "q \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = q \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
    using q_coequalizer coequalizer_def2[OF lp_type rp_type q_type] by simp

  have m_mono: "monomorphism(m)"
  proof -
    have kpc: "\<exists>! b. b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>m\<^esub>\<times>\<^sub>c\<^bsub>m\<^esub> E) \<and>
        fibered_product_left_proj(E, m, m, E) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) \<and>
        fibered_product_right_proj(E, m, m, E) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) \<and>
        epimorphism(b)"
      using kernel_pair_connection[OF f_type q_type q_epi f_eq_m_q[symmetric] q_eq m_type] by simp
    then obtain b where b_type: "b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>m\<^esub>\<times>\<^sub>c\<^bsub>m\<^esub> E)"
        and left_b_eq: "fibered_product_left_proj(E, m, m, E) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)"
        and right_b_eq: "fibered_product_right_proj(E, m, m, E) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
        and b_epi: "epimorphism(b)" by auto

    have lpE_type: "fibered_product_left_proj(E, m, m, E) : (E \<^bsub>m\<^esub>\<times>\<^sub>c\<^bsub>m\<^esub> E) \<rightarrow> E"
      using fibered_product_left_proj_type[OF m_type m_type] by simp
    have rpE_type: "fibered_product_right_proj(E, m, m, E) : (E \<^bsub>m\<^esub>\<times>\<^sub>c\<^bsub>m\<^esub> E) \<rightarrow> E"
      using fibered_product_right_proj_type[OF m_type m_type] by simp

    have eq_projs: "fibered_product_left_proj(E, m, m, E) = fibered_product_right_proj(E, m, m, E)"
    proof -
      have "fibered_product_left_proj(E, m, m, E) \<circ>\<^sub>c b = fibered_product_right_proj(E, m, m, E) \<circ>\<^sub>c b"
        using left_b_eq right_b_eq q_eq by simp
      then show ?thesis using b_epi epimorphism_def3[OF b_type] lpE_type rpE_type by auto
    qed
    show ?thesis using kern_pair_proj_iso_TFAE2[OF m_type eq_projs] by simp
  qed

  have unique_m: "\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c q \<longrightarrow> x = m"
  proof (intro allI impI)
    fix x assume x_type: "x : E \<rightarrow> Y"
    assume f_eq_x_q: "f = x \<circ>\<^sub>c q"
    have xq_eq_mq: "x \<circ>\<^sub>c q = m \<circ>\<^sub>c q" using f_eq_m_q f_eq_x_q by simp
    have q_epi_rule: "\<forall> g' h' A. g' : E \<rightarrow> A \<and> h' : E \<rightarrow> A \<longrightarrow> (g' \<circ>\<^sub>c q = h' \<circ>\<^sub>c q \<longrightarrow> g' = h')"
      using epimorphism_def3[OF q_type] q_epi by simp
    show "x = m" using q_epi_rule[rule_format, where g'=x and h'=m and A=Y] x_type m_type xq_eq_mq by auto
  qed

  have witness: "q : X \<rightarrow> E \<and> m : E \<rightarrow> Y \<and>
      coequalizer(E, q, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X)) \<and>
      monomorphism(m) \<and> f = m \<circ>\<^sub>c q \<and> (\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c q \<longrightarrow> x = m)"
  proof (intro conjI)
    show "q : X \<rightarrow> E" by (rule q_type)
  next
    show "m : E \<rightarrow> Y" by (rule m_type)
  next
    show "coequalizer(E, q, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
      by (rule q_coequalizer)
  next
    show "monomorphism(m)" by (rule m_mono)
  next
    show "f = m \<circ>\<^sub>c q" by (rule f_eq_m_q)
  next
    show "\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c q \<longrightarrow> x = m" by (rule unique_m)
  qed
  show ?thesis
    by (rule exI[where x=q], rule exI[where x=m], rule exI[where x=E], rule witness)
qed

lemma epi_monic_factorization2:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "\<exists> g m E. g : X \<rightarrow> E \<and> m : E \<rightarrow> Y
    \<and> epimorphism(g) \<and> monomorphism(m) \<and> f = m \<circ>\<^sub>c g
    \<and> (\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
proof -
  obtain g m E where g_type: "g : X \<rightarrow> E" and m_type: "m : E \<rightarrow> Y"
      and g_coeq: "coequalizer(E, g, fibered_product_left_proj(X, f, f, X), fibered_product_right_proj(X, f, f, X))"
      and m_mono: "monomorphism(m)" and f_eq: "f = m \<circ>\<^sub>c g"
      and uniq: "\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m"
    using epi_monic_factorization[OF f_type] by blast
  have g_epi: "epimorphism(g)" using coequalizer_is_epimorphism[OF g_coeq] by simp
  have witness: "g : X \<rightarrow> E \<and> m : E \<rightarrow> Y \<and> epimorphism(g) \<and> monomorphism(m) \<and> f = m \<circ>\<^sub>c g \<and>
      (\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
  proof (intro conjI)
    show "g : X \<rightarrow> E" by (rule g_type)
  next
    show "m : E \<rightarrow> Y" by (rule m_type)
  next
    show "epimorphism(g)" by (rule g_epi)
  next
    show "monomorphism(m)" by (rule m_mono)
  next
    show "f = m \<circ>\<^sub>c g" by (rule f_eq)
  next
    show "\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m" by (rule uniq)
  qed
  show ?thesis
    by (rule exI[where x=g], rule exI[where x=m], rule exI[where x=E], rule witness)
qed

subsubsection \<open>Image of a Function\<close>

text \<open>The definition below corresponds to Definition 2.3.7 in Halvorson. HOL's @{text image_of},
  @{text image_restriction_mapping}, and @{text image_subobject_mapping} are a chain of THREE
  successive @{text SOME}/@{text SOME}/@{text THE} definitions (each referencing the previous);
  following the by-now-standard conservative-Skolemization technique, all three are axiomatized
  together directly here as the combined Skolem witness of the single existence fact
  @{text epi_monic_factorization} already proves for the composite @{text "f \<circ>\<^sub>c n"}. HOL's
  @{text image_restriction_mapping} bundles its @{text "A"}/@{text n} arguments into a @{text
  "cset \<times> cfunc"} pair; flattened here to three plain arguments, matching this port's usual
  convention. A custom mixfix notation mirroring HOL's @{text "f\<lparr>A\<rparr>\<^bsub>n\<^esub>"}/@{text "f\<restriction>\<^bsub>(A,n)\<^esub>"}/
  @{text "[f\<lparr>A\<rparr>\<^bsub>n\<^esub>]map"} surface syntax was tried first but abandoned: nesting bracket-heavy
  mixfix templates (@{text "\<lparr>_\<rparr>"} inside @{text "[_]"}) inside each other caused the Isabelle
  parser/pretty-printer to hang on some later proofs, apparently from ambiguous-grammar
  backtracking -- plain function-call syntax is used instead, matching the convention already
  used for other flattened multi-argument constants throughout this port.\<close>
axiomatization
  image_of :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cset" and
  image_restriction_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" and
  image_subobject_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc"
where
  image_of_spec: "f : X \<rightarrow> Y \<Longrightarrow> n : A \<rightarrow> X \<Longrightarrow>
    image_restriction_mapping(f, A, n) : A \<rightarrow> image_of(f, A, n) \<and>
    image_subobject_mapping(f, A, n) : image_of(f, A, n) \<rightarrow> Y \<and>
    coequalizer(image_of(f, A, n), image_restriction_mapping(f, A, n),
        fibered_product_left_proj(A, f \<circ>\<^sub>c n, f \<circ>\<^sub>c n, A), fibered_product_right_proj(A, f \<circ>\<^sub>c n, f \<circ>\<^sub>c n, A)) \<and>
    monomorphism(image_subobject_mapping(f, A, n)) \<and>
    f \<circ>\<^sub>c n = image_subobject_mapping(f, A, n) \<circ>\<^sub>c image_restriction_mapping(f, A, n) \<and>
    (\<forall>x. x : image_of(f, A, n) \<rightarrow> Y \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c image_restriction_mapping(f, A, n)
        \<longrightarrow> x = image_subobject_mapping(f, A, n))"

lemma image_rest_map_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Y" and n_type: "n : A \<rightarrow> X"
  shows "image_restriction_mapping(f, A, n) : A \<rightarrow> image_of(f, A, n)"
  using image_of_spec[OF f_type n_type] by (rule conjunct1)

lemma image_subobj_map_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Y" and n_type: "n : A \<rightarrow> X"
  shows "image_subobject_mapping(f, A, n) : image_of(f, A, n) \<rightarrow> Y"
  using image_of_spec[OF f_type n_type, THEN conjunct2] by (rule conjunct1)

lemma image_rest_map_coequalizer:
  assumes f_type: "f : X \<rightarrow> Y" and n_type: "n : A \<rightarrow> X"
  shows "coequalizer(image_of(f, A, n), image_restriction_mapping(f, A, n),
      fibered_product_left_proj(A, f \<circ>\<^sub>c n, f \<circ>\<^sub>c n, A), fibered_product_right_proj(A, f \<circ>\<^sub>c n, f \<circ>\<^sub>c n, A))"
  using image_of_spec[OF f_type n_type, THEN conjunct2, THEN conjunct2] by (rule conjunct1)

lemma image_rest_map_epi:
  assumes f_type: "f : X \<rightarrow> Y" and n_type: "n : A \<rightarrow> X"
  shows "epimorphism(image_restriction_mapping(f, A, n))"
  using coequalizer_is_epimorphism[OF image_rest_map_coequalizer[OF f_type n_type]] by simp

lemma image_subobj_map_mono:
  assumes f_type: "f : X \<rightarrow> Y" and n_type: "n : A \<rightarrow> X"
  shows "monomorphism(image_subobject_mapping(f, A, n))"
  using image_of_spec[OF f_type n_type, THEN conjunct2, THEN conjunct2, THEN conjunct2] by (rule conjunct1)

lemma image_subobj_comp_image_rest:
  assumes f_type: "f : X \<rightarrow> Y" and n_type: "n : A \<rightarrow> X"
  shows "image_subobject_mapping(f, A, n) \<circ>\<^sub>c image_restriction_mapping(f, A, n) = f \<circ>\<^sub>c n"
proof -
  have raw: "f \<circ>\<^sub>c n = image_subobject_mapping(f, A, n) \<circ>\<^sub>c image_restriction_mapping(f, A, n)"
    using image_of_spec[OF f_type n_type, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
    by (rule conjunct1)
  show ?thesis using raw by simp
qed

lemma image_subobj_map_unique:
  assumes f_type: "f : X \<rightarrow> Y" and n_type: "n : A \<rightarrow> X"
  assumes x_type: "x : image_of(f, A, n) \<rightarrow> Y" and x_eq: "f \<circ>\<^sub>c n = x \<circ>\<^sub>c image_restriction_mapping(f, A, n)"
  shows "x = image_subobject_mapping(f, A, n)"
proof -
  have uniq: "\<forall>x. x : image_of(f, A, n) \<rightarrow> Y \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c image_restriction_mapping(f, A, n)
      \<longrightarrow> x = image_subobject_mapping(f, A, n)"
    using image_of_spec[OF f_type n_type, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
    by (rule conjunct2)
  show ?thesis using uniq[rule_format, where x=x] x_type x_eq by auto
qed

lemma image_self:
  assumes f_type: "f : X \<rightarrow> Y" and f_mono: "monomorphism(f)"
  assumes a_type: "a : A \<rightarrow> X" and a_mono: "monomorphism(a)"
  shows "image_of(f, A, a) \<cong> A"
proof -
  have cod_dom: "codomain(a) = domain(f)" using a_type f_type unfolding cfunc_type_def by auto
  have fa_mono: "monomorphism(f \<circ>\<^sub>c a)"
    using composition_of_monic_pair_is_monic[OF cod_dom a_mono f_mono] by simp

  have rest_type: "image_restriction_mapping(f, A, a) : A \<rightarrow> image_of(f, A, a)"
    using image_rest_map_type[OF f_type a_type] by simp
  have submap_type: "image_subobject_mapping(f, A, a) : image_of(f, A, a) \<rightarrow> Y"
    using image_subobj_map_type[OF f_type a_type] by simp
  have map_comp: "image_subobject_mapping(f, A, a) \<circ>\<^sub>c image_restriction_mapping(f, A, a) = f \<circ>\<^sub>c a"
    using image_subobj_comp_image_rest[OF f_type a_type] by simp
  have comp_mono: "monomorphism(image_subobject_mapping(f, A, a) \<circ>\<^sub>c image_restriction_mapping(f, A, a))"
    using map_comp fa_mono by simp
  have rest_mono: "monomorphism(image_restriction_mapping(f, A, a))"
    using comp_monic_imp_monic'[OF rest_type submap_type comp_mono] by simp
  have rest_epi: "epimorphism(image_restriction_mapping(f, A, a))" using image_rest_map_epi[OF f_type a_type] by simp
  have rest_iso: "isomorphism(image_restriction_mapping(f, A, a))" using epi_mon_is_iso[OF rest_epi rest_mono] by simp

  have A_cong: "A \<cong> image_of(f, A, a)" unfolding is_isomorphic_def using rest_type rest_iso by auto
  show ?thesis using isomorphic_is_symmetric A_cong by auto
qed

text \<open>The lemma below corresponds to Proposition 2.3.8 in Halvorson.\<close>
lemma image_smallest_subobject:
  assumes f_type: "f : X \<rightarrow> Y" and a_type: "a : A \<rightarrow> X"
  assumes Bn_subobj: "subobject_of(B, n, Y)" and f_factorsthru_n: "f factorsthru n"
  shows "relative_subset(image_of(f, A, a), image_subobject_mapping(f, A, a), Y, B, n)"
proof -
  have n_type: "n : B \<rightarrow> Y" and n_mono: "monomorphism(n)"
    using Bn_subobj unfolding subobject_of_def by auto
  obtain g where g_type: "g : X \<rightarrow> B" and f_eq_ng: "n \<circ>\<^sub>c g = f"
    using factors_through_def2[OF f_type n_type] f_factorsthru_n by auto

  have fa_type: "f \<circ>\<^sub>c a : A \<rightarrow> Y" using a_type f_type comp_type by blast
  have ga_type: "g \<circ>\<^sub>c a : A \<rightarrow> B" using a_type g_type comp_type by blast

  have p0_type: "fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A) : (A \<^bsub>f \<circ>\<^sub>c a\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c a\<^esub> A) \<rightarrow> A"
    using fibered_product_left_proj_type[OF fa_type fa_type] by simp
  have p1_type: "fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A) : (A \<^bsub>f \<circ>\<^sub>c a\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c a\<^esub> A) \<rightarrow> A"
    using fibered_product_right_proj_type[OF fa_type fa_type] by simp

  have fa_coequalizes: "(f \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)
      = (f \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
    using fibered_product_proj_eq[OF fa_type fa_type] by simp

  have ga_coequalizes: "(g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)
      = (g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
  proof -
    have n_lhs: "n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A))
        = (f \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
    proof -
      have "n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A))
          = (n \<circ>\<^sub>c (g \<circ>\<^sub>c a)) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
        using comp_associative2[OF p0_type ga_type n_type] by simp
      also have "... = ((n \<circ>\<^sub>c g) \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
        using comp_associative2[OF a_type g_type n_type] by simp
      also have "... = (f \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)" using f_eq_ng by simp
      finally show ?thesis by simp
    qed
    have n_rhs: "n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A))
        = (f \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
    proof -
      have "n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A))
          = (n \<circ>\<^sub>c (g \<circ>\<^sub>c a)) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
        using comp_associative2[OF p1_type ga_type n_type] by simp
      also have "... = ((n \<circ>\<^sub>c g) \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
        using comp_associative2[OF a_type g_type n_type] by simp
      also have "... = (f \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)" using f_eq_ng by simp
      finally show ?thesis by simp
    qed
    have n_eq: "n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A))
        = n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A))"
      using n_lhs n_rhs fa_coequalizes by simp
    have n_mono_rule: "\<forall> g' h' AA. g' : AA \<rightarrow> B \<and> h' : AA \<rightarrow> B \<longrightarrow> (n \<circ>\<^sub>c g' = n \<circ>\<^sub>c h' \<longrightarrow> g' = h')"
      using monomorphism_def3[OF n_type] n_mono by simp
    have g0_type: "(g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A) : (A \<^bsub>f \<circ>\<^sub>c a\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c a\<^esub> A) \<rightarrow> B"
      using p0_type ga_type comp_type by blast
    have g1_type: "(g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A) : (A \<^bsub>f \<circ>\<^sub>c a\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c a\<^esub> A) \<rightarrow> B"
      using p1_type ga_type comp_type by blast
    show ?thesis
      using n_mono_rule[rule_format, where g'="(g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)"
          and h'="(g \<circ>\<^sub>c a) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)" and AA="A \<^bsub>f \<circ>\<^sub>c a\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c a\<^esub> A"]
        g0_type g1_type n_eq by auto
  qed

  have img_coeq: "coequalizer(image_of(f, A, a), image_restriction_mapping(f, A, a),
      fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A), fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A))"
    using image_rest_map_coequalizer[OF f_type a_type] by simp
  have restA_type: "image_restriction_mapping(f, A, a) : A \<rightarrow> image_of(f, A, a)"
    using image_rest_map_type[OF f_type a_type] by simp
  have img_uniq: "\<forall> h F. (h : A \<rightarrow> F \<and>
        h \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A) = h \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c a, f \<circ>\<^sub>c a, A)) \<longrightarrow>
      (\<exists>!k. k : image_of(f, A, a) \<rightarrow> F \<and> k \<circ>\<^sub>c image_restriction_mapping(f, A, a) = h)"
    using img_coeq coequalizer_def2[OF p0_type p1_type restA_type] by simp
  have ex1k: "\<exists>!k. k : image_of(f, A, a) \<rightarrow> B \<and> k \<circ>\<^sub>c image_restriction_mapping(f, A, a) = g \<circ>\<^sub>c a"
    using img_uniq[rule_format, where h="g \<circ>\<^sub>c a" and F=B] ga_type ga_coequalizes by auto
  then obtain k where k_type: "k : image_of(f, A, a) \<rightarrow> B"
      and k_e_eq_g: "k \<circ>\<^sub>c image_restriction_mapping(f, A, a) = g \<circ>\<^sub>c a" by auto

  have nk_type: "n \<circ>\<^sub>c k : image_of(f, A, a) \<rightarrow> Y" using k_type n_type comp_type by blast
  have nk_eq: "f \<circ>\<^sub>c a = (n \<circ>\<^sub>c k) \<circ>\<^sub>c image_restriction_mapping(f, A, a)"
  proof -
    have "(n \<circ>\<^sub>c k) \<circ>\<^sub>c image_restriction_mapping(f, A, a) = n \<circ>\<^sub>c (k \<circ>\<^sub>c image_restriction_mapping(f, A, a))"
      using comp_associative2[OF restA_type k_type n_type] by simp
    also have "... = n \<circ>\<^sub>c (g \<circ>\<^sub>c a)" using k_e_eq_g by simp
    also have "... = (n \<circ>\<^sub>c g) \<circ>\<^sub>c a" using comp_associative2[OF a_type g_type n_type] by simp
    also have "... = f \<circ>\<^sub>c a" using f_eq_ng by simp
    finally show ?thesis by simp
  qed
  have n_k_eq_map: "n \<circ>\<^sub>c k = image_subobject_mapping(f, A, a)"
    using image_subobj_map_unique[OF f_type a_type nk_type nk_eq] by simp

  have subobj_map_type: "image_subobject_mapping(f, A, a) : image_of(f, A, a) \<rightarrow> Y"
    using image_subobj_map_type[OF f_type a_type] by simp
  have subobj_map_mono: "monomorphism(image_subobject_mapping(f, A, a))"
    using image_subobj_map_mono[OF f_type a_type] by simp
  show ?thesis
    unfolding relative_subset_def
  proof (intro conjI)
    show "image_subobject_mapping(f, A, a) : image_of(f, A, a) \<rightarrow> Y" by (rule subobj_map_type)
  next
    show "monomorphism(image_subobject_mapping(f, A, a))" by (rule subobj_map_mono)
  next
    show "n : B \<rightarrow> Y" by (rule n_type)
  next
    show "monomorphism(n)" by (rule n_mono)
  next
    show "\<exists>k'. k' : image_of(f, A, a) \<rightarrow> B \<and> n \<circ>\<^sub>c k' = image_subobject_mapping(f, A, a)"
      using k_type n_k_eq_map by auto
  qed
qed

lemma images_iso:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes m_type: "m : Z \<rightarrow> X" and n_type: "n : A \<rightarrow> Z"
  shows "image_of(f \<circ>\<^sub>c m, A, n) \<cong> image_of(f, A, m \<circ>\<^sub>c n)"
proof -
  have fm_type: "f \<circ>\<^sub>c m : Z \<rightarrow> Y" using m_type f_type comp_type by blast
  have mn_type: "m \<circ>\<^sub>c n : A \<rightarrow> X" using n_type m_type comp_type by blast
  have assoc: "(f \<circ>\<^sub>c m) \<circ>\<^sub>c n = f \<circ>\<^sub>c (m \<circ>\<^sub>c n)" using comp_associative2[OF n_type m_type f_type] by simp

  have f_m_image_coequalizer:
    "coequalizer(image_of(f \<circ>\<^sub>c m, A, n), image_restriction_mapping(f \<circ>\<^sub>c m, A, n),
        fibered_product_left_proj(A, (f \<circ>\<^sub>c m) \<circ>\<^sub>c n, (f \<circ>\<^sub>c m) \<circ>\<^sub>c n, A),
        fibered_product_right_proj(A, (f \<circ>\<^sub>c m) \<circ>\<^sub>c n, (f \<circ>\<^sub>c m) \<circ>\<^sub>c n, A))"
    using image_rest_map_coequalizer[OF fm_type n_type] by simp
  have f_m_image_coequalizer': "coequalizer(image_of(f \<circ>\<^sub>c m, A, n), image_restriction_mapping(f \<circ>\<^sub>c m, A, n),
      fibered_product_left_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A),
      fibered_product_right_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A))"
    using f_m_image_coequalizer assoc by simp

  have f_image_coequalizer:
    "coequalizer(image_of(f, A, m \<circ>\<^sub>c n), image_restriction_mapping(f, A, m \<circ>\<^sub>c n),
        fibered_product_left_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A),
        fibered_product_right_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A))"
    using image_rest_map_coequalizer[OF f_type mn_type] by simp

  show ?thesis using coequalizer_unique[OF f_m_image_coequalizer' f_image_coequalizer] by simp
qed

lemma image_subset_conv:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes m_type: "m : Z \<rightarrow> X" and n_type: "n : A \<rightarrow> Z"
  assumes exi: "\<exists>i. subobject_of(image_of(f \<circ>\<^sub>c m, A, n), i, B)"
  shows "\<exists>j. subobject_of(image_of(f, A, m \<circ>\<^sub>c n), j, B)"
proof -
  obtain i where i_type: "i : image_of(f \<circ>\<^sub>c m, A, n) \<rightarrow> B" and i_mono: "monomorphism(i)"
    using exi unfolding subobject_of_def by auto

  have images_cong: "image_of(f \<circ>\<^sub>c m, A, n) \<cong> image_of(f, A, m \<circ>\<^sub>c n)"
    using images_iso[OF f_type m_type n_type] by simp
  have images_cong': "image_of(f, A, m \<circ>\<^sub>c n) \<cong> image_of(f \<circ>\<^sub>c m, A, n)"
    using isomorphic_is_symmetric images_cong by auto
  then obtain k where k_type: "k : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> image_of(f \<circ>\<^sub>c m, A, n)" and k_iso: "isomorphism(k)"
    unfolding is_isomorphic_def by auto
  have k_mono: "monomorphism(k)" using k_iso iso_imp_epi_and_monic by auto

  have cod_dom: "codomain(k) = domain(i)" using k_type i_type unfolding cfunc_type_def by auto
  have ik_mono: "monomorphism(i \<circ>\<^sub>c k)" using composition_of_monic_pair_is_monic[OF cod_dom k_mono i_mono] by simp
  have ik_type: "i \<circ>\<^sub>c k : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> B" using k_type i_type comp_type by blast

  have witness: "subobject_of(image_of(f, A, m \<circ>\<^sub>c n), i \<circ>\<^sub>c k, B)"
    unfolding subobject_of_def using ik_type ik_mono by simp
  show ?thesis using witness by auto
qed

lemma image_rel_subset_conv:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes m_type: "m : Z \<rightarrow> X" and n_type: "n : A \<rightarrow> Z"
  assumes rel_sub1: "relative_subset(image_of(f \<circ>\<^sub>c m, A, n), image_subobject_mapping(f \<circ>\<^sub>c m, A, n), Y, B, b)"
  shows "relative_subset(image_of(f, A, m \<circ>\<^sub>c n), image_subobject_mapping(f, A, m \<circ>\<^sub>c n), Y, B, b)"
proof -
  have fm_type: "f \<circ>\<^sub>c m : Z \<rightarrow> Y" using m_type f_type comp_type by blast
  have mn_type: "m \<circ>\<^sub>c n : A \<rightarrow> X" using n_type m_type comp_type by blast
  have assoc: "(f \<circ>\<^sub>c m) \<circ>\<^sub>c n = f \<circ>\<^sub>c (m \<circ>\<^sub>c n)" using comp_associative2[OF n_type m_type f_type] by simp
  have fmn_type: "f \<circ>\<^sub>c (m \<circ>\<^sub>c n) : A \<rightarrow> Y" using mn_type f_type comp_type by blast

  have b_type: "b : B \<rightarrow> Y" and b_mono: "monomorphism(b)"
    using rel_sub1 unfolding relative_subset_def by auto
  obtain k where k_type: "k : image_of(f \<circ>\<^sub>c m, A, n) \<rightarrow> B"
      and b_k_eq_map: "b \<circ>\<^sub>c k = image_subobject_mapping(f \<circ>\<^sub>c m, A, n)"
    using rel_sub1 unfolding relative_subset_def by auto

  have f_m_image_coequalizer: "coequalizer(image_of(f \<circ>\<^sub>c m, A, n), image_restriction_mapping(f \<circ>\<^sub>c m, A, n),
      fibered_product_left_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A),
      fibered_product_right_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A))"
    using image_rest_map_coequalizer[OF fm_type n_type] assoc by simp

  have p0_type: "fibered_product_left_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A)
      : (A \<^bsub>f \<circ>\<^sub>c (m \<circ>\<^sub>c n)\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c (m \<circ>\<^sub>c n)\<^esub> A) \<rightarrow> A"
    using fibered_product_left_proj_type[OF fmn_type fmn_type] by simp
  have p1_type: "fibered_product_right_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A)
      : (A \<^bsub>f \<circ>\<^sub>c (m \<circ>\<^sub>c n)\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c (m \<circ>\<^sub>c n)\<^esub> A) \<rightarrow> A"
    using fibered_product_right_proj_type[OF fmn_type fmn_type] by simp

  have restfm_type: "image_restriction_mapping(f \<circ>\<^sub>c m, A, n) : A \<rightarrow> image_of(f \<circ>\<^sub>c m, A, n)"
    using image_rest_map_type[OF fm_type n_type] by simp

  have f_m_image_coequalises:
    "image_restriction_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A)
        = image_restriction_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A)"
    using f_m_image_coequalizer coequalizer_def2[OF p0_type p1_type restfm_type] by simp

  have f_image_coequalizer: "coequalizer(image_of(f, A, m \<circ>\<^sub>c n), image_restriction_mapping(f, A, m \<circ>\<^sub>c n),
      fibered_product_left_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A),
      fibered_product_right_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A))"
    using image_rest_map_coequalizer[OF f_type mn_type] by simp

  have restf_type: "image_restriction_mapping(f, A, m \<circ>\<^sub>c n) : A \<rightarrow> image_of(f, A, m \<circ>\<^sub>c n)"
    using image_rest_map_type[OF f_type mn_type] by simp

  have f_uniq: "\<forall> h F. (h : A \<rightarrow> F \<and>
        h \<circ>\<^sub>c fibered_product_left_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A)
          = h \<circ>\<^sub>c fibered_product_right_proj(A, f \<circ>\<^sub>c (m \<circ>\<^sub>c n), f \<circ>\<^sub>c (m \<circ>\<^sub>c n), A)) \<longrightarrow>
      (\<exists>!k. k : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> F \<and> k \<circ>\<^sub>c image_restriction_mapping(f, A, m \<circ>\<^sub>c n) = h)"
    using f_image_coequalizer coequalizer_def2[OF p0_type p1_type restf_type] by simp

  have ex1k': "\<exists>!k'. k' : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> image_of(f \<circ>\<^sub>c m, A, n) \<and>
      k' \<circ>\<^sub>c image_restriction_mapping(f, A, m \<circ>\<^sub>c n) = image_restriction_mapping(f \<circ>\<^sub>c m, A, n)"
    using f_uniq[rule_format, where h="image_restriction_mapping(f \<circ>\<^sub>c m, A, n)" and F="image_of(f \<circ>\<^sub>c m, A, n)"]
      restfm_type f_m_image_coequalises by auto
  then obtain k' where k'_type: "k' : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> image_of(f \<circ>\<^sub>c m, A, n)"
      and k'_eq: "k' \<circ>\<^sub>c image_restriction_mapping(f, A, m \<circ>\<^sub>c n) = image_restriction_mapping(f \<circ>\<^sub>c m, A, n)" by auto

  have subobjfm_type: "image_subobject_mapping(f \<circ>\<^sub>c m, A, n) : image_of(f \<circ>\<^sub>c m, A, n) \<rightarrow> Y"
    using image_subobj_map_type[OF fm_type n_type] by simp
  have subobjfmk'_type: "image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c k' : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> Y"
    using k'_type subobjfm_type comp_type by blast

  have subobjfm_comp: "image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c image_restriction_mapping(f \<circ>\<^sub>c m, A, n) = f \<circ>\<^sub>c (m \<circ>\<^sub>c n)"
  proof -
    have "image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c image_restriction_mapping(f \<circ>\<^sub>c m, A, n) = (f \<circ>\<^sub>c m) \<circ>\<^sub>c n"
      using image_subobj_comp_image_rest[OF fm_type n_type] by simp
    also have "... = f \<circ>\<^sub>c (m \<circ>\<^sub>c n)" using assoc by simp
    finally show ?thesis by simp
  qed

  have fmn_eq: "f \<circ>\<^sub>c (m \<circ>\<^sub>c n) = (image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c k') \<circ>\<^sub>c image_restriction_mapping(f, A, m \<circ>\<^sub>c n)"
  proof -
    have "(image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c k') \<circ>\<^sub>c image_restriction_mapping(f, A, m \<circ>\<^sub>c n)
        = image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c (k' \<circ>\<^sub>c image_restriction_mapping(f, A, m \<circ>\<^sub>c n))"
      using comp_associative2[OF restf_type k'_type subobjfm_type] by simp
    also have "... = image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c image_restriction_mapping(f \<circ>\<^sub>c m, A, n)"
      using k'_eq by simp
    also have "... = f \<circ>\<^sub>c (m \<circ>\<^sub>c n)" using subobjfm_comp by simp
    finally show ?thesis by simp
  qed

  have k'_maps_eq: "image_subobject_mapping(f, A, m \<circ>\<^sub>c n) = image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c k'"
    using image_subobj_map_unique[OF f_type mn_type subobjfmk'_type fmn_eq] by simp

  have subobjfm_mono: "monomorphism(image_subobject_mapping(f \<circ>\<^sub>c m, A, n))"
    using image_subobj_map_mono[OF fm_type n_type] by simp
  have bk_mono: "monomorphism(b \<circ>\<^sub>c k)" using b_k_eq_map subobjfm_mono by simp
  have cod_dom_bk: "domain(b) = codomain(k)" using b_type k_type unfolding cfunc_type_def by auto
  have k_mono: "monomorphism(k)" using comp_monic_imp_monic[OF cod_dom_bk bk_mono] by simp

  have subobjf_type: "image_subobject_mapping(f, A, m \<circ>\<^sub>c n) : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> Y"
    using image_subobj_map_type[OF f_type mn_type] by simp
  have subobjf_mono: "monomorphism(image_subobject_mapping(f, A, m \<circ>\<^sub>c n))"
    using image_subobj_map_mono[OF f_type mn_type] by simp
  have subobjfmk'_mono: "monomorphism(image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c k')"
    using k'_maps_eq subobjf_mono by simp
  have cod_dom_k': "domain(image_subobject_mapping(f \<circ>\<^sub>c m, A, n)) = codomain(k')"
    using subobjfm_type k'_type unfolding cfunc_type_def by auto
  have k'_mono: "monomorphism(k')"
    using comp_monic_imp_monic[OF cod_dom_k' subobjfmk'_mono] by simp

  have kk'_type: "k \<circ>\<^sub>c k' : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> B" using k'_type k_type comp_type by blast
  have b_kk'_eq: "b \<circ>\<^sub>c (k \<circ>\<^sub>c k') = image_subobject_mapping(f, A, m \<circ>\<^sub>c n)"
  proof -
    have "b \<circ>\<^sub>c (k \<circ>\<^sub>c k') = (b \<circ>\<^sub>c k) \<circ>\<^sub>c k'" using comp_associative2[OF k'_type k_type b_type] by simp
    also have "... = image_subobject_mapping(f \<circ>\<^sub>c m, A, n) \<circ>\<^sub>c k'" using b_k_eq_map by simp
    also have "... = image_subobject_mapping(f, A, m \<circ>\<^sub>c n)" using k'_maps_eq by simp
    finally show ?thesis by simp
  qed

  show ?thesis
    unfolding relative_subset_def
  proof (intro conjI)
    show "image_subobject_mapping(f, A, m \<circ>\<^sub>c n) : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> Y" by (rule subobjf_type)
  next
    show "monomorphism(image_subobject_mapping(f, A, m \<circ>\<^sub>c n))" by (rule subobjf_mono)
  next
    show "b : B \<rightarrow> Y" by (rule b_type)
  next
    show "monomorphism(b)" by (rule b_mono)
  next
    show "\<exists>k''. k'' : image_of(f, A, m \<circ>\<^sub>c n) \<rightarrow> B \<and> b \<circ>\<^sub>c k'' = image_subobject_mapping(f, A, m \<circ>\<^sub>c n)"
      using kk'_type b_kk'_eq by auto
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.3.9 in Halvorson.\<close>
lemma subset_inv_image_iff_image_subset:
  assumes Aa_sub: "subobject_of(A, a, X)" and Bm_sub: "subobject_of(B, m, Y)"
  assumes f_type: "f : X \<rightarrow> Y"
  shows "relative_subset(A, a, X, inverse_image(f, B, m), inverse_image_subobject_mapping(f, B, m))
       \<longleftrightarrow> relative_subset(image_of(f, A, a), image_subobject_mapping(f, A, a), Y, B, m)"
proof (rule iffI)
  have m_mono: "monomorphism(m)" using Bm_sub unfolding subobject_of_def by auto
  have m_type: "m : B \<rightarrow> Y" using Bm_sub unfolding subobject_of_def by auto
  have m'_type: "inverse_image_subobject_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X"
    using inverse_image_subobject_mapping_type[OF f_type m_type m_mono] by simp
  have im_type: "inverse_image_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X \<times>\<^sub>c B"
    using inverse_image_mapping_type[OF m_type f_type m_mono] by simp
  have lp_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have lpim_type: "left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X"
    using lp_type im_type comp_type by blast
  have rpim_type: "right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> B"
    using rp_type im_type comp_type by blast
  have m'_eq: "inverse_image_subobject_mapping(f, B, m) = left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using inverse_image_subobject_mapping_def2[OF f_type] by simp
  have core: "f \<circ>\<^sub>c left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)
      = m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using inverse_image_mapping_eq[OF m_type f_type m_mono] by simp

  assume "relative_subset(A, a, X, inverse_image(f, B, m), inverse_image_subobject_mapping(f, B, m))"
  then have a_type: "a : A \<rightarrow> X" and a_mono: "monomorphism(a)" and
      k_exists: "\<exists>k. k : A \<rightarrow> inverse_image(f, B, m) \<and> inverse_image_subobject_mapping(f, B, m) \<circ>\<^sub>c k = a"
    unfolding relative_subset_def by auto
  then obtain k where k_type: "k : A \<rightarrow> inverse_image(f, B, m)"
      and k_a_eq: "inverse_image_subobject_mapping(f, B, m) \<circ>\<^sub>c k = a" by auto

  define d where "d = inverse_image_subobject_mapping(f, B, m) \<circ>\<^sub>c k"
  have d_type: "d : A \<rightarrow> X" unfolding d_def using k_type m'_type comp_type by blast
  have d_eq_a: "d = a" unfolding d_def using k_a_eq by simp
  have fd_type: "f \<circ>\<^sub>c d : A \<rightarrow> Y" using d_type f_type comp_type by blast

  have fd_eq: "f \<circ>\<^sub>c d = (m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k"
  proof -
    have s1: "f \<circ>\<^sub>c d = f \<circ>\<^sub>c (inverse_image_subobject_mapping(f, B, m) \<circ>\<^sub>c k)"
      unfolding d_def by simp
    have s2: "f \<circ>\<^sub>c (inverse_image_subobject_mapping(f, B, m) \<circ>\<^sub>c k)
        = f \<circ>\<^sub>c ((left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k)"
      using m'_eq by simp
    have s3: "f \<circ>\<^sub>c ((left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k)
        = (f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))) \<circ>\<^sub>c k"
      using comp_associative2[OF k_type lpim_type f_type] by simp
    have s4: "(f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))) \<circ>\<^sub>c k
        = (f \<circ>\<^sub>c left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k" by simp
    have s5: "(f \<circ>\<^sub>c left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k
        = (m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k" using core by simp
    show ?thesis using s1 s2 s3 s4 s5 by simp
  qed

  have h_type: "(right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k : A \<rightarrow> B"
    using rpim_type k_type comp_type by blast
  have mh_eq: "m \<circ>\<^sub>c ((right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k) = f \<circ>\<^sub>c d"
  proof -
    have t1: "m \<circ>\<^sub>c ((right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k)
        = (m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))) \<circ>\<^sub>c k"
      using comp_associative2[OF k_type rpim_type m_type] by simp
    have t2: "(m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))) \<circ>\<^sub>c k
        = (m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k" by simp
    have t3: "(m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k = f \<circ>\<^sub>c d"
      using fd_eq by simp
    show ?thesis using t1 t2 t3 by simp
  qed

  have fd_factorsthru_m: "(f \<circ>\<^sub>c d) factorsthru m"
    using factors_through_def2[OF fd_type m_type] h_type mh_eq by auto

  have idA_type: "id(A) : A \<rightarrow> A" by (rule id_type)
  have rel_sub_fd: "relative_subset(image_of(f \<circ>\<^sub>c d, A, id(A)), image_subobject_mapping(f \<circ>\<^sub>c d, A, id(A)), Y, B, m)"
    using image_smallest_subobject[OF fd_type idA_type Bm_sub fd_factorsthru_m] by simp
  have rel_sub_fa: "relative_subset(image_of(f \<circ>\<^sub>c a, A, id(A)), image_subobject_mapping(f \<circ>\<^sub>c a, A, id(A)), Y, B, m)"
    using rel_sub_fd d_eq_a by simp

  have a_idA_eq: "a \<circ>\<^sub>c id(A) = a" using id_right_unit2[OF a_type] by simp
  have result: "relative_subset(image_of(f, A, a \<circ>\<^sub>c id(A)), image_subobject_mapping(f, A, a \<circ>\<^sub>c id(A)), Y, B, m)"
    using image_rel_subset_conv[OF f_type a_type idA_type rel_sub_fa] by simp
  show "relative_subset(image_of(f, A, a), image_subobject_mapping(f, A, a), Y, B, m)"
    using result a_idA_eq by simp
next
  have m_mono: "monomorphism(m)" using Bm_sub unfolding subobject_of_def by auto
  have m_type: "m : B \<rightarrow> Y" using Bm_sub unfolding subobject_of_def by auto

  assume "relative_subset(image_of(f, A, a), image_subobject_mapping(f, A, a), Y, B, m)"
  then obtain s where s_type: "s : image_of(f, A, a) \<rightarrow> B"
      and m_s_eq_subobj_map: "m \<circ>\<^sub>c s = image_subobject_mapping(f, A, a)"
    unfolding relative_subset_def by auto

  have a_mono: "monomorphism(a)" using Aa_sub unfolding subobject_of_def by auto
  have a_type: "a : A \<rightarrow> X" using Aa_sub unfolding subobject_of_def by auto

  have restA_type: "image_restriction_mapping(f, A, a) : A \<rightarrow> image_of(f, A, a)"
    using image_rest_map_type[OF f_type a_type] by simp
  have s_restA_type: "s \<circ>\<^sub>c image_restriction_mapping(f, A, a) : A \<rightarrow> B"
    using restA_type s_type comp_type by blast

  have pullback_maps_commute: "m \<circ>\<^sub>c (s \<circ>\<^sub>c image_restriction_mapping(f, A, a)) = f \<circ>\<^sub>c a"
  proof -
    have "m \<circ>\<^sub>c (s \<circ>\<^sub>c image_restriction_mapping(f, A, a)) = (m \<circ>\<^sub>c s) \<circ>\<^sub>c image_restriction_mapping(f, A, a)"
      using comp_associative2[OF restA_type s_type m_type] by simp
    also have "... = image_subobject_mapping(f, A, a) \<circ>\<^sub>c image_restriction_mapping(f, A, a)"
      using m_s_eq_subobj_map by simp
    also have "... = f \<circ>\<^sub>c a" using image_subobj_comp_image_rest[OF f_type a_type] by simp
    finally show ?thesis by simp
  qed

  have pb: "is_pullback(inverse_image(f, B, m), B, X, Y,
      right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m), m,
      left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m), f)"
    using inverse_image_pullback[OF m_type f_type m_mono] by simp
  have pb_uniq: "\<forall>Z k h. k : Z \<rightarrow> B \<and> h : Z \<rightarrow> X \<and> m \<circ>\<^sub>c k = f \<circ>\<^sub>c h \<longrightarrow>
      (\<exists>!j. j : Z \<rightarrow> inverse_image(f, B, m) \<and>
        (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = k \<and>
        (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = h)"
    using pb unfolding is_pullback_def by auto

  have ex1k: "\<exists>!k. k : A \<rightarrow> inverse_image(f, B, m) \<and>
        (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k = s \<circ>\<^sub>c image_restriction_mapping(f, A, a) \<and>
        (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k = a"
    using pb_uniq[rule_format, where Z=A and k="s \<circ>\<^sub>c image_restriction_mapping(f, A, a)" and h=a]
      s_restA_type a_type pullback_maps_commute by auto
  then obtain k where k_type: "k : A \<rightarrow> inverse_image(f, B, m)"
      and k_left_eq: "(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k = a"
    by auto

  have lpim_type: "left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X"
  proof -
    have lp_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by (rule left_cart_proj_type)
    have im_type: "inverse_image_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X \<times>\<^sub>c B"
      using inverse_image_mapping_type[OF m_type f_type m_mono] by simp
    show ?thesis using im_type lp_type comp_type by blast
  qed

  have lpim_k_mono: "monomorphism((left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c k)"
    using k_left_eq a_mono by simp
  have cod_dom_k: "domain(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) = codomain(k)"
    using lpim_type k_type unfolding cfunc_type_def by auto
  have k_mono: "monomorphism(k)" using comp_monic_imp_monic[OF cod_dom_k lpim_k_mono] by simp

  have m'_type: "inverse_image_subobject_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X"
    using inverse_image_subobject_mapping_type[OF f_type m_type m_mono] by simp
  have m'_eq: "inverse_image_subobject_mapping(f, B, m) = left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using inverse_image_subobject_mapping_def2[OF f_type] by simp
  have m'_k_eq_a: "inverse_image_subobject_mapping(f, B, m) \<circ>\<^sub>c k = a"
    using m'_eq k_left_eq by simp

  show "relative_subset(A, a, X, inverse_image(f, B, m), inverse_image_subobject_mapping(f, B, m))"
    unfolding relative_subset_def
  proof (intro conjI)
    show "a : A \<rightarrow> X" by (rule a_type)
  next
    show "monomorphism(a)" by (rule a_mono)
  next
    show "inverse_image_subobject_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X" by (rule m'_type)
  next
    show "monomorphism(inverse_image_subobject_mapping(f, B, m))"
      using inverse_image_subobject_mapping_mono[OF f_type m_type m_mono] by simp
  next
    show "\<exists>k'. k' : A \<rightarrow> inverse_image(f, B, m) \<and> inverse_image_subobject_mapping(f, B, m) \<circ>\<^sub>c k' = a"
      using k_type m'_k_eq_a by auto
  qed
qed

text \<open>The lemma below corresponds to Exercise 2.3.10 in Halvorson.\<close>
lemma in_inv_image_of_image:
  assumes Am_sub: "subobject_of(A, m, X)"
  assumes f_type: "f : X \<rightarrow> Y"
  shows "relative_subset(A, m, X,
      inverse_image(f, image_of(f, A, m), image_subobject_mapping(f, A, m)),
      inverse_image_subobject_mapping(f, image_of(f, A, m), image_subobject_mapping(f, A, m)))"
proof -
  have m_type: "m : A \<rightarrow> X" using Am_sub unfolding subobject_of_def by auto

  have subobj_map_type: "image_subobject_mapping(f, A, m) : image_of(f, A, m) \<rightarrow> Y"
    using image_subobj_map_type[OF f_type m_type] by simp
  have subobj_map_mono: "monomorphism(image_subobject_mapping(f, A, m))"
    using image_subobj_map_mono[OF f_type m_type] by simp
  have idFA_type: "id(image_of(f, A, m)) : image_of(f, A, m) \<rightarrow> image_of(f, A, m)" by (rule id_type)
  have idFA_eq: "image_subobject_mapping(f, A, m) \<circ>\<^sub>c id(image_of(f, A, m)) = image_subobject_mapping(f, A, m)"
    using id_right_unit2[OF subobj_map_type] by simp

  have self_rel_sub: "relative_subset(image_of(f, A, m), image_subobject_mapping(f, A, m), Y,
      image_of(f, A, m), image_subobject_mapping(f, A, m))"
    unfolding relative_subset_def
  proof (intro conjI)
    show "image_subobject_mapping(f, A, m) : image_of(f, A, m) \<rightarrow> Y" by (rule subobj_map_type)
  next
    show "monomorphism(image_subobject_mapping(f, A, m))" by (rule subobj_map_mono)
  next
    show "image_subobject_mapping(f, A, m) : image_of(f, A, m) \<rightarrow> Y" by (rule subobj_map_type)
  next
    show "monomorphism(image_subobject_mapping(f, A, m))" by (rule subobj_map_mono)
  next
    show "\<exists>k. k : image_of(f, A, m) \<rightarrow> image_of(f, A, m) \<and>
        image_subobject_mapping(f, A, m) \<circ>\<^sub>c k = image_subobject_mapping(f, A, m)"
      using idFA_type idFA_eq by auto
  qed

  have img_subobj: "subobject_of(image_of(f, A, m), image_subobject_mapping(f, A, m), Y)"
    unfolding subobject_of_def using subobj_map_type subobj_map_mono by simp

  show ?thesis
    using subset_inv_image_iff_image_subset[OF Am_sub img_subobj f_type] self_rel_sub by simp
qed

subsection \<open>@{text distribute_left} and @{text distribute_right} as Equivalence Relations\<close>

lemma left_pair_subset:
  assumes m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" and m_mono: "monomorphism(m)"
  shows "subobject_of(Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)), (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z))"
proof -
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have idZ_mono: "monomorphism(id(Z))"
    using iso_imp_epi_and_monic[OF id_isomorphism] by (rule conjunct2)
  have mid_type: "m \<times>\<^sub>f id(Z) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c X) \<times>\<^sub>c Z"
    using m_type idZ_type cfunc_cross_prod_type by auto
  have mid_mono: "monomorphism(m \<times>\<^sub>f id(Z))"
    using cfunc_cross_prod_mono[OF m_type idZ_type m_mono idZ_mono] by simp
  have dr_type: "distribute_right(X, X, Z) : (X \<times>\<^sub>c X) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    by (rule distribute_right_type)
  have dr_mono: "monomorphism(distribute_right(X, X, Z))" by (rule distribute_right_mono)
  have cod_dom: "codomain(m \<times>\<^sub>f id(Z)) = domain(distribute_right(X, X, Z))"
    using mid_type dr_type unfolding cfunc_type_def by auto
  have comp_type_res: "distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    using mid_type dr_type comp_type by blast
  have comp_mono: "monomorphism(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
    using composition_of_monic_pair_is_monic[OF cod_dom mid_mono dr_mono] by simp
  show ?thesis unfolding subobject_of_def using comp_type_res comp_mono by auto
qed

lemma right_pair_subset:
  assumes m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" and m_mono: "monomorphism(m)"
  shows "subobject_of(Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m), (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X))"
proof -
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have idZ_mono: "monomorphism(id(Z))"
    using iso_imp_epi_and_monic[OF id_isomorphism] by (rule conjunct2)
  have idm_type: "id(Z) \<times>\<^sub>f m : Z \<times>\<^sub>c Y \<rightarrow> Z \<times>\<^sub>c (X \<times>\<^sub>c X)"
    using idZ_type m_type cfunc_cross_prod_type by auto
  have idm_mono: "monomorphism(id(Z) \<times>\<^sub>f m)"
    using cfunc_cross_prod_mono[OF idZ_type m_type idZ_mono m_mono] by simp
  have dl_type: "distribute_left(Z, X, X) : Z \<times>\<^sub>c (X \<times>\<^sub>c X) \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    by (rule distribute_left_type)
  have dl_mono: "monomorphism(distribute_left(Z, X, X))" by (rule distribute_left_mono)
  have cod_dom: "codomain(id(Z) \<times>\<^sub>f m) = domain(distribute_left(Z, X, X))"
    using idm_type dl_type unfolding cfunc_type_def by auto
  have comp_type_res: "distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m) : Z \<times>\<^sub>c Y \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    using idm_type dl_type comp_type by blast
  have comp_mono: "monomorphism(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
    using composition_of_monic_pair_is_monic[OF cod_dom idm_mono dl_mono] by simp
  show ?thesis unfolding subobject_of_def using comp_type_res comp_mono by auto
qed

lemma left_pair_reflexive:
  assumes refl_Y: "reflexive_on(X, Y, m)"
  shows "reflexive_on(X \<times>\<^sub>c Z, Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
proof -
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using refl_Y unfolding reflexive_on_def subobject_of_def by auto
  have m_mono: "monomorphism(m)" using refl_Y unfolding reflexive_on_def subobject_of_def by auto
  have sub: "subobject_of(Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)), (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z))"
    using left_pair_subset[OF m_type m_mono] by simp
  have comp_type_res: "distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    using sub unfolding subobject_of_def by auto
  have comp_mono: "monomorphism(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
    using sub unfolding subobject_of_def by auto
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have mid_type: "m \<times>\<^sub>f id(Z) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c X) \<times>\<^sub>c Z"
    using m_type idZ_type cfunc_cross_prod_type by auto
  have dr_type: "distribute_right(X, X, Z) : (X \<times>\<^sub>c X) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    by (rule distribute_right_type)
  have main: "\<forall>xz. xz \<in>\<^sub>c X \<times>\<^sub>c Z \<longrightarrow>
      relative_member(\<langle>xz,xz\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
  proof (intro allI impI)
    fix xz
    assume xz_type: "xz \<in>\<^sub>c X \<times>\<^sub>c Z"
    obtain x z where x_type: "x \<in>\<^sub>c X" and z_type: "z \<in>\<^sub>c Z" and xz_eq: "xz = \<langle>x,z\<rangle>"
      using cart_prod_decomp[OF xz_type] by blast
    obtain y where y_type: "y \<in>\<^sub>c Y" and y_eq: "m \<circ>\<^sub>c y = \<langle>x,x\<rangle>"
      using reflexive_def2[OF refl_Y x_type] by auto
    have yz_type: "\<langle>y,z\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z" using y_type z_type cfunc_prod_type by auto
    have step1: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,z\<rangle>
        = distribute_right(X, X, Z) \<circ>\<^sub>c ((m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,z\<rangle>)"
      using comp_associative2[OF yz_type mid_type dr_type] by simp
    have idZ_z: "id(Z) \<circ>\<^sub>c z = z" using id_left_unit2[OF z_type] by simp
    have step2: "(m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,z\<rangle> = \<langle>m \<circ>\<^sub>c y, id(Z) \<circ>\<^sub>c z\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF y_type z_type m_type idZ_type] by simp
    have step3: "\<langle>m \<circ>\<^sub>c y, id(Z) \<circ>\<^sub>c z\<rangle> = \<langle>\<langle>x,x\<rangle>, z\<rangle>" using y_eq idZ_z by simp
    have step4: "distribute_right(X, X, Z) \<circ>\<^sub>c \<langle>\<langle>x,x\<rangle>, z\<rangle> = \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle>"
      using distribute_right_ap[OF x_type x_type z_type] by simp
    have main_eq: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,z\<rangle> = \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle>"
      using step1 step2 step3 step4 by simp
    have xzxz_type: "\<langle>xz,xz\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)" using xz_type cfunc_prod_type by auto
    have xzxz_eq: "\<langle>xz,xz\<rangle> = \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle>" using xz_eq by simp
    have witness_eq: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,z\<rangle> = \<langle>xz,xz\<rangle>"
      using main_eq xzxz_eq by simp
    have factorsthru: "\<langle>xz,xz\<rangle> factorsthru (distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      using factors_through_def2[OF xzxz_type comp_type_res] yz_type witness_eq by auto
    show "relative_member(\<langle>xz,xz\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      unfolding relative_member_def using xzxz_type comp_mono comp_type_res factorsthru by auto
  qed
  show ?thesis unfolding reflexive_on_def using sub main by auto
qed

lemma right_pair_reflexive:
  assumes refl_Y: "reflexive_on(X, Y, m)"
  shows "reflexive_on(Z \<times>\<^sub>c X, Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
proof -
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using refl_Y unfolding reflexive_on_def subobject_of_def by auto
  have m_mono: "monomorphism(m)" using refl_Y unfolding reflexive_on_def subobject_of_def by auto
  have sub: "subobject_of(Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m), (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X))"
    using right_pair_subset[OF m_type m_mono] by simp
  have comp_type_res: "distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m) : Z \<times>\<^sub>c Y \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    using sub unfolding subobject_of_def by auto
  have comp_mono: "monomorphism(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
    using sub unfolding subobject_of_def by auto
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have idm_type: "id(Z) \<times>\<^sub>f m : Z \<times>\<^sub>c Y \<rightarrow> Z \<times>\<^sub>c (X \<times>\<^sub>c X)"
    using idZ_type m_type cfunc_cross_prod_type by auto
  have dl_type: "distribute_left(Z, X, X) : Z \<times>\<^sub>c (X \<times>\<^sub>c X) \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    by (rule distribute_left_type)
  have main: "\<forall>zx. zx \<in>\<^sub>c Z \<times>\<^sub>c X \<longrightarrow>
      relative_member(\<langle>zx,zx\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
  proof (intro allI impI)
    fix zx
    assume zx_type: "zx \<in>\<^sub>c Z \<times>\<^sub>c X"
    obtain z x where z_type: "z \<in>\<^sub>c Z" and x_type: "x \<in>\<^sub>c X" and zx_eq: "zx = \<langle>z,x\<rangle>"
      using cart_prod_decomp[OF zx_type] by blast
    obtain y where y_type: "y \<in>\<^sub>c Y" and y_eq: "m \<circ>\<^sub>c y = \<langle>x,x\<rangle>"
      using reflexive_def2[OF refl_Y x_type] by auto
    have zy_type: "\<langle>z,y\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c Y" using z_type y_type cfunc_prod_type by auto
    have step1: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y\<rangle>
        = distribute_left(Z, X, X) \<circ>\<^sub>c ((id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y\<rangle>)"
      using comp_associative2[OF zy_type idm_type dl_type] by simp
    have idZ_z: "id(Z) \<circ>\<^sub>c z = z" using id_left_unit2[OF z_type] by simp
    have step2: "(id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y\<rangle> = \<langle>id(Z) \<circ>\<^sub>c z, m \<circ>\<^sub>c y\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF z_type y_type idZ_type m_type] by simp
    have step3: "\<langle>id(Z) \<circ>\<^sub>c z, m \<circ>\<^sub>c y\<rangle> = \<langle>z, \<langle>x,x\<rangle>\<rangle>" using y_eq idZ_z by simp
    have step4: "distribute_left(Z, X, X) \<circ>\<^sub>c \<langle>z, \<langle>x,x\<rangle>\<rangle> = \<langle>\<langle>z,x\<rangle>,\<langle>z,x\<rangle>\<rangle>"
      using distribute_left_ap[OF z_type x_type x_type] by simp
    have main_eq: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y\<rangle> = \<langle>\<langle>z,x\<rangle>,\<langle>z,x\<rangle>\<rangle>"
      using step1 step2 step3 step4 by simp
    have zxzx_type: "\<langle>zx,zx\<rangle> \<in>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)" using zx_type cfunc_prod_type by auto
    have zxzx_eq: "\<langle>zx,zx\<rangle> = \<langle>\<langle>z,x\<rangle>,\<langle>z,x\<rangle>\<rangle>" using zx_eq by simp
    have witness_eq: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y\<rangle> = \<langle>zx,zx\<rangle>"
      using main_eq zxzx_eq by simp
    have factorsthru: "\<langle>zx,zx\<rangle> factorsthru (distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      using factors_through_def2[OF zxzx_type comp_type_res] zy_type witness_eq by auto
    show "relative_member(\<langle>zx,zx\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      unfolding relative_member_def using zxzx_type comp_mono comp_type_res factorsthru by auto
  qed
  show ?thesis unfolding reflexive_on_def using sub main by auto
qed

lemma left_pair_symmetric:
  assumes sym_Y: "symmetric_on(X, Y, m)"
  shows "symmetric_on(X \<times>\<^sub>c Z, Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
proof -
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using sym_Y unfolding symmetric_on_def subobject_of_def by auto
  have m_mono: "monomorphism(m)" using sym_Y unfolding symmetric_on_def subobject_of_def by auto
  have sub: "subobject_of(Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)), (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z))"
    using left_pair_subset[OF m_type m_mono] by simp
  have comp_type_res: "distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    using sub unfolding subobject_of_def by auto
  have comp_mono: "monomorphism(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
    using sub unfolding subobject_of_def by auto
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have mid_type: "m \<times>\<^sub>f id(Z) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c X) \<times>\<^sub>c Z"
    using m_type idZ_type cfunc_cross_prod_type by auto
  have dr_type: "distribute_right(X, X, Z) : (X \<times>\<^sub>c X) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    by (rule distribute_right_type)
  have main: "\<forall>s t. s \<in>\<^sub>c X \<times>\<^sub>c Z \<and> t \<in>\<^sub>c X \<times>\<^sub>c Z \<longrightarrow>
      (relative_member(\<langle>s,t\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))
        \<longrightarrow> relative_member(\<langle>t,s\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))))"
  proof (intro allI impI)
    fix s t
    assume "s \<in>\<^sub>c X \<times>\<^sub>c Z \<and> t \<in>\<^sub>c X \<times>\<^sub>c Z"
    then have s_type: "s \<in>\<^sub>c X \<times>\<^sub>c Z" and t_type: "t \<in>\<^sub>c X \<times>\<^sub>c Z" by auto
    assume st_mem: "relative_member(\<langle>s,t\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
    have st_factorsthru: "\<langle>s,t\<rangle> factorsthru (distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      using st_mem unfolding relative_member_def by auto
    have st_type: "\<langle>s,t\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)" using s_type t_type cfunc_prod_type by auto
    obtain yz where yz_type: "yz : \<one> \<rightarrow> Y \<times>\<^sub>c Z"
        and yz_eq: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c yz = \<langle>s,t\<rangle>"
      using factors_through_def2[OF st_type comp_type_res] st_factorsthru by auto
    obtain y z where y_type: "y \<in>\<^sub>c Y" and z_type: "z \<in>\<^sub>c Z" and yz_eq2: "yz = \<langle>y,z\<rangle>"
      using cart_prod_decomp[OF yz_type] by blast
    have my_type: "m \<circ>\<^sub>c y : \<one> \<rightarrow> X \<times>\<^sub>c X" using y_type m_type comp_type by blast
    obtain my1 my2 where my1_type: "my1 \<in>\<^sub>c X" and my2_type: "my2 \<in>\<^sub>c X" and my_eq: "m \<circ>\<^sub>c y = \<langle>my1,my2\<rangle>"
      using cart_prod_decomp[OF my_type] by blast
    have rel_ex: "\<exists>v. v \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c v = \<langle>my1,my2\<rangle>" using y_type my_eq by auto
    obtain y' where y'_type: "y' \<in>\<^sub>c Y" and y'_eq: "m \<circ>\<^sub>c y' = \<langle>my2,my1\<rangle>"
      using symmetric_def2[OF sym_Y my1_type my2_type rel_ex] by auto

    have yz_pair_type: "\<langle>y,z\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z" using y_type z_type cfunc_prod_type by auto
    have yz_eq3: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,z\<rangle> = \<langle>s,t\<rangle>"
      using yz_eq yz_eq2 by simp
    have step1: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,z\<rangle>
        = distribute_right(X, X, Z) \<circ>\<^sub>c ((m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,z\<rangle>)"
      using comp_associative2[OF yz_pair_type mid_type dr_type] by simp
    have idZ_z: "id(Z) \<circ>\<^sub>c z = z" using id_left_unit2[OF z_type] by simp
    have step2: "(m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,z\<rangle> = \<langle>m \<circ>\<^sub>c y, id(Z) \<circ>\<^sub>c z\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF y_type z_type m_type idZ_type] by simp
    have step3: "\<langle>m \<circ>\<^sub>c y, id(Z) \<circ>\<^sub>c z\<rangle> = \<langle>\<langle>my1,my2\<rangle>, z\<rangle>" using my_eq idZ_z by simp
    have step4: "distribute_right(X, X, Z) \<circ>\<^sub>c \<langle>\<langle>my1,my2\<rangle>, z\<rangle> = \<langle>\<langle>my1,z\<rangle>,\<langle>my2,z\<rangle>\<rangle>"
      using distribute_right_ap[OF my1_type my2_type z_type] by simp
    have main_eq: "\<langle>s,t\<rangle> = \<langle>\<langle>my1,z\<rangle>,\<langle>my2,z\<rangle>\<rangle>"
      using yz_eq3 step1 step2 step3 step4 by simp

    have my1z_type: "\<langle>my1,z\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using my1_type z_type cfunc_prod_type by auto
    have my2z_type: "\<langle>my2,z\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using my2_type z_type cfunc_prod_type by auto
    have split_eq: "s = \<langle>my1,z\<rangle> \<and> t = \<langle>my2,z\<rangle>"
      using main_eq cart_prod_eq2[OF s_type t_type my1z_type my2z_type] by auto
    have s_eq2: "s = \<langle>my1,z\<rangle>" using split_eq by simp
    have t_eq2: "t = \<langle>my2,z\<rangle>" using split_eq by simp

    have y'z_type: "\<langle>y',z\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z" using y'_type z_type cfunc_prod_type by auto
    have w_step1: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y',z\<rangle>
        = distribute_right(X, X, Z) \<circ>\<^sub>c ((m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y',z\<rangle>)"
      using comp_associative2[OF y'z_type mid_type dr_type] by simp
    have w_step2: "(m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y',z\<rangle> = \<langle>m \<circ>\<^sub>c y', id(Z) \<circ>\<^sub>c z\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF y'_type z_type m_type idZ_type] by simp
    have w_step3: "\<langle>m \<circ>\<^sub>c y', id(Z) \<circ>\<^sub>c z\<rangle> = \<langle>\<langle>my2,my1\<rangle>, z\<rangle>" using y'_eq idZ_z by simp
    have w_step4: "distribute_right(X, X, Z) \<circ>\<^sub>c \<langle>\<langle>my2,my1\<rangle>, z\<rangle> = \<langle>\<langle>my2,z\<rangle>,\<langle>my1,z\<rangle>\<rangle>"
      using distribute_right_ap[OF my2_type my1_type z_type] by simp
    have w_main_eq: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y',z\<rangle> = \<langle>\<langle>my2,z\<rangle>,\<langle>my1,z\<rangle>\<rangle>"
      using w_step1 w_step2 w_step3 w_step4 by simp
    have w_eq_ts: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y',z\<rangle> = \<langle>t,s\<rangle>"
      using w_main_eq t_eq2 s_eq2 by simp
    have ts_type: "\<langle>t,s\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)" using t_type s_type cfunc_prod_type by auto
    have ts_factorsthru: "\<langle>t,s\<rangle> factorsthru (distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      using factors_through_def2[OF ts_type comp_type_res] y'z_type w_eq_ts by auto
    show "relative_member(\<langle>t,s\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      unfolding relative_member_def using ts_type comp_mono comp_type_res ts_factorsthru by auto
  qed
  show ?thesis unfolding symmetric_on_def using sub main by auto
qed

lemma right_pair_symmetric:
  assumes sym_Y: "symmetric_on(X, Y, m)"
  shows "symmetric_on(Z \<times>\<^sub>c X, Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
proof -
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using sym_Y unfolding symmetric_on_def subobject_of_def by auto
  have m_mono: "monomorphism(m)" using sym_Y unfolding symmetric_on_def subobject_of_def by auto
  have sub: "subobject_of(Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m), (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X))"
    using right_pair_subset[OF m_type m_mono] by simp
  have comp_type_res: "distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m) : Z \<times>\<^sub>c Y \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    using sub unfolding subobject_of_def by auto
  have comp_mono: "monomorphism(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
    using sub unfolding subobject_of_def by auto
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have idm_type: "id(Z) \<times>\<^sub>f m : Z \<times>\<^sub>c Y \<rightarrow> Z \<times>\<^sub>c (X \<times>\<^sub>c X)"
    using idZ_type m_type cfunc_cross_prod_type by auto
  have dl_type: "distribute_left(Z, X, X) : Z \<times>\<^sub>c (X \<times>\<^sub>c X) \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    by (rule distribute_left_type)
  have main: "\<forall>s t. s \<in>\<^sub>c Z \<times>\<^sub>c X \<and> t \<in>\<^sub>c Z \<times>\<^sub>c X \<longrightarrow>
      (relative_member(\<langle>s,t\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))
        \<longrightarrow> relative_member(\<langle>t,s\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)))"
  proof (intro allI impI)
    fix s t
    assume "s \<in>\<^sub>c Z \<times>\<^sub>c X \<and> t \<in>\<^sub>c Z \<times>\<^sub>c X"
    then have s_type: "s \<in>\<^sub>c Z \<times>\<^sub>c X" and t_type: "t \<in>\<^sub>c Z \<times>\<^sub>c X" by auto
    assume st_mem: "relative_member(\<langle>s,t\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
    have st_factorsthru: "\<langle>s,t\<rangle> factorsthru (distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      using st_mem unfolding relative_member_def by auto
    have st_type: "\<langle>s,t\<rangle> \<in>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)" using s_type t_type cfunc_prod_type by auto
    obtain zy where zy_type: "zy : \<one> \<rightarrow> Z \<times>\<^sub>c Y"
        and zy_eq: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c zy = \<langle>s,t\<rangle>"
      using factors_through_def2[OF st_type comp_type_res] st_factorsthru by auto
    obtain z y where z_type: "z \<in>\<^sub>c Z" and y_type: "y \<in>\<^sub>c Y" and zy_eq2: "zy = \<langle>z,y\<rangle>"
      using cart_prod_decomp[OF zy_type] by blast
    have my_type: "m \<circ>\<^sub>c y : \<one> \<rightarrow> X \<times>\<^sub>c X" using y_type m_type comp_type by blast
    obtain my1 my2 where my1_type: "my1 \<in>\<^sub>c X" and my2_type: "my2 \<in>\<^sub>c X" and my_eq: "m \<circ>\<^sub>c y = \<langle>my1,my2\<rangle>"
      using cart_prod_decomp[OF my_type] by blast
    have rel_ex: "\<exists>v. v \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c v = \<langle>my1,my2\<rangle>" using y_type my_eq by auto
    obtain y' where y'_type: "y' \<in>\<^sub>c Y" and y'_eq: "m \<circ>\<^sub>c y' = \<langle>my2,my1\<rangle>"
      using symmetric_def2[OF sym_Y my1_type my2_type rel_ex] by auto

    have zy_pair_type: "\<langle>z,y\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c Y" using z_type y_type cfunc_prod_type by auto
    have zy_eq3: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y\<rangle> = \<langle>s,t\<rangle>"
      using zy_eq zy_eq2 by simp
    have step1: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y\<rangle>
        = distribute_left(Z, X, X) \<circ>\<^sub>c ((id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y\<rangle>)"
      using comp_associative2[OF zy_pair_type idm_type dl_type] by simp
    have idZ_z: "id(Z) \<circ>\<^sub>c z = z" using id_left_unit2[OF z_type] by simp
    have step2: "(id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y\<rangle> = \<langle>id(Z) \<circ>\<^sub>c z, m \<circ>\<^sub>c y\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF z_type y_type idZ_type m_type] by simp
    have step3: "\<langle>id(Z) \<circ>\<^sub>c z, m \<circ>\<^sub>c y\<rangle> = \<langle>z, \<langle>my1,my2\<rangle>\<rangle>" using my_eq idZ_z by simp
    have step4: "distribute_left(Z, X, X) \<circ>\<^sub>c \<langle>z, \<langle>my1,my2\<rangle>\<rangle> = \<langle>\<langle>z,my1\<rangle>,\<langle>z,my2\<rangle>\<rangle>"
      using distribute_left_ap[OF z_type my1_type my2_type] by simp
    have main_eq: "\<langle>s,t\<rangle> = \<langle>\<langle>z,my1\<rangle>,\<langle>z,my2\<rangle>\<rangle>"
      using zy_eq3 step1 step2 step3 step4 by simp

    have zmy1_type: "\<langle>z,my1\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c X" using z_type my1_type cfunc_prod_type by auto
    have zmy2_type: "\<langle>z,my2\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c X" using z_type my2_type cfunc_prod_type by auto
    have split_eq: "s = \<langle>z,my1\<rangle> \<and> t = \<langle>z,my2\<rangle>"
      using main_eq cart_prod_eq2[OF s_type t_type zmy1_type zmy2_type] by auto
    have s_eq2: "s = \<langle>z,my1\<rangle>" using split_eq by simp
    have t_eq2: "t = \<langle>z,my2\<rangle>" using split_eq by simp

    have zy'_type: "\<langle>z,y'\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c Y" using z_type y'_type cfunc_prod_type by auto
    have w_step1: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y'\<rangle>
        = distribute_left(Z, X, X) \<circ>\<^sub>c ((id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y'\<rangle>)"
      using comp_associative2[OF zy'_type idm_type dl_type] by simp
    have w_step2: "(id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y'\<rangle> = \<langle>id(Z) \<circ>\<^sub>c z, m \<circ>\<^sub>c y'\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF z_type y'_type idZ_type m_type] by simp
    have w_step3: "\<langle>id(Z) \<circ>\<^sub>c z, m \<circ>\<^sub>c y'\<rangle> = \<langle>z, \<langle>my2,my1\<rangle>\<rangle>" using y'_eq idZ_z by simp
    have w_step4: "distribute_left(Z, X, X) \<circ>\<^sub>c \<langle>z, \<langle>my2,my1\<rangle>\<rangle> = \<langle>\<langle>z,my2\<rangle>,\<langle>z,my1\<rangle>\<rangle>"
      using distribute_left_ap[OF z_type my2_type my1_type] by simp
    have w_main_eq: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y'\<rangle> = \<langle>\<langle>z,my2\<rangle>,\<langle>z,my1\<rangle>\<rangle>"
      using w_step1 w_step2 w_step3 w_step4 by simp
    have w_eq_ts: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y'\<rangle> = \<langle>t,s\<rangle>"
      using w_main_eq t_eq2 s_eq2 by simp
    have ts_type: "\<langle>t,s\<rangle> \<in>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)" using t_type s_type cfunc_prod_type by auto
    have ts_factorsthru: "\<langle>t,s\<rangle> factorsthru (distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      using factors_through_def2[OF ts_type comp_type_res] zy'_type w_eq_ts by auto
    show "relative_member(\<langle>t,s\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      unfolding relative_member_def using ts_type comp_mono comp_type_res ts_factorsthru by auto
  qed
  show ?thesis unfolding symmetric_on_def using sub main by auto
qed

lemma left_pair_transitive:
  assumes trans_Y: "transitive_on(X, Y, m)"
  shows "transitive_on(X \<times>\<^sub>c Z, Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
proof -
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using trans_Y unfolding transitive_on_def subobject_of_def by auto
  have m_mono: "monomorphism(m)" using trans_Y unfolding transitive_on_def subobject_of_def by auto
  have sub: "subobject_of(Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)), (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z))"
    using left_pair_subset[OF m_type m_mono] by simp
  have comp_type_res: "distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    using sub unfolding subobject_of_def by auto
  have comp_mono: "monomorphism(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
    using sub unfolding subobject_of_def by auto
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have mid_type: "m \<times>\<^sub>f id(Z) : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c X) \<times>\<^sub>c Z"
    using m_type idZ_type cfunc_cross_prod_type by auto
  have dr_type: "distribute_right(X, X, Z) : (X \<times>\<^sub>c X) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
    by (rule distribute_right_type)
  have main: "\<forall>s t u. s \<in>\<^sub>c X \<times>\<^sub>c Z \<and> t \<in>\<^sub>c X \<times>\<^sub>c Z \<and> u \<in>\<^sub>c X \<times>\<^sub>c Z \<longrightarrow>
      (relative_member(\<langle>s,t\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))
        \<and> relative_member(\<langle>t,u\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))
        \<longrightarrow> relative_member(\<langle>s,u\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))))"
  proof (intro allI impI)
    fix s t u
    assume "s \<in>\<^sub>c X \<times>\<^sub>c Z \<and> t \<in>\<^sub>c X \<times>\<^sub>c Z \<and> u \<in>\<^sub>c X \<times>\<^sub>c Z"
    then have s_type: "s \<in>\<^sub>c X \<times>\<^sub>c Z" and t_type: "t \<in>\<^sub>c X \<times>\<^sub>c Z" and u_type: "u \<in>\<^sub>c X \<times>\<^sub>c Z" by auto
    assume "relative_member(\<langle>s,t\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))
        \<and> relative_member(\<langle>t,u\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
    then have st_mem: "relative_member(\<langle>s,t\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      and tu_mem: "relative_member(\<langle>t,u\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      by auto

    have st_factorsthru: "\<langle>s,t\<rangle> factorsthru (distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      using st_mem unfolding relative_member_def by auto
    have st_type: "\<langle>s,t\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)" using s_type t_type cfunc_prod_type by auto
    obtain h where h_type: "h : \<one> \<rightarrow> Y \<times>\<^sub>c Z"
        and h_eq: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c h = \<langle>s,t\<rangle>"
      using factors_through_def2[OF st_type comp_type_res] st_factorsthru by auto
    obtain hy hz where hy_type: "hy \<in>\<^sub>c Y" and hz_type: "hz \<in>\<^sub>c Z" and h_eq2: "h = \<langle>hy,hz\<rangle>"
      using cart_prod_decomp[OF h_type] by blast
    have mhy_type: "m \<circ>\<^sub>c hy : \<one> \<rightarrow> X \<times>\<^sub>c X" using hy_type m_type comp_type by blast
    obtain mhy1 mhy2 where mhy1_type: "mhy1 \<in>\<^sub>c X" and mhy2_type: "mhy2 \<in>\<^sub>c X" and mhy_eq: "m \<circ>\<^sub>c hy = \<langle>mhy1,mhy2\<rangle>"
      using cart_prod_decomp[OF mhy_type] by blast

    have hpair_type: "\<langle>hy,hz\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z" using hy_type hz_type cfunc_prod_type by auto
    have h_eq3: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>hy,hz\<rangle> = \<langle>s,t\<rangle>"
      using h_eq h_eq2 by simp
    have step1: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>hy,hz\<rangle>
        = distribute_right(X, X, Z) \<circ>\<^sub>c ((m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>hy,hz\<rangle>)"
      using comp_associative2[OF hpair_type mid_type dr_type] by simp
    have idZ_hz: "id(Z) \<circ>\<^sub>c hz = hz" using id_left_unit2[OF hz_type] by simp
    have step2: "(m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>hy,hz\<rangle> = \<langle>m \<circ>\<^sub>c hy, id(Z) \<circ>\<^sub>c hz\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF hy_type hz_type m_type idZ_type] by simp
    have step3: "\<langle>m \<circ>\<^sub>c hy, id(Z) \<circ>\<^sub>c hz\<rangle> = \<langle>\<langle>mhy1,mhy2\<rangle>, hz\<rangle>" using mhy_eq idZ_hz by simp
    have step4: "distribute_right(X, X, Z) \<circ>\<^sub>c \<langle>\<langle>mhy1,mhy2\<rangle>, hz\<rangle> = \<langle>\<langle>mhy1,hz\<rangle>,\<langle>mhy2,hz\<rangle>\<rangle>"
      using distribute_right_ap[OF mhy1_type mhy2_type hz_type] by simp
    have main_eq_st: "\<langle>s,t\<rangle> = \<langle>\<langle>mhy1,hz\<rangle>,\<langle>mhy2,hz\<rangle>\<rangle>"
      using h_eq3 step1 step2 step3 step4 by simp

    have mhy1hz_type: "\<langle>mhy1,hz\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using mhy1_type hz_type cfunc_prod_type by auto
    have mhy2hz_type: "\<langle>mhy2,hz\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using mhy2_type hz_type cfunc_prod_type by auto
    have split_eq_st: "s = \<langle>mhy1,hz\<rangle> \<and> t = \<langle>mhy2,hz\<rangle>"
      using main_eq_st cart_prod_eq2[OF s_type t_type mhy1hz_type mhy2hz_type] by auto
    have s_eq: "s = \<langle>mhy1,hz\<rangle>" using split_eq_st by simp
    have t_eq: "t = \<langle>mhy2,hz\<rangle>" using split_eq_st by simp

    have tu_factorsthru: "\<langle>t,u\<rangle> factorsthru (distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      using tu_mem unfolding relative_member_def by auto
    have tu_type: "\<langle>t,u\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)" using t_type u_type cfunc_prod_type by auto
    obtain g where g_type: "g : \<one> \<rightarrow> Y \<times>\<^sub>c Z"
        and g_eq: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c g = \<langle>t,u\<rangle>"
      using factors_through_def2[OF tu_type comp_type_res] tu_factorsthru by auto
    obtain gy gz where gy_type: "gy \<in>\<^sub>c Y" and gz_type: "gz \<in>\<^sub>c Z" and g_eq2: "g = \<langle>gy,gz\<rangle>"
      using cart_prod_decomp[OF g_type] by blast
    have mgy_type: "m \<circ>\<^sub>c gy : \<one> \<rightarrow> X \<times>\<^sub>c X" using gy_type m_type comp_type by blast
    obtain mgy1 mgy2 where mgy1_type: "mgy1 \<in>\<^sub>c X" and mgy2_type: "mgy2 \<in>\<^sub>c X" and mgy_eq: "m \<circ>\<^sub>c gy = \<langle>mgy1,mgy2\<rangle>"
      using cart_prod_decomp[OF mgy_type] by blast

    have gpair_type: "\<langle>gy,gz\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z" using gy_type gz_type cfunc_prod_type by auto
    have g_eq3: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>gy,gz\<rangle> = \<langle>t,u\<rangle>"
      using g_eq g_eq2 by simp
    have gstep1: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>gy,gz\<rangle>
        = distribute_right(X, X, Z) \<circ>\<^sub>c ((m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>gy,gz\<rangle>)"
      using comp_associative2[OF gpair_type mid_type dr_type] by simp
    have idZ_gz: "id(Z) \<circ>\<^sub>c gz = gz" using id_left_unit2[OF gz_type] by simp
    have gstep2: "(m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>gy,gz\<rangle> = \<langle>m \<circ>\<^sub>c gy, id(Z) \<circ>\<^sub>c gz\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF gy_type gz_type m_type idZ_type] by simp
    have gstep3: "\<langle>m \<circ>\<^sub>c gy, id(Z) \<circ>\<^sub>c gz\<rangle> = \<langle>\<langle>mgy1,mgy2\<rangle>, gz\<rangle>" using mgy_eq idZ_gz by simp
    have gstep4: "distribute_right(X, X, Z) \<circ>\<^sub>c \<langle>\<langle>mgy1,mgy2\<rangle>, gz\<rangle> = \<langle>\<langle>mgy1,gz\<rangle>,\<langle>mgy2,gz\<rangle>\<rangle>"
      using distribute_right_ap[OF mgy1_type mgy2_type gz_type] by simp
    have main_eq_tu: "\<langle>t,u\<rangle> = \<langle>\<langle>mgy1,gz\<rangle>,\<langle>mgy2,gz\<rangle>\<rangle>"
      using g_eq3 gstep1 gstep2 gstep3 gstep4 by simp

    have mgy1gz_type: "\<langle>mgy1,gz\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using mgy1_type gz_type cfunc_prod_type by auto
    have mgy2gz_type: "\<langle>mgy2,gz\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using mgy2_type gz_type cfunc_prod_type by auto
    have split_eq_tu: "t = \<langle>mgy1,gz\<rangle> \<and> u = \<langle>mgy2,gz\<rangle>"
      using main_eq_tu cart_prod_eq2[OF t_type u_type mgy1gz_type mgy2gz_type] by auto
    have t_eq2: "t = \<langle>mgy1,gz\<rangle>" using split_eq_tu by simp
    have u_eq: "u = \<langle>mgy2,gz\<rangle>" using split_eq_tu by simp

    have t_eq_combined: "\<langle>mhy2,hz\<rangle> = \<langle>mgy1,gz\<rangle>" using t_eq t_eq2 by simp
    have split_t: "mhy2 = mgy1 \<and> hz = gz"
      using t_eq_combined cart_prod_eq2[OF mhy2_type hz_type mgy1_type gz_type] by auto
    have mhy2_eq_mgy1: "mhy2 = mgy1" using split_t by simp
    have hz_eq_gz: "hz = gz" using split_t by simp

    have mhy1mhy2_type: "\<langle>mhy1,mhy2\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using mhy1_type mhy2_type cfunc_prod_type by auto
    have mhy_factorsthru: "\<langle>mhy1,mhy2\<rangle> factorsthru m"
      using factors_through_def2[OF mhy1mhy2_type m_type] hy_type mhy_eq by auto

    have mhy2mgy2_type: "\<langle>mhy2,mgy2\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using mhy2_type mgy2_type cfunc_prod_type by auto
    have mgy_eq2: "m \<circ>\<^sub>c gy = \<langle>mhy2,mgy2\<rangle>" using mgy_eq mhy2_eq_mgy1 by simp
    have mgy_factorsthru: "\<langle>mhy2,mgy2\<rangle> factorsthru m"
      using factors_through_def2[OF mhy2mgy2_type m_type] gy_type mgy_eq2 by auto

    have mhy1mhy2_rel_ex: "\<exists>v. v \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c v = \<langle>mhy1,mhy2\<rangle>" using hy_type mhy_eq by auto
    have mhy2mgy2_rel_ex: "\<exists>w. w \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c w = \<langle>mhy2,mgy2\<rangle>" using gy_type mgy_eq2 by auto

    obtain y where y_type: "y \<in>\<^sub>c Y" and y_eq: "m \<circ>\<^sub>c y = \<langle>mhy1,mgy2\<rangle>"
      using transitive_def2[OF trans_Y mhy1_type mhy2_type mgy2_type mhy1mhy2_rel_ex mhy2mgy2_rel_ex] by auto

    have ygz_type: "\<langle>y,gz\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z" using y_type gz_type cfunc_prod_type by auto
    have wstep1: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,gz\<rangle>
        = distribute_right(X, X, Z) \<circ>\<^sub>c ((m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,gz\<rangle>)"
      using comp_associative2[OF ygz_type mid_type dr_type] by simp
    have idZ_gz2: "id(Z) \<circ>\<^sub>c gz = gz" using id_left_unit2[OF gz_type] by simp
    have wstep2: "(m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,gz\<rangle> = \<langle>m \<circ>\<^sub>c y, id(Z) \<circ>\<^sub>c gz\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF y_type gz_type m_type idZ_type] by simp
    have wstep3: "\<langle>m \<circ>\<^sub>c y, id(Z) \<circ>\<^sub>c gz\<rangle> = \<langle>\<langle>mhy1,mgy2\<rangle>, gz\<rangle>" using y_eq idZ_gz2 by simp
    have wstep4: "distribute_right(X, X, Z) \<circ>\<^sub>c \<langle>\<langle>mhy1,mgy2\<rangle>, gz\<rangle> = \<langle>\<langle>mhy1,gz\<rangle>,\<langle>mgy2,gz\<rangle>\<rangle>"
      using distribute_right_ap[OF mhy1_type mgy2_type gz_type] by simp
    have wmain_eq: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,gz\<rangle> = \<langle>\<langle>mhy1,gz\<rangle>,\<langle>mgy2,gz\<rangle>\<rangle>"
      using wstep1 wstep2 wstep3 wstep4 by simp

    have s_eq_final: "s = \<langle>mhy1,gz\<rangle>" using s_eq hz_eq_gz by simp
    have u_eq_final: "u = \<langle>mgy2,gz\<rangle>" using u_eq by simp

    have w_eq_su: "(distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z))) \<circ>\<^sub>c \<langle>y,gz\<rangle> = \<langle>s,u\<rangle>"
      using wmain_eq s_eq_final u_eq_final by simp

    have su_type: "\<langle>s,u\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)" using s_type u_type cfunc_prod_type by auto
    have su_factorsthru: "\<langle>s,u\<rangle> factorsthru (distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      using factors_through_def2[OF su_type comp_type_res] ygz_type w_eq_su by auto
    show "relative_member(\<langle>s,u\<rangle>, (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z), Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
      unfolding relative_member_def using su_type comp_mono comp_type_res su_factorsthru by auto
  qed
  show ?thesis unfolding transitive_on_def using sub main by auto
qed

lemma right_pair_transitive:
  assumes trans_Y: "transitive_on(X, Y, m)"
  shows "transitive_on(Z \<times>\<^sub>c X, Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
proof -
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X" using trans_Y unfolding transitive_on_def subobject_of_def by auto
  have m_mono: "monomorphism(m)" using trans_Y unfolding transitive_on_def subobject_of_def by auto
  have sub: "subobject_of(Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m), (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X))"
    using right_pair_subset[OF m_type m_mono] by simp
  have comp_type_res: "distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m) : Z \<times>\<^sub>c Y \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    using sub unfolding subobject_of_def by auto
  have comp_mono: "monomorphism(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
    using sub unfolding subobject_of_def by auto
  have idZ_type: "id(Z) : Z \<rightarrow> Z" by (rule id_type)
  have idm_type: "id(Z) \<times>\<^sub>f m : Z \<times>\<^sub>c Y \<rightarrow> Z \<times>\<^sub>c (X \<times>\<^sub>c X)"
    using idZ_type m_type cfunc_cross_prod_type by auto
  have dl_type: "distribute_left(Z, X, X) : Z \<times>\<^sub>c (X \<times>\<^sub>c X) \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
    by (rule distribute_left_type)
  have main: "\<forall>s t u. s \<in>\<^sub>c Z \<times>\<^sub>c X \<and> t \<in>\<^sub>c Z \<times>\<^sub>c X \<and> u \<in>\<^sub>c Z \<times>\<^sub>c X \<longrightarrow>
      (relative_member(\<langle>s,t\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))
        \<and> relative_member(\<langle>t,u\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))
        \<longrightarrow> relative_member(\<langle>s,u\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)))"
  proof (intro allI impI)
    fix s t u
    assume "s \<in>\<^sub>c Z \<times>\<^sub>c X \<and> t \<in>\<^sub>c Z \<times>\<^sub>c X \<and> u \<in>\<^sub>c Z \<times>\<^sub>c X"
    then have s_type: "s \<in>\<^sub>c Z \<times>\<^sub>c X" and t_type: "t \<in>\<^sub>c Z \<times>\<^sub>c X" and u_type: "u \<in>\<^sub>c Z \<times>\<^sub>c X" by auto
    assume "relative_member(\<langle>s,t\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))
        \<and> relative_member(\<langle>t,u\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
    then have st_mem: "relative_member(\<langle>s,t\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      and tu_mem: "relative_member(\<langle>t,u\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      by auto

    have st_factorsthru: "\<langle>s,t\<rangle> factorsthru (distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      using st_mem unfolding relative_member_def by auto
    have st_type: "\<langle>s,t\<rangle> \<in>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)" using s_type t_type cfunc_prod_type by auto
    obtain h where h_type: "h : \<one> \<rightarrow> Z \<times>\<^sub>c Y"
        and h_eq: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c h = \<langle>s,t\<rangle>"
      using factors_through_def2[OF st_type comp_type_res] st_factorsthru by auto
    obtain hz hy where hz_type: "hz \<in>\<^sub>c Z" and hy_type: "hy \<in>\<^sub>c Y" and h_eq2: "h = \<langle>hz,hy\<rangle>"
      using cart_prod_decomp[OF h_type] by blast
    have mhy_type: "m \<circ>\<^sub>c hy : \<one> \<rightarrow> X \<times>\<^sub>c X" using hy_type m_type comp_type by blast
    obtain mhy1 mhy2 where mhy1_type: "mhy1 \<in>\<^sub>c X" and mhy2_type: "mhy2 \<in>\<^sub>c X" and mhy_eq: "m \<circ>\<^sub>c hy = \<langle>mhy1,mhy2\<rangle>"
      using cart_prod_decomp[OF mhy_type] by blast

    have hpair_type: "\<langle>hz,hy\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c Y" using hz_type hy_type cfunc_prod_type by auto
    have h_eq3: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>hz,hy\<rangle> = \<langle>s,t\<rangle>"
      using h_eq h_eq2 by simp
    have step1: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>hz,hy\<rangle>
        = distribute_left(Z, X, X) \<circ>\<^sub>c ((id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>hz,hy\<rangle>)"
      using comp_associative2[OF hpair_type idm_type dl_type] by simp
    have idZ_hz: "id(Z) \<circ>\<^sub>c hz = hz" using id_left_unit2[OF hz_type] by simp
    have step2: "(id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>hz,hy\<rangle> = \<langle>id(Z) \<circ>\<^sub>c hz, m \<circ>\<^sub>c hy\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF hz_type hy_type idZ_type m_type] by simp
    have step3: "\<langle>id(Z) \<circ>\<^sub>c hz, m \<circ>\<^sub>c hy\<rangle> = \<langle>hz, \<langle>mhy1,mhy2\<rangle>\<rangle>" using mhy_eq idZ_hz by simp
    have step4: "distribute_left(Z, X, X) \<circ>\<^sub>c \<langle>hz, \<langle>mhy1,mhy2\<rangle>\<rangle> = \<langle>\<langle>hz,mhy1\<rangle>,\<langle>hz,mhy2\<rangle>\<rangle>"
      using distribute_left_ap[OF hz_type mhy1_type mhy2_type] by simp
    have main_eq_st: "\<langle>s,t\<rangle> = \<langle>\<langle>hz,mhy1\<rangle>,\<langle>hz,mhy2\<rangle>\<rangle>"
      using h_eq3 step1 step2 step3 step4 by simp

    have hzmhy1_type: "\<langle>hz,mhy1\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c X" using hz_type mhy1_type cfunc_prod_type by auto
    have hzmhy2_type: "\<langle>hz,mhy2\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c X" using hz_type mhy2_type cfunc_prod_type by auto
    have split_eq_st: "s = \<langle>hz,mhy1\<rangle> \<and> t = \<langle>hz,mhy2\<rangle>"
      using main_eq_st cart_prod_eq2[OF s_type t_type hzmhy1_type hzmhy2_type] by auto
    have s_eq: "s = \<langle>hz,mhy1\<rangle>" using split_eq_st by simp
    have t_eq: "t = \<langle>hz,mhy2\<rangle>" using split_eq_st by simp

    have tu_factorsthru: "\<langle>t,u\<rangle> factorsthru (distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      using tu_mem unfolding relative_member_def by auto
    have tu_type: "\<langle>t,u\<rangle> \<in>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)" using t_type u_type cfunc_prod_type by auto
    obtain g where g_type: "g : \<one> \<rightarrow> Z \<times>\<^sub>c Y"
        and g_eq: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c g = \<langle>t,u\<rangle>"
      using factors_through_def2[OF tu_type comp_type_res] tu_factorsthru by auto
    obtain gz gy where gz_type: "gz \<in>\<^sub>c Z" and gy_type: "gy \<in>\<^sub>c Y" and g_eq2: "g = \<langle>gz,gy\<rangle>"
      using cart_prod_decomp[OF g_type] by blast
    have mgy_type: "m \<circ>\<^sub>c gy : \<one> \<rightarrow> X \<times>\<^sub>c X" using gy_type m_type comp_type by blast
    obtain mgy1 mgy2 where mgy1_type: "mgy1 \<in>\<^sub>c X" and mgy2_type: "mgy2 \<in>\<^sub>c X" and mgy_eq: "m \<circ>\<^sub>c gy = \<langle>mgy1,mgy2\<rangle>"
      using cart_prod_decomp[OF mgy_type] by blast

    have gpair_type: "\<langle>gz,gy\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c Y" using gz_type gy_type cfunc_prod_type by auto
    have g_eq3: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>gz,gy\<rangle> = \<langle>t,u\<rangle>"
      using g_eq g_eq2 by simp
    have gstep1: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>gz,gy\<rangle>
        = distribute_left(Z, X, X) \<circ>\<^sub>c ((id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz,gy\<rangle>)"
      using comp_associative2[OF gpair_type idm_type dl_type] by simp
    have idZ_gz: "id(Z) \<circ>\<^sub>c gz = gz" using id_left_unit2[OF gz_type] by simp
    have gstep2: "(id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz,gy\<rangle> = \<langle>id(Z) \<circ>\<^sub>c gz, m \<circ>\<^sub>c gy\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF gz_type gy_type idZ_type m_type] by simp
    have gstep3: "\<langle>id(Z) \<circ>\<^sub>c gz, m \<circ>\<^sub>c gy\<rangle> = \<langle>gz, \<langle>mgy1,mgy2\<rangle>\<rangle>" using mgy_eq idZ_gz by simp
    have gstep4: "distribute_left(Z, X, X) \<circ>\<^sub>c \<langle>gz, \<langle>mgy1,mgy2\<rangle>\<rangle> = \<langle>\<langle>gz,mgy1\<rangle>,\<langle>gz,mgy2\<rangle>\<rangle>"
      using distribute_left_ap[OF gz_type mgy1_type mgy2_type] by simp
    have main_eq_tu: "\<langle>t,u\<rangle> = \<langle>\<langle>gz,mgy1\<rangle>,\<langle>gz,mgy2\<rangle>\<rangle>"
      using g_eq3 gstep1 gstep2 gstep3 gstep4 by simp

    have gzmgy1_type: "\<langle>gz,mgy1\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c X" using gz_type mgy1_type cfunc_prod_type by auto
    have gzmgy2_type: "\<langle>gz,mgy2\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c X" using gz_type mgy2_type cfunc_prod_type by auto
    have split_eq_tu: "t = \<langle>gz,mgy1\<rangle> \<and> u = \<langle>gz,mgy2\<rangle>"
      using main_eq_tu cart_prod_eq2[OF t_type u_type gzmgy1_type gzmgy2_type] by auto
    have t_eq2: "t = \<langle>gz,mgy1\<rangle>" using split_eq_tu by simp
    have u_eq: "u = \<langle>gz,mgy2\<rangle>" using split_eq_tu by simp

    have t_eq_combined: "\<langle>hz,mhy2\<rangle> = \<langle>gz,mgy1\<rangle>" using t_eq t_eq2 by simp
    have split_t: "hz = gz \<and> mhy2 = mgy1"
      using t_eq_combined cart_prod_eq2[OF hz_type mhy2_type gz_type mgy1_type] by auto
    have hz_eq_gz: "hz = gz" using split_t by simp
    have mhy2_eq_mgy1: "mhy2 = mgy1" using split_t by simp

    have mhy1mhy2_type: "\<langle>mhy1,mhy2\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using mhy1_type mhy2_type cfunc_prod_type by auto
    have mhy_factorsthru: "\<langle>mhy1,mhy2\<rangle> factorsthru m"
      using factors_through_def2[OF mhy1mhy2_type m_type] hy_type mhy_eq by auto

    have mhy2mgy2_type: "\<langle>mhy2,mgy2\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using mhy2_type mgy2_type cfunc_prod_type by auto
    have mgy_eq2: "m \<circ>\<^sub>c gy = \<langle>mhy2,mgy2\<rangle>" using mgy_eq mhy2_eq_mgy1 by simp
    have mgy_factorsthru: "\<langle>mhy2,mgy2\<rangle> factorsthru m"
      using factors_through_def2[OF mhy2mgy2_type m_type] gy_type mgy_eq2 by auto

    have mhy1mhy2_rel_ex: "\<exists>v. v \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c v = \<langle>mhy1,mhy2\<rangle>" using hy_type mhy_eq by auto
    have mhy2mgy2_rel_ex: "\<exists>w. w \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c w = \<langle>mhy2,mgy2\<rangle>" using gy_type mgy_eq2 by auto

    obtain y where y_type: "y \<in>\<^sub>c Y" and y_eq: "m \<circ>\<^sub>c y = \<langle>mhy1,mgy2\<rangle>"
      using transitive_def2[OF trans_Y mhy1_type mhy2_type mgy2_type mhy1mhy2_rel_ex mhy2mgy2_rel_ex] by auto

    have gzy_type: "\<langle>gz,y\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c Y" using gz_type y_type cfunc_prod_type by auto
    have wstep1: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>gz,y\<rangle>
        = distribute_left(Z, X, X) \<circ>\<^sub>c ((id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz,y\<rangle>)"
      using comp_associative2[OF gzy_type idm_type dl_type] by simp
    have idZ_gz2: "id(Z) \<circ>\<^sub>c gz = gz" using id_left_unit2[OF gz_type] by simp
    have wstep2: "(id(Z) \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz,y\<rangle> = \<langle>id(Z) \<circ>\<^sub>c gz, m \<circ>\<^sub>c y\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF gz_type y_type idZ_type m_type] by simp
    have wstep3: "\<langle>id(Z) \<circ>\<^sub>c gz, m \<circ>\<^sub>c y\<rangle> = \<langle>gz, \<langle>mhy1,mgy2\<rangle>\<rangle>" using y_eq idZ_gz2 by simp
    have wstep4: "distribute_left(Z, X, X) \<circ>\<^sub>c \<langle>gz, \<langle>mhy1,mgy2\<rangle>\<rangle> = \<langle>\<langle>gz,mhy1\<rangle>,\<langle>gz,mgy2\<rangle>\<rangle>"
      using distribute_left_ap[OF gz_type mhy1_type mgy2_type] by simp
    have wmain_eq: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>gz,y\<rangle> = \<langle>\<langle>gz,mhy1\<rangle>,\<langle>gz,mgy2\<rangle>\<rangle>"
      using wstep1 wstep2 wstep3 wstep4 by simp

    have s_eq_final: "s = \<langle>gz,mhy1\<rangle>" using s_eq hz_eq_gz by simp
    have u_eq_final: "u = \<langle>gz,mgy2\<rangle>" using u_eq by simp

    have w_eq_su: "(distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>gz,y\<rangle> = \<langle>s,u\<rangle>"
      using wmain_eq s_eq_final u_eq_final by simp

    have su_type: "\<langle>s,u\<rangle> \<in>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)" using s_type u_type cfunc_prod_type by auto
    have su_factorsthru: "\<langle>s,u\<rangle> factorsthru (distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      using factors_through_def2[OF su_type comp_type_res] gzy_type w_eq_su by auto
    show "relative_member(\<langle>s,u\<rangle>, (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X), Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
      unfolding relative_member_def using su_type comp_mono comp_type_res su_factorsthru by auto
  qed
  show ?thesis unfolding transitive_on_def using sub main by auto
qed

lemma left_pair_equiv_rel:
  assumes "equiv_rel_on(X, Y, m)"
  shows "equiv_rel_on(X \<times>\<^sub>c Z, Y \<times>\<^sub>c Z, distribute_right(X, X, Z) \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)))"
  using assms unfolding equiv_rel_on_def
  using left_pair_reflexive left_pair_symmetric left_pair_transitive by auto

lemma right_pair_equiv_rel:
  assumes "equiv_rel_on(X, Y, m)"
  shows "equiv_rel_on(Z \<times>\<^sub>c X, Z \<times>\<^sub>c Y, distribute_left(Z, X, X) \<circ>\<^sub>c (id(Z) \<times>\<^sub>f m))"
  using assms unfolding equiv_rel_on_def
  using right_pair_reflexive right_pair_symmetric right_pair_transitive by auto

end
