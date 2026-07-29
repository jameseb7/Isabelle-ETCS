section \<open>Empty Set and Initial Objects\<close>

theory Initial
  imports Coproduct
begin

text \<open>The axiomatization below corresponds to Axiom 8 (Empty Set) in Halvorson.\<close>
axiomatization
  initial_func :: "cset \<Rightarrow> cfunc" ("\<alpha>\<^bsub>_\<^esub>" 100) and
  emptyset :: "cset" ("\<emptyset>")
where
  initial_func_type[type_rule]: "initial_func(X) : \<emptyset> \<rightarrow> X" and
  initial_func_unique: "h : \<emptyset> \<rightarrow> X \<Longrightarrow> h = initial_func(X)" and
  emptyset_is_empty: "\<not>(x \<in>\<^sub>c \<emptyset>)"

definition initial_object :: "cset \<Rightarrow> o" where
  "initial_object(X) \<longleftrightarrow> (\<forall>Y. \<exists>!f. f : X \<rightarrow> Y)"

lemma emptyset_is_initial:
  "initial_object(\<emptyset>)"
  unfolding initial_object_def
proof (intro allI)
  fix Y
  show "\<exists>!f. f : \<emptyset> \<rightarrow> Y"
  proof (rule ex1I[where a="initial_func(Y)"])
    show "initial_func(Y) : \<emptyset> \<rightarrow> Y" by (rule initial_func_type)
  next
    fix f
    assume f_type: "f : \<emptyset> \<rightarrow> Y"
    show "f = initial_func(Y)" by (rule initial_func_unique[OF f_type])
  qed
qed

lemma initial_iso_empty:
  assumes X_initial: "initial_object(X)"
  shows "X \<cong> \<emptyset>"
proof -
  have all_unique: "\<forall>Y. \<exists>!f. f : X \<rightarrow> Y"
    by (rule iffD1[OF initial_object_def X_initial])
  have unique_to_empty: "\<exists>!f. f : X \<rightarrow> \<emptyset>"
    by (rule spec[OF all_unique])
  have exists_to_empty: "\<exists>f. f : X \<rightarrow> \<emptyset>"
  proof (rule ex1E[OF unique_to_empty])
    fix f
    assume f_type: "f : X \<rightarrow> \<emptyset>"
    assume "\<forall>g. g : X \<rightarrow> \<emptyset> \<longrightarrow> g = f"
    show "\<exists>f. f : X \<rightarrow> \<emptyset>" by (rule exI[where x=f], rule f_type)
  qed
  obtain f where f_type: "f : X \<rightarrow> \<emptyset>"
    by (rule exE[OF exists_to_empty])
  have X_empty: "\<not>(\<exists>x. x \<in>\<^sub>c X)"
  proof (rule notI)
    assume exists_x: "\<exists>x. x \<in>\<^sub>c X"
    obtain x where x_type: "x \<in>\<^sub>c X" by (rule exE[OF exists_x])
    have "f \<circ>\<^sub>c x \<in>\<^sub>c \<emptyset>" using x_type f_type comp_type by blast
    then show False by (rule notE[OF emptyset_is_empty])
  qed
  have f_inj: "injective(f)"
  proof (rule iffD2[OF injective_def2[OF f_type]])
    show "\<forall>x y. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y \<longrightarrow> x = y"
    proof (intro allI impI)
      fix x y
      assume facts: "x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
      have exists_x: "\<exists>x. x \<in>\<^sub>c X"
        by (rule exI[where x=x], rule conjunct1[OF facts])
      have False by (rule notE[OF X_empty exists_x])
      then show "x = y" by (rule FalseE)
    qed
  qed
  have f_surj: "surjective(f)"
  proof (rule iffD2[OF surjective_def2[OF f_type]])
    show "\<forall>y. y \<in>\<^sub>c \<emptyset> \<longrightarrow> (\<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = y)"
    proof (intro allI impI)
      fix y
      assume y_type: "y \<in>\<^sub>c \<emptyset>"
      have False by (rule notE[OF emptyset_is_empty y_type])
      then show "\<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = y" by (rule FalseE)
    qed
  qed
  have f_mono: "monomorphism(f)" by (rule injective_imp_monomorphism[OF f_inj])
  have f_epi: "epimorphism(f)" by (rule surjective_is_epimorphism[OF f_surj])
  have f_iso: "isomorphism(f)" by (rule epi_mon_is_iso[OF f_epi f_mono])
  show ?thesis
    unfolding is_isomorphic_def
    by (rule exI[where x=f], intro conjI, rule f_type, rule f_iso)
qed

text \<open>The lemma below corresponds to Exercise 2.4.6 in Halvorson.\<close>
lemma coproduct_with_empty:
  "X \<Coprod> \<emptyset> \<cong> X"
proof -
  define p where p_def: "p = id(X) \<amalg> initial_func(X)"
  define i where i_def: "i = left_coproj(X, \<emptyset>)"

  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have alpha_type: "initial_func(X) : \<emptyset> \<rightarrow> X" by (rule initial_func_type)
  have p_type: "p : X \<Coprod> \<emptyset> \<rightarrow> X"
    unfolding p_def by (rule cfunc_coprod_type[OF idX_type alpha_type])
  have i_type: "i : X \<rightarrow> X \<Coprod> \<emptyset>"
    unfolding i_def by (rule left_proj_type)
  have pi_eq: "p \<circ>\<^sub>c i = id(X)"
    unfolding p_def i_def by (rule left_coproj_cfunc_coprod[OF idX_type alpha_type])

  have ip_type: "i \<circ>\<^sub>c p : X \<Coprod> \<emptyset> \<rightarrow> X \<Coprod> \<emptyset>"
    using p_type i_type comp_type by blast
  have ip_left: "(i \<circ>\<^sub>c p) \<circ>\<^sub>c left_coproj(X, \<emptyset>) = left_coproj(X, \<emptyset>)"
  proof -
    have s1: "(i \<circ>\<^sub>c p) \<circ>\<^sub>c left_coproj(X, \<emptyset>) =
        i \<circ>\<^sub>c (p \<circ>\<^sub>c left_coproj(X, \<emptyset>))"
      using comp_associative2[OF left_proj_type p_type i_type] by simp
    have p_left: "p \<circ>\<^sub>c left_coproj(X, \<emptyset>) = id(X)"
      unfolding p_def by (rule left_coproj_cfunc_coprod[OF idX_type alpha_type])
    have s2: "i \<circ>\<^sub>c id(X) = i" using id_right_unit2[OF i_type] by simp
    have s3: "(i \<circ>\<^sub>c p) \<circ>\<^sub>c left_coproj(X, \<emptyset>) = i"
      using s1 p_left s2 by simp
    show ?thesis by (rule trans[OF s3 i_def])
  qed
  have ip_right: "(i \<circ>\<^sub>c p) \<circ>\<^sub>c right_coproj(X, \<emptyset>) = right_coproj(X, \<emptyset>)"
  proof -
    have s1: "(i \<circ>\<^sub>c p) \<circ>\<^sub>c right_coproj(X, \<emptyset>) =
        i \<circ>\<^sub>c (p \<circ>\<^sub>c right_coproj(X, \<emptyset>))"
      using comp_associative2[OF right_proj_type p_type i_type] by simp
    have p_right: "p \<circ>\<^sub>c right_coproj(X, \<emptyset>) = initial_func(X)"
      unfolding p_def by (rule right_coproj_cfunc_coprod[OF idX_type alpha_type])
    have ia_type: "i \<circ>\<^sub>c initial_func(X) : \<emptyset> \<rightarrow> X \<Coprod> \<emptyset>"
      using alpha_type i_type comp_type by blast
    have ia_eq: "i \<circ>\<^sub>c initial_func(X) = initial_func(X \<Coprod> \<emptyset>)"
      by (rule initial_func_unique[OF ia_type])
    have right_eq: "right_coproj(X, \<emptyset>) = initial_func(X \<Coprod> \<emptyset>)"
      by (rule initial_func_unique[OF right_proj_type])
    show ?thesis using s1 p_right ia_eq right_eq by simp
  qed

  have ip_eq_coprod: "i \<circ>\<^sub>c p =
      left_coproj(X, \<emptyset>) \<amalg> right_coproj(X, \<emptyset>)"
    using cfunc_coprod_unique[OF left_proj_type right_proj_type ip_type ip_left ip_right] by simp
  have id_eq_coprod: "id(X \<Coprod> \<emptyset>) =
      left_coproj(X, \<emptyset>) \<amalg> right_coproj(X, \<emptyset>)"
  proof -
    have id_type': "id(X \<Coprod> \<emptyset>) : X \<Coprod> \<emptyset> \<rightarrow> X \<Coprod> \<emptyset>"
      by (rule id_type)
    have id_left: "id(X \<Coprod> \<emptyset>) \<circ>\<^sub>c left_coproj(X, \<emptyset>) =
        left_coproj(X, \<emptyset>)" by (rule id_left_unit2[OF left_proj_type])
    have id_right: "id(X \<Coprod> \<emptyset>) \<circ>\<^sub>c right_coproj(X, \<emptyset>) =
        right_coproj(X, \<emptyset>)" by (rule id_left_unit2[OF right_proj_type])
    show ?thesis
      using cfunc_coprod_unique[OF left_proj_type right_proj_type id_type' id_left id_right] by simp
  qed
  have ip_eq: "i \<circ>\<^sub>c p = id(X \<Coprod> \<emptyset>)"
    using ip_eq_coprod id_eq_coprod by simp
  have p_iso: "isomorphism(p)"
    unfolding isomorphism_def3[OF p_type] using i_type ip_eq pi_eq by auto
  show ?thesis unfolding is_isomorphic_def using p_type p_iso by auto
qed

text \<open>The lemma below corresponds to Proposition 2.4.7 in Halvorson.\<close>
lemma function_to_empty_is_iso:
  assumes f_type: "f : X \<rightarrow> \<emptyset>"
  shows "isomorphism(f)"
proof -
  have X_empty: "\<not>(\<exists>x. x \<in>\<^sub>c X)"
  proof
    assume "\<exists>x. x \<in>\<^sub>c X"
    then obtain x where x_type: "x \<in>\<^sub>c X" by auto
    have "f \<circ>\<^sub>c x \<in>\<^sub>c \<emptyset>" using x_type f_type comp_type by blast
    then show False using emptyset_is_empty by auto
  qed
  have f_inj: "injective(f)"
    unfolding injective_def2[OF f_type] using X_empty by auto
  have f_surj: "surjective(f)"
    unfolding surjective_def2[OF f_type] using emptyset_is_empty by auto
  have f_mono: "monomorphism(f)" by (rule injective_imp_monomorphism[OF f_inj])
  have f_epi: "epimorphism(f)" by (rule surjective_is_epimorphism[OF f_surj])
  show ?thesis by (rule epi_mon_is_iso[OF f_epi f_mono])
qed

lemma empty_prod_X:
  "\<emptyset> \<times>\<^sub>c X \<cong> \<emptyset>"
proof -
  have p_type: "left_cart_proj(\<emptyset>, X) : \<emptyset> \<times>\<^sub>c X \<rightarrow> \<emptyset>"
    by (rule left_cart_proj_type)
  have p_iso: "isomorphism(left_cart_proj(\<emptyset>, X))"
    by (rule function_to_empty_is_iso[OF p_type])
  show ?thesis unfolding is_isomorphic_def using p_type p_iso by auto
qed

lemma X_prod_empty:
  "X \<times>\<^sub>c \<emptyset> \<cong> \<emptyset>"
proof -
  have p_type: "right_cart_proj(X, \<emptyset>) : X \<times>\<^sub>c \<emptyset> \<rightarrow> \<emptyset>"
    by (rule right_cart_proj_type)
  have p_iso: "isomorphism(right_cart_proj(X, \<emptyset>))"
    by (rule function_to_empty_is_iso[OF p_type])
  show ?thesis unfolding is_isomorphic_def using p_type p_iso by auto
qed

text \<open>The lemma below corresponds to Proposition 2.4.8 in Halvorson.\<close>
lemma no_el_iff_iso_empty:
  "is_empty(X) \<longleftrightarrow> X \<cong> \<emptyset>"
proof (rule iffI)
  assume X_empty: "is_empty(X)"
  have alpha_type: "initial_func(X) : \<emptyset> \<rightarrow> X" by (rule initial_func_type)
  have alpha_inj: "injective(initial_func(X))"
    unfolding injective_def2[OF alpha_type] using emptyset_is_empty by auto
  have alpha_surj: "surjective(initial_func(X))"
    unfolding surjective_def2[OF alpha_type] using X_empty unfolding is_empty_def by auto
  have alpha_mono: "monomorphism(initial_func(X))"
    by (rule injective_imp_monomorphism[OF alpha_inj])
  have alpha_epi: "epimorphism(initial_func(X))"
    by (rule surjective_is_epimorphism[OF alpha_surj])
  have alpha_iso: "isomorphism(initial_func(X))"
    by (rule epi_mon_is_iso[OF alpha_epi alpha_mono])
  have empty_iso_X: "\<emptyset> \<cong> X"
    unfolding is_isomorphic_def using alpha_type alpha_iso by auto
  show "X \<cong> \<emptyset>" using isomorphic_is_symmetric empty_iso_X by auto
next
  assume X_iso_empty: "X \<cong> \<emptyset>"
  obtain f where f_type: "f : X \<rightarrow> \<emptyset>" and f_iso: "isomorphism(f)"
    using X_iso_empty unfolding is_isomorphic_def by auto
  show "is_empty(X)"
    unfolding is_empty_def
  proof
    assume "\<exists>x. x \<in>\<^sub>c X"
    then obtain x where x_type: "x \<in>\<^sub>c X" by auto
    have "f \<circ>\<^sub>c x \<in>\<^sub>c \<emptyset>" using x_type f_type comp_type by blast
    then show False using emptyset_is_empty by auto
  qed
qed

lemma initial_maps_mono:
  assumes X_initial: "initial_object(X)"
  assumes f_type: "f : X \<rightarrow> Y"
  shows "monomorphism(f)"
proof -
  have X_iso_empty: "X \<cong> \<emptyset>" by (rule initial_iso_empty[OF X_initial])
  have X_empty: "is_empty(X)" using no_el_iff_iso_empty X_iso_empty by auto
  have f_inj: "injective(f)"
    unfolding injective_def2[OF f_type] using X_empty unfolding is_empty_def by auto
  show ?thesis by (rule injective_imp_monomorphism[OF f_inj])
qed

lemma iso_empty_initial:
  assumes X_iso_empty: "X \<cong> \<emptyset>"
  shows "initial_object(X)"
proof -
  obtain f where f_type: "f : X \<rightarrow> \<emptyset>" and f_iso: "isomorphism(f)"
    using X_iso_empty unfolding is_isomorphic_def by auto
  have X_empty: "is_empty(X)" using no_el_iff_iso_empty X_iso_empty by auto
  show ?thesis
    unfolding initial_object_def
  proof (intro allI)
    fix Y
    have candidate_type: "initial_func(Y) \<circ>\<^sub>c f : X \<rightarrow> Y"
      using f_type initial_func_type comp_type by blast
    show "\<exists>!h. h : X \<rightarrow> Y"
    proof (rule ex1I[where a="initial_func(Y) \<circ>\<^sub>c f"])
      show "initial_func(Y) \<circ>\<^sub>c f : X \<rightarrow> Y" by (rule candidate_type)
    next
      fix h
      assume h_type: "h : X \<rightarrow> Y"
      show "h = initial_func(Y) \<circ>\<^sub>c f"
      proof (rule one_separator[OF h_type candidate_type])
        fix x
        assume x_type: "x \<in>\<^sub>c X"
        have exists_x: "\<exists>x. x \<in>\<^sub>c X" by (rule exI[where x=x], rule x_type)
        have no_x: "\<not>(\<exists>x. x \<in>\<^sub>c X)"
          by (rule iffD1[OF is_empty_def X_empty])
        have False by (rule notE[OF no_x exists_x])
        then show "h \<circ>\<^sub>c x = (initial_func(Y) \<circ>\<^sub>c f) \<circ>\<^sub>c x" by (rule FalseE)
      qed
    qed
  qed
qed

lemma function_to_empty_set_is_iso:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes Y_empty: "is_empty(Y)"
  shows "isomorphism(f)"
proof -
  have Y_no_elements: "\<not>(\<exists>y. y \<in>\<^sub>c Y)"
    by (rule iffD1[OF is_empty_def Y_empty])
  have X_empty: "is_empty(X)"
  proof (rule iffD2[OF is_empty_def], rule notI)
    assume exists_x: "\<exists>x. x \<in>\<^sub>c X"
    obtain x where x_type: "x \<in>\<^sub>c X" by (rule exE[OF exists_x])
    have "f \<circ>\<^sub>c x \<in>\<^sub>c Y" using x_type f_type comp_type by blast
    then have exists_y: "\<exists>y. y \<in>\<^sub>c Y" by (rule exI)
    show False by (rule notE[OF Y_no_elements exists_y])
  qed
  have X_no_elements: "\<not>(\<exists>x. x \<in>\<^sub>c X)"
    by (rule iffD1[OF is_empty_def X_empty])
  have f_inj: "injective(f)"
  proof (rule iffD2[OF injective_def2[OF f_type]])
    show "\<forall>x y. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y \<longrightarrow> x = y"
    proof (intro allI impI)
      fix x y
      assume facts: "x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
      have exists_x: "\<exists>x. x \<in>\<^sub>c X"
        by (rule exI[where x=x], rule conjunct1[OF facts])
      have False by (rule notE[OF X_no_elements exists_x])
      then show "x = y" by (rule FalseE)
    qed
  qed
  have f_surj: "surjective(f)"
  proof (rule iffD2[OF surjective_def2[OF f_type]])
    show "\<forall>y. y \<in>\<^sub>c Y \<longrightarrow> (\<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = y)"
    proof (intro allI impI)
      fix y
      assume y_type: "y \<in>\<^sub>c Y"
      have exists_y: "\<exists>y. y \<in>\<^sub>c Y" by (rule exI[where x=y], rule y_type)
      have False by (rule notE[OF Y_no_elements exists_y])
      then show "\<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = y" by (rule FalseE)
    qed
  qed
  have f_mono: "monomorphism(f)" by (rule injective_imp_monomorphism[OF f_inj])
  have f_epi: "epimorphism(f)" by (rule surjective_is_epimorphism[OF f_surj])
  show ?thesis by (rule epi_mon_is_iso[OF f_epi f_mono])
qed

lemma prod_iso_to_empty_right:
  assumes X_nonempty: "nonempty(X)"
  assumes prod_iso_empty: "X \<times>\<^sub>c Y \<cong> \<emptyset>"
  shows "is_empty(Y)"
proof -
  have iso_witness: "\<exists>f. f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset> \<and> isomorphism(f)"
    by (rule iffD1[OF is_isomorphic_def prod_iso_empty])
  have morphism_exists: "\<exists>f. f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset>"
  proof (rule exE[OF iso_witness])
    fix f
    assume facts: "f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset> \<and> isomorphism(f)"
    show ?thesis by (rule exI[where x=f], rule conjunct1[OF facts])
  qed
  obtain f where f_type: "f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset>"
    by (rule exE[OF morphism_exists])
  have exists_x: "\<exists>x. x \<in>\<^sub>c X" by (rule iffD1[OF nonempty_def X_nonempty])
  obtain x where x_type: "x \<in>\<^sub>c X" by (rule exE[OF exists_x])
  show ?thesis
  proof (rule iffD2[OF is_empty_def], rule notI)
    assume exists_y: "\<exists>y. y \<in>\<^sub>c Y"
    obtain y where y_type: "y \<in>\<^sub>c Y" by (rule exE[OF exists_y])
    have pair_type: "\<langle>x, y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y"
      by (rule cfunc_prod_type[OF x_type y_type])
    have "f \<circ>\<^sub>c \<langle>x, y\<rangle> \<in>\<^sub>c \<emptyset>" using pair_type f_type comp_type by blast
    then show False by (rule notE[OF emptyset_is_empty])
  qed
qed

lemma prod_iso_to_empty_left:
  assumes Y_nonempty: "nonempty(Y)"
  assumes prod_iso_empty: "X \<times>\<^sub>c Y \<cong> \<emptyset>"
  shows "is_empty(X)"
proof -
  have iso_witness: "\<exists>f. f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset> \<and> isomorphism(f)"
    by (rule iffD1[OF is_isomorphic_def prod_iso_empty])
  have morphism_exists: "\<exists>f. f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset>"
  proof (rule exE[OF iso_witness])
    fix f
    assume facts: "f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset> \<and> isomorphism(f)"
    show ?thesis by (rule exI[where x=f], rule conjunct1[OF facts])
  qed
  obtain f where f_type: "f : X \<times>\<^sub>c Y \<rightarrow> \<emptyset>"
    by (rule exE[OF morphism_exists])
  have exists_y: "\<exists>y. y \<in>\<^sub>c Y" by (rule iffD1[OF nonempty_def Y_nonempty])
  obtain y where y_type: "y \<in>\<^sub>c Y" by (rule exE[OF exists_y])
  show ?thesis
  proof (rule iffD2[OF is_empty_def], rule notI)
    assume exists_x: "\<exists>x. x \<in>\<^sub>c X"
    obtain x where x_type: "x \<in>\<^sub>c X" by (rule exE[OF exists_x])
    have pair_type: "\<langle>x, y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y"
      by (rule cfunc_prod_type[OF x_type y_type])
    have "f \<circ>\<^sub>c \<langle>x, y\<rangle> \<in>\<^sub>c \<emptyset>" using pair_type f_type comp_type by blast
    then show False by (rule notE[OF emptyset_is_empty])
  qed
qed

lemma empty_subset:
  "subobject_of(\<emptyset>, initial_func(X), X)"
proof -
  have alpha_type: "initial_func(X) : \<emptyset> \<rightarrow> X" by (rule initial_func_type)
  have alpha_inj: "injective(initial_func(X))"
  proof (rule iffD2[OF injective_def2[OF alpha_type]])
    show "\<forall>x y. x \<in>\<^sub>c \<emptyset> \<and> y \<in>\<^sub>c \<emptyset> \<and>
        initial_func(X) \<circ>\<^sub>c x = initial_func(X) \<circ>\<^sub>c y \<longrightarrow> x = y"
    proof (intro allI impI)
      fix x y
      assume facts: "x \<in>\<^sub>c \<emptyset> \<and> y \<in>\<^sub>c \<emptyset> \<and>
          initial_func(X) \<circ>\<^sub>c x = initial_func(X) \<circ>\<^sub>c y"
      have x_type: "x \<in>\<^sub>c \<emptyset>" by (rule conjunct1[OF facts])
      have False by (rule notE[OF emptyset_is_empty x_type])
      then show "x = y" by (rule FalseE)
    qed
  qed
  have alpha_mono: "monomorphism(initial_func(X))"
    by (rule injective_imp_monomorphism[OF alpha_inj])
  show ?thesis unfolding subobject_of_def using alpha_type alpha_mono by auto
qed

text \<open>HOL's unnamed Proposition 2.2.1 states that the quotient of the subobjects of \<one> by
isomorphism has cardinality two. Plain FOL has no HOL set-comprehension, quotient-set, or cardinality
library with which to state that formula. As the theorem is unnamed and no downstream theory can
reference it, it is omitted here, consistently with the analogous unnamed cardinality facts in
Truth and Coproduct.\<close>

lemma coprod_with_init_obj1:
  assumes Y_initial: "initial_object(Y)"
  shows "X \<Coprod> Y \<cong> X"
proof -
  have Y_iso_empty: "Y \<cong> \<emptyset>" by (rule initial_iso_empty[OF Y_initial])
  have X_iso_X: "X \<cong> X" by (rule isomorphic_is_reflexive)
  have coprod_iso: "X \<Coprod> Y \<cong> X \<Coprod> \<emptyset>"
    by (rule coprod_pres_iso[OF X_iso_X Y_iso_empty])
  have target_iso: "X \<Coprod> \<emptyset> \<cong> X" by (rule coproduct_with_empty)
  show ?thesis
    by (rule mp[OF isomorphic_is_transitive], intro conjI, rule coprod_iso, rule target_iso)
qed

lemma coprod_with_init_obj2:
  assumes X_initial: "initial_object(X)"
  shows "X \<Coprod> Y \<cong> Y"
proof -
  have swap_iso: "X \<Coprod> Y \<cong> Y \<Coprod> X" by (rule coproduct_commutes)
  have remove_X: "Y \<Coprod> X \<cong> Y" by (rule coprod_with_init_obj1[OF X_initial])
  show ?thesis
    by (rule mp[OF isomorphic_is_transitive], intro conjI, rule swap_iso, rule remove_X)
qed

lemma prod_with_term_obj1:
  assumes X_terminal: "terminal_object(X)"
  shows "X \<times>\<^sub>c Y \<cong> Y"
proof -
  have X_iso_one: "X \<cong> \<one>"
    by (rule terminal_objects_isomorphic[OF X_terminal one_terminal_object])
  have Y_iso_Y: "Y \<cong> Y" by (rule isomorphic_is_reflexive)
  have prod_iso: "X \<times>\<^sub>c Y \<cong> \<one> \<times>\<^sub>c Y"
    by (rule prod_pres_iso[OF X_iso_one Y_iso_Y])
  have target_iso: "\<one> \<times>\<^sub>c Y \<cong> Y" by (rule one_x_A_iso_A)
  show ?thesis
    by (rule mp[OF isomorphic_is_transitive], intro conjI, rule prod_iso, rule target_iso)
qed

lemma prod_with_term_obj2:
  assumes Y_terminal: "terminal_object(Y)"
  shows "X \<times>\<^sub>c Y \<cong> X"
proof -
  have swap_iso: "X \<times>\<^sub>c Y \<cong> Y \<times>\<^sub>c X" by (rule product_commutes)
  have remove_Y: "Y \<times>\<^sub>c X \<cong> X" by (rule prod_with_term_obj1[OF Y_terminal])
  show ?thesis
    by (rule mp[OF isomorphic_is_transitive], intro conjI, rule swap_iso, rule remove_Y)
qed

end
