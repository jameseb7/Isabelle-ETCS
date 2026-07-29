section \<open>Axiom of Choice\<close>

theory Axiom_Of_Choice
  imports Coproduct
begin

text \<open>The two definitions below correspond to Definition 2.7.1 in Halvorson.\<close>
definition section_of :: "cfunc \<Rightarrow> cfunc \<Rightarrow> o" (infix "sectionof" 90)
  where "s sectionof f \<longleftrightarrow> (s : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c s = id(codomain(f)))"

definition split_epimorphism :: "cfunc \<Rightarrow> o"
  where "split_epimorphism(f) \<longleftrightarrow> (\<exists>s. s : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c s = id(codomain(f)))"

lemma split_epimorphism_def2:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_split_epic: "split_epimorphism(f)"
  shows "\<exists>s. (f \<circ>\<^sub>c s = id(Y)) \<and> s : Y \<rightarrow> X"
proof -
  have dom_f: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
  have cod_f: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  show ?thesis using f_split_epic unfolding split_epimorphism_def using dom_f cod_f by auto
qed

lemma sections_define_splits:
  assumes s_sect: "s sectionof f"
  assumes s_type: "s : Y \<rightarrow> X"
  shows "f : X \<rightarrow> Y \<and> split_epimorphism(f)"
proof -
  have s_type2: "s : codomain(f) \<rightarrow> domain(f)" using s_sect unfolding section_of_def by auto
  have fs_eq: "f \<circ>\<^sub>c s = id(codomain(f))" using s_sect unfolding section_of_def by auto
  have cod_f_eq_Y: "codomain(f) = Y" using s_type s_type2 unfolding cfunc_type_def by auto
  have dom_f_eq_X: "domain(f) = X" using s_type s_type2 unfolding cfunc_type_def by auto
  have f_type: "f : X \<rightarrow> Y" unfolding cfunc_type_def using dom_f_eq_X cod_f_eq_Y by auto
  have split_ep: "split_epimorphism(f)" unfolding split_epimorphism_def using s_type2 fs_eq by auto
  show ?thesis using f_type split_ep by simp
qed

text \<open>The axiomatization below corresponds to Axiom 11 (Axiom of Choice) in Halvorson.\<close>
axiomatization
  where
  axiom_of_choice: "epimorphism(f) \<longrightarrow> (\<exists>g. g sectionof f)"

lemma epis_give_monos:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_epi: "epimorphism(f)"
  shows "\<exists>g. g : Y \<rightarrow> X \<and> monomorphism(g) \<and> f \<circ>\<^sub>c g = id(Y)"
proof -
  obtain g where g_sect: "g sectionof f" using axiom_of_choice f_epi by auto
  have dom_f: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
  have cod_f: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  have g_type2: "g : codomain(f) \<rightarrow> domain(f)" using g_sect unfolding section_of_def by auto
  have fg_eq: "f \<circ>\<^sub>c g = id(codomain(f))" using g_sect unfolding section_of_def by auto
  have g_type: "g : Y \<rightarrow> X" using g_type2 dom_f cod_f by simp
  have fg_eq2: "f \<circ>\<^sub>c g = id(Y)" using fg_eq cod_f by simp
  have idY_mono: "monomorphism(id(Y))" using iso_imp_epi_and_monic[OF id_isomorphism] by (rule conjunct2)
  have comp_mono: "monomorphism(f \<circ>\<^sub>c g)" using fg_eq2 idY_mono by simp
  have g_mono: "monomorphism(g)" using comp_monic_imp_monic'[OF g_type f_type comp_mono] by simp
  show ?thesis using g_type g_mono fg_eq2 by auto
qed

corollary epis_are_split:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_epi: "epimorphism(f)"
  shows "split_epimorphism(f)"
proof -
  obtain g where g_type: "g : Y \<rightarrow> X" and g_mono: "monomorphism(g)" and fg_eq: "f \<circ>\<^sub>c g = id(Y)"
    using epis_give_monos[OF f_type f_epi] by auto
  have cod_f: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  have dom_f: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
  have g_type2: "g : codomain(f) \<rightarrow> domain(f)" using g_type cod_f dom_f by simp
  have fg_eq2: "f \<circ>\<^sub>c g = id(codomain(f))" using fg_eq cod_f by simp
  show ?thesis unfolding split_epimorphism_def using g_type2 fg_eq2 by auto
qed

text \<open>The lemma below corresponds to Proposition 2.6.8 in Halvorson.\<close>
lemma monos_give_epis:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_mono: "monomorphism(f)"
  assumes X_nonempty: "nonempty(X)"
  shows "\<exists>g. g : Y \<rightarrow> X \<and> epimorphism(g) \<and> g \<circ>\<^sub>c f = id(X)"
proof -
  obtain g m E where g_type: "g : X \<rightarrow> E" and m_type: "m : E \<rightarrow> Y" and
      g_epi: "epimorphism(g)" and m_mono: "monomorphism(m)" and f_eq: "f = m \<circ>\<^sub>c g"
    using epi_monic_factorization2[OF f_type] by auto

  have g_mono: "monomorphism(g)"
    unfolding monomorphism_def3[OF g_type]
  proof (intro allI impI)
    fix x y A
    assume "x : A \<rightarrow> X \<and> y : A \<rightarrow> X"
    then have x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> X" by auto
    assume gxy_eq: "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    have s1: "(m \<circ>\<^sub>c g) \<circ>\<^sub>c x = (m \<circ>\<^sub>c g) \<circ>\<^sub>c y"
    proof -
      have l: "(m \<circ>\<^sub>c g) \<circ>\<^sub>c x = m \<circ>\<^sub>c (g \<circ>\<^sub>c x)" using comp_associative2[OF x_type g_type m_type] by simp
      have r: "(m \<circ>\<^sub>c g) \<circ>\<^sub>c y = m \<circ>\<^sub>c (g \<circ>\<^sub>c y)" using comp_associative2[OF y_type g_type m_type] by simp
      show ?thesis using l r gxy_eq by simp
    qed
    have fx_eq_fy: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y" using s1 f_eq by simp
    show "x = y"
      using monomorphism_def3[OF f_type, THEN iffD1, rule_format, where g=x and h=y and A=A]
        f_mono x_type y_type fx_eq_fy by auto
  qed

  have g_iso: "isomorphism(g)" using epi_mon_is_iso[OF g_epi g_mono] by simp
  have g_spec: "g\<^bold>\<inverse> : codomain(g) \<rightarrow> domain(g) \<and> g\<^bold>\<inverse> \<circ>\<^sub>c g = id(domain(g)) \<and> g \<circ>\<^sub>c g\<^bold>\<inverse> = id(codomain(g))"
    using inverse_def2[OF g_iso] by simp
  have dom_g: "domain(g) = X" using g_type unfolding cfunc_type_def by auto
  have cod_g: "codomain(g) = E" using g_type unfolding cfunc_type_def by auto
  have ginv_type: "g\<^bold>\<inverse> : E \<rightarrow> X" using g_spec dom_g cod_g by simp
  have ginv_g: "g\<^bold>\<inverse> \<circ>\<^sub>c g = id(X)" using g_spec dom_g by simp

  obtain x where x_type: "x \<in>\<^sub>c X" using X_nonempty unfolding nonempty_def by auto

  have xb_type: "x \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub> : set_subtraction(m) \<rightarrow> X"
    using terminal_func_type[of "set_subtraction(m)"] x_type comp_type by blast
  have ginv_xb_type: "g\<^bold>\<inverse> \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>) : E \<Coprod> set_subtraction(m) \<rightarrow> X"
    using cfunc_coprod_type[OF ginv_type xb_type] by simp
  have tc_type: "try_cast(m) : Y \<rightarrow> E \<Coprod> set_subtraction(m)" using try_cast_type[OF m_mono m_type] by simp

  define h where h_def: "h = (g\<^bold>\<inverse> \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>)) \<circ>\<^sub>c try_cast(m)"
  have h_type: "h : Y \<rightarrow> X" unfolding h_def using comp_type[OF tc_type ginv_xb_type] by simp

  have func_f_elem_eq: "\<And>yy. yy \<in>\<^sub>c X \<Longrightarrow> h \<circ>\<^sub>c (f \<circ>\<^sub>c yy) = yy"
  proof -
    fix yy assume yy_type: "yy \<in>\<^sub>c X"
    have gyy_type: "g \<circ>\<^sub>c yy \<in>\<^sub>c E" using yy_type g_type comp_type by blast
    have s0: "(m \<circ>\<^sub>c g) \<circ>\<^sub>c yy = m \<circ>\<^sub>c (g \<circ>\<^sub>c yy)" using comp_associative2[OF yy_type g_type m_type] by simp
    have s1: "h \<circ>\<^sub>c (f \<circ>\<^sub>c yy) = h \<circ>\<^sub>c (m \<circ>\<^sub>c (g \<circ>\<^sub>c yy))" using f_eq s0 by simp
    have s2: "h \<circ>\<^sub>c (m \<circ>\<^sub>c (g \<circ>\<^sub>c yy)) = (h \<circ>\<^sub>c m) \<circ>\<^sub>c (g \<circ>\<^sub>c yy)"
      using comp_associative2[OF gyy_type m_type h_type] by simp
    have s3: "h \<circ>\<^sub>c m = (g\<^bold>\<inverse> \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>)) \<circ>\<^sub>c (try_cast(m) \<circ>\<^sub>c m)"
      unfolding h_def using comp_associative2[OF m_type tc_type ginv_xb_type] by simp
    have s4: "try_cast(m) \<circ>\<^sub>c m = left_coproj(E, set_subtraction(m))" using try_cast_m_m[OF m_mono m_type] by simp
    have s5: "h \<circ>\<^sub>c m = (g\<^bold>\<inverse> \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>)) \<circ>\<^sub>c left_coproj(E, set_subtraction(m))"
      using s3 s4 by simp
    have s6: "(g\<^bold>\<inverse> \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>)) \<circ>\<^sub>c left_coproj(E, set_subtraction(m)) = g\<^bold>\<inverse>"
      using left_coproj_cfunc_coprod[OF ginv_type xb_type] by simp
    have s7: "h \<circ>\<^sub>c m = g\<^bold>\<inverse>" using s5 s6 by simp
    have s8: "(h \<circ>\<^sub>c m) \<circ>\<^sub>c (g \<circ>\<^sub>c yy) = g\<^bold>\<inverse> \<circ>\<^sub>c (g \<circ>\<^sub>c yy)" using s7 by simp
    have s9: "g\<^bold>\<inverse> \<circ>\<^sub>c (g \<circ>\<^sub>c yy) = (g\<^bold>\<inverse> \<circ>\<^sub>c g) \<circ>\<^sub>c yy" using comp_associative2[OF yy_type g_type ginv_type] by simp
    have s10: "(g\<^bold>\<inverse> \<circ>\<^sub>c g) \<circ>\<^sub>c yy = id(X) \<circ>\<^sub>c yy" using ginv_g by simp
    have s11: "id(X) \<circ>\<^sub>c yy = yy" using id_left_unit2[OF yy_type] by simp
    show "h \<circ>\<^sub>c (f \<circ>\<^sub>c yy) = yy" using s1 s2 s8 s9 s10 s11 by simp
  qed

  have hf_type: "h \<circ>\<^sub>c f : X \<rightarrow> X" using f_type h_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have hf_eq: "h \<circ>\<^sub>c f = id(X)"
  proof (rule one_separator[OF hf_type idX_type])
    fix z
    assume z_type: "z : \<one> \<rightarrow> X"
    have s1: "(h \<circ>\<^sub>c f) \<circ>\<^sub>c z = h \<circ>\<^sub>c (f \<circ>\<^sub>c z)" using comp_associative2[OF z_type f_type h_type] by simp
    have s2: "h \<circ>\<^sub>c (f \<circ>\<^sub>c z) = z" using func_f_elem_eq[OF z_type] by simp
    have s3: "id(X) \<circ>\<^sub>c z = z" using id_left_unit2[OF z_type] by simp
    show "(h \<circ>\<^sub>c f) \<circ>\<^sub>c z = id(X) \<circ>\<^sub>c z" using s1 s2 s3 by simp
  qed

  have h_surj: "surjective(h)"
    unfolding surjective_def2[OF h_type]
  proof (intro allI impI)
    fix yy
    assume yy_type: "yy \<in>\<^sub>c X"
    have fyy_type: "f \<circ>\<^sub>c yy \<in>\<^sub>c Y" using yy_type f_type comp_type by blast
    have "h \<circ>\<^sub>c (f \<circ>\<^sub>c yy) = yy" using func_f_elem_eq[OF yy_type] by simp
    then show "\<exists>xa. xa \<in>\<^sub>c Y \<and> h \<circ>\<^sub>c xa = yy" using fyy_type by auto
  qed
  have h_epi: "epimorphism(h)" using surjective_is_epimorphism[OF h_surj] by simp

  show ?thesis using h_type h_epi hf_eq by auto
qed

text \<open>The lemma below corresponds to Exercise 2.7.2(i) in Halvorson.\<close>
lemma split_epis_are_regular:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_split: "split_epimorphism(f)"
  shows "regular_epimorphism(f)"
proof -
  obtain s where s_type: "s : Y \<rightarrow> X" and s_splits: "f \<circ>\<^sub>c s = id(Y)"
    using split_epimorphism_def2[OF f_type f_split] by auto
  have f_epi: "epimorphism(f)"
    unfolding epimorphism_def3[OF f_type]
  proof (intro allI impI)
    fix a b A
    assume "a : Y \<rightarrow> A \<and> b : Y \<rightarrow> A"
    then have a_type: "a : Y \<rightarrow> A" and b_type: "b : Y \<rightarrow> A" by auto
    assume af_eq: "a \<circ>\<^sub>c f = b \<circ>\<^sub>c f"
    have s1: "(a \<circ>\<^sub>c f) \<circ>\<^sub>c s = (b \<circ>\<^sub>c f) \<circ>\<^sub>c s" using af_eq by simp
    have s2: "(a \<circ>\<^sub>c f) \<circ>\<^sub>c s = a \<circ>\<^sub>c (f \<circ>\<^sub>c s)" using comp_associative2[OF s_type f_type a_type] by simp
    have s3: "(b \<circ>\<^sub>c f) \<circ>\<^sub>c s = b \<circ>\<^sub>c (f \<circ>\<^sub>c s)" using comp_associative2[OF s_type f_type b_type] by simp
    have s4: "a \<circ>\<^sub>c (f \<circ>\<^sub>c s) = b \<circ>\<^sub>c (f \<circ>\<^sub>c s)" using s1 s2 s3 by simp
    have s5: "a \<circ>\<^sub>c id(Y) = b \<circ>\<^sub>c id(Y)" using s4 s_splits by simp
    have s6: "a \<circ>\<^sub>c id(Y) = a" using id_right_unit2[OF a_type] by simp
    have s7: "b \<circ>\<^sub>c id(Y) = b" using id_right_unit2[OF b_type] by simp
    show "a = b" using s5 s6 s7 by simp
  qed
  show ?thesis using epimorphisms_are_regular[OF f_type f_epi] by simp
qed

text \<open>The lemma below corresponds to Exercise 2.7.2(ii) in Halvorson.\<close>
lemma sections_are_regular_monos:
  assumes s_type: "s : Y \<rightarrow> X"
  assumes s_sect: "s sectionof f"
  shows "regular_monomorphism(s)"
proof -
  have s_type2: "s : codomain(f) \<rightarrow> domain(f)" using s_sect unfolding section_of_def by auto
  have fs_eq: "f \<circ>\<^sub>c s = id(codomain(f))" using s_sect unfolding section_of_def by auto
  have cod_f_eq_Y: "codomain(f) = Y" using s_type s_type2 unfolding cfunc_type_def by auto
  have dom_f_eq_X: "domain(f) = X" using s_type s_type2 unfolding cfunc_type_def by auto
  have f_type: "f : X \<rightarrow> Y" unfolding cfunc_type_def using dom_f_eq_X cod_f_eq_Y by auto
  have fs_eq2: "f \<circ>\<^sub>c s = id(Y)" using fs_eq cod_f_eq_Y by simp

  have s_mono: "monomorphism(s)"
    unfolding monomorphism_def3[OF s_type]
  proof (intro allI impI)
    fix a b A
    assume "a : A \<rightarrow> Y \<and> b : A \<rightarrow> Y"
    then have a_type: "a : A \<rightarrow> Y" and b_type: "b : A \<rightarrow> Y" by auto
    assume sa_eq: "s \<circ>\<^sub>c a = s \<circ>\<^sub>c b"
    have s1: "f \<circ>\<^sub>c (s \<circ>\<^sub>c a) = f \<circ>\<^sub>c (s \<circ>\<^sub>c b)" using sa_eq by simp
    have s2: "f \<circ>\<^sub>c (s \<circ>\<^sub>c a) = (f \<circ>\<^sub>c s) \<circ>\<^sub>c a" using comp_associative2[OF a_type s_type f_type] by simp
    have s3: "f \<circ>\<^sub>c (s \<circ>\<^sub>c b) = (f \<circ>\<^sub>c s) \<circ>\<^sub>c b" using comp_associative2[OF b_type s_type f_type] by simp
    have s4: "(f \<circ>\<^sub>c s) \<circ>\<^sub>c a = (f \<circ>\<^sub>c s) \<circ>\<^sub>c b" using s1 s2 s3 by simp
    have s5: "id(Y) \<circ>\<^sub>c a = id(Y) \<circ>\<^sub>c b" using s4 fs_eq2 by simp
    have s6: "id(Y) \<circ>\<^sub>c a = a" using id_left_unit2[OF a_type] by simp
    have s7: "id(Y) \<circ>\<^sub>c b = b" using id_left_unit2[OF b_type] by simp
    show "a = b" using s5 s6 s7 by simp
  qed
  show ?thesis using mono_is_regmono[OF s_mono] by simp
qed

end
