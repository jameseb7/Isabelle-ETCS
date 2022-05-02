theory ETCS_Choice
  imports ETCS_Nat
begin

section \<open>Axiom 11: Axiom of Choice\<close>

definition section_of :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" (infix "sectionof" 90)
  where "s sectionof f \<longleftrightarrow> s : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c s = id (codomain(f))"

(*Definition 2.7.1*)
definition split_epimorphism :: "cfunc \<Rightarrow> bool"
  where "split_epimorphism(f)\<longleftrightarrow>(\<exists> s. f \<circ>\<^sub>c s = id (codomain f))"

axiomatization
  where
  axiom_of_choice :"epimorphism(f) \<longrightarrow> (\<exists> g . g sectionof f)"


lemma epis_give_monos:  
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_epi: "epimorphism(f)"
  shows "\<exists>g. g: Y \<rightarrow> X \<and> monomorphism(g) \<and> f \<circ>\<^sub>c g = id Y"
  using assms  
  by (typecheck_cfuncs_prems, metis axiom_of_choice cfunc_type_def comp_monic_imp_monic f_epi id_isomorphism iso_imp_epi_and_monic section_of_def)

(* Proposition 2.6.8 *)
lemma monos_give_epis:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes f_mono: "monomorphism(f)"
  assumes X_nonempty: "nonempty X"
  shows "\<exists>g. g: Y \<rightarrow> X \<and> epimorphism(g) \<and> g \<circ>\<^sub>c f = id X"
proof -
  obtain g m E where g_type[type_rule]: "g : X \<rightarrow> E" and m_type[type_rule]: "m : E \<rightarrow> Y" and
      g_epi: "epimorphism g" and m_mono[type_rule]: "monomorphism m" and f_eq: "f = m \<circ>\<^sub>c g"
    using epi_monic_factorization2 f_type by blast

  have g_mono: "monomorphism g"
  proof (typecheck_cfuncs, unfold monomorphism_def3, auto)
    fix x y A
    assume x_type[type_rule]: "x : A \<rightarrow> X" and y_type[type_rule]: "y : A \<rightarrow> X"

    assume "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    then have "(m \<circ>\<^sub>c g) \<circ>\<^sub>c x = (m \<circ>\<^sub>c g) \<circ>\<^sub>c y"
      by (typecheck_cfuncs, smt comp_associative2)
    then have "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
      unfolding f_eq by auto
    then show "x = y"
      using f_mono f_type monomorphism_def2 x_type y_type by blast
  qed

  have g_iso: "isomorphism g"
    by (simp add: epi_mon_is_iso g_epi g_mono)
  then obtain g_inv where g_inv_type[type_rule]: "g_inv : E \<rightarrow> X" and
      g_g_inv: "g \<circ>\<^sub>c g_inv = id E" and g_inv_g: "g_inv \<circ>\<^sub>c g = id X"
    using cfunc_type_def g_type isomorphism_def by auto

  obtain x where x_type[type_rule]: "x \<in>\<^sub>c X"
    using X_nonempty nonempty_def by blast

  show "\<exists>g. g: Y \<rightarrow> X \<and> epimorphism(g) \<and> g \<circ>\<^sub>c f = id\<^sub>c X"
  proof (rule_tac x="(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>)) \<circ>\<^sub>c try_cast m" in exI, auto)

    show "g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m : Y \<rightarrow> X"
      by typecheck_cfuncs

    have func_f_elem_eq: "\<And> y. y \<in>\<^sub>c X \<Longrightarrow> (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f \<circ>\<^sub>c y = y"
    proof -
      fix y
      assume y_type[type_rule]: "y \<in>\<^sub>c X"

      have "(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f \<circ>\<^sub>c y
          = g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c (try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c g \<circ>\<^sub>c y"
        unfolding f_eq by (typecheck_cfuncs, smt comp_associative2)
      also have "... = (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c left_coproj E (Y \<setminus> (E,m))) \<circ>\<^sub>c g \<circ>\<^sub>c y"
        by (typecheck_cfuncs, smt comp_associative2 m_mono try_cast_m_m)
      also have "... = (g_inv \<circ>\<^sub>c g) \<circ>\<^sub>c y"
        by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
      also have "... = y"
        by (typecheck_cfuncs, simp add: g_inv_g id_left_unit2)
      then show "(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f \<circ>\<^sub>c y = y"
        using calculation by auto
    qed

    show "epimorphism (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m)"
    proof (rule surjective_is_epimorphism, typecheck_cfuncs, unfold surjective_def2, auto)
      fix y
      assume y_type[type_rule]: "y \<in>\<^sub>c X"

      show "\<exists>xa. xa \<in>\<^sub>c Y \<and> (g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c xa = y"
      proof (rule_tac x="f \<circ>\<^sub>c y" in exI, auto)

        show "f \<circ>\<^sub>c y \<in>\<^sub>c Y"
          using f_type by typecheck_cfuncs

        show "(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f \<circ>\<^sub>c y = y"
          by (simp add: func_f_elem_eq y_type)
      qed
    qed

    show "(g_inv \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (E, m)\<^esub>) \<circ>\<^sub>c try_cast m) \<circ>\<^sub>c f = id\<^sub>c X"
      by (insert comp_associative2 func_f_elem_eq id_left_unit2 f_type, typecheck_cfuncs, rule one_separator, auto)
  qed
qed

end