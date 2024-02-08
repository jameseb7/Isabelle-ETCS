theory Countable_Test
  imports ETCS_Axioms ETCS_Add ETCS_Mult ETCS_Pred ETCS_Parity ETCS_Comparison
begin





(* Definition 2.6.9 *)
definition epi_countable :: "cset \<Rightarrow> bool" where
  "epi_countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

lemma emptyset_is_not_epi_countable:
  "\<not> (epi_countable \<emptyset>)"
  using comp_type emptyset_is_empty epi_countable_def zero_type by blast


(* Definition 2.6.9 *)
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f)"

lemma epi_countable_is_countable: 
  assumes "epi_countable X"
  shows "countable X"
  using assms countable_def epi_countable_def epis_give_monos by blast



lemma emptyset_is_countable:
  "countable \<emptyset>"
  using countable_def empty_subset subobject_of_def2 by blast

lemma natural_numbers_are_countably_infinite:
  "(countable \<nat>\<^sub>c) \<and> (is_infinite \<nat>\<^sub>c)"
  by (meson CollectI Peano's_Axioms countable_def injective_imp_monomorphism is_infinite_def successor_type)




lemma smaller_than_countable_is_countable:
  assumes "X \<le>\<^sub>c Y" "countable Y"
  shows "countable X"
  by (smt assms cfunc_type_def comp_type composition_of_monic_pair_is_monic countable_def is_smaller_than_def)


lemma iso_pres_finite:
  assumes "X \<cong> Y"
  assumes "is_finite(X)"
  shows "is_finite(Y)"
  using assms is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic isomorphic_is_symmetric smaller_than_finite_is_finite by blast


lemma iso_pres_countable:
  assumes "X \<cong> Y" "countable Y"
  shows "countable X"
  using assms(1) assms(2) is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic smaller_than_countable_is_countable by blast


lemma not_finite_and_infinite:
  "\<not>(is_finite(X) \<and> is_infinite(X))"
  using epi_is_surj is_finite_def is_infinite_def iso_imp_epi_and_monic by blast




lemma NuN_is_countable:
  "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  using countable_def epis_give_monos halve_with_parity_iso halve_with_parity_type iso_imp_epi_and_monic by smt


(*Exercise 2.6.11*)
lemma coproduct_of_countables_is_countable:
  assumes "countable X" "countable Y"
  shows "countable(X \<Coprod> Y)"
  unfolding countable_def
proof-
  obtain x where x_def:  "x : X  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism x"
    using assms(1) countable_def by blast
  obtain y where y_def:  "y : Y  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism y"
    using assms(2) countable_def by blast
  obtain n where n_def: " n : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> monomorphism n"
    using NuN_is_countable countable_def by blast
  have xy_type: "x \<bowtie>\<^sub>f y : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    using x_def y_def by (typecheck_cfuncs, auto)
  then have nxy_type: "n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y) : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c"
    using comp_type n_def by blast
  have "injective(x \<bowtie>\<^sub>f y)"
    using cfunc_bowtieprod_inj monomorphism_imp_injective x_def y_def by blast
  then have "monomorphism(x \<bowtie>\<^sub>f y)"
    using injective_imp_monomorphism by auto
  then have "monomorphism(n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y))"
    using cfunc_type_def composition_of_monic_pair_is_monic n_def xy_type by auto
  then show "\<exists>f. f : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f"
    using nxy_type by blast
qed
   
  

lemma finite_is_countable: 
  assumes "is_finite X"
  shows "countable X"
  oops

lemma 
  assumes "is_infinite X"
  shows "\<nat>\<^sub>c \<le>\<^sub>c X"
  oops 


lemma N_is_smallest_infinite:
  assumes "is_infinite X"
  assumes "X \<le>\<^sub>c \<nat>\<^sub>c"
  shows "\<nat>\<^sub>c \<cong> X"
  oops

(*We could add a part 2 to the above that says if they are not isomorphic
 then an infinite set is necessarily bigger than N.*)


lemma finite_iff_nosurj_to_N:
  shows "(is_finite(X)) = (\<not>(\<exists>s. (s : X \<rightarrow> \<nat>\<^sub>c) \<and> surjective(s)))"
proof(safe)
  fix s 
  assume X_fin: "is_finite X"
  assume s_type: "s : X \<rightarrow> \<nat>\<^sub>c"
  assume s_surj: "surjective s"
  have "\<exists>g. (g: \<nat>\<^sub>c \<rightarrow> X \<and> monomorphism(g) )"
    using epis_give_monos s_surj s_type surjective_is_epimorphism by blast
  then have "is_finite \<nat>\<^sub>c"
    using X_fin is_smaller_than_def smaller_than_finite_is_finite by blast
  then show False
    using natural_numbers_are_countably_infinite not_finite_and_infinite by blast
next 
next 
  assume "\<nexists>s. s : X \<rightarrow> \<nat>\<^sub>c \<and> surjective s"
  show "is_finite X"
  proof(rule ccontr)
    assume "\<not> is_finite X"
    then have "is_infinite X"
      using either_finite_or_infinite by blast
    then obtain m where m_type[type_rule]: "m : X \<rightarrow> X" and  m_mono: "monomorphism(m)" and 
     m_not_surj:  "\<not>surjective(m)"
      using is_infinite_def by blast
    obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and 
      x_def: "\<And> y.  y \<in>\<^sub>c X \<Longrightarrow>  m \<circ>\<^sub>c y \<noteq> x"
      using m_not_surj m_type surjective_def2 by auto

    obtain i where 
      i_type[type_rule]: "i : \<nat>\<^sub>c \<rightarrow> X" and ibase: "i \<circ>\<^sub>c zero = x" and i_induct: "m \<circ>\<^sub>c i = i \<circ>\<^sub>c successor"
      using m_type natural_number_object_property2 x_type by blast
    have "injective(i)"
      unfolding injective_def
    proof(auto)
      fix p q
      assume "p \<in>\<^sub>c domain i"
      then have [type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
        using cfunc_type_def i_type by auto
      assume "q \<in>\<^sub>c domain i"
      then have [type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
        using cfunc_type_def i_type by auto
      assume eqs: "i \<circ>\<^sub>c p = i \<circ>\<^sub>c q"  

    obtain i where 
      i_type[type_rule]: "i : \<nat>\<^sub>c \<rightarrow> X" and ibase: "i \<circ>\<^sub>c zero = x" and i_induct: "m \<circ>\<^sub>c i = i \<circ>\<^sub>c successor"
      using m_type natural_number_object_property2 x_type by blast

    have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle> eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), 
                                    eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> )\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    proof(rule natural_number_object_func_unique[where X="\<Omega>", where f="id \<Omega>"])
      show "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      proof - 
        have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
        proof (rule same_evals_equal[where Z=one, where X=\<Omega>, where A="\<nat>\<^sub>c"])
          show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs
          show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs 
          show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
                eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
          proof - 
            have "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = 
                  eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
              by (typecheck_cfuncs, metis identity_distributes_across_composition)
            also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
              by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative transpose_func_def)
            also have "... = eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
            proof(rule one_separator[where X = "\<nat>\<^sub>c \<times>\<^sub>c one", where Y=\<Omega>])
              show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
                by typecheck_cfuncs
              show " eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
                by typecheck_cfuncs
              show "\<And>pone. pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
         (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone"
              proof - 
                fix pone
                assume pone_type: "pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
                then obtain p where p_def: "pone = \<langle>p, id one\<rangle>" and p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
                  by (metis cart_prod_decomp id_type one_unique_element)

                have RHS: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone = \<t>"
                proof - 
                  have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone = 
                         eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                    by (typecheck_cfuncs, simp add: comp_associative2 p_def)
                  also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                    by (typecheck_cfuncs, metis calculation flat_cancels_sharp inv_transpose_func_def2 p_def) 
                  also have "... = \<t>"
                    by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 terminal_func_comp terminal_func_unique)
                  then show ?thesis
                    by (simp add: calculation)
                qed
                
                have LHS: "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone = \<t>"
                proof - 
                  have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone = 
                         IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                    using comp_associative2 p_def by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p, zero\<rangle>"
                    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p, zero\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, zero\<rangle> \<rangle>"
                    using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c zero\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle> \<rangle>"
                    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, zero\<rangle> \<rangle>"
                    by (typecheck_cfuncs, simp add: ibase id_left_unit2)
                  also have "... = \<t>"
                  proof(cases "p = zero")
                    assume "p = zero"
                    then show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle> = \<t>"
                      by (typecheck_cfuncs, metis IMPLIES_true_true_is_true  eq_pred_iff_eq ibase)
                  next
                    assume "p \<noteq> zero"
                    then obtain j where j_def: "p = successor \<circ>\<^sub>c j" and j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
                      using \<open>p \<noteq> zero\<close> nonzero_is_succ by (typecheck_cfuncs, blast)
                    have "i \<circ>\<^sub>c p = m \<circ>\<^sub>c i \<circ>\<^sub>c j"
                      using comp_associative2 i_induct j_def successor_type by (typecheck_cfuncs, force)
                    then have "i \<circ>\<^sub>c p \<noteq> x"
                      using \<open>i \<circ>\<^sub>c p = m \<circ>\<^sub>c i \<circ>\<^sub>c j\<close> comp_type j_type x_def by (typecheck_cfuncs, presburger)
                    then have "eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, x\<rangle> = \<f>"
                      using \<open>i \<circ>\<^sub>c p \<noteq> x\<close> eq_pred_iff_eq_conv by (typecheck_cfuncs, blast)
                    then show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle> = \<t>"
                      by (typecheck_cfuncs, metis IMPLIES_false_false_is_true \<open>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle> = \<f>\<close> \<open>p \<noteq> zero\<close> eq_pred_iff_eq_conv)
                  qed
                  then show ?thesis
                    by (simp add: calculation)
                qed
                show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone =
                                  (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone "
                  by (simp add: LHS RHS)
              qed
            qed
            then show ?thesis
              using calculation by presburger
          qed
        qed
        then show ?thesis  
          by (typecheck_cfuncs, metis FORALL_is_pullback \<open>(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>\<close> cfunc_type_def comp_associative is_pullback_def square_commutes_def terminal_func_comp)
      qed
      show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
      show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor =
    id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
      proof (rule one_separator[where X="\<nat>\<^sub>c", where Y=\<Omega>])
        show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          by typecheck_cfuncs
       next
        fix q
        assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"


        have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c q = 
              (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q"
        proof (rule same_evals_equal[where Z="one", where X=\<Omega>, where A="\<nat>\<^sub>c"])
          show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c q \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs
          show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs
          show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i),eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c q =
    eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i),eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q"
          proof - 
            have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i),eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q ) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = 
                  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i),eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle>  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  q ) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>" 
            proof(rule natural_number_object_func_unique[where X = "\<Omega>", where f = "id \<Omega>"])
              show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
                by typecheck_cfuncs
              show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
                by typecheck_cfuncs
              show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
                by typecheck_cfuncs
              show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero =
    (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
              proof - 

                have LHS: "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
                  proof -
                  
                  have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = 
                          (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero" 
                    by (typecheck_cfuncs, smt (z3) comp_associative2) 
                  also have "... = (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>zero ,id one\<rangle>" 
                    by (typecheck_cfuncs, metis cart_prod_extract_left id_left_unit2) 
                  also have "... = (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c   \<langle>zero ,successor \<circ>\<^sub>c q\<rangle>" 
                    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
                  also have "... =  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i),eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c   \<langle>zero ,successor \<circ>\<^sub>c q\<rangle>" 
                    using comp_associative2 by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c   \<langle>zero ,successor \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>zero ,successor \<circ>\<^sub>c q\<rangle>\<rangle>" 
                    using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c zero ,i \<circ>\<^sub>c  successor \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c    \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero ,id\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c successor \<circ>\<^sub>c q\<rangle>\<rangle>" 
                    using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>x ,(i \<circ>\<^sub>c  successor) \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c    \<langle>zero , successor \<circ>\<^sub>c q\<rangle>\<rangle>" 
                    by (typecheck_cfuncs, simp add: comp_associative2 ibase id_left_unit2)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>x ,(m \<circ>\<^sub>c  i) \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c    \<langle>zero , successor \<circ>\<^sub>c q\<rangle>\<rangle>" 
                    using i_induct by presburger
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>\<f>, \<f>\<rangle>"
                    by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_associative comp_type eq_pred_iff_eq_conv x_def zero_is_not_successor)
                  also have "... = \<t>"
                    using IMPLIES_false_false_is_true by blast
                  then show ?thesis
                    by (simp add: calculation)
                qed

                have RHS: "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
                proof - 
                  have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero =
                         IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>  \<circ>\<^sub>c zero"
                    by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>zero, id one\<rangle>"
                    by (typecheck_cfuncs, metis cart_prod_extract_left id_left_unit2)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c   \<langle>zero, q\<rangle>"
                    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c   \<langle>zero, q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>zero, q\<rangle>\<rangle>"
                    using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c zero, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c    \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c q\<rangle>\<rangle>"
                    using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>x, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c    \<langle>zero, q\<rangle>\<rangle>"
                    using ibase id_left_unit2 by (typecheck_cfuncs, presburger)
                  also have "... = \<t>"
                  proof(cases "q = zero")
                    show "q = zero \<Longrightarrow> IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>x,i \<circ>\<^sub>c q\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero,q\<rangle>\<rangle> = \<t>"
                      by (typecheck_cfuncs, metis IMPLIES_true_true_is_true eq_pred_iff_eq ibase)
                    show "q \<noteq> zero \<Longrightarrow> IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>x,i \<circ>\<^sub>c q\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero,q\<rangle>\<rangle> = \<t>"
                      by (typecheck_cfuncs, smt (verit) IMPLIES_false_false_is_true cfunc_type_def comp_associative comp_type eq_pred_iff_eq i_induct m_type nonzero_is_succ successor_type true_false_only_truth_values x_def)
                  qed
                  then show ?thesis
                    by (simp add: calculation)
                qed
                show ?thesis
                  using LHS RHS by presburger
              qed

              show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor =
    id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
              proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<Omega>"])   
                show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
                  by typecheck_cfuncs
                show "id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
                  by typecheck_cfuncs
                show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x"
                proof - 
                  fix p 
                  assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"


                  have LHS: "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p =
                        IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c    \<langle>m \<circ>\<^sub>c i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c p, q\<rangle>\<rangle>"
                  proof - 
                    have "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = 
                          IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c p)"
                      by (typecheck_cfuncs, smt (z3) comp_associative2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p, id one\<rangle> "
                      by (typecheck_cfuncs, metis cart_prod_extract_left id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>c p, q\<rangle> "
                      using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>c p, q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>c p, q\<rangle>\<rangle>"
                      using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c    \<langle>i \<circ>\<^sub>c successor \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c p, q\<rangle>\<rangle>"
                      using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c    \<langle>m \<circ>\<^sub>c i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c p, q\<rangle>\<rangle>"
                      by (typecheck_cfuncs, simp add: comp_associative2 i_induct)
                    then show ?thesis
                      using calculation by auto
                  qed
                  have RHS: "(id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c p =
                              IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, q\<rangle>\<rangle>"
                  proof - 
                    have"(id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c p = 
                              IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>  \<circ>\<^sub>c p"
                      by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f q) \<circ>\<^sub>c \<langle>p,id one\<rangle>"
                      by (typecheck_cfuncs, metis cart_prod_extract_left id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p,q\<rangle>"
                      using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs, auto)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p,q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle>"
                      using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c q\<rangle>\<rangle>"
                      using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, q\<rangle>\<rangle>"
                      using id_left_unit2 by (typecheck_cfuncs, presburger)
                    then show ?thesis
                      using calculation by presburger
                  qed
                    









              show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor =
    id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
              proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<Omega>"])              
                show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
                  by typecheck_cfuncs
                show "id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
                  by typecheck_cfuncs
                show "\<And>p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c p"
                proof - 
                  fix p 
                  assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"

                  have LHS: "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p =
                            IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                  proof - 
                    have "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p =
                            IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c p)"
                      by (typecheck_cfuncs, smt (z3) comp_associative2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c p,id one\<rangle>"
                      by (typecheck_cfuncs, simp add: cart_prod_extract_left id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>"
                      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                      by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)  
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c successor \<circ>\<^sub>c p,i \<circ>\<^sub>c successor \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c p,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                      using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>(i \<circ>\<^sub>c successor) \<circ>\<^sub>c p,(i \<circ>\<^sub>c successor) \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                      by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>(m \<circ>\<^sub>c i) \<circ>\<^sub>c p,(m \<circ>\<^sub>c i) \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                      by (simp add: i_induct)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>m \<circ>\<^sub>c i \<circ>\<^sub>c p,m \<circ>\<^sub>c i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                      by (typecheck_cfuncs, simp add: comp_associative2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                      by (typecheck_cfuncs, smt (verit, best) eq_pred_iff_eq eq_pred_iff_eq_conv m_mono monomorphism_def3)
                    then show ?thesis
                      using calculation by presburger           
                  qed
                  have RHS: "(id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c p =
                            IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, m \<circ>\<^sub>c i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                  proof - 
                    have "(id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c p =
                               IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c p"
                      by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c q) \<circ>\<^sub>c \<langle>p,id one\<rangle>"
                      by (typecheck_cfuncs, metis cart_prod_extract_left id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c  \<langle>p,successor \<circ>\<^sub>c q\<rangle>"
                      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c  \<langle>p,successor \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>p,successor \<circ>\<^sub>c q\<rangle> \<rangle> "
                      using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,i \<circ>\<^sub>c successor \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c q\<rangle> \<rangle> "
                      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,(i \<circ>\<^sub>c successor) \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, successor \<circ>\<^sub>c q\<rangle> \<rangle> "
                      by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,(m \<circ>\<^sub>c i) \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, successor \<circ>\<^sub>c q\<rangle> \<rangle> "
                      using i_induct by presburger
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, m \<circ>\<^sub>c i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, successor \<circ>\<^sub>c q\<rangle> \<rangle> "
                      by (typecheck_cfuncs, simp add: comp_associative2)
                    then show ?thesis
                      by (simp add: calculation)
                  qed



(*Previously, what follows below started on line 273
          proof(rule one_separator[where X= "\<nat>\<^sub>c \<times>\<^sub>c one", where Y=\<Omega>])
            show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c q : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<And>pone. pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c q) \<circ>\<^sub>c pone =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q) \<circ>\<^sub>c pone"  
            proof - 
                fix pone 
                assume pone_type[type_rule]: "pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
                then obtain p where p_def: "pone = \<langle>p, id(one)\<rangle>" and p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
                  by (typecheck_cfuncs, metis cart_prod_decomp one_unique_element)

                have LHS: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c q) \<circ>\<^sub>c pone = 
                       IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p,  m \<circ>\<^sub>c i  \<circ>\<^sub>c q\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                proof - 
                  have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c q) \<circ>\<^sub>c pone =
                         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c q)) \<circ>\<^sub>c \<langle>p, id(one)\<rangle>"
                    by (typecheck_cfuncs, smt (z3) comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition p_def)
                  also have "... = (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c q)) \<circ>\<^sub>c \<langle>p, id(one)\<rangle>"
                    using transpose_func_def by (typecheck_cfuncs, presburger)
                  also have "... =  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p, (successor \<circ>\<^sub>c q)\<rangle>"
                    using cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2 by (typecheck_cfuncs, force)
                  also have "... =  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p, (successor \<circ>\<^sub>c q)\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, (successor \<circ>\<^sub>c q)\<rangle>\<rangle>"
                    using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                  also have "... =  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c (successor \<circ>\<^sub>c q)\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, (successor \<circ>\<^sub>c q)\<rangle>\<rangle>"
                    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
                  also have "... =  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, (i \<circ>\<^sub>c successor) \<circ>\<^sub>c q\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                    using comp_associative2 by (typecheck_cfuncs, force)
                  also have "... =  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, (m \<circ>\<^sub>c i) \<circ>\<^sub>c q\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                    using i_induct by presburger
                  also have "... =  IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p,  m \<circ>\<^sub>c i  \<circ>\<^sub>c q\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, successor \<circ>\<^sub>c q\<rangle>\<rangle>"
                    using comp_associative2 by (typecheck_cfuncs, auto) 
                  then show ?thesis
                    by (simp add: calculation)
                qed


                have RHS: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q) \<circ>\<^sub>c pone =
                           IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>p, q\<rangle>\<rangle>"
                proof - 
                  have"(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q) \<circ>\<^sub>c pone = 
                             (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  q) \<circ>\<^sub>c  \<langle>p, id(one)\<rangle>"
                    by (typecheck_cfuncs , smt (z3) comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition p_def)
                  also have "... = (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)  \<circ>\<^sub>c  \<langle>p, q\<rangle>"
                    using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 transpose_func_def by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i),eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle>  \<circ>\<^sub>c  \<langle>p, q\<rangle>"
                    by (typecheck_cfuncs, simp add: comp_associative2)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c  \<langle>p, q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>p, q\<rangle>\<rangle>"
                    using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)        
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c q\<rangle>\<rangle>"
                    using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>p, q\<rangle>\<rangle>"
                    using id_left_unit2 by (typecheck_cfuncs, presburger)
                  then show ?thesis
                    by (simp add: calculation)
                qed


*)


          oops

(* Definition 2.6.12 *)
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool " (infix "is'_fixed'_point'_of" 50) where 
  "fixed_point a g = (\<exists> A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = a)"

lemma fixed_point_def2: 
  assumes "g : A \<rightarrow> A" "a \<in>\<^sub>c A"
  shows "fixed_point a g = (g \<circ>\<^sub>c a = a)"
  unfolding fixed_point_def using assms by blast
  
(*Definition 2.6.12b*)
definition fixed_point_property :: "cset \<Rightarrow> bool" where
  "fixed_point_property A = (\<forall> g. g : A \<rightarrow> A \<longrightarrow> (\<exists> a . fixed_point a g \<and> a \<in>\<^sub>c A))"

(*Theorem 2.6.13*)
lemma Lawveres_fixed_point_theorem:
  assumes p_type[type_rule]: "p : X \<rightarrow> A\<^bsup>X\<^esup>"
  assumes p_surj: "surjective p"
  shows "fixed_point_property A"
proof(unfold fixed_point_property_def,auto) 
  fix g 
  assume g_type[type_rule]: "g : A \<rightarrow> A"
  obtain \<phi> where \<phi>_def: "\<phi> = p\<^sup>\<flat>"
    by auto
  then have \<phi>_type[type_rule]: "\<phi> : X \<times>\<^sub>c X \<rightarrow> A"
    by (simp add: flat_type p_type)
  obtain f where f_def: "f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X)"
    by auto
  then have f_type[type_rule]:"f : X \<rightarrow> A"
    using \<phi>_type comp_type diagonal_type f_def g_type by blast
  obtain x_f where x_f: "metafunc f = p \<circ>\<^sub>c x_f \<and> x_f \<in>\<^sub>c X"
    using assms by (typecheck_cfuncs, metis p_surj surjective_def2)
  have "\<phi>\<^bsub>(-,x_f)\<^esub> = f"
  proof(rule one_separator[where X = "X", where Y = A])
    show "\<phi>\<^bsub>(-,x_f)\<^esub> : X \<rightarrow> A"
      using assms by (typecheck_cfuncs, simp add: x_f)
    show "f : X \<rightarrow> A"
      by (simp add: f_type)
    show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> \<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
    proof - 
      fix x 
      assume x_type[type_rule]: "x \<in>\<^sub>c X"
      have "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        using assms by (typecheck_cfuncs, meson right_param_on_el x_f)
      also have "... = ((eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p)) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        using assms \<phi>_def inv_transpose_func_def2 by auto
      also have "... = (eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        by (typecheck_cfuncs, metis comp_associative2 x_f)
      also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>id X  \<circ>\<^sub>c  x, p \<circ>\<^sub>c x_f\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod x_f by (typecheck_cfuncs, force)
      also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>x, metafunc f\<rangle>"
        using id_left_unit2 x_f by (typecheck_cfuncs, auto)
      also have "... = f \<circ>\<^sub>c x"
        by (simp add: eval_lemma f_type x_type)
      then show "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
        by (simp add: calculation)
    qed
  qed
  then have "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x_f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X) \<circ>\<^sub>c x_f"
    by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_associative domain_comp f_def x_f)
  then have "\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle> = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>"
    using  diag_on_elements right_param_on_el x_f by (typecheck_cfuncs, auto)
  then have "(\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>) is_fixed_point_of g"
    by (metis \<open>\<phi>\<^bsub>(-,x_f)\<^esub> = f\<close> \<open>\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x_f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal X \<circ>\<^sub>c x_f\<close> comp_type diag_on_elements f_type fixed_point_def2 g_type x_f)
  then show "\<exists>a. a is_fixed_point_of g \<and> a \<in>\<^sub>c A"
    using fixed_point_def cfunc_type_def g_type by auto
qed

(*Theorem 2.6.14*)
lemma Cantors_Negative_Theorem:
  "\<nexists> s. s : X \<rightarrow> \<P> X \<and> surjective(s)"
proof(rule ccontr, auto)
  fix s 
  assume s_type: "s : X \<rightarrow> \<P> X"
  assume s_surj: "surjective s"
  then have Omega_has_ffp: "fixed_point_property \<Omega>"
    using Lawveres_fixed_point_theorem powerset_def s_type by auto
  have Omega_doesnt_have_ffp: "\<not>(fixed_point_property \<Omega>)"
    unfolding fixed_point_property_def
  proof(unfold fixed_point_def, auto)   
    have  "NOT : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. (\<forall>A. a \<in>\<^sub>c A \<longrightarrow> NOT : A \<rightarrow> A \<longrightarrow> NOT \<circ>\<^sub>c a \<noteq> a) \<or> \<not> a \<in>\<^sub>c \<Omega>)"
      by (typecheck_cfuncs, metis AND_complementary AND_idempotent OR_complementary OR_idempotent true_false_distinct)
    then show "\<exists>g. g : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. (\<forall>A. a \<in>\<^sub>c A \<longrightarrow> g : A \<rightarrow> A \<longrightarrow> g \<circ>\<^sub>c a \<noteq> a) \<or> \<not> a \<in>\<^sub>c \<Omega>)"
      by auto
  qed
  show False
    using Omega_doesnt_have_ffp Omega_has_ffp by auto
qed

lemma generalized_Cantors_Negative_Theorem:
  assumes "\<Omega> \<le>\<^sub>c Y"
  shows "\<nexists> s. s : X \<rightarrow> Y\<^bsup>X\<^esup> \<and> surjective(s)"
proof(rule ccontr, auto)
  fix s 
  assume s_type: "s : X \<rightarrow> Y\<^bsup>X\<^esup>"
  assume s_surj: "surjective s"
  obtain m where m_def: "m : Y\<^bsup>X\<^esup> \<rightarrow> X" and m_mono: "monomorphism(m)"
    using epis_give_monos s_surj s_type surjective_is_epimorphism by blast
  have "\<Omega>\<^bsup>X\<^esup> \<le>\<^sub>c Y\<^bsup>X\<^esup>"
    oops


(*Exercise 2.6.15*)
lemma Cantors_Positive_Theorem:
  "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
proof - 
  have eq_pred_sharp_type[type_rule]: "(eq_pred X)\<^sup>\<sharp> : X \<rightarrow>  \<Omega>\<^bsup>X\<^esup>"
    by (typecheck_cfuncs)
  have "injective((eq_pred X)\<^sup>\<sharp>)"
    unfolding injective_def
  proof(auto)
    fix x y 
    assume "x \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have x_type[type_rule]: "x \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume "y \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have y_type[type_rule]:"y \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume eq: "eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c x = eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c y"
    have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
    proof - 
      have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c x\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c y\<rangle>"
        by (simp add: eq)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      also have "... = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      then show ?thesis
        by (simp add: calculation)
    qed
    then show "x = y"
      by (metis eq_pred_iff_eq x_type y_type)
  qed
  then show "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
    using eq_pred_sharp_type injective_imp_monomorphism by blast
qed


(*Corollary 2.6.15*)
(*This is only a note: For any set X, the set \<P>X of its subsets is strictly larger than X*)






end