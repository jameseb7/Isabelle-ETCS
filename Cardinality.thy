theory Cardinality
  imports ETCS_Axioms
begin

lemma exp_set_smaller_than:
  assumes "A \<le>\<^sub>c B"
  assumes "nonempty(X)"   (*This seems like the appropriate assumption
                            since if A \<cong> \<emptyset> and X \<cong> \<emptyset> and B nonempty then 
                            X\<^bsup>A\<^esup> \<cong> 1 but X\<^bsup>B\<^esup> \<cong> \<emptyset> so the conclusion does not follow*)
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
proof(cases "nonempty(A)")
  assume "\<not>nonempty A"
  then have "(X\<^bsup>A\<^esup>) \<cong> one"
    by (simp add: Y_to_empty)
  then have "terminal_object(X\<^bsup>A\<^esup>)"
    by (simp add: iso_to1_is_term)
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
  proof(cases "nonempty(X\<^bsup>B\<^esup>)")
    show "nonempty (X\<^bsup>B\<^esup>) \<Longrightarrow> X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
      by (smt \<open>X\<^bsup>A\<^esup> \<cong> one\<close> cfunc_type_def comp_type composition_of_monic_pair_is_monic element_monomorphism is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic nonempty_def)
  next
    assume  "\<not> nonempty (X\<^bsup>B\<^esup>)" 
    then have "\<not> nonempty(X)"
      using empty_to_nonempty_converse no_el_iff_iso_0 by blast
    then have False
      using assms(2) by blast
    then show "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
      by simp
  qed
next
  assume nonemptyA: "nonempty A"
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
 proof (unfold is_smaller_than_def, cases "\<exists>x. x \<in>\<^sub>c X", auto)
  fix x
  assume x_type[type_rule]: "x \<in>\<^sub>c X"

  obtain m where m_def[type_rule]: "m : A \<rightarrow> B" "monomorphism m"
    using assms unfolding is_smaller_than_def by auto

  show "\<exists>m. m : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup> \<and> monomorphism m"
  proof (rule_tac x="(((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>))
    \<circ>\<^sub>c dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) 
    \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id (X\<^bsup>A\<^esup>)))\<^sup>\<sharp>" in exI, auto)

    show "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
      dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
      swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup>"
      by  typecheck_cfuncs

    have mono1: "monomorphism(try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))"
      by (typecheck_cfuncs,simp add: cfunc_cross_prod_mono id_isomorphism iso_imp_epi_and_monic m_def(2) try_cast_mono)
    have "monomorphism(swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>))"
      by (simp add: swap_mono)
    then have mono2: "monomorphism(swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)))"
      using m_def by (typecheck_cfuncs, simp add: cfunc_type_def composition_of_monic_pair_is_monic mono1)
    have mono3: "monomorphism(dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)))"
      by (simp add: dist_prod_coprod_inv_iso iso_imp_epi_and_monic)
    then have mono4: "monomorphism(dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) 
    \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id (X\<^bsup>A\<^esup>)))"
      by (typecheck_cfuncs, simp add: cfunc_type_def composition_of_monic_pair_is_monic mono2 mono3)
    then have mono5: "monomorphism((dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) 
    \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id (X\<^bsup>A\<^esup>)))\<^sup>\<sharp>)"
      using m_def sharp_pres_mono apply typecheck_cfuncs
      by (meson nonemptyA comp_type mono4 nonempty_def sharp_pres_mono)
 
    oops

end