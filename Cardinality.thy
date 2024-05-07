theory Cardinality
  imports ETCS_Axioms Countable
begin




lemma non_init_non_ter_sets:
  assumes "\<not>(terminal_object X)"
  assumes "\<not>(initial_object X)"
  shows "\<Omega> \<le>\<^sub>c X" 
proof - 
  obtain x1 and x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and 
                         x2_type[type_rule]: "x2 \<in>\<^sub>c X" and
                                   distinct: "x1 \<noteq> x2"
    by (metis is_empty_def assms iso_empty_initial iso_to1_is_term no_el_iff_iso_0 single_elem_iso_one)

  then have map_type: "(x1 \<amalg> x2) \<circ>\<^sub>c case_bool   : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have injective: "injective((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
  proof(unfold injective_def, auto)
    fix \<omega>1 \<omega>2 
    assume "\<omega>1 \<in>\<^sub>c domain (x1 \<amalg> x2 \<circ>\<^sub>c case_bool)"
    then have \<omega>1_type[type_rule]: "\<omega>1 \<in>\<^sub>c \<Omega>"
      using cfunc_type_def map_type by auto
    assume "\<omega>2 \<in>\<^sub>c domain (x1 \<amalg> x2 \<circ>\<^sub>c case_bool)"
    then have \<omega>2_type[type_rule]: "\<omega>2 \<in>\<^sub>c \<Omega>"
      using cfunc_type_def map_type by auto
    
    assume equals: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = (x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2"
    show "\<omega>1 = \<omega>2"
    proof(cases "\<omega>1 = \<t>", auto)
      assume "\<omega>1 = \<t>"
      show "\<t> = \<omega>2"
      proof(rule ccontr)
        assume " \<t> \<noteq> \<omega>2"
        then have "\<f> = \<omega>2"
          using \<open>\<t> \<noteq> \<omega>2\<close> true_false_only_truth_values by (typecheck_cfuncs, blast)
        then have RHS: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x2"
          by (meson coprod_case_bool_false x1_type x2_type)
        have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x1"
          using \<open>\<omega>1 = \<t>\<close> coprod_case_bool_true x1_type x2_type by blast
        then show False
          using RHS distinct equals by force
      qed
    next
      assume "\<omega>1 \<noteq> \<t>"
      then have "\<omega>1 = \<f>"
        using  true_false_only_truth_values by (typecheck_cfuncs, blast)
      have "\<omega>2 = \<f>"
      proof(rule ccontr)
        assume "\<omega>2 \<noteq> \<f>"
        then have "\<omega>2 = \<t>"
          using  true_false_only_truth_values by (typecheck_cfuncs, blast)
        then have RHS: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x2"
          using \<open>\<omega>1 = \<f>\<close> coprod_case_bool_false equals x1_type x2_type by auto
        have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x1"
          using \<open>\<omega>2 = \<t>\<close> coprod_case_bool_true equals x1_type x2_type by presburger
        then show False
          using RHS distinct equals by auto
      qed
      show "\<omega>1 = \<omega>2"
        by (simp add: \<open>\<omega>1 = \<f>\<close> \<open>\<omega>2 = \<f>\<close>)
    qed
  qed
  then have "monomorphism((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    using injective_imp_monomorphism by auto
  then show "\<Omega> \<le>\<^sub>c X"
    using  is_smaller_than_def map_type by blast
qed




lemma exp_set_smaller_than1:
  assumes "A \<le>\<^sub>c B"
  assumes "nonempty(X)"   (*This seems like the appropriate assumption
                            since if A \<cong> \<emptyset> and X \<cong> \<emptyset> and B nonempty then 
                            X\<^bsup>A\<^esup> \<cong> 1 but X\<^bsup>B\<^esup> \<cong> \<emptyset> so the conclusion does not follow*)
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
proof (unfold is_smaller_than_def)

  obtain x where x_type[type_rule]: "x \<in>\<^sub>c X"
    using assms unfolding nonempty_def by auto

  obtain m where m_def[type_rule]: "m : A \<rightarrow> B" "monomorphism m"
    using assms unfolding is_smaller_than_def by auto

  show "\<exists>m. m : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup> \<and> monomorphism m"
  proof (rule_tac x="(((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>))
    \<circ>\<^sub>c dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) 
    \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id (X\<^bsup>A\<^esup>)))\<^sup>\<sharp>" in exI, auto)

    show "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup>"
      by  typecheck_cfuncs
    then show "monomorphism
      (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
        dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
        swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)"
    proof (unfold monomorphism_def3, auto)
      fix g h Z
      assume g_type[type_rule]: "g : Z \<rightarrow> X\<^bsup>A\<^esup>"
      assume h_type[type_rule]: "h : Z \<rightarrow> X\<^bsup>A\<^esup>"

      assume eq: "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
          dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
          swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c g
        =
          ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
          dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
          swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h"

      show "g = h"
      proof (typecheck_cfuncs, rule_tac same_evals_equal[where Z=Z, where A=A, where X=X], auto)

        show "eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f h"
        proof (typecheck_cfuncs, rule one_separator[where X="A \<times>\<^sub>c Z", where Y="X"], auto)
          fix az
          assume az_type[type_rule]: "az \<in>\<^sub>c A \<times>\<^sub>c Z"

          obtain a z where az_types[type_rule]: "a \<in>\<^sub>c A" "z \<in>\<^sub>c Z" and az_def: "az = \<langle>a,z\<rangle>"
            using cart_prod_decomp az_type by blast

          have "(eval_func X B) \<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c g)) = 
          (eval_func X B) \<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h))"
            using eq by simp
          then have "(eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) = 
          (eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            using identity_distributes_across_composition by (typecheck_cfuncs, auto)
          then have "((eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>))) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) = 
          ((eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>))) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            by (typecheck_cfuncs, smt eq inv_transpose_func_def2 inv_transpose_of_composition)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g)
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            using   transpose_func_def by (typecheck_cfuncs,auto)
          then have "(((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>
          = (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>"
            by auto
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>"
            by (typecheck_cfuncs, auto simp add: comp_associative2)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs_prems, smt comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>try_cast m \<circ>\<^sub>c m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>try_cast m \<circ>\<^sub>c m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs_prems, smt)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>(try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>(try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs, auto simp add: comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            using m_def(2) try_cast_m_m by (typecheck_cfuncs, auto)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z, left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a\<rangle>"
            using swap_ap by (typecheck_cfuncs, auto)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m))) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m))) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            using dist_prod_coprod_inv_left_ap by (typecheck_cfuncs, auto)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m)))) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m)))) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
            = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: left_coproj_cfunc_coprod)
          then have "eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
            = eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
          then have "eval_func X A \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c z\<rangle> = eval_func X A \<circ>\<^sub>c \<langle>a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: swap_ap)
          then have "eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, z\<rangle> = eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>a, z\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          then show "(eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f g) \<circ>\<^sub>c az = (eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f h) \<circ>\<^sub>c az"
            unfolding az_def by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
        qed
      qed
    qed
  qed
qed



lemma exp_set_smaller_than2:
  assumes "A \<le>\<^sub>c B"
  shows "A\<^bsup>X\<^esup> \<le>\<^sub>c B\<^bsup>X\<^esup>"
proof (unfold is_smaller_than_def)
  obtain m where m_def[type_rule]: "m : A \<rightarrow> B" "monomorphism m"
        using assms unfolding is_smaller_than_def by auto
  show "\<exists>m. m : A\<^bsup>X\<^esup> \<rightarrow> B\<^bsup>X\<^esup> \<and> monomorphism m"
  proof (rule_tac x="(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>" in exI, auto)
    show "(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> : A\<^bsup>X\<^esup> \<rightarrow> B\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    then show "monomorphism((m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)"
    proof (unfold monomorphism_def3, auto)
      fix g h Z
      assume g_type[type_rule]: "g : Z \<rightarrow> A\<^bsup>X\<^esup>"
      assume h_type[type_rule]: "h : Z \<rightarrow> A\<^bsup>X\<^esup>"

      assume eq: "(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c g = (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c h"
      show "g = h"
      proof (typecheck_cfuncs, rule_tac same_evals_equal[where Z=Z, where A=X, where X=A], auto)
          have "((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = 
                ((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            by (typecheck_cfuncs, smt comp_associative2 eq inv_transpose_func_def2 inv_transpose_of_composition)
          then have "(m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = (m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            by (smt comp_type eval_func_type m_def(1) transpose_func_def)
          then have "m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g))  = m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h))"
            by (typecheck_cfuncs, smt comp_associative2)
          then have "eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            using m_def monomorphism_def3 by (typecheck_cfuncs, blast)
          then show "(eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g))  = (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h))"
            by (typecheck_cfuncs, smt comp_associative2)
      qed
    qed
  qed
qed


lemma leq_transitive:
  assumes "A \<le>\<^sub>c B"
  assumes "B \<le>\<^sub>c C"
  shows   "A \<le>\<^sub>c C"
  by (typecheck_cfuncs, metis (full_types) assms cfunc_type_def comp_type composition_of_monic_pair_is_monic is_smaller_than_def)

lemma "Generalized_Cantors_Positive_Theorem":
  assumes "\<not>(terminal_object Y)"
  assumes "\<not>(initial_object Y)"
  shows "X  \<le>\<^sub>c Y\<^bsup>X\<^esup>"
proof - 
  have "\<Omega> \<le>\<^sub>c Y"
    by (simp add: assms non_init_non_ter_sets)
  then have fact: "\<Omega>\<^bsup>X\<^esup> \<le>\<^sub>c  Y\<^bsup>X\<^esup>"
    by (simp add: exp_set_smaller_than2)
  have "X \<le>\<^sub>c \<Omega>\<^bsup>X\<^esup>"
    by (meson Cantors_Positive_Theorem CollectI injective_imp_monomorphism is_smaller_than_def)
  then show ?thesis
    using fact leq_transitive by blast
qed


lemma Generalized_Cantors_Negative_Theorem:
  assumes "\<not>(initial_object X)"
  assumes "\<not>(terminal_object Y)"
  shows "\<nexists> s. s : X \<rightarrow> Y\<^bsup>X\<^esup> \<and> surjective(s)"
proof(rule ccontr, auto) 
  fix s 
  assume s_type: "s : X \<rightarrow> Y\<^bsup>X\<^esup>"
  assume s_surj: "surjective(s)"
  obtain m where m_type: "m : Y\<^bsup>X\<^esup> \<rightarrow> X" and m_mono: "monomorphism(m)"
    by (meson epis_give_monos s_surj s_type surjective_is_epimorphism)
  have "nonempty X"
    using is_empty_def assms(1) iso_empty_initial no_el_iff_iso_0 nonempty_def by blast
  then have nonempty: "nonempty (\<Omega>\<^bsup>X\<^esup>)"
    using nonempty_def nonempty_to_nonempty true_func_type by blast
  show False
  proof(cases "initial_object Y")
    assume "initial_object Y"
    then have "Y\<^bsup>X\<^esup> \<cong> \<emptyset>"
      by (simp add: \<open>nonempty X\<close> empty_to_nonempty initial_iso_empty no_el_iff_iso_0)      
    then show False
      by (meson is_empty_def assms(1) comp_type iso_empty_initial no_el_iff_iso_0 s_type) 
  next
    assume "\<not> initial_object Y"
    then have "\<Omega> \<le>\<^sub>c Y"
      by (simp add: assms(2) non_init_non_ter_sets)
    then obtain n where n_type: "n : \<Omega>\<^bsup>X\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>" and n_mono: "monomorphism(n)"
      by (meson exp_set_smaller_than2 is_smaller_than_def)
    then have mn_type: "m \<circ>\<^sub>c n :  \<Omega>\<^bsup>X\<^esup> \<rightarrow> X"
      by (meson comp_type m_type)
    have mn_mono: "monomorphism(m \<circ>\<^sub>c n)"
      using cfunc_type_def composition_of_monic_pair_is_monic m_mono m_type n_mono n_type by presburger
    then have "\<exists>g. g: X  \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> epimorphism(g) \<and> g \<circ>\<^sub>c (m \<circ>\<^sub>c n) = id (\<Omega>\<^bsup>X\<^esup>)"
      by (simp add: mn_type monos_give_epis nonempty)
    then show False
      by (metis Cantors_Negative_Theorem epi_is_surj powerset_def)
  qed
qed





lemma exp_set_smaller_than3:
  assumes "A \<le>\<^sub>c B"
  assumes "X \<le>\<^sub>c Y"
  assumes "nonempty(X)"
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
proof - 
  have leq1: "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
    by (simp add: assms(1) assms(3) exp_set_smaller_than1)    
  have leq2: "X\<^bsup>B\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    by (simp add: assms(2) exp_set_smaller_than2)
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    using leq1 leq2 leq_transitive by blast
qed


lemma sets_squared:
  "A\<^bsup>\<Omega>\<^esup> \<cong> A \<times>\<^sub>c A "
proof - 
  obtain \<phi> where \<phi>_def: "\<phi> = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle>" and
                 \<phi>_type[type_rule]: "\<phi> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A \<times>\<^sub>c A"
                  by typecheck_cfuncs
  have "injective(\<phi>)"
  proof(unfold injective_def,auto)
    fix f g 
    assume "f \<in>\<^sub>c domain \<phi>" then have f_type[type_rule]: "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
      using \<phi>_type cfunc_type_def by (typecheck_cfuncs, auto)
    assume "g \<in>\<^sub>c domain \<phi>" then have g_type[type_rule]: "g \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
      using \<phi>_type cfunc_type_def by (typecheck_cfuncs, auto)
    assume eqs: "\<phi> \<circ>\<^sub>c f = \<phi> \<circ>\<^sub>c g"
    show "f = g"
    proof(rule one_separator[where X = one, where Y = "A\<^bsup>\<Omega>\<^esup>"])
      show "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
        by typecheck_cfuncs
      show "g \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
        by typecheck_cfuncs
      show "\<And>id_1. id_1 \<in>\<^sub>c one \<Longrightarrow> f \<circ>\<^sub>c id_1 = g \<circ>\<^sub>c id_1"
      proof(rule same_evals_equal[where Z = one, where X = A, where A = \<Omega>])
        show "\<And>id_1. id_1 \<in>\<^sub>c one \<Longrightarrow> f \<circ>\<^sub>c id_1 \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
          by (simp add: comp_type f_type)
        show "\<And>id_1. id_1 \<in>\<^sub>c one \<Longrightarrow> g \<circ>\<^sub>c id_1 \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
          by (simp add: comp_type g_type)
        show "\<And>id_1.
       id_1 \<in>\<^sub>c one \<Longrightarrow>
       eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f \<circ>\<^sub>c id_1 =
       eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g \<circ>\<^sub>c id_1"
        proof  -
          fix id_1
          assume id1_is: "id_1 \<in>\<^sub>c one"
          then have id1_eq: "id_1 = id(one)"
            using id_type one_unique_element by auto

          obtain a1 a2 where phi_f_def: "\<phi> \<circ>\<^sub>c f = \<langle>a1,a2\<rangle> \<and> a1 \<in>\<^sub>c A \<and> a2 \<in>\<^sub>c A"
            using \<phi>_type cart_prod_decomp comp_type f_type by blast
          have equation1: "\<langle>a1,a2\<rangle> =  \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>  ,
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , f \<rangle> \<rangle>"
          proof - 
              have "\<langle>a1,a2\<rangle> = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c f"
                using \<phi>_def phi_f_def by auto
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f\<rangle>"
                by (typecheck_cfuncs,smt cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f \<rangle>  ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>)\<circ>\<^sub>c f \<rangle> \<rangle>"
                by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>  ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , f \<rangle> \<rangle>"    
                by (typecheck_cfuncs, metis id1_eq id1_is id_left_unit2 id_right_unit2 terminal_func_unique)
              then show ?thesis using calculation by auto
          qed
          have equation2: "\<langle>a1,a2\<rangle> =  \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g \<rangle>  ,
                                      eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , g\<rangle> \<rangle>"
          proof - 
              have "\<langle>a1,a2\<rangle> = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c g"
                using \<phi>_def eqs phi_f_def by auto
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g ,
                                eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g\<rangle>"
                by (typecheck_cfuncs,smt cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c g \<rangle>  ,
                                eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g, id(A\<^bsup>\<Omega>\<^esup>)\<circ>\<^sub>c g \<rangle> \<rangle>"
                by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g \<rangle>  ,
                                eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , g \<rangle> \<rangle>"    
                by (typecheck_cfuncs, metis id1_eq id1_is id_left_unit2 id_right_unit2 terminal_func_unique)
              then show ?thesis using calculation by auto
         qed
            have "\<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>  , eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , f \<rangle> \<rangle> = 
                  \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g \<rangle>  , eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , g \<rangle> \<rangle>"
              using equation1 equation2 by auto
            then have equation3: "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle> = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g\<rangle>) \<and> 
                                  (eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, f \<rangle> = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, g\<rangle>)"
              using  cart_prod_eq2 by (typecheck_cfuncs, auto)
            have "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f  = eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g"
            proof(rule one_separator[where X = "\<Omega> \<times>\<^sub>c one", where Y = A])
              show "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f : \<Omega> \<times>\<^sub>c one \<rightarrow> A"
                by typecheck_cfuncs
              show "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g : \<Omega> \<times>\<^sub>c one \<rightarrow> A"
                by typecheck_cfuncs
              show "\<And>x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c one \<Longrightarrow>
         (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c x"
              proof - 
                fix x
                assume x_type[type_rule]: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c one"
                then obtain w i where  x_def: "(w \<in>\<^sub>c \<Omega>) \<and> (i \<in>\<^sub>c one) \<and> (x = \<langle>w,i\<rangle>)"
                  using cart_prod_decomp by blast
                then have i_def: "i = id(one)"
                  using id1_eq id1_is one_unique_element by auto
                have w_def: "(w = \<f>) \<or> (w = \<t>)"
                  by (simp add: true_false_only_truth_values x_def)
                then have x_def2: "(x = \<langle>\<f>,i\<rangle>) \<or> (x = \<langle>\<t>,i\<rangle>)"
                  using x_def by auto
                show "(eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c x"
                proof(cases "(x = \<langle>\<f>,i\<rangle>)",auto)
                  assume case1: "x = \<langle>\<f>,i\<rangle>"
                  have "(eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<f>,i\<rangle> = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>)"
                    using case1 comp_associative2 x_type by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<f>,f \<circ>\<^sub>c i\<rangle>"
                    using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, f \<rangle>"
                    using f_type false_func_type i_def id_left_unit2 id_right_unit2 by auto
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, g\<rangle>"
                    using equation3 by blast
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<f>,g \<circ>\<^sub>c i\<rangle>"
                    by (typecheck_cfuncs, simp add: i_def id_left_unit2 id_right_unit2)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>)"
                    using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>"
                    using case1 comp_associative2 x_type by (typecheck_cfuncs, auto)
                  then show "(eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>,i\<rangle> = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>"
                    by (simp add: calculation)
              next
                  assume case2: "x \<noteq> \<langle>\<f>,i\<rangle>"
                  then have x_eq: "x = \<langle>\<t>,i\<rangle>"
                    using x_def2 by blast
                  have "(eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<t>,i\<rangle> = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>)"
                      using case2 x_eq comp_associative2 x_type by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<t>,f \<circ>\<^sub>c i\<rangle>"
                      using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>"
                    using f_type i_def id_left_unit2 id_right_unit2 true_func_type by auto
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g\<rangle>"
                    using equation3 by blast
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<t>,g \<circ>\<^sub>c i\<rangle>"
                      by (typecheck_cfuncs, simp add: i_def id_left_unit2 id_right_unit2)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>)"
                      using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>"
                    using comp_associative2 x_eq x_type by (typecheck_cfuncs, blast)
                  then show "(eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c x"
                    by (simp add: calculation x_eq)
                qed
              qed
            qed
            then show "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f \<circ>\<^sub>c id_1 = eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g \<circ>\<^sub>c id_1"
              using  f_type g_type same_evals_equal by blast
          qed
        qed
      qed
    qed
    then have "monomorphism(\<phi>)"
      using injective_imp_monomorphism by auto
    have "surjective(\<phi>)"
      unfolding surjective_def
    proof(auto)
      fix y 
      assume "y \<in>\<^sub>c codomain \<phi>" then have y_type[type_rule]: "y \<in>\<^sub>c A \<times>\<^sub>c A"
        using \<phi>_type cfunc_type_def by auto
      then obtain a1 a2 where y_def[type_rule]: "y = \<langle>a1,a2\<rangle> \<and> a1 \<in>\<^sub>c A \<and> a2 \<in>\<^sub>c A"
        using cart_prod_decomp by blast
      then have aua: "(a1 \<amalg> a2): one \<Coprod> one \<rightarrow> A"
        by (typecheck_cfuncs, simp add: y_def)
     
    
      obtain f where f_def: "f = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj \<Omega> one)\<^sup>\<sharp>" and
                     f_type[type_rule]: "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
        by (meson aua case_bool_type comp_type left_cart_proj_type transpose_func_type)
     have a1_is: "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = a1"
     proof-
       have "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f"
         by (typecheck_cfuncs, simp add: comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f\<rangle>"
         by (metis cfunc_type_def f_type id_left_unit id_right_unit id_type one_unique_element terminal_func_comp terminal_func_type true_func_type)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id(\<Omega>) \<circ>\<^sub>c \<t>, f \<circ>\<^sub>c id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>, id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
       also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<t>, id(one)\<rangle>"
         using comp_associative2 by (typecheck_cfuncs, blast)
       also have "... = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj \<Omega> one) \<circ>\<^sub>c \<langle>\<t>, id(one)\<rangle>"
         by (typecheck_cfuncs, metis  aua f_def flat_cancels_sharp inv_transpose_func_def2)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c \<t>"
         by (typecheck_cfuncs, smt case_bool_type aua comp_associative2 left_cart_proj_cfunc_prod)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c left_coproj one one"
         by (simp add: case_bool_true)
       also have "... = a1"
         using left_coproj_cfunc_coprod y_def by blast
       then show ?thesis using calculation by auto
     qed
     have a2_is: "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = a2"
     proof-
       have "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f"
         by (typecheck_cfuncs, simp add: comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, f\<rangle>"
         by (metis cfunc_type_def f_type id_left_unit id_right_unit id_type one_unique_element terminal_func_comp terminal_func_type false_func_type)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id(\<Omega>) \<circ>\<^sub>c \<f>, f \<circ>\<^sub>c id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>, id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
       also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<f>, id(one)\<rangle>"
         using comp_associative2 by (typecheck_cfuncs, blast)
       also have "... = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj \<Omega> one) \<circ>\<^sub>c \<langle>\<f>, id(one)\<rangle>"
         by (typecheck_cfuncs, metis  aua f_def flat_cancels_sharp inv_transpose_func_def2)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c \<f>"
         by (typecheck_cfuncs, smt aua comp_associative2 left_cart_proj_cfunc_prod)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c right_coproj one one"
         by (simp add: case_bool_false)
       also have "... = a2"
         using right_coproj_cfunc_coprod y_def by blast
       then show ?thesis using calculation by auto
     qed
     have "\<phi> \<circ>\<^sub>c f  = \<langle>a1,a2\<rangle>"
       unfolding \<phi>_def by (typecheck_cfuncs, simp add: a1_is a2_is cfunc_prod_comp)
     then show "\<exists>x. x \<in>\<^sub>c domain \<phi> \<and> \<phi> \<circ>\<^sub>c x = y"
       using \<phi>_type cfunc_type_def f_type y_def by auto
   qed
   then have "epimorphism(\<phi>)"
     by (simp add: surjective_is_epimorphism)
   then have "isomorphism(\<phi>)"
     by (simp add: \<open>monomorphism \<phi>\<close> epi_mon_is_iso)
   then show ?thesis
     using \<phi>_type is_isomorphic_def by blast
qed

lemma exp_coprod:
  "A\<^bsup>(B \<Coprod> C)\<^esup> \<cong> A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>"
proof -
  obtain L where L_def: "L = (eval_func A B \<circ>\<^sub>c distribute_left_left B (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>))" and  L_type[type_rule]: "L : B \<times>\<^sub>c ((A\<^bsup>B\<^esup>) \<times>\<^sub>c (A\<^bsup>C\<^esup>)) \<rightarrow> A"
    by typecheck_cfuncs
  obtain R where R_def: "R = (eval_func A C \<circ>\<^sub>c distribute_left_right C (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>))" and R_type[type_rule]: "R : C \<times>\<^sub>c ((A\<^bsup>B\<^esup>) \<times>\<^sub>c (A\<^bsup>C\<^esup>)) \<rightarrow> A"
    by typecheck_cfuncs
  obtain \<phi> where \<phi>_def: "\<phi> = ((L \<amalg> R)  \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>))\<^sup>\<sharp>"  and \<phi>_type[type_rule]: "\<phi> : A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup> \<rightarrow> A\<^bsup>(B \<Coprod> C)\<^esup>"
    by typecheck_cfuncs
  have "injective(\<phi>)"
    unfolding  injective_def
  proof(safe)
    fix g h 
    assume "g \<in>\<^sub>c domain \<phi>" then have g_type[type_rule]: "g \<in>\<^sub>c A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>"
      using \<phi>_type cfunc_type_def by auto
    assume "h \<in>\<^sub>c domain \<phi>" then have h_type[type_rule]: "h \<in>\<^sub>c A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>"
      using \<phi>_type cfunc_type_def by auto
    assume eqn: "\<phi> \<circ>\<^sub>c g = \<phi> \<circ>\<^sub>c h"
    obtain ab1 and ac1 where f_def: "ab1 \<in>\<^sub>c A\<^bsup>B\<^esup> \<and> ac1 \<in>\<^sub>c A\<^bsup>C\<^esup> \<and> g = \<langle>ab1,ac1\<rangle>"
        using cart_prod_decomp g_type by blast
    obtain ab2 and ac2 where g_def: "ab2 \<in>\<^sub>c A\<^bsup>B\<^esup> \<and> ac2 \<in>\<^sub>c A\<^bsup>C\<^esup> \<and> h = \<langle>ab2,ac2\<rangle>"
        using cart_prod_decomp h_type by blast
    have left: "ab1 = ab2"
    proof(rule same_evals_equal[where Z = one, where X = A, where A = B])
      show "ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>"
        by (simp add: f_def)
      show "ab2 \<in>\<^sub>c A\<^bsup>B\<^esup>"
        by (simp add: g_def)
      show "eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab1 = eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab2"
      proof(rule one_separator[where X = "B\<times>\<^sub>c one", where Y = A])
        show "eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab1 : B \<times>\<^sub>c one \<rightarrow> A"
          using \<open>ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> flat_type inv_transpose_func_def2 by auto
        show "eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab2 : B \<times>\<^sub>c one \<rightarrow> A"
          using \<open>ab2 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> flat_type inv_transpose_func_def2 by auto
        show "\<And>x. x \<in>\<^sub>c B \<times>\<^sub>c one \<Longrightarrow>
         (eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab1) \<circ>\<^sub>c x =
         (eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab2) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c B \<times>\<^sub>c one"
          then obtain b where b_def: "b \<in>\<^sub>c B \<and> x = \<langle>b, id(one)\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique)
          then have lcoproj_b_type[type_rule]: "(left_coproj B C \<circ>\<^sub>c b) \<in>\<^sub>c (B \<Coprod> C)"
            using b_def by (typecheck_cfuncs, auto)
          have "(eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab1) \<circ>\<^sub>c x = eval_func A B \<circ>\<^sub>c (id\<^sub>c B \<times>\<^sub>f ab1) \<circ>\<^sub>c x"
            using \<open>ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> comp_associative2 x_type by (typecheck_cfuncs, fastforce)
          also have "... = eval_func A B \<circ>\<^sub>c (id B \<times>\<^sub>f ab1) \<circ>\<^sub>c \<langle>b, id(one)\<rangle>"
            using b_def by auto
          also have "... = eval_func A B \<circ>\<^sub>c \<langle>b, ab1\<rangle>"
            using \<open>ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> b_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs,auto)
          also have "... = eval_func A B \<circ>\<^sub>c distribute_left_left B (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>b,g\<rangle>"
            using b_def distribute_left_left_ap f_def by auto
          also have "... = L \<circ>\<^sub>c \<langle>b,g\<rangle>"
            using L_def b_def comp_associative2 by (typecheck_cfuncs, blast)
          also have  "... = ((L \<amalg> R) \<circ>\<^sub>c 
       left_coproj (B \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>))) \<circ>\<^sub>c \<langle>b,g\<rangle>"
            by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
          also have "... = (L \<amalg> R) \<circ>\<^sub>c 
       left_coproj (B \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c \<langle>b,g\<rangle>"
            using b_def comp_associative2 by (typecheck_cfuncs, fastforce)
          also have "... =  (L \<amalg> R) \<circ>\<^sub>c
       dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, g\<rangle>" 
            by (typecheck_cfuncs, simp add: b_def dist_prod_coprod_inv2_left_ap)
          also have "... = ((L \<amalg> R) \<circ>\<^sub>c
       dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, g\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = ((eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>)) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, g\<rangle>"
            by (typecheck_cfuncs, simp add: \<phi>_def transpose_func_def)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, g\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>(left_coproj B C \<circ>\<^sub>c b) \<circ>\<^sub>c id (one), g \<circ>\<^sub>c id (one)\<rangle>"
            using id_right_unit2 lcoproj_b_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c ((id(B \<Coprod> C) \<circ>\<^sub>c (left_coproj B C \<circ>\<^sub>c b))  \<times>\<^sub>f \<phi> \<circ>\<^sub>c g) \<circ>\<^sub>c  \<langle>id (one), id(one)\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod id_right_unit2 lcoproj_b_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c ((id(B \<Coprod> C) \<circ>\<^sub>c (left_coproj B C \<circ>\<^sub>c b))  \<times>\<^sub>f \<phi> \<circ>\<^sub>c h) \<circ>\<^sub>c  \<langle>id (one), id(one)\<rangle>"
            by (simp add: eqn)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>(left_coproj B C \<circ>\<^sub>c b) \<circ>\<^sub>c id (one), h \<circ>\<^sub>c id (one)\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod id_right_unit2 lcoproj_b_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, h\<rangle>"
            using id_right_unit2 lcoproj_b_type by (typecheck_cfuncs, auto)
          also have "... = ((eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>)) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, h\<rangle>"
            using comp_associative2 by (typecheck_cfuncs, blast)
          also have "... = ((L \<amalg> R) \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, h\<rangle>"
            by (typecheck_cfuncs, simp add: \<phi>_def transpose_func_def)
          also have "... = (L \<amalg> R) \<circ>\<^sub>c  dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c b, h\<rangle>" 
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... =  (L \<amalg> R) \<circ>\<^sub>c left_coproj (B \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c \<langle>b,h\<rangle>"
            by (typecheck_cfuncs, simp add: b_def dist_prod_coprod_inv2_left_ap)
          also have "... = L \<circ>\<^sub>c \<langle>b,h\<rangle>"
            by (typecheck_cfuncs, smt b_def comp_associative2 left_coproj_cfunc_coprod)
          also have "... = eval_func A B \<circ>\<^sub>c distribute_left_left B (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>b,h\<rangle>"
            using L_def b_def comp_associative2 by (typecheck_cfuncs, fastforce)
          also have "... = eval_func A B \<circ>\<^sub>c \<langle>b, ab2\<rangle>"
            using b_def distribute_left_left_ap g_def by auto
          also have "... = eval_func A B \<circ>\<^sub>c (id B \<times>\<^sub>f ab2) \<circ>\<^sub>c \<langle>b, id(one)\<rangle>"
            using \<open>ab2 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> b_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs,auto)
          also have "... = eval_func A B \<circ>\<^sub>c (id\<^sub>c B \<times>\<^sub>f ab2) \<circ>\<^sub>c x"
            using b_def by blast
          also have "... = (eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab2) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, meson \<open>ab2 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> comp_associative2 x_type)
          then show "(eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab1) \<circ>\<^sub>c x = (eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab2) \<circ>\<^sub>c x" 
            using calculation by auto
        qed
      qed
    qed
    have right: "ac1 = ac2"
    proof(rule same_evals_equal[where Z = one, where X = A, where A = C])
      show "ac1 \<in>\<^sub>c A\<^bsup>C\<^esup>"
        by (simp add: f_def)
      show "ac2 \<in>\<^sub>c A\<^bsup>C\<^esup>"
        by (simp add: g_def)
      show "eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac1 = eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac2"
      proof(rule one_separator[where X = "C\<times>\<^sub>c one", where Y = A])
        show "eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac1 : C  \<times>\<^sub>c one \<rightarrow> A"
          using \<open>ac1 \<in>\<^sub>c A\<^bsup>C\<^esup>\<close> flat_type inv_transpose_func_def2 by auto
        show "eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac2 : C \<times>\<^sub>c one \<rightarrow> A"
          using \<open>ac2 \<in>\<^sub>c A\<^bsup>C\<^esup>\<close> flat_type inv_transpose_func_def2 by auto
        show "\<And>x. x \<in>\<^sub>c C \<times>\<^sub>c one \<Longrightarrow>
         (eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac1) \<circ>\<^sub>c x =  (eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac2) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c C \<times>\<^sub>c one"
          then obtain c where c_def: "c \<in>\<^sub>c C \<and> x = \<langle>c, id(one)\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique)
          then have rcoproj_c_type[type_rule]: "(right_coproj B C \<circ>\<^sub>c c) \<in>\<^sub>c (B \<Coprod> C)"
            using c_def by (typecheck_cfuncs, auto)
          have "(eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac1) \<circ>\<^sub>c x = eval_func A C \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f ac1) \<circ>\<^sub>c x"
            using \<open>ac1 \<in>\<^sub>c A\<^bsup>C\<^esup>\<close> comp_associative2 x_type by (typecheck_cfuncs, fastforce)
          also have "... = eval_func A C \<circ>\<^sub>c (id C \<times>\<^sub>f ac1) \<circ>\<^sub>c \<langle>c, id(one)\<rangle>"
            using c_def by auto
          also have "... = eval_func A C \<circ>\<^sub>c \<langle>c, ac1\<rangle>"
            using \<open>ac1 \<in>\<^sub>c A\<^bsup>C\<^esup>\<close> c_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs,auto)
          also have "... = eval_func A C \<circ>\<^sub>c distribute_left_right C (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>c,g\<rangle>"
            using c_def distribute_left_right_ap f_def by auto
          also have "... = R \<circ>\<^sub>c \<langle>c,g\<rangle>"
            using R_def c_def comp_associative2 by (typecheck_cfuncs, blast)
          also have  "... = ((L \<amalg> R) \<circ>\<^sub>c  right_coproj (B \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>))) \<circ>\<^sub>c \<langle>c,g\<rangle>"
            by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
          also have "... = (L \<amalg> R) \<circ>\<^sub>c  right_coproj (B \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c \<langle>c,g\<rangle>"
            using c_def comp_associative2 by (typecheck_cfuncs, fastforce)
          also have "... =  (L \<amalg> R) \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, g\<rangle>" 
            by (typecheck_cfuncs, simp add: c_def dist_prod_coprod_inv2_right_ap)
          also have "... = ((L \<amalg> R) \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, g\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = ((eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>)) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, g\<rangle>"
            by (typecheck_cfuncs, simp add: \<phi>_def transpose_func_def)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, g\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>(right_coproj B C \<circ>\<^sub>c c) \<circ>\<^sub>c id (one), g \<circ>\<^sub>c id (one)\<rangle>"
            using id_right_unit2 rcoproj_c_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c ((id(B \<Coprod> C) \<circ>\<^sub>c (right_coproj B C \<circ>\<^sub>c c))  \<times>\<^sub>f \<phi> \<circ>\<^sub>c g) \<circ>\<^sub>c  \<langle>id (one), id(one)\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod id_right_unit2 rcoproj_c_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c ((id(B \<Coprod> C) \<circ>\<^sub>c (right_coproj B C \<circ>\<^sub>c c))  \<times>\<^sub>f \<phi> \<circ>\<^sub>c h) \<circ>\<^sub>c  \<langle>id (one), id(one)\<rangle>"
            by (simp add: eqn)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>(right_coproj B C \<circ>\<^sub>c c) \<circ>\<^sub>c id (one), h \<circ>\<^sub>c id (one)\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod id_right_unit2 rcoproj_c_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, h\<rangle>"
            using id_right_unit2 rcoproj_c_type by (typecheck_cfuncs, auto)
          also have "... = ((eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>)) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, h\<rangle>"
            using comp_associative2 by (typecheck_cfuncs, blast)
          also have "... = ((L \<amalg> R) \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, h\<rangle>"
            by (typecheck_cfuncs, simp add: \<phi>_def transpose_func_def)
          also have "... = (L \<amalg> R) \<circ>\<^sub>c  dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c c, h\<rangle>" 
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... =  (L \<amalg> R) \<circ>\<^sub>c right_coproj (B \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C \<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c \<langle>c,h\<rangle>"
            by (typecheck_cfuncs, simp add: c_def dist_prod_coprod_inv2_right_ap)
          also have "... = R \<circ>\<^sub>c \<langle>c,h\<rangle>"
            by (typecheck_cfuncs, smt c_def comp_associative2 right_coproj_cfunc_coprod)
          also have "... = eval_func A C \<circ>\<^sub>c distribute_left_right C (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>c,h\<rangle>"
            using R_def c_def comp_associative2 by (typecheck_cfuncs, fastforce)
          also have "... = eval_func A C \<circ>\<^sub>c \<langle>c, ac2\<rangle>"
            using c_def distribute_left_right_ap g_def by auto
          also have "... = eval_func A C \<circ>\<^sub>c (id C \<times>\<^sub>f ac2) \<circ>\<^sub>c \<langle>c, id(one)\<rangle>"
            using \<open>ac2 \<in>\<^sub>c A\<^bsup>C\<^esup>\<close> c_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs,auto)
          also have "... = eval_func A C \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f ac2) \<circ>\<^sub>c x"
            using c_def by blast
          also have "... = (eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac2) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, meson \<open>ac2 \<in>\<^sub>c A\<^bsup>C\<^esup>\<close> comp_associative2 x_type)
          then show "(eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac1) \<circ>\<^sub>c x = (eval_func A C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f ac2) \<circ>\<^sub>c x" 
            using calculation by auto
        qed
      qed
    qed
    show "g = h"
      by (simp add: f_def g_def left right)
  qed
  then have "monomorphism(\<phi>)"
    using injective_imp_monomorphism by auto
  have "surjective(\<phi>)"
    unfolding  surjective_def
  proof(safe)
    fix y 
    assume "y \<in>\<^sub>c codomain \<phi>" then have y_type[type_rule]: "y \<in>\<^sub>c A\<^bsup>(B \<Coprod> C)\<^esup>"
      using \<phi>_type cfunc_type_def by auto
    have Left_type[type_rule]: "(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> \<in>\<^sub>c (A\<^bsup>B\<^esup>)"
      by typecheck_cfuncs
    have Right_type[type_rule]: "(eval_func A (B \<Coprod> C) \<circ>\<^sub>c
                        \<langle>right_coproj B C \<circ>\<^sub>c
                         left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> \<in>\<^sub>c (A\<^bsup>C\<^esup>)"
      by typecheck_cfuncs
    show "\<exists>x. x \<in>\<^sub>c domain \<phi> \<and> \<phi> \<circ>\<^sub>c x = y"
    proof(rule_tac x="\<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one, y \<circ>\<^sub>c \<beta>\<^bsub>B\<times>\<^sub>cone\<^esub>\<rangle> )\<^sup>\<sharp> , 
                       (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C\<times>\<^sub>cone\<^esub>\<rangle> )\<^sup>\<sharp>\<rangle>" in exI,auto)
      show "\<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle> \<in>\<^sub>c  domain \<phi>"
        using cfunc_type_def by (typecheck_cfuncs, auto) 
      show "\<phi> \<circ>\<^sub>c \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>cleft_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,(eval_func A (B \<Coprod> C) \<circ>\<^sub>c
                                          \<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle> =  y"
      proof(rule same_evals_equal[where Z = one, where X = A, where A = "(B \<Coprod> C)"])
        show [type_rule]: "\<phi> \<circ>\<^sub>c \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                                 (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle> \<in>\<^sub>c A\<^bsup>(B \<Coprod> C)\<^esup>"
          by typecheck_cfuncs
        show "y \<in>\<^sub>c A\<^bsup>(B \<Coprod> C)\<^esup>"
          by typecheck_cfuncs
        show "eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f 
            (\<phi> \<circ>\<^sub>c\<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>cleft_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                 (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>)=
                  eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f y"
        proof(rule one_separator[where X = "(B \<Coprod> C) \<times>\<^sub>c one", where Y = A])
          show "eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f \<phi> \<circ>\<^sub>c \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>cone\<^esub>\<rangle>)\<^sup>\<sharp>,(eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle> : (B \<Coprod> C) \<times>\<^sub>c one \<rightarrow> A"
            by  typecheck_cfuncs
          show "eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f y : (B \<Coprod> C) \<times>\<^sub>c one \<rightarrow> A"
            by typecheck_cfuncs
          show "\<And>x. x \<in>\<^sub>c (B \<Coprod> C) \<times>\<^sub>c one \<Longrightarrow>
               (eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f \<phi> \<circ>\<^sub>c
              \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
               (eval_func A (B \<Coprod> C) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c x =
               (eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f y) \<circ>\<^sub>c x"
          proof - 
            fix x 
            assume x_type[type_rule]: "x \<in>\<^sub>c (B \<Coprod> C) \<times>\<^sub>c one"
            then obtain bc where x_def: "bc \<in>\<^sub>c (B \<Coprod> C) \<and> x = \<langle>bc, id(one)\<rangle>"
              by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique)
            have " (eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f \<phi> \<circ>\<^sub>c
                  \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                   (eval_func A (B \<Coprod> C) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c x = 
                    eval_func A (B \<Coprod> C) \<circ>\<^sub>c (id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f  \<phi> )  \<circ>\<^sub>c 
  (id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B  one,y \<circ>\<^sub>c  \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                    (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>)\<circ>\<^sub>c x"
              using comp_associative2 identity_distributes_across_composition by (typecheck_cfuncs, auto)
            also have "... = ((L \<amalg> R)   \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c (id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f 
                  \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B  one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c  one\<^esub>\<rangle>)\<^sup>\<sharp>,
                   (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c x"
              by (typecheck_cfuncs, smt \<phi>_def comp_associative2 transpose_func_def)
            also have "... = (L \<amalg> R) \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c (id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f 
                  \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B  one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                  (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c \<langle>bc, id(one)\<rangle>"
                by (typecheck_cfuncs, smt comp_associative2 x_def)
            also have "... = (L \<amalg> R) \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)\<circ>\<^sub>c  \<langle>id\<^sub>c (B \<Coprod> C) \<circ>\<^sub>c bc,  
                 \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B  one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                  (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle> \<circ>\<^sub>c id(one)\<rangle>"
                using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
            also have "... = (L \<amalg> R) \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>bc,  \<langle>
                 (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B  one,y \<circ>\<^sub>c  \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                 (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle> \<rangle>"
                using id_left_unit2 id_right_unit2 x_def by (typecheck_cfuncs, auto)
            also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>bc, y\<rangle>"
  proof(cases "\<exists> b. b\<in>\<^sub>c B \<and> left_coproj B C \<circ>\<^sub>c b = bc")
    assume "\<exists>b. b \<in>\<^sub>c B \<and> left_coproj B C \<circ>\<^sub>c b = bc"
    then obtain b where b_def[type_rule]: "b \<in>\<^sub>c B \<and> left_coproj B C \<circ>\<^sub>c b = bc"
      by blast
    have "L \<amalg> R \<circ>\<^sub>c    dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>bc,
        \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B   one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
         (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle> =
          L \<amalg> R \<circ>\<^sub>c left_coproj (B\<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C\<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c \<langle>b,\<langle>
         (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B  one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
          (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle>"
      using b_def dist_prod_coprod_inv2_left_ap by (typecheck_cfuncs, auto)
    also have "... = L \<circ>\<^sub>c \<langle>b,\<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>c  left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                             (eval_func A (B \<Coprod> C) \<circ>\<^sub>c  \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle>"
      by (typecheck_cfuncs,smt b_def comp_associative2 left_coproj_cfunc_coprod)
    also have "... = eval_func A B \<circ>\<^sub>c distribute_left_left B (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>b,
                   \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                    (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt L_def b_def comp_associative2)
    also have "... = eval_func A B \<circ>\<^sub>c \<langle>b, (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> \<rangle>"
      using b_def distribute_left_left_ap by (typecheck_cfuncs, auto)
    also have "... = eval_func A B \<circ>\<^sub>c \<langle>id B \<circ>\<^sub>c b, (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>cleft_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c id(one)\<rangle>"
      using b_def id_left_unit2 id_right_unit2 by (typecheck_cfuncs,auto)
    also have "... = eval_func A B \<circ>\<^sub>c (id B \<times>\<^sub>f (eval_func A (B \<Coprod> C) \<circ>\<^sub>c  \<langle>left_coproj B C \<circ>\<^sub>cleft_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>b,id(one)\<rangle>"
      using b_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
    also have "... = (eval_func A (B \<Coprod> C)\<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>) \<circ>\<^sub>c \<langle>b,id(one)\<rangle>"
      by (typecheck_cfuncs, smt b_def comp_associative2 transpose_func_def)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle> \<circ>\<^sub>c \<langle>b,id(one)\<rangle>"
      using b_def cfunc_type_def comp_associative by (typecheck_cfuncs, auto)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one \<circ>\<^sub>c \<langle>b,id(one)\<rangle> ,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub> \<circ>\<^sub>c \<langle>b,id(one)\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt b_def cfunc_prod_comp cfunc_type_def comp_associative)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c b ,y \<circ>\<^sub>c id(one)\<rangle>"
      by (typecheck_cfuncs, metis b_def left_cart_proj_cfunc_prod one_unique_element)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>bc, y\<rangle>"
      by (typecheck_cfuncs, simp add: b_def id_right_unit2)
    then show ?thesis
      by (simp add: calculation)
  next
    assume "\<nexists>b. b \<in>\<^sub>c B \<and> left_coproj B C \<circ>\<^sub>c b = bc"
    then obtain c where c_def[type_rule]: "c \<in>\<^sub>c C \<and> right_coproj B C \<circ>\<^sub>c c = bc"
      using coprojs_jointly_surj x_def by blast
    have "L \<amalg> R \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>) \<circ>\<^sub>c \<langle>bc,
          \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
           (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c  left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle> =
          L \<amalg> R \<circ>\<^sub>c right_coproj (B\<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) (C\<times>\<^sub>c (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>)) \<circ>\<^sub>c \<langle>c,
          \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c  one\<^esub>\<rangle>)\<^sup>\<sharp>,
           (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle>"
      using c_def dist_prod_coprod_inv2_right_ap by (typecheck_cfuncs, auto)
    also have "... = R \<circ>\<^sub>c \<langle>c,\<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                             (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle>"
      by (typecheck_cfuncs,smt c_def comp_associative2 right_coproj_cfunc_coprod)
    also have "... = eval_func A C \<circ>\<^sub>c distribute_left_right C (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>)\<circ>\<^sub>c \<langle>c,
                    \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,
                     (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt R_def c_def comp_associative2)
    also have "... = eval_func A C \<circ>\<^sub>c \<langle>c, (eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>"
      using c_def distribute_left_right_ap by (typecheck_cfuncs, auto)
    also have "... = eval_func A C \<circ>\<^sub>c\<langle>id C \<circ>\<^sub>c c, (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c id(one)\<rangle>"
      using c_def id_left_unit2 id_right_unit2 by (typecheck_cfuncs,auto)
    also have "... = eval_func A C \<circ>\<^sub>c(id C \<times>\<^sub>f (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>c,id(one)\<rangle>"
      using c_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
    also have "... = (eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>) \<circ>\<^sub>c \<langle>c,id(one)\<rangle>"
      by (typecheck_cfuncs, smt c_def comp_associative2 transpose_func_def)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle> \<circ>\<^sub>c \<langle>c,id(one)\<rangle>"
      using c_def cfunc_type_def comp_associative by (typecheck_cfuncs, auto)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>cleft_cart_proj C one \<circ>\<^sub>c \<langle>c,id(one)\<rangle> ,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub> \<circ>\<^sub>c \<langle>c,id(one)\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt c_def cfunc_prod_comp cfunc_type_def comp_associative)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c\<langle>right_coproj B C \<circ>\<^sub>c c ,y \<circ>\<^sub>c id(one)\<rangle>"
      by (typecheck_cfuncs, metis c_def left_cart_proj_cfunc_prod one_unique_element)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>bc, y\<rangle>"
      by (typecheck_cfuncs, simp add: c_def id_right_unit2)
    then show ?thesis
      by (simp add: calculation)
   qed
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>id\<^sub>c (B \<Coprod> C) \<circ>\<^sub>c bc, y \<circ>\<^sub>c id(one)\<rangle>"
      by (typecheck_cfuncs, metis cfunc_type_def id_left_unit id_right_unit2 x_def)
    also have "... = eval_func A (B \<Coprod> C) \<circ>\<^sub>c (id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>bc, id(one)\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
    also have "... = (eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f y) \<circ>\<^sub>c x"
      using comp_associative2 x_def by (typecheck_cfuncs, blast)
    then show "(eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f \<phi> \<circ>\<^sub>c \<langle>(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>left_coproj B C \<circ>\<^sub>c left_cart_proj B one,y \<circ>\<^sub>c \<beta>\<^bsub>B \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>,(eval_func A (B \<Coprod> C) \<circ>\<^sub>c \<langle>right_coproj B C \<circ>\<^sub>c left_cart_proj C  one,y \<circ>\<^sub>c \<beta>\<^bsub>C \<times>\<^sub>c one\<^esub>\<rangle>)\<^sup>\<sharp>\<rangle>) \<circ>\<^sub>c  x = (eval_func A (B \<Coprod> C) \<circ>\<^sub>c id\<^sub>c (B \<Coprod> C) \<times>\<^sub>f y) \<circ>\<^sub>c x"
      by (simp add: calculation)
     qed
    qed
   qed
  qed
 qed
  then have "epimorphism(\<phi>)"
    by (simp add: surjective_is_epimorphism)
  then have "isomorphism(\<phi>)"
    by (simp add: \<open>monomorphism \<phi>\<close> epi_mon_is_iso)
  then show ?thesis
    using \<phi>_type is_isomorphic_def isomorphic_is_symmetric by blast
qed


(*   This is also proved in countable. Is it a new proof?  Is the injection the same?
lemma prod_leq_exp:
  assumes "\<not>(Y \<cong> one)"
  shows "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
proof(cases "nonempty Y")
  case True
  obtain y0 y1 where 
    y0_type[type_rule]: "y0 \<in>\<^sub>c Y" and
    y1_type[type_rule]: "y1 \<in>\<^sub>c Y" and
    distinct_y: "y0 \<noteq> y1"
    by (meson assms True nonempty_def single_elem_iso_one)
  obtain m where m_def:
    "m = (((y0 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj \<Omega> one)
            \<amalg> (((y0\<^sup>c \<circ>\<^sub>c right_cart_proj one (Y \<setminus> (one, y0))) \<amalg> (y0 \<circ>\<^sub>c left_cart_proj one (Y \<setminus> (one, y0))))
                \<circ>\<^sub>c dist_prod_coprod_inv2 one one (Y \<setminus> (one, y0))
                \<circ>\<^sub>c (case_bool \<times>\<^sub>f id (Y \<setminus> (one, y0))))
          \<circ>\<^sub>c dist_prod_coprod_inv \<Omega> one (Y \<setminus> (one, y0))
          \<circ>\<^sub>c (eq_pred X \<times>\<^sub>f try_cast y0)
          \<circ>\<^sub>c associate_left X X Y)\<^sup>\<sharp>"
    by blast
  have m_type[type_rule]: "m : (X \<times>\<^sub>c Y) \<rightarrow> Y\<^bsup>X\<^esup>"
    unfolding m_def using y0_type y1_type element_monomorphism  by (typecheck_cfuncs, blast)
  have "injective m"
  proof(unfold injective_def, auto)
    fix a b
    assume a_type[type_rule]: "a \<in>\<^sub>c domain m"
    assume b_type[type_rule]: "b \<in>\<^sub>c domain m"
    assume eql: "m \<circ>\<^sub>c a = m \<circ>\<^sub>c b"
    
    obtain u1 and v1 where u1_type[type_rule]: "u1 \<in>\<^sub>c X" and
                           v1_type[type_rule]: "v1 \<in>\<^sub>c Y" and 
                           a_def: "a = \<langle>u1,v1\<rangle>"
      by (typecheck_cfuncs, metis cart_prod_decomp cfunc_type_def m_type)
    obtain u2 and v2 where u2_type[type_rule]: "u2 \<in>\<^sub>c X" and
                           v2_type[type_rule]: "v2 \<in>\<^sub>c Y" and 
                           a_def: "b = \<langle>u2,v2\<rangle>"
      by (typecheck_cfuncs, metis cart_prod_decomp cfunc_type_def m_type)  
    
    show "a = b"
    proof(cases "v1 = y0")
      case True
      have "
      
*)

end