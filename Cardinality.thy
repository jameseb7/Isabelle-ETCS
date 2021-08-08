theory Cardinality
  imports ETCS_Axioms
begin

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

      show "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
        dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
        swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup>"
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
          show "eval_func A X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f g = eval_func A X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f h"
          proof (typecheck_cfuncs, rule one_separator[where X="X \<times>\<^sub>c Z", where Y="A"], auto)
            fix xz
            assume xz_type[type_rule]: "xz \<in>\<^sub>c X \<times>\<^sub>c Z"
            have "((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c g)) \<circ>\<^sub>c xz  = 
                  ((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c h)) \<circ>\<^sub>c xz"
              using eq by auto
            then have "((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f g) \<circ>\<^sub>c xz  = 
                  ((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f h) \<circ>\<^sub>c xz"
              by (typecheck_cfuncs, smt comp_associative2 eq inv_transpose_func_def2 inv_transpose_of_composition)
            then have "(m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f g) \<circ>\<^sub>c xz  = (m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f h) \<circ>\<^sub>c xz"
              by (smt comp_type eval_func_type m_def(1) transpose_func_def)
            then have "m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g) \<circ>\<^sub>c xz)  = m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h) \<circ>\<^sub>c xz)"
              by (typecheck_cfuncs, smt comp_associative2)
            then have "eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g) \<circ>\<^sub>c xz = eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h) \<circ>\<^sub>c xz"
              using m_def monomorphism_def3 by (typecheck_cfuncs, blast)
            then show "(eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g)) \<circ>\<^sub>c xz = (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h)) \<circ>\<^sub>c xz"
              by (typecheck_cfuncs, smt comp_associative2)
        qed
      qed
    qed
  qed
qed


lemma leq_transitive:
  assumes "A \<le>\<^sub>c B"
  assumes "B \<le>\<^sub>c C"
  shows   "A \<le>\<^sub>c C"
  by (typecheck_cfuncs, metis (full_types) assms cfunc_type_def comp_type composition_of_monic_pair_is_monic is_smaller_than_def)




lemma exp_set_smaller_than3:
  assumes "A \<le>\<^sub>c B"
  assumes "X \<le>\<^sub>c Y"
  assumes "nonempty(X)"
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
proof - 
  have leq1: "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
    using assms(1) assms(3) exp_set_smaller_than1 by blast
  have leq2: "X\<^bsup>B\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    by (simp add: assms(2) exp_set_smaller_than2)
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    using leq1 leq2 leq_transitive by blast
qed






end