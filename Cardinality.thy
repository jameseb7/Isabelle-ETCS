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


lemma sets_squared:
  "A\<^bsup>\<Omega>\<^esup> \<cong> A \<times>\<^sub>c A "
proof - 
  obtain \<phi> where \<phi>_def: "\<phi> = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle>"
    by simp
  have type1[type_rule]: "\<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c (A\<^bsup>\<Omega>\<^esup>)"
    by typecheck_cfuncs
  have type2[type_rule]: "\<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c (A\<^bsup>\<Omega>\<^esup>)"
    by typecheck_cfuncs
  have \<phi>_type[type_rule]: "\<phi> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A \<times>\<^sub>c A"
    unfolding \<phi>_def by typecheck_cfuncs
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
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , g \<rangle> \<rangle>"
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
     
    
      obtain f where f_def: "f = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj \<Omega> one)\<^sup>\<sharp>"
        by simp
      then have f_type[type_rule]: "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
       using case_bool_type aua cfunc_type_def codomain_comp domain_comp f_def left_cart_proj_type transpose_func_type by auto
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
  "A\<^bsup>(B \<Coprod> C)\<^esup> \<cong> A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup> "
proof -
  obtain \<phi> where \<phi>_def:
    "\<phi> = 
    (((eval_func A B \<circ>\<^sub>c distribute_left_left B (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>))
        \<amalg>
     (eval_func A C \<circ>\<^sub>c distribute_left_right C (A\<^bsup>B\<^esup>) (A\<^bsup>C\<^esup>)))
      \<circ>\<^sub>c dist_prod_coprod_inv2 B C (A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>))\<^sup>\<sharp>"
    by auto

  have \<phi>_type[type_rule]: "\<phi> : A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup> \<rightarrow> A\<^bsup>(B \<Coprod> C)\<^esup>"
    unfolding \<phi>_def by typecheck_cfuncs
  have "injective(\<phi>)"
    unfolding  injective_def
  proof(safe)
    fix x y 
    assume "x \<in>\<^sub>c domain \<phi>" then have x_type[type_rule]: "x \<in>\<^sub>c A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>"
      using \<phi>_type cfunc_type_def by auto
    assume "y \<in>\<^sub>c domain \<phi>" then have y_type[type_rule]: "y \<in>\<^sub>c A\<^bsup>B\<^esup> \<times>\<^sub>c A\<^bsup>C\<^esup>"
      using \<phi>_type cfunc_type_def by auto
    assume eqn: "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c y"
    obtain ab1 and ac1 where x_def: "ab1 \<in>\<^sub>c A\<^bsup>B\<^esup> \<and> ac1 \<in>\<^sub>c A\<^bsup>C\<^esup> \<and> x = \<langle>ab1,ac1\<rangle>"
        using cart_prod_decomp x_type by blast
    obtain ab2 and ac2 where y_def: "ab2 \<in>\<^sub>c A\<^bsup>B\<^esup> \<and> ac2 \<in>\<^sub>c A\<^bsup>C\<^esup> \<and> y = \<langle>ab2,ac2\<rangle>"
        using cart_prod_decomp y_type by blast
    have "ab1 = ab2"
    proof(rule same_evals_equal[where Z = one, where X = A, where A = B])
      show "ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>"
        by (simp add: x_def)
      show "ab2 \<in>\<^sub>c A\<^bsup>B\<^esup>"
        by (simp add: y_def)
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

          have eqn1: "(eval_func A (B \<Coprod> C)) \<circ>\<^sub>c (id(B \<Coprod> C) \<times>\<^sub>f \<phi>) \<circ>\<^sub>c \<langle>left_coproj B C b), x\<rangle> 



(*



          have "(eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ab1) \<circ>\<^sub>c x = 
                 eval_func A B \<circ>\<^sub>c ((id\<^sub>c B \<times>\<^sub>f ab1) \<circ>\<^sub>c x)"
            using \<open>ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> comp_associative2 x_type by (typecheck_cfuncs, fastforce)
          also have "... = eval_func A B \<circ>\<^sub>c \<langle>id\<^sub>c B \<circ>\<^sub>c b, ab1 \<circ>\<^sub>c id(one)\<rangle>"
            using \<open>ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> b_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
          also have "... = eval_func A B \<circ>\<^sub>c \<langle>b, ab1\<rangle>"
            using \<open>ab1 \<in>\<^sub>c A\<^bsup>B\<^esup>\<close> b_def id_left_unit2 id_right_unit2 by auto
          also have "... = eval_func A B \<circ>\<^sub>c \<langle>b, ab2\<rangle>"
            oops
*)

      
      
      
        



lemma smaller_than_N_finite:
  assumes "X \<le>\<^sub>c \<nat>\<^sub>c"
  assumes "\<not>(\<exists>s. (s: X \<rightarrow> \<nat>\<^sub>c \<and> surjective(s)))"
  shows "is_finite(X)"
  oops



end