theory ETCS_Ordinal_Inequalities
  imports ETCS_Exp ETCS_Comparison
begin

lemma
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle>,
        leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c c  = \<t>"
proof(etcs_rule nat_induction)
  show "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                    leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero =  \<t>"
  proof(rule ccontr)
    assume "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                        leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero \<noteq>  \<t>"
    then have "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                        leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero =  \<f>"
      using  true_false_only_truth_values by (typecheck_cfuncs, blast)  
    then have "IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> ,
                          leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c zero =  \<f>"
      using  comp_associative2 by (typecheck_cfuncs, force)
    then have "IMPLIES \<circ>\<^sub>c \<langle>(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c zero ,
                           (leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero\<rangle>  =  \<f>"
      by (typecheck_cfuncs, metis cfunc_prod_comp)
    then have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t> \<and>
                           (leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero  =  \<f>"
      using IMPLIES_false_is_true_false  by (typecheck_cfuncs, blast)
    then have "(leq \<circ>\<^sub>c (\<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c zero) = \<t>) \<and>
                            leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero  =  \<f>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then have "(leq \<circ>\<^sub>c (\<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>)  \<circ>\<^sub>c zero,(exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c zero\<rangle>) = \<t>) \<and>
                            leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero  =  \<f>"
      using  cfunc_prod_comp by (typecheck_cfuncs, auto)
    then have "(leq \<circ>\<^sub>c (\<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>  \<circ>\<^sub>c zero, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c zero\<rangle>) = \<t>) \<and>
                            leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero ,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero\<rangle>   =  \<f>"
      by (typecheck_cfuncs, smt (z3)  cfunc_prod_comp comp_associative2)
    then have "(leq \<circ>\<^sub>c (\<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)  \<circ>\<^sub>c zero,successor  \<circ>\<^sub>c zero\<rangle> , exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)  \<circ>\<^sub>c zero,successor  \<circ>\<^sub>c zero\<rangle>\<rangle>) = \<t>) \<and>
                            leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero ,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero\<rangle>   =  \<f>"
      using  cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
    then have "(leq \<circ>\<^sub>c (\<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c zero,successor  \<circ>\<^sub>c zero\<rangle> , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c zero,successor  \<circ>\<^sub>c zero\<rangle>\<rangle>) = \<t>) \<and>
                            leq \<circ>\<^sub>c \<langle>a ,b \<rangle>   =  \<f>"
      by (typecheck_cfuncs, smt (z3)  beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 terminal_func_comp)
    then have "(leq \<circ>\<^sub>c (\<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,successor  \<circ>\<^sub>c zero\<rangle> , exp_uncurried \<circ>\<^sub>c \<langle>b ,successor  \<circ>\<^sub>c zero\<rangle>\<rangle>) = \<t>) \<and>
                            leq \<circ>\<^sub>c \<langle>a ,b \<rangle>   =  \<f>"
      by (typecheck_cfuncs, metis id_right_unit2 terminal_func_comp_elem)
    then have "(leq \<circ>\<^sub>c \<langle>a ,b \<rangle>   = \<t>) \<and>  (leq \<circ>\<^sub>c \<langle>a ,b \<rangle>   =  \<f>)"
      using  exp_def exp_respects_one_right by (typecheck_cfuncs, force)
    then show False
      using true_false_distinct by auto
  qed
  
  show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
        (IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                    leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>
    \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                    leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n =\<t>"    
  proof - 
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume ind_hyp: "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                    leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
    then show "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                    leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n =\<t>"
      oops






(*


lemma exp_order_preserving_converse0:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" 
  assumes "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" 
  shows "leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" 
proof(rule nat_induction)

  show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c zero =
    (leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
  proof -
    have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c zero
        = leq \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c zero, (exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c zero\<rangle>"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)  \<circ>\<^sub>c zero,successor  \<circ>\<^sub>c zero\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero,successor \<circ>\<^sub>c zero\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    also have "... = leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)  \<circ>\<^sub>c zero, (b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero\<rangle>"
      by (typecheck_cfuncs, smt exp_def exp_respects_one_right)
    also have "... = (leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    then show ?thesis
      using calculation by auto
  qed

  show "(leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
  proof -
    have "(leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor
        = leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor, (b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor\<rangle>"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    also have "... = leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 terminal_func_comp)
    also have "... = id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      using id_left_unit2 by (typecheck_cfuncs, presburger)
    then show ?thesis
      using calculation by auto
  qed

  show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c successor
      = id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>"
  proof -
    have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c successor
        = leq \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor, (exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor\<rangle>"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor, successor \<circ>\<^sub>c successor\<rangle>, 
                            exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor, successor \<circ>\<^sub>c successor\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor \<circ>\<^sub>c successor\<rangle>, 
                            exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor \<circ>\<^sub>c successor\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 terminal_func_comp)
    also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>, 
                            exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>\<rangle>"
    proof (rule one_separator[where X="\<nat>\<^sub>c", where Y=\<Omega>])
      show "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
    next
      fix n
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>,
                    exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>\<rangle>) \<circ>\<^sub>c n
          = (leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c n"
      proof -
        have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>,
                    exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>\<rangle>) \<circ>\<^sub>c n
            = leq \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>) \<circ>\<^sub>c n,
                     (exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>) \<circ>\<^sub>c n\<rangle>"
          by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
        also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n, (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c n\<rangle>,
                                exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n, (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c n\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
        also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>,
                                exp_uncurried \<circ>\<^sub>c \<langle>b, successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt (z3) beta_N_succ_mEqs_Id1 cfunc_type_def comp_associative id_right_unit2 terminal_func_comp)
        also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle>,
                                exp_uncurried \<circ>\<^sub>c \<langle>b, successor \<circ>\<^sub>c n\<rangle>\<rangle>"
        proof (cases "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a, successor \<circ>\<^sub>c n\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b, successor \<circ>\<^sub>c n\<rangle>\<rangle> = \<t>")
          assume leq_exp_true: "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c n\<rangle>\<rangle> = \<t>"

          show "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>\<rangle>
              = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c n\<rangle>\<rangle>"
          proof (cases "leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t>")
            assume leq_true: "leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t>"

            have "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> (exp_uncurried \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle>), b \<cdot>\<^sub>\<nat> (exp_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c n\<rangle>)\<rangle> = \<t>"
              by (typecheck_cfuncs, meson leq_exp_true leq_true mult_monotonic)
            then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>\<rangle> = \<t>"
              by (typecheck_cfuncs, metis exp_def exp_respects_successor)
            then show "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>\<rangle>
                     = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c n\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c n\<rangle>\<rangle>"
              by (simp add: leq_exp_true)
          next
            assume "leq \<circ>\<^sub>c \<langle>a,b\<rangle> \<noteq> \<t>"
            then have leq_true: "leq \<circ>\<^sub>c \<langle>b,a\<rangle> = \<t>"
              by (meson a_type b_type lqe_connexity)
 *)             

lemma exp_order_preserving_converse0:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" 
  (*assumes "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"*)
  shows "IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  proof(rule natural_number_object_func_unique[where X = "\<Omega>", where f = "id \<Omega>" ])
    show main_type[type_rule]: "IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
    proof - 
      have "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero = 
             IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c zero"
        using assms comp_associative2 by (typecheck_cfuncs, force)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>  ,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<rangle> \<circ>\<^sub>c zero,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>  \<circ>\<^sub>c zero\<rangle>"
        using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<circ>\<^sub>c zero  ,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c zero\<rangle> ,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>  \<circ>\<^sub>c zero\<rangle>"
        using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero,successor \<circ>\<^sub>c zero\<rangle>  ,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c zero,successor \<circ>\<^sub>c zero\<rangle> \<rangle> ,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c zero,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c zero\<rangle>  \<rangle>"
        using assms cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a ,successor \<circ>\<^sub>c zero\<rangle>  ,exp_uncurried \<circ>\<^sub>c \<langle>b ,successor \<circ>\<^sub>c zero\<rangle> \<rangle> ,leq \<circ>\<^sub>c \<langle>a ,b \<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>a  ,b \<rangle> ,leq \<circ>\<^sub>c \<langle>a ,b \<rangle>\<rangle>"
        using assms exp_def exp_respects_one_right by (typecheck_cfuncs, presburger)
      also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
        using assms  by (typecheck_cfuncs,smt (z3) IMPLIES_false_is_true_false beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 successor_type terminal_func_comp true_false_only_truth_values)
      then show ?thesis
        by (simp add: calculation)
    qed
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
    show "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor
      =  id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>"
    proof -
      have "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                        leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor
          = IMPLIES \<circ>\<^sub>c (\<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                        leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c successor)"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c successor,
                                  (leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_prod_comp)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c successor,
                                  leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor,(exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor\<rangle>,
                                  leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor\<rangle>\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_prod_comp)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c successor,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c successor\<rangle>,
                                  leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor\<rangle>\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,successor \<circ>\<^sub>c successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,successor \<circ>\<^sub>c successor\<rangle>\<rangle>,
                                  leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor\<rangle>\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_prod_comp)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,successor \<circ>\<^sub>c successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,successor \<circ>\<^sub>c successor\<rangle>\<rangle>,
                                  leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor\<rangle>\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor \<circ>\<^sub>c successor\<rangle>\<rangle>,
                                  leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>"
        by (typecheck_cfuncs, metis terminal_func_unique)
    
    proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<Omega>"])
      show "(IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "\<And>c. c \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c c =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c c"
      proof - 
        fix c
        assume c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
        have  "((IMPLIES \<circ>\<^sub>c
           \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c
          successor) \<circ>\<^sub>c
         c"

        (*have "(id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c c = 
              (id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c c"
          using assms apply typecheck_cfuncs
        also have "... = IMPLIES \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c c"
          using assms by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2)
        also have "... = IMPLIES \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c c,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c c,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c c\<rangle>\<rangle>"
          using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
        also have "... = IMPLIES \<circ>\<^sub>c \<langle>\<t>,leq \<circ>\<^sub>c \<langle>a, b\<rangle>\<rangle>"
          using assms by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
        also have "... = IMPLIES \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c c),leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c c),b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c c)\<rangle>\<rangle>"
          using assms by (typecheck_cfuncs, simp add: beta_N_succ_mEqs_Id1 id_right_unit2)
        also have "... = IMPLIES \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c c)"
          using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
        also have "... = ((IMPLIES \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c c"
          using assms by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
        also have "... = ((IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c c"
          using assms(3) by presburger
        then show "((IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c c =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c c"
          using calculation by auto
      qed
    qed
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
qed*)

(*
  have "\<And> c. (c \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ> c = \<t>)"



  proof(cases "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>")
    assume "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"

    show ?thesis
    proof(rule one_separator[where X ="\<nat>\<^sub>c", where Y = \<Omega>] )
      show "leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        using assms by typecheck_cfuncs
      show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
      proof - 
        fix c
        assume c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"

        then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>  \<circ>\<^sub>c c  = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c c"
          using assms by (typecheck_cfuncs, metis assms(3) cfunc_type_def comp_associative)
        then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>  \<circ>\<^sub>c c  = \<t>"
          by (typecheck_cfuncs, metis id_right_unit2 id_type terminal_func_comp terminal_func_unique)



        have "IMPLIES \<circ>\<^sub>c \<langle> leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<rangle> \<circ>\<^sub>c c = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c c"
          using assms by (typecheck_cfuncs, metis cfunc_type_def comp_associative main_result)
        then have "IMPLIES \<circ>\<^sub>c \<langle> leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle> \<circ>\<^sub>c c,
                                leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c \<rangle>  = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c c"
          using assms by (typecheck_cfuncs,  smt (z3) \<open>IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c c = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c c\<close> \<open>\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<close> \<open>leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<close> assms(3) cfunc_prod_comp comp_associative2)
        then have "IMPLIES \<circ>\<^sub>c \<langle> \<t>,  leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c \<rangle>  = \<t>"
          using assms by (metis \<open>IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c c,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c c\<close> \<open>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c c = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c c\<close> \<open>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c c = \<t>\<close>)
        then have "leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c = \<t>"
          using assms by (typecheck_cfuncs, metis IMPLIES_true_false_is_false \<open>IMPLIES \<circ>\<^sub>c \<langle>\<t>,leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c\<rangle> = \<t>\<close> true_false_only_truth_values)
        then show "(leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c c = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c c"
          using assms by (typecheck_cfuncs, metis \<open>leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c = \<t>\<close> cfunc_type_def comp_associative id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
      qed
    qed
  next
    assume "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<noteq> \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    then obtain c where c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c" and c_seps: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c c =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c c"
      by (meson assms(3))

  qed
qed
*)

*)

(*
lemma exp_order_preserving_converse:
  assumes a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes c_nonzero: "c \<noteq> zero"
  sorry

*)

(*
lemma exp_order_preserving_converse:
  assumes a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes c_nonzero: "c \<noteq> zero"
  assumes "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a  , c\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b , c\<rangle>\<rangle> = \<t> "
  shows "leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t>"
proof(rule nat_induction)
*)


lemma exp_order_preserving1:
  assumes a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes leq: "leq \<circ>\<^sub>c \<langle>a , b\<rangle> = \<t>"
  shows "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> c , b ^\<^sub>\<nat> c\<rangle> = \<t>"
proof(cases "a = b")
  show "a = b \<Longrightarrow> leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> c,b ^\<^sub>\<nat> c\<rangle> = \<t>"
    by (meson b_type c_type exp_closure lqe_connexity)
  show "a \<noteq> b \<Longrightarrow> leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> c,b ^\<^sub>\<nat> c\<rangle> = \<t>"
  proof - 
    assume "a \<noteq> b"
    show "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> c,b ^\<^sub>\<nat> c\<rangle> = \<t>"
    proof(rule ccontr)
      assume not_leq: "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> c,b ^\<^sub>\<nat> c\<rangle> \<noteq> \<t>"
      then have "leq \<circ>\<^sub>c \<langle>b ^\<^sub>\<nat> c,a ^\<^sub>\<nat> c\<rangle> = \<t>"
        by (meson a_type b_type c_type exp_closure lqe_connexity)
      then have "leq \<circ>\<^sub>c \<langle>b, a\<rangle> = \<t>"
        by (metis not_leq a_type b_type c_type exp_order_preserving_converse exp_respects_Zero_Left)
      then have "a = b"
        by (simp add: a_type b_type leq lqe_antisymmetry)
      then show False
        using \<open>a \<noteq> b\<close> by simp
    qed
  qed
qed







(*  Original proof of exp_order_preserving1
proof-
  obtain \<phi> where \<phi>_def: "\<phi> = leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)"
    by blast
  have exp_exp_dist_type: "(exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
    by typecheck_cfuncs
  have \<phi>_type: "\<phi> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
    using \<phi>_def comp_type exp_exp_dist_type leq_type by blast
  then have \<phi>_sharp_type: "\<phi>\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by typecheck_cfuncs

  have main_result: "\<phi>\<^sup>\<sharp> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>"
  proof(rule natural_number_object_func_unique[where X = "\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>", where f = "id(\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"])
    show "\<phi>\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by (simp add: \<phi>_sharp_type)
    show true_b_sharp_type: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show "id\<^sub>c (\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) : \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup> \<rightarrow> \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    
    show "\<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule same_evals_equal[where Z = one, where X = "\<Omega>", where A = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"])
      show phisharp_zero_type: "\<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        using \<phi>_sharp_type comp_type zero_type by auto
      show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        using comp_type true_b_sharp_type zero_type by blast
      show "eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (\<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero) =
            eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y="\<Omega>"])
        show "eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<Omega>"
          by (typecheck_cfuncs, simp add: phisharp_zero_type)
        show "eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
          obtain y where x_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and>  x = \<langle>y, id(one)\<rangle>"
            using cart_prod_decomp id_type one_unique_element x_type by blast
          obtain m n where y_def: "m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>m,n\<rangle>"
            using cart_prod_decomp x_def by blast
          have m0_type: "\<langle>m,zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type y_def zero_type)
          have n0_type: "\<langle>n,zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type y_def zero_type)
          have m0n0_type: "\<langle>\<langle>m,zero\<rangle>, \<langle>n,zero\<rangle>\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            using cfunc_prod_type m0_type n0_type by blast

          have "(eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
                ((eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp>) \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis \<phi>_sharp_type inv_transpose_func_def2 inv_transpose_of_composition)
          also have "... = (\<phi> \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero)) \<circ>\<^sub>c x"
            using \<phi>_type transpose_func_def by auto
          also have "... = \<phi> \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero) \<circ>\<^sub>c x"
            using \<phi>_type comp_associative2 x_type by (typecheck_cfuncs, auto) 
          also have "... = \<phi> \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>m,n\<rangle>,zero \<circ>\<^sub>c id(one)\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def y_def)
          also have "... = \<phi> \<circ>\<^sub>c \<langle>\<langle>m,n\<rangle>,zero\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 y_def)
          also have "... = (leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried)) \<circ>\<^sub>c ((distribute_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>m,n\<rangle>,zero\<rangle>)"
            by (typecheck_cfuncs, smt \<phi>_def comp_associative2 y_def)
          also have "... = (leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried)) \<circ>\<^sub>c \<langle>\<langle>m,zero\<rangle>,\<langle>n,zero\<rangle>\<rangle>"
            using distribute_right_ap y_def by (typecheck_cfuncs, auto)
          also have "... = leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>m,zero\<rangle>,\<langle>n,zero\<rangle>\<rangle>"
            using comp_associative2 m0n0_type by (typecheck_cfuncs, auto)
          also have "... = leq \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>m,zero\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>n,zero\<rangle>\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod m0_type n0_type by (typecheck_cfuncs, auto)
          also have "... = leq \<circ>\<^sub>c \<langle>m ^\<^sub>\<nat> zero, n ^\<^sub>\<nat> zero\<rangle>"
            by (simp add: exp_def)
          also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c zero\<rangle>"
            by (simp add: exp_respects_Zero_Left y_def)
          also have "... = \<t>"
            using lqe_connexity succ_n_type zero_type by blast
          also have "... = \<t> \<circ>\<^sub>c id(one)"
            using id_right_unit2 true_func_type by auto
          also have "... = \<t> \<circ>\<^sub>c (((\<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero)) \<circ>\<^sub>c x)"
            by (typecheck_cfuncs, metis terminal_func_unique x_type)
          also have "... = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero)) \<circ>\<^sub>c x"
            using comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = ((eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
          then show "(eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
                     (eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^esub>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
    show "\<phi>\<^sup>\<sharp> \<circ>\<^sub>c successor = id\<^sub>c (\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c \<phi>\<^sup>\<sharp>"
    proof(rule same_evals_equal[where Z ="\<nat>\<^sub>c", where X = "\<Omega>", where A = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"])
      show phi_succ_type: "\<phi>\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        using \<phi>_sharp_type by typecheck_cfuncs
      show "id\<^sub>c (\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c \<phi>\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        using \<phi>_sharp_type by typecheck_cfuncs
      show "eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c successor =
            eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c \<phi>\<^sup>\<sharp>"
      proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<Omega>"])
        show "eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
          using phi_succ_type by typecheck_cfuncs
        show "eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c \<phi>\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega>"
          using \<phi>_type by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c \<phi>\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          obtain y p where p_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> p \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>y,p\<rangle>"
            using cart_prod_decomp x_type by blast
          obtain m n where y_def: "m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>m,n\<rangle>"
            using cart_prod_decomp p_def by blast
          have mnsp_type: "\<langle>\<langle>m,n\<rangle>,successor \<circ>\<^sub>c p\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
            using p_def y_def by (typecheck_cfuncs, blast)
          have msp_type: "\<langle>m,successor \<circ>\<^sub>c p\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type p_def succ_n_type y_def)
          have nsp_type: "\<langle>n,successor \<circ>\<^sub>c p\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type p_def succ_n_type y_def)
          have mspnsp_type: "\<langle>\<langle>m,successor \<circ>\<^sub>c p\<rangle>,\<langle>n,successor \<circ>\<^sub>c p\<rangle>\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type msp_type nsp_type)
          have mp_type: "\<langle>m,p\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type p_def y_def)
          have np_type: "\<langle>n,p\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type p_def y_def)
          have mpnp_type: "\<langle>\<langle>m,p\<rangle>,\<langle>n,p\<rangle>\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type mp_type np_type)




          




          have "(eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
               ((eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f \<phi>\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fsuccessor)) \<circ>\<^sub>c x" 
            by (typecheck_cfuncs, metis \<phi>_sharp_type inv_transpose_func_def2 inv_transpose_of_composition)
          also have "... = (\<phi> \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fsuccessor)) \<circ>\<^sub>c x" 
            using \<phi>_type transpose_func_def by (typecheck_cfuncs, auto)
          also have "... = \<phi> \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fsuccessor) \<circ>\<^sub>c x)"
            using \<phi>_type comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = \<phi> \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>m,n\<rangle>,successor \<circ>\<^sub>c p\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod p_def y_def)
          also have "... = \<phi> \<circ>\<^sub>c \<langle>\<langle>m,n\<rangle>,successor \<circ>\<^sub>c p\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 y_def)
          also have "... = (leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried))\<circ>\<^sub>c ((distribute_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>m,n\<rangle>,successor \<circ>\<^sub>c p\<rangle>)"
            using \<phi>_def comp_associative2 mnsp_type by (typecheck_cfuncs, auto)
          also have "... = (leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried))\<circ>\<^sub>c  \<langle>\<langle>m,successor \<circ>\<^sub>c p\<rangle>,\<langle>n,successor \<circ>\<^sub>c p\<rangle>\<rangle>"
            using distribute_right_ap p_def y_def by (typecheck_cfuncs, auto)
          also have "... = leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried)\<circ>\<^sub>c  \<langle>\<langle>m,successor \<circ>\<^sub>c p\<rangle>,\<langle>n,successor \<circ>\<^sub>c p\<rangle>\<rangle>"
            using comp_associative2 mspnsp_type by (typecheck_cfuncs, auto) 
          also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c p\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c p\<rangle>\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod msp_type nsp_type by (typecheck_cfuncs, auto)
          also have "... = leq \<circ>\<^sub>c \<langle>m ^\<^sub>\<nat> (successor \<circ>\<^sub>c p),n ^\<^sub>\<nat> (successor \<circ>\<^sub>c p)\<rangle>"
            by (simp add: exp_def)
          also have "... = leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat>(m ^\<^sub>\<nat> p),n \<cdot>\<^sub>\<nat>(n ^\<^sub>\<nat> p)\<rangle>"
            by (simp add: exp_respects_successor p_def y_def)
          also have "... = leq \<circ>\<^sub>c \<langle>(m ^\<^sub>\<nat> p),(n ^\<^sub>\<nat> p)\<rangle>"
            oops
*)




(*
have "(eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f id\<^sub>c (\<Omega>\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c \<phi>\<^sup>\<sharp>) \<circ>\<^sub>c x = 
                (eval_func \<Omega> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  \<phi>\<^sup>\<sharp>) \<circ>\<^sub>c x"
            using \<phi>_sharp_type id_left_unit2 by auto
          also have "... = \<phi> \<circ>\<^sub>c x"
            using \<phi>_type transpose_func_def by auto
          also have "... = (leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried))\<circ>\<^sub>c \<langle>\<langle>m,p\<rangle>,\<langle>n,p\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt \<phi>_def comp_associative2 distribute_right_ap distribute_right_type p_def x_type y_def)
          also have "... = leq \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried)\<circ>\<^sub>c \<langle>\<langle>m,p\<rangle>,\<langle>n,p\<rangle>\<rangle>"
            using comp_associative2 mpnp_type by (typecheck_cfuncs, auto)
          also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>m,p\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>n,p\<rangle>\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod mp_type np_type by (typecheck_cfuncs,auto)
            by (simp add: exp_def)
            apply typecheck_cfuncs
            oops
*)




(*
lemma nonzero_to_k_nonzero:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<noteq> zero"
  shows "a ^\<^sub>\<nat> k \<noteq> zero"
proof - 
  have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero , a\<rangle> = \<t>"
    by (metis add_respects_succ2 add_respects_zero_on_right assms(1) assms(3) exists_implies_leq_true nonzero_is_succ succ_n_type zero_type)
  then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> k,  a ^\<^sub>\<nat> k\<rangle> = \<t>"
    using  assms(1) assms(2) exp_order_preserving1 by (typecheck_cfuncs, presburger)
  then show "a ^\<^sub>\<nat> k \<noteq> zero"
    using  assms(2) exp_respects_one_left lqe_antisymmetry succ_n_type zero_is_not_successor zero_is_smallest by (typecheck_cfuncs,force)
qed

*)


(*
lemma exp_order_preserving2:
  assumes x_type: "x \<in>\<^sub>c \<nat>\<^sub>c" and y_type: "y \<in>\<^sub>c \<nat>\<^sub>c" and a_type: "a \<in>\<^sub>c \<nat>\<^sub>c"
  assumes a_nonzero: "a \<noteq> zero"
  assumes leq_true: "leq \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>"
  shows "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> x, a ^\<^sub>\<nat> y\<rangle> = \<t>"
proof - 

  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> x = y"
    using leq_true leq_true_implies_exists x_type y_type by blast
  have ay_def: "a ^\<^sub>\<nat> y = (a ^\<^sub>\<nat> k) \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat>x)"
    using a_type exp_right_dist k_def x_type by blast
  have "(a ^\<^sub>\<nat> k) \<noteq> zero"
    by (simp add: a_nonzero a_type exp_order_preserving1 k_def nonzero_to_k_nonzero)
  then obtain p where p_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and>  (a ^\<^sub>\<nat> k) = successor \<circ>\<^sub>c p"
    using  a_type k_def nonzero_is_succ by (typecheck_cfuncs, blast)
  then have "a ^\<^sub>\<nat> y = (successor \<circ>\<^sub>c p)  \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat>x)"
    by (simp add: ay_def)
  also have "... = ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> p) \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat>x)"
    by (simp add: add_respects_succ3 add_respects_zero_on_left p_def zero_type)
  also have "... = ((successor \<circ>\<^sub>c zero)\<cdot>\<^sub>\<nat> (a^\<^sub>\<nat>x)) +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat>(a^\<^sub>\<nat>x)) "
    by (simp add: a_type exp_closure mult_Left_Distributivity p_def succ_n_type x_type zero_type)
  also have "... = (p \<cdot>\<^sub>\<nat>(a^\<^sub>\<nat>x)) +\<^sub>\<nat> (a^\<^sub>\<nat>x)"
    by (metis a_type add_commutes exp_closure mult_closure p_def s0_is_left_id x_type)
  then show "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> x, a ^\<^sub>\<nat> y\<rangle> = \<t>"
    by (typecheck_cfuncs, metis  a_type calculation exists_implies_leq_true mult_closure p_def x_type y_type)
qed
*)

(*
lemma succ_n_le_2_to_n:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , (successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> n \<rangle> = \<t>"
proof - 
  have main_result: "leq \<circ>\<^sub>c \<langle>successor  , exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero))\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle> \<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  proof(rule natural_number_object_func_unique[where X = "\<Omega>", where f = "id \<Omega>" ]) 
    show "leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "(leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
    proof - 
      have "(leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = 
             leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c zero"
        using comp_associative2 by (typecheck_cfuncs, force)
      also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero\<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>\<rangle>"
        using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
      also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), zero\<rangle>\<rangle>"
        using exp_def exp_respects_Zero_Left id_left_unit2 by (typecheck_cfuncs, presburger)
      also have "... = \<t>"
        by (typecheck_cfuncs, metis exp_def exp_order_preserving1 exp_respects_Zero_Left zero_is_smallest)
      also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, smt (z3) beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 successor_type terminal_func_comp)
      then show ?thesis
        using calculation by simp
    qed
    show "(leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor =
    id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
    proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<Omega>"])
      show "(leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c x"
      proof - 
        fix m 
        assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"

        have LHS: "((leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m  = 
                     leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (successor \<circ>\<^sub>c m),exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), (successor \<circ>\<^sub>c m)\<rangle>\<rangle>"
        proof -
          have"((leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m = 
                 (leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c m)"
            by (typecheck_cfuncs, metis comp_associative2)
          also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (successor \<circ>\<^sub>c m),exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c m)\<rangle>"
            by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
          also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (successor \<circ>\<^sub>c m),exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), (successor \<circ>\<^sub>c m)\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add:  cart_prod_extract_right)
          then show ?thesis
            by (simp add: calculation)
        qed

        have RHS: "(id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c m = 
                    leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m ,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) , m\<rangle>\<rangle>"
        proof - 
          have"(id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c m = 
                               leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c m"
            using comp_associative2 id_left_unit2 by (typecheck_cfuncs, auto)
          also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m ,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m\<rangle>"
            by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
          also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m ,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m\<rangle>\<rangle>"
            using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
          also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m ,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) , m\<rangle>\<rangle>"
            by (typecheck_cfuncs, metis beta_N_succ_mEqs_Id1 cfunc_type_def id_left_unit2 id_right_unit terminal_func_comp)
          then show ?thesis
            by (simp add: calculation)
        qed

          

        have "((leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m =
         (leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c m"
        proof(cases "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m ,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), m\<rangle> \<rangle> = \<t>")
          assume main_case: "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m ,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), m\<rangle> \<rangle> = \<t>"
          then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) +\<^sub>\<nat>  (successor \<circ>\<^sub>c zero),(exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), m\<rangle>) +\<^sub>\<nat>  (successor \<circ>\<^sub>c zero) \<rangle> = \<t>"
            by (typecheck_cfuncs, meson add_monotonic lqe_connexity)
          then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) +\<^sub>\<nat>  (successor \<circ>\<^sub>c zero),(exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), m\<rangle>) +\<^sub>\<nat>  (exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), m\<rangle>) \<rangle> = \<t>"
            by (typecheck_cfuncs, metis add_monotonic exists_implies_leq_true exp_def exp_order_preserving_converse exp_respects_one_left lqe_antisymmetry lqe_connexity one_plus_one_is_two main_case)
          then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) +\<^sub>\<nat>  (successor \<circ>\<^sub>c zero),(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), m\<rangle>) \<rangle> = \<t>"
            by (typecheck_cfuncs, metis  mult_Left_Distributivity one_plus_one_is_two s0_is_left_id)
          then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) +\<^sub>\<nat>  (successor \<circ>\<^sub>c zero),(exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), successor \<circ>\<^sub>c m\<rangle>) \<rangle> = \<t>"
            using  exp_def exp_respects_successor by (typecheck_cfuncs, presburger)
          then show ?thesis
            using LHS RHS add_respects_succ1 add_respects_zero_on_right id_left_unit2 m_type succ_n_type main_case zero_type by (typecheck_cfuncs, auto)
        next
          assume "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m,exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero,m\<rangle>\<rangle> \<noteq> \<t>"
          then have other_case: "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero,m\<rangle>, successor \<circ>\<^sub>c m\<rangle> = \<t>"
            using  lqe_connexity by (typecheck_cfuncs, blast)
          then have "(m = zero) \<or> (m = successor \<circ>\<^sub>c zero)"
            sorry
          then show ?thesis
            sorry
        qed

        then show "((leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c leq \<circ>\<^sub>c \<langle>successor,exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c m"
          using  id_left_unit2 by (typecheck_cfuncs, presburger)
      qed
    qed
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
  qed
  have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , (successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> n \<rangle> = 
        leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n), id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>\<rangle>"
    by (smt (verit, ccfv_SIG) assms comp_type exp_def id_left_unit2 id_right_unit2 id_type one_unique_element successor_type terminal_func_type zero_type)
  also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n, exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c n \<rangle>"
    by (typecheck_cfuncs, metis assms calculation exp_apply1)
  also have "... = (leq \<circ>\<^sub>c \<langle>successor , exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c \<rangle>  \<rangle>) \<circ>\<^sub>c n"
    by (typecheck_cfuncs, smt (z3) assms cfunc_prod_comp comp_associative2)
  also have "... = \<t>"
    by (typecheck_cfuncs, smt (z3) assms beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 main_result terminal_func_comp)
  then show ?thesis
    using calculation by presburger
qed

*)
  
  

(*


lemma mult_le_exp:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" and "b \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<noteq> successor \<circ>\<^sub>c zero" and "b \<noteq> zero"
  shows "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> b , a ^\<^sub>\<nat> b\<rangle> = \<t>"
proof(cases "a = zero",auto)
  show "a = zero \<Longrightarrow> leq \<circ>\<^sub>c \<langle>zero \<cdot>\<^sub>\<nat> b,zero ^\<^sub>\<nat> b\<rangle> = \<t>"
    by (typecheck_cfuncs, simp add: assms(2) mult_respects_zero_left zero_is_smallest)
next
  assume "a \<noteq> zero"
then have ge2: "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero), a\<rangle> = \<t>"
  by (smt add_respects_succ2 add_respects_zero_on_right assms(1) assms(3) exists_implies_leq_true nonzero_is_succ succ_n_type zero_type)
obtain c where c_def: "c \<in>\<^sub>c \<nat>\<^sub>c \<and>  b = successor \<circ>\<^sub>c c"
    using assms(2) assms(4) nonzero_is_succ by blast
have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c c, (successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> c\<rangle> = \<t>"
  by (simp add: c_def succ_n_le_2_to_n)
then have f1: "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c), a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> c\<rangle> = \<t>"
  by (meson  assms(1) c_def exp_closure lqe_connexity mult_monotonic succ_n_type zero_type)
have f2: "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> c), a \<cdot>\<^sub>\<nat>(a ^\<^sub>\<nat> c)\<rangle> = \<t>"
  by (meson assms(1) c_def exp_closure exp_order_preserving1 ge2 lqe_connexity mult_monotonic succ_n_type zero_type)
have "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat>(a ^\<^sub>\<nat> c), a ^\<^sub>\<nat> b \<rangle> = \<t>"
  by (metis assms(1) c_def exp_closure exp_respects_successor lqe_connexity mult_closure)
then show "leq \<circ>\<^sub>c \<langle>a  \<cdot>\<^sub>\<nat> b , a ^\<^sub>\<nat> b\<rangle> = \<t>"
  by (metis assms(1) c_def exp_closure exp_respects_successor f1 f2 leq_transitivity mult_closure succ_n_type zero_type)
qed

*)



end
