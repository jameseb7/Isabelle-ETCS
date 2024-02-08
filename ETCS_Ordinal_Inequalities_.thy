theory ETCS_Ordinal_Inequalities_
  imports ETCS_Exp ETCS_Comparison
begin

lemma exp_leq_preserving: 
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes a_leq_b: "leq \<circ>\<^sub>c \<langle>a, b\<rangle> = \<t>"
  shows "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c c  = \<t>"
proof(etcs_rule nat_induction)
  show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t>"
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_apply1 exp_respects_Zero_Left lqe_connexity succ_n_type)
  show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t> \<Longrightarrow>
         (leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
  proof - 
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume ind_hyp: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
    have "(a ^\<^sub>\<nat> n) \<le>\<^sub>\<nat> (b ^\<^sub>\<nat> n)"
    proof - 
      have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = 
             leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n\<rangle> "
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a , n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>b  , n\<rangle> \<rangle>"
        by (typecheck_cfuncs, metis cart_prod_extract_right)
      then show ?thesis
        using calculation exp_def ind_hyp leq_infix_def by presburger
    qed
    then have "(a ^\<^sub>\<nat> (successor \<circ>\<^sub>c n)) \<le>\<^sub>\<nat> (b ^\<^sub>\<nat> (successor \<circ>\<^sub>c n))"
      using  a_leq_b exp_closure exp_respects_successor leq_infix_def mult_monotonic by (typecheck_cfuncs, force)
    then show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_apply1 leq_infix_def)
  qed
qed



(*There might be a way to prove this in a single line!*)
lemma exp_leq_preserving': 
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "a \<le>\<^sub>\<nat> b \<Longrightarrow> a ^\<^sub>\<nat> c \<le>\<^sub>\<nat> b ^\<^sub>\<nat> c"
proof(unfold leq_infix_def exp_def)
  have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c c = 
         leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle>"
    by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  then show "leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t> \<Longrightarrow> leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle> = \<t>"
    by (typecheck_cfuncs, metis exp_leq_preserving)
qed



lemma nonzero_to_k_nonzero:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<noteq> zero"
  shows "a ^\<^sub>\<nat> k \<noteq> zero"
proof - 
  have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero , a\<rangle> = \<t>"
    by (metis add_respects_succ2 add_respects_zero_on_right assms(1) assms(3) exists_implies_leq_true nonzero_is_succ succ_n_type zero_type)
  then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> k,  a ^\<^sub>\<nat> k\<rangle> = \<t>"
    by (typecheck_cfuncs, meson assms exp_leq_preserving' leq_infix_def)
  then show "a ^\<^sub>\<nat> k \<noteq> zero"
    using  assms(2) exp_respects_one_left lqe_antisymmetry succ_n_type zero_is_not_successor zero_is_smallest by (typecheck_cfuncs,force)
qed






lemma exp_order_preserving:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "((a ^\<^sub>\<nat> (successor \<circ>\<^sub>cc)) = (b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)))"
  shows "a = b"
proof(rule ccontr)
  assume "a \<noteq> b"
  show False
  proof(cases "a \<le>\<^sub>\<nat> b")
    case True
    then have f0: "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, meson exp_leq_preserving' leq_infix_def)
    then have f1: "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis True exp_closure exp_leq_preserving' exp_respects_successor leq_infix_def lqe_connexity mult_monotonic)
    have f2: "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c), b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis True exp_respects_successor leq_infix_def lqe_connexity mult_monotonic) 
    have f3: "a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c) \<noteq> b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      by (typecheck_cfuncs, metis \<open>a \<noteq> b\<close> assms(4) exp_respects_successor exp_respects_zero_left mult_cancellative nonzero_to_k_nonzero)
    have f4: "a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c) = b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      using a_type assms(4) b_type c_type exp_closure f1 f2 lqe_antisymmetry mult_type succ_n_type by presburger
    then show ?thesis
      using f3 by blast
  next
    case False 
    then have "b \<le>\<^sub>\<nat> a"
      using a_type b_type leq_infix_def lqe_connexity by auto
    then have f0: "leq \<circ>\<^sub>c \<langle>b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, meson exp_leq_preserving' leq_infix_def)
    then have f1: "leq \<circ>\<^sub>c \<langle>b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis False exp_closure exp_leq_preserving' exp_respects_successor leq_infix_def lqe_connexity mult_monotonic)
    have f2: "leq \<circ>\<^sub>c \<langle>b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c), a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis False exp_respects_successor leq_infix_def lqe_connexity mult_monotonic) 
    have f3: "b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c) \<noteq> a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      by (typecheck_cfuncs, metis \<open>a \<noteq> b\<close> assms(4) exp_respects_successor exp_respects_zero_left mult_cancellative nonzero_to_k_nonzero)
    have f4: "b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c) = a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      using a_type assms(4) b_type c_type exp_closure f1 f2 lqe_antisymmetry mult_type succ_n_type by presburger
    then show ?thesis
      using f3 by blast  
  qed
qed


lemma exp_order_preserving':
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes nonzero_exp: "c \<noteq> zero"
  shows "(a = b) \<longleftrightarrow> ((a ^\<^sub>\<nat> c) = (b ^\<^sub>\<nat> c))"
  by (typecheck_cfuncs, metis exp_order_preserving nonzero_exp nonzero_is_succ)















































































(*
lemma exp_neq_preserving: 
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(IFF \<circ>\<^sub>c \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> , 
                eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle> \<rangle>) \<circ>\<^sub>c c = \<t>"
proof(etcs_rule nat_induction)
  show "(IFF \<circ>\<^sub>c
     \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
      eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c   zero = \<t>"
  proof(cases "a=b")
    case True
    then have lhs: "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c   zero = \<t>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 eq_pred_iff_eq id_right_unit2 terminal_func_comp_elem)
    have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c   zero = \<t>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_def2 exp_respects_one_right exp_uncurried_apply id_right_unit2 lhs succ_n_type terminal_func_comp_elem)
    then show ?thesis
      by (typecheck_cfuncs, smt IFF_true_true_is_true  cfunc_prod_comp comp_associative2 lhs)
  next
    case False
    then have lhs: "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c   zero = \<f>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv id_right_unit2 terminal_func_comp_elem)
    have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c   zero = \<f>"
      by (typecheck_cfuncs, smt False cfunc_prod_comp comp_associative2 eq_pred_iff_eq exp_def exp_respects_one_right id_right_unit2 terminal_func_comp_elem true_false_only_truth_values)
    then show ?thesis
      by (typecheck_cfuncs, smt IFF_false_false_is_true  cfunc_prod_comp comp_associative2 lhs)
  qed
  show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
       (IFF \<circ>\<^sub>c \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
               eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c  n =  \<t> \<Longrightarrow>
       (IFF \<circ>\<^sub>c \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
               eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
  proof - 
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume  "(IFF \<circ>\<^sub>c \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
               eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c  n =  \<t>"
    then have "IFF \<circ>\<^sub>c \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
               eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>\<rangle> \<circ>\<^sub>c  n =  \<t>"
      using comp_associative2  by (typecheck_cfuncs, force)
    then have ind_hyp:"IFF \<circ>\<^sub>c \<langle>(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> ) \<circ>\<^sub>c  n,
               (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c  n \<rangle>  =  \<t>"
      by (typecheck_cfuncs, metis cfunc_prod_comp)
    


    show "(IFF \<circ>\<^sub>c \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,
               eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
    proof(cases "a=b")
      case True
      then have lhs: "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c   n  = \<t>"
        by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 eq_pred_iff_eq id_right_unit2 terminal_func_comp_elem) 
      have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c  successor \<circ>\<^sub>c  n = \<t>"
        by (typecheck_cfuncs, smt True cfunc_prod_comp comp_type eq_pred_iff_eq_conv true_false_only_truth_values)
      then show ?thesis
        by (typecheck_cfuncs, smt IFF_true_true_is_true cfunc_prod_comp comp_associative2 lhs terminal_func_comp_elem)
    next
      case False
      then have lhs: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c   n  = \<f>"
        by (typecheck_cfuncs, smt False cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv id_right_unit2 terminal_func_comp_elem)
      then have rhs: "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c   n  = \<f>"
        by (typecheck_cfuncs, metis IFF_false_true_is_false comp_associative2 ind_hyp lhs true_false_only_truth_values)
      have "a ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) \<noteq> b ^\<^sub>\<nat> (successor \<circ>\<^sub>c n)"
      proof - 
        have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c   n = 
              eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c n, (exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c n\<rangle> "
          by (typecheck_cfuncs, simp add: cfunc_prod_comp)
        also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n,successor \<circ>\<^sub>c n\<rangle>) , (exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n ,successor \<circ>\<^sub>c n\<rangle>)\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
        also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) , b ^\<^sub>\<nat> (successor \<circ>\<^sub>c n)\<rangle>"
          by (typecheck_cfuncs, smt (z3) comp_associative2 exp_def2 exp_uncurried_apply id_right_unit2 terminal_func_comp_elem)
        also have "... = \<f>"
          using rhs calculation by presburger
        then show ?thesis
          by (metis a_type eq_pred_iff_eq_conv exp_closure n_type succ_n_type)
      qed
      have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c n  = \<f>"
*)



(*

lemma exp_order_preserving:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(IFF \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>  , exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>\<rangle>,
        leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c c  = \<t>"
proof(etcs_rule nat_induction)
  show "(IFF \<circ>\<^sub>c
     \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
      leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c
    zero = \<t>"
  proof(cases "leq \<circ>\<^sub>c \<langle>a ,b\<rangle>  = \<t>")
    case True
    then have f1: "leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero\<rangle>  = \<t>"
      by (typecheck_cfuncs, smt comp_associative2 id_right_unit2 terminal_func_comp_elem)
    then have f2: "(leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>),(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<rangle>) \<circ>\<^sub>c zero  = \<t>"
      by (typecheck_cfuncs,smt cfunc_prod_comp comp_associative2)
    then have f3:"(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_def exp_respects_one_right f1 id_right_unit2 terminal_func_comp_elem)
    then have "IFF \<circ>\<^sub>c
     \<langle>(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c zero,
      leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero\<rangle>\<rangle> = \<t>"
      by (simp add: IFF_true_true_is_true f1 f3)
    then have "IFF \<circ>\<^sub>c
     \<langle>(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>),
      leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) ,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<rangle> \<rangle> \<circ>\<^sub>c zero = \<t>"
      using IFF_true_true_is_true cfunc_prod_comp f2 f3 by (typecheck_cfuncs, force)
    then show "(IFF \<circ>\<^sub>c  
     \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
      leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero =  \<t>"
      using  comp_associative2 by (typecheck_cfuncs, auto)
  next
    case False
    then have "(leq \<circ>\<^sub>c \<langle>b ,a\<rangle>  = \<t>) \<and> (a \<noteq> b)"
      using lqe_connexity by (typecheck_cfuncs, blast)
    then have f0: "(leq \<circ>\<^sub>c \<langle>a ,b\<rangle>  = \<f>) \<and> (a \<noteq> b)"
      using False true_false_only_truth_values by (typecheck_cfuncs, blast)
    then have f1: "leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero,(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero\<rangle>  = \<f>"
      by (smt (z3) a_type b_type comp_associative2 id_right_unit2 terminal_func_comp_elem terminal_func_type zero_type)
    then have f2: "(leq \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>),(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<rangle>) \<circ>\<^sub>c zero  = \<f>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
    then have f3:"(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<f>"
      by (typecheck_cfuncs, smt f0 cfunc_prod_comp comp_associative2 exp_def exp_respects_one_right id_right_unit2 terminal_func_comp_elem)
    then show "(IFF \<circ>\<^sub>c  
     \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
      leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero =  \<t>"
      by (typecheck_cfuncs, smt IFF_false_false_is_true cfunc_prod_comp comp_associative2 f2)
  qed
  show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> 
         (IFF \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                 leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c n =  \<t> \<Longrightarrow>
         (IFF \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                 leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n =  \<t>"
  proof - 
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume inductive_hyp: "(IFF \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                 leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c n =  \<t>"
    then have inductive_hyp1: "IFF \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                 leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c n =  \<t>"  
      by (typecheck_cfuncs, simp add: comp_associative2)
    then have inductive_hyp2: "IFF \<circ>\<^sub>c \<langle>(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c n,
                 (leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c n \<rangle>  =  \<t>"
      by (typecheck_cfuncs, metis cfunc_prod_comp)
    
    show "(IFF \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>,
                 leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n =  \<t>"
    proof(cases "leq \<circ>\<^sub>c \<langle>a ,b\<rangle>  = \<t>")
      case True
      then have f0:"(leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c n = \<t>"
        by (typecheck_cfuncs, smt (z3) True cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      then have f1:"(leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c  successor \<circ>\<^sub>c n = \<t>"
        by (typecheck_cfuncs, smt True beta_N_succ_mEqs_Id1 cfunc_prod_comp comp_associative2 id_right_unit2)
      have f2: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
        by (typecheck_cfuncs, metis IFF_false_true_is_false inductive_hyp2 true_false_only_truth_values f0)
      have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c n = \<t>"
        by (typecheck_cfuncs, simp add: comp_associative2 f2)
      then have "leq \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c n,(exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>)  \<circ>\<^sub>c n\<rangle> = \<t>"
        using cfunc_prod_comp by (typecheck_cfuncs, force)
      then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c n, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>  \<circ>\<^sub>c n\<rangle> = \<t>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n,successor \<circ>\<^sub>c n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n ,successor \<circ>\<^sub>c n \<rangle> \<rangle> = \<t>"
        using cfunc_prod_comp by (typecheck_cfuncs, force)
      then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a ,successor \<circ>\<^sub>c n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>b ,successor \<circ>\<^sub>c n \<rangle> \<rangle> = \<t>"
        by (typecheck_cfuncs, smt comp_associative2 id_right_unit2 terminal_func_comp_elem terminal_func_type)
      then have "leq \<circ>\<^sub>c \<langle> a \<cdot>\<^sub>\<nat> a^\<^sub>\<nat>(successor \<circ>\<^sub>c n) , b \<cdot>\<^sub>\<nat> b^\<^sub>\<nat>(successor \<circ>\<^sub>c n) \<rangle> = \<t>"
        by (typecheck_cfuncs, simp add: True exp_def mult_monotonic)
      then have "leq \<circ>\<^sub>c \<langle> a^\<^sub>\<nat>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c n) , b^\<^sub>\<nat>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c n) \<rangle> = \<t>"
        by (typecheck_cfuncs, metis exp_respects_successor)
      then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c n ,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c n ,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n \<rangle> \<rangle> = \<t>"
        by (typecheck_cfuncs, smt comp_associative2 exp_def2 exp_uncurried_apply id_right_unit2 terminal_func_comp_elem)
      then have f3: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
        by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
      then show ?thesis
        by (typecheck_cfuncs, smt (z3) IFF_true_true_is_true cfunc_prod_comp comp_associative2 f1 f3)
    next 
      case False
      then have b_leq_a: "(leq \<circ>\<^sub>c \<langle>b ,a\<rangle>  = \<t>) \<and> (a \<noteq> b)"
        using lqe_connexity by (typecheck_cfuncs, blast)
      then have b_lt_a:"(leq \<circ>\<^sub>c \<langle>a ,b\<rangle>  = \<f>) \<and> (a \<noteq> b)"
        using False true_false_only_truth_values by (typecheck_cfuncs, blast)
      then have f0:"(leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c n = \<f>"
        by (typecheck_cfuncs, smt  cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      then have f1:"(leq \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c  successor \<circ>\<^sub>c n = \<f>"
        by (typecheck_cfuncs, smt (z3) b_lt_a beta_N_succ_mEqs_Id1 cfunc_prod_comp comp_associative2 id_right_unit2)
      have f2: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c n = \<f>"
        by (typecheck_cfuncs, metis IFF_true_false_is_false f0 inductive_hyp2 true_false_only_truth_values)
      have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle> \<circ>\<^sub>c n = \<f>"
        by (typecheck_cfuncs, simp add: comp_associative2 f2)
      then have "leq \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c n,(exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>)  \<circ>\<^sub>c n\<rangle> = \<f>"
        using cfunc_prod_comp by (typecheck_cfuncs, force)
      then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c n, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>  \<circ>\<^sub>c n\<rangle> = \<f>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n,successor \<circ>\<^sub>c n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n ,successor \<circ>\<^sub>c n \<rangle> \<rangle> = \<f>"
        using cfunc_prod_comp by (typecheck_cfuncs, force)
      then have f2b: "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a ,successor \<circ>\<^sub>c n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>b ,successor \<circ>\<^sub>c n \<rangle> \<rangle> = \<f>"
        by (typecheck_cfuncs, smt comp_associative2 id_right_unit2 terminal_func_comp_elem terminal_func_type)
      have "leq \<circ>\<^sub>c \<langle> a \<cdot>\<^sub>\<nat> a^\<^sub>\<nat>(successor \<circ>\<^sub>c n) , b \<cdot>\<^sub>\<nat> b^\<^sub>\<nat>(successor \<circ>\<^sub>c n) \<rangle> = \<f>"
      proof - 
        have "(leq \<circ>\<^sub>c \<langle> b^\<^sub>\<nat>(successor \<circ>\<^sub>c n) , a^\<^sub>\<nat>(successor \<circ>\<^sub>c n) \<rangle> = \<t>) \<and> (b^\<^sub>\<nat>(successor \<circ>\<^sub>c n) \<noteq> a^\<^sub>\<nat>(successor \<circ>\<^sub>c n))"
          by (typecheck_cfuncs, metis exp_def lqe_connexity true_false_distinct f2b)
        then have "(leq \<circ>\<^sub>c \<langle> b \<cdot>\<^sub>\<nat> b^\<^sub>\<nat>(successor \<circ>\<^sub>c n) , a \<cdot>\<^sub>\<nat> a^\<^sub>\<nat>(successor \<circ>\<^sub>c n) \<rangle> = \<t>)"
          by (typecheck_cfuncs, simp add:  b_leq_a mult_monotonic)
        then show ?thesis      
          by (typecheck_cfuncs, metis  b_lt_a exp_neq_preserving2 exp_respects_successor lqe_antisymmetry succ_n_type true_false_only_truth_values zero_is_not_successor)
      qed
      then have "leq \<circ>\<^sub>c \<langle> a^\<^sub>\<nat>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c n) , b^\<^sub>\<nat>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c n) \<rangle> = \<f>"
        by (typecheck_cfuncs, metis exp_respects_successor)
      then have "leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>(a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c n ,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>(b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c n ,successor \<circ>\<^sub>c successor \<circ>\<^sub>c n \<rangle> \<rangle> = \<f>"
        by (typecheck_cfuncs, smt comp_associative2 exp_def2 exp_uncurried_apply id_right_unit2 terminal_func_comp_elem)
      then have f3: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<f>"
        by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
      then show ?thesis
        by (typecheck_cfuncs, smt IFF_false_false_is_true cfunc_prod_comp comp_associative2 f1 f3)
    qed
  qed
  
*)



(*
lemma exp_order_preserving2:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> c , b ^\<^sub>\<nat> c\<rangle> = \<t>) \<longleftrightarrow>  (leq \<circ>\<^sub>c \<langle>a , b \<rangle> = \<t>)"
  sorry
*)




end