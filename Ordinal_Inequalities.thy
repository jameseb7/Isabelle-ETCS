theory Ordinal_Inequalities
  imports Exp Inequality
begin

lemma exp_leq_preserving: 
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes a_leq_b: "leq \<circ>\<^sub>c \<langle>a, b\<rangle> = \<t>"
  shows "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c c  = \<t>"
proof(etcs_rule nat_induction)
  show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t>"
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_apply1 exp_respects_Zero_Left lqe_connexity succ_n_type)
  show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t> \<Longrightarrow>
         (leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
  proof - 
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume ind_hyp: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
    have "a ^\<^sub>\<nat> n \<le>\<^sub>\<nat> b ^\<^sub>\<nat> n"
    proof - 
      have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = 
             leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n\<rangle> "
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a, n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>b, n\<rangle>\<rangle>"
        by (typecheck_cfuncs, metis cart_prod_extract_right)
      then show ?thesis
        using calculation exp_def ind_hyp leq_infix_def by presburger
    qed
    then have "a ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) \<le>\<^sub>\<nat> b ^\<^sub>\<nat> (successor \<circ>\<^sub>c n)"
      using  a_leq_b exp_closure exp_respects_successor leq_infix_def mult_monotonic by (typecheck_cfuncs, force)
    then show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_apply1 leq_infix_def)
  qed
qed

lemma exp_leq_preserving': 
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "a \<le>\<^sub>\<nat> b \<Longrightarrow> a ^\<^sub>\<nat> c \<le>\<^sub>\<nat> b ^\<^sub>\<nat> c"
proof(unfold leq_infix_def exp_def)
  have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c c = 
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
  have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, a\<rangle> = \<t>"
    by (metis add_respects_succ2 add_respects_zero_on_right assms(1,3) exists_implies_leq_true nonzero_is_succ succ_n_type zero_type)
  then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> k, a ^\<^sub>\<nat> k\<rangle> = \<t>"
    by (typecheck_cfuncs, meson assms exp_leq_preserving' leq_infix_def)
  then show "a ^\<^sub>\<nat> k \<noteq> zero"
    using  assms(2) exp_respects_one_left lqe_antisymmetry succ_n_type zero_is_not_successor zero_is_smallest by(typecheck_cfuncs, force)
qed

lemma exp_order_preserving:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c) = b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
  shows "a = b"
proof(rule ccontr)
  assume "a \<noteq> b"
  show False
  proof(cases "a \<le>\<^sub>\<nat> b")
    case True
    then have "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, meson exp_leq_preserving' leq_infix_def)
    then have f1: "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis True exp_closure exp_leq_preserving' exp_respects_successor leq_infix_def lqe_connexity mult_monotonic)
    have f2: "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c), b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis True exp_respects_successor leq_infix_def lqe_connexity mult_monotonic) 
    have f3: "a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c) \<noteq> b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      by (typecheck_cfuncs, metis \<open>a \<noteq> b\<close> assms(4) exp_respects_successor exp_respects_zero_left mult_cancellative nonzero_to_k_nonzero)
    have "a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c) = b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
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
  shows "(a = b) \<longleftrightarrow> (a ^\<^sub>\<nat> c = b ^\<^sub>\<nat> c)"
  by (typecheck_cfuncs, metis exp_order_preserving nonzero_exp nonzero_is_succ)

end