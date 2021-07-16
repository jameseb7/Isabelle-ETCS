theory ETCS_Ordinal_Inequalities
  imports ETCS_Exp ETCS_Comparison
begin

(*
lemma exp_order_preserving1:
  assumes a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes leq: "leq \<circ>\<^sub>c \<langle>a , b\<rangle> = \<t>"
  shows "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> c , b ^\<^sub>\<nat> c\<rangle> = \<t>"
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
    proof(rule same_evals_equal[where Z = one, where X = "\<Omega>", where A = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone"])
      show "\<phi>\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>((\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one)\<^esup>" 
        apply typecheck_cfuncs
        oops
*)


lemma nonzero_to_k_nonzero:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<noteq> zero"
  assumes "\<And>x y z. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  y \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  z \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  leq \<circ>\<^sub>c \<langle>x , y\<rangle> = \<t>  \<Longrightarrow> leq \<circ>\<^sub>c \<langle>x ^\<^sub>\<nat> z , y ^\<^sub>\<nat> z\<rangle> = \<t>" (*Delete once above is proven*)
  shows "a ^\<^sub>\<nat> k \<noteq> zero"
proof - 
  have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero , a\<rangle> = \<t>"
    by (metis add_respects_succ2 add_respects_zero_on_right assms(1) assms(3) exists_implies_leq_true nonzero_is_succ succ_n_type zero_type)
  then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> k,  a ^\<^sub>\<nat> k\<rangle> = \<t>"
    by (typecheck_cfuncs, simp add: assms(1) assms(2) assms(4))
  then show "a ^\<^sub>\<nat> k \<noteq> zero" 
    using  assms(2) exp_respects_one_left lqe_antisymmetry succ_n_type zero_is_not_successor zero_is_smallest by (typecheck_cfuncs,force)
qed





lemma exp_order_preserving:
  assumes x_type: "x \<in>\<^sub>c \<nat>\<^sub>c" and y_type: "y \<in>\<^sub>c \<nat>\<^sub>c" and a_type: "a \<in>\<^sub>c \<nat>\<^sub>c"
  assumes a_nonzero: "a \<noteq> zero"
  assumes leq_true: "leq \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>"
  assumes "\<And>x y z. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  y \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  z \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  leq \<circ>\<^sub>c \<langle>x , y\<rangle> = \<t>  \<Longrightarrow> leq \<circ>\<^sub>c \<langle>x ^\<^sub>\<nat> z , y ^\<^sub>\<nat> z\<rangle> = \<t>" (*Delete once above is proven*)
  shows "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> x, a ^\<^sub>\<nat> y\<rangle> = \<t>"
proof - 

  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> x = y"
    using leq_true leq_true_implies_exists x_type y_type by blast
  have ay_def: "a ^\<^sub>\<nat> y = (a ^\<^sub>\<nat> k) \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat>x)"
    using a_type exp_right_dist k_def x_type by blast
  have "(a ^\<^sub>\<nat> k) \<noteq> zero"
    by (simp add: a_nonzero a_type assms(6) k_def nonzero_to_k_nonzero)
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

(*
lemma succ_n_le_2_to_n:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , (successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> n \<rangle> = \<t>"
*)

lemma mult_le_exp:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" and "b \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<noteq> successor \<circ>\<^sub>c zero" and "b \<noteq> zero"
  assumes "\<And>x y z. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  y \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  z \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  leq \<circ>\<^sub>c \<langle>x , y\<rangle> = \<t>  \<Longrightarrow> leq \<circ>\<^sub>c \<langle>x ^\<^sub>\<nat> z , y ^\<^sub>\<nat> z\<rangle> = \<t>" (*Delete once above is proven*)
  assumes "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , (successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> n \<rangle> = \<t>" (*Delete once above is proven*)
  shows "leq \<circ>\<^sub>c \<langle>a  \<cdot>\<^sub>\<nat> b , a ^\<^sub>\<nat> b\<rangle> = \<t>"
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
  using assms(6) c_def by blast
then have f1: "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c), a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> c\<rangle> = \<t>"
  by (meson  assms(1) c_def exp_closure lqe_connexity mult_monotonic succ_n_type zero_type)
have f2: "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)) ^\<^sub>\<nat> c), a \<cdot>\<^sub>\<nat>(a ^\<^sub>\<nat> c)\<rangle> = \<t>"
    by (metis add_respects_zero_on_left assms(1) assms(5) c_def exists_implies_leq_true exp_closure ge2 mult_monotonic succ_n_type zero_type)
have "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat>(a ^\<^sub>\<nat> c), a ^\<^sub>\<nat> b \<rangle> = \<t>"
    by (metis assms(1) c_def exp_closure exp_respects_successor lqe_connexity mult_closure)
then show "leq \<circ>\<^sub>c \<langle>a  \<cdot>\<^sub>\<nat> b , a ^\<^sub>\<nat> b\<rangle> = \<t>"
  by (metis assms(1) c_def exp_closure exp_respects_successor f1 f2 leq_transitivity mult_closure succ_n_type zero_type)
qed


end
