theory ETCS_Parity
  imports ETCS_Add ETCS_Mult ETCS_Exp ETCS_Pred ETCS_Quantifier
begin

definition nth_even :: "cfunc" where
  "nth_even = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> 
    u \<circ>\<^sub>c zero = zero \<and>
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma nth_even_def2:
  "nth_even: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c zero = zero \<and> (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even = nth_even \<circ>\<^sub>c successor"
  by (unfold nth_even_def, rule theI', typecheck_cfuncs, rule natural_number_object_property2, auto)

lemma nth_even_type[type_rule]:
  "nth_even: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  by (simp add: nth_even_def2)

lemma nth_even_zero:
  "nth_even \<circ>\<^sub>c zero = zero"
  by (simp add: nth_even_def2)

lemma nth_even_successor:
  "nth_even \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
  by (simp add: nth_even_def2)

lemma nth_even_successor2:
  "nth_even \<circ>\<^sub>c successor = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
  using comp_associative2 nth_even_def2 by (typecheck_cfuncs, auto)

lemma nth_even_is_times_two:
  "nth_even = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
proof (rule natural_number_object_func_unique[where f="successor \<circ>\<^sub>c successor", where X="\<nat>\<^sub>c"])
  show "nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "nth_even \<circ>\<^sub>c zero = (mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
  proof -
    have "(mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero
      = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero, zero\<rangle>"
      by (typecheck_cfuncs, simp add: cart_prod_extract_right)
    also have "... = zero"
      using mult_def mult_respects_zero_right succ_n_type zero_type by auto
    also have "... = nth_even \<circ>\<^sub>c zero"
      by (simp add: nth_even_def2)
    then show ?thesis
      using calculation by auto
  qed

  show "nth_even \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
    by (simp add: nth_even_successor)

  show "(mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
  proof -
    have "(mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor
      = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
    also have "... = add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      using mult2_respects_succ_right by (typecheck_cfuncs, blast)
    also have "... = add2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: add2_commutes_succ add2_respects_succ_right)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, simp add: add2_respects_zero_on_left)
    also have "... = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, smt comp_associative2)
    then show ?thesis
      using calculation by auto
  qed
qed

lemma nth_even_is_times_twoB:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "nth_even \<circ>\<^sub>c n = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n"
proof - 
  have "nth_even \<circ>\<^sub>c n  = (mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
    using nth_even_is_times_two by auto
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n, id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c id(one), id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, metis terminal_func_unique)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n"
    by (simp add: mult_def)
  then show ?thesis using calculation by auto
qed



definition nth_odd :: "cfunc" where
  "nth_odd = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> 
    u \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero \<and>
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma nth_odd_def2:
  "nth_odd: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero \<and> (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd = nth_odd \<circ>\<^sub>c successor"
  by (unfold nth_odd_def, rule theI', typecheck_cfuncs, rule natural_number_object_property2, auto)

lemma nth_odd_type[type_rule]:
  "nth_odd: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  by (simp add: nth_odd_def2)

lemma nth_odd_zero:
  "nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero"
  by (simp add: nth_odd_def2)

lemma nth_odd_successor:
  "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
  by (simp add: nth_odd_def2)

lemma nth_odd_successor2:
  "nth_odd \<circ>\<^sub>c successor = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
  using comp_associative2 nth_odd_def2 by (typecheck_cfuncs, auto)

lemma nth_odd_is_succ_times_two:
  "nth_odd = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
proof (rule natural_number_object_func_unique[where f="successor \<circ>\<^sub>c successor", where X="\<nat>\<^sub>c"])
  show "nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "nth_odd \<circ>\<^sub>c zero =
    (successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
  proof -
    have "(successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero
      = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero, zero\<rangle>"
      by (typecheck_cfuncs, simp add: cart_prod_extract_right)
    also have "... = successor \<circ>\<^sub>c zero"
      using mult_def mult_respects_zero_right succ_n_type zero_type by auto
    also have "... = nth_odd \<circ>\<^sub>c zero"
      by (simp add: nth_odd_def2)
    then show ?thesis
      using calculation by auto
  qed

  show "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
    by (simp add: nth_odd_successor)

  show "(successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c  successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
  proof -
    have "(successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor
      = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
    also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      using mult2_respects_succ_right by (typecheck_cfuncs, auto)
    also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: add2_commutes_succ add2_respects_succ_right)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, simp add: add2_respects_zero_on_left)
    also have "... = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, smt comp_associative2)
    then show ?thesis
      using calculation by auto
  qed
qed

lemma nth_odd_is_succ_times_twoB:
 assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
 shows "nth_odd \<circ>\<^sub>c n = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n)"
proof - 
  have "nth_odd \<circ>\<^sub>c n = (successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
    by (simp add: nth_odd_is_succ_times_two)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n, id \<nat>\<^sub>c \<circ>\<^sub>c n \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c id(one), id \<nat>\<^sub>c \<circ>\<^sub>c n \<rangle>"
    using assms by (typecheck_cfuncs, metis terminal_func_unique)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), n \<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  also have "... = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n)"
    by (simp add: mult_def)
  then show ?thesis using calculation by auto
qed


lemma nth_odd_is_succ_nth_even:
  "nth_odd = successor \<circ>\<^sub>c nth_even"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f="successor \<circ>\<^sub>c successor"])
  show "nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor \<circ>\<^sub>c nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "nth_odd \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero"
  proof -
    have "nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero"
      by (simp add: nth_odd_zero)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero"
      using nth_even_is_times_two nth_odd_def2 nth_odd_is_succ_times_two by (typecheck_cfuncs, auto)
    then show ?thesis
      using calculation by auto
  qed

  show "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
    by (simp add: nth_odd_successor)

  show "(successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
  proof -
    have "(successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      by (simp add: nth_even_successor2)
    also have "... = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then show ?thesis
      using calculation by auto
  qed
qed

lemma succ_nth_odd_is_nth_even_succ:
  "successor \<circ>\<^sub>c nth_odd = nth_even \<circ>\<^sub>c successor"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f="successor \<circ>\<^sub>c successor"])
  show "successor \<circ>\<^sub>c nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "nth_even \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "(successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = (nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
  proof -
    have "(successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero"
      using comp_associative2 nth_odd_def2 successor_type zero_type by fastforce
    also have "... = (nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
      using calculation nth_even_successor2 nth_odd_is_succ_nth_even by auto
    then show ?thesis
      using calculation by auto
  qed

  show "(successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
    by (metis cfunc_type_def codomain_comp comp_associative nth_odd_def2 successor_type)
  then show "(nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
    using nth_even_successor2 nth_odd_is_succ_nth_even by auto
qed
      

definition is_even :: "cfunc" where
  "is_even = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> u \<circ>\<^sub>c zero = \<t> \<and> NOT \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma is_even_def2:
  "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_even \<circ>\<^sub>c zero = \<t> \<and> NOT \<circ>\<^sub>c is_even = is_even \<circ>\<^sub>c successor"
  by (unfold is_even_def, rule theI', typecheck_cfuncs, rule natural_number_object_property2, auto)

lemma is_even_type[type_rule]:
  "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega>"
  by (simp add: is_even_def2)

lemma is_even_zero:
  "is_even \<circ>\<^sub>c zero = \<t>"
  by (simp add: is_even_def2)

lemma is_even_successor:
  "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
  by (simp add: is_even_def2)

definition is_odd :: "cfunc" where
  "is_odd = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> u \<circ>\<^sub>c zero = \<f> \<and> NOT \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma is_odd_def2:
  "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_odd \<circ>\<^sub>c zero = \<f> \<and> NOT \<circ>\<^sub>c is_odd = is_odd \<circ>\<^sub>c successor"
  by (unfold is_odd_def, rule theI', typecheck_cfuncs, rule natural_number_object_property2, auto)

lemma is_odd_type[type_rule]:
  "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>"
  by (simp add: is_odd_def2)

lemma is_odd_zero:
  "is_odd \<circ>\<^sub>c zero = \<f>"
  by (simp add: is_odd_def2)

lemma is_odd_successor:
  "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
  by (simp add: is_odd_def2)

lemma is_even_not_is_odd:
  "is_even = NOT \<circ>\<^sub>c is_odd"
proof (typecheck_cfuncs, rule natural_number_object_func_unique[where f="NOT", where X="\<Omega>"], auto)

  show "is_even \<circ>\<^sub>c zero = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, metis NOT_false_is_true cfunc_type_def comp_associative is_even_def2 is_odd_def2)

  show "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
    by (simp add: is_even_successor)

  show "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_odd"
    by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative is_odd_def2)
qed

lemma is_odd_not_is_even:
  "is_odd = NOT \<circ>\<^sub>c is_even"
proof (typecheck_cfuncs, rule natural_number_object_func_unique[where f="NOT", where X="\<Omega>"], auto)

  show "is_odd \<circ>\<^sub>c zero = (NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, metis NOT_true_is_false cfunc_type_def comp_associative is_even_def2 is_odd_def2)

  show "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
    by (simp add: is_odd_successor)

  show "(NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_even"
    by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative is_even_def2)
qed


lemma not_even_and_odd:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<not>(is_even \<circ>\<^sub>c m = \<t> \<and> is_odd \<circ>\<^sub>c m = \<t>)"
  using assms NOT_true_is_false NOT_type comp_associative2 is_even_not_is_odd true_false_distinct by (typecheck_cfuncs, fastforce)




lemma even_or_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(is_even \<circ>\<^sub>c n = \<t>) \<or> (is_odd \<circ>\<^sub>c n = \<t>)"
  by (typecheck_cfuncs, metis NOT_false_is_true NOT_type comp_associative2 is_even_not_is_odd true_false_only_truth_values assms)

lemma is_even_nth_even_true:
  "is_even \<circ>\<^sub>c nth_even = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof (rule natural_number_object_func_unique[where f="id \<Omega>", where X=\<Omega>])
  show "is_even \<circ>\<^sub>c nth_even : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
    by typecheck_cfuncs

  show "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
  proof -
    have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = is_even \<circ>\<^sub>c nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<t>"
      by (simp add: is_even_zero nth_even_zero)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis comp_associative2 id_right_unit2 terminal_func_comp_elem)
    then show ?thesis
      using calculation by auto
  qed

  show "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c is_even \<circ>\<^sub>c nth_even"
  proof -
    have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = is_even \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = is_even \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      by (simp add: nth_even_successor2)
    also have "... = ((is_even \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... =  is_even \<circ>\<^sub>c nth_even"
      using is_even_def2 is_even_not_is_odd is_odd_def2 is_odd_not_is_even by (typecheck_cfuncs, auto)
    also have "... = id \<Omega> \<circ>\<^sub>c is_even \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: id_left_unit2)
    then show ?thesis
      using calculation by auto
  qed

  show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
qed

lemma is_odd_nth_odd_true:
  "is_odd \<circ>\<^sub>c nth_odd = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof (rule natural_number_object_func_unique[where f="id \<Omega>", where X=\<Omega>])
  show "is_odd \<circ>\<^sub>c nth_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
    by typecheck_cfuncs

  show "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
  proof -
    have "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = is_odd \<circ>\<^sub>c nth_odd \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = \<t>"
      using comp_associative2 is_even_not_is_odd is_even_zero is_odd_def2 nth_odd_def2 successor_type zero_type by auto
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis comp_associative2 is_even_nth_even_true is_even_type is_even_zero nth_even_def2)
    then show ?thesis
      using calculation by auto
  qed

  show "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c nth_odd"
  proof -
    have "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = is_odd \<circ>\<^sub>c nth_odd \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = is_odd \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
      by (simp add: nth_odd_successor2)
    also have "... = ((is_odd \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... =  is_odd \<circ>\<^sub>c nth_odd"
      using is_even_def2 is_even_not_is_odd is_odd_def2 is_odd_not_is_even by (typecheck_cfuncs, auto)
    also have "... = id \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: id_left_unit2)
    then show ?thesis
      using calculation by auto
  qed

  show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
qed

lemma is_odd_nth_even_false:
  "is_odd \<circ>\<^sub>c nth_even = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  by (smt NOT_true_is_false NOT_type comp_associative2 is_even_def2 is_even_nth_even_true
      is_odd_not_is_even nth_even_def2 terminal_func_type true_func_type)

lemma is_even_nth_odd_false:
  "is_even \<circ>\<^sub>c nth_odd = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  by (smt NOT_true_is_false NOT_type comp_associative2 is_odd_def2 is_odd_nth_odd_true
      is_even_not_is_odd nth_odd_def2 terminal_func_type true_func_type)


lemma add_evens_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k = n"
  shows   "(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k) = m +\<^sub>\<nat> n"
proof - 
  have m_pls_n: "m +\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)"
    using assms(3) assms(4) by blast
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)"
    by (typecheck_cfuncs, simp add: assms(3) assms(4) mult_right_distributivity)
  then show ?thesis
    by (simp add: m_pls_n)
qed


lemma add_odds_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ((j +\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) = (m +\<^sub>\<nat> n)"
proof - 
  have m_pls_n: "m +\<^sub>\<nat> n = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) +\<^sub>\<nat> (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using assms(3) assms(4) by blast
  also have "... = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: add_associates_mix_commutes assms(3) assms(4))
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: assms(3) assms(4) mult_right_distributivity)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)"
    by (simp add: one_plus_one_is_two)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: s0_is_right_id)
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ((j +\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: assms(3) assms(4) mult_right_distributivity)
  then show ?thesis
    by (simp add: calculation)
qed


lemma add_mixed_is_odd: 
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) = m +\<^sub>\<nat> n"
proof(typecheck_cfuncs)
assume a1: "successor \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c"
assume a2: "successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c"
have "\<forall>c ca. \<not> c \<in>\<^sub>c \<nat>\<^sub>c \<or> \<not> ca \<in>\<^sub>c \<nat>\<^sub>c \<or> c \<cdot>\<^sub>\<nat> ca \<in>\<^sub>c \<nat>\<^sub>c"
  using mult_closure by blast
  then show ?thesis
    using a2 a1 add_associates assms(3) assms(4) mult_right_distributivity by force
qed




lemma mult_even_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  shows   "(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> n) = m \<cdot>\<^sub>\<nat> n"
proof - 
  have " m \<cdot>\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) \<cdot>\<^sub>\<nat> n"
    using assms(3) by presburger
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> n)"
    by (typecheck_cfuncs, simp add: assms(2) assms(3) mult_associative)
  then show ?thesis
    by (simp add: calculation)
qed

lemma mult_odds_is_odd:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
  assumes "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "\<exists>l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m \<cdot>\<^sub>\<nat> n"
proof - 
  obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
    using assms(3) by blast
  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
    using assms(4) by blast
  have "m \<cdot>\<^sub>\<nat> n = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)) +\<^sub>\<nat> 
                 (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j)  \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) +\<^sub>\<nat>
               ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)  \<cdot>\<^sub>\<nat>  (successor \<circ>\<^sub>c zero) +\<^sub>\<nat> 
                (successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat>   (successor \<circ>\<^sub>c zero)"
    using FOIL_2 j_def k_def mult_closure succ_n_type zero_type by auto
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k))) +\<^sub>\<nat> 
                   ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))) +\<^sub>\<nat>
                   ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (k \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))) +\<^sub>\<nat> 
                (successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat>   (successor \<circ>\<^sub>c zero)"
    by (simp add: j_def k_def mult_associative mult_closure succ_n_type zero_type)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> 
        ( (j \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)) +\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) +\<^sub>\<nat> (k \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))))
        +\<^sub>\<nat>  (successor \<circ>\<^sub>c zero)"
    by (smt assms(2) j_def k_def mult_closure mult_right_distributivity s0_is_right_id succ_n_type zero_type)
  then show ?thesis
    by (typecheck_cfuncs, metis add_type calculation j_def k_def mult_closure)
qed

lemma EXISTS_zero_nth_even:
  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<t>"
proof -
  have  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero
      = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: comp_associative2 sharp_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>cone\<^esub>\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis cfunc_cross_prod_def cfunc_type_def right_cart_proj_type terminal_func_unique)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one, (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
  also have "... = \<t>"
  proof (rule exists_true_implies_EXISTS_true)
    show "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "\<exists>x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
    proof (typecheck_cfuncs, rule_tac x="zero" in exI, auto)
      have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero
        = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c zero, zero\<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = \<t>"
        using eq_pred_iff_eq nth_even_zero by (typecheck_cfuncs, blast)
      then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
        using calculation by auto
    qed
  qed
  then show ?thesis
    using calculation by auto
qed

lemma not_EXISTS_zero_nth_odd:
  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<f>"
proof -
  have  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: comp_associative2 sharp_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_odd \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>cone\<^esub>\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis cfunc_cross_prod_def cfunc_type_def right_cart_proj_type terminal_func_unique)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one, (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one\<rangle> )\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp)
  also have "... = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
  also have "... = \<f>"
  proof -
    have "\<nexists> x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
    proof auto
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c"

      assume "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
      then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c x = \<t>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c x, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x\<rangle> = \<t>"
        by (typecheck_cfuncs_prems, auto simp add: cfunc_prod_comp comp_associative2)
      then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c x, zero\<rangle> = \<t>"
        by (typecheck_cfuncs_prems, metis cfunc_type_def id_right_unit id_type one_unique_element)
      then have "nth_odd \<circ>\<^sub>c x = zero"
        using eq_pred_iff_eq by (typecheck_cfuncs_prems, blast)
      then have "successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> x) = zero"
        using  nth_odd_is_succ_times_twoB by (typecheck_cfuncs, auto)
      then show "False"
        by (metis mult_closure succ_n_type x_type zero_is_not_successor zero_type)
    qed
    then have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<noteq> \<t>"
      using EXISTS_true_implies_exists_true by (typecheck_cfuncs, blast)
    then show "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<f>"
      using true_false_only_truth_values by (typecheck_cfuncs, blast)
  qed
  then show ?thesis
    using calculation by auto
qed

definition halve_with_parity :: "cfunc" where
  "halve_with_parity = (THE u. u: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and> 
    u \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero \<and>
    (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma halve_with_parity_def2:
  "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and> 
    halve_with_parity \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero \<and>
    (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity = halve_with_parity \<circ>\<^sub>c successor"
  by (unfold halve_with_parity_def, rule theI', typecheck_cfuncs, rule natural_number_object_property2, auto)

lemma halve_with_parity_type[type_rule]:
  "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
  by (simp add: halve_with_parity_def2)

lemma halve_with_parity_zero:
  "halve_with_parity \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  by (simp add: halve_with_parity_def2)

lemma halve_with_parity_successor:
  "(right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity = halve_with_parity \<circ>\<^sub>c successor"
  by (simp add: halve_with_parity_def2)

lemma halve_with_parity_nth_even:
  "halve_with_parity \<circ>\<^sub>c nth_even = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c", where f="(left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)"])
  show "halve_with_parity \<circ>\<^sub>c nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "left_coproj \<nat>\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "(left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = halve_with_parity \<circ>\<^sub>c nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c zero"
      by (simp add: nth_even_zero)
    also have "... = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_zero)
    then show ?thesis
      using calculation by auto
  qed

  show "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor =
      ((left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = halve_with_parity \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (simp add: nth_even_successor)
    also have "... = ((halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (simp add: halve_with_parity_def2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c ((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c nth_even"
      by (simp add: halve_with_parity_def2)
    also have "... = ((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)))
        \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
        \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    then show ?thesis
      using calculation by auto
  qed

  show "left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor =
    (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
qed

lemma halve_with_parity_nth_odd:
  "halve_with_parity \<circ>\<^sub>c nth_odd = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c", where f="(left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)"])
  show "halve_with_parity \<circ>\<^sub>c nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "right_coproj \<nat>\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "(left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = halve_with_parity \<circ>\<^sub>c nth_odd \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c successor \<circ>\<^sub>c zero"
      by (simp add: nth_odd_def2)
    also have "... = (halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_def2)
    also have "... = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_def2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    then show ?thesis
      using calculation by auto
  qed

  show "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor =
      (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = halve_with_parity \<circ>\<^sub>c nth_odd \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (simp add: nth_odd_successor)
    also have "... = ((halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity) 
        \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (simp add: halve_with_parity_successor)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)
        \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c successor)) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)
        \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity)) \<circ>\<^sub>c nth_odd"
      by (simp add: halve_with_parity_successor)
    also have "... = (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)
        \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    then show ?thesis
      using calculation by auto
  qed

  show "right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor =
      (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<amalg> (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
qed

lemma nth_even_nth_odd_halve_with_parity:
  "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity = id \<nat>\<^sub>c"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f="successor"])
  show "nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  proof -
    have "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero = nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<amalg> nth_odd \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_zero)
    also have "... = (nth_even \<amalg> nth_odd \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      using id_left_unit2 nth_even_def2 zero_type by auto
    then show ?thesis
      using calculation by auto
  qed

  show "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity"
  proof -
    have "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor = nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<amalg> nth_odd \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity"
      by (simp add: halve_with_parity_successor)
    also have "... = (nth_even \<amalg> nth_odd \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_odd \<amalg> (nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> ((successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even) \<circ>\<^sub>c halve_with_parity"
      by (simp add: nth_even_successor nth_odd_is_succ_nth_even)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> (successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c halve_with_parity"
      by (simp add: nth_odd_is_succ_nth_even)
    also have "... = successor \<circ>\<^sub>c nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: cfunc_coprod_comp comp_associative2)
    then show ?thesis
      using calculation by auto
  qed

  show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
    using id_left_unit2 id_right_unit2 successor_type by auto
qed

lemma halve_with_parity_nth_even_nth_odd:
  "halve_with_parity \<circ>\<^sub>c (nth_even \<amalg> nth_odd) = id (\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  by (typecheck_cfuncs, smt cfunc_coprod_comp halve_with_parity_nth_even halve_with_parity_nth_odd id_coprod)

lemma even_odd_iso:
  "isomorphism (nth_even \<amalg> nth_odd)"
proof (unfold isomorphism_def, rule_tac x=halve_with_parity in exI, auto)
  show "domain halve_with_parity = codomain (nth_even \<amalg> nth_odd)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "codomain halve_with_parity = domain (nth_even \<amalg> nth_odd)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "halve_with_parity \<circ>\<^sub>c nth_even \<amalg> nth_odd = id\<^sub>c (domain (nth_even \<amalg> nth_odd))"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: halve_with_parity_nth_even_nth_odd)
  show "nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity = id\<^sub>c (domain halve_with_parity)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: nth_even_nth_odd_halve_with_parity)
qed

lemma halve_with_parity_iso:
  "isomorphism halve_with_parity"
proof (unfold isomorphism_def, rule_tac x="nth_even \<amalg> nth_odd" in exI, auto)
  show "domain (nth_even \<amalg> nth_odd) = codomain halve_with_parity"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "codomain (nth_even \<amalg> nth_odd) = domain halve_with_parity"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto)
  show "nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity = id\<^sub>c (domain halve_with_parity)"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: nth_even_nth_odd_halve_with_parity)
  show "halve_with_parity \<circ>\<^sub>c nth_even \<amalg> nth_odd = id\<^sub>c (domain (nth_even \<amalg> nth_odd))"
    by (typecheck_cfuncs, unfold cfunc_type_def, auto simp add: halve_with_parity_nth_even_nth_odd)
qed

definition halve :: "cfunc" where
  "halve = (id \<nat>\<^sub>c \<amalg> id \<nat>\<^sub>c) \<circ>\<^sub>c halve_with_parity"

lemma halve_type[type_rule]:
  "halve : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  unfolding halve_def by typecheck_cfuncs

lemma halve_nth_even:
  "halve \<circ>\<^sub>c nth_even = id \<nat>\<^sub>c"
  unfolding halve_def by (typecheck_cfuncs, smt comp_associative2 halve_with_parity_nth_even left_coproj_cfunc_coprod)

lemma halve_nth_odd:
  "halve \<circ>\<^sub>c nth_odd = id \<nat>\<^sub>c"
  unfolding halve_def by (typecheck_cfuncs, smt comp_associative2 halve_with_parity_nth_odd right_coproj_cfunc_coprod)

lemma is_even_def3:
  "is_even = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
proof (rule natural_number_object_func_unique[where X=\<Omega>, where f=NOT])
  show "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "NOT : \<Omega> \<rightarrow> \<Omega>"
    by typecheck_cfuncs

  show "is_even \<circ>\<^sub>c zero = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
  proof -
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero
      = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative halve_with_parity_zero)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
    also have "... = \<t>"
      using comp_associative2 is_even_def2 is_even_nth_even_true nth_even_def2 by (typecheck_cfuncs, force)
    also have "... = is_even \<circ>\<^sub>c zero"
      by (simp add: is_even_zero)
    then show ?thesis
      using calculation by auto
  qed

  show "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
    by (simp add: is_even_successor)

  show "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
  proof -
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor
      = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 halve_with_parity_successor)
    also have "... = 
        (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c)
          \<amalg> 
        ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
          \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2)
    also have "... = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    also have "... = ((NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: NOT_false_is_true NOT_true_is_false comp_associative2)
    also have "... = NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 terminal_func_unique)
    then show ?thesis
      using calculation by auto
  qed
qed

lemma is_odd_def3:
  "is_odd = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
proof (rule natural_number_object_func_unique[where X=\<Omega>, where f=NOT])
  show "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "NOT : \<Omega> \<rightarrow> \<Omega>"
    by typecheck_cfuncs

  show "is_odd \<circ>\<^sub>c zero = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
  proof -
    have "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero
      = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative halve_with_parity_zero)
    also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
    also have "... = \<f>"
      using comp_associative2 is_odd_nth_even_false is_odd_type is_odd_zero nth_even_def2 by (typecheck_cfuncs, force)
    also have "... = is_odd \<circ>\<^sub>c zero"
      by (simp add: is_odd_def2)
    then show ?thesis
      using calculation by auto
  qed

  show "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
    by (simp add: is_odd_successor)

  show "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    NOT \<circ>\<^sub>c (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
  proof -
    have "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor
      = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<amalg> (left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 halve_with_parity_successor)
    also have "... = 
        (((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c)
          \<amalg> 
        ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))
          \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2)
    also have "... = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    also have "... = ((NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: NOT_false_is_true NOT_true_is_false comp_associative2)
    also have "... = NOT \<circ>\<^sub>c (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 terminal_func_unique)
    then show ?thesis
      using calculation by auto
  qed
qed



lemma nth_even_or_nth_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n) \<or> (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c m = n)"
proof -
  have "(\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m)
      \<or> (\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m)"
    by (rule coprojs_jointly_surj, insert assms, typecheck_cfuncs)
  then show ?thesis
  proof auto
    fix m
    assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    assume "halve_with_parity \<circ>\<^sub>c n = left_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m"
    then have "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = ((nth_even \<amalg> nth_odd) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c m"
      by (typecheck_cfuncs, smt assms comp_associative2)
    then have "n = nth_even \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs_prems, smt comp_associative2 halve_with_parity_nth_even id_left_unit2 nth_even_nth_odd_halve_with_parity)
    then show "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n"
      using m_type by auto
  next
    fix m
    assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    assume "halve_with_parity \<circ>\<^sub>c n = right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m"
    then have "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = ((nth_even \<amalg> nth_odd) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c m"
      by (typecheck_cfuncs, smt assms comp_associative2)
    then have "n = nth_odd \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs_prems, smt comp_associative2 halve_with_parity_nth_odd id_left_unit2 nth_even_nth_odd_halve_with_parity)
    then show "\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> nth_odd \<circ>\<^sub>c m \<noteq> n \<Longrightarrow> \<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n"
      using m_type by auto
  qed
qed

lemma even_or_odd2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m)) \<or> 
         (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n =              (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m) "
proof -
  have "(\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n) \<or> (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c m = n)"
    by (simp add: assms nth_even_or_nth_odd)
  then show ?thesis
  proof auto
    fix m 
    assume m_type: "m \<in>\<^sub>c \<nat>\<^sub>c"

    have "nth_even \<circ>\<^sub>c m = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m"
      by (simp add: m_type nth_even_is_times_twoB)
    then show "\<forall>ma. ma \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> nth_even \<circ>\<^sub>c m \<noteq> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ma \<Longrightarrow>
        \<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = successor \<circ>\<^sub>c (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k"
      using m_type by auto
  next
    fix m 
    assume m_type: "m \<in>\<^sub>c \<nat>\<^sub>c"

    have "nth_odd \<circ>\<^sub>c m = successor \<circ>\<^sub>c (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m"
      by (simp add: m_type nth_odd_is_succ_times_twoB)
    then show "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c m = successor \<circ>\<^sub>c (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k"
      using m_type by auto
  qed
qed



lemma not_even_and_odd2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<not>((\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m)) \<and> 
           (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n =              (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m))"
  by (smt (z3) assms comp_associative2 halve_nth_even halve_nth_odd halve_type id_left_unit2 n_neq_succ_n nth_even_is_times_twoB nth_even_type nth_odd_def2 nth_odd_is_succ_times_twoB)


lemma is_even_exists_nth_even:
  assumes "is_even \<circ>\<^sub>c n = \<t>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c m"
proof (rule ccontr)
  assume "\<nexists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c m"
  then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "n = nth_odd \<circ>\<^sub>c m"
    using n_type nth_even_or_nth_odd by blast
  then have "is_even \<circ>\<^sub>c nth_odd \<circ>\<^sub>c m = \<t>"
    using assms(1) by blast
  then have "is_odd \<circ>\<^sub>c nth_odd \<circ>\<^sub>c m = \<f>"
    using NOT_true_is_false NOT_type comp_associative2 is_even_def2 is_odd_not_is_even n_def n_type by fastforce
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<f>"
    by (typecheck_cfuncs_prems, smt comp_associative2 is_odd_nth_odd_true terminal_func_type true_func_type)
  then have "\<t> = \<f>"
    by (typecheck_cfuncs_prems, metis id_right_unit2 id_type one_unique_element)
  then show False
    using true_false_distinct by auto
qed

lemma is_odd_exists_nth_odd:
  assumes "is_odd \<circ>\<^sub>c n = \<t>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c m"
proof (rule ccontr)
  assume "\<nexists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c m"
  then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "n = nth_even \<circ>\<^sub>c m"
    using n_type nth_even_or_nth_odd by blast
  then have "is_odd \<circ>\<^sub>c nth_even \<circ>\<^sub>c m = \<t>"
    using assms(1) by blast
  then have "is_even \<circ>\<^sub>c nth_even \<circ>\<^sub>c m = \<f>"
    using NOT_true_is_false NOT_type comp_associative2 is_even_not_is_odd is_odd_def2 n_def n_type by fastforce
  then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<f>"
    by (typecheck_cfuncs_prems, smt comp_associative2 is_even_nth_even_true terminal_func_type true_func_type)
  then have "\<t> = \<f>"
    by (typecheck_cfuncs_prems, metis id_right_unit2 id_type one_unique_element)
  then show False
    using true_false_distinct by auto
qed







lemma add_evens_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_even \<circ>\<^sub>c m = \<t>" "is_even \<circ>\<^sub>c n = \<t>"
  shows "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
proof-
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_even \<circ>\<^sub>c p"
    using assms(1) assms(3) is_even_exists_nth_even by blast
  obtain q where n_def: "q \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c q"
    using assms(2) assms(4) is_even_exists_nth_even by blast
  have m_def2: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p)"
    by (simp add: m_def nth_even_is_times_twoB)
  have n_def2: "n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q)"
    by (simp add: n_def nth_even_is_times_twoB)
  have "m +\<^sub>\<nat> n  = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (p +\<^sub>\<nat> q))"  
    using m_def m_def2 mult_right_distributivity n_def n_def2 by (typecheck_cfuncs, auto)
  then have "m +\<^sub>\<nat> n  = nth_even \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    by (simp add: add_type m_def n_def nth_even_is_times_twoB)
  then have "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = (is_even \<circ>\<^sub>c  nth_even) \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    by (typecheck_cfuncs, metis  comp_associative2 m_def n_def)
  also have "... =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    by (simp add: is_even_nth_even_true)
  also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    using comp_associative2 m_def n_def by (typecheck_cfuncs, fastforce)
  also have "... = \<t> \<circ>\<^sub>c id(one)"
    by (typecheck_cfuncs, metis m_def n_def terminal_func_unique)
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed

lemma add_odds_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_odd \<circ>\<^sub>c m = \<t>" "is_odd \<circ>\<^sub>c n = \<t>"
  shows "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
proof-
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_odd \<circ>\<^sub>c p"
    using assms(1) assms(3) is_odd_exists_nth_odd by blast
  obtain q where n_def: "q \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c q"
    using assms(2) assms(4) is_odd_exists_nth_odd by blast
  have m_def2: "m = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) "
    using m_def nth_odd_is_succ_times_twoB by blast
  then have m_def3: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right m_def m_def2 by (typecheck_cfuncs, auto)
  have n_def2: "n = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q)"
    using n_def nth_odd_is_succ_times_twoB by blast
  have n_def3: "n= ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right n_def n_def2 by (typecheck_cfuncs, auto)
  have "(m +\<^sub>\<nat> n) = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using add_odds_is_even assms(1) assms(2) m_def m_def3 n_def n_def3 by auto  
  then have "(m +\<^sub>\<nat> n) = nth_even \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add:  m_def n_def nth_even_is_times_twoB)
  then have "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = (is_even \<circ>\<^sub>c  nth_even) \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using   comp_associative2 m_def n_def by (typecheck_cfuncs, auto)
  also have  "...  =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add:  is_even_nth_even_true)
  also have "...  =  \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using  comp_associative2 m_def n_def by (typecheck_cfuncs, auto)
  also have "... = \<t> \<circ>\<^sub>c id(one)"
    by (typecheck_cfuncs, metis m_def n_def terminal_func_unique)
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed

lemma add_mixed_is_odd2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_odd \<circ>\<^sub>c m = \<t>" "is_even \<circ>\<^sub>c n = \<t>"
  shows "is_odd \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
  by (typecheck_cfuncs, smt add_evens_is_even2 add_respects_succ3 assms cfunc_type_def comp_associative comp_type is_even_def2 is_odd_not_is_even successor_type)

lemma mult_evens_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_even \<circ>\<^sub>c m = \<t>" 
  shows "is_even \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = \<t>"
proof - 
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_even \<circ>\<^sub>c p"
    using assms(1,3) is_even_exists_nth_even by blast
  have m_def2: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p)"
    by (simp add: m_def nth_even_is_times_twoB)
  then have mn_def: "m \<cdot>\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> n))"
    by (simp add: assms(2) m_def mult_associative succ_n_type zero_type)
  then have "(m \<cdot>\<^sub>\<nat> n) = nth_even \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    by (simp add: assms(2) m_def mult_closure nth_even_is_times_twoB)
  then have "is_even \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = (is_even \<circ>\<^sub>c  nth_even) \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    by (typecheck_cfuncs, metis assms(2) comp_associative2 m_def)
  also have "... =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    by (simp add: is_even_nth_even_true)
  also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    using assms(2) comp_associative2 m_def by (typecheck_cfuncs, fastforce)
  also have "... = \<t> \<circ>\<^sub>c id(one)"
    by (typecheck_cfuncs, metis assms(2) m_def terminal_func_unique)
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed

lemma mult_odds_is_odd2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_odd \<circ>\<^sub>c m = \<t>" "is_odd \<circ>\<^sub>c n = \<t>" 
  shows "is_odd \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = \<t>"
proof - 
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_odd \<circ>\<^sub>c p"
    using assms(1,3) is_odd_exists_nth_odd by blast
  obtain q where n_def: "q \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c q"
    using assms(2,4) is_odd_exists_nth_odd by blast
  have m_def2: "m = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) "
    using m_def nth_odd_is_succ_times_twoB by blast
  then have m_def3: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right m_def m_def2 by (typecheck_cfuncs, auto)
  then have m_def4: "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
    using m_def by blast
  
  have n_def2: "n = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q)"
    using n_def nth_odd_is_succ_times_twoB by blast
  have n_def3: "n= ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right n_def n_def2 by (typecheck_cfuncs, auto)
  then have n_def4: "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
    using n_def by blast
  
  have "\<exists>l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m \<cdot>\<^sub>\<nat> n"
    by (rule mult_odds_is_odd, simp_all add: assms m_def4 n_def4)
  then obtain l where mn_def: "l \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m \<cdot>\<^sub>\<nat> n"
    by blast
  then have "m \<cdot>\<^sub>\<nat> n = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l)"
    using add_respects_succ1 add_respects_zero_on_right mn_def by (typecheck_cfuncs, auto)
  then have "m \<cdot>\<^sub>\<nat> n = nth_odd \<circ>\<^sub>c l"
    by (simp add: mn_def nth_odd_is_succ_times_twoB)
  then have "is_odd \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = (is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c l"
    using comp_associative2 mn_def by (typecheck_cfuncs, auto)
  also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c l"
    by (simp add: is_odd_nth_odd_true)
  also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c l"
    using comp_associative2 mn_def by (typecheck_cfuncs, auto)
  also have "... = \<t> \<circ>\<^sub>c id(one)"
    using id_type mn_def one_unique_element terminal_func_comp terminal_func_type by fastforce
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed


lemma prod_of_consecutive_nats_is_even:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "is_even \<circ>\<^sub>c (n \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n)) = \<t>"
  by (metis add_odds_is_even2 assms even_or_odd mult_evens_is_even2 mult_odds_is_odd2 mult_respects_succ_right mult_type succ_n_type)       



lemma powers_of_two_are_even:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" 
  assumes "n \<noteq> zero"
  shows "is_even \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero,n\<rangle>) = \<t>"
proof - 
  obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and j_def: "n = successor \<circ>\<^sub>c j"
    using assms nonzero_is_succ by blast
  have "exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero,n\<rangle> = exp_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero, (successor  \<circ>\<^sub>c zero) +\<^sub>\<nat> j\<rangle>"
    by (typecheck_cfuncs, metis add_commutes add_respects_succ3 add_respects_zero_on_right j_def)
  also have "... = ((successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero) ^\<^sub>\<nat> (successor  \<circ>\<^sub>c zero)) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero) ^\<^sub>\<nat> j)"
    using exp_def exp_right_dist by (typecheck_cfuncs, force)
  also have "... = (successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero)  \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero) ^\<^sub>\<nat> j)"
    by (typecheck_cfuncs, simp add: exp_respects_one_right)
  then show ?thesis
    by (metis calculation exp_closure j_type mult_evens_is_even2 prod_of_consecutive_nats_is_even s0_is_left_id succ_n_type zero_type)
qed


lemma three_is_odd:
  "is_odd \<circ>\<^sub>c (successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero) = \<t>"
  by (typecheck_cfuncs, metis (full_types) comp_associative2 is_even_not_is_odd is_odd_def2 prod_of_consecutive_nats_is_even s0_is_left_id)





lemma powers_of_three_are_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero,n\<rangle>) = \<t>"
proof - 
  have main_result: "is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle>) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  proof(rule natural_number_object_func_unique[where X = "\<Omega>", where f = "id \<Omega>" ]) 
    show func_type[type_rule]: "is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle>) : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "(is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
    proof - 
      have "(is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = 
             is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero"
        using comp_associative2 by (typecheck_cfuncs, force)
      also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle> "
        using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
      also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero, zero\<rangle>"
        by (typecheck_cfuncs, metis beta_N_succ_nEqs_Id1 id_left_unit2 id_right_unit2 terminal_func_comp)
      also have "... = is_odd \<circ>\<^sub>c (successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)"
        by (typecheck_cfuncs, metis even_or_odd exp_def exp_respects_Zero_Left mult_evens_is_even2 not_even_and_odd s0_is_left_id three_is_odd)
      also have "... = \<t>"
        by (simp add: three_is_odd)
      then show ?thesis
        by (metis calculation cfunc_type_def comp_associative is_even_def2 is_even_nth_even_true nth_even_def2 zero_type)
    qed
    show "(is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =  id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<Omega>"])
      show "(is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
      proof - 
        fix m
        assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
        have " (id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m = 
                (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>)  \<circ>\<^sub>c m"  
          using id_left_unit2 by (typecheck_cfuncs, presburger)
        also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c m"
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
        also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m\<rangle>"
          using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
        also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,m\<rangle>"
          by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
        also have "... = ((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m"
        proof(cases "is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,m\<rangle> = \<t>")
          assume real_case: "is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,m\<rangle> = \<t>"  (*The only real case*)
          have "((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m = 
                 (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "...  =  (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis add_commutes add_respects_succ3 add_respects_zero_on_left)
          also have "... =  is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
          also have "... =  is_odd \<circ>\<^sub>c ((exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m) \<cdot>\<^sub>\<nat> 
                                       (exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)))"
            by (typecheck_cfuncs, metis exp_apply1 exp_right_dist)
          also have "... = \<t>"
            by (typecheck_cfuncs, metis real_case exp_apply1 exp_def exp_respects_one_right mult_odds_is_odd2 three_is_odd)
          then show ?thesis
            using calculation real_case by presburger
        next
          assume "is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero,m\<rangle> \<noteq> \<t>"
          then have fake_case: "is_even \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero,m\<rangle> = \<t>"   (*The fake case... only difference is final line!*)
            by (metis even_or_odd exp_closure exp_def m_type succ_n_type zero_type)
          have "((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m = 
                 (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "...  =  (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis add_commutes add_respects_succ3 add_respects_zero_on_left)
          also have "... =  is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
          also have "... =  is_odd \<circ>\<^sub>c ((exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m) \<cdot>\<^sub>\<nat> 
                                       (exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)))"
            by (typecheck_cfuncs, metis exp_apply1 exp_right_dist)
          also have "... = \<f>"
            by (typecheck_cfuncs, metis cart_prod_extract_right fake_case mult_evens_is_even2 not_even_and_odd true_false_only_truth_values)
          then show ?thesis
            by (metis NOT_true_is_false NOT_type calculation cfunc_type_def comp_associative exp_closure exp_def fake_case is_even_type is_odd_not_is_even m_type succ_n_type zero_type)
        qed
        then show "((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m"
          by (simp add: calculation)
      qed
    qed
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
  qed
  have "is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero,n\<rangle>) = 
        (is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle>)) \<circ>\<^sub>c n"
    using assms cfunc_type_def comp_associative exp_apply1 exp_def by (typecheck_cfuncs, fastforce)
  then show ?thesis
    by (typecheck_cfuncs, smt (z3) main_result assms beta_N_succ_nEqs_Id1 comp_associative2 id_right_unit2 terminal_func_comp terminal_func_type)
qed




end