theory ETCS_Parity
  imports ETCS_Add ETCS_Mult ETCS_Pred ETCS_Quantifier
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

lemma even_or_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(is_even \<circ>\<^sub>c n = \<t>) \<or> (is_odd \<circ>\<^sub>c n = \<t>)"
proof(auto)
  assume not_odd: "is_odd \<circ>\<^sub>c n \<noteq> \<t>"
  show "is_even \<circ>\<^sub>c n = \<t>"
    using assms by (typecheck_cfuncs, metis NOT_false_is_true NOT_type cfunc_type_def comp_associative is_odd_not_is_even not_odd true_false_only_truth_values)
qed

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
      by (typecheck_cfuncs, smt beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 successor_type terminal_func_comp)
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
      by (typecheck_cfuncs, smt beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 successor_type terminal_func_comp)
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
  assumes "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  assumes "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k = n"
  shows   "\<exists>l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l = m +\<^sub>\<nat> n"
proof - 
  obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
    using assms(3) by blast
  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k = n"
    using assms(4) by blast
  have m_pls_n: "m +\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)"
    using j_def k_def by fastforce
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)"
    by (simp add: j_def k_def mult_right_distributivity succ_n_type zero_type)
  then show ?thesis
    using  add_type j_def k_def by auto
qed


lemma add_odds_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
  assumes "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "\<exists>l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l = m +\<^sub>\<nat> n"
proof - 
  obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
    using assms(3) by blast
  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
    using assms(4) by blast

  have m_pls_n: "m +\<^sub>\<nat> n = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) +\<^sub>\<nat> (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using j_def k_def by fastforce
  also have "... = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (simp add: add_associates_mix_commutes j_def k_def mult_closure succ_n_type zero_type)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (simp add: j_def k_def mult_right_distributivity succ_n_type zero_type)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)"
    using one_plus_one_is_two by auto
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (simp add: s0_is_right_id succ_n_type zero_type)
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ((j +\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: j_def k_def mult_right_distributivity)
  then show ?thesis
    by (typecheck_cfuncs, metis  add_type calculation j_def k_def)
qed


lemma add_mixed_is_odd: 
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  assumes "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "\<exists>l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m +\<^sub>\<nat> n"
  apply typecheck_cfuncs
proof -
  assume a1: "successor \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c"
  assume a2: "successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c"
  obtain cc :: cfunc where
    "cc \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> cc = m"
  using assms(3) by blast
  then show ?thesis
    using a2 a1 by (metis add_associates add_evens_is_even assms(4) mult_type)
qed



lemma mult_even_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  shows   "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k = m \<cdot>\<^sub>\<nat> n"
proof - 
  obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
    using assms(3) by blast
  have " m \<cdot>\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) \<cdot>\<^sub>\<nat> n"
    by (simp add: j_def)
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> n)"
    by (simp add: assms(2) j_def mult_associative succ_n_type zero_type)
  then show ?thesis
    using assms(2) j_def mult_closure by auto
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
        by (typecheck_cfuncs, smt beta_N_succ_mEqs_Id1 cfunc_prod_comp comp_associative2 id_right_unit2 successor_type terminal_func_comp)
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
  have  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero
      = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
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

lemma nth_even_or_nth_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists> m. nth_even \<circ>\<^sub>c m = n) \<or> (\<exists> m. nth_odd \<circ>\<^sub>c m = n)"
proof auto
  have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f id \<nat>\<^sub>c))\<^sup>\<sharp> = NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_odd \<times>\<^sub>f id \<nat>\<^sub>c))\<^sup>\<sharp>"
  proof (rule natural_number_object_func_unique[where f="NOT", where X=\<Omega>])
    show "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "NOT : \<Omega> \<rightarrow> \<Omega>"
      by typecheck_cfuncs

    show "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero =
        (NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero"
    proof -
      have  "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<t>"
        by (simp add: EXISTS_zero_nth_even)
      also have "... = NOT \<circ>\<^sub>c \<f>"
        by (simp add: NOT_false_is_true)
      also have "... = NOT \<circ>\<^sub>c (EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero"
        by (simp add: not_EXISTS_zero_nth_odd)
      also have "... = (NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_odd \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, simp add: comp_associative2)
      then show ?thesis
        using calculation by auto
    qed

    show "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c successor =
        NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof (rule one_separator[where X="\<nat>\<^sub>c", where Y=\<Omega>])
      show "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
    next
      fix n
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      have "(\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = successor \<circ>\<^sub>c n) = (\<nexists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n)"
      proof(auto) 
        fix m j
        assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
        assume nth_even_m_is: "nth_even \<circ>\<^sub>c m = successor \<circ>\<^sub>c nth_even \<circ>\<^sub>c j"
        assume j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
        assume n_is_nth_even_j: "n = nth_even \<circ>\<^sub>c j"
       
        have "n = nth_even \<circ>\<^sub>c m"
          by (typecheck_cfuncs, smt comp_associative2 false_func_type is_even_def2 is_even_not_is_odd is_even_nth_even_true is_even_nth_odd_false is_odd_def2 is_odd_not_is_even j_type nth_even_is_times_two nth_even_m_is nth_odd_def2 nth_odd_is_succ_times_two successor_type terminal_func_comp terminal_func_type true_false_distinct true_func_type zero_type)
        have "nth_even \<circ>\<^sub>c m = successor \<circ>\<^sub>c n"
          by (simp add: n_is_nth_even_j nth_even_m_is)
        then have "n = successor \<circ>\<^sub>c n "
          using \<open>n = nth_even \<circ>\<^sub>c m\<close> by blast
        then have False
          using n_neq_succ_n n_type by auto
      next
        assume "\<forall>m. m \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> nth_even \<circ>\<^sub>c m \<noteq> n"
        oops


lemma is_even_def3:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "is_even = EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f id \<nat>\<^sub>c))\<^sup>\<sharp>)"
  proof (rule natural_number_object_func_unique[where f="NOT", where X=\<Omega>])
    show "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "NOT : \<Omega> \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "is_even \<circ>\<^sub>c zero = (EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero"
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
            by (typecheck_cfuncs, smt beta_N_succ_mEqs_Id1 cfunc_prod_comp comp_associative2 id_right_unit2 successor_type terminal_func_comp)
          also have "... = \<t>"
            using eq_pred_iff_eq nth_even_zero by (typecheck_cfuncs, blast)
          then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
            using calculation by auto
        qed
      qed
      also have "... = is_even \<circ>\<^sub>c zero"
        by (simp add: is_even_zero)
      then show ?thesis
        using calculation by auto
    qed

    show "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c successor =
      NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof (rule one_separator[where X="\<nat>\<^sub>c", where Y="\<Omega>"])
      show "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
    next
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c"
      have "(\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = successor \<circ>\<^sub>c x) = (\<nexists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = x)"
      proof auto
        fix m1 m2
        assume m1_type[type_rule]: "m1 \<in>\<^sub>c \<nat>\<^sub>c" and m2_type[type_rule]: "m2 \<in>\<^sub>c \<nat>\<^sub>c"

        assume "nth_even \<circ>\<^sub>c m1 = successor \<circ>\<^sub>c nth_even \<circ>\<^sub>c m2"
        then have "is_even \<circ>\<^sub>c nth_even \<circ>\<^sub>c m1 = is_even \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even \<circ>\<^sub>c m2"
          by auto
        then have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c m1 = (is_even \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even \<circ>\<^sub>c m2"
          by (typecheck_cfuncs, smt comp_associative2)
        then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m1 = (NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c nth_even \<circ>\<^sub>c m2"
          by (simp add: is_even_nth_even_true is_even_successor)
        then have "\<t> = NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c m2"
          by (typecheck_cfuncs_prems, smt cfunc_type_def comp_associative id_right_unit id_type
              is_even_nth_even_true m1_type one_unique_element terminal_func_comp terminal_func_type)
        then have "\<t> = NOT \<circ>\<^sub>c \<t>"
          by (typecheck_cfuncs_prems, smt comp_associative2 is_even_nth_even_true terminal_func_comp terminal_func_type)
        then show "False"
          using NOT_true_is_false true_false_distinct by auto
      next
            
          


        thm is_even_successor is_even_nth_even_true
      

      show "((EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (NOT \<circ>\<^sub>c EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
      

(*shows "OR \<nat>\<^sub>c \<circ>\<^sub>c \<langle>EXISTS \<nat>\<^sub>c \<circ>\<^sub>c  ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f id \<nat>\<^sub>c))\<^sup>\<sharp>),
                  EXISTS \<nat>\<^sub>c \<circ>\<^sub>c  ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_odd \<times>\<^sub>f id \<nat>\<^sub>c))\<^sup>\<sharp>)\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
*)


(*Use the above result to prove that if a number n is_even then in fact there exists k such that n=2k*)

        oops
lemma add_evens_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_even \<circ>\<^sub>c m = \<t>" "is_even \<circ>\<^sub>c n = \<t>"
  shows "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
proof(rule ccontr)
  assume BWOC: "is_even \<circ>\<^sub>c m +\<^sub>\<nat> n \<noteq> \<t>"
  then have thats_odd: "is_odd \<circ>\<^sub>c m +\<^sub>\<nat> n = \<t>"
    using assms BWOC even_or_odd by (typecheck_cfuncs,blast)
  then have False
    using assms apply typecheck_cfuncs
    oops

(*
lemma is_even_def4:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(is_even \<circ>\<^sub>c n = \<t>) = (\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = n)"
proof(auto)  
  assume "is_even \<circ>\<^sub>c n = \<t>"
  show "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = n"
*)  
  










  
  







(*lemma 
  assumes "is_even \<circ>\<^sub>c y = \<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>" and "y : A \<rightarrow> \<nat>\<^sub>c"
  shows "\<exists> x. x : A \<rightarrow> \<nat>\<^sub>c \<and> y = nth_even \<circ>\<^sub>c x"
proof -
  have "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (nth_even \<times>\<^sub>f id \<nat>\<^sub>c))\<^sup>\<sharp>) = is_even"
  proof (rule natural_number_object_func_unique[where f="NOT", where X=\<Omega>])
    show "EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "NOT : \<Omega> \<rightarrow> \<Omega>"
      by typecheck_cfuncs

    show "(EXISTS \<nat>\<^sub>c \<circ>\<^sub>c (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c nth_even \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c zero = is_even \<circ>\<^sub>c zero"
    proof -
  *)    
      

(*lemma odd_even_iso:
  "isomorphism (nth_odd \<amalg> nth_even)"
proof (rule epi_mon_is_iso)
  show "epimorphism (nth_odd \<amalg> nth_even)"
  proof (rule surjective_is_epimorphism, typecheck_cfuncs, unfold surjective_def2, auto)
    fix y
    assume y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c"

    show "\<exists>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and> nth_odd \<amalg> nth_even \<circ>\<^sub>c x = y"
    proof (cases "is_even \<circ>\<^sub>c y = \<t>")
      assume y_is_even: "is_even \<circ>\<^sub>c y = \<t>"
      then show "\<exists>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and> nth_odd \<amalg> nth_even \<circ>\<^sub>c x = y"
        apply (rule_tac x="right_coproj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c "

    oops*)



end