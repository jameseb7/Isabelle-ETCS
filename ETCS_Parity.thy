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

lemma even_or_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists>j. (j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = n)) \<or> 
         (\<exists>j. (j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n))"
proof(safe)
  assume "\<nexists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and>
        (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  show "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = n"
  proof(cases "n = zero")
    assume "n = zero" 
    have "zero \<in>\<^sub>c \<nat>\<^sub>c \<and> zero = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> zero"
      by (typecheck_cfuncs, simp add: mult_respects_zero_right)
    then show "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = n"
      using \<open>n = zero\<close> by auto
  next
    assume "n \<noteq> zero"
    then obtain k where k_def:  "n = successor \<circ>\<^sub>c k"
      using \<open>n \<noteq> zero\<close> assms nonzero_is_succ by blast
    oops




(*
lemma even_or_odd:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> m = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n) \<or>
         ( \<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
proof(safe)
  assume "\<nexists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and>
        m = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
*)  
  
  


(*

lemma is_even_def3:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_even \<circ>\<^sub>c  m = \<t>"
  shows "\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> m = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n"
proof(cases "m = zero",auto)
  assume "m = zero"
  have "zero \<in>\<^sub>c \<nat>\<^sub>c \<and> zero = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> zero"
    by (typecheck_cfuncs, simp add: mult_respects_zero_right)
  then show "\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> zero = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n"
    by blast
next
  assume "m \<noteq> zero"
  oops
*)

  
  



(*is_even \<circ>\<^sub>c zero = \<t> \<and> NOT \<circ>\<^sub>c is_even = is_even \<circ>\<^sub>c successor*)

(*

lemma add_evens_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_even \<circ>\<^sub>c m = \<t>" "is_even \<circ>\<^sub>c n = \<t>"
  shows "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
  using assms apply typecheck_cfuncs
proof - 

*)

(*"nth_even = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>*)



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