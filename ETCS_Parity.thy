theory ETCS_Parity
  imports ETCS_Add ETCS_Mult ETCS_Pred
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

lemma is_even_type:
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

lemma is_odd_type:
  "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>"
  by (simp add: is_odd_def2)

lemma is_odd_zero:
  "is_odd \<circ>\<^sub>c zero = \<f>"
  by (simp add: is_odd_def2)

lemma is_odd_successor:
  "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
  by (simp add: is_odd_def2)

(*lemma odd_even_iso:
  "isomorphism (
    (successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>)
      \<amalg>
    (mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>))"
proof (rule epi_mon_is_iso)
  show "epimorphism
     ((successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<amalg>
      (mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>))"
  proof (typecheck_cfuncs, unfold epimorphism_def3, auto)
    fix g h A
    oops*)



end