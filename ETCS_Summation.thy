theory ETCS_Summation
  imports ETCS_Add
begin

definition indexed_sum :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "indexed_sum f low = (THE u. u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c 
    \<and> u \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle> 
    \<and> \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma indexed_sum_def2:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c 
    \<and> indexed_sum f low \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle> 
    \<and> \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low = indexed_sum f low \<circ>\<^sub>c successor"
  unfolding indexed_sum_def
  by (rule theI', typecheck_cfuncs, simp add: natural_number_object_property2)

lemma indexed_sum_type[type_rule]:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  using indexed_sum_def2 assms by auto

lemma indexed_sum_zero:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  shows "indexed_sum f low \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle>"
  using indexed_sum_def2 assms by auto

lemma indexed_sum_successor:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  shows "indexed_sum f low \<circ>\<^sub>c successor 
    = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low"
  using indexed_sum_def2 assms by auto

lemma 
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low = (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f=successor])
  show "left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "(add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c zero = ((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
    sorry

  show "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low"
    sorry

  show "((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    sorry
qed

lemma add_indexed_sum:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n1_type[type_rule]: "n1 \<in>\<^sub>c \<nat>\<^sub>c" and n2_type[type_rule]: "n2 \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low \<circ>\<^sub>c n1)
          +\<^sub>\<nat> (right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>low, n1\<rangle>) \<circ>\<^sub>c n2)
      = right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>n1, n2\<rangle>"
proof -
  have "add2 \<circ>\<^sub>c \<langle>indexed_sum f low \<circ>\<^sub>c n1 \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, indexed_sum f (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>low, n1\<rangle>)\<rangle>
      = indexed_sum f low \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>n1 \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
  proof (rule natural_number_object_func_unique)
    oops

end