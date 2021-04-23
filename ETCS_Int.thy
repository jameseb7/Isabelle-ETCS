theory ETCS_Int
  imports ETCS_Add
begin

definition add_outers :: "cfunc" where
  "add_outers = add2 \<circ>\<^sub>c \<langle>
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle>"

lemma add_outers_type[type_rule]: "add_outers : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_outers_def by typecheck_cfuncs

lemma add_outers_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_outers \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add2 \<circ>\<^sub>c \<langle>a,d\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = add2 \<circ>\<^sub>c \<langle>
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding add_outers_def using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = add2 \<circ>\<^sub>c \<langle>
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>, right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = add2 \<circ>\<^sub>c \<langle>a, d\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed

definition add_inners :: "cfunc" where
  "add_inners = add2 \<circ>\<^sub>c \<langle>
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle>"

lemma add_inners_type[type_rule]: "add_inners : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_inners_def by typecheck_cfuncs
    
lemma add_inners_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_inners \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add2 \<circ>\<^sub>c \<langle>b,c\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = add2 \<circ>\<^sub>c \<langle>
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding add_inners_def using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = add2 \<circ>\<^sub>c \<langle>
      right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = add2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = add2 \<circ>\<^sub>c \<langle>b, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed

definition int_equiv_set :: "cset" where
  "int_equiv_set = (SOME E. \<exists>m. equalizer E m add_outers add_inners)"

definition int_equiv_morphism :: "cfunc" where
  "int_equiv_morphism = (SOME m. equalizer int_equiv_set m add_outers add_inners)"

lemma int_equiv_equalizer: "equalizer int_equiv_set int_equiv_morphism add_outers add_inners"
  unfolding int_equiv_morphism_def
proof (rule someI_ex)
  show "\<exists>x. equalizer int_equiv_set x add_outers add_inners"
    unfolding int_equiv_set_def
  proof (rule someI_ex)
    show "\<exists>x xa. equalizer x xa add_outers add_inners"
      using add_inners_type add_outers_type equalizer_exists by auto
  qed
qed

lemma elements_of_int_equiv_set1:
  assumes  "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"  "d \<in>\<^sub>c \<nat>\<^sub>c" 
  assumes "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"
  shows "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
proof - 
  have f1: "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> factorsthru int_equiv_morphism"
    using assms(5) relative_member_def by auto
  have f2: "add_outers \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> = add_inners  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle>"
     using assms apply typecheck_cfuncs
     by (meson f1 int_equiv_equalizer xfactorthru_equalizer_iff_fx_eq_gx)
  show  "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
     using assms apply typecheck_cfuncs
     using add_def add_inners_apply add_outers_apply f2 by auto
 qed

lemma elements_of_int_equiv_set2:
  assumes  "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"  "d \<in>\<^sub>c \<nat>\<^sub>c" 
  assumes "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
  shows "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"
proof-
  have f1: "add_outers \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> = add_inners  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle>"
     using assms apply typecheck_cfuncs
     using add_def add_inners_apply add_outers_apply assms(5) by presburger
  have f2: "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> factorsthru int_equiv_morphism"
     using assms apply typecheck_cfuncs
     using add_inners_type add_outers_type f1 int_equiv_equalizer xfactorthru_equalizer_iff_fx_eq_gx by blast
  have f3: "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: assms(1) assms(2) assms(3) assms(4) cfunc_prod_type)
  have f4: "monomorphism(int_equiv_morphism)"
    using equalizer_is_monomorphism int_equiv_equalizer by auto
  have f5: "int_equiv_morphism: domain(int_equiv_morphism) \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (smt add_inners_type add_outers_type cfunc_type_def codomain_comp f1 f3 factors_through_def int_equiv_equalizer xfactorthru_equalizer_iff_fx_eq_gx)
 show "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"
     using assms apply typecheck_cfuncs
     using cfunc_type_def equalizer_def f2 f4 f5 int_equiv_equalizer relative_member_def2 by force
qed




lemma pair_is_subset:
"(int_equiv_set,int_equiv_morphism) \<subseteq>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (metis add_inners_type cfunc_type_def equalizer_def equalizer_is_monomorphism int_equiv_equalizer subobject_of_def2)

lemma "reflexive_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"
  by (metis add_commutes cart_prod_decomp elements_of_int_equiv_set2 pair_is_subset reflexive_on_def)


lemma "symmetric_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"
  by (typecheck_cfuncs, smt add_commutes cart_prod_decomp elements_of_int_equiv_set1 elements_of_int_equiv_set2 pair_is_subset symmetric_on_def)

(*
lemma "transitive_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"

In order to prove this we need to establish the cancellative law on N.

Proof: 
Suppose <<a,b>,<c,d>> in Rz
Suppose <<c,d>,<e,f>> in Rz

then 
b+c = a+d  AND d+e = c+f

hence
(b+e) + (c+d) = (a+f) +(c+d)

and by applying the cancellative law on N we simplify this to
(b+e) = (a+f)

therefore
<<a,b>,<e,f>> in Rz.

*)
 




end