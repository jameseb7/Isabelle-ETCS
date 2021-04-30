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

lemma NN_rel_is_reflexive:
"reflexive_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"
  by (metis add_commutes cart_prod_decomp elements_of_int_equiv_set2 pair_is_subset reflexive_on_def)

lemma NN_rel_is_symmetric:
"symmetric_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"
  by (typecheck_cfuncs, smt add_commutes cart_prod_decomp elements_of_int_equiv_set1 elements_of_int_equiv_set2 pair_is_subset symmetric_on_def)

lemma NN_rel_is_transitive:
"transitive_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"
proof -
  have f1: "(\<forall>x y z. x \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<and>  y \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<and> z \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)  \<longrightarrow>
      (\<langle>x,y\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set,int_equiv_morphism) \<and> \<langle>y,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set,int_equiv_morphism) \<longrightarrow> \<langle>x,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set,int_equiv_morphism)))"
  proof(auto)
    fix x y z
    assume x_type:  "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    assume y_type:  "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    assume z_type:  "z \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
   
    assume rel1: "\<langle>x,y\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"
    assume rel2: "\<langle>y,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"

(*Now we decompose x, y, and z as x = <a,b> and y = <c,d> and z = <e,f>*)

    have x_decomp: "\<exists> a b. x = \<langle>a, b\<rangle> \<and> a \<in>\<^sub>c \<nat>\<^sub>c \<and> b \<in>\<^sub>c \<nat>\<^sub>c"
      by (simp add: cart_prod_decomp x_type)
    obtain a where a_def: "\<exists>b. x = \<langle>a,b\<rangle> \<and> a \<in>\<^sub>c \<nat>\<^sub>c \<and> b \<in>\<^sub>c \<nat>\<^sub>c"
      using x_decomp by blast
    obtain b where b_def: "x = \<langle>a,b\<rangle> \<and> b \<in>\<^sub>c \<nat>\<^sub>c"
      using a_def by blast
    have x_def: "x = \<langle>a,b\<rangle>"
      by (simp add: b_def)

    have y_decomp: "\<exists> c d. y = \<langle>c, d\<rangle> \<and> c \<in>\<^sub>c \<nat>\<^sub>c \<and> d \<in>\<^sub>c \<nat>\<^sub>c"
      by (simp add: cart_prod_decomp y_type)
    obtain c where c_def: "\<exists>d. y = \<langle>c,d\<rangle> \<and> c \<in>\<^sub>c \<nat>\<^sub>c \<and> d \<in>\<^sub>c \<nat>\<^sub>c"
      using y_decomp by blast
    obtain d where d_def: "y = \<langle>c,d\<rangle> \<and> d \<in>\<^sub>c \<nat>\<^sub>c"
      using c_def by blast
    have y_def: "y = \<langle>c,d\<rangle>"
          by (simp add: d_def)

     have z_decomp: "\<exists> e f. z = \<langle>e, f\<rangle> \<and> e \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<in>\<^sub>c \<nat>\<^sub>c"
      by (simp add: cart_prod_decomp z_type)
    obtain e where e_def: "\<exists>f. z = \<langle>e,f\<rangle> \<and> e \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<in>\<^sub>c \<nat>\<^sub>c"
      using z_decomp by blast
    obtain f where f_def: "z = \<langle>e,f\<rangle> \<and> f \<in>\<^sub>c \<nat>\<^sub>c"
      using e_def by blast 
    have z_def: "z = \<langle>e,f\<rangle>"
        by (simp add: f_def)

    have rel1_decomp: "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"
      using x_type y_type x_def y_def rel1 by blast
 
    have rel2_decomp: "\<langle>\<langle>c,d\<rangle>,\<langle>e,f\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"
      using y_type z_type y_def z_def rel2 by blast

    have equation1: "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
      by (metis a_def b_def c_def d_def elements_of_int_equiv_set1 rel1)

    have equation2: "d +\<^sub>\<nat> e = c +\<^sub>\<nat> f"
      by (metis c_def d_def e_def elements_of_int_equiv_set1 f_def rel2)

    have eq1_plus_eq2: "(b +\<^sub>\<nat> e) +\<^sub>\<nat> (c +\<^sub>\<nat> d) = (a +\<^sub>\<nat> f) +\<^sub>\<nat> (c +\<^sub>\<nat> d)"
      by (smt a_def add_associates add_commutes add_type b_def c_def d_def e_def equation1 equation2 f_def)
    have simplified_eq1_plus_eq2: "b +\<^sub>\<nat> e = a +\<^sub>\<nat> f"
      by (smt a_def add_associates add_cancellative add_commutes add_type b_def c_def d_def e_def element_pair_eq equation1 equation2 f_def x_def z_def)
    
    have desiredrelation_decomp: "\<langle>\<langle>a,b\<rangle>,\<langle>e,f\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> (int_equiv_set, int_equiv_morphism)"
      using a_def b_def e_def elements_of_int_equiv_set2 f_def simplified_eq1_plus_eq2 by auto

    show "\<langle>x,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub> (int_equiv_set, int_equiv_morphism)"
      by (simp add: desiredrelation_decomp x_def z_def)
  qed

  show ?thesis
    using f1 pair_is_subset transitive_on_def by blast
qed

lemma NN_rel_is_relation:
"equiv_rel_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"
  by (simp add: NN_rel_is_reflexive NN_rel_is_symmetric NN_rel_is_transitive equiv_rel_on_def)

definition int :: "cset" ("\<int>\<^sub>c") where
  "\<int>\<^sub>c = quotient_set (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (int_equiv_set,int_equiv_morphism)"

definition natpair2int :: "cfunc" where
  "natpair2int = equiv_class (int_equiv_set,int_equiv_morphism)"

lemma nat2int_type[type_rule]:
  "natpair2int : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow> \<int>\<^sub>c"
  unfolding natpair2int_def int_def
  by (simp add: NN_rel_is_relation equiv_class_type)

lemma equiv_is_natpair2int_eq:
  "\<langle>x, y\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set,int_equiv_morphism) \<longleftrightarrow> natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y"
  unfolding natpair2int_def int_def
  by (simp add: ETCS_Equivalence.equiv_class_eq NN_rel_is_relation)

lemma nat_pair_eq: 
  assumes  "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"  "d \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle> \<longleftrightarrow> b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
proof auto
  assume "natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle>"
  then have "\<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set,int_equiv_morphism)"
    by (simp add: equiv_is_natpair2int_eq)
  then show "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
    by (simp add: assms elements_of_int_equiv_set1)
next
  assume "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
  then have "\<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set,int_equiv_morphism)"
    by (simp add: assms elements_of_int_equiv_set2)
  then show "natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle>"
    by (simp add: equiv_is_natpair2int_eq)
qed

definition lift_int_func :: "cfunc \<Rightarrow> cfunc" ("lift\<^sub>\<int>") where
  "lift\<^sub>\<int> f = quotient_func f (int_equiv_set,int_equiv_morphism)"

lemma const_on_int_rel_def:
  assumes "\<And>x y. natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y \<Longrightarrow> natpair2int \<circ>\<^sub>c f \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c f \<circ>\<^sub>c y"
  shows "\<And>x y. \<langle>x, y\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> (int_equiv_set,int_equiv_morphism) \<Longrightarrow> 
    equiv_class (int_equiv_set,int_equiv_morphism) \<circ>\<^sub>c f \<circ>\<^sub>c x = equiv_class (int_equiv_set,int_equiv_morphism) \<circ>\<^sub>c f \<circ>\<^sub>c y"
  by (metis assms equiv_is_natpair2int_eq natpair2int_def)


lemma lift_int_func_type[type_rule]:
  assumes "\<And>x y. natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y \<Longrightarrow> natpair2int \<circ>\<^sub>c f \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c f \<circ>\<^sub>c y"
  shows "f : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> Y \<Longrightarrow> lift\<^sub>\<int> f : \<int>\<^sub>c \<rightarrow> Y"
  unfolding lift_int_func_def int_def
  by (metis NN_rel_is_relation assms equiv_is_natpair2int_eq natpair2int_def quotient_func_type) 

lemma lift_int_func_natpair2int_eq:
  assumes "\<And>x y. natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y \<Longrightarrow> natpair2int \<circ>\<^sub>c f \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c f \<circ>\<^sub>c y"
  assumes "f : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> Y"
  shows "lift\<^sub>\<int> f \<circ>\<^sub>c natpair2int = f"
  unfolding lift_int_func_def natpair2int_def
  by (metis NN_rel_is_relation assms equiv_is_natpair2int_eq natpair2int_def quotient_func_eq)

end