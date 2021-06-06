theory ETCS_Int
  imports ETCS_Add ETCS_Mult ETCS_Comparison
begin

definition add_outers :: "cfunc" where
  "add_outers = add2 \<circ>\<^sub>c outers \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c"

lemma add_outers_type[type_rule]: "add_outers : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_outers_def by typecheck_cfuncs

lemma add_outers_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_outers \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add2 \<circ>\<^sub>c \<langle>a,d\<rangle>"
  unfolding add_outers_def using assms 
  by (typecheck_cfuncs, smt comp_associative2 outers_apply)

definition add_inners :: "cfunc" where
  "add_inners = add2 \<circ>\<^sub>c inners \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c"

lemma add_inners_type[type_rule]: "add_inners : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_inners_def by typecheck_cfuncs
    
lemma add_inners_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_inners \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add2 \<circ>\<^sub>c \<langle>b,c\<rangle>"
  unfolding add_inners_def using assms 
  by (typecheck_cfuncs, smt comp_associative2 inners_apply)

definition int_equiv_set :: "cset" where
  "int_equiv_set = (SOME E. \<exists>m. equalizer E m add_outers add_inners)"

definition int_equiv_morphism :: "cfunc" where
  "int_equiv_morphism = (SOME m. equalizer int_equiv_set m add_outers add_inners)"

definition int_equiv_rel :: "cset \<times> cfunc" ("R\<^sub>\<int>") where
  "R\<^sub>\<int> = (int_equiv_set, int_equiv_morphism)"

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
  assumes "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
  shows "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
proof - 
  have f1: "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> factorsthru int_equiv_morphism"
    using assms(5) unfolding relative_member_def int_equiv_rel_def by auto
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
  shows "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
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
  show "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
     using assms apply typecheck_cfuncs
     using cfunc_type_def equalizer_def f2 f4 f5 int_equiv_equalizer
     unfolding relative_member_def2 int_equiv_rel_def by force
 qed

lemma pair_is_subset:
"(int_equiv_set,int_equiv_morphism) \<subseteq>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (metis add_inners_type cfunc_type_def equalizer_def equalizer_is_monomorphism int_equiv_equalizer subobject_of_def2)

lemma NN_rel_is_reflexive:
"reflexive_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int>"
  by (metis add_commutes cart_prod_decomp elements_of_int_equiv_set2 pair_is_subset reflexive_on_def int_equiv_rel_def)

lemma NN_rel_is_symmetric:
"symmetric_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int>"
  by (typecheck_cfuncs, smt add_commutes cart_prod_decomp elements_of_int_equiv_set1 elements_of_int_equiv_set2 pair_is_subset symmetric_on_def int_equiv_rel_def)

lemma NN_rel_is_transitive:
"transitive_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int>"
proof -
  have f1: "(\<forall>x y z. x \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<and>  y \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<and> z \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)  \<longrightarrow>
      (\<langle>x,y\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int> \<and> \<langle>y,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int> \<longrightarrow> \<langle>x,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int>))"
  proof(auto)
    fix x y z
    assume x_type:  "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    assume y_type:  "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    assume z_type:  "z \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
   
    assume rel1: "\<langle>x,y\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
    assume rel2: "\<langle>y,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"

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

    have rel1_decomp: "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
      using x_type y_type x_def y_def rel1 by blast
 
    have rel2_decomp: "\<langle>\<langle>c,d\<rangle>,\<langle>e,f\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
      using y_type z_type y_def z_def rel2 by blast

    have equation1: "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
      by (metis a_def b_def c_def d_def elements_of_int_equiv_set1 rel1)

    have equation2: "d +\<^sub>\<nat> e = c +\<^sub>\<nat> f"
      by (metis c_def d_def e_def elements_of_int_equiv_set1 f_def rel2)

    have eq1_plus_eq2: "(b +\<^sub>\<nat> e) +\<^sub>\<nat> (c +\<^sub>\<nat> d) = (a +\<^sub>\<nat> f) +\<^sub>\<nat> (c +\<^sub>\<nat> d)"
      by (smt a_def add_associates add_commutes add_type b_def c_def d_def e_def equation1 equation2 f_def)
    have simplified_eq1_plus_eq2: "b +\<^sub>\<nat> e = a +\<^sub>\<nat> f"
      by (smt a_def add_associates add_cancellative add_commutes add_type b_def c_def d_def e_def element_pair_eq equation1 equation2 f_def x_def z_def)
    
    have desiredrelation_decomp: "\<langle>\<langle>a,b\<rangle>,\<langle>e,f\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
      using a_def b_def e_def elements_of_int_equiv_set2 f_def simplified_eq1_plus_eq2 by auto

    show "\<langle>x,z\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub> R\<^sub>\<int>"
      by (simp add: desiredrelation_decomp x_def z_def)
  qed

  show ?thesis
    using f1 pair_is_subset unfolding transitive_on_def int_equiv_rel_def by blast
qed

lemma NN_rel_is_relation:
"equiv_rel_on (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int>"
  by (simp add: NN_rel_is_reflexive NN_rel_is_symmetric NN_rel_is_transitive equiv_rel_on_def)

definition int :: "cset" ("\<int>\<^sub>c") where
  "\<int>\<^sub>c = quotient_set (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int>"

definition natpair2int :: "cfunc" where
  "natpair2int = equiv_class R\<^sub>\<int>"


lemma nat2int_type[type_rule]:
  "natpair2int : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow> \<int>\<^sub>c"
  unfolding natpair2int_def int_def
  by (simp add: NN_rel_is_relation equiv_class_type)


lemma NNtoZ_map_is_epic:
  "epimorphism(natpair2int)"
  by (metis NN_rel_is_relation canonical_quot_map_is_epi natpair2int_def int_equiv_rel_def)

lemma representation_map_exists:
"(\<exists> g . g sectionof natpair2int)"
  using NNtoZ_map_is_epic axiom_of_choice by blast


definition int2natpair :: "cfunc"  where
  "int2natpair = (SOME g . g sectionof natpair2int)"

lemma int2natpair_type[type_rule]:
  "int2natpair : \<int>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c"
  unfolding int2natpair_def int_def
  by (metis int_def cfunc_type_def nat2int_type representation_map_exists section_of_def someI_ex)

lemma int2natpair_is_sectionof_natpair2int:
  "int2natpair sectionof natpair2int"
  by (metis int2natpair_def representation_map_exists someI_ex)

lemma natpair2int_int2natpair:
  "natpair2int \<circ>\<^sub>c int2natpair  = id \<int>\<^sub>c"
  using cfunc_type_def int2natpair_is_sectionof_natpair2int nat2int_type section_of_def by auto

lemma representation_theorem:
  assumes "z \<in>\<^sub>c \<int>\<^sub>c"
  shows "\<exists> m n. (m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> z = natpair2int \<circ>\<^sub>c \<langle>m, n \<rangle>)"
proof - 
  have some_representation: "\<exists> x. (x \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)  \<and> z = natpair2int \<circ>\<^sub>c x)"
    by (smt assms cfunc_type_def comp_associative comp_type id_left_unit nat2int_type representation_map_exists section_of_def)
  then show "\<exists> m n. (m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> z = natpair2int \<circ>\<^sub>c \<langle>m, n \<rangle>)"
    using cart_prod_decomp by blast
qed


    

lemma equiv_is_natpair2int_eq:
  assumes "\<langle>x,y\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
  shows "\<langle>x, y\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int> \<longleftrightarrow> natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y"
  unfolding natpair2int_def int_def by (simp add: assms equiv_class_eq NN_rel_is_relation)

lemma nat_pair_eq: 
  assumes  "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"  "d \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle> \<longleftrightarrow> b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
proof auto
  assume "natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle>"
  then have "\<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
    by (simp add: assms cfunc_prod_type equiv_is_natpair2int_eq)
  then show "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
    by (simp add: assms elements_of_int_equiv_set1)
next
  assume "b +\<^sub>\<nat> c = a +\<^sub>\<nat> d"
  then have "\<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
    by (simp add: assms elements_of_int_equiv_set2)
  then show "natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle>"
    using equiv_is_natpair2int_eq relative_member_def by blast
qed


lemma canonical_representation_theorem:
  assumes "m \<in>\<^sub>c \<int>\<^sub>c"
  shows "\<exists> n. (n \<in>\<^sub>c \<nat>\<^sub>c \<and> ((m = natpair2int \<circ>\<^sub>c \<langle>zero, n \<rangle>) \<or> (m = natpair2int \<circ>\<^sub>c \<langle>n, zero \<rangle>)))"
proof - 
  have rep: "\<exists> j k. (j \<in>\<^sub>c \<nat>\<^sub>c \<and> k \<in>\<^sub>c \<nat>\<^sub>c \<and> m = natpair2int \<circ>\<^sub>c \<langle>j, k \<rangle>)"
    using assms representation_theorem by blast
  then obtain j where j_def: "\<exists>k. (j \<in>\<^sub>c \<nat>\<^sub>c \<and> k \<in>\<^sub>c \<nat>\<^sub>c \<and> m = natpair2int \<circ>\<^sub>c \<langle>j, k \<rangle>)"
    by auto
  then obtain k where k_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> k \<in>\<^sub>c \<nat>\<^sub>c \<and> m = natpair2int \<circ>\<^sub>c \<langle>j, k \<rangle>"
    by auto
  have connexity: "(leq \<circ>\<^sub>c \<langle>j, k\<rangle> = \<t>) \<or> (leq \<circ>\<^sub>c \<langle>k, j\<rangle> = \<t>)"
    by (simp add: k_def lqe_connexity)
  show ?thesis
  proof(cases "(leq \<circ>\<^sub>c \<langle>j, k\<rangle> = \<t>)")
    assume case1: "(leq \<circ>\<^sub>c \<langle>j, k\<rangle> = \<t>)"
    then have l_exists: "\<exists> l. (l \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> l = k)"
      using add_commutes k_def leq_true_implies_exists by blast
    then obtain l where l_def: "l \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> l = k"
      by auto
    then have eqn1: "k +\<^sub>\<nat> zero = j +\<^sub>\<nat> l"
      by (simp add: add_respects_zero_on_right k_def)
    then have a_positive_integer: "natpair2int \<circ>\<^sub>c \<langle>j,k\<rangle> = natpair2int \<circ>\<^sub>c \<langle>zero,l\<rangle>"
      by (simp add: k_def l_def nat_pair_eq zero_type)
    then show ?thesis
      using k_def l_def by blast
  next
    assume case2: "leq \<circ>\<^sub>c \<langle>j,k\<rangle> \<noteq> \<t>"
    then have case2i: "leq \<circ>\<^sub>c \<langle>k,j\<rangle> = \<t>"
      using connexity by blast
    then have p_exists: "\<exists> p. (p \<in>\<^sub>c \<nat>\<^sub>c \<and> p+\<^sub>\<nat> k = j)"
      by (simp add: k_def leq_true_implies_exists)
    then obtain p where p_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> p+\<^sub>\<nat> k = j"
      by auto
    then have eqn2: "k +\<^sub>\<nat> p = zero +\<^sub>\<nat> j"
      using add_commutes add_respects_zero_on_left k_def by auto
    then have a_negative_integer: "natpair2int \<circ>\<^sub>c \<langle>j,k\<rangle> = natpair2int \<circ>\<^sub>c \<langle>p,zero\<rangle>"
      using k_def nat_pair_eq p_def zero_type by auto
    then show ?thesis
      using k_def p_def by blast
  qed
qed

section \<open>Lifting function domains to integers\<close>

definition lift_int_func :: "cfunc \<Rightarrow> cfunc" ("lift\<^sub>\<int>") where
  "lift\<^sub>\<int> f = quotient_func f R\<^sub>\<int>"

lemma const_on_int_rel_def:
  assumes "\<And>x y. x \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> y \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y \<Longrightarrow> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
  shows "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> f"
  unfolding const_on_rel_def using assms equiv_is_natpair2int_eq relative_member_def by blast

lemma lift_int_func_type[type_rule]:
  assumes "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> f"
  shows "f : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> Y \<Longrightarrow> lift\<^sub>\<int> f : \<int>\<^sub>c \<rightarrow> Y"
  unfolding lift_int_func_def int_def
  using NN_rel_is_relation assms const_on_int_rel_def quotient_func_type by blast

lemma lift_int_func_natpair2int_eq:
  assumes "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> f"
  assumes "f : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> Y"
  shows "lift\<^sub>\<int> f \<circ>\<^sub>c natpair2int = f"
  unfolding lift_int_func_def natpair2int_def
  using NN_rel_is_relation assms const_on_int_rel_def quotient_func_eq by blast

lemma quot_map_swap_constant_on_equiv:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "\<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esub> R\<^sub>\<int>"
  shows "natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>c,d\<rangle>"
proof - 
  have "natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>  = natpair2int \<circ>\<^sub>c  \<langle>b,a\<rangle>"
    using assms(1) assms(2) swap_ap by auto
  also have "... = natpair2int \<circ>\<^sub>c  \<langle>d,c\<rangle>"
    using assms elements_of_int_equiv_set1 nat_pair_eq by auto
  also have "... = natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>c,d\<rangle>"
    using assms(3) assms(4) swap_ap by auto
  then show ?thesis using calculation by auto
qed

definition liftr_int_func :: "cfunc \<Rightarrow> cfunc" ("liftr\<^sub>\<int>") where
  "liftr\<^sub>\<int> f = (lift\<^sub>\<int> (f\<^sup>\<sharp>))\<^sup>\<flat>"

lemma transpose_const_on_int_rel:
  assumes f_const_on_equiv_class:
    "\<And>x y k. k \<in>\<^sub>c X \<Longrightarrow> x \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> y \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y \<Longrightarrow> f \<circ>\<^sub>c \<langle>k, x\<rangle> = f \<circ>\<^sub>c \<langle>k, y\<rangle>"
  assumes f_type: "f : X \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y"
  shows "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> (f\<^sup>\<sharp>)"
proof (rule const_on_int_rel_def)
  fix x y
  assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  assume y_type: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"

  assume x_y_in_same_equiv_class: "natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y"

  show "f\<^sup>\<sharp> \<circ>\<^sub>c x = f\<^sup>\<sharp> \<circ>\<^sub>c y"
  proof (rule same_evals_equal[where X=Y, where A=X, where Z="one"])
    show "f\<^sup>\<sharp> \<circ>\<^sub>c x \<in>\<^sub>c Y\<^bsup>X\<^esup>"
      using x_type f_type by typecheck_cfuncs
    show "f\<^sup>\<sharp> \<circ>\<^sub>c y \<in>\<^sub>c Y\<^bsup>X\<^esup>"
      using y_type f_type by typecheck_cfuncs

    show "eval_func Y X \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c x)) = eval_func Y X \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c y))"
    proof (rule one_separator[where X="X \<times>\<^sub>c one", where Y=Y])
      show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f\<^sup>\<sharp> \<circ>\<^sub>c x : X \<times>\<^sub>c one \<rightarrow> Y"
        using x_type f_type by typecheck_cfuncs
      show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f\<^sup>\<sharp> \<circ>\<^sub>c y : X \<times>\<^sub>c one \<rightarrow> Y"
        using y_type f_type by typecheck_cfuncs
    next
      fix k_one
      assume "k_one \<in>\<^sub>c X \<times>\<^sub>c one"
      then obtain k where k_type: "k \<in>\<^sub>c X" and k_one_def: "k_one = \<langle>k, id one\<rangle>"
        using cart_prod_decomp id_type one_unique_element by blast

      have "f \<circ>\<^sub>c \<langle>k, x\<rangle> = f \<circ>\<^sub>c \<langle>k, y\<rangle>"
        using f_const_on_equiv_class k_type x_type x_y_in_same_equiv_class y_type by blast
      then have "(eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp>))) \<circ>\<^sub>c \<langle>k, x\<rangle> = (eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp>))) \<circ>\<^sub>c \<langle>k, y\<rangle>"
        using f_type transpose_func_def by auto
      then have "eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>k, x\<rangle> = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>k, y\<rangle>"
        using x_type y_type k_type f_type comp_associative2 by (typecheck_cfuncs, auto)
      then have "eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c x)) \<circ>\<^sub>c \<langle>k, id one\<rangle>
          = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c y)) \<circ>\<^sub>c \<langle>k, id one\<rangle>"
        using x_type y_type k_type f_type cfunc_cross_prod_comp_cfunc_prod id_right_unit2
        by (typecheck_cfuncs, auto)
      then have "(eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c x))) \<circ>\<^sub>c \<langle>k, id one\<rangle>
          = (eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c y))) \<circ>\<^sub>c \<langle>k, id one\<rangle>"
        using x_type y_type k_type f_type comp_associative2 by (typecheck_cfuncs, auto)
      then show "(eval_func Y X \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c x))) \<circ>\<^sub>c k_one
          = (eval_func Y X \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c y))) \<circ>\<^sub>c k_one"
        by (simp add: k_one_def)
    qed
  qed
qed

lemma liftr_int_func_type[type_rule]:
  assumes "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> (f\<^sup>\<sharp>)"
  assumes f_type: "f : X \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y"
  shows "liftr\<^sub>\<int> f : X \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> Y"
  unfolding liftr_int_func_def lift_int_func_def
  by (metis int_def NN_rel_is_relation assms flat_type  quotient_func_type transpose_func_type)
  
lemma liftr_int_func_natpair2int_eq:
  assumes "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> (f\<^sup>\<sharp>)"
  assumes f_type: "f : X \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y"
  shows "liftr\<^sub>\<int> f \<circ>\<^sub>c (id X \<times>\<^sub>f natpair2int) = f"
proof -
  have "liftr\<^sub>\<int> f \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f natpair2int) = (lift\<^sub>\<int> (f\<^sup>\<sharp>))\<^sup>\<flat> \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f natpair2int)"
    unfolding liftr_int_func_def by auto
  also have "... = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (lift\<^sub>\<int> (f\<^sup>\<sharp>))) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f natpair2int)"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2)
  also have "... = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (lift\<^sub>\<int> (f\<^sup>\<sharp>) \<circ>\<^sub>c natpair2int))"
    using assms by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
  also have "... = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f f\<^sup>\<sharp>)"
    using assms by (typecheck_cfuncs, simp add: lift_int_func_natpair2int_eq)
  also have "... = f"
    using f_type transpose_func_def by auto
  then show ?thesis
    using calculation by auto
qed

lemma liftr_int_func_unique:
  assumes f_const_on_equiv_class: "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> (f\<^sup>\<sharp>)"
  assumes f_type: "f : X \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y" and g_type: "g : X \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> Y"
  shows "g \<circ>\<^sub>c (id X \<times>\<^sub>f natpair2int) = f \<Longrightarrow> g = liftr\<^sub>\<int> f"
proof -
  have prod_epi: "epimorphism (id\<^sub>c X \<times>\<^sub>f natpair2int)"
    by (simp add: NNtoZ_map_is_epic cfunc_type_def id_isomorphism iso_imp_epi_and_monic product_of_epis_is_epi)

  assume "g \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f natpair2int = f"
  then have "g \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f natpair2int) = liftr\<^sub>\<int> f \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f natpair2int)"
    using f_const_on_equiv_class f_type liftr_int_func_natpair2int_eq by auto
  then show "g = liftr\<^sub>\<int> f"
    using prod_epi assms cfunc_cross_prod_type epimorphism_def3 id_type nat2int_type prod_epi 
    by (typecheck_cfuncs, auto, blast)
qed

lemma transpose_swap_const_on_int_rel:
  assumes f_const_on_equiv_class:
    "\<And>x y k. k \<in>\<^sub>c X \<Longrightarrow> x \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> y \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y \<Longrightarrow> f \<circ>\<^sub>c \<langle>x, k\<rangle> = f \<circ>\<^sub>c \<langle>y, k\<rangle>"
  assumes f_type: "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c X \<rightarrow> Y"
  shows "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)"
proof (rule const_on_int_rel_def)
  fix x y
  assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  assume y_type: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"

  assume x_y_in_same_equiv_class: "natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y"

  show "(f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c x = (f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c y"
  proof (rule same_evals_equal[where X=Y, where A=X, where Z="one"])
    show "(f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c x \<in>\<^sub>c Y\<^bsup>X\<^esup>"
      using x_type f_type by typecheck_cfuncs
    show "(f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c y \<in>\<^sub>c Y\<^bsup>X\<^esup>"
      using y_type f_type by typecheck_cfuncs

    show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f (f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c x =
        eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f (f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c y"
    proof (rule one_separator[where X="X \<times>\<^sub>c one", where Y=Y])
      show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f (f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c x : X \<times>\<^sub>c one \<rightarrow> Y"
        using x_type f_type by typecheck_cfuncs
      show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f (f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c y : X \<times>\<^sub>c one \<rightarrow> Y"
        using y_type f_type by typecheck_cfuncs
    next
      fix k_one
      assume "k_one \<in>\<^sub>c X \<times>\<^sub>c one"
      then obtain k where k_type: "k \<in>\<^sub>c X" and k_one_def: "k_one = \<langle>k, id one\<rangle>"
        using cart_prod_decomp id_type one_unique_element by blast

      have "f \<circ>\<^sub>c \<langle>x, k\<rangle> = f \<circ>\<^sub>c \<langle>y, k\<rangle>"
        using f_const_on_equiv_class k_type x_type x_y_in_same_equiv_class y_type by blast
      then have "f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>k, x\<rangle> = f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>k, y\<rangle>"
        using k_type swap_ap x_type y_type by auto
      then have "(f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>k, x\<rangle> = (f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>k, y\<rangle>"
        using f_type k_type x_type y_type comp_associative2 by (typecheck_cfuncs, auto)
      then have "(eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))) \<circ>\<^sub>c \<langle>k, x\<rangle>
          = (eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)))  \<circ>\<^sub>c \<langle>k, y\<rangle>"
        using f_type transpose_func_def by (typecheck_cfuncs, auto)
      then have "eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>k, x\<rangle>
          = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))  \<circ>\<^sub>c \<langle>k, y\<rangle>"
        using x_type y_type k_type f_type comp_associative2 by (typecheck_cfuncs, auto)
      then have "eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c x)) \<circ>\<^sub>c \<langle>k, id one\<rangle>
          = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c y)) \<circ>\<^sub>c \<langle>k, id one\<rangle>"
        using x_type y_type k_type f_type cfunc_cross_prod_comp_cfunc_prod id_right_unit2
        by (typecheck_cfuncs, auto)
      then have "(eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c x))) \<circ>\<^sub>c \<langle>k, id one\<rangle>
          = (eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c y))) \<circ>\<^sub>c \<langle>k, id one\<rangle>"
        using x_type y_type k_type f_type comp_associative2 by (typecheck_cfuncs, auto)
      then show "(eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c x))) \<circ>\<^sub>c k_one
          = (eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c y))) \<circ>\<^sub>c k_one"
        by (simp add: k_one_def)
    qed
  qed
qed

definition liftl_int_func :: "cfunc \<Rightarrow> cfunc" ("liftl\<^sub>\<int>") where
  "liftl\<^sub>\<int> f = (THE g. \<exists> X. domain f = (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c X \<and> g = (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c X)"

lemma liftl_int_func_def2:
  assumes "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c X \<rightarrow> Y"
  shows "liftl\<^sub>\<int> f = (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c X"
  using assms unfolding liftl_int_func_def cfunc_type_def
  by (rule_tac the1I2, auto, (metis cfunc_type_def transpose_func_type)+)

lemma liftl_int_func_type[type_rule]:
  assumes "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)"
  assumes "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c X \<rightarrow> Y"
  shows "liftl\<^sub>\<int> f : \<int>\<^sub>c \<times>\<^sub>c X \<rightarrow> Y"
  using assms NN_rel_is_relation
  by (unfold liftl_int_func_def2 lift_int_func_def int_def, typecheck_cfuncs)

lemma liftl_int_func_natpair2int_eq:
  assumes "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)"
  assumes f_type: "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c X \<rightarrow> Y"
  shows "liftl\<^sub>\<int> f \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X) = f"
proof -
  have "liftl\<^sub>\<int> f \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X) = ((lift\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c X) \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X)"
    using assms by (unfold liftl_int_func_def2, auto)
  also have "... = (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c X \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X)"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<^sup>\<flat> \<circ>\<^sub>c (id X \<times>\<^sub>f natpair2int) \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) X"
    using assms by (typecheck_cfuncs, simp add: swap_cross_prod)
  also have "... = (eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f lift\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))) \<circ>\<^sub>c (id X \<times>\<^sub>f natpair2int) \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) X"
    by (smt assms(1) comp_type f_type inv_transpose_func_def2 lift_int_func_type swap_type transpose_func_type)
  also have "... = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c natpair2int)) \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) X"
    using assms by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition)
  also have "... = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) X"
    using assms by (typecheck_cfuncs, simp add: lift_int_func_natpair2int_eq)
  also have "... = f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) X"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = f"
    using f_type id_right_unit2 swap_idempotent by auto
  then show ?thesis
    using calculation by auto
qed

lemma liftl_int_func_unique:
  assumes f_const_on_equiv_class: 
    "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((f \<circ>\<^sub>c swap X (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)"
  assumes f_type: "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c X \<rightarrow> Y" and g_type: "g : \<int>\<^sub>c \<times>\<^sub>c X \<rightarrow> Y"
  shows "g \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X) = f \<Longrightarrow> g = liftl\<^sub>\<int> f"
proof -
  have prod_epi: "epimorphism (natpair2int \<times>\<^sub>f id X)"
    by (simp add: NNtoZ_map_is_epic cfunc_type_def id_isomorphism iso_imp_epi_and_monic product_of_epis_is_epi)

  assume "g \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X) = f"
  then have "g \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X) = liftl\<^sub>\<int> f \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id X)"
    using f_const_on_equiv_class f_type liftl_int_func_natpair2int_eq by auto
  then show "g = liftl\<^sub>\<int> f"
    using prod_epi assms cfunc_cross_prod_type epimorphism_def3 id_type nat2int_type prod_epi 
    by (typecheck_cfuncs, auto, meson)
qed

lemma pair_const_on_int_rel_transpose_swap:
  assumes const_on_equiv_class:
    "\<And>a b c d. a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c \<Longrightarrow> natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d \<Longrightarrow> f \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c \<langle>c, d\<rangle>"
  assumes f_type: "f : (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> Y"
  shows "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)"
  using const_on_equiv_class f_type transpose_swap_const_on_int_rel by blast

lemma pair_const_on_int_rel_transpose:
  assumes const_on_equiv_class:
    "\<And>a b c d. a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c \<Longrightarrow> natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d \<Longrightarrow> f \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c \<langle>c, d\<rangle>"
  assumes f_type: "f : (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> Y"
  shows "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> (f\<^sup>\<sharp>)"
  using const_on_equiv_class f_type transpose_const_on_int_rel by blast

lemma pair_const_on_int_rel_liftl_transpose:
  assumes const_on_equiv_class:
    "\<And>a b c d. a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c \<Longrightarrow> natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d \<Longrightarrow> f \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c \<langle>c, d\<rangle>"
  assumes f_type: "f : (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> Y"
  shows "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((liftl\<^sub>\<int> f)\<^sup>\<sharp>)"
proof (rule transpose_const_on_int_rel[where X="\<int>\<^sub>c", where Y=Y])
  show "liftl\<^sub>\<int> f : \<int>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y"
    using assms liftl_int_func_type pair_const_on_int_rel_transpose_swap by blast
next
  fix x y k
  assume k_type: "k \<in>\<^sub>c \<int>\<^sub>c" and x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and y_type: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  assume x_y_equiv: "natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y"

  have f_swap_transpose_const: "const_on_rel (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) R\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)"
    using const_on_equiv_class f_type pair_const_on_int_rel_transpose_swap by blast

  obtain n where n_type: "n \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and k_def: "k = natpair2int \<circ>\<^sub>c n"
    using canonical_representation_theorem cfunc_prod_type k_type zero_type by blast

  have "liftl\<^sub>\<int> f \<circ>\<^sub>c \<langle>k,x\<rangle> = (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>k,x\<rangle>"
    using f_type by (unfold liftl_int_func_def2, simp)
  also have "... = lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>k,x\<rangle>"
    using f_type k_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, smt comp_associative2)
  also have "... = lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>x,k\<rangle>"
    using k_type swap_ap x_type by auto
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,k\<rangle>"
    using f_type k_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2)
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,natpair2int \<circ>\<^sub>c n\<rangle>"
    unfolding k_def by auto
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c natpair2int)) \<circ>\<^sub>c \<langle>x, n\<rangle>"
    using f_type n_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2)
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x, n\<rangle>"
    using f_type n_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, simp add: f_swap_transpose_const lift_int_func_natpair2int_eq)
  also have "... = (f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>x, n\<rangle>"
    using f_type x_type n_type by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = f \<circ>\<^sub>c \<langle>n, x\<rangle>"
    using f_type x_type n_type by (typecheck_cfuncs, smt comp_associative2 swap_ap)
  also have "... = f \<circ>\<^sub>c \<langle>n, y\<rangle>"
    by (simp add: const_on_equiv_class n_type x_type x_y_equiv y_type)
  also have "... = (f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>y, n\<rangle>"
    using f_type y_type n_type by (typecheck_cfuncs, smt comp_associative2 swap_ap)
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>y, n\<rangle>"
    using f_type y_type n_type by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c natpair2int)) \<circ>\<^sub>c \<langle>y, n\<rangle>"
    using f_type n_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, simp add: f_swap_transpose_const lift_int_func_natpair2int_eq)
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>y,natpair2int \<circ>\<^sub>c n\<rangle>"
    using f_type n_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2)
  also have "... = eval_func Y (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>y,k\<rangle>"
    unfolding k_def by auto
  also have "... = lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>y,k\<rangle>"
    using f_type k_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2)
  also have "... = lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>k,y\<rangle>"
    using k_type swap_ap y_type by auto
  also have "... = (lift\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c swap \<int>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>k,y\<rangle>"
    using f_type k_type x_type y_type f_swap_transpose_const NN_rel_is_relation
    by (typecheck_cfuncs, smt comp_associative2)
  also have "... = liftl\<^sub>\<int> f \<circ>\<^sub>c \<langle>k,y\<rangle>"
    using f_type by (unfold liftl_int_func_def2, simp)
  then show "liftl\<^sub>\<int> f \<circ>\<^sub>c \<langle>k,x\<rangle> = liftl\<^sub>\<int> f \<circ>\<^sub>c \<langle>k,y\<rangle>"
    using calculation by auto
qed

definition lift2_int_func :: "cfunc \<Rightarrow> cfunc" ("lift2\<^sub>\<int>") where
  "lift2\<^sub>\<int> f = liftr\<^sub>\<int> (liftl\<^sub>\<int> f)"

lemma lift2_int_func_type[type_rule]:
  assumes "\<And>a b c d. a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c \<Longrightarrow> natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d \<Longrightarrow> f \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c \<langle>c, d\<rangle>"
  assumes "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y"
  shows "lift2\<^sub>\<int> f : \<int>\<^sub>c \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> Y"
  unfolding lift2_int_func_def
  using assms liftl_int_func_type liftr_int_func_type pair_const_on_int_rel_liftl_transpose pair_const_on_int_rel_transpose_swap
  by blast

lemma lift2_int_func_natpair2int_eq:
  assumes "\<And>a b c d. a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c \<Longrightarrow> natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d \<Longrightarrow> f \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c \<langle>c, d\<rangle>"
  assumes "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y"
  shows "lift2\<^sub>\<int> f \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) = f"
proof -
  have f_swap_transpose_const: "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((f \<circ>\<^sub>c swap (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)"
    using assms pair_const_on_int_rel_transpose_swap by blast
  have liftl_f_transpose_const: "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> ((liftl\<^sub>\<int> f)\<^sup>\<sharp>)"
    using assms pair_const_on_int_rel_liftl_transpose by blast

  have "lift2\<^sub>\<int> f \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) = liftr\<^sub>\<int> (liftl\<^sub>\<int> f) \<circ>\<^sub>c natpair2int \<times>\<^sub>f natpair2int"
    unfolding lift2_int_func_def by auto
  also have "... = liftr\<^sub>\<int> (liftl\<^sub>\<int> f) \<circ>\<^sub>c (id \<int>\<^sub>c \<times>\<^sub>f natpair2int) \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  also have "... = (liftr\<^sub>\<int> (liftl\<^sub>\<int> f) \<circ>\<^sub>c (id \<int>\<^sub>c \<times>\<^sub>f natpair2int)) \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))"
    using assms f_swap_transpose_const liftl_f_transpose_const comp_associative2
    by (typecheck_cfuncs, blast)
  also have "... = liftl\<^sub>\<int> f \<circ>\<^sub>c (natpair2int \<times>\<^sub>f id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))"
    using assms f_swap_transpose_const liftl_f_transpose_const
    by (typecheck_cfuncs, simp add: liftr_int_func_natpair2int_eq)
  also have "... = f"
    using assms f_swap_transpose_const liftl_int_func_natpair2int_eq by blast
  then show ?thesis
    using calculation by auto
qed

lemma lift2_int_func_unique:
  assumes f_const_on_equiv_class: 
    "\<And>a b c d. a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow> d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<Longrightarrow>
      natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c \<Longrightarrow> natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d \<Longrightarrow> f \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c \<langle>c, d\<rangle>"
  assumes f_type: "f : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> Y" and g_type: "g : \<int>\<^sub>c \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> Y"
  shows "g \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) = f \<Longrightarrow> g = lift2\<^sub>\<int> f"
proof -
  have  "epimorphism (natpair2int \<times>\<^sub>f natpair2int)"
    using NNtoZ_map_is_epic nat2int_type product_of_epis_is_epi by auto
  then have prod_epi: "\<And> g h A. g : \<int>\<^sub>c \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> A \<Longrightarrow> h : \<int>\<^sub>c \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> A \<Longrightarrow>
    g \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) = h \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) \<Longrightarrow> g = h"
    unfolding epimorphism_def2 using cfunc_cross_prod_type nat2int_type by blast

  assume "g \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) = f"
  then have "g \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) = lift2\<^sub>\<int> f \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int)"
    by (metis f_const_on_equiv_class f_type lift2_int_func_natpair2int_eq)
  then show "g = lift2\<^sub>\<int> f"
    using prod_epi assms by (typecheck_cfuncs, blast)
qed

section \<open>Integer Negation\<close>

definition neg_int :: "cfunc" where
  "neg_int = lift\<^sub>\<int> (natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c)"

lemma natpair2int_swap_const_on_equiv_classes:
  "const_on_rel (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) R\<^sub>\<int> (natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c)"
proof (rule const_on_int_rel_def)
  fix x y
  assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and y_type: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  assume natpair2int_eq: "natpair2int \<circ>\<^sub>c x = natpair2int \<circ>\<^sub>c y"

  show "(natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c x = (natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c y"
proof -
obtain cc :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" and cca :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  f1: "\<forall>x0 x1 x2 x3. (\<exists>v4 v5. x3 = \<langle>v4,v5\<rangle> \<and> v4 : x2 \<rightarrow> x1 \<and> v5 : x2 \<rightarrow> x0) = (x3 = \<langle>cc x0 x1 x2 x3,cca x0 x1 x2 x3\<rangle> \<and> cc x0 x1 x2 x3 : x2 \<rightarrow> x1 \<and> cca x0 x1 x2 x3 : x2 \<rightarrow> x0)"
  by moura
  then have f2: "x = \<langle>cc \<nat>\<^sub>c \<nat>\<^sub>c one x,cca \<nat>\<^sub>c \<nat>\<^sub>c one x\<rangle> \<and> cc \<nat>\<^sub>c \<nat>\<^sub>c one x \<in>\<^sub>c \<nat>\<^sub>c \<and> cca \<nat>\<^sub>c \<nat>\<^sub>c one x \<in>\<^sub>c \<nat>\<^sub>c"
using cart_prod_decomp x_type by presburger
have f3: "y = \<langle>cc \<nat>\<^sub>c \<nat>\<^sub>c one y,cca \<nat>\<^sub>c \<nat>\<^sub>c one y\<rangle> \<and> cc \<nat>\<^sub>c \<nat>\<^sub>c one y \<in>\<^sub>c \<nat>\<^sub>c \<and> cca \<nat>\<^sub>c \<nat>\<^sub>c one y \<in>\<^sub>c \<nat>\<^sub>c"
  using f1 cart_prod_decomp y_type by presburger
  have f4: "\<forall>c ca cb cc cd ce cf. \<not> c : ca \<rightarrow> cb \<or> \<not> cc : cb \<rightarrow> cd \<or> \<not> ce : cd \<rightarrow> cf \<or> ce \<circ>\<^sub>c cc \<circ>\<^sub>c c = (ce \<circ>\<^sub>c cc) \<circ>\<^sub>c c"
    using comp_associative2 by satx
then have f5: "(natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c x = equiv_class R\<^sub>\<int> \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x"
  using nat2int_type natpair2int_def swap_type x_type by fastforce
  have "\<langle>\<langle>cc \<nat>\<^sub>c \<nat>\<^sub>c one x,cca \<nat>\<^sub>c \<nat>\<^sub>c one x\<rangle>,\<langle>cc \<nat>\<^sub>c \<nat>\<^sub>c one y,cca \<nat>\<^sub>c \<nat>\<^sub>c one y\<rangle>\<rangle> \<in>\<^bsub>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^esub> R\<^sub>\<int>"
    using f3 f2 by (simp add: cfunc_prod_type equiv_is_natpair2int_eq natpair2int_eq x_type y_type)
  then have "natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>cc \<nat>\<^sub>c \<nat>\<^sub>c one x,cca \<nat>\<^sub>c \<nat>\<^sub>c one x\<rangle> = natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>cc \<nat>\<^sub>c \<nat>\<^sub>c one y,cca \<nat>\<^sub>c \<nat>\<^sub>c one y\<rangle>"
using f3 f2 by (meson quot_map_swap_constant_on_equiv)
  then show ?thesis
    using f5 f4 f3 f2 nat2int_type natpair2int_def swap_type y_type by fastforce
qed
qed


lemma neg_int_type[type_rule]:
 "neg_int: \<int>\<^sub>c \<rightarrow> \<int>\<^sub>c"
  by (metis ETCS_Int.int_def NN_rel_is_relation comp_type lift_int_func_def nat2int_type natpair2int_swap_const_on_equiv_classes neg_int_def quotient_func_type swap_type)
  
lemma neg_square: 
  "neg_int \<circ>\<^sub>c natpair2int = natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c"
  using comp_type lift_int_func_natpair2int_eq nat2int_type natpair2int_swap_const_on_equiv_classes neg_int_def swap_type by fastforce

lemma neg_el:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "neg_int \<circ>\<^sub>c natpair2int \<circ>\<^sub>c \<langle>m,n\<rangle> = natpair2int \<circ>\<^sub>c \<langle>n,m\<rangle>" 
proof - 
  have "neg_int \<circ>\<^sub>c natpair2int \<circ>\<^sub>c \<langle>m,n\<rangle> = natpair2int \<circ>\<^sub>c swap \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative neg_square)
  also have "... = natpair2int \<circ>\<^sub>c \<langle>n,m\<rangle>"
    using assms swap_ap by auto
  then show ?thesis using calculation by auto
qed


lemma neg_zero:
  "neg_int \<circ>\<^sub>c natpair2int \<circ>\<^sub>c \<langle>zero, zero\<rangle> = natpair2int \<circ>\<^sub>c \<langle>zero, zero\<rangle>"
  by (simp add: neg_el zero_type)
  


lemma neg_cancels_neg: 
  "neg_int \<circ>\<^sub>c neg_int = id \<int>\<^sub>c"
  by (typecheck_cfuncs, smt comp_associative2 id_right_unit2 int2natpair_type nat2int_type natpair2int_int2natpair neg_square swap_idempotent swap_type)


lemma neg_cancels_neg2: 
  assumes "n \<in>\<^sub>c \<int>\<^sub>c"
  shows "neg_int \<circ>\<^sub>c neg_int \<circ>\<^sub>c n = n"
  using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative id_left_unit2 neg_cancels_neg)







section \<open>Integer Addition\<close>

definition add_lefts :: "cfunc" where
  "add_lefts = add2 \<circ>\<^sub>c lefts \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c"

lemma add_lefts_type[type_rule]: "add_lefts : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_lefts_def by typecheck_cfuncs

lemma add_lefts_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_lefts \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add2 \<circ>\<^sub>c \<langle>a,c\<rangle>"
  unfolding add_lefts_def using assms
  by (typecheck_cfuncs, smt comp_associative2 lefts_apply)

definition add_rights :: "cfunc" where
  "add_rights = add2 \<circ>\<^sub>c rights \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c"

lemma add_rights_type[type_rule]: "add_rights : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding add_rights_def by typecheck_cfuncs

lemma add_rights_apply:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_rights \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = add2 \<circ>\<^sub>c \<langle>b,d\<rangle>"
  unfolding add_rights_def using assms
  by (typecheck_cfuncs, smt comp_associative2 rights_apply)

definition add2_int :: "cfunc" where
  "add2_int = lift2\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>add_lefts, add_rights\<rangle>)"

lemma add2_int_const_on_int_rel:
  assumes type_assms: "a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c"
  assumes a_c_equiv: "natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c" and b_d_equiv: "natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d"
  shows "(natpair2int \<circ>\<^sub>c \<langle>add_lefts, add_rights\<rangle>) \<circ>\<^sub>c \<langle>a, b\<rangle> = (natpair2int \<circ>\<^sub>c \<langle>add_lefts, add_rights\<rangle>) \<circ>\<^sub>c \<langle>c, d\<rangle>"
proof -
  obtain a1 a2 b1 b2 c1 c2 d1 d2 where
    inner_type_assms: "a1 \<in>\<^sub>c \<nat>\<^sub>c" "a2 \<in>\<^sub>c \<nat>\<^sub>c" "b1 \<in>\<^sub>c \<nat>\<^sub>c" "b2 \<in>\<^sub>c \<nat>\<^sub>c" "c1 \<in>\<^sub>c \<nat>\<^sub>c" "c2 \<in>\<^sub>c \<nat>\<^sub>c" "d1 \<in>\<^sub>c \<nat>\<^sub>c" "d2 \<in>\<^sub>c \<nat>\<^sub>c"
    and pair_expansions: "a = \<langle>a1,a2\<rangle>" "b = \<langle>b1,b2\<rangle>" "c = \<langle>c1,c2\<rangle>" "d = \<langle>d1,d2\<rangle>"
    by (smt cart_prod_decomp type_assms)

  have "a1 +\<^sub>\<nat> c2 = a2 +\<^sub>\<nat> c1 \<and> b1 +\<^sub>\<nat> d2 = b2 +\<^sub>\<nat> d1"
    using a_c_equiv b_d_equiv inner_type_assms nat_pair_eq pair_expansions by auto
  then have "a1 +\<^sub>\<nat> c2 +\<^sub>\<nat> b1 +\<^sub>\<nat> d2 = a2 +\<^sub>\<nat> c1 +\<^sub>\<nat> b2 +\<^sub>\<nat> d1"
    by (smt add_associates add_type inner_type_assms)
  then have "(a1 +\<^sub>\<nat> b1) +\<^sub>\<nat> (c2 +\<^sub>\<nat> d2) = (a2 +\<^sub>\<nat> b2) +\<^sub>\<nat> (c1 +\<^sub>\<nat> d1)"
    by (smt add_associates add_commutes add_type inner_type_assms)
  then have "natpair2int \<circ>\<^sub>c \<langle>a1 +\<^sub>\<nat> b1, a2 +\<^sub>\<nat> b2\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c1 +\<^sub>\<nat> d1, c2 +\<^sub>\<nat> d2\<rangle>"
    using inner_type_assms by (typecheck_cfuncs, simp add: add_commutes nat_pair_eq)
  then have "natpair2int \<circ>\<^sub>c \<langle>add_lefts \<circ>\<^sub>c \<langle>a, b\<rangle> , add_rights \<circ>\<^sub>c \<langle>a, b\<rangle>\<rangle>
      = natpair2int \<circ>\<^sub>c \<langle>add_lefts \<circ>\<^sub>c \<langle>c, d\<rangle>, add_rights \<circ>\<^sub>c \<langle>c, d\<rangle>\<rangle>"
    using add2_apply add_def2 add_lefts_apply add_rights_apply inner_type_assms pair_expansions by auto
  then have "natpair2int \<circ>\<^sub>c \<langle>add_lefts,add_rights\<rangle> \<circ>\<^sub>c \<langle>a,b\<rangle> = natpair2int \<circ>\<^sub>c \<langle>add_lefts,add_rights\<rangle> \<circ>\<^sub>c \<langle>c,d\<rangle>"
    using type_assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  then show "(natpair2int \<circ>\<^sub>c \<langle>add_lefts,add_rights\<rangle>) \<circ>\<^sub>c \<langle>a,b\<rangle> = (natpair2int \<circ>\<^sub>c \<langle>add_lefts,add_rights\<rangle>) \<circ>\<^sub>c \<langle>c,d\<rangle>"
    using type_assms by (typecheck_cfuncs, simp add: comp_associative2)
qed

lemma add2_int_type[type_rule]:
  "add2_int : \<int>\<^sub>c \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> \<int>\<^sub>c"
  unfolding add2_int_def using add2_int_const_on_int_rel by (typecheck_cfuncs, blast)

definition add_int :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "+\<^sub>\<int>" 65)
  where "m +\<^sub>\<int> n = add2_int \<circ>\<^sub>c \<langle>m, n\<rangle>"

lemma add_type[type_rule]:
  assumes "m : X \<rightarrow> \<int>\<^sub>c" "n : X \<rightarrow> \<int>\<^sub>c"
  shows "m +\<^sub>\<int> n : X \<rightarrow> \<int>\<^sub>c"
  unfolding add_int_def using assms by typecheck_cfuncs


lemma add2_int_natpair2int_eq:
  "add2_int \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) = natpair2int \<circ>\<^sub>c \<langle>add_lefts, add_rights\<rangle>"
  unfolding add2_int_def using add2_int_const_on_int_rel 
  by (rule lift2_int_func_natpair2int_eq[where Y="\<int>\<^sub>c"], blast+, typecheck_cfuncs)

lemma add2_int_natpair2int_eq_el_form:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c"  "c \<in>\<^sub>c \<nat>\<^sub>c"  "d \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "\<langle>add_lefts, add_rights\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,\<langle>c,d\<rangle>\<rangle> = 
    \<langle>add2 \<circ>\<^sub>c \<langle>a,c\<rangle>, add2 \<circ>\<^sub>c \<langle>b,d\<rangle>\<rangle>"
  using assms add_lefts_apply add_rights_apply cfunc_prod_comp 
  by (typecheck_cfuncs, force)

lemma addZtoAddN:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c"  "c \<in>\<^sub>c \<nat>\<^sub>c"  "d \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "(natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle>) = 
          natpair2int \<circ>\<^sub>c \<langle> a +\<^sub>\<nat> c , b +\<^sub>\<nat> d\<rangle>"
proof - 
  have "(natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle>) =
        add2_int \<circ>\<^sub>c \<langle>natpair2int \<circ>\<^sub>c \<langle>a,b\<rangle>,  natpair2int \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    by (simp add: add_int_def)
  also have "... = add2_int \<circ>\<^sub>c (natpair2int \<times>\<^sub>f natpair2int) \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>, \<langle>c,d\<rangle> \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = natpair2int \<circ>\<^sub>c \<langle>add_lefts, add_rights\<rangle> \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>, \<langle>c,d\<rangle> \<rangle>"
    using assms by (typecheck_cfuncs,  simp add: add2_int_natpair2int_eq comp_associative2)
  also have "... = natpair2int \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a,c\<rangle>, add2 \<circ>\<^sub>c \<langle>b, d\<rangle> \<rangle>"
    by (simp add: add2_int_natpair2int_eq_el_form assms)
  also have "... = natpair2int \<circ>\<^sub>c \<langle> a +\<^sub>\<nat> c , b +\<^sub>\<nat> d\<rangle>"
    by (simp add: add_def)
  then show ?thesis using calculation by auto
qed
  
    









lemma addZ_respects_zero_left:
  assumes "x \<in>\<^sub>c \<int>\<^sub>c"
  shows "(natpair2int \<circ>\<^sub>c\<langle>zero, zero\<rangle>) +\<^sub>\<int> x = x"
proof - 
  obtain n m  where x_def:"n  \<in>\<^sub>c \<nat>\<^sub>c \<and> m  \<in>\<^sub>c \<nat>\<^sub>c \<and> x = natpair2int \<circ>\<^sub>c\<langle>m, n\<rangle>"
    using assms representation_theorem by blast
  then have "(natpair2int \<circ>\<^sub>c\<langle>zero, zero\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c\<langle>m, n\<rangle>) = 
              natpair2int \<circ>\<^sub>c \<langle> zero +\<^sub>\<nat> m , zero +\<^sub>\<nat> n\<rangle>"
    by (simp add: addZtoAddN zero_type)
  also have "... = natpair2int \<circ>\<^sub>c \<langle> m , n\<rangle>"
    by (simp add: add_respects_zero_on_left x_def)
  also have "... = x"
    by (simp add: x_def)
  then show ?thesis using calculation by auto
qed

lemma addZ_commutative:
  assumes "x \<in>\<^sub>c \<int>\<^sub>c" "y \<in>\<^sub>c \<int>\<^sub>c"
  shows "x +\<^sub>\<int> y = y +\<^sub>\<int> x"
proof - 
  obtain a b c d where xy_defs: "a  \<in>\<^sub>c \<nat>\<^sub>c \<and> b  \<in>\<^sub>c \<nat>\<^sub>c \<and> c  \<in>\<^sub>c \<nat>\<^sub>c \<and> d  \<in>\<^sub>c \<nat>\<^sub>c \<and>
            x = natpair2int \<circ>\<^sub>c\<langle>a, b\<rangle> \<and> y = natpair2int \<circ>\<^sub>c\<langle>c, d\<rangle>"
    using assms representation_theorem by blast
  then have "x +\<^sub>\<int> y = (natpair2int \<circ>\<^sub>c\<langle>a, b\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c\<langle>c, d\<rangle>)"
    by simp
  also have "... = natpair2int \<circ>\<^sub>c \<langle>a +\<^sub>\<nat> c, b +\<^sub>\<nat> d\<rangle>"
    by (simp add: addZtoAddN xy_defs)
  also have "... = natpair2int \<circ>\<^sub>c \<langle>c +\<^sub>\<nat> a, d +\<^sub>\<nat> b\<rangle>"
    by (simp add: add_commutes xy_defs)
  also have "... = (natpair2int \<circ>\<^sub>c\<langle>c, d\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c\<langle>a, b\<rangle>)"
    by (simp add: addZtoAddN xy_defs)
  also have "... = y +\<^sub>\<int> x"
    by (simp add: xy_defs)
  then show ?thesis using calculation by auto
qed

lemma addZ_respects_zero_right:
  assumes "x \<in>\<^sub>c \<int>\<^sub>c"
  shows "x +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>zero, zero\<rangle>) = x"
  by (metis addZtoAddN add_respects_zero_on_right assms representation_theorem zero_type)

(*Eventually we should prove that 0 is the unique element with this property*)

lemma addZ_associative:
  assumes "x \<in>\<^sub>c \<int>\<^sub>c" "y \<in>\<^sub>c \<int>\<^sub>c" "z \<in>\<^sub>c \<int>\<^sub>c" 
  shows "(x +\<^sub>\<int> y) +\<^sub>\<int> z = x +\<^sub>\<int> (y +\<^sub>\<int> z)"
proof - 
  obtain x1 x2 y1 y2 z1 z2 where xyz_defs: 
"x1 \<in>\<^sub>c \<nat>\<^sub>c \<and> x2 \<in>\<^sub>c \<nat>\<^sub>c \<and> y1 \<in>\<^sub>c \<nat>\<^sub>c \<and> y2 \<in>\<^sub>c \<nat>\<^sub>c \<and> z1 \<in>\<^sub>c \<nat>\<^sub>c \<and> z2 \<in>\<^sub>c \<nat>\<^sub>c \<and>
 x = natpair2int \<circ>\<^sub>c \<langle>x1,x2\<rangle> \<and>
 y = natpair2int \<circ>\<^sub>c \<langle>y1,y2\<rangle> \<and> 
 z = natpair2int \<circ>\<^sub>c \<langle>z1,z2\<rangle>"
    by (meson assms representation_theorem) 
  then have "(x +\<^sub>\<int> y) +\<^sub>\<int> z = 
((natpair2int \<circ>\<^sub>c \<langle>x1,x2\<rangle>)  +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>y1,y2\<rangle>))  +\<^sub>\<int>  (natpair2int \<circ>\<^sub>c \<langle>z1,z2\<rangle>)"
    by blast
  also have "... = 
(natpair2int \<circ>\<^sub>c \<langle> x1 +\<^sub>\<nat> y1 , x2 +\<^sub>\<nat> y2\<rangle>)  +\<^sub>\<int>  (natpair2int \<circ>\<^sub>c \<langle>z1,z2\<rangle>)"
    by (simp add: addZtoAddN xyz_defs)
  also have "... = 
natpair2int \<circ>\<^sub>c \<langle> (x1 +\<^sub>\<nat> y1) +\<^sub>\<nat> z1 , (x2 +\<^sub>\<nat> y2) +\<^sub>\<nat> z2\<rangle>"
    by (simp add: ETCS_Add.add_type addZtoAddN xyz_defs)
  also have "... = 
natpair2int \<circ>\<^sub>c \<langle> x1 +\<^sub>\<nat> (y1 +\<^sub>\<nat> z1) , x2 +\<^sub>\<nat> (y2 +\<^sub>\<nat> z2)\<rangle>"
    by (simp add: add_associates xyz_defs)
  also have "... =
(natpair2int \<circ>\<^sub>c \<langle> x1  , x2\<rangle>)  +\<^sub>\<int>  (natpair2int \<circ>\<^sub>c \<langle>y1 +\<^sub>\<nat> z1 ,y2 +\<^sub>\<nat> z2\<rangle>)"
    by (simp add: ETCS_Add.add_type addZtoAddN xyz_defs)
  also have "... = 
(natpair2int \<circ>\<^sub>c \<langle>x1,x2\<rangle>)  +\<^sub>\<int> ((natpair2int \<circ>\<^sub>c \<langle>y1,y2\<rangle>)  +\<^sub>\<int>  (natpair2int \<circ>\<^sub>c \<langle>z1,z2\<rangle>))"
    by (simp add: addZtoAddN xyz_defs)
  also have "... = x +\<^sub>\<int> (y +\<^sub>\<int> z)"
    by (simp add: xyz_defs)
  then show ?thesis using calculation by auto
qed

lemma add_neg:
  assumes "x \<in>\<^sub>c \<int>\<^sub>c"
  shows "x +\<^sub>\<int> (neg_int \<circ>\<^sub>c x) = natpair2int \<circ>\<^sub>c \<langle>zero, zero\<rangle>"
proof - 
  obtain n where x_def: "n \<in>\<^sub>c \<nat>\<^sub>c \<and> 
(x = natpair2int \<circ>\<^sub>c \<langle>zero, n\<rangle> \<or> x = natpair2int \<circ>\<^sub>c \<langle>n, zero\<rangle>)"
    using assms canonical_representation_theorem by blast
  then show ?thesis 
  proof(cases "x = natpair2int \<circ>\<^sub>c \<langle>zero, n\<rangle>",auto)
    assume "x = natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>"  
    assume "n \<in>\<^sub>c \<nat>\<^sub>c"
    have  "(natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>) +\<^sub>\<int> (neg_int \<circ>\<^sub>c natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>) =
         (natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>)"
      by (simp add: neg_el x_def zero_type)
    also have "... = add2_int \<circ>\<^sub>c \<langle>natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>,  natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>\<rangle>"
      by (simp add: add_int_def) 
    also have "... = natpair2int \<circ>\<^sub>c \<langle>n,n\<rangle>"
      by (metis \<open>(natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>) = add2_int \<circ>\<^sub>c \<langle>natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>,natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>\<rangle>\<close> addZtoAddN add_respects_zero_on_right nat_pair_eq x_def zero_type)
    also have "... = natpair2int \<circ>\<^sub>c \<langle>zero,zero\<rangle>"
      by (simp add: nat_pair_eq x_def zero_type)
    then show "(natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>) +\<^sub>\<int> (neg_int \<circ>\<^sub>c natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>) =
    natpair2int \<circ>\<^sub>c \<langle>zero,zero\<rangle>"
      by (simp add: calculation)
  next
 assume "x = natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>"
 assume "n \<in>\<^sub>c \<nat>\<^sub>c"
have  "(natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>) +\<^sub>\<int> (neg_int \<circ>\<^sub>c natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>) =
         (natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>)"
      by (simp add: neg_el x_def zero_type)
    also have "... = add2_int \<circ>\<^sub>c \<langle>natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>,  natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>\<rangle>"
      by (simp add: add_int_def) 
    also have "... = natpair2int \<circ>\<^sub>c \<langle>n,n\<rangle>"
      by (metis \<open>(natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>) +\<^sub>\<int> (natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>) = add2_int \<circ>\<^sub>c \<langle>natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>,natpair2int \<circ>\<^sub>c \<langle>zero,n\<rangle>\<rangle>\<close> addZtoAddN add_respects_zero_on_left nat_pair_eq x_def zero_type)
    also have "... = natpair2int \<circ>\<^sub>c \<langle>zero,zero\<rangle>"
      by (simp add: nat_pair_eq x_def zero_type)
    then show "(natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>) +\<^sub>\<int> (neg_int \<circ>\<^sub>c natpair2int \<circ>\<^sub>c \<langle>n,zero\<rangle>) =
    natpair2int \<circ>\<^sub>c \<langle>zero,zero\<rangle>"
      by (simp add: calculation)
  qed
qed


lemma add_inverse_unique:
  assumes "x \<in>\<^sub>c \<int>\<^sub>c" "y \<in>\<^sub>c \<int>\<^sub>c"
  shows "x +\<^sub>\<int> y = natpair2int \<circ>\<^sub>c \<langle>zero, zero\<rangle> \<Longrightarrow> y = neg_int \<circ>\<^sub>c x"
  by (smt addZ_associative addZ_respects_zero_right add_neg assms comp_type neg_cancels_neg2 neg_int_type)

section \<open>Integer Multiplication\<close>

definition mult2_natpair :: "cfunc" where
  "mult2_natpair = \<langle>
      add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c outers \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c, mult2 \<circ>\<^sub>c inners \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
      add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c lefts \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c, mult2 \<circ>\<^sub>c rights \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
    \<rangle>"


lemma mult2_natpair_type[type_rule]: 
  "mult2_natpair : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
  unfolding mult2_natpair_def by typecheck_cfuncs

lemma mult2_natpair_apply: 
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "mult2_natpair \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> = \<langle>(a \<cdot>\<^sub>\<nat> d) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c), (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> d)\<rangle>"
proof - 
  have "mult2_natpair \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> =
 \<langle>
      add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c outers \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c, mult2 \<circ>\<^sub>c inners \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
      add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c lefts \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c, mult2 \<circ>\<^sub>c rights \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle>"
    by (simp add: mult2_natpair_def)
  also have "... = \<langle>
      add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c outers \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle>, mult2 \<circ>\<^sub>c inners \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> \<rangle>,
      add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c lefts \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle>, mult2 \<circ>\<^sub>c rights \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> \<rangle>\<rangle> "
    using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
  also have "... =  \<langle>(a \<cdot>\<^sub>\<nat> d) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c), (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> d)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: add_def inners_apply lefts_apply mult_def outers_apply rights_apply)
  then show ?thesis using calculation by auto
qed


lemma mult2_natpair_const_on_int_rel:
  assumes type_assms: "a \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c"
  assumes a_c_equiv: "natpair2int \<circ>\<^sub>c a = natpair2int \<circ>\<^sub>c c" and b_d_equiv: "natpair2int \<circ>\<^sub>c b = natpair2int \<circ>\<^sub>c d"
  shows "(natpair2int \<circ>\<^sub>c mult2_natpair) \<circ>\<^sub>c \<langle>a, b\<rangle> = (natpair2int \<circ>\<^sub>c mult2_natpair) \<circ>\<^sub>c \<langle>c, d\<rangle>"
proof - 
  obtain a1 a2 b1 b2 c1 c2 d1 d2 where pairs_def: "a1 \<in>\<^sub>c \<nat>\<^sub>c \<and> a2 \<in>\<^sub>c \<nat>\<^sub>c \<and>
 b1 \<in>\<^sub>c \<nat>\<^sub>c \<and> b2 \<in>\<^sub>c \<nat>\<^sub>c \<and>  c1 \<in>\<^sub>c \<nat>\<^sub>c \<and> c2 \<in>\<^sub>c \<nat>\<^sub>c \<and> d1 \<in>\<^sub>c \<nat>\<^sub>c \<and> d2 \<in>\<^sub>c \<nat>\<^sub>c \<and> 
 a =  \<langle>a1,a2\<rangle> \<and>
 b =  \<langle>b1,b2\<rangle> \<and>
 c =  \<langle>c1,c2\<rangle> \<and>
 d =  \<langle>d1,d2\<rangle> "
    by (smt cart_prod_decomp type_assms)
  then have rel1: "natpair2int \<circ>\<^sub>c \<langle>a1,a2\<rangle> = natpair2int \<circ>\<^sub>c \<langle>c1,c2\<rangle>"
    using a_c_equiv by blast
  have rel2: "natpair2int \<circ>\<^sub>c \<langle>b1,b2\<rangle> = natpair2int \<circ>\<^sub>c \<langle>d1,d2\<rangle>"
    using b_d_equiv pairs_def by blast
  have equiv_eqn1: "a2 +\<^sub>\<nat> c1 = a1 +\<^sub>\<nat> c2"
    using nat_pair_eq pairs_def rel1 by auto
  have equiv_eqn2: "(b2 +\<^sub>\<nat> d1 = b1 +\<^sub>\<nat> d2)"
    using nat_pair_eq pairs_def rel2 by auto
  have eqn1: "(a1\<cdot>\<^sub>\<nat> c1) +\<^sub>\<nat> (b1 +\<^sub>\<nat> a2)\<cdot>\<^sub>\<nat> d2 = (a1\<cdot>\<^sub>\<nat> c1) +\<^sub>\<nat> (a2 +\<^sub>\<nat> b1)\<cdot>\<^sub>\<nat> d2"
    by (simp add: add_commutes pairs_def)
  also have "... = (a1\<cdot>\<^sub>\<nat> c1) +\<^sub>\<nat> ((a2\<cdot>\<^sub>\<nat>d2) +\<^sub>\<nat> (b1\<cdot>\<^sub>\<nat>d2))"



definition mult2_int :: "cfunc" where
  "mult2_int = lift2\<^sub>\<int> (natpair2int \<circ>\<^sub>c mult2_natpair)"

lemma mult2_int_type[type_rule]: 
  "mult2_int : \<int>\<^sub>c \<times>\<^sub>c \<int>\<^sub>c \<rightarrow> \<int>\<^sub>c"
  unfolding mult2_int_def using mult2_natpair_const_on_int_rel by (typecheck_cfuncs, blast)
  

end