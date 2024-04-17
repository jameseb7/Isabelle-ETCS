theory ETCS_Empty
  imports ETCS_Coproduct
begin

section  \<open>Axiom 8: Empty Set\<close>

axiomatization
  initial_func :: "cset \<Rightarrow> cfunc" ("\<alpha>\<^bsub>_\<^esub>" 100) and
  emptyset :: "cset" ("\<emptyset>")
where
  initial_func_type[type_rule]: "initial_func X :  \<emptyset> \<rightarrow> X" and
  initial_func_unique: "h : \<emptyset> \<rightarrow> X \<Longrightarrow> h = initial_func X" and
  emptyset_is_empty: "\<not>(x \<in>\<^sub>c \<emptyset>)"


(*characteristic_function_exists:
    "\<forall> X m. ((m : B \<rightarrow> X) \<and> monomorphism(m)) \<longrightarrow> (\<exists>! \<chi>. is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi> )"*)

definition initial_object :: "cset \<Rightarrow> bool" where
  "initial_object(X) \<longleftrightarrow> (\<forall> Y. \<exists>! f. f : X \<rightarrow> Y)"


lemma emptyset_is_initial:
  "initial_object(\<emptyset>)"
  using initial_func_type initial_func_unique initial_object_def by blast

lemma initial_iso_empty:
  assumes "initial_object(X)"
  shows "X \<cong> \<emptyset>"
  by (metis assms cfunc_type_def comp_type emptyset_is_empty epi_mon_is_iso initial_object_def injective_def injective_imp_monomorphism is_isomorphic_def singletonI surjective_def surjective_is_epimorphism)



(* Exercise 2.4.6 *)
lemma coproduct_with_zero_does_nothing:
  shows "X \<Coprod> \<emptyset> \<cong> X"
proof -
  have comp1: "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = left_coproj X \<emptyset>"
  proof -
    have "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) =
            (left_coproj X \<emptyset>) \<circ>\<^sub>c ((id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c (left_coproj X \<emptyset>))"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (left_coproj X \<emptyset>) \<circ>\<^sub>c id(X)"
      by (typecheck_cfuncs, metis left_coproj_cfunc_coprod)
    also have "... = left_coproj X \<emptyset>"
      by (typecheck_cfuncs, metis id_right_unit2)
    then show ?thesis using calculation by auto
  qed
  have comp2: "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = right_coproj X \<emptyset>"
  proof -
    have "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = 
             (left_coproj X \<emptyset>) \<circ>\<^sub>c ((id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c (right_coproj X \<emptyset>))"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (left_coproj X \<emptyset>) \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>"
      by (typecheck_cfuncs, metis right_coproj_cfunc_coprod)
    also have "... = right_coproj X \<emptyset>"
      by (typecheck_cfuncs, metis initial_func_unique)
    then show ?thesis using calculation by auto
  qed
  then have fact1: "((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = (left_coproj X \<emptyset>)"
    using left_coproj_cfunc_coprod by (typecheck_cfuncs, blast)
  then have fact2: "((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = (right_coproj X \<emptyset>)"
    using right_coproj_cfunc_coprod by (typecheck_cfuncs, blast)
  then have concl: "(left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) = ((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>))"
    using cfunc_coprod_unique comp1 comp2 by (typecheck_cfuncs, blast)
  also have "... = id(X\<Coprod>\<emptyset>)"
    using cfunc_coprod_unique id_left_unit2 by (typecheck_cfuncs, auto)
  then have "isomorphism(id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)"
    unfolding isomorphism_def 
    by (rule_tac x="left_coproj X \<emptyset>" in exI, typecheck_cfuncs, simp add: cfunc_type_def concl left_coproj_cfunc_coprod)
  then show "X\<Coprod>\<emptyset> \<cong> X"
    using cfunc_coprod_type id_type initial_func_type is_isomorphic_def by blast
qed



(* Proposition 2.4.7 *)
lemma function_to_empty_is_iso:
  assumes "f: X \<rightarrow> \<emptyset>"
  shows "isomorphism(f)"
  by (metis assms cfunc_type_def comp_type emptyset_is_empty epi_mon_is_iso injective_def injective_imp_monomorphism singletonI surjective_def surjective_is_epimorphism)




lemma zero_times_X:
  "\<emptyset> \<times>\<^sub>c X \<cong> \<emptyset>"
  using cfunc_type_def function_to_empty_is_iso is_isomorphic_def left_cart_proj_type by blast

lemma X_times_zero: 
  "X \<times>\<^sub>c \<emptyset> \<cong> \<emptyset>"
  using cfunc_type_def function_to_empty_is_iso is_isomorphic_def right_cart_proj_type by blast





(* Proposition  2.4.8 *)
lemma no_el_iff_iso_0:
  "\<not>(nonempty(X)) \<longleftrightarrow> X \<cong> \<emptyset>"
proof auto
  assume "X \<cong> \<emptyset>"
  then show "nonempty X \<Longrightarrow> False "
    using comp_type emptyset_is_empty is_isomorphic_def nonempty_def by blast
  have "\<not>(nonempty(X))"
    using \<open>nonempty X \<Longrightarrow> False\<close> by blast
next 
  assume "\<not>(nonempty(X))"
  obtain f where f_type: "f: \<emptyset> \<rightarrow> X"
    using initial_func_type by blast  (* f = \<alpha>_X *)
 
  have  f_inj: "injective(f)"
    using cfunc_type_def emptyset_is_empty f_type injective_def by auto
  then have f_mono: "monomorphism(f)"
    using  cfunc_type_def f_type injective_imp_monomorphism by blast
  have f_surj: "surjective(f)"
    using \<open>\<not> nonempty X\<close> cfunc_type_def f_type nonempty_def surjective_def by auto
  then have epi_f: "epimorphism(f)"
    using surjective_is_epimorphism by blast
  then have iso_f: "isomorphism(f)"
    using cfunc_type_def epi_mon_is_iso f_mono f_type by blast
  then show "X \<cong> \<emptyset>"
    using f_type is_isomorphic_def isomorphic_is_symmetric by blast
qed

lemma initial_maps_mono:
  assumes "initial_object(X)"
  assumes "f : X \<rightarrow> Y"
  shows "monomorphism(f)"
  by (metis UNIV_I assms cfunc_type_def initial_iso_empty injective_def injective_imp_monomorphism no_el_iff_iso_0 nonempty_def)



lemma iso_empty_initial:
  assumes "X \<cong> \<emptyset>"
  shows "initial_object(X)"
  unfolding initial_object_def
  by (meson assms comp_type is_isomorphic_def isomorphic_is_symmetric isomorphic_is_transitive no_el_iff_iso_0 nonempty_def one_separator terminal_func_type)
 

lemma function_to_empty_set_is_iso:
  assumes "f: X \<rightarrow> Y"
  assumes "\<not>(nonempty(Y))"
  shows "isomorphism(f)"
  by (metis assms cfunc_type_def comp_type epi_mon_is_iso injective_def injective_imp_monomorphism nonempty_def singletonI surjective_def surjective_is_epimorphism)
  


lemma prod_iso_to_empty_right:
  assumes "nonempty(X)"
  assumes "X \<times>\<^sub>c Y \<cong> \<emptyset>"
  shows "\<not>(nonempty(Y))"
  by (meson assms cfunc_prod_type no_el_iff_iso_0 nonempty_def)

lemma prod_iso_to_empty_left:
  assumes "nonempty(Y)"
  assumes "X \<times>\<^sub>c Y \<cong> \<emptyset>"
  shows "\<not>(nonempty(X))"
  using assms prod_iso_to_empty_right by blast

 


lemma empty_subset: "(\<emptyset>, \<alpha>\<^bsub>X\<^esub>) \<subseteq>\<^sub>c X"
  by (metis UNIV_I cfunc_type_def emptyset_is_empty initial_func_type injective_def injective_imp_monomorphism subobject_of_def2)

(* Proposition 2.2.1 *)
lemma "card ({(X,m). (X,m) \<subseteq>\<^sub>c one}//{((X,m1),(Y,m2)). X \<cong> Y}) = 2"
proof -
  have one_subobject: "(one, id one) \<subseteq>\<^sub>c one"
    using element_monomorphism id_type subobject_of_def2 by blast
  have empty_subobject: "(\<emptyset>, \<alpha>\<^bsub>one\<^esub>) \<subseteq>\<^sub>c one"
    by (simp add: empty_subset)

  have subobject_one_or_empty: "\<And>X m. (X,m) \<subseteq>\<^sub>c one \<Longrightarrow> X \<cong> one \<or> X \<cong> \<emptyset>"
  proof -
    fix X m
    assume X_m_subobject: "(X, m) \<subseteq>\<^sub>c one"

    obtain \<chi> where \<chi>_pullback: "is_pullback X one one \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> m \<chi>"
      using X_m_subobject characteristic_function_exists subobject_of_def2 by blast
    then have \<chi>_true_or_false: "\<chi> = \<t> \<or> \<chi> = \<f>"
      unfolding is_pullback_def square_commutes_def using true_false_only_truth_values by auto

    have true_iso_one: "\<chi> = \<t> \<Longrightarrow> X \<cong> one"
    proof -
      assume \<chi>_true: "\<chi> = \<t>"
      then have "\<exists>! x. x \<in>\<^sub>c X"
        using \<chi>_pullback unfolding is_pullback_def         
        by (clarsimp, (erule_tac x=one in allE, erule_tac x="id one" in allE, erule_tac x="id one" in allE), metis comp_type id_type square_commutes_def terminal_func_unique)
      then show "X \<cong> one"
        using single_elem_iso_one by auto
    qed

    have false_iso_one: "\<chi> = \<f> \<Longrightarrow> X \<cong> \<emptyset>"
    proof -
      assume \<chi>_false: "\<chi> = \<f>"
      have "\<nexists> x. x \<in>\<^sub>c X"
      proof auto
        fix x
        assume x_in_X: "x \<in>\<^sub>c X"
        have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> = \<f> \<circ>\<^sub>c m"
          using \<chi>_false \<chi>_pullback is_pullback_def square_commutes_def by auto
        then have "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x) = \<f> \<circ>\<^sub>c (m \<circ>\<^sub>c x)"
          by (smt X_m_subobject comp_associative2 false_func_type subobject_of_def2
              terminal_func_type true_func_type x_in_X)
        then have "\<t> = \<f>"
          by (smt X_m_subobject cfunc_type_def comp_type false_func_type id_right_unit id_type
              subobject_of_def2 terminal_func_unique true_func_type x_in_X)
        then show False
          using true_false_distinct by auto
      qed
      then show "X \<cong> \<emptyset>"
        using no_el_iff_iso_0 nonempty_def by blast
    qed

    show "X \<cong> one \<or> X \<cong> \<emptyset>"
      using \<chi>_true_or_false false_iso_one true_iso_one by blast
  qed

  have classes_distinct: "{(X, m). X \<cong> \<emptyset>} \<noteq> {(X, m). X \<cong> one}"
    by (metis case_prod_eta curry_case_prod emptyset_is_empty id_isomorphism id_type is_isomorphic_def mem_Collect_eq)

  have "{(X, m). (X, m) \<subseteq>\<^sub>c one} // {((X, m1), Y, m2). X \<cong> Y} = {{(X, m). X \<cong> \<emptyset>}, {(X, m). X \<cong> one}}"
    unfolding quotient_def apply auto
    using isomorphic_is_symmetric isomorphic_is_transitive subobject_one_or_empty apply blast+
    using empty_subobject apply (rule_tac x=\<emptyset> in exI, auto simp add: isomorphic_is_symmetric)
    using one_subobject apply (rule_tac x=one in exI, auto simp add: isomorphic_is_symmetric)
    done
  then show "card ({(X, m). (X, m) \<subseteq>\<^sub>c one} // {((X, m1), Y, m2). X \<cong> Y}) = 2"
    by (simp add: classes_distinct)
qed


lemma coprod_with_init_obj1: 
  assumes "initial_object Y"
  shows "X \<Coprod> Y \<cong> X"
  by (meson assms coprod_pres_iso coproduct_with_zero_does_nothing initial_iso_empty isomorphic_is_reflexive isomorphic_is_transitive)

lemma coprod_with_init_obj2: 
  assumes "initial_object X"
  shows "X \<Coprod> Y \<cong> Y"
  using assms coprod_with_init_obj1 coproduct_commutes isomorphic_is_transitive by blast


lemma prod_with_term_obj1:
  assumes "terminal_object(X)" 
  shows  "X \<times>\<^sub>c Y \<cong> Y" 
  by (meson assms isomorphic_is_reflexive isomorphic_is_transitive one_terminal_object one_x_A_iso_A prod_pres_iso terminal_objects_isomorphic)

lemma prod_with_term_obj2:
  assumes "terminal_object(Y)" 
  shows  "X \<times>\<^sub>c Y \<cong> X"
  by (meson assms isomorphic_is_transitive prod_with_term_obj1 product_commutes)

lemma coprojs_jointly_surj':
  assumes z_type[type_rule]: "z : Z \<rightarrow> X \<Coprod> Y"
  shows "(\<exists> x. (x : Z \<rightarrow> X \<and> z = (left_coproj X Y) \<circ>\<^sub>c x))
      \<or>  (\<exists> y. (y : Z \<rightarrow> Y \<and> z = (right_coproj X Y) \<circ>\<^sub>c y))"
proof (cases "\<exists> z'. z' \<in>\<^sub>c Z", auto)
  assume Z_empty: "\<forall>z'. \<not> z' \<in>\<^sub>c Z"
  then have "Z \<cong> \<emptyset>"
    using no_el_iff_iso_0 nonempty_def by auto
  then have "\<exists> f. f : Z \<rightarrow> \<emptyset>"
    using is_isomorphic_def by blast
  then show "\<forall>y. y : Z \<rightarrow> Y \<longrightarrow> z \<noteq> right_coproj X Y \<circ>\<^sub>c y \<Longrightarrow> \<exists>x. x : Z \<rightarrow> X \<and> z = left_coproj X Y \<circ>\<^sub>c x"
    by (auto, rule_tac x="\<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c f" in exI, typecheck_cfuncs, meson Z_empty assms comp_type one_separator)
next
  fix z'
  assume z'_in_Z[type_rule]: "z' \<in>\<^sub>c Z"
  
  have "(\<exists>x. x \<in>\<^sub>c X \<and> z \<circ>\<^sub>c z' = left_coproj X Y \<circ>\<^sub>c x) \<or> (\<exists>y. y \<in>\<^sub>c Y \<and> z \<circ>\<^sub>c z' = right_coproj X Y \<circ>\<^sub>c y)"
    by (typecheck_cfuncs, simp add: coprojs_jointly_surj)
  then show "\<forall>y. y : Z \<rightarrow> Y \<longrightarrow> z \<noteq> right_coproj X Y \<circ>\<^sub>c y \<Longrightarrow> \<exists>x. x : Z \<rightarrow> X \<and> z = left_coproj X Y \<circ>\<^sub>c x"
  proof auto
    fix x
    assume x_type[type_rule]: "x \<in>\<^sub>c X"

    assume x_eq: "z \<circ>\<^sub>c z' = left_coproj X Y \<circ>\<^sub>c x"
    then show "\<exists>x. x : Z \<rightarrow> X \<and> z = left_coproj X Y \<circ>\<^sub>c x"
      apply (rule_tac x="x \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>" in exI, typecheck_cfuncs, auto)
      oops

    thm coprojs_jointly_surj[where z="z \<circ>\<^sub>c z'", where X=X, where Y=Y]




end