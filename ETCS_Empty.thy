theory ETCS_Empty
  imports ETCS_Coproduct
begin

section  \<open>Axiom 8: Empty Set\<close>

axiomatization
  initial_func :: "cset \<Rightarrow> cfunc" ("\<alpha>\<^bsub>_\<^esub>" 100) and
  emptyset :: "cset" ("\<emptyset>")
where
  initial_func_type: "initial_func(X) :  \<emptyset> \<rightarrow> X" and
  initial_func_unique: "((\<forall> h. h : \<emptyset> \<rightarrow> X) \<longrightarrow> (h = initial_func(X)))" and
  emptyset_is_empty: "\<not>(x \<in>\<^sub>c \<emptyset>)"

(*characteristic_function_exists:
    "\<forall> X m. ((m : B \<rightarrow> X) \<and> monomorphism(m)) \<longrightarrow> (\<exists>! \<chi>. is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi> )"*)


(* Exercise 2.4.6 *)
(* This lemma is a pre-requiste to the real version of the theorem. *)
lemma coproduct_with_zero_does_nothing:
  shows "X \<Coprod> \<emptyset> \<cong> X"
proof -
  have i0_type: "(left_coproj X \<emptyset>) : X \<rightarrow> X\<Coprod>\<emptyset>"
    by (simp add: left_proj_type)
  have i1_type: "(right_coproj X \<emptyset>) : \<emptyset> \<rightarrow> X\<Coprod>\<emptyset>"
    by (simp add: right_proj_type)  
  have i0Ui1_type:"(left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>):  X\<Coprod>\<emptyset> \<rightarrow> X\<Coprod>\<emptyset>"
    by (simp add: cfunc_coprod_type i0_type i1_type)
  have idX_U_alpha_X_type: "(id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) : X\<Coprod>\<emptyset> \<rightarrow> X"
    by (simp add: cfunc_coprod_type id_type initial_func_type)
  then have "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = 
          (left_coproj X \<emptyset>) \<circ>\<^sub>c ((id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c (left_coproj X \<emptyset>))"
    by (simp add: comp_associative) 
  also have "... = (left_coproj X \<emptyset>) \<circ>\<^sub>c id(X)"
    by (metis id_type initial_func_type left_coproj_cfunc_coprod)
  also have "... = left_coproj X \<emptyset>"
    by (metis cfunc_type_def i0_type id_right_unit)
  then have comp1: "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = left_coproj X \<emptyset>"
    by (simp add: calculation)
  have "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = 
             (left_coproj X \<emptyset>) \<circ>\<^sub>c ((id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c (right_coproj X \<emptyset>))"
    by (simp add: comp_associative)
  have "... = (left_coproj X \<emptyset>) \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>"
    by (metis id_type initial_func_type right_coproj_cfunc_coprod)
  have "... = right_coproj X \<emptyset>"
    by (meson comp_type emptyset_is_empty initial_func_type left_proj_type one_separator right_proj_type)
  then have comp2: "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) =right_coproj X \<emptyset>"
    by (simp add: \<open>(left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>\<close>)
  then have fact1: "((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = (left_coproj X \<emptyset>)"
    using i0_type i1_type left_coproj_cfunc_coprod by blast
  then have fact2: "((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = (right_coproj X \<emptyset>)"
    using i0_type i1_type right_coproj_cfunc_coprod by blast
  then have concl: "(left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) = ((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>))"
    using \<open>(left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub> = right_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X = left_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>\<close> calculation cfunc_coprod_unique i0_type i1_type idX_U_alpha_X_type by auto
  also have "... = id(X\<Coprod>\<emptyset>)"
    by (metis cfunc_coprod_unique cfunc_type_def i0_type i1_type id_left_unit id_type)
  then have "isomorphism(id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)"
    using cfunc_type_def concl i0_type idX_U_alpha_X_type id_type initial_func_type isomorphism_def left_coproj_cfunc_coprod by auto
  then show "X\<Coprod>\<emptyset> \<cong> X"
    using idX_U_alpha_X_type is_isomorphic_def by blast
qed

(* Proposition 2.4.7 *)
lemma function_to_empty_is_iso:
  assumes "codomain(f) = \<emptyset>" "f \<in> ETCS_func"
  shows "isomorphism(f)"
proof -
  have "surjective(f)"
    by (simp add: assms emptyset_is_empty surjective_def)
  have "epimorphism(f)"
    by (simp add: \<open>surjective f\<close> surjective_is_epimorphism) 
 
  have dom_f_is_empty: "\<not>nonempty(domain(f))"
  proof (rule ccontr, auto)
    assume BWOC:  "nonempty(domain(f))"
    obtain x where x_type: "x \<in>\<^sub>c domain(f)"
    using BWOC nonempty_def by blast
    have contradiction: "f \<circ>\<^sub>c x \<in>\<^sub>c \<emptyset>"
       using assms(1) assms(2) cfunc_type_def comp_type x_type by blast
     show False
       using contradiction emptyset_is_empty by auto
   qed
   have f_inj: "injective(f)"
     using dom_f_is_empty injective_def nonempty_def by blast
   have f_mono: "monomorphism(f)"
     by (simp add: assms(2) f_inj injective_imp_monomorphism)
   show "isomorphism(f)"    (*Modify this proof after you've shown that mono + epi = iso*)
      proof -
          have f1: "f : domain f \<rightarrow> \<emptyset>"
              using assms(1) assms(2) cfunc_type_def by blast
              have f2: "\<forall>c. domain (\<alpha>\<^bsub>c\<^esub>) = \<emptyset>"
              using cfunc_type_def initial_func_type by presburger
              have f3: "f \<circ>\<^sub>c \<alpha>\<^bsub>domain f\<^esub> = id\<^sub>c \<emptyset>"
              using f1 by (meson comp_type emptyset_is_empty id_type initial_func_type one_separator)
              have "\<alpha>\<^bsub>domain f\<^esub> \<circ>\<^sub>c f = id\<^sub>c (domain f)"
              using f1 by (meson comp_type emptyset_is_empty id_type initial_func_type one_separator)
              then show ?thesis
              using f3 f2 assms(1) cfunc_type_def initial_func_type isomorphism_def by auto
      qed
qed

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

lemma empty_subset: "(\<emptyset>, \<alpha>\<^bsub>X\<^esub>) \<subseteq>\<^sub>c X"
  by (metis cfunc_type_def emptyset_is_empty initial_func_type injective_def
      injective_imp_monomorphism subobject_of_def2)

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
      using is_pullback_def square_commutes_def true_false_only_truth_values by auto

    have true_iso_one: "\<chi> = \<t> \<Longrightarrow> X \<cong> one"
    proof -
      assume \<chi>_true: "\<chi> = \<t>"
      then have "\<exists>! x. x \<in>\<^sub>c X"
        using \<chi>_pullback unfolding is_pullback_def apply clarsimp
        apply (erule_tac x=one in allE, erule_tac x="id one" in allE, erule_tac x="id one" in allE)
        by (metis comp_type id_type square_commutes_def terminal_func_unique)
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
          by (simp add: comp_associative)
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

end