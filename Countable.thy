theory Countable
  imports ETCS_Axioms ETCS_Add ETCS_Mult ETCS_Pred ETCS_Parity ETCS_Comparison
begin





(* Definition 2.6.9 *)
definition epi_countable :: "cset \<Rightarrow> bool" where
  "epi_countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

lemma emptyset_is_not_epi_countable:
  "\<not> (epi_countable \<emptyset>)"
  using comp_type emptyset_is_empty epi_countable_def zero_type by blast


(* Definition 2.6.9 *)
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f)"

lemma epi_countable_is_countable: 
  assumes "epi_countable X"
  shows "countable X"
  using assms countable_def epi_countable_def epis_give_monos by blast



lemma emptyset_is_countable:
  "countable \<emptyset>"
  using countable_def empty_subset subobject_of_def2 by blast

lemma natural_numbers_are_countably_infinite:
  "(countable \<nat>\<^sub>c) \<and> (is_infinite \<nat>\<^sub>c)"
  by (meson CollectI Peano's_Axioms countable_def injective_imp_monomorphism is_infinite_def successor_type)




lemma smaller_than_countable_is_countable:
  assumes "X \<le>\<^sub>c Y" "countable Y"
  shows "countable X"
  by (smt assms cfunc_type_def comp_type composition_of_monic_pair_is_monic countable_def is_smaller_than_def)


lemma iso_pres_finite:
  assumes "X \<cong> Y"
  assumes "is_finite(X)"
  shows "is_finite(Y)"
  using assms is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic isomorphic_is_symmetric smaller_than_finite_is_finite by blast


lemma iso_pres_countable:
  assumes "X \<cong> Y" "countable Y"
  shows "countable X"
  using assms(1) assms(2) is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic smaller_than_countable_is_countable by blast


lemma not_finite_and_infinite:
  "\<not>(is_finite(X) \<and> is_infinite(X))"
  using epi_is_surj is_finite_def is_infinite_def iso_imp_epi_and_monic by blast

lemma iso_pres_infinite:
  assumes "X \<cong> Y"
  assumes "is_infinite(X)"
  shows "is_infinite(Y)"
  using assms either_finite_or_infinite not_finite_and_infinite iso_pres_finite isomorphic_is_symmetric by blast

(*Consider moving the result below*)

lemma coprod_leq_product:
  assumes X_not_init: "\<not>(initial_object(X))" 
  assumes Y_not_init: "\<not>(initial_object(Y))" 
  assumes X_not_term: "\<not>(terminal_object(X))"
  assumes Y_not_term: "\<not>(terminal_object(Y))"
  shows "(X \<Coprod> Y) \<le>\<^sub>c (X \<times>\<^sub>c Y)"
proof - 
  obtain x1 x2 where x1x2_def[type_rule]:  "(x1 \<in>\<^sub>c X)" "(x2 \<in>\<^sub>c X)" "(x1 \<noteq> x2)"
    using X_not_init X_not_term iso_empty_initial iso_to1_is_term no_el_iff_iso_0 nonempty_def single_elem_iso_one by blast
  obtain y1 y2 where y1y2_def[type_rule]:  "(y1 \<in>\<^sub>c Y)" "(y2 \<in>\<^sub>c Y)" "(y1 \<noteq> y2)"
    using Y_not_init Y_not_term iso_empty_initial iso_to1_is_term no_el_iff_iso_0 nonempty_def single_elem_iso_one by blast
  then have y1_mono[type_rule]: "monomorphism(y1)"
    using element_monomorphism by blast
  obtain m where m_def: "m = \<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1)"
    by simp
  have type1: "\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> (X \<times>\<^sub>c Y)"
    by (meson cfunc_prod_type comp_type id_type terminal_func_type y1y2_def)
  have trycast_y1_type: "try_cast y1 : Y \<rightarrow> one \<Coprod> (Y \<setminus> (one,y1))"
    by (meson element_monomorphism try_cast_type y1y2_def)
  have y1'_type[type_rule]: "y1\<^sup>c : Y \<setminus> (one,y1) \<rightarrow> Y"
    using complement_morphism_type one_terminal_object terminal_el__monomorphism y1y2_def by blast
  have type4: "\<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle> : Y \<setminus> (one,y1) \<rightarrow> (X \<times>\<^sub>c Y)"
    using cfunc_prod_type comp_type terminal_func_type x1x2_def y1'_type by blast
  have type5: "\<langle>x2, y2\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Y)"
    by (simp add: cfunc_prod_type x1x2_def y1y2_def)
  then have type6: "\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle> :(one \<Coprod> (Y \<setminus> (one,y1))) \<rightarrow> (X \<times>\<^sub>c Y)"
    using cfunc_coprod_type type4 by blast
  then have type7: "((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) : Y \<rightarrow> (X \<times>\<^sub>c Y)"
    using comp_type trycast_y1_type by blast
  then have m_type: "m : X  \<Coprod> Y \<rightarrow> (X \<times>\<^sub>c Y)"
    by (simp add: cfunc_coprod_type m_def type1)

  have relative: "\<And>y. y \<in>\<^sub>c Y \<Longrightarrow> (y \<in>\<^bsub>Y\<^esub> (one, y1)) = (y = y1)"
  proof(auto)
    fix y 
    assume y_type: "y \<in>\<^sub>c Y"
    show "y \<in>\<^bsub>Y\<^esub> (one, y1) \<Longrightarrow> y = y1"
      by (metis cfunc_type_def factors_through_def id_right_unit2 id_type one_unique_element relative_member_def2)
  next 
    show "y1 \<in>\<^sub>c Y \<Longrightarrow> y1 \<in>\<^bsub>Y\<^esub> (one, y1)"
      by (metis cfunc_type_def factors_through_def id_right_unit2 id_type relative_member_def2 y1_mono)
  qed


  have "injective(m)"
  proof(unfold injective_def ,auto)
    fix a b 
    assume "a \<in>\<^sub>c domain m" "b \<in>\<^sub>c domain m"
    then have a_type[type_rule]: "a \<in>\<^sub>c X  \<Coprod> Y" and b_type[type_rule]: "b \<in>\<^sub>c X  \<Coprod> Y"
      using m_type unfolding cfunc_type_def by auto
    assume eqs: "m \<circ>\<^sub>c a = m \<circ>\<^sub>c b"

      have m_leftproj_l_equals: "\<And> l. l  \<in>\<^sub>c X \<Longrightarrow> m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = \<langle>l, y1\<rangle>"
      proof-
        fix l 
        assume l_type: "l \<in>\<^sub>c X"
        have "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = (\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1)) \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l"
          by (simp add: m_def)
        also have "... = (\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c l"
          using comp_associative2 l_type by (typecheck_cfuncs, blast)
        also have "... = \<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c l"
          by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
        also have "... = \<langle>id(X)\<circ>\<^sub>c l , (y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c l\<rangle>"
          using l_type cfunc_prod_comp by (typecheck_cfuncs, auto)
        also have "... = \<langle>l , y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c l\<rangle>"
          using l_type comp_associative2 id_left_unit2 by (typecheck_cfuncs, auto)
        also have "... = \<langle>l , y1\<rangle>"
          using l_type by (typecheck_cfuncs,metis id_right_unit2 id_type one_unique_element)
        then show "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = \<langle>l,y1\<rangle>"
          by (simp add: calculation)
      qed

      have m_rightproj_y1_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y1 = \<langle>x2, y2\<rangle>"
          proof - 
            have "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y1 = (m \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y1"
              using  comp_associative2 m_type by (typecheck_cfuncs, auto)
            also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c y1"
              using m_def right_coproj_cfunc_coprod type1 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1 \<circ>\<^sub>c y1"
              using  comp_associative2 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c left_coproj one (Y \<setminus> (one,y1))"
              using  try_cast_m_m y1_mono y1y2_def(1) by auto
            also have "... =  \<langle>x2, y2\<rangle>"
              using left_coproj_cfunc_coprod type4 type5 by blast
            then show ?thesis using calculation by auto
          qed

     have m_rightproj_not_y1_equals: "\<And> r. r  \<in>\<^sub>c Y \<and> r \<noteq> y1 \<Longrightarrow>
          \<exists>k. k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c r = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          proof(auto)
           fix r 
           assume r_type: "r \<in>\<^sub>c Y"
           assume r_not_y1: "r \<noteq> y1"
           then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c r = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k"
            using r_type relative try_cast_not_in_X y1_mono y1y2_def(1) by blast
           have m_rightproj_l_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
           
           proof -
             have "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = (m \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c r"
              using r_type comp_associative2 m_type by (typecheck_cfuncs, auto)
            also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c r"
              using m_def right_coproj_cfunc_coprod type1 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  (try_cast y1 \<circ>\<^sub>c r)"
              using r_type comp_associative2 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c (right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k)"
              using k_def by auto
            also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c right_coproj one (Y \<setminus> (one,y1))) \<circ>\<^sub>c k"
              using comp_associative2 k_def by (typecheck_cfuncs, blast)
            also have "... =  \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle> \<circ>\<^sub>c k"
              using right_coproj_cfunc_coprod type4 type5 by auto
            also have "... =  \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub> \<circ>\<^sub>c k, y1\<^sup>c \<circ>\<^sub>c k \<rangle>"
              using cfunc_prod_comp comp_associative2 k_def by (typecheck_cfuncs, auto)
            also have "... =  \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              by (metis id_right_unit2 id_type k_def one_unique_element terminal_func_comp terminal_func_type x1x2_def(1))
            then show ?thesis using calculation by auto
          qed
          then show "\<exists>k. k \<in>\<^sub>c Y \<setminus> (one, y1) \<and>
             try_cast y1 \<circ>\<^sub>c r = right_coproj one (Y \<setminus> (one, y1)) \<circ>\<^sub>c k \<and>
             m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using k_def by blast
        qed

  
    show "a = b"
    proof(cases "\<exists>x. a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X")
      assume "\<exists>x. a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X"
      then obtain x where x_def: "a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X"
        by auto
      then have m_proj_a: "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c x = \<langle>x, y1\<rangle>"
        using m_leftproj_l_equals by (simp add: x_def)
      show "a = b"
      proof(cases "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X")
        assume "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
        then obtain c where c_def: "b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X"
          by auto
        then have "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c, y1\<rangle>"
          by (simp add: m_leftproj_l_equals)
        then show ?thesis
          using c_def element_pair_eq eqs m_proj_a x_def y1y2_def(1) by auto
      next
        assume "\<nexists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
        then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y"
          using b_type coprojs_jointly_surj by blast
        show "a = b"
        proof(cases "c = y1")
          assume "c = y1"       
          have m_rightproj_l_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x2, y2\<rangle>"
            by (simp add: \<open>c = y1\<close> m_rightproj_y1_equals)       
          then show ?thesis
            using \<open>c = y1\<close> c_def cart_prod_eq2 eqs m_proj_a x1x2_def(2) x_def y1y2_def(2) y1y2_def(3) by auto
        next
          assume "c \<noteq> y1"       
          then obtain k where k_def:  "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using c_def m_rightproj_not_y1_equals by blast                     
          then have "\<langle>x, y1\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using c_def eqs m_proj_a x_def by auto
          then have "(x = x1) \<and> (y1 = y1\<^sup>c \<circ>\<^sub>c k)"
            by (smt \<open>c \<noteq> y1\<close> c_def cfunc_type_def comp_associative comp_type element_pair_eq k_def m_rightproj_not_y1_equals monomorphism_def3 try_cast_m_m' try_cast_mono trycast_y1_type x1x2_def(1) x_def y1'_type y1_mono y1y2_def(1))
          then have False
            by (smt \<open>c \<noteq> y1\<close>  c_def comp_type complement_disjoint element_pair_eq id_right_unit2 id_type k_def m_rightproj_not_y1_equals x_def y1'_type y1_mono y1y2_def(1))
          then show ?thesis by auto
        qed
      qed
    next 
      assume "\<nexists>x. a = left_coproj X Y \<circ>\<^sub>c x \<and> x \<in>\<^sub>c X"
      then obtain y where y_def: "a = right_coproj X Y \<circ>\<^sub>c y \<and> y \<in>\<^sub>c Y"
        using a_type coprojs_jointly_surj by blast

      show "a = b"
      proof(cases "y = y1")
        assume "y = y1"
        then  have m_rightproj_y_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x2, y2\<rangle>"
          using m_rightproj_y1_equals by blast
        then have "m \<circ>\<^sub>c a  = \<langle>x2, y2\<rangle>"
          using y_def by blast
        show "a = b"
        proof(cases "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X")
          assume "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
          then obtain c where c_def: "b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
            by blast
          then show "a = b"
            using cart_prod_eq2 eqs m_leftproj_l_equals m_rightproj_y_equals x1x2_def(2) y1y2_def y_def by auto
        next
          assume "\<nexists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
          then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            using b_type coprojs_jointly_surj by blast
          show "a = b"
          proof(cases "c = y")
            assume "c = y"
            show "a = b"
              by (simp add: \<open>c = y\<close> c_def y_def)
          next
            assume "c \<noteq> y"
            then have "c \<noteq> y1"
              by (simp add: \<open>y = y1\<close>)
            then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c c = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              using c_def m_rightproj_not_y1_equals by blast
            then have "\<langle>x2, y2\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              using \<open>m \<circ>\<^sub>c a = \<langle>x2,y2\<rangle>\<close> c_def eqs by auto
            then have False
              using comp_type element_pair_eq k_def x1x2_def y1'_type y1y2_def(2) by auto
            then show ?thesis
              by simp
          qed
        qed
      next
        assume "y \<noteq> y1"
        then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          using m_rightproj_not_y1_equals y_def by blast  
        then have "m \<circ>\<^sub>c a  = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          using y_def by blast
        show "a = b"
        proof(cases "\<exists>c. b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y")
          assume "\<exists>c. b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y"
          then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            by blast  
          show "a = b"
          proof(cases "c = y1")
            assume "c = y1" 
            show "a = b"
              proof -
                obtain cc :: cfunc where
                  f1: "cc \<in>\<^sub>c Y \<setminus> (one, y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj one (Y \<setminus> (one, y1)) \<circ>\<^sub>c cc \<and> m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c cc\<rangle>"
                  using \<open>\<And>thesis. (\<And>k. k \<in>\<^sub>c Y \<setminus> (one, y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj one (Y \<setminus> (one, y1)) \<circ>\<^sub>c k \<and> m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
                have "\<langle>x2,y2\<rangle> = m \<circ>\<^sub>c a"
              using \<open>c = y1\<close> c_def eqs m_rightproj_y1_equals by presburger
              then show ?thesis
              using f1 cart_prod_eq2 comp_type x1x2_def y1'_type y1y2_def(2) y_def by force
              qed
          next
              assume "c \<noteq> y1"              
              then obtain k' where k'_def: "k' \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c c = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k' \<and> 
              m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k'\<rangle>"
                using c_def m_rightproj_not_y1_equals by blast
              then have "\<langle>x1, y1\<^sup>c \<circ>\<^sub>c k'\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
                using c_def eqs k_def y_def by auto
              then have "(x1 = x1) \<and> (y1\<^sup>c \<circ>\<^sub>c k' = y1\<^sup>c \<circ>\<^sub>c k)"
                using  element_pair_eq k'_def k_def by (typecheck_cfuncs, blast)
              then have "k' = k"
                by (metis cfunc_type_def complement_morphism_mono k'_def k_def monomorphism_def y1'_type y1_mono)
              then have "c = y"
                by (metis c_def cfunc_type_def k'_def k_def monomorphism_def try_cast_mono trycast_y1_type y1_mono y_def)
              then show "a = b"
                by (simp add: c_def y_def)
          qed
        next
            assume "\<nexists>c. b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            then obtain c where c_def:  "b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
              using b_type coprojs_jointly_surj by blast
            then have  "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c, y1\<rangle>"
              by (simp add: m_leftproj_l_equals)      
            then have "\<langle>c, y1\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
                using \<open>m \<circ>\<^sub>c a = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle>\<close> \<open>m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c,y1\<rangle>\<close> c_def eqs by auto      
            then have "(c = x1) \<and> (y1 = y1\<^sup>c \<circ>\<^sub>c k)"
              using c_def cart_prod_eq2 comp_type k_def x1x2_def(1) y1'_type y1y2_def(1) by auto 
            then have False
              by (metis cfunc_type_def complement_disjoint id_right_unit id_type k_def y1_mono y1y2_def(1))
            then show ?thesis
              by simp
        qed
      qed
    qed
  qed
  then have "monomorphism m"
    using injective_imp_monomorphism by auto 
  then show ?thesis
    using is_smaller_than_def m_type by blast
qed





lemma prod_finite_with_self_finite:
  assumes "is_finite(Y)"
  shows "is_finite(Y \<times>\<^sub>c Y)"
proof(cases "initial_object(Y)")
  assume "initial_object Y"
  then have "Y \<times>\<^sub>c Y \<cong> Y"
    using function_to_empty_set_is_iso initial_iso_empty is_isomorphic_def left_cart_proj_type no_el_iff_iso_0 by blast
  then show ?thesis
    using assms iso_pres_finite isomorphic_is_symmetric by blast
next
  assume "\<not> initial_object Y"
  show ?thesis
  proof(cases "terminal_object Y")
    assume "terminal_object Y"
    then have "Y \<times>\<^sub>c Y \<cong> Y"
      by (simp add: prod_with_term_obj1)
    then show ?thesis
      using assms iso_pres_finite isomorphic_is_symmetric by blast
  next
    assume "\<not> terminal_object Y"
    oops








lemma product_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  assumes "nonempty(X)" "nonempty(Y)"
  shows "is_finite(X \<times>\<^sub>c Y)"
proof(cases "initial_object(X)")
  assume "initial_object X"
  then have "X \<times>\<^sub>c Y \<cong> \<emptyset>"
    using assms(3) initial_iso_empty no_el_iff_iso_0 by blast
  then show ?thesis
    using \<open>initial_object X\<close> assms(3) initial_iso_empty no_el_iff_iso_0 by blast
next
  assume "\<not> initial_object X"
  show ?thesis
  proof(cases "terminal_object(X)")
    assume "terminal_object(X)" 
    then have "X \<times>\<^sub>c Y \<cong> Y"
      by (simp add: prod_with_term_obj1) 
    then show ?thesis
      using assms(2) iso_pres_finite isomorphic_is_symmetric by blast
  next
    assume "\<not> terminal_object X"
    show ?thesis
    proof(cases "terminal_object(Y)")
      assume "terminal_object Y"
      then have "X \<times>\<^sub>c Y \<cong> X"
        by (simp add: prod_with_term_obj2)
      then show ?thesis
        using assms(1) iso_pres_finite isomorphic_is_symmetric by blast
    next
      assume "\<not> terminal_object Y"
      then show "is_finite (X \<times>\<^sub>c Y)"
        oops

(*
  fix xy
  assume xy_type: "xy:  X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c Y"
  assume xy_mono: "monomorphism(xy)"
  obtain m where m_def: "m :  X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism(m)"
    using assms(4) is_smaller_than_def smaller_than_product1 by blast
  obtain n where n_def: "n :  Y \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism(n)"
    using assms(3) is_smaller_than_def smaller_than_product2 by blast
  oops
*)




lemma coprod_finite_with_self_finite:
  assumes "is_finite(Y)"
  assumes "is_finite(Y \<times>\<^sub>c Y)"
  shows "is_finite(Y \<Coprod> Y)"
proof(cases "initial_object Y")
  assume "initial_object Y"
  then show ?thesis
    using  assms coprod_with_init_obj2 either_finite_or_infinite iso_pres_infinite not_finite_and_infinite by blast
next
  assume "\<not> initial_object Y"
  show ?thesis
  proof(cases "terminal_object Y")
    assume "terminal_object Y"
    then have "Y \<Coprod> Y \<cong> \<Omega>"
      by (meson coprod_pres_iso isomorphic_is_transitive oneUone_iso_\<Omega> one_terminal_object terminal_objects_isomorphic)
    then show ?thesis
      using either_finite_or_infinite iso_pres_infinite not_finite_and_infinite truth_set_is_finite by blast
  next
    assume "\<not> terminal_object Y"
    then have "(Y \<Coprod> Y) \<le>\<^sub>c (Y \<times>\<^sub>c Y)"
      by (simp add: \<open>\<not> initial_object Y\<close> coprod_leq_product)
    then show ?thesis
      using assms(2) smaller_than_finite_is_finite by blast
  qed
qed
 


lemma coproduct_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  assumes "is_finite(X \<times>\<^sub>c Y)"
  shows "is_finite(X \<Coprod> Y)"
proof(cases "initial_object(X)")
  assume "initial_object X"
  then have "X \<Coprod> Y \<cong> Y"
    by (simp add: coprod_with_init_obj2)
  then show ?thesis
    using  assms(2) iso_pres_finite isomorphic_is_symmetric by blast
next
  assume "\<not>(initial_object X)"
  show ?thesis
  proof(cases "initial_object(Y)")
    assume "initial_object Y"
    then have "X \<Coprod> Y \<cong> X"
      using coprod_with_init_obj1 by blast
    then show ?thesis
      using assms(1) iso_pres_finite isomorphic_is_symmetric by blast
  next 
    assume "\<not>(initial_object Y)"  
    show ?thesis
    proof(cases "terminal_object(X)")
      assume "terminal_object X"
      then obtain y where y_def:  "y : X \<rightarrow> Y \<and> monomorphism(y)"
        by (meson \<open>\<not> initial_object Y\<close> comp_type iso_empty_initial no_el_iff_iso_0 nonempty_def terminal_el__monomorphism terminal_func_type)
      then have y_id_type: "(y \<bowtie>\<^sub>f  id(Y)) : X \<Coprod> Y \<rightarrow> Y \<Coprod> Y"
        by (simp add: cfunc_bowtie_prod_type id_type)
      then have "monomorphism(y \<bowtie>\<^sub>f  id(Y))"
        by (typecheck_cfuncs, metis cfunc_bowtieprod_inj id_isomorphism injective_imp_monomorphism iso_imp_epi_and_monic mem_Collect_eq monomorphism_imp_injective y_def)
      have "is_finite(Y \<Coprod> Y)"
        by (simp add: assms(4))
      have "(X \<Coprod> Y) \<le>\<^sub>c (Y \<Coprod> Y)"
        using \<open>monomorphism (y \<bowtie>\<^sub>f id\<^sub>c Y)\<close> is_smaller_than_def y_id_type by auto
      then show ?thesis
        using assms(4) smaller_than_finite_is_finite by blast
    next
      assume "\<not>(terminal_object X)"
      show ?thesis 
      proof(cases "terminal_object(Y)")
        assume "terminal_object(Y)"
        then obtain x where x_def:  "x : Y \<rightarrow> X \<and> monomorphism(x)"
          by (meson \<open>\<not> initial_object X\<close> comp_type is_isomorphic_def iso_empty_initial no_el_iff_iso_0 nonempty_def one_terminal_object terminal_el__monomorphism terminal_objects_isomorphic)
      then have y_id_type: "(id(X) \<bowtie>\<^sub>f  x) : X \<Coprod> Y \<rightarrow> X \<Coprod> X"
        by (simp add: cfunc_bowtie_prod_type id_type)
      then have "monomorphism(id(X) \<bowtie>\<^sub>f  x)"
        by (typecheck_cfuncs, metis cfunc_bowtieprod_inj id_isomorphism injective_imp_monomorphism iso_imp_epi_and_monic mem_Collect_eq monomorphism_imp_injective x_def)
      have "is_finite(X \<Coprod> X)"
        by (simp add: assms(3))
      have "(X \<Coprod> Y) \<le>\<^sub>c (X \<Coprod> X)"
        using \<open>monomorphism (id\<^sub>c X \<bowtie>\<^sub>f x)\<close> is_smaller_than_def y_id_type by auto
      then show ?thesis
        using assms(3) smaller_than_finite_is_finite by blast
    next 
      assume "\<not> terminal_object Y"
      then have "(X \<Coprod> Y) \<le>\<^sub>c (X \<times>\<^sub>c Y)"
        by (simp add: \<open>\<not> initial_object X\<close> \<open>\<not> initial_object Y\<close> \<open>\<not> terminal_object X\<close> coprod_leq_product)
      then show "is_finite(X \<Coprod> Y)"
        using assms(5) smaller_than_finite_is_finite by blast
      qed
    qed
  qed
qed



(*Proposition 2.6.10*)
lemma NxN_is_countable:
  "countable(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
proof -
  obtain f where f_def:
    "f = ((\<langle>id \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c right_cart_proj one \<nat>\<^sub>c) \<amalg> id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))
          \<circ>\<^sub>c dist_prod_coprod_inv2 one \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (predecessor \<times>\<^sub>f successor)"
    by auto

  have f_type[type_rule]: "f : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding f_def by typecheck_cfuncs

  obtain seq where seq_type[type_rule]: "seq : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and
    seq_triangle: "seq \<circ>\<^sub>c zero = \<langle>zero, zero\<rangle>" and
    seq_square: "seq \<circ>\<^sub>c successor = f \<circ>\<^sub>c seq"
    using natural_number_object_property[where q = "\<langle>zero, zero\<rangle>", where f=f, where X="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"]
    unfolding triangle_commutes_def square_commutes_def by (auto, typecheck_cfuncs, metis)

  (* seq((n+m)(n+m+1)/2 + n) = (m, n)? *)
  (* seq(0) = (0,0) = seq(0*1/2 + 0) *)
  (* seq(1) = (1,0) = seq(1*2/2 + 0) *)
  (* seq(2) = (0,1) = seq(1*2/2 + 1) *)
  (* seq(3) = (2,0) = seq(2*3/2 + 0) *)
  (* seq(4) = (1,1) = seq(2*3/2 + 1) *)
  (* seq(5) = (0,2) = seq(2*3/2 + 2) *)
  (* seq(6) = (3,0) = seq(3*4/2 + 0) *)

  have "\<And> m n k. m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
    seq \<circ>\<^sub>c k = \<langle>m, n\<rangle> \<longleftrightarrow> seq \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>k, m\<rangle> = \<langle>zero, add2 \<circ>\<^sub>c \<langle>m, n\<rangle>\<rangle>"
    

    have "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> seq \<circ>\<^sub>c halve \<circ>\<^sub>c (n \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n)) = \<langle>n, zero\<rangle>"
  proof -
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"

    have "seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, successor\<rangle> = \<langle>id \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where f="successor \<times>\<^sub>f id \<nat>\<^sub>c"])
      show "seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
        by typecheck_cfuncs
      show "\<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
        by typecheck_cfuncs
      show "successor \<times>\<^sub>f id \<nat>\<^sub>c : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
        by typecheck_cfuncs

      show "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c zero = \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero"
      proof -
        have "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c zero = seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>zero, successor \<circ>\<^sub>c zero\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
        also have "... = seq \<circ>\<^sub>c halve \<circ>\<^sub>c zero"
          using mult_def s0_is_right_id zero_type by auto
        also have "... = seq \<circ>\<^sub>c zero"
          by (smt comp_associative2 halve_nth_even halve_type id_left_unit2 nth_even_def2 zero_type)
        also have "... = \<langle>zero, zero\<rangle>"
          by (simp add: seq_triangle)
        also have "... = \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero"
          by (typecheck_cfuncs, simp add: cart_prod_extract_left)
        then show ?thesis
          using calculation by auto
      qed

      show "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c successor
        = (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>"
      proof -
        have "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c successor = seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>successor, successor \<circ>\<^sub>c successor\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
        also have "... = undefined"

(*  have "\<And> m. seq \<circ>\<^sub>c (k +\<^sub>\<nat> m) = \<langle>zero, m\<rangle>"

  have "\<And> k m. k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> seq \<circ>\<^sub>c k = \<langle>m, zero\<rangle> \<Longrightarrow> seq \<circ>\<^sub>c (k +\<^sub>\<nat> m) = \<langle>zero, m\<rangle>"
  proof -
    fix k m
    assume k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
    assume seq_k_eq: "seq \<circ>\<^sub>c k = \<langle>m, zero\<rangle>"

    have "eq_pred (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>seq \<circ>\<^sub>c k \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, \<langle>id \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> =
      eq_pred (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>seq\<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>k \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>"
    proof (rule natural_number_object_func_unique[where X="\<Omega>", where f="id \<Omega>"])
*)
  oops





(*Once we have this  result above we can generalize it to any countable sets*)
lemma product_of_countables_is_countable:
  assumes "countable X" "countable Y"
  assumes NxN_is_countable: "countable(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)" (*DELETE later*)
  shows "countable(X \<times>\<^sub>c Y)"
proof - 
  have "\<exists>f. f: X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(f)"
    using assms(1) countable_def by blast
  then obtain f where f_def: "f: X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(f)"
    by blast
  have "\<exists>g. g: Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(g)"
    using assms(2) countable_def by blast
  then obtain g where g_def: "g: Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(g)"
    by blast
  then have fg_type: "(f \<times>\<^sub>f g) : (X \<times>\<^sub>c Y) \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_cross_prod_type f_def)
  have fg_mono: "monomorphism(f \<times>\<^sub>f g)"
    using cfunc_cross_prod_mono f_def g_def by blast
  obtain \<phi> where \<phi>_def: "(\<phi> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c) \<and> monomorphism(\<phi>)"
    using NxN_is_countable countable_def by blast
  have "(\<phi> \<circ>\<^sub>c (f \<times>\<^sub>f g) : (X \<times>\<^sub>c Y) \<rightarrow> \<nat>\<^sub>c) \<and> monomorphism(\<phi> \<circ>\<^sub>c (f \<times>\<^sub>f g))"
    using \<phi>_def cfunc_type_def comp_type composition_of_monic_pair_is_monic fg_mono fg_type by auto
  then show "countable(X \<times>\<^sub>c Y)"
    using countable_def by blast
qed

      


lemma NuN_is_countable:
  "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  using countable_def epis_give_monos halve_with_parity_iso halve_with_parity_type iso_imp_epi_and_monic by smt


(*Exercise 2.6.11*)
lemma coproduct_of_countables_is_countable:
  assumes "countable X" "countable Y"
  shows "countable(X \<Coprod> Y)"
  unfolding countable_def
proof-
  obtain x where x_def:  "x : X  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism x"
    using assms(1) countable_def by blast
  obtain y where y_def:  "y : Y  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism y"
    using assms(2) countable_def by blast
  obtain n where n_def: " n : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> monomorphism n"
    using NuN_is_countable countable_def by blast
  have xy_type: "x \<bowtie>\<^sub>f y : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    using x_def y_def by (typecheck_cfuncs, auto)
  then have nxy_type: "n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y) : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c"
    using comp_type n_def by blast
  have "injective(x \<bowtie>\<^sub>f y)"
    using cfunc_bowtieprod_inj monomorphism_imp_injective x_def y_def by blast
  then have "monomorphism(x \<bowtie>\<^sub>f y)"
    using injective_imp_monomorphism by auto
  then have "monomorphism(n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y))"
    using cfunc_type_def composition_of_monic_pair_is_monic n_def xy_type by auto
  then show "\<exists>f. f : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f"
    using nxy_type by blast
qed
   
  

lemma finite_is_countable: 
  assumes "is_finite X"
  shows "countable X"
  oops

lemma 
  assumes "is_infinite X"
  shows "\<nat>\<^sub>c \<le>\<^sub>c X"
  oops 


lemma N_is_smallest_infinite:
  assumes "is_infinite X"
  assumes "X \<le>\<^sub>c \<nat>\<^sub>c"
  shows "\<nat>\<^sub>c \<cong> X"
  oops

(*We could add a part 2 to the above that says if they are not isomorphic
 then an infinite set is necessarily bigger than N.*)

lemma
  assumes i_zero: "i 0 = x" and i_suc: "\<And> n. i (Suc n) = (m \<circ> i) n" 
  assumes m_mono: "\<And> p q. m p = m q \<Longrightarrow> p = q"
  assumes x_def: "\<And> y. m y \<noteq> x"
  shows "\<And>q. i p = i q \<Longrightarrow> p = q"
proof (induct p)
  fix q
  show "i 0 = i q \<Longrightarrow> 0 = q"
  proof (induct q)
    show "0 = 0"
      by simp
  next
    fix q
    assume "i 0 = i (Suc q)"
    then have "x = (m \<circ> i) q"
      using i_suc i_zero by auto
    then have False
      using x_def by auto
    then show "0 = Suc q"
      by simp
  qed
next
  fix p q
  assume ind_hyp: "\<And>q. i p = i q \<Longrightarrow> p = q"

  show "i (Suc p) = i q \<Longrightarrow> Suc p = q"
  proof (induct q)
    assume "i (Suc p) = i 0"
    then have "x = (m \<circ> i) p"
      using i_suc i_zero by auto
    then have False
      using x_def by auto
    then show "Suc p = 0"
      by simp
  next
    fix q
    assume "i (Suc p) = i (Suc q)"
    then have "(m \<circ> i) p = (m \<circ> i) q"
      by (simp add: i_suc)
    then have "i p = i q"
      by (metis comp_apply m_mono)
    then have "p = q"
      by (meson ind_hyp)
    then show "Suc p = Suc q"
      by simp
  qed
qed

lemma finite_iff_nosurj_to_N:
  shows "(is_finite(X)) = (\<not>(\<exists>s. (s : X \<rightarrow> \<nat>\<^sub>c) \<and> surjective(s)))"
proof(safe)
  fix s 
  assume X_fin: "is_finite X"
  assume s_type: "s : X \<rightarrow> \<nat>\<^sub>c"
  assume s_surj: "surjective s"
  have "\<exists>g. (g: \<nat>\<^sub>c \<rightarrow> X \<and> monomorphism(g) )"
    using epis_give_monos s_surj s_type surjective_is_epimorphism by blast
  then have "is_finite \<nat>\<^sub>c"
    using X_fin is_smaller_than_def smaller_than_finite_is_finite by blast
  then show False
    using natural_numbers_are_countably_infinite not_finite_and_infinite by blast
next 
  assume "\<nexists>s. s : X \<rightarrow> \<nat>\<^sub>c \<and> surjective s"
  show "is_finite X"
  proof(rule ccontr)
    assume "\<not> is_finite X"
    then have "is_infinite X"
      using either_finite_or_infinite by blast
    then obtain m where m_type[type_rule]: "m : X \<rightarrow> X" and  m_mono: "monomorphism(m)" and 
     m_not_surj:  "\<not>surjective(m)"
      using is_infinite_def by blast
    obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and 
      x_def: "\<And> y.  y \<in>\<^sub>c X \<Longrightarrow>  m \<circ>\<^sub>c y \<noteq> x"
      using m_not_surj m_type surjective_def2 by auto

    obtain i where 
      i_type[type_rule]: "i : \<nat>\<^sub>c \<rightarrow> X" and ibase: "i \<circ>\<^sub>c zero = x" and i_induct: "m \<circ>\<^sub>c i = i \<circ>\<^sub>c successor"
      using m_type natural_number_object_property2 x_type by blast
    have "injective(i)"
      unfolding injective_def
    proof(auto)
      fix p q
      assume "p \<in>\<^sub>c domain i"
      then have [type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
        using cfunc_type_def i_type by auto
      assume "q \<in>\<^sub>c domain i"
      then have [type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
        using cfunc_type_def i_type by auto
      assume eqs: "i \<circ>\<^sub>c p = i \<circ>\<^sub>c q"  

      (* i(n) = i(m) \<Longrightarrow>  n = m   *)
    have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle> eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    proof (rule natural_number_object_func_unique[where X="\<Omega>", where f="id \<Omega>"])

      show "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show  "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      proof - 
        have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
        proof (rule same_evals_equal[where Z=one, where X=\<Omega>, where A="\<nat>\<^sub>c"])
          show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs
          show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
            by typecheck_cfuncs 
          show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
          proof - 
            have "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = 
                  eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
              by (typecheck_cfuncs, metis identity_distributes_across_composition)
            also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
              by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative transpose_func_def)
            also have "... = eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
            proof(rule one_separator[where X = "\<nat>\<^sub>c \<times>\<^sub>c one", where Y=\<Omega>])
              show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
                by typecheck_cfuncs
              show " eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
                by typecheck_cfuncs
              show "\<And>pone. pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
         (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone =
         (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone"
              proof - 
                fix pone
                assume pone_type: "pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
                then obtain p where p_def: "pone = \<langle>p, id one\<rangle>" and p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
                  by (metis cart_prod_decomp id_type one_unique_element)

                have RHS: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone = \<t>"
                proof - 
                  have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone = 
                         eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                    by (typecheck_cfuncs, simp add: comp_associative2 p_def)
                  also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                    by (typecheck_cfuncs, metis calculation flat_cancels_sharp inv_transpose_func_def2 p_def) 
                  also have "... = \<t>"
                    by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 terminal_func_comp terminal_func_unique)
                  then show ?thesis
                    by (simp add: calculation)
                qed
                
                have LHS: "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone = \<t>"
                proof - 
                  have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone = 
                         IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                    using comp_associative2 p_def by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p, zero\<rangle>"
                    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p, zero\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, zero\<rangle> \<rangle>"
                    using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c zero\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle> \<rangle>"
                    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
                  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, zero\<rangle> \<rangle>"
                    by (typecheck_cfuncs, simp add: ibase id_left_unit2)
                  also have "... = \<t>"
                  proof(cases "p = zero")
                    assume "p = zero"
                    then show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle> = \<t>"
                      by (typecheck_cfuncs, metis IMPLIES_true_true_is_true  eq_pred_iff_eq ibase)
                  next
                    assume "p \<noteq> zero"
                    then obtain j where j_def: "p = successor \<circ>\<^sub>c j" and j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
                      using \<open>p \<noteq> zero\<close> nonzero_is_succ by (typecheck_cfuncs, blast)
                    have "i \<circ>\<^sub>c p = m \<circ>\<^sub>c i \<circ>\<^sub>c j"
                      using comp_associative2 i_induct j_def successor_type by (typecheck_cfuncs, force)
                    then have "i \<circ>\<^sub>c p \<noteq> x"
                      using \<open>i \<circ>\<^sub>c p = m \<circ>\<^sub>c i \<circ>\<^sub>c j\<close> comp_type j_type x_def by (typecheck_cfuncs, presburger)
                    then have "eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, x\<rangle> = \<f>"
                      using \<open>i \<circ>\<^sub>c p \<noteq> x\<close> eq_pred_iff_eq_conv by (typecheck_cfuncs, blast)
                    then show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle> = \<t>"
                      by (typecheck_cfuncs, metis IMPLIES_false_false_is_true \<open>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle> = \<f>\<close> \<open>p \<noteq> zero\<close> eq_pred_iff_eq_conv)
                  qed
                  then show ?thesis
                    by (simp add: calculation)
                qed
                show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone =
                                  (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone "
                  by (simp add: LHS RHS)
              qed
            qed
            then show ?thesis
              using calculation by presburger
          qed
        qed
        then show ?thesis  
              by (typecheck_cfuncs, metis FORALL_is_pullback \<open>(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>\<close> cfunc_type_def comp_associative is_pullback_def square_commutes_def terminal_func_comp)
      qed
      




      show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)

      show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor
        = id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
       
      proof -
        have case1: "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>
          \<Longrightarrow> id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        proof - 
          assume "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> ((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p"
            by presburger
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> ((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = \<t>"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative is_even_def2 is_even_nth_even_true nth_even_type nth_even_zero terminal_func_comp terminal_func_type zero_type)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (successor \<circ>\<^sub>c p) = \<t>"
            using  comp_associative2 by (typecheck_cfuncs, force)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (successor \<circ>\<^sub>c p) = \<t>"
            by (typecheck_cfuncs, smt (z3) cfunc_type_def codomain_comp comp_associative)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c p)))\<^sup>\<sharp> = \<t>"
            by (typecheck_cfuncs, metis sharp_comp succ_n_type)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
            by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp succ_n_type)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
          proof -
            fix p
            assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
            have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one
                = (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one"
              by (typecheck_cfuncs, simp add: comp_associative2)
            then show "(\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>)
              \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
              using p_type by force
          qed
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>)"
          proof (rule_tac FORALL_true_implies_all_true[where X="\<nat>\<^sub>c"], auto)
            fix p
            assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
            show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,(successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by (typecheck_cfuncs)
          qed
          then have f1: "\<And> p q. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
            by auto
          have ind_hyp: "\<And> p q. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)) \<Longrightarrow> (q = (successor \<circ>\<^sub>c p))"    
          proof - 
            fix p q
            assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
            assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
            have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
              using f1 by (typecheck_cfuncs, blast)
            then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c q = \<t>"
              using  comp_associative2 by (typecheck_cfuncs, force)
            then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>  = \<t>"
              by (typecheck_cfuncs, metis cart_prod_extract_left)
            then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>  = \<t>"
              using  comp_associative2 by (typecheck_cfuncs, force)
            then have "IMPLIES \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>, (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle> \<rangle>   = \<t>"
              by (typecheck_cfuncs, metis cfunc_prod_comp)
            then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>\<rangle>   = \<t>"
              by (typecheck_cfuncs, smt (verit, ccfv_threshold)  cfunc_type_def comp_associative domain_comp)
            then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>\<rangle> = \<t>"
              using cfunc_cross_prod_comp_cfunc_prod id_cross_prod id_left_unit2 by (typecheck_cfuncs, force)
            then have "(eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)\<rangle> = \<t>) \<Longrightarrow> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle> = \<t>)  "
              by (typecheck_cfuncs, metis IMPLIES_true_false_is_false \<open>IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q,i \<circ>\<^sub>c successor \<circ>\<^sub>c p\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q,successor \<circ>\<^sub>c p\<rangle>\<rangle> = \<t>\<close> true_false_only_truth_values)
            then show "(i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)) \<Longrightarrow> (q = (successor \<circ>\<^sub>c p))"
              using  eq_pred_iff_eq by (typecheck_cfuncs, auto)
          qed
          show "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          proof (rule one_separator[where X="\<nat>\<^sub>c", where Y=\<Omega>])
            show "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
          next
            fix p
            assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
            show "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p"
              by (typecheck_cfuncs, metis \<open>(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle> eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<close> 
                         \<open>(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero\<close> 
                         \<open>\<And>p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> ((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = \<t>\<close>
                        \<open>\<And>p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor \<circ>\<^sub>c p = \<t>\<close>
                        id_left_unit2 nonzero_is_succ)
          qed
        qed
      
(*This concludes Case 1*)











        have case2: "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>
            \<Longrightarrow> (FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        proof -
          assume "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
            by (typecheck_cfuncs_prems, insert id_left_unit2, presburger)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p"
            by presburger
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c p = \<t>"
            by (typecheck_cfuncs, smt comp_associative2 id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f p))\<^sup>\<sharp> = \<t>"
            by (typecheck_cfuncs, metis sharp_comp)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
            by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp)
          then have "\<And> p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>)"
          proof -
            fix p
            assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
            assume "\<And>p. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
              FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
              using p_type by auto
            then show "\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
              by (rule_tac FORALL_true_implies_all_true[where X="\<nat>\<^sub>c"], auto, 
                  typecheck_cfuncs, typecheck_cfuncs, smt comp_associative2)
          qed
          then have f1: "\<And> p q. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
            by auto
          have ind_hyp: "\<And> p q. p \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c p) \<Longrightarrow> (q = p)"
          proof - 
            fix p q
            assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
            assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
            have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
              by (simp add: f1  p_type q_type)
            then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c q = \<t>"
              using  comp_associative2 by (typecheck_cfuncs, force)
            then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>q, p\<rangle>  = \<t>"
              by (typecheck_cfuncs, metis cart_prod_extract_left)
            then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>q, p\<rangle>  = \<t>"
              using  comp_associative2 by (typecheck_cfuncs, force)
            then have "IMPLIES \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>q, p\<rangle>, (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>q, p\<rangle>\<rangle>   = \<t>"
              by (typecheck_cfuncs, metis cfunc_prod_comp)
            then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>q, p\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>q, p\<rangle> \<rangle>   = \<t>"
              by (typecheck_cfuncs, smt (verit, ccfv_threshold) cfunc_type_def comp_associative domain_comp)
            then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c p\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>q, p\<rangle>\<rangle>   = \<t>"
              using cfunc_cross_prod_comp_cfunc_prod id_cross_prod id_left_unit2 by (typecheck_cfuncs, force)            
            then have "(eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c p\<rangle> = \<t>) \<Longrightarrow> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q, p\<rangle> = \<t>)"
              by (typecheck_cfuncs, metis IMPLIES_true_false_is_false  eq_pred_iff_eq eq_pred_iff_eq_conv)
            then show "(i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c p) \<Longrightarrow>  (q = p)"
              using eq_pred_iff_eq by (typecheck_cfuncs, auto)
          qed
          show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          proof (rule one_separator[where X="\<nat>\<^sub>c", where Y=\<Omega>])
            show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
          next
            fix p
            assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
            show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> ((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
              using \<open>(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<close>
                    \<open>FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<close>
                    \<open>id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<close>
              by presburger
          qed
        qed


(*This concludes Case 2*)          


        have case3: "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>
          \<Longrightarrow> (FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        proof - 
          assume f0: "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          proof (rule one_separator [where X = "\<nat>\<^sub>c", where Y = \<Omega>])
            show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
            proof - 
              fix x
              assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c"
              have f1: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x = \<f>"
                by (typecheck_cfuncs, smt (z3) \<open>x \<in>\<^sub>c \<nat>\<^sub>c\<close> beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 successor_type terminal_func_comp)
              have "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = \<f>"
              proof(rule ccontr)
                assume "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x \<noteq> \<f>"
                then have f2: "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = \<t>"
                  using  true_false_only_truth_values x_type by (typecheck_cfuncs, blast)
                then have LHS_case1: "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
                  by (typecheck_cfuncs, metis cfunc_type_def comp_associative f0 f1 f2 false_func_type id_left_unit2 terminal_func_comp)
                then have RHS_case1: "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
                  using case1 LHS_case1 by blast
                then have "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
                  using f0 by presburger
                then show False
                  using f1 f2 LHS_case1 true_false_distinct by auto
              qed
              then show "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
                by (simp add: f1)
            qed
          qed
        qed
(*This concludes Case3*)


        have case4: "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>
          \<Longrightarrow> id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        proof - 
         assume f0: "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
         then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
           using comp_associative2 f0 by (typecheck_cfuncs, force)
         then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
           by (typecheck_cfuncs,  metis  sharp_comp)
         then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
           using  comp_associative2 by (typecheck_cfuncs, force)
         then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i))\<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor), (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor)\<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
           by (typecheck_cfuncs, metis cfunc_prod_comp)
         then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)\<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor) \<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
           by (typecheck_cfuncs, smt (z3)  cfunc_type_def comp_associative domain_comp)
         then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c ((i \<circ>\<^sub>c id \<nat>\<^sub>c) \<times>\<^sub>f (i \<circ>\<^sub>c successor)), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor))\<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
           using  cfunc_cross_prod_comp_cfunc_cross_prod by (typecheck_cfuncs, force)
         then have f0b: "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i  \<times>\<^sub>f (m \<circ>\<^sub>c i)), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f  successor)\<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
           by (typecheck_cfuncs, metis  i_induct id_left_unit2 id_right_unit2)


          show "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          proof (rule one_separator [where X = "\<nat>\<^sub>c", where Y = \<Omega>])
            show "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
            proof - 
              fix x
              assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c"
              then have "x = zero \<or> (\<exists>y. y \<in>\<^sub>c \<nat>\<^sub>c \<and> x = successor \<circ>\<^sub>c y)"
                using nonzero_is_succ by blast
              then show "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
              proof auto
                show "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
                  sorry
              next
                fix y
                assume y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c"
                show "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor \<circ>\<^sub>c y
                    = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c y"
                  by (typecheck_cfuncs, smt (z3) comp_associative2 f0 id_left_unit2 terminal_func_comp)
              qed
            qed
          qed
        qed

              (*have f1: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x = \<f>"
                by (typecheck_cfuncs, smt (z3) \<open>x \<in>\<^sub>c \<nat>\<^sub>c\<close> beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 successor_type terminal_func_comp)
              have "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x = \<f>"
              proof(rule ccontr)
                assume "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x \<noteq> \<f>"
                then have f2: "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x = \<t>"
                  using  true_false_only_truth_values x_type by (typecheck_cfuncs, blast)
                then have LHS_case2: "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
                  sorry
                then have RHS_case2: "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
                  using LHS_case2 case2 by blast
                then have "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
                  using f0 by presburger
                then show False
                  using f1 f2 LHS_case2 true_false_distinct by auto
              qed
              then show "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
                using  f1 by presburger
            qed
          qed
        qed*)


(*This concludes Case4*)

      

      have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c), 
        NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<longrightarrow> (p=q)"
      proof(auto) 
        assume "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c 
            (IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle>)\<^sup>\<sharp> 
              \<circ>\<^sub>c q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c q"
          using comp_associative2 by (typecheck_cfuncs, force)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c 
            (IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle>)\<^sup>\<sharp> 
              \<circ>\<^sub>c q = \<t>"
          by (typecheck_cfuncs_prems, metis id_right_unit2 id_type one_unique_element)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c 
            ((IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle>) 
                \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f q))\<^sup>\<sharp> = \<t>"
          by (typecheck_cfuncs, metis sharp_comp)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c 
            ((IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle>) 
                \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
          by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c 
            ((IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle>
                \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
          using cfunc_type_def comp_associative domain_comp by (typecheck_cfuncs, auto)
        then have "(IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c p = \<t>"
          by (typecheck_cfuncs, rule_tac FORALL_true_implies_all_true[where X="\<nat>\<^sub>c"], auto)
        then have "IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c p = \<t>"
          by (typecheck_cfuncs_prems, smt comp_associative2)
        then have "IMPLIES \<circ>\<^sub>c \<langle>NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c,NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i\<rangle> \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>"
          by (typecheck_cfuncs_prems, metis cart_prod_extract_left)
        then have "IMPLIES \<circ>\<^sub>c \<langle>(NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, q\<rangle>, (NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>p, q\<rangle>\<rangle>  = \<t>"
          using  cfunc_prod_comp by (typecheck_cfuncs, auto)
        then have "(NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t> \<Longrightarrow> (NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>"
          by (typecheck_cfuncs, metis IMPLIES_true_false_is_false true_false_only_truth_values)
        then have "NOT \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t> \<Longrightarrow> NOT \<circ>\<^sub>c eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>"
          by (typecheck_cfuncs_prems, smt comp_associative2)
        then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<f> \<Longrightarrow> eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<f>"
          using NOT_false_is_true NOT_is_true_implies_false by (typecheck_cfuncs_prems, presburger)
        then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, q\<rangle> = \<f> \<Longrightarrow> eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> = \<f>"
          using cfunc_cross_prod_comp_cfunc_prod id_cross_prod id_left_unit2 by (typecheck_cfuncs, auto)
        then have "p \<noteq> q \<Longrightarrow> i \<circ>\<^sub>c p \<noteq> i \<circ>\<^sub>c q"
          using eq_pred_iff_eq_conv by (typecheck_cfuncs_prems, blast)
        then show "p = q"
          using eqs by auto
      qed
        





(* Definition 2.6.12 *)
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool " (infix "is'_fixed'_point'_of" 50) where 
  "fixed_point a g = (\<exists> A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = a)"

lemma fixed_point_def2: 
  assumes "g : A \<rightarrow> A" "a \<in>\<^sub>c A"
  shows "fixed_point a g = (g \<circ>\<^sub>c a = a)"
  unfolding fixed_point_def using assms by blast
  
(*Definition 2.6.12b*)
definition fixed_point_property :: "cset \<Rightarrow> bool" where
  "fixed_point_property A = (\<forall> g. g : A \<rightarrow> A \<longrightarrow> (\<exists> a . fixed_point a g \<and> a \<in>\<^sub>c A))"

(*Theorem 2.6.13*)
lemma Lawveres_fixed_point_theorem:
  assumes p_type[type_rule]: "p : X \<rightarrow> A\<^bsup>X\<^esup>"
  assumes p_surj: "surjective p"
  shows "fixed_point_property A"
proof(unfold fixed_point_property_def,auto) 
  fix g 
  assume g_type[type_rule]: "g : A \<rightarrow> A"
  obtain \<phi> where \<phi>_def: "\<phi> = p\<^sup>\<flat>"
    by auto
  then have \<phi>_type[type_rule]: "\<phi> : X \<times>\<^sub>c X \<rightarrow> A"
    by (simp add: flat_type p_type)
  obtain f where f_def: "f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X)"
    by auto
  then have f_type[type_rule]:"f : X \<rightarrow> A"
    using \<phi>_type comp_type diagonal_type f_def g_type by blast
  obtain x_f where x_f: "metafunc f = p \<circ>\<^sub>c x_f \<and> x_f \<in>\<^sub>c X"
    using assms by (typecheck_cfuncs, metis p_surj surjective_def2)
  have "\<phi>\<^bsub>(-,x_f)\<^esub> = f"
  proof(rule one_separator[where X = "X", where Y = A])
    show "\<phi>\<^bsub>(-,x_f)\<^esub> : X \<rightarrow> A"
      using assms by (typecheck_cfuncs, simp add: x_f)
    show "f : X \<rightarrow> A"
      by (simp add: f_type)
    show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> \<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
    proof - 
      fix x 
      assume x_type[type_rule]: "x \<in>\<^sub>c X"
      have "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        using assms by (typecheck_cfuncs, meson right_param_on_el x_f)
      also have "... = ((eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p)) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        using assms \<phi>_def inv_transpose_func_def2 by auto
      also have "... = (eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        by (typecheck_cfuncs, metis comp_associative2 x_f)
      also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>id X  \<circ>\<^sub>c  x, p \<circ>\<^sub>c x_f\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod x_f by (typecheck_cfuncs, force)
      also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>x, metafunc f\<rangle>"
        using id_left_unit2 x_f by (typecheck_cfuncs, auto)
      also have "... = f \<circ>\<^sub>c x"
        by (simp add: eval_lemma f_type x_type)
      then show "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
        by (simp add: calculation)
    qed
  qed
  then have "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x_f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X) \<circ>\<^sub>c x_f"
    by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_associative domain_comp f_def x_f)
  then have "\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle> = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>"
    using  diag_on_elements right_param_on_el x_f by (typecheck_cfuncs, auto)
  then have "(\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>) is_fixed_point_of g"
    by (metis \<open>\<phi>\<^bsub>(-,x_f)\<^esub> = f\<close> \<open>\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x_f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal X \<circ>\<^sub>c x_f\<close> comp_type diag_on_elements f_type fixed_point_def2 g_type x_f)
  then show "\<exists>a. a is_fixed_point_of g \<and> a \<in>\<^sub>c A"
    using fixed_point_def cfunc_type_def g_type by auto
qed

(*Theorem 2.6.14*)
lemma Cantors_Negative_Theorem:
  "\<nexists> s. s : X \<rightarrow> \<P> X \<and> surjective(s)"
proof(rule ccontr, auto)
  fix s 
  assume s_type: "s : X \<rightarrow> \<P> X"
  assume s_surj: "surjective s"
  then have Omega_has_ffp: "fixed_point_property \<Omega>"
    using Lawveres_fixed_point_theorem powerset_def s_type by auto
  have Omega_doesnt_have_ffp: "\<not>(fixed_point_property \<Omega>)"
    unfolding fixed_point_property_def
  proof(unfold fixed_point_def, auto)   
    have  "NOT : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. (\<forall>A. a \<in>\<^sub>c A \<longrightarrow> NOT : A \<rightarrow> A \<longrightarrow> NOT \<circ>\<^sub>c a \<noteq> a) \<or> \<not> a \<in>\<^sub>c \<Omega>)"
      by (typecheck_cfuncs, metis AND_complementary AND_idempotent OR_complementary OR_idempotent true_false_distinct)
    then show "\<exists>g. g : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. (\<forall>A. a \<in>\<^sub>c A \<longrightarrow> g : A \<rightarrow> A \<longrightarrow> g \<circ>\<^sub>c a \<noteq> a) \<or> \<not> a \<in>\<^sub>c \<Omega>)"
      by auto
  qed
  show False
    using Omega_doesnt_have_ffp Omega_has_ffp by auto
qed

lemma generalized_Cantors_Negative_Theorem:
  assumes "\<Omega> \<le>\<^sub>c Y"
  shows "\<nexists> s. s : X \<rightarrow> Y\<^bsup>X\<^esup> \<and> surjective(s)"
proof(rule ccontr, auto)
  fix s 
  assume s_type: "s : X \<rightarrow> Y\<^bsup>X\<^esup>"
  assume s_surj: "surjective s"
  obtain m where m_def: "m : Y\<^bsup>X\<^esup> \<rightarrow> X" and m_mono: "monomorphism(m)"
    using epis_give_monos s_surj s_type surjective_is_epimorphism by blast
  have "\<Omega>\<^bsup>X\<^esup> \<le>\<^sub>c Y\<^bsup>X\<^esup>"
    oops


(*Exercise 2.6.15*)
lemma Cantors_Positive_Theorem:
  "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
proof - 
  have eq_pred_sharp_type[type_rule]: "(eq_pred X)\<^sup>\<sharp> : X \<rightarrow>  \<Omega>\<^bsup>X\<^esup>"
    by (typecheck_cfuncs)
  have "injective((eq_pred X)\<^sup>\<sharp>)"
    unfolding injective_def
  proof(auto)
    fix x y 
    assume "x \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have x_type[type_rule]: "x \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume "y \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have y_type[type_rule]:"y \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume eq: "eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c x = eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c y"
    have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
    proof - 
      have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c x\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c y\<rangle>"
        by (simp add: eq)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      also have "... = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      then show ?thesis
        by (simp add: calculation)
    qed
    then show "x = y"
      by (metis eq_pred_iff_eq x_type y_type)
  qed
  then show "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
    using eq_pred_sharp_type injective_imp_monomorphism by blast
qed


(*Corollary 2.6.15*)
(*This is only a note: For any set X, the set \<P>X of its subsets is strictly larger than X*)






end