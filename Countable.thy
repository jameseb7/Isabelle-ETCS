theory Countable
  imports ETCS_Axioms ETCS_Add ETCS_Mult ETCS_Pred ETCS_Parity
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
  shows "is_finite(Y \<Coprod> Y)"
  unfolding is_finite_def
proof(safe)
  fix m 
  assume m_type: " m : Y \<Coprod> Y \<rightarrow> Y \<Coprod> Y"
  assume m_mono: "monomorphism m"
  obtain x y where m_def: "m = (x \<amalg> y) \<and> x : Y \<rightarrow> Y \<Coprod> Y \<and> y : Y \<rightarrow> Y \<Coprod> Y"
    using m_type coprod_decomp by blast
  show "isomorphism m"
    using assms m_def m_type m_mono apply typecheck_cfuncs
    oops



lemma coproduct_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  assumes "is_finite(X \<Coprod> X)"
  assumes "is_finite(Y \<Coprod> Y)"
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
  using countable_def epis_give_monos halve_with_parity_iso halve_with_parity_type iso_imp_epi_and_monic by auto



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
  then have False
    using natural_numbers_are_countably_infinite not_finite_and_infinite by blast
next 
  assume "\<nexists>s. s : X \<rightarrow> \<nat>\<^sub>c \<and> surjective s"
  show "is_finite X"
    unfolding is_finite_def
 
  proof(rule ccontr)
    assume "\<not> is_finite X"
    then have "is_infinite X"
      using either_finite_or_infinite by blast
    then obtain m where m_def: "m : X \<rightarrow> X \<and> monomorphism(m) \<and> \<not>surjective(m)"
      using is_infinite_def by blast
    oops








end