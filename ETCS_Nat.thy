theory ETCS_Nat
  imports ETCS_Func
begin

section \<open>Axiom 10: Natural Number Object\<close>

axiomatization
  natural_numbers :: "cset" ("\<nat>\<^sub>c") and
  zero :: "cfunc" and
  successor :: "cfunc"
  where
  zero_type[type_rule]: "zero \<in>\<^sub>c \<nat>\<^sub>c" and 
  successor_type[type_rule]: "successor: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and 
  natural_number_object_property: 
  "q : one \<rightarrow> X \<Longrightarrow> f: X \<rightarrow> X \<Longrightarrow>
   (\<exists>!u. u: \<nat>\<^sub>c \<rightarrow> X \<and>
   triangle_commutes one \<nat>\<^sub>c X zero u q \<and>
   square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X u f successor u)"

lemma natural_number_object_property2:
  assumes "q : one \<rightarrow> X" "f: X \<rightarrow> X"
  shows "\<exists>!u. u: \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = q \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
  using assms natural_number_object_property[where q=q, where f=f, where X=X]
  unfolding triangle_commutes_def square_commutes_def
  by auto

lemma natural_number_object_func_unique:
  assumes u_type: "u : \<nat>\<^sub>c \<rightarrow> X" and v_type: "v : \<nat>\<^sub>c \<rightarrow> X" and f_type: "f: X \<rightarrow> X"
  assumes zeros_eq: "u \<circ>\<^sub>c zero = v \<circ>\<^sub>c zero"
  assumes u_successor_eq: "u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u"
  assumes v_successor_eq: "v \<circ>\<^sub>c successor = f \<circ>\<^sub>c v"
  shows "u = v"
proof -
  have u_zero_type: "u \<circ>\<^sub>c zero : one \<rightarrow> X"
    using u_type zero_type comp_type by auto
  have triangle_commutes_u: "triangle_commutes one \<nat>\<^sub>c X zero u (u \<circ>\<^sub>c zero)"
    by (simp add: triangle_commutes_def u_type u_zero_type zero_type)
  have square_commutes_u: "square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X u f successor u"
    by (simp add: f_type square_commutes_def successor_type u_successor_eq u_type)
  have uniqueness: "\<And> w. w: \<nat>\<^sub>c \<rightarrow> X \<and>
   triangle_commutes one \<nat>\<^sub>c X zero w (u \<circ>\<^sub>c zero) \<and>
   square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X w f successor w \<Longrightarrow> w = u"
    using u_zero_type triangle_commutes_u square_commutes_u
    using natural_number_object_property square_commutes_def by blast

  have v_zero_type: "v \<circ>\<^sub>c zero : one \<rightarrow> X"
    using v_type zero_type comp_type by auto
  have triangle_commutes_v: "triangle_commutes one \<nat>\<^sub>c X zero v (u \<circ>\<^sub>c zero)"
    by (simp add: triangle_commutes_def v_type v_zero_type zero_type zeros_eq)
  have square_commutes_v: "square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X v f successor v"
    by (simp add: f_type square_commutes_def successor_type v_successor_eq v_type)

  from uniqueness show "u = v"
    using square_commutes_v triangle_commutes_v v_type by blast
qed


definition is_NNO :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool"  where
   "is_NNO Y z s \<longleftrightarrow>(\<forall> X f q. ((q : one \<rightarrow> X) \<and> (f: X \<rightarrow> X))\<longrightarrow>
   (\<exists>!u. u: Y \<rightarrow> X \<and>
   triangle_commutes one Y X z u q \<and>
   square_commutes Y X Y X u f s u))"

lemma N_is_a_NNO:
    "is_NNO \<nat>\<^sub>c zero successor"
  by (simp add: is_NNO_def natural_number_object_property)

(* Exercise 2.6.5 *)
lemma NNOs_are_iso_N:
  assumes "is_NNO N z s"
  shows "N \<cong> \<nat>\<^sub>c"
proof-
  have z_and_s_type: "(z : one \<rightarrow>  N) \<and> (s:  N \<rightarrow>  N)"
    using assms is_NNO_def square_commutes_def successor_type triangle_commutes_def zero_type by auto
  then obtain u where u_type: "(u: \<nat>\<^sub>c \<rightarrow> N \<and>
   triangle_commutes one \<nat>\<^sub>c N zero u z \<and>
   square_commutes \<nat>\<^sub>c N \<nat>\<^sub>c N u s successor u)"
      proof -
         assume "\<And>u. u : \<nat>\<^sub>c \<rightarrow> N \<and> triangle_commutes one \<nat>\<^sub>c N zero u z \<and> square_commutes \<nat>\<^sub>c N \<nat>\<^sub>c N u s successor u \<Longrightarrow> thesis"
         then show ?thesis
           using z_and_s_type natural_number_object_property by blast
      qed
  then obtain v where v_type: "(v: N \<rightarrow> \<nat>\<^sub>c \<and>
   triangle_commutes one N  \<nat>\<^sub>c z v zero \<and>
   square_commutes N  \<nat>\<^sub>c N  \<nat>\<^sub>c v successor s v)"
     using assms is_NNO_def successor_type zero_type by blast
  then have vuzeroEqzero: "v \<circ>\<^sub>c (u \<circ>\<^sub>c zero) = zero"
     using  u_type triangle_commutes_def by auto
  have id_facts1: "(id(\<nat>\<^sub>c): \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c)\<and>
          (triangle_commutes one \<nat>\<^sub>c \<nat>\<^sub>c zero (id(\<nat>\<^sub>c)) zero)\<and>
          (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c (id(\<nat>\<^sub>c)) successor successor (id(\<nat>\<^sub>c)))"
     by (metis cfunc_type_def id_left_unit id_right_unit id_type square_commutes_def successor_type triangle_commutes_def zero_type)
  then have vu_facts: "((v \<circ>\<^sub>c u): \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c)\<and>
          (triangle_commutes one \<nat>\<^sub>c \<nat>\<^sub>c zero (v \<circ>\<^sub>c u) zero)\<and>
          (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c (v \<circ>\<^sub>c u) successor successor (v \<circ>\<^sub>c u))"
  proof auto
    show vu_type: "v \<circ>\<^sub>c u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      using comp_type u_type v_type by blast
    show "triangle_commutes one \<nat>\<^sub>c \<nat>\<^sub>c zero (v \<circ>\<^sub>c u) zero"
      using comp_associative2 comp_type triangle_commutes_def u_type v_type by auto
    show "square_commutes \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c (v \<circ>\<^sub>c u) successor successor (v \<circ>\<^sub>c u)"
      by (metis vu_type cfunc_type_def comp_associative square_commutes_def u_type v_type)
  qed
  then have half_isomorphism: "(v \<circ>\<^sub>c u) = id(\<nat>\<^sub>c)"
      using id_facts1 natural_number_object_property successor_type zero_type by blast
  have uvzEqz: "u \<circ>\<^sub>c (v \<circ>\<^sub>c z) = z"
    using triangle_commutes_def u_type v_type by auto
  have id_facts2: "(id(N): N \<rightarrow> N)\<and>
          (triangle_commutes one N N z (id(N)) z)\<and>
          (square_commutes N N N N (id(N)) s s (id(N)))"
    by (metis cfunc_type_def id_left_unit id_right_unit id_type square_commutes_def triangle_commutes_def z_and_s_type)
  then have uv_facts: "((u \<circ>\<^sub>c v): N \<rightarrow> N)\<and>
          (triangle_commutes one N N z (u \<circ>\<^sub>c v) z)\<and>
          (square_commutes N N N N (u \<circ>\<^sub>c v) s s (u \<circ>\<^sub>c v))"
    proof -
      have "u \<circ>\<^sub>c v : N \<rightarrow> N"
        using cfunc_type_def codomain_comp domain_comp u_type v_type by presburger
      then show ?thesis
        by (metis cfunc_type_def comp_associative triangle_commutes_def square_commutes_def u_type v_type)
    qed
  then have half_isomorphism2: "(u \<circ>\<^sub>c v) = id(N)"
    using assms id_facts2 is_NNO_def z_and_s_type by blast
  then show "N \<cong> \<nat>\<^sub>c"
    using cfunc_type_def half_isomorphism is_isomorphic_def isomorphism_def u_type v_type by fastforce
qed

(* Converse to Exercise 2.6.5 *)
lemma Iso_to_N_is_NNO:
  assumes "N \<cong> \<nat>\<^sub>c"
  shows "\<exists> z s. is_NNO N z s"
proof - 
  obtain i where i_type: "i: N \<rightarrow> \<nat>\<^sub>c \<and> isomorphism(i)"
    using assms is_isomorphic_def by auto 
  obtain j where j_type: "j: \<nat>\<^sub>c \<rightarrow> N \<and> isomorphism(j) \<and> i \<circ>\<^sub>c j = id(\<nat>\<^sub>c) \<and> j \<circ>\<^sub>c i = id(N)"
    using cfunc_type_def i_type isomorphism_def by fastforce
  obtain z where z_form: "z = j \<circ>\<^sub>c zero"
    by simp
  obtain s where s_form: "s = (j \<circ>\<^sub>c successor)  \<circ>\<^sub>c i"
    by simp
  have z_type: "z: one \<rightarrow> N"
    using comp_type j_type z_form zero_type by blast
  have s_type: "s: N \<rightarrow> N"
    using cfunc_type_def codomain_comp domain_comp i_type j_type s_form successor_type by auto
  have "is_NNO N z s"
    unfolding is_NNO_def
  proof auto
    fix X q f 
    assume q_type: "q: one \<rightarrow> X"
    assume f_type: "f:   X \<rightarrow> X"

    obtain u where u_properties: "
     (u: \<nat>\<^sub>c \<rightarrow> X \<and>
   triangle_commutes one \<nat>\<^sub>c X zero u q \<and>
   square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X u f successor u)"
      using f_type natural_number_object_property q_type by blast
    obtain v where v_Eqs_ui: "v = u \<circ>\<^sub>c i"
      by simp
    then have v_type: "v: N \<rightarrow> X"
      using comp_type i_type u_properties by blast
    then have D2_triangle: "v \<circ>\<^sub>c z = q"
      by (metis cfunc_type_def comp_associative i_type id_right_unit2 j_type triangle_commutes_def u_properties v_Eqs_ui z_form)
      
    have D2_square: "v \<circ>\<^sub>c s = f \<circ>\<^sub>c v"
      by (metis cfunc_type_def codomain_comp comp_associative i_type id_right_unit2 j_type s_form
          square_commutes_def u_properties v_Eqs_ui v_type)
      
    show unique_v: "\<And> w y. w : N \<rightarrow> X \<Longrightarrow> y : N \<rightarrow> X \<Longrightarrow>
       triangle_commutes one N X z w q \<Longrightarrow> square_commutes N X N X w f s w \<Longrightarrow>
       triangle_commutes one N X z y q \<Longrightarrow> square_commutes N X N X y f s y \<Longrightarrow> w = y"
    proof -
      fix w y
      assume w_type: "w: N \<rightarrow> X"
      assume "square_commutes N X N X w f s w"
      then have w_square:"w \<circ>\<^sub>c s = f \<circ>\<^sub>c w"
        by (simp add: square_commutes_def)
      assume "triangle_commutes one N X z w q"
      then have w_triangle: "q = w \<circ>\<^sub>c z"
        by (simp add: triangle_commutes_def)

      assume y_type: "y: N \<rightarrow> X"
      assume "square_commutes N X N X y f s y"
      then have y_square:"y \<circ>\<^sub>c s = f \<circ>\<^sub>c y"
        by (simp add: square_commutes_def)
      assume "triangle_commutes one N X z y q"
      then have y_triangle: "q = y \<circ>\<^sub>c z"
        by (simp add: triangle_commutes_def)

      have "\<And> w. w: N \<rightarrow> X \<Longrightarrow> w \<circ>\<^sub>c s = f \<circ>\<^sub>c w \<Longrightarrow> q = w \<circ>\<^sub>c z \<Longrightarrow> w = v"
      proof -
        fix w 
        assume w_type: "w: N \<rightarrow> X"
        assume w_square:"w \<circ>\<^sub>c s = f \<circ>\<^sub>c w"
        assume w_triangle: "q = w \<circ>\<^sub>c z"

        have fact1: "(w \<circ>\<^sub>c j): \<nat>\<^sub>c \<rightarrow> X"
          by (meson comp_type j_type w_type)
        then have fact2: "triangle_commutes one \<nat>\<^sub>c X zero (w \<circ>\<^sub>c j) q"
          using comp_associative2 j_type q_type triangle_commutes_def w_triangle w_type z_form zero_type by auto
        then have fact3: "square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X (w \<circ>\<^sub>c j) f successor (w \<circ>\<^sub>c j)"
        proof -
          have "successor = successor \<circ>\<^sub>c i \<circ>\<^sub>c j"
            by (metis (no_types) cfunc_type_def id_right_unit j_type successor_type)
          then show ?thesis
            by (metis cfunc_type_def codomain_comp comp_associative domain_comp f_type i_type j_type s_form square_commutes_def successor_type w_square w_type)
        qed
        then have fact4: "(w \<circ>\<^sub>c j)\<circ>\<^sub>c successor = (f \<circ>\<^sub>c w) \<circ>\<^sub>c j"
          using comp_associative2 j_type square_commutes_def w_type by auto
        then have wj_Eqs_u: "w \<circ>\<^sub>c j = u"
          using f_type fact1 fact2 fact3 natural_number_object_property q_type u_properties by blast
        then show "w = v"
          by (smt comp_associative2 i_type id_right_unit2 j_type v_Eqs_ui w_type)
      qed
      then show "w = y"
        using w_square w_triangle w_type y_square y_triangle y_type by blast
    qed
    show "\<exists>u. u : N \<rightarrow> X \<and> triangle_commutes one N X z u q \<and> square_commutes N X N X u f s u"
      using D2_square D2_triangle f_type q_type s_type square_commutes_def triangle_commutes_def v_type z_type by auto
  qed
  then show "\<exists>z s. is_NNO N z s"
    by auto
qed

lemma zero_is_not_successor:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "zero \<noteq> successor \<circ>\<^sub>c n"
proof (rule ccontr, auto)
  assume for_contradiction: "zero = successor \<circ>\<^sub>c n"
  have "\<exists>!u. u: \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> u \<circ>\<^sub>c zero = \<t> \<and> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    by (typecheck_cfuncs, rule natural_number_object_property2)
  then obtain u where  u_type:  "u: \<nat>\<^sub>c \<rightarrow> \<Omega>" and 
                       u_triangle: "u \<circ>\<^sub>c zero = \<t>" and  
                       u_square: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    by auto
  have "\<t> = \<f>" 
  proof -
    have "\<t> = u  \<circ>\<^sub>c zero"
      by (simp add: u_triangle)
    also have "... = u \<circ>\<^sub>c successor \<circ>\<^sub>c n"
      by (simp add: for_contradiction)
    also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c u \<circ>\<^sub>c n"
      using assms u_type by (typecheck_cfuncs, simp add:  comp_associative2 u_square)
    also have "... = \<f>"
      using assms u_type by (typecheck_cfuncs, metis cfunc_type_def comp_associative id_right_unit2 id_type terminal_func_comp terminal_func_unique)
    then show ?thesis using calculation by auto
  qed
  then show False
    using true_false_distinct by blast
qed




(* Proposition 2.6.6 *)
lemma  oneUN_iso_N_isomorphism:
 "isomorphism(zero \<amalg> successor)" 
proof - 
 have iso_type: "zero \<amalg> successor : one \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
   by (simp add: cfunc_coprod_type successor_type zero_type)
  obtain i0 where coproj0:  "i0 = left_coproj one \<nat>\<^sub>c"
    by simp
  obtain i1 where coproj1:  "i1 = right_coproj one \<nat>\<^sub>c"
    by simp 
  have i1zUi1s_type: "(i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor) : one \<Coprod> \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c"
    using cfunc_coprod_type coproj1 right_proj_type successor_type zero_type comp_type by auto
  have i1z_type: "i1 \<circ>\<^sub>c zero : one \<rightarrow>  one \<Coprod> \<nat>\<^sub>c"
    using coproj1 right_proj_type zero_type comp_type by auto
  obtain g where g_type: "g: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)" and
   g_triangle: "triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0" and
   g_square: "square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))"
    by (metis coproj0 i1zUi1s_type left_proj_type natural_number_object_property square_commutes_def)
  then have second_diagram1: "g\<circ>\<^sub>c zero = i0"
    by (simp add: triangle_commutes_def)
  have second_diagram2: "g \<circ>\<^sub>c successor =   ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c g"
    using g_square unfolding square_commutes_def by auto
  then have second_diagram3: "g \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)  = (i1 \<circ>\<^sub>c zero)"
    using g_type i1z_type
    by (typecheck_cfuncs, smt cfunc_coprod_comp comp_associative2 coproj0 coproj1 i1zUi1s_type
        iso_type left_coproj_cfunc_coprod left_proj_type right_proj_type second_diagram1 second_diagram2)
  then have g_s_s_Eqs_i1zUi1s_g_s:
    "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (g \<circ>\<^sub>c successor)"
    using comp_associative2 g_type i1zUi1s_type second_diagram2 successor_type by fastforce
  then have g_s_s_zEqs_i1zUi1s_i1z: "((g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor)\<circ>\<^sub>c zero =
    ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (i1 \<circ>\<^sub>c zero)"
    by (smt cfunc_type_def codomain_comp comp_associative domain_comp g_type i1zUi1s_type second_diagram3 successor_type zero_type)
    
  then have i1_sEqs_i1zUi1s_i1: "i1 \<circ>\<^sub>c successor =
    ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c i1"
    by (metis comp_type coproj1 i1z_type right_coproj_cfunc_coprod right_proj_type successor_type)
  then obtain u where u_type: "(u: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c))" and
      u_triangle: "(triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero u (i1 \<circ>\<^sub>c zero))" and
      u_square: "(square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor u u ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)))"
    using comp_type coproj1 i1zUi1s_type right_proj_type square_commutes_def successor_type triangle_commutes_def zero_type by fastforce
  then have u_Eqs_i1: "u=i1"
    by (metis coproj1 i1_sEqs_i1zUi1s_i1 natural_number_object_property right_proj_type square_commutes_def triangle_commutes_def)
  then have g_s_type: "g\<circ>\<^sub>c successor: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)"
    using comp_type g_type successor_type by blast
  then have g_s_triangle: 
  "triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero (g\<circ>\<^sub>c successor) ( (i1 \<circ>\<^sub>c zero))"
    using comp_associative2 g_type i1z_type second_diagram3 successor_type triangle_commutes_def zero_type by auto
  then have g_s_square: 
"square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor  (g\<circ>\<^sub>c successor)  (g\<circ>\<^sub>c successor) ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))"
    by (simp add: g_s_s_Eqs_i1zUi1s_g_s g_s_type i1zUi1s_type square_commutes_def successor_type)
  then have u_Eqs_g_s: "u=(g\<circ>\<^sub>c successor)"
    using g_s_s_Eqs_i1zUi1s_g_s g_s_triangle i1_sEqs_i1zUi1s_i1 i1zUi1s_type natural_number_object_func_unique triangle_commutes_def u_Eqs_i1 u_type by blast
  then have g_sEqs_i1: "(g\<circ>\<^sub>c successor) = i1"
    using u_Eqs_i1 by blast
  then have eq1: "(zero \<amalg> successor) \<circ>\<^sub>c g = id(\<nat>\<^sub>c)"
  proof - 
    have firstCenteredEqn1: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c zero) = 
                            (zero \<amalg> successor) \<circ>\<^sub>c i0"
      using second_diagram1 by auto
    also have firstCenteredEqn2:  "... = zero"
      using coproj0 left_coproj_cfunc_coprod successor_type zero_type by auto
    then have firstCenteredEqn: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c zero) = zero"
      by (simp add: firstCenteredEqn1)
    have secondCenteredEqn1: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c successor) = 
                            (zero \<amalg> successor) \<circ>\<^sub>c i1"
      using g_sEqs_i1 by blast
    have secondCenteredEqn: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c successor) = successor"
      using coproj1 right_coproj_cfunc_coprod secondCenteredEqn1 successor_type zero_type by auto
    then show "(zero \<amalg> successor) \<circ>\<^sub>c g = id(\<nat>\<^sub>c)"
    proof -
        have f1: "\<forall>c ca cb. (c : ca \<rightarrow> cb) = (domain c = ca \<and> codomain c = cb)"
           using cfunc_type_def by blast
        then have f2: "domain successor = \<nat>\<^sub>c \<and> codomain successor = \<nat>\<^sub>c"
           using successor_type by presburger
        have f3: "domain successor = \<nat>\<^sub>c \<and> codomain successor = \<nat>\<^sub>c"
           using f1 successor_type by presburger
        have f5: "domain i1 = \<nat>\<^sub>c \<and> codomain i1 = one \<Coprod> \<nat>\<^sub>c"
           using f1 g_sEqs_i1 g_s_type by presburger
        have "i1 \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c g = (i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor) \<circ>\<^sub>c g"
          using cfunc_coprod_comp comp_associative f1 g_sEqs_i1 g_s_type g_type iso_type successor_type zero_type by auto
        then have "i1 \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c g = i1 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
          by (metis f5 g_sEqs_i1 id_right_unit second_diagram2)
        then show ?thesis
          by (smt cfunc_type_def comp_type coproj1 f5 g_type id_codomain iso_type monomorphism_def right_coproj_are_monomorphisms)
    qed
  qed
  then have eq2: "g \<circ>\<^sub>c (zero \<amalg> successor) = id(one \<Coprod> \<nat>\<^sub>c)"
  proof - 
    have ThirdCenteredEqn1: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i0) = g \<circ>\<^sub>c zero"
      using coproj0 left_coproj_cfunc_coprod successor_type zero_type by auto
    also have ThirdCenteredEqn2: "... = i0"
      by (simp add: second_diagram1)
    then have ThirdCenteredEqn: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i0) = i0"
      by (simp add: calculation)
    have ForthCenteredEqn1: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i1) = g \<circ>\<^sub>c successor"
      using coproj1 right_coproj_cfunc_coprod successor_type zero_type by auto
    have ForthCenteredEqn2: "... = i1"
      using g_sEqs_i1 by blast
    then have ForthCenteredEqn: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i1) = i1"
      using ForthCenteredEqn1 by blast
    then show "g \<circ>\<^sub>c (zero \<amalg> successor) = id(one \<Coprod> \<nat>\<^sub>c)"
      using g_type by (typecheck_cfuncs, smt cfunc_coprod_comp cfunc_coprod_unique coproj0 coproj1
          id_left_unit2 left_proj_type second_diagram1 u_Eqs_g_s u_Eqs_i1 u_type)
  qed
  show "isomorphism(zero \<amalg> successor)"
    using eq1 eq2 cfunc_type_def g_type iso_type isomorphism_def by auto
qed

lemma zUs_epic:
 "epimorphism(zero \<amalg> successor)"
  by (simp add: iso_imp_epi_and_monic oneUN_iso_N_isomorphism)

lemma zUs_surj:
 "surjective(zero \<amalg> successor)"
  by (simp add: cfunc_type_def epi_is_surj zUs_epic)

lemma nonzero_is_succ_pre:
  assumes "x \<in>\<^sub>c  (one \<Coprod> \<nat>\<^sub>c)"
  shows "(x = (left_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c id one) \<or>
         (\<exists>n. (n \<in>\<^sub>c \<nat>\<^sub>c) \<and> (x = (right_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c n ))"
proof(auto)
  assume not_this: "\<forall> n. n \<in>\<^sub>c  \<nat>\<^sub>c  \<longrightarrow>  x \<noteq> right_coproj one \<nat>\<^sub>c \<circ>\<^sub>c n"
  show "x = left_coproj one \<nat>\<^sub>c  \<circ>\<^sub>c  id one"
    using assms not_this coprojs_jointly_surj one_unique_element by (typecheck_cfuncs, blast)
qed




lemma nonzero_is_succ:
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "k \<noteq> zero"
  shows "\<exists>n.(n\<in>\<^sub>c \<nat>\<^sub>c \<and> k = successor \<circ>\<^sub>c n)"
proof - 
  have x_exists: "\<exists>x. ((x \<in>\<^sub>c one \<Coprod> \<nat>\<^sub>c) \<and> (zero \<amalg> successor \<circ>\<^sub>c x = k))"
    using assms cfunc_type_def surjective_def zUs_surj by (typecheck_cfuncs, auto)
  obtain x where x_def: "((x \<in>\<^sub>c one \<Coprod> \<nat>\<^sub>c) \<and> (zero \<amalg> successor \<circ>\<^sub>c x = k))"
    using x_exists by blast
  have cases:  "(x = (left_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c id one) \<or> 
                (\<exists>n. (n \<in>\<^sub>c \<nat>\<^sub>c \<and> x = (right_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c n))"
    by (simp add: nonzero_is_succ_pre x_def)
  have not_case_1: "x \<noteq> (left_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c id one"
  proof(rule ccontr,auto)
    assume bwoc: "x = left_coproj one \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c one"
    have contradiction: "k = zero"
      by (metis bwoc id_right_unit2 left_coproj_cfunc_coprod left_proj_type successor_type x_def zero_type)
    show False
      using contradiction assms(2) by force
  qed
  then obtain n where n_def: "n \<in>\<^sub>c \<nat>\<^sub>c \<and> x = (right_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c n"
    using cases by blast
  then have "k = zero \<amalg> successor \<circ>\<^sub>c x"
    using x_def by blast
  also have "... = zero \<amalg> successor \<circ>\<^sub>c  right_coproj one \<nat>\<^sub>c \<circ>\<^sub>c n"
    by (simp add: n_def)
  also have "... =  (zero \<amalg> successor \<circ>\<^sub>c  right_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c n"
    using cfunc_coprod_type cfunc_type_def comp_associative n_def right_proj_type successor_type zero_type by auto
  also have "... = successor \<circ>\<^sub>c n"
    using right_coproj_cfunc_coprod successor_type zero_type by auto
  then show ?thesis
    using   calculation n_def by auto
qed



(* Corollary *)
lemma oneUN_iso_N:
  "one \<Coprod> \<nat>\<^sub>c \<cong> \<nat>\<^sub>c"
  using cfunc_coprod_type is_isomorphic_def oneUN_iso_N_isomorphism successor_type zero_type by blast

lemma NUone_iso_N:
  "\<nat>\<^sub>c \<Coprod> one \<cong> \<nat>\<^sub>c"
  using coproduct_commutes isomorphic_is_transitive oneUN_iso_N by blast





    










(* Proposition 2.6.7 *)
lemma Peano's_Axioms:
 "injective(successor) \<and> \<not>surjective(successor)"
proof - 
  have i1_mono: "monomorphism(right_coproj one \<nat>\<^sub>c)"
    by (simp add: right_coproj_are_monomorphisms)
  have zUs_iso: "isomorphism(zero \<amalg> successor)"
    using oneUN_iso_N_isomorphism by blast
  have zUsi1EqsS: "(zero \<amalg> successor) \<circ>\<^sub>c (right_coproj one \<nat>\<^sub>c) = successor"
    using right_coproj_cfunc_coprod successor_type zero_type by auto
  then have succ_mono: "monomorphism(successor)"
    by (metis cfunc_coprod_type cfunc_type_def composition_of_monic_pair_is_monic i1_mono iso_imp_epi_and_monic oneUN_iso_N_isomorphism right_proj_type successor_type zero_type)
  have f_fact: "(\<f>\<circ>\<^sub>c\<beta>\<^bsub>\<Omega>\<^esub>): \<Omega> \<rightarrow> \<Omega>"
    using comp_type false_func_type terminal_func_type by blast
  then obtain u where u_form: "(u:  \<nat>\<^sub>c  \<rightarrow> \<Omega>) \<and>
   (triangle_commutes one  \<nat>\<^sub>c \<Omega> zero u \<t>) \<and>
   (square_commutes \<nat>\<^sub>c \<Omega> \<nat>\<^sub>c \<Omega> u (\<f>\<circ>\<^sub>c\<beta>\<^bsub>\<Omega>\<^esub>) successor u)"
    using natural_number_object_property true_func_type by blast
  have s_not_surj: "\<not>(surjective(successor))"
    proof (rule ccontr, auto)
      assume BWOC : "surjective(successor)"
      obtain n where snEqz: "successor \<circ>\<^sub>c n = zero" and n_type: "n : one \<rightarrow> \<nat>\<^sub>c"
        using BWOC cfunc_type_def successor_type surjective_def zero_type by auto
      then show False
        by (metis zero_is_not_successor)
    qed
  then show "injective successor \<and> \<not> surjective successor"
    using monomorphism_imp_injective succ_mono by blast
qed

lemma succ_inject:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "successor \<circ>\<^sub>c n = successor \<circ>\<^sub>c m \<Longrightarrow> n=m"
  by (metis Peano's_Axioms assms cfunc_type_def injective_def successor_type) 





(* Definition 2.6.9 *)
definition epi_countable :: "cset \<Rightarrow> bool" where
  "epi_countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

lemma emptyset_is_not_epi_countable:
  "\<not> (epi_countable \<emptyset>)"
  using comp_type emptyset_is_empty epi_countable_def zero_type by blast


(* Definition 2.6.9 *)
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f)"



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


lemma product_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  shows "is_finite(X \<times>\<^sub>c Y)"
  oops

lemma coproduct_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  shows "is_finite(X \<Coprod>  Y)"
  unfolding is_finite_def
  oops


lemma NxN_is_countable:
  "countable(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
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
  unfolding countable_def
  oops


(*Exercise 2.6.11*)
lemma coproduct_of_countables_is_countable:
  assumes "countable X" "countable Y"
  assumes NuN_is_countable: "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
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




(* Definition 2.6.12 *)
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "fixed_point a g \<longleftrightarrow> (\<exists> A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = g)"
definition has_fixed_point :: "cfunc \<Rightarrow> bool" where
  "has_fixed_point g \<longleftrightarrow> (\<exists> a. fixed_point a g)"
definition fixed_point_property :: "cset \<Rightarrow> bool" where
  "fixed_point_property A \<longleftrightarrow> (\<forall> g. g : A \<rightarrow> A \<longrightarrow> has_fixed_point g)"

(* Exercise 2.6.15 *)
lemma inject_into_powerset: 
  "(\<exists> f.((f : X \<rightarrow> \<P> X) \<and> injective(f)))"
proof -
  obtain \<delta> where delta_def: "\<delta> = diagonal(X)"
    by simp
  have \<delta>_type: "\<delta> : X \<rightarrow> X \<times>\<^sub>c X"
    by (simp add: cfunc_prod_type delta_def diagonal_def id_type)
  have \<delta>_mono: "monomorphism(\<delta>)"
    by (metis \<delta>_type cfunc_type_def comp_monic_imp_monic delta_def diagonal_def id_isomorphism id_type iso_imp_epi_and_monic right_cart_proj_cfunc_prod right_cart_proj_type)
  obtain \<chi>\<^sub>\<delta> where chi_delta_def: "is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> \<delta> \<chi>\<^sub>\<delta>"
    using \<delta>_mono \<delta>_type characteristic_function_exists by blast 
  have helpful_fact: "\<forall> x y. (x\<in>\<^sub>c X \<and> y\<in>\<^sub>c X \<longrightarrow> (x=y \<longleftrightarrow> \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>))"
  proof (auto)
    fix y 
    assume y_type: "y \<in>\<^sub>c X"
    have "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>y,y\<rangle> = \<chi>\<^sub>\<delta> \<circ>\<^sub>c (\<delta> \<circ>\<^sub>c y)"
      by (simp add: delta_def diag_on_elements y_type)
    also have "... =  \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c y)"
      using y_type \<delta>_type chi_delta_def comp_associative2 is_pullback_def square_commutes_def
      by (typecheck_cfuncs, auto)
    also have "... = \<t>"
      by (metis cfunc_type_def comp_type id_right_unit id_type one_unique_element terminal_func_type true_func_type y_type)
    then show "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>y,y\<rangle> = \<t>"
      by (simp add: calculation)
  next
    fix x y
    assume x_type: "x\<in>\<^sub>c X" 
    assume y_type: "y\<in>\<^sub>c X" 
    assume chi_xxEq_t: "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>"
     
    have xy_prod_type: "\<langle>x,y\<rangle> : one \<rightarrow> X \<times>\<^sub>c X"
          by (simp add: cfunc_prod_type x_type y_type)
    have pullbackProp: "is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> \<delta> \<chi>\<^sub>\<delta>"
      using chi_delta_def by blast
    then obtain k where k_type: "k : one \<rightarrow> X \<and> \<delta> \<circ>\<^sub>c k = \<langle>x,y\<rangle>"
      unfolding is_pullback_def
      by (metis chi_xxEq_t id_right_unit2 id_type true_func_type xy_prod_type)
    then have "x = (left_cart_proj X X) \<circ>\<^sub>c \<langle>x,y\<rangle>"
          using left_cart_proj_cfunc_prod x_type y_type by auto
    also have "... = (left_cart_proj X X) \<circ>\<^sub>c (\<delta> \<circ>\<^sub>c k)"
          using k_type by auto
    also have "... = ((left_cart_proj X X) \<circ>\<^sub>c \<langle>id(X),id(X)\<rangle>) \<circ>\<^sub>c k"
      using \<delta>_type comp_associative2 delta_def diagonal_def k_type left_cart_proj_type by fastforce
    also have "... = id(X) \<circ>\<^sub>c k"
          by (metis id_type left_cart_proj_cfunc_prod)
    also have "... = y"
          by (metis calculation cfunc_prod_comp cfunc_type_def delta_def diagonal_def id_left_unit id_type k_type right_cart_proj_cfunc_prod y_type)
    then show "x = y"
         using calculation by blast
    qed
  
  have  \<chi>\<^sub>\<delta>sharp_type: "\<chi>\<^sub>\<delta>\<^sup>\<sharp> : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>"
    using chi_delta_def is_pullback_def square_commutes_def transpose_func_type by auto
  have \<chi>\<^sub>\<delta>sharp_injective: "injective(\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      unfolding injective_def
  proof (auto)
      fix x y 
      assume "x \<in>\<^sub>c domain (\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      then have x_type: "x \<in>\<^sub>c X"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_type_def by auto
      assume "y \<in>\<^sub>c domain (\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      then have y_type: "y \<in>\<^sub>c X"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_type_def by auto
      assume chixEqschiy: "\<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c x = \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c y"
      
      have "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,x\<rangle> = ((eval_func \<Omega> X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,x\<rangle>"
        using chi_delta_def is_pullback_def square_commutes_def transpose_func_def by auto
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,x\<rangle>)"
        using \<chi>\<^sub>\<delta>sharp_type x_type by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c x, \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c x\<rangle>"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_type x_type by auto
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c x, \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c y\<rangle>"
        using chixEqschiy by auto
      also have "... =  (eval_func \<Omega> X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,y\<rangle>)"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_type x_type y_type by auto
      also have "... = \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle>"
        using \<chi>\<^sub>\<delta>sharp_type x_type y_type chi_delta_def comp_associative2 is_pullback_def
          square_commutes_def transpose_func_def by (typecheck_cfuncs, auto)
      then have computation: "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,x\<rangle> = \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle>"
        by (simp add: calculation)
      then show "x=y"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_type_def helpful_fact x_type y_type by fastforce
    qed
  then show "(\<exists> f.((f : X \<rightarrow> \<P> X) \<and> injective(f)))"
    using \<chi>\<^sub>\<delta>sharp_type powerset_def by auto
qed






end