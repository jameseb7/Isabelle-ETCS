theory ETCS_Nat
  imports ETCS_Func
begin

section \<open>Axiom 10: Natural Number Object\<close>

axiomatization
  natural_numbers :: "cset" ("\<nat>\<^sub>c") and
  zero :: "cfunc" and
  successor :: "cfunc"
  where
  zero_type: "zero \<in>\<^sub>c \<nat>\<^sub>c" and 
  successor_type: "successor: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and 
  natural_number_object_property: 
  "((q : one \<rightarrow> X) \<and> (f: X \<rightarrow> X))\<longrightarrow>
   (\<exists>!u. u: \<nat>\<^sub>c \<rightarrow> X \<and>
   triangle_commutes one \<nat>\<^sub>c X zero u q \<and>
   square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X u f successor u)"

lemma natural_number_object_func_unique:
  assumes u_type: "u : \<nat>\<^sub>c \<rightarrow> X" and v_type: "v : \<nat>\<^sub>c \<rightarrow> X" and f_type: "f: X \<rightarrow> X"
  assumes zeros_eq: "u \<circ>\<^sub>c zero = v \<circ>\<^sub>c zero"
  assumes u_successor_eq: "u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u"
  assumes v_successor_eq: "v \<circ>\<^sub>c successor = f \<circ>\<^sub>c v"
  shows "u = v"
proof -
  have u_zero_type: "u \<circ>\<^sub>c zero : one \<rightarrow> X"
    using u_type zero_type by auto
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
    using v_type zero_type by auto
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
    proof -
      have "triangle_commutes one \<nat>\<^sub>c \<nat>\<^sub>c zero (v \<circ>\<^sub>c u) zero"
        using u_type v_type comp_associative triangle_commutes_def by auto
      then show ?thesis
        by (metis (no_types) u_type v_type comp_associative square_commutes_def triangle_commutes_def)
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
      have "u \<circ>\<^sub>c v \<in> ETCS_func"
        using cfunc_type_def compatible_comp_ETCS_func u_type v_type by presburger
      then have "u \<circ>\<^sub>c v : N \<rightarrow> N"
        using cfunc_type_def codomain_comp domain_comp u_type v_type by presburger
      then show ?thesis
        by (metis comp_associative square_commutes_def triangle_commutes_def u_type v_type)
    qed
  then have half_isomorphism2: "(u \<circ>\<^sub>c v) = id(N)"
    using assms id_facts2 is_NNO_def z_and_s_type by blast
  then show "N \<cong> \<nat>\<^sub>c"
    by (metis codomain_comp domain_comp half_isomorphism id_codomain id_domain is_isomorphic_def isomorphic_is_symmetric isomorphism_def u_type)
qed

(* Converse to Exercise 2.6.5 *)
lemma Iso_to_N_is_NNO:
  assumes "N \<cong> \<nat>\<^sub>c"
  shows "\<exists> z s. is_NNO N z s"
proof - 
  obtain i where i_type: "i: N \<rightarrow> \<nat>\<^sub>c \<and> isomorphism(i)"
    using assms is_isomorphic_def by auto 
  obtain j where j_type: "j: \<nat>\<^sub>c \<rightarrow> N \<and> isomorphism(j) \<and> i \<circ>\<^sub>c j = id(\<nat>\<^sub>c) \<and> j \<circ>\<^sub>c i = id(N)"
    using cfunc_type_def compatible_comp_ETCS_func i_type id_ETCS_func isomorphism_def by fastforce
  obtain z where z_form: "z = j \<circ>\<^sub>c zero"
    by simp
  obtain s where s_form: "s = (j \<circ>\<^sub>c successor)  \<circ>\<^sub>c i"
    by simp
  have z_type: "z: one \<rightarrow> N"
    using j_type z_form zero_type by auto
  have s_type: "s: N \<rightarrow> N"
    using i_type j_type s_form successor_type by auto
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
      by (metis cfunc_type_def comp_associative id_left_unit j_type triangle_commutes_def u_properties v_Eqs_ui z_form)
    have D2_square: "v \<circ>\<^sub>c s = f \<circ>\<^sub>c v"
      by (metis cfunc_type_def comp_associative id_left_unit j_type s_form square_commutes_def u_properties v_Eqs_ui)
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
          using comp_associative  triangle_commutes_def w_triangle z_form zero_type by force
        then have fact3: "square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X (w \<circ>\<^sub>c j) f successor (w \<circ>\<^sub>c j)"
        proof -
          have "successor = successor \<circ>\<^sub>c i \<circ>\<^sub>c j"
            by (metis (no_types) cfunc_type_def id_right_unit j_type successor_type)
          then show ?thesis
            by (metis comp_associative f_type fact1 s_form square_commutes_def successor_type w_square)
        qed
        then have fact4: "(w \<circ>\<^sub>c j)\<circ>\<^sub>c successor = (f \<circ>\<^sub>c w) \<circ>\<^sub>c j"
          by (simp add: comp_associative square_commutes_def)
        then have wj_Eqs_u: "w \<circ>\<^sub>c j = u"
          using f_type fact1 fact2 fact3 natural_number_object_property q_type u_properties by blast
        then show "w = v"
          by (metis cfunc_type_def comp_associative id_right_unit j_type v_Eqs_ui w_type)
      qed
      then show "w = y"
        using w_square w_triangle w_type y_square y_triangle y_type by blast
    qed
    show "\<exists>u. u : N \<rightarrow> X \<and> triangle_commutes one N X z u q \<and> square_commutes N X N X u f s u"
      using D2_square D2_triangle f_type s_type square_commutes_def triangle_commutes_def v_type z_type by auto
  qed
  then show "\<exists>z s. is_NNO N z s"
    by auto
qed

lemma zero_is_not_successor:
  "\<not>(\<exists> x. (x \<in>\<^sub>c \<nat>\<^sub>c \<and> zero = successor \<circ>\<^sub>c x))"
  oops




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
    using cfunc_coprod_type coproj1 right_proj_type successor_type zero_type by auto
  have i1z_type: "i1 \<circ>\<^sub>c zero : one \<rightarrow>  one \<Coprod> \<nat>\<^sub>c"
    using coproj1 right_proj_type zero_type by auto
  obtain g where "(g: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)) \<and>
   (triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0) \<and>
   (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)))"
    by (metis coproj0 i1zUi1s_type left_proj_type natural_number_object_property square_commutes_def)
  then have second_diagram1: "g\<circ>\<^sub>c zero = i0"
    by (simp add: triangle_commutes_def)
  have second_diagram2: "g \<circ>\<^sub>c successor =   ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c g"
    using \<open>g : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0 \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> square_commutes_def by auto
  then have second_diagram3: "g \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)  = (i1 \<circ>\<^sub>c zero)"
    by (smt cfunc_coprod_comp comp_associative coproj0 coproj1 left_coproj_cfunc_coprod right_proj_type second_diagram1 successor_type zero_type)
  then have g_s_s_Eqs_i1zUi1s_g_s:
    "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (g \<circ>\<^sub>c successor)"
    by (metis comp_associative second_diagram2)
  then have g_s_s_zEqs_i1zUi1s_i1z: "((g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor)\<circ>\<^sub>c zero =
    ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (i1 \<circ>\<^sub>c zero)"
    by (metis comp_associative second_diagram3)
  then have i1_sEqs_i1zUi1s_i1: "i1 \<circ>\<^sub>c successor =
    ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c i1"
    by (metis comp_type coproj1 i1z_type right_coproj_cfunc_coprod right_proj_type successor_type)
  then obtain u where "(u: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)) \<and>
      (triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero u (i1 \<circ>\<^sub>c zero)) \<and>
      (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor u u ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)))"
    using coproj1 i1zUi1s_type right_proj_type square_commutes_def successor_type triangle_commutes_def zero_type by auto
  then have u_Eqs_i1: "u=i1"
    by (metis coproj1 i1_sEqs_i1zUi1s_i1 natural_number_object_property right_proj_type square_commutes_def triangle_commutes_def)
  then have g_s_type: "g\<circ>\<^sub>c successor: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)"
    using \<open>g : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0 \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> comp_type successor_type by blast
  then have g_s_triangle: 
  "triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero (g\<circ>\<^sub>c successor) ( (i1 \<circ>\<^sub>c zero))"
    using comp_associative i1z_type second_diagram3 triangle_commutes_def zero_type by auto
  then have g_s_square: 
"square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor  (g\<circ>\<^sub>c successor)  (g\<circ>\<^sub>c successor) ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))"
    by (simp add: g_s_s_Eqs_i1zUi1s_g_s g_s_type i1zUi1s_type square_commutes_def successor_type)
  then have u_Eqs_g_s: "u=(g\<circ>\<^sub>c successor)"
    by (metis \<open>u : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero u (i1 \<circ>\<^sub>c zero) \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor u u ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> g_s_triangle i1z_type natural_number_object_property square_commutes_def)
  then have g_sEqs_i1: "(g\<circ>\<^sub>c successor) = i1"
    using u_Eqs_i1 by blast
  then have "(zero \<amalg> successor) \<circ>\<^sub>c g = id(\<nat>\<^sub>c)"
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
        have f1: "\<forall>c ca cb. (c : ca \<rightarrow> cb) = (domain c = ca \<and> codomain c = cb \<and> c \<in> ETCS_func)"
           using cfunc_type_def by blast
        then have f2: "domain successor = \<nat>\<^sub>c \<and> codomain successor = \<nat>\<^sub>c \<and> successor \<in> ETCS_func"
           using successor_type by presburger
        have f3: "domain successor = \<nat>\<^sub>c \<and> codomain successor = \<nat>\<^sub>c \<and> successor \<in> ETCS_func"
           using f1 successor_type by presburger
        have f4: "\<forall>c ca. (c \<circ>\<^sub>c ca \<in> ETCS_func) = (domain c = codomain ca \<and> c \<in> ETCS_func \<and> ca \<in> ETCS_func)"
           using compatible_comp_ETCS_func by presburger
        have f5: "domain i1 = \<nat>\<^sub>c \<and> codomain i1 = one \<Coprod> \<nat>\<^sub>c \<and> i1 \<in> ETCS_func"
           using f1 g_sEqs_i1 g_s_type by presburger
        have "i1 \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c g = (i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor) \<circ>\<^sub>c g"
           using cfunc_coprod_comp comp_associative g_sEqs_i1 g_s_type successor_type zero_type by force
        then have "i1 \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c g = i1 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
           using f3 by (metis comp_associative g_sEqs_i1 id_right_unit second_diagram2)
        then show ?thesis
           using f5 f4 f2 by (metis comp_associative coproj1 monomorphism_def right_coproj_are_monomorphisms secondCenteredEqn)
    qed
  qed
  then have "g \<circ>\<^sub>c (zero \<amalg> successor) = id(one \<Coprod> \<nat>\<^sub>c)"
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
      by (metis \<open>g : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0 \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> cfunc_coprod_comp cfunc_coprod_unique cfunc_type_def coproj0 coproj1 g_sEqs_i1 g_s_type id_left_unit id_type left_proj_type second_diagram1 successor_type zero_type)
  qed
  then show "isomorphism(zero \<amalg> successor)"
    by (metis \<open>g \<circ>\<^sub>c zero \<amalg> successor = id\<^sub>c (one \<Coprod> \<nat>\<^sub>c)\<close> \<open>zero \<amalg> successor \<circ>\<^sub>c g = id\<^sub>c \<nat>\<^sub>c\<close> codomain_comp domain_comp id_codomain id_domain isomorphism_def)
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
    by (metis  cfunc_type_def compatible_comp_ETCS_func composition_of_monic_pair_is_monic i1_mono iso_imp_epi_and_monic oneUN_iso_N_isomorphism successor_type)
  have f_fact: "(\<f>\<circ>\<^sub>c\<beta>\<^bsub>\<Omega>\<^esub>): \<Omega> \<rightarrow> \<Omega>"
    using comp_type false_func_type terminal_func_type by blast
  then obtain u where u_form: "(u:  \<nat>\<^sub>c  \<rightarrow> \<Omega>) \<and>
   (triangle_commutes one  \<nat>\<^sub>c \<Omega> zero u \<t>) \<and>
   (square_commutes \<nat>\<^sub>c \<Omega> \<nat>\<^sub>c \<Omega> u (\<f>\<circ>\<^sub>c\<beta>\<^bsub>\<Omega>\<^esub>) successor u)"
    using natural_number_object_property true_func_type by blast
  have s_not_surj: "\<not>(surjective(successor))"
    proof (rule ccontr, auto)
      assume BWOC : "surjective(successor)"
      obtain n where snEqz: "successor \<circ>\<^sub>c n = zero"
        using BWOC cfunc_type_def successor_type surjective_def zero_type by auto
      have map_type: "\<beta>\<^bsub>\<Omega>\<^esub>\<circ>\<^sub>c (u\<circ>\<^sub>c n): one \<rightarrow> one"
       by (metis (mono_tags, lifting) cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp f_fact false_func_type snEqz successor_type u_form zero_type)
      then have uniqueness: "\<beta>\<^bsub>\<Omega>\<^esub>\<circ>\<^sub>c (u\<circ>\<^sub>c n) = id(one)"
       using id_type one_unique_element by blast
      have "\<t> = u \<circ>\<^sub>c zero"
       using triangle_commutes_def u_form by auto
      also have "... = u \<circ>\<^sub>c (successor \<circ>\<^sub>c n)"
       by (simp add: snEqz)
      also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>\<Omega>\<^esub>\<circ>\<^sub>c (u\<circ>\<^sub>c n))"
       using comp_associative square_commutes_def u_form by auto
      also have "... =\<f>"
        by (metis cfunc_type_def false_func_type id_right_unit uniqueness)
      then  have Contradiction: "\<t> = \<f>"
        by (simp add: calculation)
      then show False
        using true_false_distinct by auto
    qed
  then show "injective successor \<and> \<not> surjective successor"
    using monomorphism_imp_injective succ_mono by blast
qed

(* Definition 2.6.9 *)
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

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
    by (metis comp_monic_imp_monic delta_def diagonal_def id_isomorphism id_type iso_imp_epi_and_monic left_cart_proj_cfunc_prod)
  obtain \<chi>\<^sub>\<delta> where chi_delta_def: "is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> \<delta> \<chi>\<^sub>\<delta>"
    using \<delta>_mono \<delta>_type characteristic_function_exists by blast 
  have helpful_fact: "\<forall> x y. (x\<in>\<^sub>c X \<and> y\<in>\<^sub>c X \<longrightarrow> (x=y \<longleftrightarrow> \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>))"
  proof (auto)
    fix y 
    assume y_type: "y \<in>\<^sub>c X"
    have "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>y,y\<rangle> = \<chi>\<^sub>\<delta> \<circ>\<^sub>c (\<delta> \<circ>\<^sub>c y)"
      by (simp add: delta_def diag_on_elements y_type)
    also have "... =  \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c y)"
      using chi_delta_def comp_associative is_pullback_def square_commutes_def by auto
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
          by (smt cfunc_type_def chi_xxEq_t id_right_unit id_type is_pullback_def true_func_type xy_prod_type)
    then have "x = (left_cart_proj X X) \<circ>\<^sub>c \<langle>x,y\<rangle>"
          using left_cart_proj_cfunc_prod x_type y_type by auto
    also have "... = (left_cart_proj X X) \<circ>\<^sub>c (\<delta> \<circ>\<^sub>c k)"
          using k_type by auto
    also have "... = ((left_cart_proj X X) \<circ>\<^sub>c \<langle>id(X),id(X)\<rangle>) \<circ>\<^sub>c k"
          by (simp add: comp_associative delta_def diagonal_def)
    also have "... = id(X) \<circ>\<^sub>c k"
          by (metis id_type left_cart_proj_cfunc_prod)
    also have "... = y"
          by (metis calculation cfunc_prod_comp cfunc_type_def delta_def diagonal_def id_left_unit id_type k_type right_cart_proj_cfunc_prod y_type)
    then show "x = y"
         using calculation by blast
    qed
  
  have  \<chi>\<^sub>\<delta>sharp_type: "\<chi>\<^sub>\<delta>\<^sup>\<sharp> : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>"
      using chi_delta_def is_pullback_def square_commutes_def transpose_func_def by auto
  have \<chi>\<^sub>\<delta>sharp_injective: "injective(\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      unfolding injective_def
  proof (auto)
      fix x y 
      assume x_type: "x \<in>\<^sub>c domain (\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      assume y_type: "y \<in>\<^sub>c domain (\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      assume chixEqschiy: "\<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c x = \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c y"
      
      have "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,x\<rangle> = ((eval_func \<Omega> X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,x\<rangle>"
        using chi_delta_def is_pullback_def square_commutes_def transpose_func_def by auto
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,x\<rangle>)"
        by (simp add: comp_associative)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c x, \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c x\<rangle>"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_type x_type by auto
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c x, \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c y\<rangle>"
        using chixEqschiy by auto
      also have "... =  (eval_func \<Omega> X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,y\<rangle>)"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_type x_type y_type by auto
      also have "... = \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle>"
        using chi_delta_def comp_associative is_pullback_def square_commutes_def transpose_func_def by auto
      then have computation: "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,x\<rangle> = \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle>"
        by (simp add: calculation)
      then show "x=y"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_type_def helpful_fact x_type y_type by fastforce
    qed
  then show "(\<exists> f.((f : X \<rightarrow> \<P> X) \<and> injective(f)))"
    using \<chi>\<^sub>\<delta>sharp_type powerset_def by auto
qed

end