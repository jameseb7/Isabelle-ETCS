theory Nats
  imports Exponential_Objects
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
   q = u \<circ>\<^sub>c zero \<and>
   f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma beta_N_succ_nEqs_Id1:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n = id one"
  by (typecheck_cfuncs, simp add: terminal_func_comp_elem)

lemma natural_number_object_property2:
  assumes "q : one \<rightarrow> X" "f: X \<rightarrow> X"
  shows "\<exists>!u. u: \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = q \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
  using assms natural_number_object_property[where q=q, where f=f, where X=X]
  by metis

lemma natural_number_object_func_unique:
  assumes u_type: "u : \<nat>\<^sub>c \<rightarrow> X" and v_type: "v : \<nat>\<^sub>c \<rightarrow> X" and f_type: "f: X \<rightarrow> X"
  assumes zeros_eq: "u \<circ>\<^sub>c zero = v \<circ>\<^sub>c zero"
  assumes u_successor_eq: "u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u"
  assumes v_successor_eq: "v \<circ>\<^sub>c successor = f \<circ>\<^sub>c v"
  shows "u = v"
  by (smt (verit, best) comp_type f_type natural_number_object_property2 u_successor_eq u_type v_successor_eq v_type zero_type zeros_eq)

definition is_NNO :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool"  where
   "is_NNO Y z s \<longleftrightarrow>(z: one \<rightarrow> Y \<and> s: Y \<rightarrow> Y  \<and> (\<forall> X f q. ((q : one \<rightarrow> X) \<and> (f: X \<rightarrow> X))\<longrightarrow>
   (\<exists>!u. u: Y \<rightarrow> X \<and>
   q = u \<circ>\<^sub>c z \<and>
   f \<circ>\<^sub>c u = u \<circ>\<^sub>c s)))"

lemma N_is_a_NNO:
    "is_NNO \<nat>\<^sub>c zero successor"
by (simp add: is_NNO_def natural_number_object_property successor_type zero_type)

text \<open>The lemma below corresponds to Exercise 2.6.5 in Halvorson\<close>
lemma NNOs_are_iso_N:
  assumes "is_NNO N z s"
  shows "N \<cong> \<nat>\<^sub>c"
proof-
  have z_type[type_rule]: "(z : one \<rightarrow>  N)" 
    using assms is_NNO_def by blast
  have s_type[type_rule]: "(s : N \<rightarrow>  N)"
    using assms is_NNO_def by blast 
  then obtain u where u_type[type_rule]: "u: \<nat>\<^sub>c \<rightarrow> N" 
                 and  u_triangle: "u \<circ>\<^sub>c zero = z" 
                 and  u_square: "s \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    using natural_number_object_property z_type by blast
  obtain v where v_type[type_rule]: "v: N \<rightarrow> \<nat>\<^sub>c" 
                 and  v_triangle: "v \<circ>\<^sub>c z = zero" 
                 and  v_square: "successor \<circ>\<^sub>c v = v \<circ>\<^sub>c s"
    by (metis assms is_NNO_def successor_type zero_type)
  then have vuzeroEqzero: "v \<circ>\<^sub>c (u \<circ>\<^sub>c zero) = zero"
    by (simp add: u_triangle v_triangle)
  have id_facts1: "id(\<nat>\<^sub>c): \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<and> id(\<nat>\<^sub>c) \<circ>\<^sub>c zero = zero \<and>
          (successor \<circ>\<^sub>c id(\<nat>\<^sub>c) = id(\<nat>\<^sub>c) \<circ>\<^sub>c successor)"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  then have vu_facts: "v \<circ>\<^sub>c u: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<and> (v \<circ>\<^sub>c u) \<circ>\<^sub>c zero = zero \<and> 
          successor \<circ>\<^sub>c (v \<circ>\<^sub>c u) = (v \<circ>\<^sub>c u) \<circ>\<^sub>c successor"
    by (typecheck_cfuncs, smt (verit, best) comp_associative2 s_type u_square v_square vuzeroEqzero)
  then have half_isomorphism: "(v \<circ>\<^sub>c u) = id(\<nat>\<^sub>c)"
    by (metis id_facts1 natural_number_object_property successor_type vu_facts zero_type)
  have uvzEqz: "u \<circ>\<^sub>c (v \<circ>\<^sub>c z) = z"
    by (simp add: u_triangle v_triangle)
  have id_facts2: "id(N): N \<rightarrow> N \<and> id(N) \<circ>\<^sub>c z = z \<and> s \<circ>\<^sub>c id(N) = id(N) \<circ>\<^sub>c  s"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  then have uv_facts: "u \<circ>\<^sub>c v: N \<rightarrow> N \<and>
          (u \<circ>\<^sub>c v) \<circ>\<^sub>c  z = z \<and>  s \<circ>\<^sub>c (u \<circ>\<^sub>c v) =  (u \<circ>\<^sub>c v) \<circ>\<^sub>c s"
    by (typecheck_cfuncs, smt (verit, best) comp_associative2 successor_type u_square uvzEqz v_square)
 then have half_isomorphism2: "(u \<circ>\<^sub>c v) = id(N)"
   by (smt (verit, ccfv_threshold) assms id_facts2 is_NNO_def)
  then show "N \<cong> \<nat>\<^sub>c"
    using cfunc_type_def half_isomorphism is_isomorphic_def isomorphism_def u_type v_type by fastforce
qed

text \<open>The lemma below is the converse to Exercise 2.6.5 in Halvorson\<close>
lemma Iso_to_N_is_NNO:
  assumes "N \<cong> \<nat>\<^sub>c"
  shows "\<exists> z s. is_NNO N z s"
proof - 
  obtain i where i_type[type_rule]: "i: \<nat>\<^sub>c \<rightarrow> N" and i_iso: "isomorphism(i)"
    using assms isomorphic_is_symmetric is_isomorphic_def by blast 
  obtain z where z_type[type_rule]: "z \<in>\<^sub>c N" and z_def: "z = i \<circ>\<^sub>c zero"
    by typecheck_cfuncs
  obtain s where s_type[type_rule]: "s: N \<rightarrow> N" and s_def: "s = (i \<circ>\<^sub>c successor) \<circ>\<^sub>c i\<^bold>\<inverse>"
    using i_iso by typecheck_cfuncs
  have "is_NNO N z s"
  proof(unfold is_NNO_def, typecheck_cfuncs, clarify)
    fix X q f 
    assume q_type[type_rule]: "q: one \<rightarrow> X"
    assume f_type[type_rule]: "f:   X \<rightarrow> X"

    obtain u where u_type[type_rule]: "u: \<nat>\<^sub>c \<rightarrow> X" and u_def:  "u \<circ>\<^sub>c zero =  q \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
      using natural_number_object_property2 by (typecheck_cfuncs, blast)
    obtain v where v_type[type_rule]: "v: N \<rightarrow> X" and v_def: "v = u \<circ>\<^sub>c i\<^bold>\<inverse>"
      using i_iso by typecheck_cfuncs
    then have bottom_triangle: "v \<circ>\<^sub>c z = q"
      unfolding v_def u_def z_def using i_iso
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative id_right_unit2 inv_left u_def)
    have bottom_square: "v \<circ>\<^sub>c s = f \<circ>\<^sub>c v"
      unfolding v_def u_def s_def using i_iso
      by (typecheck_cfuncs, smt (verit, ccfv_SIG) comp_associative2 id_right_unit2 inv_left u_def)
    show "\<exists>!u. u : N \<rightarrow> X \<and> q = u \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c s"
    proof auto
      show "\<exists>u. u : N \<rightarrow> X \<and> q = u \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c s"
        by (rule_tac x=v in exI, auto simp add: bottom_triangle bottom_square v_type)
    next
      fix w y
      assume w_type[type_rule]: "w : N \<rightarrow> X"
      assume y_type[type_rule]: "y : N \<rightarrow> X"
      assume w_y_z: "w \<circ>\<^sub>c z = y \<circ>\<^sub>c z"
      assume q_def: "q = y \<circ>\<^sub>c z"
      assume f_w: "f \<circ>\<^sub>c w = w \<circ>\<^sub>c s"
      assume f_y: "f \<circ>\<^sub>c y = y \<circ>\<^sub>c s"

      have "w \<circ>\<^sub>c i = u"
      proof (etcs_rule natural_number_object_func_unique[where f=f])
        show "(w \<circ>\<^sub>c i) \<circ>\<^sub>c zero = u \<circ>\<^sub>c zero"
          using q_def u_def w_y_z z_def by (etcs_assocr, argo)
        show "(w \<circ>\<^sub>c i) \<circ>\<^sub>c successor = f \<circ>\<^sub>c w \<circ>\<^sub>c i"
          using i_iso by (typecheck_cfuncs, smt (verit, best) comp_associative2 comp_type f_w id_right_unit2 inv_left inverse_type s_def)
        show "u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u"
          by (simp add: u_def)
      qed
      then have w_eq_v: "w = v"
        unfolding v_def using i_iso
        by (typecheck_cfuncs, smt (verit, best) comp_associative2 id_right_unit2 inv_right)

      have "y \<circ>\<^sub>c i = u"
      proof (etcs_rule natural_number_object_func_unique[where f=f])
        show "(y \<circ>\<^sub>c i) \<circ>\<^sub>c zero = u \<circ>\<^sub>c zero"
          using q_def u_def w_y_z z_def by (etcs_assocr, argo)
        show "(y \<circ>\<^sub>c i) \<circ>\<^sub>c successor = f \<circ>\<^sub>c y \<circ>\<^sub>c i"
          using i_iso by (typecheck_cfuncs, smt (verit, best) comp_associative2 comp_type f_y id_right_unit2 inv_left inverse_type s_def)
        show "u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u"
          by (simp add: u_def)
      qed
      then have y_eq_v: "y = v"
        unfolding v_def using i_iso
        by (typecheck_cfuncs, smt (verit, best) comp_associative2 id_right_unit2 inv_right)
      show "w = y"
        using w_eq_v y_eq_v by auto
    qed
  qed
  then show ?thesis
    by auto
qed

section \<open>Cardinality and Finiteness\<close>

text \<open>The definitions below correspond to Definition 2.6.1 in Halvorson\<close>
definition is_finite :: "cset \<Rightarrow> bool"  where
   "is_finite(X) \<longleftrightarrow> (\<forall>m. (m : X \<rightarrow> X \<and> monomorphism(m)) \<longrightarrow>  isomorphism(m))"

definition is_infinite :: "cset \<Rightarrow> bool"  where
   "is_infinite(X) \<longleftrightarrow> (\<exists> m. (m : X \<rightarrow> X \<and> monomorphism(m) \<and> \<not>surjective(m)))"

lemma either_finite_or_infinite:
  "is_finite(X) \<or> is_infinite(X)"
  using epi_mon_is_iso is_finite_def is_infinite_def surjective_is_epimorphism by blast

text \<open>The definition below corresponds to Definition 2.6.2 in Halvorson\<close>
definition is_smaller_than :: "cset \<Rightarrow> cset \<Rightarrow> bool" (infix "\<le>\<^sub>c" 50) where
   "X \<le>\<^sub>c Y \<longleftrightarrow> (\<exists> m. m : X \<rightarrow> Y \<and> monomorphism(m))"

text \<open>The purpose of the following lemma is simply to unify the two notations used in the book.\<close>
lemma subobject_iff_smaller_than:
  "(X \<le>\<^sub>c Y) = (\<exists>m. (X,m) \<subseteq>\<^sub>c Y)"
  using is_smaller_than_def subobject_of_def2 by auto

lemma set_card_transitive:
  assumes "A \<le>\<^sub>c B"
  assumes "B \<le>\<^sub>c C"
  shows   "A \<le>\<^sub>c C"
  by (typecheck_cfuncs, metis (full_types) assms cfunc_type_def comp_type composition_of_monic_pair_is_monic is_smaller_than_def)

lemma all_emptysets_are_finite:
  assumes "is_empty X"
  shows "is_finite(X)"
  by (metis assms epi_mon_is_iso epimorphism_def3 is_finite_def is_empty_def one_separator)

lemma emptyset_is_smallest_set:
  "\<emptyset> \<le>\<^sub>c X"
  using empty_subset is_smaller_than_def subobject_of_def2 by auto

lemma truth_set_is_finite:
  "is_finite \<Omega>"
  unfolding is_finite_def
proof(auto)
  fix m 
  assume m_type[type_rule]: "m : \<Omega> \<rightarrow> \<Omega>"
  assume m_mono: "monomorphism(m)"
  have "surjective(m)"
    unfolding surjective_def
  proof(auto)
    fix y
    assume "y \<in>\<^sub>c codomain m" 
    then have "y \<in>\<^sub>c \<Omega>"
      using cfunc_type_def m_type by force
    show "\<exists>x. x \<in>\<^sub>c domain m \<and> m \<circ>\<^sub>c x = y"
      by (smt (verit, del_insts) \<open>y \<in>\<^sub>c \<Omega>\<close> cfunc_type_def codomain_comp domain_comp injective_def m_mono m_type monomorphism_imp_injective true_false_only_truth_values)
  qed
  then show "isomorphism m"
    by (simp add: epi_mon_is_iso m_mono surjective_is_epimorphism)
qed

lemma smaller_than_finite_is_finite:
  assumes "X \<le>\<^sub>c Y" "is_finite Y" 
  shows "is_finite X"
  unfolding is_finite_def
proof(auto)
  fix x
  assume x_type: "x : X \<rightarrow> X"
  assume x_mono: "monomorphism x"

  obtain m where m_def: "m: X \<rightarrow> Y \<and> monomorphism m"
    using assms(1) is_smaller_than_def by blast
  obtain \<phi> where \<phi>_def: "\<phi> = into_super m \<circ>\<^sub>c (x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c try_cast m" 
    by auto

  have \<phi>_type: "\<phi> : Y \<rightarrow> Y"
    unfolding \<phi>_def
    using x_type m_def by (typecheck_cfuncs, blast)

  have "injective(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using cfunc_bowtieprod_inj id_isomorphism id_type iso_imp_epi_and_monic monomorphism_imp_injective x_mono x_type by blast
  then have mono1: "monomorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using injective_imp_monomorphism by auto
  have mono2: "monomorphism(try_cast m)"
    using m_def try_cast_mono by blast
  have mono3: "monomorphism((x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c try_cast m)"
    using cfunc_type_def composition_of_monic_pair_is_monic m_def mono1 mono2 x_type by (typecheck_cfuncs, auto)
  then have \<phi>_mono: "monomorphism(\<phi>)" 
    unfolding \<phi>_def
    using cfunc_type_def composition_of_monic_pair_is_monic 
          into_super_mono m_def mono3 x_type by (typecheck_cfuncs,auto)
  then have "isomorphism(\<phi>)" 
    using \<phi>_def \<phi>_type assms(2) is_finite_def by blast
  have iso_x_bowtie_id: "isomorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    by (typecheck_cfuncs, smt \<open>isomorphism \<phi>\<close> \<phi>_def comp_associative2 id_left_unit2 into_super_iso into_super_try_cast into_super_type isomorphism_sandwich m_def try_cast_type x_type)
  have "left_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x = (x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c left_coproj X (Y \<setminus> (X,m))"
    using x_type  
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_bowtie_prod)
  have "epimorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using iso_imp_epi_and_monic iso_x_bowtie_id by blast
  then have "surjective(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using  epi_is_surj x_type by (typecheck_cfuncs, blast)
  then have "epimorphism(x)"
    using x_type cfunc_bowtieprod_surj_converse id_type surjective_is_epimorphism by blast
  then show "isomorphism(x)"
    by (simp add: epi_mon_is_iso x_mono)
qed

lemma larger_than_infinite_is_infinite:
  assumes "X \<le>\<^sub>c Y" "is_infinite(X)" 
  shows "is_infinite(Y)"
  using assms either_finite_or_infinite epi_is_surj is_finite_def is_infinite_def
    iso_imp_epi_and_monic smaller_than_finite_is_finite by blast

text \<open>The next two lemmas below correspond to Proposition 2.6.3 in Halvorson\<close>
lemma smaller_than_coproduct1:
  "X \<le>\<^sub>c X \<Coprod> Y"
  using is_smaller_than_def left_coproj_are_monomorphisms left_proj_type by blast

lemma  smaller_than_coproduct2:
  "X \<le>\<^sub>c Y \<Coprod> X"
  using is_smaller_than_def right_coproj_are_monomorphisms right_proj_type by blast

text \<open>The next two lemmas below correspond to Proposition 2.6.4 in Halvorson\<close>
lemma smaller_than_product1:
  assumes "nonempty Y"
  shows "X \<le>\<^sub>c X \<times>\<^sub>c Y"
  unfolding is_smaller_than_def  
proof-
  obtain y where y_type: "y \<in>\<^sub>c Y"
  using assms nonempty_def by blast
  have map_type: "\<langle>id(X),y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c Y"
   using y_type cfunc_prod_type cfunc_type_def codomain_comp domain_comp id_type terminal_func_type by auto
  have mono: "monomorphism(\<langle>id X, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"
    using map_type
  proof (unfold monomorphism_def3, auto)
    fix g h A
    assume g_h_types: "g : A \<rightarrow> X" "h : A \<rightarrow> X"
    
    assume "\<langle>id\<^sub>c X,y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g = \<langle>id\<^sub>c X,y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c h"
    then have "\<langle>id\<^sub>c X \<circ>\<^sub>c g, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g\<rangle>  = \<langle>id\<^sub>c X \<circ>\<^sub>c h, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h\<rangle>"
      using y_type g_h_types by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 comp_type)
    then have "\<langle>g, y \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>\<rangle>  = \<langle>h, y \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>\<rangle>"
      using y_type g_h_types id_left_unit2 terminal_func_comp by (typecheck_cfuncs, auto)
    then show "g = h"
      using g_h_types y_type
      by (metis (full_types) comp_type left_cart_proj_cfunc_prod terminal_func_type)
  qed

  show "\<exists>m. m : X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism m"
    using mono map_type by auto
qed

lemma smaller_than_product2:
  assumes "nonempty Y"
  shows "X \<le>\<^sub>c Y \<times>\<^sub>c X"
  unfolding is_smaller_than_def  
proof - 
  have "X \<le>\<^sub>c X \<times>\<^sub>c Y"
    by (simp add: assms smaller_than_product1)
  then obtain m where m_def: "m : X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism m"
    using is_smaller_than_def by blast
  obtain i  where "i : (X \<times>\<^sub>c Y) \<rightarrow> (Y \<times>\<^sub>c X) \<and> isomorphism i"
    using is_isomorphic_def product_commutes by blast
  then have "i \<circ>\<^sub>c m : X \<rightarrow>  (Y \<times>\<^sub>c X) \<and> monomorphism(i \<circ>\<^sub>c m)"
    using cfunc_type_def comp_type composition_of_monic_pair_is_monic iso_imp_epi_and_monic m_def by auto
  then show "\<exists>m. m : X \<rightarrow> Y \<times>\<^sub>c X \<and> monomorphism m"
    by blast
qed

lemma Y_nonempty_then_X_le_XtoY:
  assumes "nonempty Y"
  shows "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
proof - 
  obtain f where f_def: "f = (right_cart_proj Y X)\<^sup>\<sharp>"
    by blast
  then have f_type: "f : X \<rightarrow> X\<^bsup>Y\<^esup>"
    by (simp add: right_cart_proj_type transpose_func_type)
  have mono_f: "injective(f)"
    unfolding injective_def
  proof(auto)
    fix x y 
    assume x_type: "x \<in>\<^sub>c domain f"
    assume y_type: "y \<in>\<^sub>c domain f"
    assume equals: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    have x_type2 : "x \<in>\<^sub>c X"
      using cfunc_type_def f_type x_type by auto
    have y_type2 : "y \<in>\<^sub>c X"
      using cfunc_type_def f_type y_type by auto
    have "x \<circ>\<^sub>c (right_cart_proj Y one) = (right_cart_proj Y X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      using right_cart_proj_cfunc_cross_prod x_type2 by (typecheck_cfuncs, auto)
    also have "... = ((eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    also have "... = (eval_func X Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x))"
      using comp_associative2 f_type x_type2 by (typecheck_cfuncs, fastforce)
    also have "... = (eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c x))"
      using f_type identity_distributes_across_composition x_type2 by auto
    also have "... = (eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c y))"
      by (simp add: equals)
    also have "... = (eval_func X Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y))"
      using f_type identity_distributes_across_composition y_type2 by auto
    also have "... = ((eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      using comp_associative2 f_type y_type2 by (typecheck_cfuncs, fastforce)
    also have "... = (right_cart_proj Y X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    also have "... = y \<circ>\<^sub>c (right_cart_proj Y one)"
      using right_cart_proj_cfunc_cross_prod y_type2 by (typecheck_cfuncs, auto)
    then show "x = y"
      using  assms calculation epimorphism_def3 nonempty_left_imp_right_proj_epimorphism right_cart_proj_type x_type2 y_type2 by fastforce
  qed
  then show "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
    using f_type injective_imp_monomorphism is_smaller_than_def by blast
qed





lemma non_init_non_ter_sets:
  assumes "\<not>(terminal_object X)"
  assumes "\<not>(initial_object X)"
  shows "\<Omega> \<le>\<^sub>c X" 
proof - 
  obtain x1 and x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and 
                         x2_type[type_rule]: "x2 \<in>\<^sub>c X" and
                                   distinct: "x1 \<noteq> x2"
    using is_empty_def assms iso_empty_initial iso_to1_is_term no_el_iff_iso_empty single_elem_iso_one by blast


    then have map_type: "(x1 \<amalg> x2) \<circ>\<^sub>c case_bool   : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have injective: "injective((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
  proof(unfold injective_def, auto)
    fix \<omega>1 \<omega>2 
    assume "\<omega>1 \<in>\<^sub>c domain (x1 \<amalg> x2 \<circ>\<^sub>c case_bool)"
    then have \<omega>1_type[type_rule]: "\<omega>1 \<in>\<^sub>c \<Omega>"
      using cfunc_type_def map_type by auto
    assume "\<omega>2 \<in>\<^sub>c domain (x1 \<amalg> x2 \<circ>\<^sub>c case_bool)"
    then have \<omega>2_type[type_rule]: "\<omega>2 \<in>\<^sub>c \<Omega>"
      using cfunc_type_def map_type by auto
    
    assume equals: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = (x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2"
    show "\<omega>1 = \<omega>2"
    proof(cases "\<omega>1 = \<t>", auto)
      assume "\<omega>1 = \<t>"
      show "\<t> = \<omega>2"
      proof(rule ccontr)
        assume " \<t> \<noteq> \<omega>2"
        then have "\<f> = \<omega>2"
          using \<open>\<t> \<noteq> \<omega>2\<close> true_false_only_truth_values by (typecheck_cfuncs, blast)
        then have RHS: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x2"
          by (meson coprod_case_bool_false x1_type x2_type)
        have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x1"
          using \<open>\<omega>1 = \<t>\<close> coprod_case_bool_true x1_type x2_type by blast
        then show False
          using RHS distinct equals by force
      qed
    next
      assume "\<omega>1 \<noteq> \<t>"
      then have "\<omega>1 = \<f>"
        using  true_false_only_truth_values by (typecheck_cfuncs, blast)
      have "\<omega>2 = \<f>"
      proof(rule ccontr)
        assume "\<omega>2 \<noteq> \<f>"
        then have "\<omega>2 = \<t>"
          using  true_false_only_truth_values by (typecheck_cfuncs, blast)
        then have RHS: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x2"
          using \<open>\<omega>1 = \<f>\<close> coprod_case_bool_false equals x1_type x2_type by auto
        have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x1"
          using \<open>\<omega>2 = \<t>\<close> coprod_case_bool_true equals x1_type x2_type by presburger
        then show False
          using RHS distinct equals by auto
      qed
      show "\<omega>1 = \<omega>2"
        by (simp add: \<open>\<omega>1 = \<f>\<close> \<open>\<omega>2 = \<f>\<close>)
    qed
  qed
  then have "monomorphism((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    using injective_imp_monomorphism by auto
  then show "\<Omega> \<le>\<^sub>c X"
    using  is_smaller_than_def map_type by blast
qed

lemma exp_preserves_card1:
  assumes "A \<le>\<^sub>c B"
  assumes "nonempty X"   
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
proof (unfold is_smaller_than_def)

  obtain x where x_type[type_rule]: "x \<in>\<^sub>c X"
    using assms(2) unfolding nonempty_def by auto

  obtain m where m_def[type_rule]: "m : A \<rightarrow> B" "monomorphism m"
    using assms(1) unfolding is_smaller_than_def by auto

  show "\<exists>m. m : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup> \<and> monomorphism m"
  proof (rule_tac x="(((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>))
    \<circ>\<^sub>c dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) 
    \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id (X\<^bsup>A\<^esup>)))\<^sup>\<sharp>" in exI, auto)

    show "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup>"
      by  typecheck_cfuncs
    then show "monomorphism
      (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
        dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
        swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)"
    proof (unfold monomorphism_def3, auto)
      fix g h Z
      assume g_type[type_rule]: "g : Z \<rightarrow> X\<^bsup>A\<^esup>"
      assume h_type[type_rule]: "h : Z \<rightarrow> X\<^bsup>A\<^esup>"
      assume eq: "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
          dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
          swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c g
        =
          ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
          dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
          swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h"

      show "g = h"
      proof (typecheck_cfuncs, rule_tac same_evals_equal[where Z=Z, where A=A, where X=X], auto)
        show "eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f h"
        proof (typecheck_cfuncs, rule one_separator[where X="A \<times>\<^sub>c Z", where Y="X"], auto)
          fix az
          assume az_type[type_rule]: "az \<in>\<^sub>c A \<times>\<^sub>c Z"

          obtain a z where az_types[type_rule]: "a \<in>\<^sub>c A" "z \<in>\<^sub>c Z" and az_def: "az = \<langle>a,z\<rangle>"
            using cart_prod_decomp az_type by blast

          have "(eval_func X B) \<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c g)) = 
          (eval_func X B) \<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h))"
            using eq by simp
          then have "(eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) = 
          (eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            using identity_distributes_across_composition by (typecheck_cfuncs, auto)
          then have "((eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>))) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) = 
          ((eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>))) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            by (typecheck_cfuncs, smt eq inv_transpose_func_def3 inv_transpose_of_composition)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g)
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            using   transpose_func_def by (typecheck_cfuncs,auto)
          then have "(((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>
          = (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>"
            by auto
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>"
            by (typecheck_cfuncs, auto simp add: comp_associative2)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs_prems, smt comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>try_cast m \<circ>\<^sub>c m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>try_cast m \<circ>\<^sub>c m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs_prems, smt)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>(try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>(try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs, auto simp add: comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            using m_def(2) try_cast_m_m by (typecheck_cfuncs, auto)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_inv (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z, left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a\<rangle>"
            using swap_ap by (typecheck_cfuncs, auto)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m))) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m))) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            using dist_prod_coprod_inv_left_ap by (typecheck_cfuncs, auto)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m)))) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m)))) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
            = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: left_coproj_cfunc_coprod)
          then have "eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
            = eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
          then have "eval_func X A \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c z\<rangle> = eval_func X A \<circ>\<^sub>c \<langle>a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: swap_ap)
          then have "eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, z\<rangle> = eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>a, z\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          then show "(eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f g) \<circ>\<^sub>c az = (eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f h) \<circ>\<^sub>c az"
            unfolding az_def by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
        qed
      qed
    qed
  qed
qed

lemma exp_preserves_card2:
  assumes "A \<le>\<^sub>c B"
  shows "A\<^bsup>X\<^esup> \<le>\<^sub>c B\<^bsup>X\<^esup>"
proof (unfold is_smaller_than_def)
  obtain m where m_def[type_rule]: "m : A \<rightarrow> B" "monomorphism m"
        using assms unfolding is_smaller_than_def by auto
  show "\<exists>m. m : A\<^bsup>X\<^esup> \<rightarrow> B\<^bsup>X\<^esup> \<and> monomorphism m"
  proof (rule_tac x="(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>" in exI, auto)
    show "(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> : A\<^bsup>X\<^esup> \<rightarrow> B\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    then show "monomorphism((m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)"
    proof (unfold monomorphism_def3, auto)
      fix g h Z
      assume g_type[type_rule]: "g : Z \<rightarrow> A\<^bsup>X\<^esup>"
      assume h_type[type_rule]: "h : Z \<rightarrow> A\<^bsup>X\<^esup>"

      assume eq: "(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c g = (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c h"
      show "g = h"
      proof (typecheck_cfuncs, rule_tac same_evals_equal[where Z=Z, where A=X, where X=A], auto)
          have "((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = 
                ((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            by (typecheck_cfuncs, smt comp_associative2 eq inv_transpose_func_def3 inv_transpose_of_composition)
          then have "(m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = (m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            by (smt comp_type eval_func_type m_def(1) transpose_func_def)
          then have "m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g))  = m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h))"
            by (typecheck_cfuncs, smt comp_associative2)
          then have "eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            using m_def monomorphism_def3 by (typecheck_cfuncs, blast)
          then show "(eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g))  = (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h))"
            by (typecheck_cfuncs, smt comp_associative2)
      qed
    qed
  qed
qed

lemma exp_preserves_card3:
  assumes "A \<le>\<^sub>c B"
  assumes "X \<le>\<^sub>c Y"
  assumes "nonempty(X)"
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
proof - 
  have leq1: "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
    by (simp add: assms(1,3) exp_preserves_card1)    
  have leq2: "X\<^bsup>B\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    by (simp add: assms(2) exp_preserves_card2)
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    using leq1 leq2 set_card_transitive by blast
qed

section \<open>Zero and Successor\<close>

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
      using assms u_type by (etcs_assocr,typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
    then show ?thesis using calculation by auto
  qed
  then show False
    using true_false_distinct by blast
qed

text \<open>The lemma below corresponds to Proposition 2.6.6 in Halvorson\<close>
lemma oneUN_iso_N_isomorphism:
 "isomorphism(zero \<amalg> successor)" 
proof - 
  obtain i0 where i0_type[type_rule]:  "i0: one \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)" and i0_def: "i0 = left_coproj one \<nat>\<^sub>c"
    by typecheck_cfuncs
  obtain i1 where i1_type[type_rule]:  "i1: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)" and i1_def: "i1 = right_coproj one \<nat>\<^sub>c"
    by typecheck_cfuncs
  obtain g where g_type[type_rule]: "g: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)" and
   g_triangle: " g \<circ>\<^sub>c zero = i0" and
   g_square: "g \<circ>\<^sub>c successor = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c g"
    by (typecheck_cfuncs, metis natural_number_object_property)
  then have second_diagram3: "g \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)  = (i1 \<circ>\<^sub>c zero)"
    by (typecheck_cfuncs, smt (verit, best) cfunc_coprod_type comp_associative2 comp_type i0_def left_coproj_cfunc_coprod)
  then have g_s_s_Eqs_i1zUi1s_g_s:
    "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (g \<circ>\<^sub>c successor)"
    by (typecheck_cfuncs, smt (verit, del_insts) comp_associative2 g_square)
  then have g_s_s_zEqs_i1zUi1s_i1z: "((g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor)\<circ>\<^sub>c zero =
    ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (i1 \<circ>\<^sub>c zero)"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) comp_associative2 g_square second_diagram3)
  then have i1_sEqs_i1zUi1s_i1: "i1 \<circ>\<^sub>c successor = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c i1"
    by (typecheck_cfuncs, simp add: i1_def right_coproj_cfunc_coprod)   
  then obtain u where u_type[type_rule]: "(u: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c))" and
      u_triangle: "u \<circ>\<^sub>c zero = i1 \<circ>\<^sub>c zero" and
      u_square: "u \<circ>\<^sub>c successor =  ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c u "
    using i1_sEqs_i1zUi1s_i1 by (typecheck_cfuncs, blast)    
  then have u_Eqs_i1: "u=i1"
    by (typecheck_cfuncs, meson cfunc_coprod_type comp_type i1_sEqs_i1zUi1s_i1 natural_number_object_func_unique successor_type zero_type)
  have g_s_type[type_rule]: "g \<circ>\<^sub>c successor: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)"
    by typecheck_cfuncs
  have g_s_triangle: "(g\<circ>\<^sub>c successor) \<circ>\<^sub>c zero = i1 \<circ>\<^sub>c zero"
    using comp_associative2 second_diagram3 by (typecheck_cfuncs, force)
  then have u_Eqs_g_s: "u= g\<circ>\<^sub>c successor"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_coprod_type comp_type g_s_s_Eqs_i1zUi1s_g_s g_s_triangle i1_sEqs_i1zUi1s_i1 natural_number_object_func_unique u_Eqs_i1 zero_type)
  then have g_sEqs_i1: "g\<circ>\<^sub>c successor = i1"
    using u_Eqs_i1 by blast
  have eq1: "(zero \<amalg> successor) \<circ>\<^sub>c g = id(\<nat>\<^sub>c)"
    by (typecheck_cfuncs, smt (verit, best) cfunc_coprod_comp comp_associative2 g_square g_triangle i0_def i1_def i1_type id_left_unit2 id_right_unit2 left_coproj_cfunc_coprod natural_number_object_func_unique right_coproj_cfunc_coprod)
  then have eq2: "g \<circ>\<^sub>c (zero \<amalg> successor) = id(one \<Coprod> \<nat>\<^sub>c)"
    by (typecheck_cfuncs, metis cfunc_coprod_comp g_sEqs_i1 g_triangle i0_def i1_def id_coprod)
  show "isomorphism(zero \<amalg> successor)"
    using cfunc_coprod_type eq1 eq2 g_type isomorphism_def3 successor_type zero_type by blast
qed

lemma zUs_epic:
 "epimorphism(zero \<amalg> successor)"
  by (simp add: iso_imp_epi_and_monic oneUN_iso_N_isomorphism)

lemma zUs_surj:
 "surjective(zero \<amalg> successor)"
  by (simp add: cfunc_type_def epi_is_surj zUs_epic)

lemma nonzero_is_succ_aux:
  assumes "x \<in>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)"
  shows "(x = (left_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c id one) \<or>
         (\<exists>n. (n \<in>\<^sub>c \<nat>\<^sub>c) \<and> (x = (right_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c n))"
proof auto
  assume "\<forall> n. n \<in>\<^sub>c  \<nat>\<^sub>c  \<longrightarrow>  x \<noteq> right_coproj one \<nat>\<^sub>c \<circ>\<^sub>c n"
  then show "x = left_coproj one \<nat>\<^sub>c \<circ>\<^sub>c id one"
    using assms coprojs_jointly_surj one_unique_element by (typecheck_cfuncs, blast)
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
  have cases: "(x = (left_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c id one) \<or> 
                (\<exists>n. (n \<in>\<^sub>c \<nat>\<^sub>c \<and> x = (right_coproj one \<nat>\<^sub>c) \<circ>\<^sub>c n))"
    by (simp add: nonzero_is_succ_aux x_def)
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

section \<open>Predecessor\<close>

definition predecessor :: "cfunc" where
  "predecessor = (THE f. f : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c 
    \<and> f \<circ>\<^sub>c (zero \<amalg> successor) = id (one \<Coprod> \<nat>\<^sub>c) \<and>  (zero \<amalg> successor) \<circ>\<^sub>c f = id \<nat>\<^sub>c)"

lemma predecessor_def2:
  "predecessor : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> predecessor \<circ>\<^sub>c (zero \<amalg> successor) = id (one \<Coprod> \<nat>\<^sub>c)
    \<and> (zero \<amalg> successor) \<circ>\<^sub>c predecessor = id \<nat>\<^sub>c"
proof (unfold predecessor_def, rule theI', auto)
  show "\<exists>x. x : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and>
        x \<circ>\<^sub>c zero \<amalg> successor = id\<^sub>c (one \<Coprod> \<nat>\<^sub>c) \<and> zero \<amalg> successor \<circ>\<^sub>c x = id\<^sub>c \<nat>\<^sub>c"
    using oneUN_iso_N_isomorphism by (typecheck_cfuncs, unfold isomorphism_def cfunc_type_def, auto)
next
  fix x y
  assume x_type[type_rule]: "x : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c" and y_type[type_rule]: "y : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c"
  assume x_left_inv: "zero \<amalg> successor \<circ>\<^sub>c x = id\<^sub>c \<nat>\<^sub>c"
  assume "x \<circ>\<^sub>c zero \<amalg> successor = id\<^sub>c (one \<Coprod> \<nat>\<^sub>c)" "y \<circ>\<^sub>c zero \<amalg> successor = id\<^sub>c (one \<Coprod> \<nat>\<^sub>c)"
  then have "x \<circ>\<^sub>c zero \<amalg> successor = y \<circ>\<^sub>c zero \<amalg> successor"
    by auto
  then have "x \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c x = y \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c x"
    by (typecheck_cfuncs, auto simp add: comp_associative2)
  then show "x = y"
    using id_right_unit2 x_left_inv x_type y_type by auto
qed

lemma predecessor_type[type_rule]:
  "predecessor : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c"
  by (simp add: predecessor_def2)

lemma predecessor_left_inv:
  "(zero \<amalg> successor) \<circ>\<^sub>c predecessor = id \<nat>\<^sub>c"
  by (simp add: predecessor_def2)

lemma predecessor_right_inv:
  "predecessor \<circ>\<^sub>c (zero \<amalg> successor) = id (one \<Coprod> \<nat>\<^sub>c)"
  by (simp add: predecessor_def2)

lemma predecessor_successor:
  "predecessor \<circ>\<^sub>c successor = right_coproj one \<nat>\<^sub>c"
proof -
  have "predecessor \<circ>\<^sub>c successor = predecessor \<circ>\<^sub>c (zero \<amalg> successor) \<circ>\<^sub>c right_coproj one \<nat>\<^sub>c"
    using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
  also have "... = (predecessor \<circ>\<^sub>c (zero \<amalg> successor)) \<circ>\<^sub>c right_coproj one \<nat>\<^sub>c"
    by (typecheck_cfuncs, auto simp add: comp_associative2)
  also have "... = right_coproj one \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: id_left_unit2 predecessor_def2)
  then show ?thesis
    using calculation by auto
qed

lemma predecessor_zero:
  "predecessor \<circ>\<^sub>c zero = left_coproj one \<nat>\<^sub>c"
proof -
  have "predecessor \<circ>\<^sub>c zero = predecessor \<circ>\<^sub>c (zero \<amalg> successor) \<circ>\<^sub>c left_coproj one \<nat>\<^sub>c"
    using left_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
  also have "... = (predecessor \<circ>\<^sub>c (zero \<amalg> successor)) \<circ>\<^sub>c left_coproj one \<nat>\<^sub>c"
    by (typecheck_cfuncs, auto simp add: comp_associative2)
  also have "... = left_coproj one \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: id_left_unit2 predecessor_def2)
  then show ?thesis
    using calculation by auto
qed
    
section \<open>Peano's Axioms and Induction\<close>

text \<open>The lemma below corresponds to Proposition 2.6.7 in Halvorson\<close>
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
  obtain u where u_type: "u:  \<nat>\<^sub>c  \<rightarrow> \<Omega>" and u_def: "u \<circ>\<^sub>c zero = \<t>  \<and> (\<f>\<circ>\<^sub>c\<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c u = u \<circ>\<^sub>c  successor"
    by (typecheck_cfuncs, metis natural_number_object_property)    
  have s_not_surj: "\<not>(surjective(successor))"
    proof (rule ccontr, auto)
      assume BWOC : "surjective(successor)"
      obtain n where n_type: "n : one \<rightarrow> \<nat>\<^sub>c" and snEqz: "successor \<circ>\<^sub>c n = zero"
        using BWOC cfunc_type_def successor_type surjective_def zero_type by auto
      then show False
        by (metis zero_is_not_successor)
    qed
  then show "injective successor \<and> \<not> surjective successor"
    using monomorphism_imp_injective succ_mono by blast
qed

corollary nat_is_infinite:
  "is_infinite \<nat>\<^sub>c"
  unfolding is_infinite_def using Peano's_Axioms injective_imp_monomorphism successor_type by blast

lemma succ_inject:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "successor \<circ>\<^sub>c n = successor \<circ>\<^sub>c m \<Longrightarrow> n = m"
  by (metis Peano's_Axioms assms cfunc_type_def injective_def successor_type) 

theorem nat_induction:
  assumes p_type[type_rule]: "p : \<nat>\<^sub>c \<rightarrow> \<Omega>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes base_case: "p \<circ>\<^sub>c zero = \<t>"
  assumes induction_case: "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> p \<circ>\<^sub>c n = \<t> \<Longrightarrow> p \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
  shows "p \<circ>\<^sub>c n = \<t>"
proof -
  obtain p' P where
    p'_type[type_rule]: "p' : P \<rightarrow> \<nat>\<^sub>c" and
    p'_equalizer: "p \<circ>\<^sub>c p' = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p'" and
    p'_uni_prop: "\<forall> h F. ((h : F \<rightarrow> \<nat>\<^sub>c) \<and> (p \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> P) \<and> p' \<circ>\<^sub>c k = h)"
    using equalizer_exists2 by (typecheck_cfuncs, blast)

  from base_case have "p \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
    by (etcs_assocr, etcs_subst terminal_func_comp_elem id_right_unit2, -)
  then obtain z' where
    z'_type[type_rule]: "z' \<in>\<^sub>c P" and
    z'_def: "zero = p' \<circ>\<^sub>c z'"
    using p'_uni_prop by (typecheck_cfuncs, metis)

  have "p \<circ>\<^sub>c successor \<circ>\<^sub>c p' = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c p'"
  proof (etcs_rule one_separator)
    fix m
    assume m_type[type_rule]: "m \<in>\<^sub>c P"

    have "p  \<circ>\<^sub>c p' \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c p' \<circ>\<^sub>c m"
      by (etcs_assocl, simp add: p'_equalizer)
    then have "p \<circ>\<^sub>c p' \<circ>\<^sub>c m = \<t>"
      by (-, etcs_subst_asm terminal_func_comp_elem id_right_unit2, simp)
    then have "p \<circ>\<^sub>c successor \<circ>\<^sub>c p' \<circ>\<^sub>c m = \<t>"
      using induction_case by (typecheck_cfuncs, simp)
    then show "(p \<circ>\<^sub>c successor \<circ>\<^sub>c p') \<circ>\<^sub>c m = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c p') \<circ>\<^sub>c m"
      by (etcs_assocr, etcs_subst terminal_func_comp_elem id_right_unit2, -)
  qed
  then obtain s' where
    s'_type[type_rule]: "s' : P \<rightarrow> P" and
    s'_def: "p' \<circ>\<^sub>c s' = successor \<circ>\<^sub>c p'"
    using p'_uni_prop by (typecheck_cfuncs, metis)

  obtain u where
    u_type[type_rule]: "u : \<nat>\<^sub>c \<rightarrow> P" and
    u_zero: "u \<circ>\<^sub>c zero = z'" and
    u_succ: "u \<circ>\<^sub>c successor = s' \<circ>\<^sub>c u"
    using natural_number_object_property2 by (typecheck_cfuncs, metis s'_type)

  have p'_u_is_id: "p' \<circ>\<^sub>c u = id \<nat>\<^sub>c"
  proof (etcs_rule natural_number_object_func_unique[where f=successor])
    show "(p' \<circ>\<^sub>c u) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (etcs_subst id_left_unit2, etcs_assocr, etcs_subst u_zero z'_def, simp)
    show "(p' \<circ>\<^sub>c u) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c p' \<circ>\<^sub>c u"
      by (etcs_assocr, etcs_subst u_succ, etcs_assocl, etcs_subst s'_def, simp)
    show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
      by (etcs_subst id_right_unit2 id_left_unit2, simp)
  qed

  have "p \<circ>\<^sub>c p' \<circ>\<^sub>c u \<circ>\<^sub>c n = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p' \<circ>\<^sub>c u \<circ>\<^sub>c n"
    by (typecheck_cfuncs, smt comp_associative2 p'_equalizer)
  then show "p \<circ>\<^sub>c n = \<t>"
    by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 id_right_unit2 p'_type p'_u_is_id terminal_func_comp_elem terminal_func_type u_type)
qed
    
section \<open>Function Iteration\<close>

definition ITER_curried :: "cset \<Rightarrow> cfunc" where 
  "ITER_curried U = (THE u . u : \<nat>\<^sub>c \<rightarrow> (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<and>  u \<circ>\<^sub>c zero = (metafunc (id U) \<circ>\<^sub>c (right_cart_proj (U\<^bsup>U\<^esup>) one))\<^sup>\<sharp> \<and>
    ((meta_comp U U U) \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>)\<times>\<^sub>f id ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp>    \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma ITER_curried_def2: 
"ITER_curried U : \<nat>\<^sub>c \<rightarrow> (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<and>  ITER_curried U \<circ>\<^sub>c zero = (metafunc (id U) \<circ>\<^sub>c (right_cart_proj (U\<^bsup>U\<^esup>) one))\<^sup>\<sharp> \<and>
  ((meta_comp U U U) \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>)\<times>\<^sub>f id ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp>    \<circ>\<^sub>c ITER_curried U = ITER_curried U  \<circ>\<^sub>c successor"
  unfolding ITER_curried_def
  by(rule theI', etcs_rule natural_number_object_property2)
  
lemma ITER_curried_type[type_rule]:
  "ITER_curried U : \<nat>\<^sub>c \<rightarrow> (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>"
  by (simp add: ITER_curried_def2)

lemma ITER_curried_zero: 
  "ITER_curried U \<circ>\<^sub>c zero = (metafunc (id U) \<circ>\<^sub>c (right_cart_proj (U\<^bsup>U\<^esup>) one))\<^sup>\<sharp>"
  by (simp add: ITER_curried_def2)

lemma ITER_curried_successor:
"ITER_curried U \<circ>\<^sub>c successor = (meta_comp U U U \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>)\<times>\<^sub>f id ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp>    \<circ>\<^sub>c ITER_curried U"
  using ITER_curried_def2 by simp 

definition ITER :: "cset \<Rightarrow> cfunc" where 
  "ITER U = (ITER_curried U)\<^sup>\<flat>"

lemma ITER_type[type_rule]:
  "ITER U : ((U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> (U\<^bsup>U\<^esup>)"
  unfolding ITER_def by typecheck_cfuncs

lemma ITER_zero: 
  assumes "f : Z \<rightarrow> (U\<^bsup>U\<^esup>)"
  shows "ITER U \<circ>\<^sub>c \<langle>f, zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> = metafunc (id U) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>"
proof(rule one_separator[where X = Z, where Y = "U\<^bsup>U\<^esup>"])
  show "ITER U \<circ>\<^sub>c \<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> : Z \<rightarrow> U\<^bsup>U\<^esup>"
    using assms by typecheck_cfuncs
  show "metafunc (id\<^sub>c U) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub> : Z \<rightarrow> U\<^bsup>U\<^esup>"
    using assms by typecheck_cfuncs
next
  fix z 
  assume z_type[type_rule]: "z \<in>\<^sub>c Z"
  have "(ITER U \<circ>\<^sub>c \<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle>) \<circ>\<^sub>c z = ITER U \<circ>\<^sub>c \<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> \<circ>\<^sub>c z"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = ITER U \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z,zero\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (id\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z,zero\<rangle>"
    using assms ITER_def comp_associative2 inv_transpose_func_def3 by (typecheck_cfuncs, auto)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z,ITER_curried U \<circ>\<^sub>c zero\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z,(metafunc (id U) \<circ>\<^sub>c (right_cart_proj (U\<^bsup>U\<^esup>) one))\<^sup>\<sharp>\<rangle>"
    using assms by (simp add: ITER_curried_def2)   
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z,((left_cart_proj (U) one)\<^sup>\<sharp> \<circ>\<^sub>c (right_cart_proj (U\<^bsup>U\<^esup>) one))\<^sup>\<sharp>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 metafunc_def2)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (id\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>f  ((left_cart_proj (U) one)\<^sup>\<sharp> \<circ>\<^sub>c (right_cart_proj (U\<^bsup>U\<^esup>) one))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>f  \<circ>\<^sub>c z,id\<^sub>c one\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
  also have "... = (left_cart_proj (U) one)\<^sup>\<sharp> \<circ>\<^sub>c (right_cart_proj (U\<^bsup>U\<^esup>) one)  \<circ>\<^sub>c \<langle>f  \<circ>\<^sub>c z,id\<^sub>c one\<rangle>"
    using assms by (typecheck_cfuncs,simp add: cfunc_type_def comp_associative transpose_func_def)
  also have "... = (left_cart_proj (U) one)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: id_right_unit2 right_cart_proj_cfunc_prod)
  also have "... = (metafunc (id\<^sub>c U))"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 metafunc_def2)
  also have "... = (metafunc (id\<^sub>c U) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>) \<circ>\<^sub>c z"
    using assms by (typecheck_cfuncs, metis cfunc_type_def comp_associative id_right_unit2 terminal_func_comp_elem)
  then show "(ITER U \<circ>\<^sub>c \<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle>) \<circ>\<^sub>c z = (metafunc (id\<^sub>c U) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>) \<circ>\<^sub>c z"
    using calculation by auto
qed

lemma ITER_zero': 
  assumes "f \<in>\<^sub>c (U\<^bsup>U\<^esup>)"
  shows "ITER U \<circ>\<^sub>c \<langle>f, zero\<rangle> = metafunc (id U)"
  by (typecheck_cfuncs, metis ITER_zero assms id_right_unit2 id_type one_unique_element terminal_func_type)

lemma ITER_succ:
 assumes "f : Z \<rightarrow> (U\<^bsup>U\<^esup>)"
 assumes "n : Z \<rightarrow> \<nat>\<^sub>c"
 shows "ITER U \<circ>\<^sub>c \<langle>f, successor \<circ>\<^sub>c n\<rangle> = f \<box> (ITER U \<circ>\<^sub>c \<langle>f, n \<rangle>)"
proof(rule one_separator[where X = Z, where Y = "U\<^bsup>U\<^esup>"])
  show "ITER U \<circ>\<^sub>c \<langle>f,successor \<circ>\<^sub>c n\<rangle> : Z \<rightarrow> U\<^bsup>U\<^esup>"
    using assms by typecheck_cfuncs
  show "f \<box> ITER U \<circ>\<^sub>c \<langle>f,n\<rangle> : Z \<rightarrow> U\<^bsup>U\<^esup>"
    using assms by typecheck_cfuncs
next
  fix z 
  assume z_type[type_rule]: "z \<in>\<^sub>c Z"
  have "(ITER U \<circ>\<^sub>c \<langle>f,successor \<circ>\<^sub>c n\<rangle>) \<circ>\<^sub>c z  = ITER U \<circ>\<^sub>c \<langle>f,successor \<circ>\<^sub>c n\<rangle> \<circ>\<^sub>c z"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = ITER U \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (id\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: ITER_def comp_associative2 inv_transpose_func_def3)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried U \<circ>\<^sub>c (successor \<circ>\<^sub>c (n  \<circ>\<^sub>c z))\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs, force)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, (ITER_curried U \<circ>\<^sub>c successor) \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>"
    using assms by(typecheck_cfuncs, metis comp_associative2)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ((meta_comp U U U \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>)\<times>\<^sub>f id ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp> \<circ>\<^sub>c ITER_curried U) \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>"
    using assms ITER_curried_successor by presburger
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f ((meta_comp U U U \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>)\<times>\<^sub>f id ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp> \<circ>\<^sub>c ITER_curried U) \<circ>\<^sub>c (n  \<circ>\<^sub>c z))\<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id one\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
  also have "... = (eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f ((meta_comp U U U \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>)\<times>\<^sub>f id ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp> ))\<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried U \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_right_unit2)
  also have "... = (meta_comp U U U \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>)\<times>\<^sub>f id ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried U \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>"
    using assms by (typecheck_cfuncs, metis cfunc_type_def comp_associative transpose_func_def)
  also have "... = (meta_comp U U U \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) ((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<circ>\<^sub>c \<langle>\<langle>f \<circ>\<^sub>c z,f \<circ>\<^sub>c z\<rangle>, ITER_curried U \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>"
    using assms by (etcs_assocr, typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod diag_on_elements id_left_unit2)
  also have "... = meta_comp U U U \<circ>\<^sub>c (id (U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, \<langle>f \<circ>\<^sub>c z, ITER_curried U \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) associate_right_ap comp_associative2)
  also have "... = meta_comp U U U \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried U \<circ>\<^sub>c (n  \<circ>\<^sub>c z)\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = meta_comp U U U \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, eval_func (U\<^bsup>U\<^esup>) (U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried U)\<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = meta_comp U U U \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER U \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) ITER_def comp_associative2 inv_transpose_func_def3)
  also have "... = meta_comp U U U \<circ>\<^sub>c \<langle>f, ITER U \<circ>\<^sub>c \<langle>f , n\<rangle>\<rangle> \<circ>\<^sub>c z"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
  also have "... = (meta_comp U U U \<circ>\<^sub>c \<langle>f, ITER U \<circ>\<^sub>c \<langle>f , n\<rangle>\<rangle>) \<circ>\<^sub>c z"
    using assms by (typecheck_cfuncs, meson comp_associative2)
  also have "... = (f \<box> (ITER U \<circ>\<^sub>c \<langle>f,n\<rangle>)) \<circ>\<^sub>c z"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def5)
  then show "(ITER U \<circ>\<^sub>c \<langle>f,successor \<circ>\<^sub>c n\<rangle>) \<circ>\<^sub>c z = (f \<box> ITER U \<circ>\<^sub>c \<langle>f,n\<rangle>) \<circ>\<^sub>c z"
    by (simp add: calculation)
qed

lemma ITER_one:
 assumes "f \<in>\<^sub>c (U\<^bsup>U\<^esup>)"
 shows "ITER U \<circ>\<^sub>c \<langle>f, successor \<circ>\<^sub>c zero\<rangle> = f \<box> (metafunc (id U))"
  using ITER_succ ITER_zero' assms zero_type by presburger

definition iter_comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("_\<^bsup>\<circ>_\<^esup>"[55,0]55) where
  "iter_comp g n  \<equiv> cnufatem (ITER (domain g) \<circ>\<^sub>c \<langle>metafunc g,n\<rangle>)"

lemma iter_comp_def2: 
  "g\<^bsup>\<circ>n\<^esup>  \<equiv> cnufatem(ITER (domain g) \<circ>\<^sub>c \<langle>metafunc g,n\<rangle>)"
  by (simp add: iter_comp_def)

lemma iter_comp_type[type_rule]:
  assumes "g : X \<rightarrow> X"
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "g\<^bsup>\<circ>n\<^esup>: X \<rightarrow> X"
  unfolding iter_comp_def2
  by (smt (verit, ccfv_SIG) ITER_type assms cfunc_type_def cnufatem_type comp_type metafunc_type right_param_on_el right_param_type) 

lemma iter_comp_def3: 
  assumes "g : X \<rightarrow> X"
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "g\<^bsup>\<circ>n\<^esup>  = cnufatem (ITER X \<circ>\<^sub>c \<langle>metafunc g,n\<rangle>)"
  using assms cfunc_type_def iter_comp_def2 by auto

lemma zero_iters:
  assumes "g : X \<rightarrow> X"
  shows "g\<^bsup>\<circ>zero\<^esup> = id\<^sub>c X"
proof(rule one_separator[where X=X, where Y=X])
  show "g\<^bsup>\<circ>zero\<^esup> : X \<rightarrow> X"
    using assms by typecheck_cfuncs
  show "id\<^sub>c X : X \<rightarrow> X"
    by typecheck_cfuncs
next 
  fix x 
  assume x_type[type_rule]: "x \<in>\<^sub>c X"
  have "(g\<^bsup>\<circ>zero\<^esup>) \<circ>\<^sub>c x = (cnufatem (ITER X \<circ>\<^sub>c \<langle>metafunc g,zero\<rangle>)) \<circ>\<^sub>c x"
    using assms iter_comp_def3 by (typecheck_cfuncs, auto)
  also have "... = cnufatem (metafunc (id X)) \<circ>\<^sub>c x"
    by (simp add: ITER_zero' assms metafunc_type)
  also have "... = id\<^sub>c X \<circ>\<^sub>c x"
    by (metis cnufatem_metafunc id_type)
  also have "... = x"
    by (typecheck_cfuncs, simp add: id_left_unit2)
  then show "(g\<^bsup>\<circ>zero\<^esup>) \<circ>\<^sub>c x = id\<^sub>c X \<circ>\<^sub>c x"
    by (simp add: calculation)
qed

lemma succ_iters:
  assumes "g : X \<rightarrow> X"
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "g\<^bsup>\<circ>(successor \<circ>\<^sub>c n)\<^esup> = g \<circ>\<^sub>c (g\<^bsup>\<circ>n\<^esup>)"    
proof - 
  have "g\<^bsup>\<circ>successor \<circ>\<^sub>c n\<^esup>   = cnufatem(ITER X \<circ>\<^sub>c \<langle>metafunc g,successor \<circ>\<^sub>c n \<rangle>)"
    using assms by (typecheck_cfuncs, simp add: iter_comp_def3)
  also have "... = cnufatem(metafunc g \<box> ITER X \<circ>\<^sub>c \<langle>metafunc g, n \<rangle>)"
    using assms by (typecheck_cfuncs, simp add: ITER_succ)
  also have "... = cnufatem(metafunc g \<box> metafunc (g\<^bsup>\<circ>n\<^esup>))"
    using assms by (typecheck_cfuncs, metis iter_comp_def3 metafunc_cnufatem)
  also have "... = g \<circ>\<^sub>c (g\<^bsup>\<circ>n\<^esup>)"
    using assms by (typecheck_cfuncs, simp add: comp_as_metacomp)
  then show ?thesis
    using calculation by auto
qed

corollary one_iter:
  assumes "g : X \<rightarrow> X"
  shows "g\<^bsup>\<circ>(successor \<circ>\<^sub>c zero)\<^esup> = g"
  using assms id_right_unit2 succ_iters zero_iters zero_type by force

lemma eval_lemma_for_ITER:
  assumes "f : X \<rightarrow> X"
  assumes "x \<in>\<^sub>c X"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(f\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c x = eval_func X X \<circ>\<^sub>c \<langle>x ,ITER X \<circ>\<^sub>c \<langle>metafunc f ,m\<rangle>\<rangle>"
  using assms by (typecheck_cfuncs, metis eval_lemma iter_comp_def3 metafunc_cnufatem)

lemma n_accessible_by_succ_iter_aux:
   "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>(metafunc successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id \<nat>\<^sub>c\<rangle>\<rangle> = id \<nat>\<^sub>c"
proof(rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f = successor])
  show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
next
  have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero =
         eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>\<rangle>"
    by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
  also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor,zero\<rangle>\<rangle>"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero,metafunc (id \<nat>\<^sub>c) \<rangle>"
    by (typecheck_cfuncs, simp add: ITER_zero')
  also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    using eval_lemma by (typecheck_cfuncs, blast)
  then show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    using calculation by auto
  show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
  proof(rule one_separator[where X ="\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
    show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by typecheck_cfuncs
    show "successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by typecheck_cfuncs
  next    
    fix m
    assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    have "(successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c m = 
         successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    also have "... = successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero ,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor ,m\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)
    also have "... = successor \<circ>\<^sub>c (successor\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: eval_lemma_for_ITER)
    also have "... = (successor\<^bsup>\<circ>successor \<circ>\<^sub>c m\<^esup>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2 succ_iters)
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero ,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor ,successor \<circ>\<^sub>c m\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: eval_lemma_for_ITER)
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c m),ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c m),id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (successor \<circ>\<^sub>c m)\<rangle>\<rangle>"
      by (typecheck_cfuncs,simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)
    also have "... = ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    then show "((eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m =
         (successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c m"
      using calculation by presburger
  qed
  show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
qed

lemma n_accessible_by_succ_iter:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(successor\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c zero = n"
proof - 
  have "n = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2 n_accessible_by_succ_iter_aux)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n , ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n, id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero,  ITER \<nat>\<^sub>c \<circ>\<^sub>c \<langle>metafunc successor, n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  also have "... = (successor\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c zero"
    using assms by (typecheck_cfuncs, metis eval_lemma iter_comp_def3 metafunc_cnufatem)
  then show ?thesis
    using calculation by auto
qed

section \<open>Relation of Nat to Other Sets\<close>

lemma oneUN_iso_N:
  "one \<Coprod> \<nat>\<^sub>c \<cong> \<nat>\<^sub>c"
  using cfunc_coprod_type is_isomorphic_def oneUN_iso_N_isomorphism successor_type zero_type by blast

lemma NUone_iso_N:
  "\<nat>\<^sub>c \<Coprod> one \<cong> \<nat>\<^sub>c"
  using coproduct_commutes isomorphic_is_transitive oneUN_iso_N by blast
  
end