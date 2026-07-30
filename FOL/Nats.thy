section \<open>Natural Number Object\<close>

theory Nats
  imports Exponential_Objects Cardinality
begin

text \<open>The axiomatization below corresponds to Axiom 10 (Natural Number Object) in Halvorson.\<close>
axiomatization
  natural_numbers :: "cset" ("\<nat>\<^sub>c") and
  zero :: "cfunc" and
  successor :: "cfunc"
  where
  zero_type[type_rule]: "zero \<in>\<^sub>c \<nat>\<^sub>c" and
  successor_type[type_rule]: "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and
  natural_number_object_property:
  "q : \<one> \<rightarrow> X \<Longrightarrow> f : X \<rightarrow> X \<Longrightarrow>
   (\<exists>!u. u : \<nat>\<^sub>c \<rightarrow> X \<and>
   q = u \<circ>\<^sub>c zero \<and>
   f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma beta_N_succ_nEqs_Id1:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n = id(\<one>)"
  by (typecheck_cfuncs, simp add: terminal_func_comp_elem)

lemma natural_number_object_property2:
  assumes q_type[type_rule]: "q : \<one> \<rightarrow> X" and f_type[type_rule]: "f : X \<rightarrow> X"
  shows "\<exists>!u. u : \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = q \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
proof (rule ex1E[OF natural_number_object_property[OF q_type f_type]])
  fix u
  assume u_props: "u : \<nat>\<^sub>c \<rightarrow> X \<and> q = u \<circ>\<^sub>c zero \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
  assume u_uniq: "\<forall>y. y : \<nat>\<^sub>c \<rightarrow> X \<and> q = y \<circ>\<^sub>c zero \<and> f \<circ>\<^sub>c y = y \<circ>\<^sub>c successor \<longrightarrow> y = u"
  show "\<exists>!u. u : \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = q \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
  proof (rule ex1I[where a=u])
    show "u : \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = q \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
      using u_props by auto
  next
    fix w
    assume w_props: "w : \<nat>\<^sub>c \<rightarrow> X \<and> w \<circ>\<^sub>c zero = q \<and> f \<circ>\<^sub>c w = w \<circ>\<^sub>c successor"
    have w_props': "w : \<nat>\<^sub>c \<rightarrow> X \<and> q = w \<circ>\<^sub>c zero \<and> f \<circ>\<^sub>c w = w \<circ>\<^sub>c successor"
      using w_props by auto
    show "w = u" using u_uniq w_props' by auto
  qed
qed

lemma natural_number_object_func_unique:
  assumes u_type: "u : \<nat>\<^sub>c \<rightarrow> X" and v_type: "v : \<nat>\<^sub>c \<rightarrow> X" and f_type: "f : X \<rightarrow> X"
  assumes zeros_eq: "u \<circ>\<^sub>c zero = v \<circ>\<^sub>c zero"
  assumes u_successor_eq: "u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u"
  assumes v_successor_eq: "v \<circ>\<^sub>c successor = f \<circ>\<^sub>c v"
  shows "u = v"
proof -
  have uz_type: "u \<circ>\<^sub>c zero : \<one> \<rightarrow> X" using u_type by typecheck_cfuncs
  show "u = v"
  proof (rule ex1E[OF natural_number_object_property[OF uz_type f_type]])
    fix w
    assume w_props: "w : \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = w \<circ>\<^sub>c zero \<and> f \<circ>\<^sub>c w = w \<circ>\<^sub>c successor"
    assume w_uniq: "\<forall>y. y : \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = y \<circ>\<^sub>c zero \<and> f \<circ>\<^sub>c y = y \<circ>\<^sub>c successor \<longrightarrow> y = w"
    have u_fits: "u : \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = u \<circ>\<^sub>c zero \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
      using u_type u_successor_eq by auto
    have v_fits: "v : \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = v \<circ>\<^sub>c zero \<and> f \<circ>\<^sub>c v = v \<circ>\<^sub>c successor"
      using v_type zeros_eq v_successor_eq by auto
    have u_eq_w: "u = w" using w_uniq u_fits by auto
    have v_eq_w: "v = w" using w_uniq v_fits by auto
    show "u = v" using u_eq_w v_eq_w by simp
  qed
qed

definition is_NNO :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> o" where
  "is_NNO(Y, z, s) \<longleftrightarrow> (z : \<one> \<rightarrow> Y \<and> s : Y \<rightarrow> Y \<and> (\<forall>X f q. ((q : \<one> \<rightarrow> X) \<and> (f : X \<rightarrow> X)) \<longrightarrow>
    (\<exists>!u. u : Y \<rightarrow> X \<and> q = u \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c u = u \<circ>\<^sub>c s)))"

lemma N_is_a_NNO:
  "is_NNO(\<nat>\<^sub>c, zero, successor)"
  unfolding is_NNO_def
  using natural_number_object_property successor_type zero_type by auto

text \<open>The lemma below corresponds to Exercise 2.6.5 in Halvorson.\<close>
lemma NNOs_are_iso_N:
  assumes NNO: "is_NNO(N, z, s)"
  shows "N \<cong> \<nat>\<^sub>c"
proof -
  have z_type[type_rule]: "z : \<one> \<rightarrow> N" using NNO is_NNO_def by auto
  have s_type[type_rule]: "s : N \<rightarrow> N" using NNO is_NNO_def by auto
  have all_prop: "\<forall>X f q. (q : \<one> \<rightarrow> X \<and> f : X \<rightarrow> X) \<longrightarrow> (\<exists>!v. v : N \<rightarrow> X \<and> q = v \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c v = v \<circ>\<^sub>c s)"
    using NNO is_NNO_def by auto
  have ex1_N: "\<exists>!v. v : N \<rightarrow> \<nat>\<^sub>c \<and> zero = v \<circ>\<^sub>c z \<and> successor \<circ>\<^sub>c v = v \<circ>\<^sub>c s"
    using all_prop zero_type successor_type by blast
  obtain u where u_type[type_rule]: "u : \<nat>\<^sub>c \<rightarrow> N" and u_triangle: "u \<circ>\<^sub>c zero = z" and u_square: "s \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    using natural_number_object_property[OF z_type s_type] by auto
  obtain v where v_type[type_rule]: "v : N \<rightarrow> \<nat>\<^sub>c" and v_triangle: "v \<circ>\<^sub>c z = zero" and v_square: "successor \<circ>\<^sub>c v = v \<circ>\<^sub>c s"
    using ex1_N by auto
  have vuzeroEqzero: "v \<circ>\<^sub>c (u \<circ>\<^sub>c zero) = zero"
    using u_triangle v_triangle by simp
  have idN_props: "id(\<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> id(\<nat>\<^sub>c) \<circ>\<^sub>c zero = zero \<and> successor \<circ>\<^sub>c id(\<nat>\<^sub>c) = id(\<nat>\<^sub>c) \<circ>\<^sub>c successor"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  have vu_type[type_rule]: "v \<circ>\<^sub>c u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have vu_zero: "(v \<circ>\<^sub>c u) \<circ>\<^sub>c zero = zero"
  proof -
    have "(v \<circ>\<^sub>c u) \<circ>\<^sub>c zero = v \<circ>\<^sub>c (u \<circ>\<^sub>c zero)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then show ?thesis using vuzeroEqzero by simp
  qed
  have vu_square: "successor \<circ>\<^sub>c (v \<circ>\<^sub>c u) = (v \<circ>\<^sub>c u) \<circ>\<^sub>c successor"
  proof -
    have s1: "successor \<circ>\<^sub>c (v \<circ>\<^sub>c u) = (successor \<circ>\<^sub>c v) \<circ>\<^sub>c u"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have s2: "(successor \<circ>\<^sub>c v) \<circ>\<^sub>c u = (v \<circ>\<^sub>c s) \<circ>\<^sub>c u"
      using v_square by simp
    have s3: "(v \<circ>\<^sub>c s) \<circ>\<^sub>c u = v \<circ>\<^sub>c (s \<circ>\<^sub>c u)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have s4: "v \<circ>\<^sub>c (s \<circ>\<^sub>c u) = v \<circ>\<^sub>c (u \<circ>\<^sub>c successor)"
      using u_square by simp
    have s5: "v \<circ>\<^sub>c (u \<circ>\<^sub>c successor) = (v \<circ>\<^sub>c u) \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    show ?thesis using s1 s2 s3 s4 s5 by simp
  qed
  have half_isomorphism: "v \<circ>\<^sub>c u = id(\<nat>\<^sub>c)"
  proof (rule ex1E[OF natural_number_object_property[OF zero_type successor_type]])
    fix w
    assume w_props: "w : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> zero = w \<circ>\<^sub>c zero \<and> successor \<circ>\<^sub>c w = w \<circ>\<^sub>c successor"
    assume w_uniq: "\<forall>y. y : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> zero = y \<circ>\<^sub>c zero \<and> successor \<circ>\<^sub>c y = y \<circ>\<^sub>c successor \<longrightarrow> y = w"
    have vu_fits: "v \<circ>\<^sub>c u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> zero = (v \<circ>\<^sub>c u) \<circ>\<^sub>c zero \<and> successor \<circ>\<^sub>c (v \<circ>\<^sub>c u) = (v \<circ>\<^sub>c u) \<circ>\<^sub>c successor"
      using vu_type vu_zero vu_square by auto
    have id_fits: "id(\<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> zero = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero \<and> successor \<circ>\<^sub>c id(\<nat>\<^sub>c) = id(\<nat>\<^sub>c) \<circ>\<^sub>c successor"
      using idN_props by auto
    have vu_eq_w: "v \<circ>\<^sub>c u = w" using w_uniq vu_fits by auto
    have id_eq_w: "id(\<nat>\<^sub>c) = w" using w_uniq id_fits by auto
    show "v \<circ>\<^sub>c u = id(\<nat>\<^sub>c)" using vu_eq_w id_eq_w by simp
  qed
  have uvzEqz: "u \<circ>\<^sub>c (v \<circ>\<^sub>c z) = z"
    using u_triangle v_triangle by simp
  have idNN_props: "id(N) : N \<rightarrow> N \<and> id(N) \<circ>\<^sub>c z = z \<and> s \<circ>\<^sub>c id(N) = id(N) \<circ>\<^sub>c s"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  have uv_type[type_rule]: "u \<circ>\<^sub>c v : N \<rightarrow> N" by typecheck_cfuncs
  have uv_z: "(u \<circ>\<^sub>c v) \<circ>\<^sub>c z = z"
  proof -
    have "(u \<circ>\<^sub>c v) \<circ>\<^sub>c z = u \<circ>\<^sub>c (v \<circ>\<^sub>c z)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    then show ?thesis using uvzEqz by simp
  qed
  have uv_square: "s \<circ>\<^sub>c (u \<circ>\<^sub>c v) = (u \<circ>\<^sub>c v) \<circ>\<^sub>c s"
  proof -
    have t1: "s \<circ>\<^sub>c (u \<circ>\<^sub>c v) = (s \<circ>\<^sub>c u) \<circ>\<^sub>c v"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have t2: "(s \<circ>\<^sub>c u) \<circ>\<^sub>c v = (u \<circ>\<^sub>c successor) \<circ>\<^sub>c v"
      using u_square by simp
    have t3: "(u \<circ>\<^sub>c successor) \<circ>\<^sub>c v = u \<circ>\<^sub>c (successor \<circ>\<^sub>c v)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    have t4: "u \<circ>\<^sub>c (successor \<circ>\<^sub>c v) = u \<circ>\<^sub>c (v \<circ>\<^sub>c s)"
      using v_square by simp
    have t5: "u \<circ>\<^sub>c (v \<circ>\<^sub>c s) = (u \<circ>\<^sub>c v) \<circ>\<^sub>c s"
      by (typecheck_cfuncs, simp add: comp_associative2)
    show ?thesis using t1 t2 t3 t4 t5 by simp
  qed
  have ex1_NN: "\<exists>!w. w : N \<rightarrow> N \<and> z = w \<circ>\<^sub>c z \<and> s \<circ>\<^sub>c w = w \<circ>\<^sub>c s"
    using all_prop z_type s_type by blast
  have half_isomorphism2: "u \<circ>\<^sub>c v = id(N)"
  proof (rule ex1E[OF ex1_NN])
    fix w
    assume w_props: "w : N \<rightarrow> N \<and> z = w \<circ>\<^sub>c z \<and> s \<circ>\<^sub>c w = w \<circ>\<^sub>c s"
    assume w_uniq: "\<forall>y. y : N \<rightarrow> N \<and> z = y \<circ>\<^sub>c z \<and> s \<circ>\<^sub>c y = y \<circ>\<^sub>c s \<longrightarrow> y = w"
    have uv_fits: "u \<circ>\<^sub>c v : N \<rightarrow> N \<and> z = (u \<circ>\<^sub>c v) \<circ>\<^sub>c z \<and> s \<circ>\<^sub>c (u \<circ>\<^sub>c v) = (u \<circ>\<^sub>c v) \<circ>\<^sub>c s"
      using uv_type uv_z uv_square by auto
    have id_fits: "id(N) : N \<rightarrow> N \<and> z = id(N) \<circ>\<^sub>c z \<and> s \<circ>\<^sub>c id(N) = id(N) \<circ>\<^sub>c s"
      using idNN_props by auto
    have uv_eq_w: "u \<circ>\<^sub>c v = w" using w_uniq uv_fits by auto
    have id_eq_w: "id(N) = w" using w_uniq id_fits by auto
    show "u \<circ>\<^sub>c v = id(N)" using uv_eq_w id_eq_w by simp
  qed
  show "N \<cong> \<nat>\<^sub>c"
    unfolding is_isomorphic_def
  proof (rule exI[where x=v])
    have v_iso: "isomorphism(v)"
      unfolding isomorphism_def3[OF v_type]
      using u_type half_isomorphism half_isomorphism2 by auto
    show "v : N \<rightarrow> \<nat>\<^sub>c \<and> isomorphism(v)" using v_type v_iso by auto
  qed
qed

text \<open>The lemma below is the converse to Exercise 2.6.5 in Halvorson.\<close>
lemma Iso_to_N_is_NNO:
  assumes NcongNc: "N \<cong> \<nat>\<^sub>c"
  shows "\<exists>z s. is_NNO(N, z, s)"
proof -
  have Ncong: "\<nat>\<^sub>c \<cong> N" using NcongNc isomorphic_is_symmetric by auto
  obtain i where i_type[type_rule]: "i : \<nat>\<^sub>c \<rightarrow> N" and i_iso[type_rule]: "isomorphism(i)"
    using Ncong is_isomorphic_def by auto
  have dom_i: "domain(i) = \<nat>\<^sub>c" using i_type unfolding cfunc_type_def by auto
  have cod_i: "codomain(i) = N" using i_type unfolding cfunc_type_def by auto
  have inv_facts: "i\<^bold>\<inverse> : codomain(i) \<rightarrow> domain(i) \<and> i\<^bold>\<inverse> \<circ>\<^sub>c i = id(domain(i)) \<and> i \<circ>\<^sub>c i\<^bold>\<inverse> = id(codomain(i))"
    using inverse_def2[OF i_iso] .
  have iinv_type[type_rule]: "i\<^bold>\<inverse> : N \<rightarrow> \<nat>\<^sub>c" using inv_facts dom_i cod_i unfolding cfunc_type_def by auto
  have s4: "i\<^bold>\<inverse> \<circ>\<^sub>c i = id(\<nat>\<^sub>c)" using inv_facts dom_i by simp
  have s5: "i \<circ>\<^sub>c i\<^bold>\<inverse> = id(N)" using inv_facts cod_i by simp
  define z where z_def: "z = i \<circ>\<^sub>c zero"
  have z_type[type_rule]: "z : \<one> \<rightarrow> N" unfolding z_def by typecheck_cfuncs
  define s where s_def: "s = (i \<circ>\<^sub>c successor) \<circ>\<^sub>c i\<^bold>\<inverse>"
  have s_type[type_rule]: "s : N \<rightarrow> N" unfolding s_def by typecheck_cfuncs
  have iz_type[type_rule]: "i \<circ>\<^sub>c zero : \<one> \<rightarrow> N" by typecheck_cfuncs
  have isucc_type[type_rule]: "i \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> N" by typecheck_cfuncs
  have main_prop: "\<forall>X f q. (q : \<one> \<rightarrow> X \<and> f : X \<rightarrow> X) \<longrightarrow> (\<exists>!v. v : N \<rightarrow> X \<and> q = v \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c v = v \<circ>\<^sub>c s)"
  proof (clarify)
    fix X q f
    assume q_type[type_rule]: "q : \<one> \<rightarrow> X"
    assume f_type[type_rule]: "f : X \<rightarrow> X"
    obtain u where u_type[type_rule]: "u : \<nat>\<^sub>c \<rightarrow> X" and u_zero: "u \<circ>\<^sub>c zero = q" and u_succ: "f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
      using natural_number_object_property2[OF q_type f_type] by auto
    define v where v_def: "v = u \<circ>\<^sub>c i\<^bold>\<inverse>"
    have v_type[type_rule]: "v : N \<rightarrow> X" unfolding v_def by typecheck_cfuncs
    have bottom_triangle: "q = v \<circ>\<^sub>c z"
    proof -
      have s1: "v \<circ>\<^sub>c z = (u \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c z"
        unfolding v_def by simp
      have s2: "(u \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c z = u \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c z)"
        by (rule sym[OF comp_associative2[OF z_type iinv_type u_type]])
      have s3: "i\<^bold>\<inverse> \<circ>\<^sub>c z = (i\<^bold>\<inverse> \<circ>\<^sub>c i) \<circ>\<^sub>c zero"
        unfolding z_def by (rule comp_associative2[OF zero_type i_type iinv_type])
      have s3': "(i\<^bold>\<inverse> \<circ>\<^sub>c i) \<circ>\<^sub>c zero = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero"
        using s4 by simp
      have s6: "id(\<nat>\<^sub>c) \<circ>\<^sub>c zero = zero" by (typecheck_cfuncs, simp add: id_left_unit2)
      show "q = v \<circ>\<^sub>c z" using s1 s2 s3 s3' s6 u_zero by simp
    qed
    have bottom_square: "f \<circ>\<^sub>c v = v \<circ>\<^sub>c s"
    proof -
      have t1: "v \<circ>\<^sub>c s = (u \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c s"
        unfolding v_def by simp
      have t2: "(u \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c s = u \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c s)"
        by (rule sym[OF comp_associative2[OF s_type iinv_type u_type]])
      have t3: "i\<^bold>\<inverse> \<circ>\<^sub>c s = (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c successor)) \<circ>\<^sub>c i\<^bold>\<inverse>"
        unfolding s_def by (rule comp_associative2[OF iinv_type isucc_type iinv_type])
      have t4: "i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c successor) = (i\<^bold>\<inverse> \<circ>\<^sub>c i) \<circ>\<^sub>c successor"
        by (rule comp_associative2[OF successor_type i_type iinv_type])
      have t5: "(i\<^bold>\<inverse> \<circ>\<^sub>c i) \<circ>\<^sub>c successor = id(\<nat>\<^sub>c) \<circ>\<^sub>c successor"
        using s4 by simp
      have t6: "id(\<nat>\<^sub>c) \<circ>\<^sub>c successor = successor" by (typecheck_cfuncs, simp add: id_left_unit2)
      have t7: "u \<circ>\<^sub>c (successor \<circ>\<^sub>c i\<^bold>\<inverse>) = (u \<circ>\<^sub>c successor) \<circ>\<^sub>c i\<^bold>\<inverse>"
        by (rule comp_associative2[OF iinv_type successor_type u_type])
      have t8: "(u \<circ>\<^sub>c successor) \<circ>\<^sub>c i\<^bold>\<inverse> = (f \<circ>\<^sub>c u) \<circ>\<^sub>c i\<^bold>\<inverse>"
        using u_succ by simp
      have t9: "(f \<circ>\<^sub>c u) \<circ>\<^sub>c i\<^bold>\<inverse> = f \<circ>\<^sub>c (u \<circ>\<^sub>c i\<^bold>\<inverse>)"
        by (rule sym[OF comp_associative2[OF iinv_type u_type f_type]])
      show "f \<circ>\<^sub>c v = v \<circ>\<^sub>c s"
        using t1 t2 t3 t4 t5 t6 t7 t8 t9 v_def by simp
    qed
    show "\<exists>!v. v : N \<rightarrow> X \<and> q = v \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c v = v \<circ>\<^sub>c s"
    proof (rule ex1I[where a=v])
      show "v : N \<rightarrow> X \<and> q = v \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c v = v \<circ>\<^sub>c s"
        using v_type bottom_triangle bottom_square by auto
    next
      fix w
      assume w_props: "w : N \<rightarrow> X \<and> q = w \<circ>\<^sub>c z \<and> f \<circ>\<^sub>c w = w \<circ>\<^sub>c s"
      have w_type[type_rule]: "w : N \<rightarrow> X" and w_z: "q = w \<circ>\<^sub>c z" and w_s: "f \<circ>\<^sub>c w = w \<circ>\<^sub>c s"
        using w_props by auto
      have wi_type[type_rule]: "w \<circ>\<^sub>c i : \<nat>\<^sub>c \<rightarrow> X" by typecheck_cfuncs
      have wi_zero: "(w \<circ>\<^sub>c i) \<circ>\<^sub>c zero = u \<circ>\<^sub>c zero"
      proof -
        have a1: "(w \<circ>\<^sub>c i) \<circ>\<^sub>c zero = w \<circ>\<^sub>c (i \<circ>\<^sub>c zero)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        have a2: "i \<circ>\<^sub>c zero = z" using z_def by simp
        show ?thesis using a1 a2 w_z u_zero by simp
      qed
      have wi_succ: "(w \<circ>\<^sub>c i) \<circ>\<^sub>c successor = f \<circ>\<^sub>c (w \<circ>\<^sub>c i)"
      proof -
        have b1: "(w \<circ>\<^sub>c i) \<circ>\<^sub>c successor = w \<circ>\<^sub>c (i \<circ>\<^sub>c successor)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        have b2: "i \<circ>\<^sub>c successor = s \<circ>\<^sub>c i"
        proof -
          have c1: "s \<circ>\<^sub>c i = ((i \<circ>\<^sub>c successor) \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c i"
            unfolding s_def by simp
          have c2: "((i \<circ>\<^sub>c successor) \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c i = (i \<circ>\<^sub>c successor) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c i)"
            by (rule sym[OF comp_associative2[OF i_type iinv_type isucc_type]])
          have c3: "(i \<circ>\<^sub>c successor) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c i) = (i \<circ>\<^sub>c successor) \<circ>\<^sub>c id(\<nat>\<^sub>c)"
            using s4 by simp
          have c4: "(i \<circ>\<^sub>c successor) \<circ>\<^sub>c id(\<nat>\<^sub>c) = i \<circ>\<^sub>c successor"
            by (typecheck_cfuncs, simp add: id_right_unit2)
          show ?thesis using c1 c2 c3 c4 by simp
        qed
        have b4: "w \<circ>\<^sub>c (s \<circ>\<^sub>c i) = (w \<circ>\<^sub>c s) \<circ>\<^sub>c i"
          by (typecheck_cfuncs, simp add: comp_associative2)
        have b6: "(f \<circ>\<^sub>c w) \<circ>\<^sub>c i = f \<circ>\<^sub>c (w \<circ>\<^sub>c i)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        show ?thesis using b1 b2 b4 b6 w_s by simp
      qed
      have wi_eq_u: "w \<circ>\<^sub>c i = u"
        using natural_number_object_func_unique[OF wi_type u_type f_type wi_zero wi_succ u_succ[symmetric]] .
      have w_eq_v: "w = v"
      proof -
        have d2: "v = (w \<circ>\<^sub>c i) \<circ>\<^sub>c i\<^bold>\<inverse>" unfolding v_def using wi_eq_u by simp
        have d3: "(w \<circ>\<^sub>c i) \<circ>\<^sub>c i\<^bold>\<inverse> = w \<circ>\<^sub>c (i \<circ>\<^sub>c i\<^bold>\<inverse>)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        have d4: "w \<circ>\<^sub>c (i \<circ>\<^sub>c i\<^bold>\<inverse>) = w \<circ>\<^sub>c id(N)"
          using s5 by simp
        have d5: "w \<circ>\<^sub>c id(N) = w"
          by (typecheck_cfuncs, simp add: id_right_unit2)
        show ?thesis using d2 d3 d4 d5 by simp
      qed
      show "w = v" using w_eq_v by simp
    qed
  qed
  have "is_NNO(N, z, s)"
    unfolding is_NNO_def using z_type s_type main_prop by auto
  then show ?thesis by auto
qed

subsection \<open>Zero and Successor\<close>

lemma zero_is_not_successor:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "zero \<noteq> successor \<circ>\<^sub>c n"
proof
  assume for_contradiction: "zero = successor \<circ>\<^sub>c n"
  have tf_type[type_rule]: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub> : \<Omega> \<rightarrow> \<Omega>" by typecheck_cfuncs
  obtain u where u_type[type_rule]: "u : \<nat>\<^sub>c \<rightarrow> \<Omega>" and u_triangle: "u \<circ>\<^sub>c zero = \<t>"
    and u_square: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    using natural_number_object_property2[OF true_func_type tf_type] by auto
  have un_type[type_rule]: "u \<circ>\<^sub>c n \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have e1: "\<t> = u \<circ>\<^sub>c zero" using u_triangle by simp
  have e2: "u \<circ>\<^sub>c zero = u \<circ>\<^sub>c (successor \<circ>\<^sub>c n)" using for_contradiction by simp
  have e3: "u \<circ>\<^sub>c (successor \<circ>\<^sub>c n) = (u \<circ>\<^sub>c successor) \<circ>\<^sub>c n"
    by (rule comp_associative2[OF n_type successor_type u_type])
  have e5: "(u \<circ>\<^sub>c successor) \<circ>\<^sub>c n = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c u) \<circ>\<^sub>c n" using u_square by simp
  have e6: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c u) \<circ>\<^sub>c n = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c (u \<circ>\<^sub>c n)"
    by (rule sym[OF comp_associative2[OF n_type u_type tf_type]])
  have e7: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<circ>\<^sub>c (u \<circ>\<^sub>c n) = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>\<Omega>\<^esub> \<circ>\<^sub>c (u \<circ>\<^sub>c n))"
    by (rule sym[OF comp_associative2[OF un_type terminal_func_type false_func_type]])
  have e8: "\<beta>\<^bsub>\<Omega>\<^esub> \<circ>\<^sub>c (u \<circ>\<^sub>c n) = id(\<one>)" by (rule terminal_func_comp_elem[OF un_type])
  have e9: "\<f> \<circ>\<^sub>c (\<beta>\<^bsub>\<Omega>\<^esub> \<circ>\<^sub>c (u \<circ>\<^sub>c n)) = \<f> \<circ>\<^sub>c id(\<one>)" using e8 by simp
  have e10: "\<f> \<circ>\<^sub>c id(\<one>) = \<f>" by (typecheck_cfuncs, simp add: id_right_unit2)
  have "\<t> = \<f>" using e1 e2 e3 e5 e6 e7 e9 e10 by simp
  then show False using true_false_distinct by auto
qed

text \<open>The lemma below corresponds to Proposition 2.6.6 in Halvorson.\<close>
lemma oneUN_iso_N_isomorphism:
 "isomorphism(zero \<amalg> successor)"
proof -
  define H where H_def: "H = zero \<amalg> successor"
  have H_type[type_rule]: "H : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" unfolding H_def by typecheck_cfuncs
  define i0 where i0_def: "i0 = left_coproj(\<one>, \<nat>\<^sub>c)"
  have i0_type[type_rule]: "i0 : \<one> \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)" unfolding i0_def by typecheck_cfuncs
  define i1 where i1_def: "i1 = right_coproj(\<one>, \<nat>\<^sub>c)"
  have i1_type[type_rule]: "i1 : \<nat>\<^sub>c \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)" unfolding i1_def by typecheck_cfuncs
  have i1z_type[type_rule]: "i1 \<circ>\<^sub>c zero : \<one> \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)" by typecheck_cfuncs
  have i1s_type[type_rule]: "i1 \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)" by typecheck_cfuncs
  define F where F_def: "F = (i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)"
  have F_type[type_rule]: "F : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)" unfolding F_def by typecheck_cfuncs
  obtain g where g_type[type_rule]: "g : \<nat>\<^sub>c \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)" and g_triangle: "g \<circ>\<^sub>c zero = i0"
    and g_square: "g \<circ>\<^sub>c successor = F \<circ>\<^sub>c g"
    using natural_number_object_property2[OF i0_type F_type] by auto
  have gs_type[type_rule]: "g \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)" by typecheck_cfuncs
  have second_diagram3: "g \<circ>\<^sub>c (successor \<circ>\<^sub>c zero) = i1 \<circ>\<^sub>c zero"
  proof -
    have m1: "g \<circ>\<^sub>c (successor \<circ>\<^sub>c zero) = (g \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
      by (rule comp_associative2[OF zero_type successor_type g_type])
    have m2: "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c zero = (F \<circ>\<^sub>c g) \<circ>\<^sub>c zero"
      using g_square by simp
    have m3: "(F \<circ>\<^sub>c g) \<circ>\<^sub>c zero = F \<circ>\<^sub>c (g \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type g_type F_type]])
    have m4: "F \<circ>\<^sub>c (g \<circ>\<^sub>c zero) = F \<circ>\<^sub>c i0" using g_triangle by simp
    have m5: "F \<circ>\<^sub>c i0 = i1 \<circ>\<^sub>c zero"
    proof -
      have raw: "((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c) = i1 \<circ>\<^sub>c zero"
        by (rule left_coproj_cfunc_coprod[OF i1z_type i1s_type])
      have i0_is_lc: "i0 = left_coproj(\<one>, \<nat>\<^sub>c)" using i0_def by simp
      have "F \<circ>\<^sub>c i0 = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c i0" using F_def by simp
      also have "... = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c)"
        using i0_is_lc by simp
      also have "... = i1 \<circ>\<^sub>c zero" using raw by simp
      finally show ?thesis by simp
    qed
    show ?thesis using m1 m2 m3 m4 m5 by simp
  qed
  have gs_zero: "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c zero = i1 \<circ>\<^sub>c zero"
  proof -
    have "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c zero = g \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type successor_type g_type]])
    then show ?thesis using second_diagram3 by simp
  qed
  have gs_square: "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = F \<circ>\<^sub>c (g \<circ>\<^sub>c successor)"
  proof -
    have n1: "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = (F \<circ>\<^sub>c g) \<circ>\<^sub>c successor"
      using g_square by simp
    have n2: "(F \<circ>\<^sub>c g) \<circ>\<^sub>c successor = F \<circ>\<^sub>c (g \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type g_type F_type]])
    show ?thesis using n1 n2 by simp
  qed
  have i1_succ_eq: "i1 \<circ>\<^sub>c successor = F \<circ>\<^sub>c i1"
  proof -
    have raw: "((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c) = i1 \<circ>\<^sub>c successor"
      by (rule right_coproj_cfunc_coprod[OF i1z_type i1s_type])
    have i1_is_rc: "i1 = right_coproj(\<one>, \<nat>\<^sub>c)" using i1_def by simp
    have "F \<circ>\<^sub>c i1 = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c i1" using F_def by simp
    also have "... = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c)"
      using i1_is_rc by simp
    also have "... = i1 \<circ>\<^sub>c successor" using raw by simp
    finally show ?thesis by simp
  qed
  have i1_eq_gs: "i1 = g \<circ>\<^sub>c successor"
    using natural_number_object_func_unique[OF i1_type gs_type F_type gs_zero[symmetric] i1_succ_eq gs_square] .
  have HF_eq_sH: "H \<circ>\<^sub>c F = successor \<circ>\<^sub>c H"
  proof -
    have p1: "H \<circ>\<^sub>c F = (H \<circ>\<^sub>c (i1 \<circ>\<^sub>c zero)) \<amalg> (H \<circ>\<^sub>c (i1 \<circ>\<^sub>c successor))"
      unfolding F_def by (rule sym[OF cfunc_coprod_comp[OF H_type i1z_type i1s_type]])
    have p2: "H \<circ>\<^sub>c (i1 \<circ>\<^sub>c zero) = (H \<circ>\<^sub>c i1) \<circ>\<^sub>c zero"
      by (rule comp_associative2[OF zero_type i1_type H_type])
    have p3: "H \<circ>\<^sub>c i1 = successor"
      unfolding H_def i1_def by (rule right_coproj_cfunc_coprod[OF zero_type successor_type])
    have p4: "H \<circ>\<^sub>c (i1 \<circ>\<^sub>c zero) = successor \<circ>\<^sub>c zero"
      using p2 p3 by simp
    have p5: "H \<circ>\<^sub>c (i1 \<circ>\<^sub>c successor) = (H \<circ>\<^sub>c i1) \<circ>\<^sub>c successor"
      by (rule comp_associative2[OF successor_type i1_type H_type])
    have p6: "H \<circ>\<^sub>c (i1 \<circ>\<^sub>c successor) = successor \<circ>\<^sub>c successor"
      using p5 p3 by simp
    have p7: "H \<circ>\<^sub>c F = (successor \<circ>\<^sub>c zero) \<amalg> (successor \<circ>\<^sub>c successor)"
      using p1 p4 p6 by simp
    have p8: "(successor \<circ>\<^sub>c zero) \<amalg> (successor \<circ>\<^sub>c successor) = successor \<circ>\<^sub>c H"
      unfolding H_def by (rule cfunc_coprod_comp[OF successor_type zero_type successor_type])
    show ?thesis using p7 p8 by simp
  qed
  have Hg_type[type_rule]: "H \<circ>\<^sub>c g : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have Hg_zero: "(H \<circ>\<^sub>c g) \<circ>\<^sub>c zero = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero"
  proof -
    have q1: "(H \<circ>\<^sub>c g) \<circ>\<^sub>c zero = H \<circ>\<^sub>c (g \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type g_type H_type]])
    have q2: "H \<circ>\<^sub>c (g \<circ>\<^sub>c zero) = H \<circ>\<^sub>c i0" using g_triangle by simp
    have q3: "H \<circ>\<^sub>c i0 = zero"
      unfolding H_def i0_def by (rule left_coproj_cfunc_coprod[OF zero_type successor_type])
    have q4: "id(\<nat>\<^sub>c) \<circ>\<^sub>c zero = zero" by (typecheck_cfuncs, simp add: id_left_unit2)
    show ?thesis using q1 q2 q3 q4 by simp
  qed
  have Hg_succ: "(H \<circ>\<^sub>c g) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c (H \<circ>\<^sub>c g)"
  proof -
    have r1: "(H \<circ>\<^sub>c g) \<circ>\<^sub>c successor = H \<circ>\<^sub>c (g \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type g_type H_type]])
    have r2: "H \<circ>\<^sub>c (g \<circ>\<^sub>c successor) = H \<circ>\<^sub>c (F \<circ>\<^sub>c g)" using g_square by simp
    have r3: "H \<circ>\<^sub>c (F \<circ>\<^sub>c g) = (H \<circ>\<^sub>c F) \<circ>\<^sub>c g"
      by (rule comp_associative2[OF g_type F_type H_type])
    have r4: "(H \<circ>\<^sub>c F) \<circ>\<^sub>c g = (successor \<circ>\<^sub>c H) \<circ>\<^sub>c g" using HF_eq_sH by simp
    have r5: "(successor \<circ>\<^sub>c H) \<circ>\<^sub>c g = successor \<circ>\<^sub>c (H \<circ>\<^sub>c g)"
      by (rule sym[OF comp_associative2[OF g_type H_type successor_type]])
    show ?thesis using r1 r2 r3 r4 r5 by simp
  qed
  have idsucc: "id(\<nat>\<^sub>c) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id(\<nat>\<^sub>c)"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  have eq1: "H \<circ>\<^sub>c g = id(\<nat>\<^sub>c)"
    using natural_number_object_func_unique[OF Hg_type id_type successor_type Hg_zero Hg_succ idsucc] .
  have eq2: "g \<circ>\<^sub>c H = id(\<one> \<Coprod> \<nat>\<^sub>c)"
  proof -
    have v1: "g \<circ>\<^sub>c H = (g \<circ>\<^sub>c zero) \<amalg> (g \<circ>\<^sub>c successor)"
      unfolding H_def by (rule sym[OF cfunc_coprod_comp[OF g_type zero_type successor_type]])
    have v2: "g \<circ>\<^sub>c zero = i0" using g_triangle by simp
    have v3: "g \<circ>\<^sub>c successor = i1" using i1_eq_gs by simp
    have v4: "g \<circ>\<^sub>c H = i0 \<amalg> i1" using v1 v2 v3 by simp
    have v5: "i0 \<amalg> i1 = left_coproj(\<one>, \<nat>\<^sub>c) \<amalg> right_coproj(\<one>, \<nat>\<^sub>c)"
      using i0_def i1_def by simp
    have v6: "left_coproj(\<one>, \<nat>\<^sub>c) \<amalg> right_coproj(\<one>, \<nat>\<^sub>c) = id(\<one> \<Coprod> \<nat>\<^sub>c)"
      by (rule sym[OF id_coprod])
    show ?thesis using v4 v5 v6 by simp
  qed
  have H_iso: "isomorphism(H)"
    unfolding isomorphism_def3[OF H_type]
    using g_type eq1 eq2 by auto
  show "isomorphism(zero \<amalg> successor)" using H_iso H_def by simp
qed

lemma nonzero_is_succ:
  assumes k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes k_not_zero: "k \<noteq> zero"
  shows "\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> k = successor \<circ>\<^sub>c n"
proof -
  have H_type[type_rule]: "zero \<amalg> successor : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have H_iso[type_rule]: "isomorphism(zero \<amalg> successor)" using oneUN_iso_N_isomorphism .
  have inv_facts: "(zero \<amalg> successor)\<^bold>\<inverse> : codomain(zero \<amalg> successor) \<rightarrow> domain(zero \<amalg> successor)
                  \<and> (zero \<amalg> successor)\<^bold>\<inverse> \<circ>\<^sub>c (zero \<amalg> successor) = id(domain(zero \<amalg> successor))
                  \<and> (zero \<amalg> successor) \<circ>\<^sub>c (zero \<amalg> successor)\<^bold>\<inverse> = id(codomain(zero \<amalg> successor))"
    using inverse_def2[OF H_iso] .
  have dom_H: "domain(zero \<amalg> successor) = \<one> \<Coprod> \<nat>\<^sub>c" using H_type unfolding cfunc_type_def by auto
  have cod_H: "codomain(zero \<amalg> successor) = \<nat>\<^sub>c" using H_type unfolding cfunc_type_def by auto
  have Hinv_type[type_rule]: "(zero \<amalg> successor)\<^bold>\<inverse> : \<nat>\<^sub>c \<rightarrow> (\<one> \<Coprod> \<nat>\<^sub>c)"
    using inv_facts dom_H cod_H unfolding cfunc_type_def by auto
  have H_Hinv: "(zero \<amalg> successor) \<circ>\<^sub>c (zero \<amalg> successor)\<^bold>\<inverse> = id(\<nat>\<^sub>c)"
    using inv_facts cod_H by simp
  define x where x_def: "x = (zero \<amalg> successor)\<^bold>\<inverse> \<circ>\<^sub>c k"
  have x_type[type_rule]: "x \<in>\<^sub>c \<one> \<Coprod> \<nat>\<^sub>c" unfolding x_def by typecheck_cfuncs
  have Hx_eq_k: "(zero \<amalg> successor) \<circ>\<^sub>c x = k"
  proof -
    have w1: "(zero \<amalg> successor) \<circ>\<^sub>c x = ((zero \<amalg> successor) \<circ>\<^sub>c (zero \<amalg> successor)\<^bold>\<inverse>) \<circ>\<^sub>c k"
      unfolding x_def by (rule comp_associative2[OF k_type Hinv_type H_type])
    then show ?thesis using H_Hinv id_left_unit2[OF k_type] by simp
  qed
  have cases: "(\<exists>x1. x1 \<in>\<^sub>c \<one> \<and> x = left_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c x1) \<or> (\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> x = right_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c n)"
    using coprojs_jointly_surj[OF x_type] by simp
  show ?thesis
  proof (rule disjE[OF cases])
    assume "\<exists>x1. x1 \<in>\<^sub>c \<one> \<and> x = left_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c x1"
    then obtain x1 where x1_type[type_rule]: "x1 \<in>\<^sub>c \<one>" and x_eq: "x = left_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c x1"
      by auto
    have x1_eq_id: "x1 = id(\<one>)" using x1_type id_type one_unique_element by auto
    have "k = (zero \<amalg> successor) \<circ>\<^sub>c (left_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c x1)"
      using Hx_eq_k x_eq by simp
    also have "... = (zero \<amalg> successor) \<circ>\<^sub>c (left_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c id(\<one>))"
      using x1_eq_id by simp
    also have "... = ((zero \<amalg> successor) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c)) \<circ>\<^sub>c id(\<one>)"
      by (rule comp_associative2[OF id_type left_proj_type H_type])
    also have "... = zero \<circ>\<^sub>c id(\<one>)"
      using left_coproj_cfunc_coprod[OF zero_type successor_type] by simp
    also have "... = zero" by (typecheck_cfuncs, simp add: id_right_unit2)
    finally have k_eq_zero: "k = zero" .
    then show ?thesis using k_not_zero by auto
  next
    assume "\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> x = right_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c n"
    then obtain n where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and x_eq: "x = right_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c n"
      by auto
    have "k = (zero \<amalg> successor) \<circ>\<^sub>c (right_coproj(\<one>, \<nat>\<^sub>c) \<circ>\<^sub>c n)"
      using Hx_eq_k x_eq by simp
    also have "... = ((zero \<amalg> successor) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c)) \<circ>\<^sub>c n"
      by (rule comp_associative2[OF n_type right_proj_type H_type])
    also have "... = successor \<circ>\<^sub>c n"
      using right_coproj_cfunc_coprod[OF zero_type successor_type] by simp
    finally have k_eq: "k = successor \<circ>\<^sub>c n" .
    show ?thesis using n_type k_eq by auto
  qed
qed

subsection \<open>Predecessor\<close>

definition predecessor' :: "cfunc" where
  "predecessor' = (zero \<amalg> successor)\<^bold>\<inverse>"

lemma predecessor'_def2:
  "predecessor' : \<nat>\<^sub>c \<rightarrow> \<one> \<Coprod> \<nat>\<^sub>c \<and> predecessor' \<circ>\<^sub>c (zero \<amalg> successor) = id(\<one> \<Coprod> \<nat>\<^sub>c)
    \<and> (zero \<amalg> successor) \<circ>\<^sub>c predecessor' = id(\<nat>\<^sub>c)"
proof -
  have H_type[type_rule]: "zero \<amalg> successor : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have H_iso: "isomorphism(zero \<amalg> successor)" using oneUN_iso_N_isomorphism .
  have inv_facts: "(zero \<amalg> successor)\<^bold>\<inverse> : codomain(zero \<amalg> successor) \<rightarrow> domain(zero \<amalg> successor)
                  \<and> (zero \<amalg> successor)\<^bold>\<inverse> \<circ>\<^sub>c (zero \<amalg> successor) = id(domain(zero \<amalg> successor))
                  \<and> (zero \<amalg> successor) \<circ>\<^sub>c (zero \<amalg> successor)\<^bold>\<inverse> = id(codomain(zero \<amalg> successor))"
    using inverse_def2[OF H_iso] .
  have dom_H: "domain(zero \<amalg> successor) = \<one> \<Coprod> \<nat>\<^sub>c" using H_type unfolding cfunc_type_def by auto
  have cod_H: "codomain(zero \<amalg> successor) = \<nat>\<^sub>c" using H_type unfolding cfunc_type_def by auto
  have p_type: "predecessor' : \<nat>\<^sub>c \<rightarrow> \<one> \<Coprod> \<nat>\<^sub>c"
    unfolding predecessor'_def using inv_facts dom_H cod_H unfolding cfunc_type_def by auto
  have p_right: "predecessor' \<circ>\<^sub>c (zero \<amalg> successor) = id(\<one> \<Coprod> \<nat>\<^sub>c)"
    unfolding predecessor'_def using inv_facts dom_H by simp
  have p_left: "(zero \<amalg> successor) \<circ>\<^sub>c predecessor' = id(\<nat>\<^sub>c)"
    unfolding predecessor'_def using inv_facts cod_H by simp
  show ?thesis using p_type p_right p_left by auto
qed

lemma predecessor'_type[type_rule]:
  "predecessor' : \<nat>\<^sub>c \<rightarrow> \<one> \<Coprod> \<nat>\<^sub>c"
  using predecessor'_def2 by auto

lemma predecessor'_left_inv:
  "(zero \<amalg> successor) \<circ>\<^sub>c predecessor' = id(\<nat>\<^sub>c)"
  using predecessor'_def2 by auto

lemma predecessor'_right_inv:
  "predecessor' \<circ>\<^sub>c (zero \<amalg> successor) = id(\<one> \<Coprod> \<nat>\<^sub>c)"
  using predecessor'_def2 by auto

lemma predecessor'_successor:
  "predecessor' \<circ>\<^sub>c successor = right_coproj(\<one>, \<nat>\<^sub>c)"
proof -
  have H_type[type_rule]: "zero \<amalg> successor : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have a1: "predecessor' \<circ>\<^sub>c successor = predecessor' \<circ>\<^sub>c ((zero \<amalg> successor) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c))"
    using right_coproj_cfunc_coprod[OF zero_type successor_type] by simp
  have a2: "predecessor' \<circ>\<^sub>c ((zero \<amalg> successor) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c))
           = (predecessor' \<circ>\<^sub>c (zero \<amalg> successor)) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c)"
    by (rule comp_associative2[OF right_proj_type H_type predecessor'_type])
  have a3: "(predecessor' \<circ>\<^sub>c (zero \<amalg> successor)) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c) = id(\<one> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c)"
    using predecessor'_right_inv by simp
  have a4: "id(\<one> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c) = right_coproj(\<one>, \<nat>\<^sub>c)"
    by (typecheck_cfuncs, simp add: id_left_unit2)
  show ?thesis using a1 a2 a3 a4 by simp
qed

lemma predecessor'_zero:
  "predecessor' \<circ>\<^sub>c zero = left_coproj(\<one>, \<nat>\<^sub>c)"
proof -
  have H_type[type_rule]: "zero \<amalg> successor : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have a1: "predecessor' \<circ>\<^sub>c zero = predecessor' \<circ>\<^sub>c ((zero \<amalg> successor) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c))"
    using left_coproj_cfunc_coprod[OF zero_type successor_type] by simp
  have a2: "predecessor' \<circ>\<^sub>c ((zero \<amalg> successor) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c))
           = (predecessor' \<circ>\<^sub>c (zero \<amalg> successor)) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c)"
    by (rule comp_associative2[OF left_proj_type H_type predecessor'_type])
  have a3: "(predecessor' \<circ>\<^sub>c (zero \<amalg> successor)) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c) = id(\<one> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c)"
    using predecessor'_right_inv by simp
  have a4: "id(\<one> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c) = left_coproj(\<one>, \<nat>\<^sub>c)"
    by (typecheck_cfuncs, simp add: id_left_unit2)
  show ?thesis using a1 a2 a3 a4 by simp
qed

definition predecessor :: "cfunc" where
  "predecessor = (zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c predecessor'"

lemma predecessor_type[type_rule]:
  "predecessor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  unfolding predecessor_def by typecheck_cfuncs

lemma predecessor_zero:
  "predecessor \<circ>\<^sub>c zero = zero"
proof -
  have zi_type[type_rule]: "zero \<amalg> id(\<nat>\<^sub>c) : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have a1: "predecessor \<circ>\<^sub>c zero = (zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c (predecessor' \<circ>\<^sub>c zero)"
    unfolding predecessor_def by (rule sym[OF comp_associative2[OF zero_type predecessor'_type zi_type]])
  have a2: "predecessor' \<circ>\<^sub>c zero = left_coproj(\<one>, \<nat>\<^sub>c)" using predecessor'_zero .
  have a3: "(zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c (predecessor' \<circ>\<^sub>c zero) = (zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c)"
    using a2 by simp
  have a4: "(zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c left_coproj(\<one>, \<nat>\<^sub>c) = zero"
    by (rule left_coproj_cfunc_coprod[OF zero_type id_type])
  show ?thesis using a1 a3 a4 by simp
qed

lemma predecessor_successor:
  "predecessor \<circ>\<^sub>c successor = id(\<nat>\<^sub>c)"
proof -
  have zi_type[type_rule]: "zero \<amalg> id(\<nat>\<^sub>c) : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have b1: "predecessor \<circ>\<^sub>c successor = (zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c (predecessor' \<circ>\<^sub>c successor)"
    unfolding predecessor_def by (rule sym[OF comp_associative2[OF successor_type predecessor'_type zi_type]])
  have b2: "predecessor' \<circ>\<^sub>c successor = right_coproj(\<one>, \<nat>\<^sub>c)" using predecessor'_successor .
  have b3: "(zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c (predecessor' \<circ>\<^sub>c successor) = (zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c)"
    using b2 by simp
  have b4: "(zero \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c) = id(\<nat>\<^sub>c)"
    by (rule right_coproj_cfunc_coprod[OF zero_type id_type])
  show ?thesis using b1 b3 b4 by simp
qed

subsection \<open>Peano's Axioms and Induction\<close>

text \<open>The lemma below corresponds to Proposition 2.6.7 in Halvorson.\<close>
lemma Peano's_Axioms:
 "injective(successor) \<and> \<not> surjective(successor)"
proof -
  have i1_mono: "monomorphism(right_coproj(\<one>, \<nat>\<^sub>c))"
    by (rule right_coproj_are_monomorphisms)
  have H_type[type_rule]: "zero \<amalg> successor : (\<one> \<Coprod> \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have zUsi1EqsS: "(zero \<amalg> successor) \<circ>\<^sub>c right_coproj(\<one>, \<nat>\<^sub>c) = successor"
    by (rule right_coproj_cfunc_coprod[OF zero_type successor_type])
  have H_iso: "isomorphism(zero \<amalg> successor)" using oneUN_iso_N_isomorphism .
  have H_mono: "monomorphism(zero \<amalg> successor)" using H_iso iso_imp_epi_and_monic by auto
  have cod_dom: "codomain(right_coproj(\<one>, \<nat>\<^sub>c)) = domain(zero \<amalg> successor)"
    using right_proj_type H_type unfolding cfunc_type_def by auto
  have succ_mono: "monomorphism(successor)"
    using composition_of_monic_pair_is_monic[OF cod_dom i1_mono H_mono] zUsi1EqsS by simp
  have succ_inj: "injective(successor)"
    using monomorphism_imp_injective[OF succ_mono] .
  have s_not_surj: "\<not> surjective(successor)"
  proof
    assume BWOC: "surjective(successor)"
    have all_y: "\<forall>y. y \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> (\<exists>x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> successor \<circ>\<^sub>c x = y)"
      using iffD1[OF surjective_def2[OF successor_type] BWOC] .
    obtain n where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and snEqz: "successor \<circ>\<^sub>c n = zero"
      using all_y zero_type by auto
    show False using snEqz zero_is_not_successor[OF n_type] by auto
  qed
  show "injective(successor) \<and> \<not> surjective(successor)" using succ_inj s_not_surj by auto
qed

lemma succ_inject:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes eq: "successor \<circ>\<^sub>c n = successor \<circ>\<^sub>c m"
  shows "n = m"
proof -
  have inj: "injective(successor)" using Peano's_Axioms by auto
  have all_eq: "\<forall>x y. x \<in>\<^sub>c \<nat>\<^sub>c \<and> y \<in>\<^sub>c \<nat>\<^sub>c \<and> successor \<circ>\<^sub>c x = successor \<circ>\<^sub>c y \<longrightarrow> x = y"
    using injective_def2[OF successor_type] inj by auto
  show "n = m" using all_eq n_type m_type eq by auto
qed

theorem nat_induction:
  assumes p_type[type_rule]: "p : \<nat>\<^sub>c \<rightarrow> \<Omega>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes base_case: "p \<circ>\<^sub>c zero = \<t>"
  assumes induction_case: "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> p \<circ>\<^sub>c n = \<t> \<Longrightarrow> p \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
  shows "p \<circ>\<^sub>c n = \<t>"
proof -
  have tb_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  obtain P p' where
    p'_type[type_rule]: "p' : P \<rightarrow> \<nat>\<^sub>c" and
    p'_equalizer: "p \<circ>\<^sub>c p' = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p'" and
    p'_uni_prop: "\<forall> h F. (h : F \<rightarrow> \<nat>\<^sub>c \<and> p \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c h) \<longrightarrow> (\<exists>! k. k : F \<rightarrow> P \<and> p' \<circ>\<^sub>c k = h)"
    using equalizer_exists2[OF p_type tb_type] by auto

  have base_eq: "p \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
  proof -
    have c1: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type terminal_func_type true_func_type]])
    have c2: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero = id(\<one>)" by (rule terminal_func_comp_elem[OF zero_type])
    have c3: "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero) = \<t> \<circ>\<^sub>c id(\<one>)" using c2 by simp
    have c4: "\<t> \<circ>\<^sub>c id(\<one>) = \<t>" by (typecheck_cfuncs, simp add: id_right_unit2)
    show ?thesis using base_case c1 c3 c4 by simp
  qed
  have ex1_z: "\<exists>!k. k : \<one> \<rightarrow> P \<and> p' \<circ>\<^sub>c k = zero"
    using p'_uni_prop zero_type base_eq by auto
  obtain z' where z'_type[type_rule]: "z' \<in>\<^sub>c P" and z'_eq: "p' \<circ>\<^sub>c z' = zero"
    using ex1_z by auto
  have z'_def: "zero = p' \<circ>\<^sub>c z'" using z'_eq by simp

  have succp'_type[type_rule]: "successor \<circ>\<^sub>c p' : P \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have succ_p'_eq: "p \<circ>\<^sub>c (successor \<circ>\<^sub>c p') = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c p')"
  proof (etcs_rule one_separator)
    fix m
    assume m_type[type_rule]: "m \<in>\<^sub>c P"
    have pm_type[type_rule]: "p' \<circ>\<^sub>c m \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
    have d1: "(p \<circ>\<^sub>c p') \<circ>\<^sub>c m = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p') \<circ>\<^sub>c m"
      using p'_equalizer by simp
    have d2: "p \<circ>\<^sub>c (p' \<circ>\<^sub>c m) = (p \<circ>\<^sub>c p') \<circ>\<^sub>c m"
      by (rule comp_associative2[OF m_type p'_type p_type])
    have d3: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p') \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p' \<circ>\<^sub>c m)"
      by (rule sym[OF comp_associative2[OF m_type p'_type tb_type]])
    have d4: "p \<circ>\<^sub>c (p' \<circ>\<^sub>c m) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p' \<circ>\<^sub>c m))"
    proof -
      have "p \<circ>\<^sub>c (p' \<circ>\<^sub>c m) = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p' \<circ>\<^sub>c m)" using d1 d2 d3 by simp
      also have "... = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p' \<circ>\<^sub>c m))"
        by (rule sym[OF comp_associative2[OF pm_type terminal_func_type true_func_type]])
      finally show ?thesis .
    qed
    have d5': "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p' \<circ>\<^sub>c m) = id(\<one>)" using terminal_func_comp_elem[OF pm_type] .
    have d5: "p \<circ>\<^sub>c (p' \<circ>\<^sub>c m) = \<t>"
    proof -
      have "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p' \<circ>\<^sub>c m)) = \<t> \<circ>\<^sub>c id(\<one>)" using d5' by simp
      also have "... = \<t>" by (typecheck_cfuncs, simp add: id_right_unit2)
      finally show ?thesis using d4 by simp
    qed
    have d6: "p \<circ>\<^sub>c (successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m)) = \<t>"
      using induction_case[OF pm_type d5] .
    have e1: "(p \<circ>\<^sub>c (successor \<circ>\<^sub>c p')) \<circ>\<^sub>c m = p \<circ>\<^sub>c ((successor \<circ>\<^sub>c p') \<circ>\<^sub>c m)"
      by (rule sym[OF comp_associative2[OF m_type succp'_type p_type]])
    have e2: "(successor \<circ>\<^sub>c p') \<circ>\<^sub>c m = successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m)"
      by (rule sym[OF comp_associative2[OF m_type p'_type successor_type]])
    have e3: "(p \<circ>\<^sub>c (successor \<circ>\<^sub>c p')) \<circ>\<^sub>c m = \<t>" using e1 e2 d6 by simp
    have snm_type[type_rule]: "successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m) \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
    have f1: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c p')) \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c p') \<circ>\<^sub>c m)"
      by (rule sym[OF comp_associative2[OF m_type succp'_type tb_type]])
    have f2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c p') \<circ>\<^sub>c m) = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m))"
      using e2 by simp
    have f3: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m)) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m)))"
      by (rule sym[OF comp_associative2[OF snm_type terminal_func_type true_func_type]])
    have f4: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m)) = id(\<one>)"
      using terminal_func_comp_elem[OF snm_type] .
    have f5: "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c (p' \<circ>\<^sub>c m))) = \<t> \<circ>\<^sub>c id(\<one>)" using f4 by simp
    have f6: "\<t> \<circ>\<^sub>c id(\<one>) = \<t>" by (typecheck_cfuncs, simp add: id_right_unit2)
    have f7: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c p')) \<circ>\<^sub>c m = \<t>" using f1 f2 f3 f5 f6 by simp
    show "(p \<circ>\<^sub>c successor \<circ>\<^sub>c p') \<circ>\<^sub>c m = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor \<circ>\<^sub>c p') \<circ>\<^sub>c m"
      using e3 f7 by simp
  qed
  have ex1_s: "\<exists>!k. k : P \<rightarrow> P \<and> p' \<circ>\<^sub>c k = successor \<circ>\<^sub>c p'"
    using p'_uni_prop succp'_type succ_p'_eq by auto
  obtain s' where s'_type[type_rule]: "s' : P \<rightarrow> P" and s'_def: "p' \<circ>\<^sub>c s' = successor \<circ>\<^sub>c p'"
    using ex1_s by auto

  obtain u where u_type[type_rule]: "u : \<nat>\<^sub>c \<rightarrow> P" and u_zero: "u \<circ>\<^sub>c zero = z'" and u_succ: "u \<circ>\<^sub>c successor = s' \<circ>\<^sub>c u"
    using natural_number_object_property2[OF z'_type s'_type] by auto

  have p'u_type[type_rule]: "p' \<circ>\<^sub>c u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have g1: "(p' \<circ>\<^sub>c u) \<circ>\<^sub>c zero = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero"
  proof -
    have "(p' \<circ>\<^sub>c u) \<circ>\<^sub>c zero = p' \<circ>\<^sub>c (u \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type u_type p'_type]])
    also have "... = p' \<circ>\<^sub>c z'" using u_zero by simp
    also have "... = zero" using z'_def by simp
    also have "... = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero" using id_left_unit2[OF zero_type] by simp
    finally show ?thesis .
  qed
  have g2: "(p' \<circ>\<^sub>c u) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c (p' \<circ>\<^sub>c u)"
  proof -
    have "(p' \<circ>\<^sub>c u) \<circ>\<^sub>c successor = p' \<circ>\<^sub>c (u \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type u_type p'_type]])
    also have "... = p' \<circ>\<^sub>c (s' \<circ>\<^sub>c u)" using u_succ by simp
    also have "... = (p' \<circ>\<^sub>c s') \<circ>\<^sub>c u"
      by (rule comp_associative2[OF u_type s'_type p'_type])
    also have "... = (successor \<circ>\<^sub>c p') \<circ>\<^sub>c u" using s'_def by simp
    also have "... = successor \<circ>\<^sub>c (p' \<circ>\<^sub>c u)"
      by (rule sym[OF comp_associative2[OF u_type p'_type successor_type]])
    finally show ?thesis .
  qed
  have g3: "id(\<nat>\<^sub>c) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id(\<nat>\<^sub>c)"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  have p'_u_is_id: "p' \<circ>\<^sub>c u = id(\<nat>\<^sub>c)"
    using natural_number_object_func_unique[OF p'u_type id_type successor_type g1 g2 g3] .

  have h1: "p \<circ>\<^sub>c (p' \<circ>\<^sub>c (u \<circ>\<^sub>c n)) = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p' \<circ>\<^sub>c (u \<circ>\<^sub>c n))"
  proof -
    have un_type[type_rule]: "u \<circ>\<^sub>c n \<in>\<^sub>c P" by typecheck_cfuncs
    have h1a: "p \<circ>\<^sub>c (p' \<circ>\<^sub>c (u \<circ>\<^sub>c n)) = (p \<circ>\<^sub>c p') \<circ>\<^sub>c (u \<circ>\<^sub>c n)"
      by (rule comp_associative2[OF un_type p'_type p_type])
    have h1b: "(p \<circ>\<^sub>c p') \<circ>\<^sub>c (u \<circ>\<^sub>c n) = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p') \<circ>\<^sub>c (u \<circ>\<^sub>c n)"
      using p'_equalizer by simp
    have h1c: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c p') \<circ>\<^sub>c (u \<circ>\<^sub>c n) = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p' \<circ>\<^sub>c (u \<circ>\<^sub>c n))"
      by (rule sym[OF comp_associative2[OF un_type p'_type tb_type]])
    show ?thesis using h1a h1b h1c by simp
  qed
  have h2: "p' \<circ>\<^sub>c (u \<circ>\<^sub>c n) = n"
  proof -
    have "p' \<circ>\<^sub>c (u \<circ>\<^sub>c n) = (p' \<circ>\<^sub>c u) \<circ>\<^sub>c n"
      by (rule comp_associative2[OF n_type u_type p'_type])
    also have "... = id(\<nat>\<^sub>c) \<circ>\<^sub>c n" using p'_u_is_id by simp
    also have "... = n" using id_left_unit2[OF n_type] by simp
    finally show ?thesis .
  qed
  have h3: "p \<circ>\<^sub>c n = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n" using h1 h2 by simp
  have h4: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)"
    by (rule sym[OF comp_associative2[OF n_type terminal_func_type true_func_type]])
  have h5: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n = id(\<one>)" using terminal_func_comp_elem[OF n_type] .
  have h6: "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n) = \<t> \<circ>\<^sub>c id(\<one>)" using h5 by simp
  have h7: "\<t> \<circ>\<^sub>c id(\<one>) = \<t>" by (typecheck_cfuncs, simp add: id_right_unit2)
  show "p \<circ>\<^sub>c n = \<t>" using h3 h4 h6 h7 by simp
qed

subsection \<open>Function Iteration\<close>

text \<open>HOL's @{text THE}-based definition is replaced by its uniquely determined Skolem
  specification, exactly as for @{text inverse}, @{text cnufatem}, etc.: existence and
  uniqueness of the witness are guaranteed for the specific @{text q}/@{text f} below by
  @{thm natural_number_object_property2}, so axiomatizing the witness directly is a
  conservative extension.\<close>
axiomatization ITER_curried :: "cset \<Rightarrow> cfunc" where
  ITER_curried_spec: "ITER_curried(U) : \<nat>\<^sub>c \<rightarrow> (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<and>
    ITER_curried(U) \<circ>\<^sub>c zero = (metafunc(id(U)) \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>))\<^sup>\<sharp> \<and>
    (meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp> \<circ>\<^sub>c ITER_curried(U) = ITER_curried(U) \<circ>\<^sub>c successor"

lemma ITER_curried_type[type_rule]:
  "ITER_curried(U) : \<nat>\<^sub>c \<rightarrow> (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>"
  using ITER_curried_spec by auto

lemma ITER_curried_zero:
  "ITER_curried(U) \<circ>\<^sub>c zero = (metafunc(id(U)) \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>))\<^sup>\<sharp>"
  using ITER_curried_spec by auto

lemma ITER_curried_successor:
  "(meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp> \<circ>\<^sub>c ITER_curried(U) = ITER_curried(U) \<circ>\<^sub>c successor"
  using ITER_curried_spec by auto

definition ITER :: "cset \<Rightarrow> cfunc" where
  "ITER(U) = (ITER_curried(U))\<^sup>\<flat>"

lemma ITER_type[type_rule]:
  "ITER(U) : ((U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> (U\<^bsup>U\<^esup>)"
  unfolding ITER_def by typecheck_cfuncs

lemma ITER_zero:
  assumes f_type[type_rule]: "f : Z \<rightarrow> (U\<^bsup>U\<^esup>)"
  shows "ITER(U) \<circ>\<^sub>c \<langle>f, zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> = metafunc(id(U)) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>"
proof (etcs_rule one_separator)
  fix z
  assume z_type[type_rule]: "z \<in>\<^sub>c Z"
  define g where g_def: "g = (left_cart_proj(U, \<one>))\<^sup>\<sharp> \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>)"
  have g_type[type_rule]: "g : (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<one> \<rightarrow> U\<^bsup>U\<^esup>" unfolding g_def by typecheck_cfuncs
  define W where W_def: "W = g\<^sup>\<sharp>"
  have W_type[type_rule]: "W : \<one> \<rightarrow> (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>" unfolding W_def by typecheck_cfuncs
  have id1_type[type_rule]: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have fz_pair_type[type_rule]: "\<langle>f, zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> : Z \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
  have fz_elem_type[type_rule]: "f \<circ>\<^sub>c z \<in>\<^sub>c U\<^bsup>U\<^esup>" by typecheck_cfuncs

  have s1: "(ITER(U) \<circ>\<^sub>c \<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle>) \<circ>\<^sub>c z = ITER(U) \<circ>\<^sub>c (\<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> \<circ>\<^sub>c z)"
    by (rule sym[OF comp_associative2[OF z_type fz_pair_type ITER_type]])
  have s2a: "\<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> \<circ>\<^sub>c z = \<langle>f \<circ>\<^sub>c z, (zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>) \<circ>\<^sub>c z\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have s2b: "(zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>) \<circ>\<^sub>c z = zero \<circ>\<^sub>c (\<beta>\<^bsub>Z\<^esub> \<circ>\<^sub>c z)"
    by (rule sym[OF comp_associative2[OF z_type terminal_func_type zero_type]])
  have s2c: "\<beta>\<^bsub>Z\<^esub> \<circ>\<^sub>c z = id(\<one>)" using terminal_func_comp_elem[OF z_type] .
  have s2d: "zero \<circ>\<^sub>c id(\<one>) = zero" using id_right_unit2[OF zero_type] .
  have s2: "\<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle> \<circ>\<^sub>c z = \<langle>f \<circ>\<^sub>c z, zero\<rangle>"
    using s2a s2b s2c s2d by simp

  have idIC_type[type_rule]: "id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U) : (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>"
    by typecheck_cfuncs
  have eval_type[type_rule]: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> U\<^bsup>U\<^esup>"
    by typecheck_cfuncs
  have fz_zero_type[type_rule]: "\<langle>f \<circ>\<^sub>c z, zero\<rangle> \<in>\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs

  have t1: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle> = (ITER_curried(U))\<^sup>\<flat> \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle>"
    unfolding ITER_def by simp
  have t2: "(ITER_curried(U))\<^sup>\<flat> = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))"
    by (rule inv_transpose_func_def3[OF ITER_curried_type])
  have t3: "(ITER_curried(U))\<^sup>\<flat> \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle>
           = (eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle>"
    using t2 by simp
  have t4: "(eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle>
           = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle>)"
    by (rule sym[OF comp_associative2[OF fz_zero_type idIC_type eval_type]])
  have s3: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle> = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle>)"
    using t1 t3 t4 by simp

  have s4a: "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle> = \<langle>id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z), ITER_curried(U) \<circ>\<^sub>c zero\<rangle>"
    by (rule cfunc_cross_prod_comp_cfunc_prod[OF fz_elem_type zero_type id_type ITER_curried_type])
  have s4b: "id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z) = f \<circ>\<^sub>c z" using id_left_unit2[OF fz_elem_type] .
  have s4c: "ITER_curried(U) \<circ>\<^sub>c zero = (metafunc(id(U)) \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>))\<^sup>\<sharp>"
    using ITER_curried_zero .
  have s4: "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle>
           = \<langle>f \<circ>\<^sub>c z, (metafunc(id(U)) \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>))\<^sup>\<sharp>\<rangle>"
    using s4a s4b s4c by simp

  have s5a: "metafunc(id(U)) = (id(U) \<circ>\<^sub>c left_cart_proj(U, \<one>))\<^sup>\<sharp>"
    by (rule metafunc_def2[OF id_type])
  have s5b: "id(U) \<circ>\<^sub>c left_cart_proj(U, \<one>) = left_cart_proj(U, \<one>)"
    using id_left_unit2[OF left_cart_proj_type] .
  have s5: "metafunc(id(U)) = (left_cart_proj(U, \<one>))\<^sup>\<sharp>"
    using s5a s5b by simp
  have s6: "(metafunc(id(U)) \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>))\<^sup>\<sharp> = W"
    unfolding W_def g_def using s5 by simp

  have s7: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, zero\<rangle> = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, W\<rangle>"
    using s3 s4 s6 by simp

  have s8a: "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle> = \<langle>id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z), W \<circ>\<^sub>c id(\<one>)\<rangle>"
    by (rule cfunc_cross_prod_comp_cfunc_prod[OF fz_elem_type id1_type id_type W_type])
  have s8b: "W \<circ>\<^sub>c id(\<one>) = W" using id_right_unit2[OF W_type] .
  have s8: "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle> = \<langle>f \<circ>\<^sub>c z, W\<rangle>"
    using s8a s4b s8b by simp

  have iW_type[type_rule]: "id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W : (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<one> \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>" by typecheck_cfuncs
  have fzi_type[type_rule]: "\<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle> \<in>\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<one>" by typecheck_cfuncs

  have s9: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, W\<rangle> = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>)"
    using s8 by simp
  have s10: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>)
           = (eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>"
    by (rule comp_associative2[OF fzi_type iW_type eval_type])
  have s11: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W) = g"
    unfolding W_def by (rule transpose_func_def[OF g_type])
  have s12: "(eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f W)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle> = g \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>"
    using s11 by simp
  have s13: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, W\<rangle> = g \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>"
    using s9 s10 s12 by simp

  have s14a: "g \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle> = ((left_cart_proj(U, \<one>))\<^sup>\<sharp> \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>"
    unfolding g_def by simp
  have lcp_type[type_rule]: "(left_cart_proj(U, \<one>))\<^sup>\<sharp> : \<one> \<rightarrow> U\<^bsup>U\<^esup>" by typecheck_cfuncs
  have s14b: "((left_cart_proj(U, \<one>))\<^sup>\<sharp> \<circ>\<^sub>c right_cart_proj(U\<^bsup>U\<^esup>, \<one>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>
             = (left_cart_proj(U, \<one>))\<^sup>\<sharp> \<circ>\<^sub>c (right_cart_proj(U\<^bsup>U\<^esup>, \<one>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle>)"
    by (rule sym[OF comp_associative2[OF fzi_type right_cart_proj_type lcp_type]])
  have s14c: "right_cart_proj(U\<^bsup>U\<^esup>, \<one>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle> = id(\<one>)"
    by (rule right_cart_proj_cfunc_prod[OF fz_elem_type id1_type])
  have s14d: "(left_cart_proj(U, \<one>))\<^sup>\<sharp> \<circ>\<^sub>c id(\<one>) = (left_cart_proj(U, \<one>))\<^sup>\<sharp>"
    using id_right_unit2[OF lcp_type] .
  have s14: "g \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, id(\<one>)\<rangle> = (left_cart_proj(U, \<one>))\<^sup>\<sharp>"
    using s14a s14b s14c s14d by simp

  have s15: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, W\<rangle> = (left_cart_proj(U, \<one>))\<^sup>\<sharp>"
    using s13 s14 by simp
  have s16: "(left_cart_proj(U, \<one>))\<^sup>\<sharp> = metafunc(id(U))" using s5 by simp

  have s17: "(ITER(U) \<circ>\<^sub>c \<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle>) \<circ>\<^sub>c z = metafunc(id(U))"
    using s1 s2 s7 s15 s16 by simp

  have mfid_type[type_rule]: "metafunc(id(U)) \<in>\<^sub>c U\<^bsup>U\<^esup>" using metafunc_type[OF id_type] .
  have s18: "(metafunc(id(U)) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>) \<circ>\<^sub>c z = metafunc(id(U)) \<circ>\<^sub>c (\<beta>\<^bsub>Z\<^esub> \<circ>\<^sub>c z)"
    by (rule sym[OF comp_associative2[OF z_type terminal_func_type mfid_type]])
  have s19: "\<beta>\<^bsub>Z\<^esub> \<circ>\<^sub>c z = id(\<one>)" using s2c .
  have s20: "metafunc(id(U)) \<circ>\<^sub>c id(\<one>) = metafunc(id(U))" using id_right_unit2[OF mfid_type] .
  have s21: "(metafunc(id(U)) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>) \<circ>\<^sub>c z = metafunc(id(U))"
    using s18 s19 s20 by simp

  show "(ITER(U) \<circ>\<^sub>c \<langle>f,zero \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>\<rangle>) \<circ>\<^sub>c z = (metafunc(id(U)) \<circ>\<^sub>c \<beta>\<^bsub>Z\<^esub>) \<circ>\<^sub>c z"
    using s17 s21 by simp
qed

lemma ITER_zero':
  assumes f_type[type_rule]: "f \<in>\<^sub>c (U\<^bsup>U\<^esup>)"
  shows "ITER(U) \<circ>\<^sub>c \<langle>f, zero\<rangle> = metafunc(id(U))"
proof -
  have b1_id: "\<beta>\<^bsub>\<one>\<^esub> = id(\<one>)" by (rule sym[OF terminal_func_unique[OF id_type]])
  have z1: "ITER(U) \<circ>\<^sub>c \<langle>f, zero \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>\<rangle> = metafunc(id(U)) \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub>"
    using ITER_zero[OF f_type] .
  have z2: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = zero" using b1_id id_right_unit2[OF zero_type] by simp
  have z3: "metafunc(id(U)) \<circ>\<^sub>c \<beta>\<^bsub>\<one>\<^esub> = metafunc(id(U))"
    using b1_id id_right_unit2[OF metafunc_type[OF id_type]] by simp
  show ?thesis using z1 z2 z3 by simp
qed

lemma ITER_succ:
  assumes f_type[type_rule]: "f : Z \<rightarrow> (U\<^bsup>U\<^esup>)" and n_type[type_rule]: "n : Z \<rightarrow> \<nat>\<^sub>c"
  shows "ITER(U) \<circ>\<^sub>c \<langle>f, successor \<circ>\<^sub>c n\<rangle> = f \<box> (ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>)"
proof (etcs_rule one_separator)
  fix z
  assume z_type[type_rule]: "z \<in>\<^sub>c Z"
  have sn_type[type_rule]: "successor \<circ>\<^sub>c n : Z \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have fsn_type[type_rule]: "\<langle>f, successor \<circ>\<^sub>c n\<rangle> : Z \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
  have nz_type[type_rule]: "n \<circ>\<^sub>c z \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
  have fz_type[type_rule]: "f \<circ>\<^sub>c z \<in>\<^sub>c (U\<^bsup>U\<^esup>)" by typecheck_cfuncs
  have snz_type[type_rule]: "successor \<circ>\<^sub>c (n \<circ>\<^sub>c z) \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs

  have a1: "(ITER(U) \<circ>\<^sub>c \<langle>f,successor \<circ>\<^sub>c n\<rangle>) \<circ>\<^sub>c z = ITER(U) \<circ>\<^sub>c (\<langle>f,successor \<circ>\<^sub>c n\<rangle> \<circ>\<^sub>c z)"
    by (rule sym[OF comp_associative2[OF z_type fsn_type ITER_type]])
  have a2a: "\<langle>f,successor \<circ>\<^sub>c n\<rangle> \<circ>\<^sub>c z = \<langle>f \<circ>\<^sub>c z, (successor \<circ>\<^sub>c n) \<circ>\<^sub>c z\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have a2b: "(successor \<circ>\<^sub>c n) \<circ>\<^sub>c z = successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)"
    by (rule sym[OF comp_associative2[OF z_type n_type successor_type]])
  have a2: "\<langle>f,successor \<circ>\<^sub>c n\<rangle> \<circ>\<^sub>c z = \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    using a2a a2b by simp
  have a3: "(ITER(U) \<circ>\<^sub>c \<langle>f,successor \<circ>\<^sub>c n\<rangle>) \<circ>\<^sub>c z = ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    using a1 a2 by simp

  have fzsnz_type[type_rule]: "\<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle> \<in>\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
  have idIC_type[type_rule]: "id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U) : (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>"
    by typecheck_cfuncs
  have eval_type[type_rule]: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> U\<^bsup>U\<^esup>"
    by typecheck_cfuncs

  have b1: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle> = (ITER_curried(U))\<^sup>\<flat> \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    unfolding ITER_def by simp
  have b2: "(ITER_curried(U))\<^sup>\<flat> = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))"
    by (rule inv_transpose_func_def3[OF ITER_curried_type])
  have b3: "(ITER_curried(U))\<^sup>\<flat> \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = (eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    using b2 by simp
  have b4: "(eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>)"
    by (rule sym[OF comp_associative2[OF fzsnz_type idIC_type eval_type]])
  have b5: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>)"
    using b1 b3 b4 by simp

  have c1: "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = \<langle>id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z), ITER_curried(U) \<circ>\<^sub>c (successor \<circ>\<^sub>c (n \<circ>\<^sub>c z))\<rangle>"
    by (rule cfunc_cross_prod_comp_cfunc_prod[OF fz_type snz_type id_type ITER_curried_type])
  have c2: "id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z) = f \<circ>\<^sub>c z" using id_left_unit2[OF fz_type] .
  have c3: "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (successor \<circ>\<^sub>c (n \<circ>\<^sub>c z))\<rangle>"
    using c1 c2 by simp
  have b6: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (successor \<circ>\<^sub>c (n \<circ>\<^sub>c z))\<rangle>"
    using b5 c3 by simp

  have d1: "ITER_curried(U) \<circ>\<^sub>c (successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)) = (ITER_curried(U) \<circ>\<^sub>c successor) \<circ>\<^sub>c (n \<circ>\<^sub>c z)"
    by (rule comp_associative2[OF nz_type successor_type ITER_curried_type])
  have d2: "ITER_curried(U) \<circ>\<^sub>c successor =
    (meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp> \<circ>\<^sub>c ITER_curried(U)"
    by (rule sym[OF ITER_curried_successor])
  have d3: "ITER_curried(U) \<circ>\<^sub>c (successor \<circ>\<^sub>c (n \<circ>\<^sub>c z))
    = ((meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp> \<circ>\<^sub>c ITER_curried(U)) \<circ>\<^sub>c (n \<circ>\<^sub>c z)"
    using d1 d2 by simp

  define K where K_def:
    "K = (meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))\<^sup>\<sharp>"
  have K_type[type_rule]: "K : (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>" unfolding K_def by typecheck_cfuncs
  have d3': "ITER_curried(U) \<circ>\<^sub>c (successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)) = (K \<circ>\<^sub>c ITER_curried(U)) \<circ>\<^sub>c (n \<circ>\<^sub>c z)"
    using d3 unfolding K_def by simp
  have d4: "(K \<circ>\<^sub>c ITER_curried(U)) \<circ>\<^sub>c (n \<circ>\<^sub>c z) = K \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z))"
    by (rule sym[OF comp_associative2[OF nz_type ITER_curried_type K_type]])
  have d5: "ITER_curried(U) \<circ>\<^sub>c (successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)) = K \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z))"
    using d3' d4 by simp

  have b7: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, K \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z))\<rangle>"
    using b6 d5 by simp

  have icnz_type[type_rule]: "ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z) \<in>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>" by typecheck_cfuncs
  have kicnz_type[type_rule]: "K \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)) \<in>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>" by typecheck_cfuncs
  have idK_type[type_rule]: "id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>" by typecheck_cfuncs
  have fzicnz_type[type_rule]: "\<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle> \<in>\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>" by typecheck_cfuncs

  have e1: "\<langle>f \<circ>\<^sub>c z, K \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z))\<rangle>
           = (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
  proof -
    have "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
        = \<langle>id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z), K \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z))\<rangle>"
      by (rule cfunc_cross_prod_comp_cfunc_prod[OF fz_type icnz_type id_type K_type])
    then show ?thesis using c2 by simp
  qed

  have b8: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>)"
    using b7 e1 by simp
  have b9: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>)
           = (eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    by (rule comp_associative2[OF fzicnz_type idK_type eval_type])
  have b10: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
           = (eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    using b8 b9 by simp

  have MC_type[type_rule]: "meta_comp(U, U, U) : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>) \<rightarrow> U\<^bsup>U\<^esup>" by typecheck_cfuncs
  have IE_type[type_rule]: "id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)
      : (U\<^bsup>U\<^esup>) \<times>\<^sub>c ((U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>) \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)"
    by typecheck_cfuncs
  have AR_type[type_rule]: "associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      : ((U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c ((U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)"
    by typecheck_cfuncs
  have DI_type[type_rule]: "diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> ((U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>"
    by typecheck_cfuncs
  have AR_DI_type[type_rule]:
    "associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>))
      : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c ((U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)"
    using comp_type[OF DI_type AR_type] .
  have IE_AR_DI_type[type_rule]:
    "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>) \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)))
      : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)"
    using comp_type[OF AR_DI_type IE_type] .
  have KK_def_type[type_rule]:
    "meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>))
      : (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup> \<rightarrow> U\<^bsup>U\<^esup>"
    using comp_type[OF IE_AR_DI_type MC_type] .
  have f1: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f K) =
    meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>))"
    unfolding K_def by (rule transpose_func_def[OF KK_def_type])
  have b11: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
    = (meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
      \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    using b10 f1 by simp

  have h1: "(diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
    = \<langle>diagonal(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z), id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>) \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z))\<rangle>"
    by (rule cfunc_cross_prod_comp_cfunc_prod[OF fz_type icnz_type diagonal_type id_type])
  have h2: "diagonal(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z) = \<langle>f \<circ>\<^sub>c z, f \<circ>\<^sub>c z\<rangle>" using diag_on_elements[OF fz_type] .
  have h3: "id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>) \<circ>\<^sub>c (ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)) = ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)"
    using id_left_unit2[OF icnz_type] .
  have h4: "(diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
    = \<langle>\<langle>f \<circ>\<^sub>c z, f \<circ>\<^sub>c z\<rangle>, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
    using h1 h2 h3 by simp

  have i1: "associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>) \<circ>\<^sub>c \<langle>\<langle>f \<circ>\<^sub>c z, f \<circ>\<^sub>c z\<rangle>, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
    = \<langle>f \<circ>\<^sub>c z, \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>\<rangle>"
    by (rule associate_right_ap[OF fz_type fz_type icnz_type])

  have ffic_type[type_rule]: "\<langle>f \<circ>\<^sub>c z, \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>\<rangle>
      \<in>\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>c ((U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)" by typecheck_cfuncs
  have j1: "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>\<rangle>
    = \<langle>id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z), eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>\<rangle>"
    by (rule cfunc_cross_prod_comp_cfunc_prod[OF fz_type fzicnz_type id_type eval_type])
  have j2: "id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z) = f \<circ>\<^sub>c z" using id_left_unit2[OF fz_type] .

  have k1: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
    = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>)"
  proof -
    have "(id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>
        = \<langle>id(U\<^bsup>U\<^esup>) \<circ>\<^sub>c (f \<circ>\<^sub>c z), ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
      by (rule cfunc_cross_prod_comp_cfunc_prod[OF fz_type nz_type id_type ITER_curried_type])
    then show ?thesis using j2 by simp
  qed
  have fnz_type[type_rule]: "\<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle> \<in>\<^sub>c (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
  have k2a: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle> = (ITER_curried(U))\<^sup>\<flat> \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>"
    unfolding ITER_def by simp
  have k2b: "(ITER_curried(U))\<^sup>\<flat> \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>
    = (eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>"
    using b2 by simp
  have k2c: "(eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>
    = eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>)"
    by (rule sym[OF comp_associative2[OF fnz_type idIC_type eval_type]])
  have k2: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f ITER_curried(U)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>)
    = ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>"
    using k2a k2b k2c by simp
  have k3: "eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle> = ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>"
    using k1 k2 by simp

  have g6: "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
    = meta_comp(U, U, U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>\<rangle>"
  proof -
    have "ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, successor \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>
        = (meta_comp(U, U, U) \<circ>\<^sub>c (id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
          \<circ>\<^sub>c (diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>))) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>"
      using b11 .
    also have "... = meta_comp(U, U, U) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
          \<circ>\<^sub>c ((diagonal(U\<^bsup>U\<^esup>) \<times>\<^sub>f id((U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>)))"
      by (etcs_assocr, simp)
    also have "... = meta_comp(U, U, U) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c (associate_right(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>, (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)
          \<circ>\<^sub>c \<langle>\<langle>f \<circ>\<^sub>c z, f \<circ>\<^sub>c z\<rangle>, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>))"
      using h4 by simp
    also have "... = meta_comp(U, U, U) \<circ>\<^sub>c ((id(U\<^bsup>U\<^esup>) \<times>\<^sub>f eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>)) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>\<rangle>)"
      using i1 by simp
    also have "... = meta_comp(U, U, U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, eval_func(U\<^bsup>U\<^esup>, U\<^bsup>U\<^esup>) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER_curried(U) \<circ>\<^sub>c (n \<circ>\<^sub>c z)\<rangle>\<rangle>"
      using j1 j2 by simp
    also have "... = meta_comp(U, U, U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>\<rangle>"
      using k3 by simp
    finally show ?thesis .
  qed

  have ITERfn_type[type_rule]: "ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle> : Z \<rightarrow> U\<^bsup>U\<^esup>" by typecheck_cfuncs
  have fITERfn_type[type_rule]: "\<langle>f, ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>\<rangle> : Z \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)" by typecheck_cfuncs

  have fn_type[type_rule]: "\<langle>f, n\<rangle> : Z \<rightarrow> (U\<^bsup>U\<^esup>) \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
  have l1: "\<langle>f, ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>\<rangle> \<circ>\<^sub>c z = \<langle>f \<circ>\<^sub>c z, (ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>) \<circ>\<^sub>c z\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have l2: "(ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>) \<circ>\<^sub>c z = ITER(U) \<circ>\<^sub>c (\<langle>f, n\<rangle> \<circ>\<^sub>c z)"
    by (rule sym[OF comp_associative2[OF z_type fn_type ITER_type]])
  have l3: "\<langle>f, n\<rangle> \<circ>\<^sub>c z = \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>" by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have l4: "\<langle>f, ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>\<rangle> \<circ>\<^sub>c z = \<langle>f \<circ>\<^sub>c z, ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>\<rangle>"
    using l1 l2 l3 by simp

  have g7: "meta_comp(U, U, U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, ITER(U) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c z, n \<circ>\<^sub>c z\<rangle>\<rangle>
    = meta_comp(U, U, U) \<circ>\<^sub>c (\<langle>f, ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>\<rangle> \<circ>\<^sub>c z)"
    using l4 by simp
  have g8: "meta_comp(U, U, U) \<circ>\<^sub>c (\<langle>f, ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>\<rangle> \<circ>\<^sub>c z) = (meta_comp(U, U, U) \<circ>\<^sub>c \<langle>f, ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>\<rangle>) \<circ>\<^sub>c z"
    by (rule comp_associative2[OF z_type fITERfn_type meta_comp_type])

  have g9: "(meta_comp(U, U, U) \<circ>\<^sub>c \<langle>f, ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>\<rangle>) \<circ>\<^sub>c z = (f \<box> (ITER(U) \<circ>\<^sub>c \<langle>f, n\<rangle>)) \<circ>\<^sub>c z"
    using meta_comp2_def5[OF f_type ITERfn_type] by simp

  show "(ITER(U) \<circ>\<^sub>c \<langle>f,successor \<circ>\<^sub>c n\<rangle>) \<circ>\<^sub>c z = (f \<box> (ITER(U) \<circ>\<^sub>c \<langle>f,n\<rangle>)) \<circ>\<^sub>c z"
    using a3 g6 g7 g8 g9 by simp
qed

corollary ITER_one:
  assumes f_type[type_rule]: "f \<in>\<^sub>c (U\<^bsup>U\<^esup>)"
  shows "ITER(U) \<circ>\<^sub>c \<langle>f, successor \<circ>\<^sub>c zero\<rangle> = f \<box> (metafunc(id(U)))"
proof -
  have step: "ITER(U) \<circ>\<^sub>c \<langle>f, successor \<circ>\<^sub>c zero\<rangle> = f \<box> (ITER(U) \<circ>\<^sub>c \<langle>f, zero\<rangle>)"
    using ITER_succ[OF f_type zero_type] .
  show ?thesis using step ITER_zero'[OF f_type] by simp
qed

definition iter_comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("_\<^bsup>\<circ>_\<^esup>" [55,0] 55) where
  "g\<^bsup>\<circ>n\<^esup> = cnufatem(ITER(domain(g)) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>)"

lemma iter_comp_type[type_rule]:
  assumes g_type[type_rule]: "g : X \<rightarrow> X"
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "g\<^bsup>\<circ>n\<^esup> : X \<rightarrow> X"
proof -
  have dom_eq: "domain(g) = X" using g_type unfolding cfunc_type_def by auto
  have s1: "ITER(domain(g)) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle> = ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>" using dom_eq by simp
  have s2_type[type_rule]: "ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle> \<in>\<^sub>c X\<^bsup>X\<^esup>" by typecheck_cfuncs
  show ?thesis unfolding iter_comp_def s1 using cnufatem_type[OF s2_type] by simp
qed

lemma iter_comp_def3:
  assumes g_type[type_rule]: "g : X \<rightarrow> X"
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "g\<^bsup>\<circ>n\<^esup> = cnufatem(ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>)"
proof -
  have dom_eq: "domain(g) = X" using g_type unfolding cfunc_type_def by auto
  show ?thesis unfolding iter_comp_def using dom_eq by simp
qed

lemma zero_iters:
  assumes g_type[type_rule]: "g : X \<rightarrow> X"
  shows "g\<^bsup>\<circ>zero\<^esup> = id(X)"
proof (etcs_rule one_separator)
  fix x
  assume x_type[type_rule]: "x \<in>\<^sub>c X"
  have s1: "(g\<^bsup>\<circ>zero\<^esup>) \<circ>\<^sub>c x = cnufatem(ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), zero\<rangle>) \<circ>\<^sub>c x"
    using iter_comp_def3[OF g_type zero_type] by simp
  have s2: "ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), zero\<rangle> = metafunc(id(X))"
    using ITER_zero'[OF metafunc_type[OF g_type]] .
  have s3: "cnufatem(ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), zero\<rangle>) \<circ>\<^sub>c x = cnufatem(metafunc(id(X))) \<circ>\<^sub>c x"
    using s2 by simp
  have s4: "cnufatem(metafunc(id(X))) = id(X)" using cnufatem_metafunc[OF id_type] .
  have s5: "cnufatem(metafunc(id(X))) \<circ>\<^sub>c x = id(X) \<circ>\<^sub>c x" using s4 by simp
  show "(g\<^bsup>\<circ>zero\<^esup>) \<circ>\<^sub>c x = id(X) \<circ>\<^sub>c x" using s1 s3 s5 by simp
qed

lemma succ_iters:
  assumes g_type[type_rule]: "g : X \<rightarrow> X"
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "g\<^bsup>\<circ>(successor \<circ>\<^sub>c n)\<^esup> = g \<circ>\<^sub>c (g\<^bsup>\<circ>n\<^esup>)"
proof -
  have sn_type[type_rule]: "successor \<circ>\<^sub>c n \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
  have mg_type[type_rule]: "metafunc(g) \<in>\<^sub>c X\<^bsup>X\<^esup>" by typecheck_cfuncs
  have s1: "g\<^bsup>\<circ>(successor \<circ>\<^sub>c n)\<^esup> = cnufatem(ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), successor \<circ>\<^sub>c n\<rangle>)"
    using iter_comp_def3[OF g_type sn_type] .
  have s2: "ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), successor \<circ>\<^sub>c n\<rangle> = metafunc(g) \<box> (ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>)"
    using ITER_succ[OF mg_type n_type] .
  have s3: "g\<^bsup>\<circ>(successor \<circ>\<^sub>c n)\<^esup> = cnufatem(metafunc(g) \<box> (ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>))"
    using s1 s2 by simp
  have icn_type[type_rule]: "ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle> \<in>\<^sub>c X\<^bsup>X\<^esup>" by typecheck_cfuncs
  have s4: "metafunc(g\<^bsup>\<circ>n\<^esup>) = ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>"
  proof -
    have "metafunc(g\<^bsup>\<circ>n\<^esup>) = metafunc(cnufatem(ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>))"
      using iter_comp_def3[OF g_type n_type] by simp
    also have "... = ITER(X) \<circ>\<^sub>c \<langle>metafunc(g), n\<rangle>" using metafunc_cnufatem[OF icn_type] .
    finally show ?thesis .
  qed
  have s5: "g\<^bsup>\<circ>(successor \<circ>\<^sub>c n)\<^esup> = cnufatem(metafunc(g) \<box> metafunc(g\<^bsup>\<circ>n\<^esup>))"
    using s3 s4 by simp
  have gn_type[type_rule]: "g\<^bsup>\<circ>n\<^esup> : X \<rightarrow> X" using iter_comp_type[OF g_type n_type] .
  have s6: "g \<circ>\<^sub>c (g\<^bsup>\<circ>n\<^esup>) = cnufatem(metafunc(g) \<box> metafunc(g\<^bsup>\<circ>n\<^esup>))"
    using comp_as_metacomp[OF gn_type g_type] .
  show ?thesis using s5 s6 by simp
qed

corollary one_iter:
  assumes g_type[type_rule]: "g : X \<rightarrow> X"
  shows "g\<^bsup>\<circ>(successor \<circ>\<^sub>c zero)\<^esup> = g"
proof -
  have s1: "g\<^bsup>\<circ>(successor \<circ>\<^sub>c zero)\<^esup> = g \<circ>\<^sub>c (g\<^bsup>\<circ>zero\<^esup>)"
    using succ_iters[OF g_type zero_type] .
  have s2: "g\<^bsup>\<circ>zero\<^esup> = id(X)" using zero_iters[OF g_type] .
  have s3: "g \<circ>\<^sub>c (g\<^bsup>\<circ>zero\<^esup>) = g \<circ>\<^sub>c id(X)" using s2 by simp
  have s4: "g \<circ>\<^sub>c id(X) = g" using id_right_unit2[OF g_type] .
  show ?thesis using s1 s3 s4 by simp
qed

lemma eval_func_cnufatem:
  assumes g_type[type_rule]: "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  assumes x_type[type_rule]: "x \<in>\<^sub>c X"
  shows "eval_func(Y, X) \<circ>\<^sub>c \<langle>x, g\<rangle> = cnufatem(g) \<circ>\<^sub>c x"
proof -
  have gbx_type[type_rule]: "g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> Y\<^bsup>X\<^esup>" by typecheck_cfuncs
  have idgbx_type[type_rule]: "\<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>" by typecheck_cfuncs
  have eval_type2[type_rule]: "eval_func(Y, X) : X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Y" by typecheck_cfuncs
  have s1: "cnufatem(g) = eval_func(Y, X) \<circ>\<^sub>c \<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>" using cnufatem_def2[OF g_type] .
  have s2: "cnufatem(g) \<circ>\<^sub>c x = (eval_func(Y, X) \<circ>\<^sub>c \<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x" using s1 by simp
  have s3: "(eval_func(Y, X) \<circ>\<^sub>c \<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x = eval_func(Y, X) \<circ>\<^sub>c (\<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x)"
    by (rule sym[OF comp_associative2[OF x_type idgbx_type eval_type2]])
  have s4: "\<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = \<langle>id(X) \<circ>\<^sub>c x, (g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have s5: "id(X) \<circ>\<^sub>c x = x" using id_left_unit2[OF x_type] .
  have s6: "(g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = g \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)"
    by (rule sym[OF comp_associative2[OF x_type terminal_func_type g_type]])
  have s7: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = id(\<one>)" using terminal_func_comp_elem[OF x_type] .
  have s8: "g \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x) = g \<circ>\<^sub>c id(\<one>)" using s7 by simp
  have s9: "g \<circ>\<^sub>c id(\<one>) = g" using id_right_unit2[OF g_type] .
  show ?thesis using s2 s3 s4 s5 s6 s8 s9 by simp
qed

lemma eval_lemma_for_ITER:
  assumes f_type[type_rule]: "f : X \<rightarrow> X"
  assumes x_type[type_rule]: "x \<in>\<^sub>c X"
  assumes m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(f\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c x = eval_func(X, X) \<circ>\<^sub>c \<langle>x, ITER(X) \<circ>\<^sub>c \<langle>metafunc(f), m\<rangle>\<rangle>"
proof -
  have k_type[type_rule]: "ITER(X) \<circ>\<^sub>c \<langle>metafunc(f), m\<rangle> \<in>\<^sub>c X\<^bsup>X\<^esup>" by typecheck_cfuncs
  have s1: "(f\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c x = cnufatem(ITER(X) \<circ>\<^sub>c \<langle>metafunc(f), m\<rangle>) \<circ>\<^sub>c x"
    using iter_comp_def3[OF f_type m_type] by simp
  show ?thesis using s1 eval_func_cnufatem[OF k_type x_type] by simp
qed

lemma n_accessible_by_succ_iter_aux:
  "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> = id(\<nat>\<^sub>c)"
proof -
  define Phi where Phi_def:
    "Phi = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle>"
  have Phi_type[type_rule]: "Phi : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" unfolding Phi_def by typecheck_cfuncs

  have base: "Phi \<circ>\<^sub>c zero = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero"
  proof -
    have pair_type[type_rule]: "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
    have ms_type[type_rule]: "metafunc(successor) \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
    have "Phi \<circ>\<^sub>c zero
        = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c zero)"
      unfolding Phi_def by (rule sym[OF comp_associative2[OF zero_type pair_type eval_func_type]])
    also have "... = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero, (ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c zero\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have "... = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), zero\<rangle>\<rangle>"
    proof -
      have e1: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero)"
        by (rule sym[OF comp_associative2[OF zero_type terminal_func_type zero_type]])
      have e2: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero = id(\<one>)" using terminal_func_comp_elem[OF zero_type] .
      have e3: "zero \<circ>\<^sub>c id(\<one>) = zero" using id_right_unit2[OF zero_type] .
      have e4: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = zero" using e1 e2 e3 by simp
      have zic_type[type_rule]: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
      have e5: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c zero
          = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c zero)"
        by (rule sym[OF comp_associative2[OF zero_type zic_type ITER_type]])
      have e6: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c zero
          = \<langle>(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero, id(\<nat>\<^sub>c) \<circ>\<^sub>c zero\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_prod_comp)
      have e7: "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = metafunc(successor)"
      proof -
        have "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = metafunc(successor) \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero)"
          by (rule sym[OF comp_associative2[OF zero_type terminal_func_type ms_type]])
        also have "... = metafunc(successor) \<circ>\<^sub>c id(\<one>)" using e2 by simp
        also have "... = metafunc(successor)" using id_right_unit2[OF ms_type] .
        finally show ?thesis .
      qed
      have e8: "id(\<nat>\<^sub>c) \<circ>\<^sub>c zero = zero" using id_left_unit2[OF zero_type] .
      have e9: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c zero = \<langle>metafunc(successor), zero\<rangle>"
        using e6 e7 e8 by simp
      have e10: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c zero = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), zero\<rangle>"
        using e5 e9 by simp
      show ?thesis using e4 e10 by simp
    qed
    also have "... = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, metafunc(id(\<nat>\<^sub>c))\<rangle>"
      using ITER_zero'[OF ms_type] by simp
    also have "... = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero"
      using eval_lemma[OF id_type zero_type] .
    finally show ?thesis .
  qed

  have succ_case: "Phi \<circ>\<^sub>c successor = successor \<circ>\<^sub>c Phi"
  proof (etcs_rule one_separator)
    fix m
    assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
    have sm_type[type_rule]: "successor \<circ>\<^sub>c m \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
    have K_type[type_rule]: "ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle> \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
    have Kp_type[type_rule]: "ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle> \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
    have smn_type[type_rule]: "successor\<^bsup>\<circ>m\<^esup> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" using iter_comp_type[OF successor_type m_type] .
    have pair_type[type_rule]: "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
    have ms_type[type_rule]: "metafunc(successor) \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs

    have lhs: "(Phi \<circ>\<^sub>c successor) \<circ>\<^sub>c m = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>\<rangle>"
    proof -
      have "(Phi \<circ>\<^sub>c successor) \<circ>\<^sub>c m = Phi \<circ>\<^sub>c (successor \<circ>\<^sub>c m)"
        by (rule sym[OF comp_associative2[OF m_type successor_type Phi_type]])
      also have "... = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c m))"
        unfolding Phi_def by (rule sym[OF comp_associative2[OF sm_type pair_type eval_func_type]])
      also have "... = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>\<rangle>"
      proof -
        have f1: "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c m)
            = \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m), (ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_prod_comp)
        have f2: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m) = zero"
        proof -
          have "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m) = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c m))"
            by (rule sym[OF comp_associative2[OF sm_type terminal_func_type zero_type]])
          also have "... = zero \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF sm_type] by simp
          also have "... = zero" using id_right_unit2[OF zero_type] .
          finally show ?thesis .
        qed
        have f3: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)
            = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>"
        proof -
          have zic_type[type_rule]: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
          have g1: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)
              = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c m))"
            by (rule sym[OF comp_associative2[OF sm_type zic_type ITER_type]])
          have g2: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c m)
              = \<langle>(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m), id(\<nat>\<^sub>c) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp)
          have g3: "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m) = metafunc(successor)"
          proof -
            have "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m) = metafunc(successor) \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c m))"
              by (rule sym[OF comp_associative2[OF sm_type terminal_func_type ms_type]])
            also have "... = metafunc(successor) \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF sm_type] by simp
            also have "... = metafunc(successor)" using id_right_unit2[OF ms_type] .
            finally show ?thesis .
          qed
          have g4: "id(\<nat>\<^sub>c) \<circ>\<^sub>c (successor \<circ>\<^sub>c m) = successor \<circ>\<^sub>c m" using id_left_unit2[OF sm_type] .
          show ?thesis using g1 g2 g3 g4 by simp
        qed
        show ?thesis using f1 f2 f3 by simp
      qed
      finally show ?thesis .
    qed

    have rhs: "(successor \<circ>\<^sub>c Phi) \<circ>\<^sub>c m = successor \<circ>\<^sub>c (eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>\<rangle>)"
    proof -
      have "(successor \<circ>\<^sub>c Phi) \<circ>\<^sub>c m = successor \<circ>\<^sub>c (Phi \<circ>\<^sub>c m)"
        by (rule sym[OF comp_associative2[OF m_type Phi_type successor_type]])
      also have "... = successor \<circ>\<^sub>c (eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c m))"
      proof -
        have "Phi \<circ>\<^sub>c m = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c m)"
          unfolding Phi_def by (rule sym[OF comp_associative2[OF m_type pair_type eval_func_type]])
        then show ?thesis by simp
      qed
      also have "... = successor \<circ>\<^sub>c (eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>\<rangle>)"
      proof -
        have h1: "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c m
            = \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m, (ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c m\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_prod_comp)
        have h2: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m = zero"
        proof -
          have "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)"
            by (rule sym[OF comp_associative2[OF m_type terminal_func_type zero_type]])
          also have "... = zero \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF m_type] by simp
          also have "... = zero" using id_right_unit2[OF zero_type] .
          finally show ?thesis .
        qed
        have h3: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c m = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>"
        proof -
          have zic_type[type_rule]: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
          have k1: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c m
              = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c m)"
            by (rule sym[OF comp_associative2[OF m_type zic_type ITER_type]])
          have k2: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c m
              = \<langle>(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m, id(\<nat>\<^sub>c) \<circ>\<^sub>c m\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp)
          have k3: "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m = metafunc(successor)"
          proof -
            have "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m = metafunc(successor) \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)"
              by (rule sym[OF comp_associative2[OF m_type terminal_func_type ms_type]])
            also have "... = metafunc(successor) \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF m_type] by simp
            also have "... = metafunc(successor)" using id_right_unit2[OF ms_type] .
            finally show ?thesis .
          qed
          have k4: "id(\<nat>\<^sub>c) \<circ>\<^sub>c m = m" using id_left_unit2[OF m_type] .
          show ?thesis using k1 k2 k3 k4 by simp
        qed
        show ?thesis using h1 h2 h3 by simp
      qed
      finally show ?thesis .
    qed

    have K_cn: "cnufatem(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>) = successor\<^bsup>\<circ>m\<^esup>"
      using iter_comp_def3[OF successor_type m_type] by simp
    have Kp_cn: "cnufatem(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>) = successor\<^bsup>\<circ>(successor \<circ>\<^sub>c m)\<^esup>"
      using iter_comp_def3[OF successor_type sm_type] by simp

    have final: "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>\<rangle>
        = successor \<circ>\<^sub>c (eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>\<rangle>)"
    proof -
      have e1: "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>\<rangle>
          = cnufatem(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>) \<circ>\<^sub>c zero"
        using eval_func_cnufatem[OF Kp_type zero_type] .
      have e2: "cnufatem(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), successor \<circ>\<^sub>c m\<rangle>) \<circ>\<^sub>c zero = (successor\<^bsup>\<circ>(successor \<circ>\<^sub>c m)\<^esup>) \<circ>\<^sub>c zero"
        using Kp_cn by simp
      have e3: "successor\<^bsup>\<circ>(successor \<circ>\<^sub>c m)\<^esup> = successor \<circ>\<^sub>c (successor\<^bsup>\<circ>m\<^esup>)"
        using succ_iters[OF successor_type m_type] .
      have e4: "(successor\<^bsup>\<circ>(successor \<circ>\<^sub>c m)\<^esup>) \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c (successor\<^bsup>\<circ>m\<^esup>)) \<circ>\<^sub>c zero"
        using e3 by simp
      have e5: "(successor \<circ>\<^sub>c (successor\<^bsup>\<circ>m\<^esup>)) \<circ>\<^sub>c zero = successor \<circ>\<^sub>c ((successor\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c zero)"
        by (rule sym[OF comp_associative2[OF zero_type smn_type successor_type]])
      have e6: "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>\<rangle> = (successor\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c zero"
      proof -
        have "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>\<rangle>
            = cnufatem(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), m\<rangle>) \<circ>\<^sub>c zero"
          using eval_func_cnufatem[OF K_type zero_type] .
        then show ?thesis using K_cn by simp
      qed
      show ?thesis using e1 e2 e4 e5 e6 by simp
    qed

    show "(Phi \<circ>\<^sub>c successor) \<circ>\<^sub>c m = (successor \<circ>\<^sub>c Phi) \<circ>\<^sub>c m"
      using lhs rhs final by simp
  qed

  have id_succ: "id(\<nat>\<^sub>c) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id(\<nat>\<^sub>c)"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)

  have "Phi = id(\<nat>\<^sub>c)"
    using natural_number_object_func_unique[OF Phi_type id_type successor_type base succ_case id_succ] .
  then show ?thesis unfolding Phi_def by simp
qed

lemma n_accessible_by_succ_iter:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(successor\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c zero = n"
proof -
  have Phi_eq: "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> = id(\<nat>\<^sub>c)"
    using n_accessible_by_succ_iter_aux .
  have pair_type[type_rule]: "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
  have ms_type[type_rule]: "metafunc(successor) \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
  have s1: "n = id(\<nat>\<^sub>c) \<circ>\<^sub>c n" using id_left_unit2[OF n_type] by simp
  have s2a: "id(\<nat>\<^sub>c) \<circ>\<^sub>c n = (eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c n"
    using Phi_eq by simp
  have s2: "id(\<nat>\<^sub>c) \<circ>\<^sub>c n = eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c n)"
    using s2a comp_associative2[OF n_type pair_type eval_func_type] by simp
  have s4: "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c n
      = \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n, (ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c n\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  have s5: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n = zero"
  proof -
    have "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)"
      by (rule sym[OF comp_associative2[OF n_type terminal_func_type zero_type]])
    also have "... = zero \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF n_type] by simp
    also have "... = zero" using id_right_unit2[OF zero_type] .
    finally show ?thesis .
  qed
  have s6: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c n = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), n\<rangle>"
  proof -
    have zic_type[type_rule]: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
    have t1: "(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c n
        = ITER(\<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c n)"
      by (rule sym[OF comp_associative2[OF n_type zic_type ITER_type]])
    have t2: "\<langle>metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id(\<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c n
        = \<langle>(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n, id(\<nat>\<^sub>c) \<circ>\<^sub>c n\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    have t3: "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n = metafunc(successor)"
    proof -
      have "(metafunc(successor) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n = metafunc(successor) \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)"
        by (rule sym[OF comp_associative2[OF n_type terminal_func_type ms_type]])
      also have "... = metafunc(successor) \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF n_type] by simp
      also have "... = metafunc(successor)" using id_right_unit2[OF ms_type] .
      finally show ?thesis .
    qed
    have t4: "id(\<nat>\<^sub>c) \<circ>\<^sub>c n = n" using id_left_unit2[OF n_type] .
    show ?thesis using t1 t2 t3 t4 by simp
  qed
  have s7: "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), n\<rangle>\<rangle> = (successor\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c zero"
  proof -
    have k_type[type_rule]: "ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), n\<rangle> \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>" by typecheck_cfuncs
    have "eval_func(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero, ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), n\<rangle>\<rangle>
        = cnufatem(ITER(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>metafunc(successor), n\<rangle>) \<circ>\<^sub>c zero"
      using eval_func_cnufatem[OF k_type zero_type] .
    also have "... = (successor\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c zero"
      using iter_comp_def3[OF successor_type n_type] by simp
    finally show ?thesis .
  qed
  show ?thesis using s1 s2 s4 s5 s6 s7 by simp
qed

lemma oneUN_iso_N:
  "\<one> \<Coprod> \<nat>\<^sub>c \<cong> \<nat>\<^sub>c"
proof -
  have zs_type: "zero \<amalg> successor : \<one> \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" using cfunc_coprod_type[OF zero_type successor_type] .
  show ?thesis unfolding is_isomorphic_def using zs_type oneUN_iso_N_isomorphism by auto
qed

lemma NUone_iso_N:
  "\<nat>\<^sub>c \<Coprod> \<one> \<cong> \<nat>\<^sub>c"
  using coproduct_commutes isomorphic_is_transitive oneUN_iso_N by blast

end
