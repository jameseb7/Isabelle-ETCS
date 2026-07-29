section \<open>Coproducts\<close>

theory Coproduct
  imports Equivalence
begin

text \<open>The axiomatization below corresponds to Axiom 7 (Coproducts) in Halvorson.\<close>
axiomatization
  coprod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<Coprod>" 65) and
  left_coproj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_coproj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_coprod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<amalg>" 65)
where
  left_proj_type[type_rule]: "left_coproj(X, Y) : X \<rightarrow> X \<Coprod> Y" and
  right_proj_type[type_rule]: "right_coproj(X, Y) : Y \<rightarrow> X \<Coprod> Y" and
  cfunc_coprod_type[type_rule]: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> f \<amalg> g : X \<Coprod> Y \<rightarrow> Z" and
  left_coproj_cfunc_coprod: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> (f \<amalg> g) \<circ>\<^sub>c left_coproj(X, Y) = f" and
  right_coproj_cfunc_coprod: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> (f \<amalg> g) \<circ>\<^sub>c right_coproj(X, Y) = g" and
  cfunc_coprod_unique: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> h : X \<Coprod> Y \<rightarrow> Z \<Longrightarrow>
    h \<circ>\<^sub>c left_coproj(X, Y) = f \<Longrightarrow> h \<circ>\<^sub>c right_coproj(X, Y) = g \<Longrightarrow> h = f \<amalg> g"

text \<open>HOL bundles the coproduct's witness set and two injections into a @{text "cset \<times> cfunc \<times>
  cfunc"} triple, with an @{text is_coprod_triple} abbreviation unpacking it; FOL has no tuple type,
  so @{text is_coprod} simply takes all five arguments directly and call sites list @{text "W, i\<^sub>0,
  i\<^sub>1"} out explicitly instead of bundling them.\<close>
definition is_coprod :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> o" where
  "is_coprod(W, i0, i1, X, Y) \<longleftrightarrow>
    (i0 : X \<rightarrow> W \<and> i1 : Y \<rightarrow> W \<and>
    (\<forall>f g Z. (f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow>
      (\<exists>h. h : W \<rightarrow> Z \<and> h \<circ>\<^sub>c i0 = f \<and> h \<circ>\<^sub>c i1 = g \<and>
        (\<forall>hh. (hh : W \<rightarrow> Z \<and> hh \<circ>\<^sub>c i0 = f \<and> hh \<circ>\<^sub>c i1 = g) \<longrightarrow> hh = h))))"

lemma is_coprod_def2:
  assumes i0_type: "i0 : X \<rightarrow> W" and i1_type: "i1 : Y \<rightarrow> W"
  shows "is_coprod(W, i0, i1, X, Y) \<longleftrightarrow>
    (\<forall>f g Z. (f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow>
      (\<exists>h. h : W \<rightarrow> Z \<and> h \<circ>\<^sub>c i0 = f \<and> h \<circ>\<^sub>c i1 = g \<and>
        (\<forall>hh. (hh : W \<rightarrow> Z \<and> hh \<circ>\<^sub>c i0 = f \<and> hh \<circ>\<^sub>c i1 = g) \<longrightarrow> hh = h)))"
  unfolding is_coprod_def using i0_type i1_type by auto

lemma canonical_coprod_is_coprod:
  "is_coprod(X \<Coprod> Y, left_coproj(X, Y), right_coproj(X, Y), X, Y)"
  unfolding is_coprod_def
proof (intro conjI allI impI)
  show "left_coproj(X, Y) : X \<rightarrow> X \<Coprod> Y" by (rule left_proj_type)
next
  show "right_coproj(X, Y) : Y \<rightarrow> X \<Coprod> Y" by (rule right_proj_type)
next
  fix f g Z
  assume "f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z"
  then have f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z" by auto
  have h_type: "f \<amalg> g : X \<Coprod> Y \<rightarrow> Z" using cfunc_coprod_type[OF f_type g_type] by simp
  have h_left: "(f \<amalg> g) \<circ>\<^sub>c left_coproj(X, Y) = f" using left_coproj_cfunc_coprod[OF f_type g_type] by simp
  have h_right: "(f \<amalg> g) \<circ>\<^sub>c right_coproj(X, Y) = g" using right_coproj_cfunc_coprod[OF f_type g_type] by simp
  have h_uniq: "\<forall>hh. hh : X \<Coprod> Y \<rightarrow> Z \<and> hh \<circ>\<^sub>c left_coproj(X, Y) = f \<and> hh \<circ>\<^sub>c right_coproj(X, Y) = g
      \<longrightarrow> hh = f \<amalg> g"
  proof (intro allI impI)
    fix hh
    assume "hh : X \<Coprod> Y \<rightarrow> Z \<and> hh \<circ>\<^sub>c left_coproj(X, Y) = f \<and> hh \<circ>\<^sub>c right_coproj(X, Y) = g"
    then show "hh = f \<amalg> g"
      using cfunc_coprod_unique[OF f_type g_type] by auto
  qed
  have witness: "f \<amalg> g : X \<Coprod> Y \<rightarrow> Z \<and> (f \<amalg> g) \<circ>\<^sub>c left_coproj(X, Y) = f \<and> (f \<amalg> g) \<circ>\<^sub>c right_coproj(X, Y) = g \<and>
      (\<forall>hh. hh : X \<Coprod> Y \<rightarrow> Z \<and> hh \<circ>\<^sub>c left_coproj(X, Y) = f \<and> hh \<circ>\<^sub>c right_coproj(X, Y) = g \<longrightarrow> hh = f \<amalg> g)"
  proof (intro conjI)
    show "f \<amalg> g : X \<Coprod> Y \<rightarrow> Z" by (rule h_type)
  next
    show "(f \<amalg> g) \<circ>\<^sub>c left_coproj(X, Y) = f" by (rule h_left)
  next
    show "(f \<amalg> g) \<circ>\<^sub>c right_coproj(X, Y) = g" by (rule h_right)
  next
    show "\<forall>hh. hh : X \<Coprod> Y \<rightarrow> Z \<and> hh \<circ>\<^sub>c left_coproj(X, Y) = f \<and> hh \<circ>\<^sub>c right_coproj(X, Y) = g \<longrightarrow> hh = f \<amalg> g"
      by (rule h_uniq)
  qed
  show "\<exists>h. h : X \<Coprod> Y \<rightarrow> Z \<and> h \<circ>\<^sub>c left_coproj(X, Y) = f \<and> h \<circ>\<^sub>c right_coproj(X, Y) = g \<and>
      (\<forall>hh. hh : X \<Coprod> Y \<rightarrow> Z \<and> hh \<circ>\<^sub>c left_coproj(X, Y) = f \<and> hh \<circ>\<^sub>c right_coproj(X, Y) = g \<longrightarrow> hh = h)"
    by (rule exI[where x="f \<amalg> g"], rule witness)
qed

text \<open>The lemma below is dual to Proposition 2.1.8 in Halvorson.\<close>
lemma coprods_isomorphic:
  assumes W_coprod: "is_coprod(W, i0, i1, X, Y)"
  assumes W'_coprod: "is_coprod(W', i0', i1', X, Y)"
  shows "\<exists>g. g : W \<rightarrow> W' \<and> isomorphism(g) \<and> g \<circ>\<^sub>c i0 = i0' \<and> g \<circ>\<^sub>c i1 = i1'"
proof -
  have i0_type: "i0 : X \<rightarrow> W" using W_coprod unfolding is_coprod_def by auto
  have i1_type: "i1 : Y \<rightarrow> W" using W_coprod unfolding is_coprod_def by auto
  have i0'_type: "i0' : X \<rightarrow> W'" using W'_coprod unfolding is_coprod_def by auto
  have i1'_type: "i1' : Y \<rightarrow> W'" using W'_coprod unfolding is_coprod_def by auto

  have W_univ: "\<forall>f g Z. (f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow>
      (\<exists>h. h : W \<rightarrow> Z \<and> h \<circ>\<^sub>c i0 = f \<and> h \<circ>\<^sub>c i1 = g \<and>
        (\<forall>hh. (hh : W \<rightarrow> Z \<and> hh \<circ>\<^sub>c i0 = f \<and> hh \<circ>\<^sub>c i1 = g) \<longrightarrow> hh = h))"
    using W_coprod unfolding is_coprod_def by auto
  have W'_univ: "\<forall>f g Z. (f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow>
      (\<exists>h. h : W' \<rightarrow> Z \<and> h \<circ>\<^sub>c i0' = f \<and> h \<circ>\<^sub>c i1' = g \<and>
        (\<forall>hh. (hh : W' \<rightarrow> Z \<and> hh \<circ>\<^sub>c i0' = f \<and> hh \<circ>\<^sub>c i1' = g) \<longrightarrow> hh = h))"
    using W'_coprod unfolding is_coprod_def by auto

  obtain g where g_type: "g : W \<rightarrow> W'" and g0: "g \<circ>\<^sub>c i0 = i0'" and g1: "g \<circ>\<^sub>c i1 = i1'"
    using W_univ[rule_format, where f=i0' and g=i1' and Z=W'] i0'_type i1'_type by auto
  obtain f where f_type: "f : W' \<rightarrow> W" and f0: "f \<circ>\<^sub>c i0' = i0" and f1: "f \<circ>\<^sub>c i1' = i1"
    using W'_univ[rule_format, where f=i0 and g=i1 and Z=W] i0_type i1_type by auto

  have fg0: "(f \<circ>\<^sub>c g) \<circ>\<^sub>c i0 = i0"
  proof -
    have "(f \<circ>\<^sub>c g) \<circ>\<^sub>c i0 = f \<circ>\<^sub>c (g \<circ>\<^sub>c i0)" using comp_associative2[OF i0_type g_type f_type] by simp
    also have "... = f \<circ>\<^sub>c i0'" using g0 by simp
    also have "... = i0" using f0 by simp
    finally show ?thesis by simp
  qed
  have fg1: "(f \<circ>\<^sub>c g) \<circ>\<^sub>c i1 = i1"
  proof -
    have "(f \<circ>\<^sub>c g) \<circ>\<^sub>c i1 = f \<circ>\<^sub>c (g \<circ>\<^sub>c i1)" using comp_associative2[OF i1_type g_type f_type] by simp
    also have "... = f \<circ>\<^sub>c i1'" using g1 by simp
    also have "... = i1" using f1 by simp
    finally show ?thesis by simp
  qed

  obtain hW where hW_type: "hW : W \<rightarrow> W" and hW0: "hW \<circ>\<^sub>c i0 = i0" and hW1: "hW \<circ>\<^sub>c i1 = i1"
      and hW_uniq: "\<forall>hh. hh : W \<rightarrow> W \<and> hh \<circ>\<^sub>c i0 = i0 \<and> hh \<circ>\<^sub>c i1 = i1 \<longrightarrow> hh = hW"
    using W_univ[rule_format, where f=i0 and g=i1 and Z=W] i0_type i1_type by auto
  have fg_type: "f \<circ>\<^sub>c g : W \<rightarrow> W" using g_type f_type comp_type by blast
  have fg_eq_hW: "f \<circ>\<^sub>c g = hW" using hW_uniq[rule_format, where hh="f \<circ>\<^sub>c g"] fg_type fg0 fg1 by auto
  have idW_type: "id(W) : W \<rightarrow> W" by (rule id_type)
  have idW0: "id(W) \<circ>\<^sub>c i0 = i0" using id_left_unit2[OF i0_type] by simp
  have idW1: "id(W) \<circ>\<^sub>c i1 = i1" using id_left_unit2[OF i1_type] by simp
  have idW_eq_hW: "id(W) = hW" using hW_uniq[rule_format, where hh="id(W)"] idW_type idW0 idW1 by auto
  have fg: "f \<circ>\<^sub>c g = id(W)" using fg_eq_hW idW_eq_hW by simp

  have gf0: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c i0' = i0'"
  proof -
    have "(g \<circ>\<^sub>c f) \<circ>\<^sub>c i0' = g \<circ>\<^sub>c (f \<circ>\<^sub>c i0')" using comp_associative2[OF i0'_type f_type g_type] by simp
    also have "... = g \<circ>\<^sub>c i0" using f0 by simp
    also have "... = i0'" using g0 by simp
    finally show ?thesis by simp
  qed
  have gf1: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c i1' = i1'"
  proof -
    have "(g \<circ>\<^sub>c f) \<circ>\<^sub>c i1' = g \<circ>\<^sub>c (f \<circ>\<^sub>c i1')" using comp_associative2[OF i1'_type f_type g_type] by simp
    also have "... = g \<circ>\<^sub>c i1" using f1 by simp
    also have "... = i1'" using g1 by simp
    finally show ?thesis by simp
  qed

  obtain hW' where hW'_type: "hW' : W' \<rightarrow> W'" and hW'0: "hW' \<circ>\<^sub>c i0' = i0'" and hW'1: "hW' \<circ>\<^sub>c i1' = i1'"
      and hW'_uniq: "\<forall>hh. hh : W' \<rightarrow> W' \<and> hh \<circ>\<^sub>c i0' = i0' \<and> hh \<circ>\<^sub>c i1' = i1' \<longrightarrow> hh = hW'"
    using W'_univ[rule_format, where f=i0' and g=i1' and Z=W'] i0'_type i1'_type by auto
  have gf_type: "g \<circ>\<^sub>c f : W' \<rightarrow> W'" using f_type g_type comp_type by blast
  have gf_eq_hW': "g \<circ>\<^sub>c f = hW'" using hW'_uniq[rule_format, where hh="g \<circ>\<^sub>c f"] gf_type gf0 gf1 by auto
  have idW'_type: "id(W') : W' \<rightarrow> W'" by (rule id_type)
  have idW'0: "id(W') \<circ>\<^sub>c i0' = i0'" using id_left_unit2[OF i0'_type] by simp
  have idW'1: "id(W') \<circ>\<^sub>c i1' = i1'" using id_left_unit2[OF i1'_type] by simp
  have idW'_eq_hW': "id(W') = hW'" using hW'_uniq[rule_format, where hh="id(W')"] idW'_type idW'0 idW'1 by auto
  have gf: "g \<circ>\<^sub>c f = id(W')" using gf_eq_hW' idW'_eq_hW' by simp

  have g_iso: "isomorphism(g)"
    using isomorphism_def3[OF g_type] f_type fg gf by auto
  show ?thesis using g_type g_iso g0 g1 by auto
qed

subsection \<open>Coproduct Function Properties\<close>

lemma cfunc_coprod_comp:
  assumes a_type: "a : Y \<rightarrow> Z" and b_type: "b : X \<rightarrow> Y" and c_type: "c : W \<rightarrow> Y"
  shows "(a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c) = a \<circ>\<^sub>c (b \<amalg> c)"
proof -
  have ab_type: "a \<circ>\<^sub>c b : X \<rightarrow> Z" using b_type a_type comp_type by blast
  have ac_type: "a \<circ>\<^sub>c c : W \<rightarrow> Z" using c_type a_type comp_type by blast
  have bc_type: "b \<amalg> c : X \<Coprod> W \<rightarrow> Y" using cfunc_coprod_type[OF b_type c_type] by simp
  have h_type: "a \<circ>\<^sub>c (b \<amalg> c) : X \<Coprod> W \<rightarrow> Z" using bc_type a_type comp_type by blast
  have h_left: "(a \<circ>\<^sub>c (b \<amalg> c)) \<circ>\<^sub>c left_coproj(X, W) = a \<circ>\<^sub>c b"
  proof -
    have "(a \<circ>\<^sub>c (b \<amalg> c)) \<circ>\<^sub>c left_coproj(X, W) = a \<circ>\<^sub>c ((b \<amalg> c) \<circ>\<^sub>c left_coproj(X, W))"
      using comp_associative2[OF left_proj_type bc_type a_type] by simp
    also have "... = a \<circ>\<^sub>c b" using left_coproj_cfunc_coprod[OF b_type c_type] by simp
    finally show ?thesis by simp
  qed
  have h_right: "(a \<circ>\<^sub>c (b \<amalg> c)) \<circ>\<^sub>c right_coproj(X, W) = a \<circ>\<^sub>c c"
  proof -
    have "(a \<circ>\<^sub>c (b \<amalg> c)) \<circ>\<^sub>c right_coproj(X, W) = a \<circ>\<^sub>c ((b \<amalg> c) \<circ>\<^sub>c right_coproj(X, W))"
      using comp_associative2[OF right_proj_type bc_type a_type] by simp
    also have "... = a \<circ>\<^sub>c c" using right_coproj_cfunc_coprod[OF b_type c_type] by simp
    finally show ?thesis by simp
  qed
  show ?thesis using cfunc_coprod_unique[OF ab_type ac_type h_type h_left h_right] by simp
qed

lemma id_coprod:
  "id(A \<Coprod> B) = left_coproj(A, B) \<amalg> right_coproj(A, B)"
proof -
  have idAB_type: "id(A \<Coprod> B) : A \<Coprod> B \<rightarrow> A \<Coprod> B" by (rule id_type)
  have left_eq: "id(A \<Coprod> B) \<circ>\<^sub>c left_coproj(A, B) = left_coproj(A, B)"
    using id_left_unit2[OF left_proj_type] by simp
  have right_eq: "id(A \<Coprod> B) \<circ>\<^sub>c right_coproj(A, B) = right_coproj(A, B)"
    using id_left_unit2[OF right_proj_type] by simp
  show ?thesis using cfunc_coprod_unique[OF left_proj_type right_proj_type idAB_type left_eq right_eq] by simp
qed

text \<open>HOL's original @{text injective_imp_monomorphism} (Proposition 2.1.27) is a general
  @{text Cfunc}/@{text Terminal}-level fact never needed until this theory; rather than reopening
  the already-committed @{text Terminal.thy}, it is proved here where it is first used.\<close>
lemma injective_imp_monomorphism:
  assumes f_inj: "injective(f)"
  shows "monomorphism(f)"
  unfolding monomorphism_def
proof (intro allI impI)
  fix g h
  assume "codomain(g) = domain(f) \<and> codomain(h) = domain(f)"
  then have cd_g: "codomain(g) = domain(f)" and cd_h: "codomain(h) = domain(f)" by auto
  assume fg_eq_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"

  obtain X Y where f_type: "f : X \<rightarrow> Y" using cfunc_type_def by auto
  have fX: "domain(f) = X" using f_type unfolding cfunc_type_def by auto

  have dom_fg: "domain(f \<circ>\<^sub>c g) = domain(g)" using domain_comp[of f g] cd_g by auto
  have dom_fh: "domain(f \<circ>\<^sub>c h) = domain(h)" using domain_comp[of f h] cd_h by auto
  have dom_eq: "domain(g) = domain(h)" using dom_fg dom_fh fg_eq_fh by simp

  have g_type: "g : domain(g) \<rightarrow> X" unfolding cfunc_type_def using cd_g fX by auto
  have h_type: "h : domain(g) \<rightarrow> X" unfolding cfunc_type_def using cd_h fX dom_eq by auto

  have pointwise: "\<forall>x. x \<in>\<^sub>c domain(g) \<longrightarrow> g \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
  proof (intro allI impI)
    fix x
    assume x_in_A: "x \<in>\<^sub>c domain(g)"
    have gx_type: "g \<circ>\<^sub>c x : \<one> \<rightarrow> X" using x_in_A g_type comp_type by blast
    have hx_type: "h \<circ>\<^sub>c x : \<one> \<rightarrow> X" using x_in_A h_type comp_type by blast
    have step: "f \<circ>\<^sub>c (g \<circ>\<^sub>c x) = f \<circ>\<^sub>c (h \<circ>\<^sub>c x)"
    proof -
      have "f \<circ>\<^sub>c (g \<circ>\<^sub>c x) = (f \<circ>\<^sub>c g) \<circ>\<^sub>c x" using comp_associative2[OF x_in_A g_type f_type] by simp
      also have "... = (f \<circ>\<^sub>c h) \<circ>\<^sub>c x" using fg_eq_fh by simp
      also have "... = f \<circ>\<^sub>c (h \<circ>\<^sub>c x)" using comp_associative2[OF x_in_A h_type f_type] by simp
      finally show ?thesis by simp
    qed
    have gx_in_X: "g \<circ>\<^sub>c x \<in>\<^sub>c X" using gx_type by simp
    have hx_in_X: "h \<circ>\<^sub>c x \<in>\<^sub>c X" using hx_type by simp
    show "g \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
      using f_inj unfolding injective_def using gx_in_X hx_in_X step fX by auto
  qed
  show "g = h"
  proof (rule one_separator[OF g_type h_type])
    fix x
    assume "x : \<one> \<rightarrow> domain(g)"
    then show "g \<circ>\<^sub>c x = h \<circ>\<^sub>c x" using pointwise by auto
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.4.1 in Halvorson.\<close>
lemma coproducts_disjoint:
  assumes x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c Y"
  shows "left_coproj(X, Y) \<circ>\<^sub>c x \<noteq> right_coproj(X, Y) \<circ>\<^sub>c y"
proof
  assume BWOC: "left_coproj(X, Y) \<circ>\<^sub>c x = right_coproj(X, Y) \<circ>\<^sub>c y"
  have g_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using terminal_func_type[of X] true_func_type comp_type by blast
  have h_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<Omega>" using terminal_func_type[of Y] false_func_type comp_type by blast
  have gh_type: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) : X \<Coprod> Y \<rightarrow> \<Omega>" using cfunc_coprod_type[OF g_type h_type] by simp
  have gh_left: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
    using left_coproj_cfunc_coprod[OF g_type h_type] by simp
  have gh_right: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c right_coproj(X, Y) = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    using right_coproj_cfunc_coprod[OF g_type h_type] by simp

  have at_x: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x) = \<t>"
  proof -
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x)
        = (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x"
      using comp_associative2[OF x_type left_proj_type gh_type] by simp
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x" using gh_left by simp
    also have "... = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)" using comp_associative2[OF x_type terminal_func_type true_func_type] by simp
    also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF x_type] by simp
    also have "... = \<t>" using id_right_unit2[OF true_func_type] by simp
    finally show ?thesis by simp
  qed
  have at_y: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y) = \<f>"
  proof -
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y)
        = (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y"
      using comp_associative2[OF y_type right_proj_type gh_type] by simp
    also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y" using gh_right by simp
    also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y)" using comp_associative2[OF y_type terminal_func_type false_func_type] by simp
    also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF y_type] by simp
    also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
    finally show ?thesis by simp
  qed
  have "\<t> = \<f>" using at_x at_y BWOC by simp
  then show False using true_false_distinct by simp
qed

text \<open>The lemma below corresponds to Proposition 2.4.2 in Halvorson.\<close>
lemma left_coproj_are_monomorphisms:
  "monomorphism(left_coproj(X, Y))"
proof (cases "\<exists>x. x \<in>\<^sub>c X")
  case True
  then obtain x where x_type: "x \<in>\<^sub>c X" by auto
  have xb_type: "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X" using terminal_func_type[of Y] x_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have j_type: "id(X) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) : X \<Coprod> Y \<rightarrow> X" using cfunc_coprod_type[OF idX_type xb_type] by simp
  have j_left: "(id(X) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y) = id(X)"
    using left_coproj_cfunc_coprod[OF idX_type xb_type] by simp
  have comp_mono: "monomorphism((id(X) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y))"
    using j_left id_isomorphism[of X] iso_imp_epi_and_monic[of "id(X)"] by simp
  show "monomorphism(left_coproj(X, Y))"
    using comp_monic_imp_monic'[OF left_proj_type j_type comp_mono] by simp
next
  case False
  have inj: "injective(left_coproj(X, Y))"
    unfolding injective_def
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c domain(left_coproj(X, Y)) \<and> y \<in>\<^sub>c domain(left_coproj(X, Y)) \<and>
        left_coproj(X, Y) \<circ>\<^sub>c x = left_coproj(X, Y) \<circ>\<^sub>c y"
    then have "x \<in>\<^sub>c domain(left_coproj(X, Y))" by auto
    then have "x \<in>\<^sub>c X" using left_proj_type unfolding cfunc_type_def by auto
    then show "x = y" using False by auto
  qed
  show "monomorphism(left_coproj(X, Y))" using injective_imp_monomorphism[OF inj] by simp
qed

lemma right_coproj_are_monomorphisms:
  "monomorphism(right_coproj(X, Y))"
proof (cases "\<exists>y. y \<in>\<^sub>c Y")
  case True
  then obtain y where y_type: "y \<in>\<^sub>c Y" by auto
  have yb_type: "y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> Y" using terminal_func_type[of X] y_type comp_type by blast
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have j_type: "(y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> id(Y) : X \<Coprod> Y \<rightarrow> Y" using cfunc_coprod_type[OF yb_type idY_type] by simp
  have j_right: "((y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> id(Y)) \<circ>\<^sub>c right_coproj(X, Y) = id(Y)"
    using right_coproj_cfunc_coprod[OF yb_type idY_type] by simp
  have comp_mono: "monomorphism(((y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> id(Y)) \<circ>\<^sub>c right_coproj(X, Y))"
    using j_right id_isomorphism[of Y] iso_imp_epi_and_monic[of "id(Y)"] by simp
  show "monomorphism(right_coproj(X, Y))"
    using comp_monic_imp_monic'[OF right_proj_type j_type comp_mono] by simp
next
  case False
  have inj: "injective(right_coproj(X, Y))"
    unfolding injective_def
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c domain(right_coproj(X, Y)) \<and> y \<in>\<^sub>c domain(right_coproj(X, Y)) \<and>
        right_coproj(X, Y) \<circ>\<^sub>c x = right_coproj(X, Y) \<circ>\<^sub>c y"
    then have "x \<in>\<^sub>c domain(right_coproj(X, Y))" by auto
    then have "x \<in>\<^sub>c Y" using right_proj_type unfolding cfunc_type_def by auto
    then show "x = y" using False by auto
  qed
  show "monomorphism(right_coproj(X, Y))" using injective_imp_monomorphism[OF inj] by simp
qed

text \<open>Ported ahead of HOL's own ordering (it lists @{text coprod_eq} after @{text
  coprojs_jointly_surj}) since it has no dependency on it and is needed to prove it.\<close>
lemma coprod_eq:
  assumes a_type: "a : X \<Coprod> Y \<rightarrow> Z" and b_type: "b : X \<Coprod> Y \<rightarrow> Z"
  shows "a = b \<longleftrightarrow>
    (a \<circ>\<^sub>c left_coproj(X, Y) = b \<circ>\<^sub>c left_coproj(X, Y) \<and> a \<circ>\<^sub>c right_coproj(X, Y) = b \<circ>\<^sub>c right_coproj(X, Y))"
proof (rule iffI)
  assume "a = b"
  then show "a \<circ>\<^sub>c left_coproj(X, Y) = b \<circ>\<^sub>c left_coproj(X, Y) \<and> a \<circ>\<^sub>c right_coproj(X, Y) = b \<circ>\<^sub>c right_coproj(X, Y)"
    by simp
next
  assume "a \<circ>\<^sub>c left_coproj(X, Y) = b \<circ>\<^sub>c left_coproj(X, Y) \<and> a \<circ>\<^sub>c right_coproj(X, Y) = b \<circ>\<^sub>c right_coproj(X, Y)"
  then have el: "a \<circ>\<^sub>c left_coproj(X, Y) = b \<circ>\<^sub>c left_coproj(X, Y)"
    and er: "a \<circ>\<^sub>c right_coproj(X, Y) = b \<circ>\<^sub>c right_coproj(X, Y)" by auto
  have al_type: "a \<circ>\<^sub>c left_coproj(X, Y) : X \<rightarrow> Z" using left_proj_type a_type comp_type by blast
  have ar_type: "a \<circ>\<^sub>c right_coproj(X, Y) : Y \<rightarrow> Z" using right_proj_type a_type comp_type by blast
  have bl_type: "b \<circ>\<^sub>c left_coproj(X, Y) : X \<rightarrow> Z" using left_proj_type b_type comp_type by blast
  have br_type: "b \<circ>\<^sub>c right_coproj(X, Y) : Y \<rightarrow> Z" using right_proj_type b_type comp_type by blast
  have a_eq: "a = (a \<circ>\<^sub>c left_coproj(X, Y)) \<amalg> (a \<circ>\<^sub>c right_coproj(X, Y))"
    using cfunc_coprod_unique[OF al_type ar_type a_type refl refl] by simp
  have b_eq: "b = (b \<circ>\<^sub>c left_coproj(X, Y)) \<amalg> (b \<circ>\<^sub>c right_coproj(X, Y))"
    using cfunc_coprod_unique[OF bl_type br_type b_type refl refl] by simp
  show "a = b" using a_eq b_eq el er by simp
qed

lemma coprod_eqI:
  assumes a_type: "a : X \<Coprod> Y \<rightarrow> Z" and b_type: "b : X \<Coprod> Y \<rightarrow> Z"
  assumes "a \<circ>\<^sub>c left_coproj(X, Y) = b \<circ>\<^sub>c left_coproj(X, Y) \<and> a \<circ>\<^sub>c right_coproj(X, Y) = b \<circ>\<^sub>c right_coproj(X, Y)"
  shows "a = b"
  using assms coprod_eq[OF a_type b_type] by auto

lemma coprod_eq2:
  assumes a_type: "a : X \<rightarrow> Z" and b_type: "b : Y \<rightarrow> Z" and c_type: "c : X \<rightarrow> Z" and d_type: "d : Y \<rightarrow> Z"
  shows "(a \<amalg> b) = (c \<amalg> d) \<longleftrightarrow> (a = c \<and> b = d)"
proof (rule iffI)
  assume eq: "(a \<amalg> b) = (c \<amalg> d)"
  have "(a \<amalg> b) \<circ>\<^sub>c left_coproj(X, Y) = (c \<amalg> d) \<circ>\<^sub>c left_coproj(X, Y)" using eq by simp
  then have ac: "a = c" using left_coproj_cfunc_coprod[OF a_type b_type] left_coproj_cfunc_coprod[OF c_type d_type] by simp
  have "(a \<amalg> b) \<circ>\<^sub>c right_coproj(X, Y) = (c \<amalg> d) \<circ>\<^sub>c right_coproj(X, Y)" using eq by simp
  then have bd: "b = d" using right_coproj_cfunc_coprod[OF a_type b_type] right_coproj_cfunc_coprod[OF c_type d_type] by simp
  show "a = c \<and> b = d" using ac bd by simp
next
  assume "a = c \<and> b = d"
  then show "(a \<amalg> b) = (c \<amalg> d)" by auto
qed

lemma coprod_decomp:
  assumes a_type: "a : X \<Coprod> Y \<rightarrow> A"
  shows "\<exists>x y. a = x \<amalg> y \<and> x : X \<rightarrow> A \<and> y : Y \<rightarrow> A"
proof -
  have x_type: "a \<circ>\<^sub>c left_coproj(X, Y) : X \<rightarrow> A" using left_proj_type a_type comp_type by blast
  have y_type: "a \<circ>\<^sub>c right_coproj(X, Y) : Y \<rightarrow> A" using right_proj_type a_type comp_type by blast
  have a_eq: "a = (a \<circ>\<^sub>c left_coproj(X, Y)) \<amalg> (a \<circ>\<^sub>c right_coproj(X, Y))"
    using cfunc_coprod_unique[OF x_type y_type a_type refl refl] by simp
  show ?thesis using x_type y_type a_eq by auto
qed

text \<open>The lemma below corresponds to Exercise 2.4.3 in Halvorson.\<close>
lemma coprojs_jointly_surj:
  assumes z_type: "z \<in>\<^sub>c X \<Coprod> Y"
  shows "(\<exists>x. x \<in>\<^sub>c X \<and> z = left_coproj(X, Y) \<circ>\<^sub>c x) \<or> (\<exists>y. y \<in>\<^sub>c Y \<and> z = right_coproj(X, Y) \<circ>\<^sub>c y)"
proof (rule ccontr)
  assume contra: "\<not> ((\<exists>x. x \<in>\<^sub>c X \<and> z = left_coproj(X, Y) \<circ>\<^sub>c x) \<or> (\<exists>y. y \<in>\<^sub>c Y \<and> z = right_coproj(X, Y) \<circ>\<^sub>c y))"
  have not_in_left: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> z \<noteq> left_coproj(X, Y) \<circ>\<^sub>c x" using contra by auto
  have not_in_right: "\<forall>y. y \<in>\<^sub>c Y \<longrightarrow> z \<noteq> right_coproj(X, Y) \<circ>\<^sub>c y" using contra by auto

  have zb_type: "z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> X \<Coprod> Y" using terminal_func_type[of "X \<Coprod> Y"] z_type comp_type by blast
  have idW_type: "id(X \<Coprod> Y) : X \<Coprod> Y \<rightarrow> X \<Coprod> Y" by (rule id_type)
  have pair_type: "\<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> (X \<Coprod> Y) \<times>\<^sub>c (X \<Coprod> Y)"
    using zb_type idW_type cfunc_prod_type by auto
  have indicator_type: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> \<Omega>"
    using pair_type eq_pred_type comp_type by blast
  have h_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> \<Omega>" using terminal_func_type[of "X \<Coprod> Y"] false_func_type comp_type by blast

  have LHS_l_type: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj(X, Y) : X \<rightarrow> \<Omega>"
    using left_proj_type indicator_type comp_type by blast
  have RHS_l_type: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c left_coproj(X, Y) : X \<rightarrow> \<Omega>"
    using left_proj_type h_type comp_type by blast
  have fact1: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj(X, Y)
      = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c left_coproj(X, Y)"
  proof (rule one_separator[OF LHS_l_type RHS_l_type])
    fix x
    assume x_type: "x : \<one> \<rightarrow> X"
    have lx_type: "left_coproj(X, Y) \<circ>\<^sub>c x : \<one> \<rightarrow> X \<Coprod> Y" using x_type left_proj_type comp_type by blast
    have z_ne: "z \<noteq> left_coproj(X, Y) \<circ>\<^sub>c x" using not_in_left[rule_format, where x=x] x_type by auto
    have step1: "((eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x
        = (eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x)"
      using comp_associative2[OF x_type left_proj_type indicator_type] by simp
    have step1b: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x)
        = eq_pred(X \<Coprod> Y) \<circ>\<^sub>c (\<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x))"
      using comp_associative2[OF lx_type pair_type eq_pred_type] by simp
    have step2: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c (\<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x)) = \<f>"
      using eq_pred_false_extract_right[OF z_type lx_type z_ne] by simp
    have step3: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x) = \<f>"
    proof -
      have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x) = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X \<Coprod> Y\<^esub> \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x))"
        using comp_associative2[OF lx_type terminal_func_type false_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF lx_type] by simp
      also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
      finally show ?thesis by simp
    qed
    have step4: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x)"
      using comp_associative2[OF x_type left_proj_type h_type] by simp
    show "((eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x
        = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x"
      using step1 step1b step2 step3 step4 by simp
  qed

  have LHS_r_type: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj(X, Y) : Y \<rightarrow> \<Omega>"
    using right_proj_type indicator_type comp_type by blast
  have RHS_r_type: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c right_coproj(X, Y) : Y \<rightarrow> \<Omega>"
    using right_proj_type h_type comp_type by blast
  have fact2: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj(X, Y)
      = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c right_coproj(X, Y)"
  proof (rule one_separator[OF LHS_r_type RHS_r_type])
    fix y
    assume y_type: "y : \<one> \<rightarrow> Y"
    have ry_type: "right_coproj(X, Y) \<circ>\<^sub>c y : \<one> \<rightarrow> X \<Coprod> Y" using y_type right_proj_type comp_type by blast
    have z_ne: "z \<noteq> right_coproj(X, Y) \<circ>\<^sub>c y" using not_in_right[rule_format, where y=y] y_type by auto
    have step1: "((eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y
        = (eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y)"
      using comp_associative2[OF y_type right_proj_type indicator_type] by simp
    have step1b: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y)
        = eq_pred(X \<Coprod> Y) \<circ>\<^sub>c (\<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y))"
      using comp_associative2[OF ry_type pair_type eq_pred_type] by simp
    have step2: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c (\<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y)) = \<f>"
      using eq_pred_false_extract_right[OF z_type ry_type z_ne] by simp
    have step3: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y) = \<f>"
    proof -
      have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y) = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X \<Coprod> Y\<^esub> \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y))"
        using comp_associative2[OF ry_type terminal_func_type false_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF ry_type] by simp
      also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
      finally show ?thesis by simp
    qed
    have step4: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y)"
      using comp_associative2[OF y_type right_proj_type h_type] by simp
    show "((eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y
        = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y"
      using step1 step1b step2 step3 step4 by simp
  qed

  have indicator_eq_h: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>"
    using coprod_eq[OF indicator_type h_type] fact1 fact2 by simp

  have indicator_z_assoc: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c z
      = eq_pred(X \<Coprod> Y) \<circ>\<^sub>c (\<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> \<circ>\<^sub>c z)"
    using comp_associative2[OF z_type pair_type eq_pred_type] by simp
  have indicator_z_raw: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c (\<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle> \<circ>\<^sub>c z) = \<t>"
    using eq_pred_true_extract_right[OF z_type] by simp
  have indicator_z: "(eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id(X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c z = \<t>"
    using indicator_z_assoc indicator_z_raw by simp
  have h_z: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c z = \<f>"
  proof -
    have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>) \<circ>\<^sub>c z = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X \<Coprod> Y\<^esub> \<circ>\<^sub>c z)" using comp_associative2[OF z_type terminal_func_type false_func_type] by simp
    also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF z_type] by simp
    also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
    finally show ?thesis by simp
  qed
  have "\<t> = \<f>" using indicator_z h_z indicator_eq_h by simp
  then show False using true_false_distinct by simp
qed

lemma maps_into_1u1:
  assumes x_type: "x \<in>\<^sub>c \<one> \<Coprod> \<one>"
  shows "x = left_coproj(\<one>, \<one>) \<or> x = right_coproj(\<one>, \<one>)"
proof -
  have disj: "(\<exists>a. a \<in>\<^sub>c \<one> \<and> x = left_coproj(\<one>, \<one>) \<circ>\<^sub>c a) \<or> (\<exists>b. b \<in>\<^sub>c \<one> \<and> x = right_coproj(\<one>, \<one>) \<circ>\<^sub>c b)"
    using coprojs_jointly_surj[OF x_type] by simp
  show ?thesis
  proof (cases "\<exists>a. a \<in>\<^sub>c \<one> \<and> x = left_coproj(\<one>, \<one>) \<circ>\<^sub>c a")
    case True
    then obtain a where a_type: "a \<in>\<^sub>c \<one>" and x_eq: "x = left_coproj(\<one>, \<one>) \<circ>\<^sub>c a" by auto
    have a_eq_beta: "a = \<beta>\<^bsub>\<one>\<^esub>" using terminal_func_unique[of a] a_type by simp
    have id_eq_beta: "id(\<one>) = \<beta>\<^bsub>\<one>\<^esub>" using terminal_func_unique[of "id(\<one>)"] id_type by simp
    have a_eq_id: "a = id(\<one>)" using a_eq_beta id_eq_beta by simp
    have "x = left_coproj(\<one>, \<one>)" using x_eq a_eq_id id_right_unit2[OF left_proj_type] by simp
    then show ?thesis by (rule disjI1)
  next
    case False
    then have "\<exists>b. b \<in>\<^sub>c \<one> \<and> x = right_coproj(\<one>, \<one>) \<circ>\<^sub>c b" using disj by auto
    then obtain b where b_type: "b \<in>\<^sub>c \<one>" and x_eq: "x = right_coproj(\<one>, \<one>) \<circ>\<^sub>c b" by auto
    have b_eq_beta: "b = \<beta>\<^bsub>\<one>\<^esub>" using terminal_func_unique[of b] b_type by simp
    have id_eq_beta: "id(\<one>) = \<beta>\<^bsub>\<one>\<^esub>" using terminal_func_unique[of "id(\<one>)"] id_type by simp
    have b_eq_id: "b = id(\<one>)" using b_eq_beta id_eq_beta by simp
    have "x = right_coproj(\<one>, \<one>)" using x_eq b_eq_id id_right_unit2[OF right_proj_type] by simp
    then show ?thesis by (rule disjI2)
  qed
qed

lemma coprod_preserves_left_epi:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  assumes f_surj: "surjective(f)"
  shows "surjective(f \<amalg> g)"
proof -
  have fg_type: "f \<amalg> g : X \<Coprod> Y \<rightarrow> Z" using cfunc_coprod_type[OF f_type g_type] by simp
  show ?thesis unfolding surjective_def2[OF fg_type]
  proof (intro allI impI)
    fix z
    assume z_type: "z \<in>\<^sub>c Z"
    obtain x where x_type: "x \<in>\<^sub>c X" and fx_eq: "f \<circ>\<^sub>c x = z"
      using surjective_def2[OF f_type] f_surj z_type by auto
    have lx_type: "left_coproj(X, Y) \<circ>\<^sub>c x \<in>\<^sub>c X \<Coprod> Y" using x_type left_proj_type comp_type by blast
    have "(f \<amalg> g) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x) = z"
    proof -
      have "(f \<amalg> g) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x) = ((f \<amalg> g) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x"
        using comp_associative2[OF x_type left_proj_type fg_type] by simp
      also have "... = f \<circ>\<^sub>c x" using left_coproj_cfunc_coprod[OF f_type g_type] by simp
      also have "... = z" using fx_eq by simp
      finally show ?thesis by simp
    qed
    then show "\<exists>x. x \<in>\<^sub>c X \<Coprod> Y \<and> (f \<amalg> g) \<circ>\<^sub>c x = z" using lx_type by auto
  qed
qed

lemma coprod_preserves_right_epi:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  assumes g_surj: "surjective(g)"
  shows "surjective(f \<amalg> g)"
proof -
  have fg_type: "f \<amalg> g : X \<Coprod> Y \<rightarrow> Z" using cfunc_coprod_type[OF f_type g_type] by simp
  show ?thesis unfolding surjective_def2[OF fg_type]
  proof (intro allI impI)
    fix z
    assume z_type: "z \<in>\<^sub>c Z"
    obtain y where y_type: "y \<in>\<^sub>c Y" and gy_eq: "g \<circ>\<^sub>c y = z"
      using surjective_def2[OF g_type] g_surj z_type by auto
    have ry_type: "right_coproj(X, Y) \<circ>\<^sub>c y \<in>\<^sub>c X \<Coprod> Y" using y_type right_proj_type comp_type by blast
    have "(f \<amalg> g) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y) = z"
    proof -
      have "(f \<amalg> g) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y) = ((f \<amalg> g) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y"
        using comp_associative2[OF y_type right_proj_type fg_type] by simp
      also have "... = g \<circ>\<^sub>c y" using right_coproj_cfunc_coprod[OF f_type g_type] by simp
      also have "... = z" using gy_eq by simp
      finally show ?thesis by simp
    qed
    then show "\<exists>y. y \<in>\<^sub>c X \<Coprod> Y \<and> (f \<amalg> g) \<circ>\<^sub>c y = z" using ry_type by auto
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.4.4 in Halvorson.\<close>
lemma truth_value_set_iso_1u1:
  "isomorphism(\<t> \<amalg> \<f>)"
proof -
  have tf_type: "\<t> \<amalg> \<f> : \<one> \<Coprod> \<one> \<rightarrow> \<Omega>" using cfunc_coprod_type[OF true_func_type false_func_type] by simp
  have tf_left: "(\<t> \<amalg> \<f>) \<circ>\<^sub>c left_coproj(\<one>, \<one>) = \<t>" using left_coproj_cfunc_coprod[OF true_func_type false_func_type] by simp
  have tf_right: "(\<t> \<amalg> \<f>) \<circ>\<^sub>c right_coproj(\<one>, \<one>) = \<f>" using right_coproj_cfunc_coprod[OF true_func_type false_func_type] by simp
  have inj: "injective(\<t> \<amalg> \<f>)"
    unfolding injective_def2[OF tf_type]
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c \<one> \<Coprod> \<one> \<and> y \<in>\<^sub>c \<one> \<Coprod> \<one> \<and> (\<t> \<amalg> \<f>) \<circ>\<^sub>c x = (\<t> \<amalg> \<f>) \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c \<one> \<Coprod> \<one>" and y_type: "y \<in>\<^sub>c \<one> \<Coprod> \<one>" and eq: "(\<t> \<amalg> \<f>) \<circ>\<^sub>c x = (\<t> \<amalg> \<f>) \<circ>\<^sub>c y" by auto
    have x_cases: "x = left_coproj(\<one>, \<one>) \<or> x = right_coproj(\<one>, \<one>)" using maps_into_1u1[OF x_type] by simp
    have y_cases: "y = left_coproj(\<one>, \<one>) \<or> y = right_coproj(\<one>, \<one>)" using maps_into_1u1[OF y_type] by simp
    show "x = y"
    proof (cases "x = left_coproj(\<one>, \<one>)")
      case True
      show ?thesis
      proof (cases "y = left_coproj(\<one>, \<one>)")
        case True
        then show ?thesis using \<open>x = left_coproj(\<one>, \<one>)\<close> by simp
      next
        case False
        then have y_eq_right: "y = right_coproj(\<one>, \<one>)" using y_cases by auto
        have "\<t> = \<f>" using eq \<open>x = left_coproj(\<one>, \<one>)\<close> y_eq_right tf_left tf_right by simp
        then show ?thesis using true_false_distinct by simp
      qed
    next
      case False
      then have x_eq_right: "x = right_coproj(\<one>, \<one>)" using x_cases by auto
      show ?thesis
      proof (cases "y = left_coproj(\<one>, \<one>)")
        case True
        have "\<f> = \<t>" using eq x_eq_right True tf_left tf_right by simp
        then show ?thesis using true_false_distinct by simp
      next
        case False
        then have y_eq_right: "y = right_coproj(\<one>, \<one>)" using y_cases by auto
        then show ?thesis using x_eq_right by simp
      qed
    qed
  qed
  have surj: "surjective(\<t> \<amalg> \<f>)"
    unfolding surjective_def2[OF tf_type]
  proof (intro allI impI)
    fix w
    assume w_type: "w \<in>\<^sub>c \<Omega>"
    have w_cases: "w = \<f> \<or> w = \<t>" using true_false_only_truth_values[OF w_type] by simp
    show "\<exists>x. x \<in>\<^sub>c \<one> \<Coprod> \<one> \<and> (\<t> \<amalg> \<f>) \<circ>\<^sub>c x = w"
    proof (cases "w = \<t>")
      case True
      have "(\<t> \<amalg> \<f>) \<circ>\<^sub>c left_coproj(\<one>, \<one>) = w" using tf_left True by simp
      then show ?thesis using left_proj_type by auto
    next
      case False
      then have w_eq_f: "w = \<f>" using w_cases by auto
      have "(\<t> \<amalg> \<f>) \<circ>\<^sub>c right_coproj(\<one>, \<one>) = w" using tf_right w_eq_f by simp
      then show ?thesis using right_proj_type by auto
    qed
  qed
  have mono: "monomorphism(\<t> \<amalg> \<f>)" using injective_imp_monomorphism[OF inj] by simp
  have epi: "epimorphism(\<t> \<amalg> \<f>)" using surjective_is_epimorphism[OF surj] by simp
  show ?thesis using epi_mon_is_iso[OF epi mono] by simp
qed

subsubsection \<open>Equality Predicate with Coproduct Properties\<close>

lemma eq_pred_left_coproj:
  assumes u_type: "u \<in>\<^sub>c X \<Coprod> Y" and x_type: "x \<in>\<^sub>c X"
  shows "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj(X, Y) \<circ>\<^sub>c x\<rangle>
      = ((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c u"
proof -
  have lx_type: "left_coproj(X, Y) \<circ>\<^sub>c x \<in>\<^sub>c X \<Coprod> Y" using x_type left_proj_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have xb_type: "x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> X" using terminal_func_type[of X] x_type comp_type by blast
  have pair1_type: "\<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c X" using idX_type xb_type cfunc_prod_type by auto
  have g1_type: "eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> \<Omega>" using pair1_type eq_pred_type comp_type by blast
  have g2_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<Omega>" using terminal_func_type[of Y] false_func_type comp_type by blast
  have gfull_type: "(eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) : X \<Coprod> Y \<rightarrow> \<Omega>"
    using cfunc_coprod_type[OF g1_type g2_type] by simp
  have upair_type: "\<langle>u, left_coproj(X, Y) \<circ>\<^sub>c x\<rangle> \<in>\<^sub>c (X \<Coprod> Y) \<times>\<^sub>c (X \<Coprod> Y)" using u_type lx_type cfunc_prod_type by auto
  have pred_type: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj(X, Y) \<circ>\<^sub>c x\<rangle> \<in>\<^sub>c \<Omega>" using upair_type eq_pred_type comp_type by blast

  show ?thesis
  proof (cases "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj(X, Y) \<circ>\<^sub>c x\<rangle> = \<t>")
    case True
    have u_eq_lx: "u = left_coproj(X, Y) \<circ>\<^sub>c x" using eq_pred_iff_eq[OF u_type lx_type] True by simp
    have s1: "((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c u
        = ((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x)"
      using u_eq_lx by simp
    have s2: "((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c x)
        = (((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x"
      using comp_associative2[OF x_type left_proj_type gfull_type] by simp
    have s3: "(((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c x
        = (eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x"
      using left_coproj_cfunc_coprod[OF g1_type g2_type] by simp
    have s4: "(eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x = eq_pred(X) \<circ>\<^sub>c (\<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x)"
      using comp_associative2[OF x_type pair1_type eq_pred_type] by simp
    have s5: "\<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = \<langle>x, x\<rangle>" using cart_prod_extract_left[OF x_type x_type] by simp
    have s6: "eq_pred(X) \<circ>\<^sub>c \<langle>x, x\<rangle> = \<t>" using eq_pred_iff_eq[OF x_type x_type] by simp
    show ?thesis using s1 s2 s3 s4 s5 s6 True by simp
  next
    case False
    have pred_eq_f: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj(X, Y) \<circ>\<^sub>c x\<rangle> = \<f>"
      using true_false_only_truth_values[OF pred_type] False by auto
    have u_ne_lx: "u \<noteq> left_coproj(X, Y) \<circ>\<^sub>c x" using eq_pred_iff_eq_conv[OF u_type lx_type] pred_eq_f by simp
    have disj: "(\<exists>g. g \<in>\<^sub>c X \<and> u = left_coproj(X, Y) \<circ>\<^sub>c g) \<or> (\<exists>g. g \<in>\<^sub>c Y \<and> u = right_coproj(X, Y) \<circ>\<^sub>c g)"
      using coprojs_jointly_surj[OF u_type] by simp
    show ?thesis
    proof (cases "\<exists>g. g \<in>\<^sub>c X \<and> u = left_coproj(X, Y) \<circ>\<^sub>c g")
      case True
      then obtain g where g_type: "g \<in>\<^sub>c X" and g_def: "u = left_coproj(X, Y) \<circ>\<^sub>c g" by auto
      have x_ne_g: "g \<noteq> x" using u_ne_lx g_def by auto
      have pairg_type: "\<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g : \<one> \<rightarrow> X \<times>\<^sub>c X" using g_type pair1_type comp_type by blast
      have s1: "((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c u
          = ((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c g)"
        using g_def by simp
      have s2: "((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c g)
          = (((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c g"
        using comp_associative2[OF g_type left_proj_type gfull_type] by simp
      have s3: "(((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c g
          = (eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c g"
        using left_coproj_cfunc_coprod[OF g1_type g2_type] by simp
      have s4: "(eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c g = eq_pred(X) \<circ>\<^sub>c (\<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g)"
        using comp_associative2[OF g_type pair1_type eq_pred_type] by simp
      have s5: "\<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g = \<langle>g, x\<rangle>" using cart_prod_extract_left[OF g_type x_type] by simp
      have s6: "eq_pred(X) \<circ>\<^sub>c \<langle>g, x\<rangle> = \<f>" using eq_pred_iff_eq_conv[OF g_type x_type] x_ne_g by simp
      show ?thesis using s1 s2 s3 s4 s5 s6 pred_eq_f by simp
    next
      case False
      then have "\<exists>g. g \<in>\<^sub>c Y \<and> u = right_coproj(X, Y) \<circ>\<^sub>c g" using disj by auto
      then obtain g where g_type: "g \<in>\<^sub>c Y" and g_def: "u = right_coproj(X, Y) \<circ>\<^sub>c g" by auto
      have s1: "((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c u
          = ((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c g)"
        using g_def by simp
      have s2: "((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c g)
          = (((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c g"
        using comp_associative2[OF g_type right_proj_type gfull_type] by simp
      have s3: "(((eq_pred(X) \<circ>\<^sub>c \<langle>id(X), x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c g
          = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c g"
        using right_coproj_cfunc_coprod[OF g1_type g2_type] by simp
      have s4: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c g = \<f>"
      proof -
        have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c g = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g)" using comp_associative2[OF g_type terminal_func_type false_func_type] by simp
        also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF g_type] by simp
        also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
        finally show ?thesis by simp
      qed
      show ?thesis using s1 s2 s3 s4 pred_eq_f by simp
    qed
  qed
qed

lemma eq_pred_right_coproj:
  assumes u_type: "u \<in>\<^sub>c X \<Coprod> Y" and y_type: "y \<in>\<^sub>c Y"
  shows "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj(X, Y) \<circ>\<^sub>c y\<rangle>
      = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u"
proof -
  have ry_type: "right_coproj(X, Y) \<circ>\<^sub>c y \<in>\<^sub>c X \<Coprod> Y" using y_type right_proj_type comp_type by blast
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have yb_type: "y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> Y" using terminal_func_type[of Y] y_type comp_type by blast
  have pair1_type: "\<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> : Y \<rightarrow> Y \<times>\<^sub>c Y" using idY_type yb_type cfunc_prod_type by auto
  have g1_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using terminal_func_type[of X] false_func_type comp_type by blast
  have g2_type: "eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> : Y \<rightarrow> \<Omega>" using pair1_type eq_pred_type comp_type by blast
  have gfull_type: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) : X \<Coprod> Y \<rightarrow> \<Omega>"
    using cfunc_coprod_type[OF g1_type g2_type] by simp
  have upair_type: "\<langle>u, right_coproj(X, Y) \<circ>\<^sub>c y\<rangle> \<in>\<^sub>c (X \<Coprod> Y) \<times>\<^sub>c (X \<Coprod> Y)" using u_type ry_type cfunc_prod_type by auto
  have pred_type: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj(X, Y) \<circ>\<^sub>c y\<rangle> \<in>\<^sub>c \<Omega>" using upair_type eq_pred_type comp_type by blast

  show ?thesis
  proof (cases "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj(X, Y) \<circ>\<^sub>c y\<rangle> = \<t>")
    case True
    have u_eq_ry: "u = right_coproj(X, Y) \<circ>\<^sub>c y" using eq_pred_iff_eq[OF u_type ry_type] True by simp
    have s1: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u
        = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y)"
      using u_eq_ry by simp
    have s2: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c y)
        = (((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y"
      using comp_associative2[OF y_type right_proj_type gfull_type] by simp
    have s3: "(((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c y
        = (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c y"
      using right_coproj_cfunc_coprod[OF g1_type g2_type] by simp
    have s4: "(eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c y = eq_pred(Y) \<circ>\<^sub>c (\<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c y)"
      using comp_associative2[OF y_type pair1_type eq_pred_type] by simp
    have s5: "\<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c y = \<langle>y, y\<rangle>" using cart_prod_extract_left[OF y_type y_type] by simp
    have s6: "eq_pred(Y) \<circ>\<^sub>c \<langle>y, y\<rangle> = \<t>" using eq_pred_iff_eq[OF y_type y_type] by simp
    show ?thesis using s1 s2 s3 s4 s5 s6 True by simp
  next
    case False
    have pred_eq_f: "eq_pred(X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj(X, Y) \<circ>\<^sub>c y\<rangle> = \<f>"
      using true_false_only_truth_values[OF pred_type] False by auto
    have u_ne_ry: "u \<noteq> right_coproj(X, Y) \<circ>\<^sub>c y" using eq_pred_iff_eq_conv[OF u_type ry_type] pred_eq_f by simp
    have disj: "(\<exists>g. g \<in>\<^sub>c X \<and> u = left_coproj(X, Y) \<circ>\<^sub>c g) \<or> (\<exists>g. g \<in>\<^sub>c Y \<and> u = right_coproj(X, Y) \<circ>\<^sub>c g)"
      using coprojs_jointly_surj[OF u_type] by simp
    show ?thesis
    proof (cases "\<exists>g. g \<in>\<^sub>c Y \<and> u = right_coproj(X, Y) \<circ>\<^sub>c g")
      case True
      then obtain g where g_type: "g \<in>\<^sub>c Y" and g_def: "u = right_coproj(X, Y) \<circ>\<^sub>c g" by auto
      have y_ne_g: "g \<noteq> y" using u_ne_ry g_def by auto
      have s1: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u
          = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c g)"
        using g_def by simp
      have s2: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c (right_coproj(X, Y) \<circ>\<^sub>c g)
          = (((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c g"
        using comp_associative2[OF g_type right_proj_type gfull_type] by simp
      have s3: "(((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c right_coproj(X, Y)) \<circ>\<^sub>c g
          = (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c g"
        using right_coproj_cfunc_coprod[OF g1_type g2_type] by simp
      have s4: "(eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c g = eq_pred(Y) \<circ>\<^sub>c (\<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c g)"
        using comp_associative2[OF g_type pair1_type eq_pred_type] by simp
      have s5: "\<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c g = \<langle>g, y\<rangle>" using cart_prod_extract_left[OF g_type y_type] by simp
      have s6: "eq_pred(Y) \<circ>\<^sub>c \<langle>g, y\<rangle> = \<f>" using eq_pred_iff_eq_conv[OF g_type y_type] y_ne_g by simp
      show ?thesis using s1 s2 s3 s4 s5 s6 pred_eq_f by simp
    next
      case False
      then have "\<exists>g. g \<in>\<^sub>c X \<and> u = left_coproj(X, Y) \<circ>\<^sub>c g" using disj by auto
      then obtain g where g_type: "g \<in>\<^sub>c X" and g_def: "u = left_coproj(X, Y) \<circ>\<^sub>c g" by auto
      have s1: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u
          = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c g)"
        using g_def by simp
      have s2: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c (left_coproj(X, Y) \<circ>\<^sub>c g)
          = (((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c g"
        using comp_associative2[OF g_type left_proj_type gfull_type] by simp
      have s3: "(((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred(Y) \<circ>\<^sub>c \<langle>id(Y), y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c left_coproj(X, Y)) \<circ>\<^sub>c g
          = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c g"
        using left_coproj_cfunc_coprod[OF g1_type g2_type] by simp
      have s4: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c g = \<f>"
      proof -
        have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c g = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g)" using comp_associative2[OF g_type terminal_func_type false_func_type] by simp
        also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF g_type] by simp
        also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
        finally show ?thesis by simp
      qed
      show ?thesis using s1 s2 s3 s4 pred_eq_f by simp
    qed
  qed
qed

subsection \<open>Bowtie Product\<close>

definition cfunc_bowtie_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<bowtie>\<^sub>f" 55) where
  "f \<bowtie>\<^sub>f g = (left_coproj(codomain(f), codomain(g)) \<circ>\<^sub>c f) \<amalg> (right_coproj(codomain(f), codomain(g)) \<circ>\<^sub>c g)"

lemma cfunc_bowtie_prod_def2:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  shows "f \<bowtie>\<^sub>f g = (left_coproj(Y, W) \<circ>\<^sub>c f) \<amalg> (right_coproj(Y, W) \<circ>\<^sub>c g)"
proof -
  have codf: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  have codg: "codomain(g) = W" using g_type unfolding cfunc_type_def by auto
  show ?thesis unfolding cfunc_bowtie_prod_def using codf codg by simp
qed

lemma cfunc_bowtie_prod_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  shows "f \<bowtie>\<^sub>f g : X \<Coprod> V \<rightarrow> Y \<Coprod> W"
proof -
  have lc_type: "left_coproj(Y, W) \<circ>\<^sub>c f : X \<rightarrow> Y \<Coprod> W" using f_type left_proj_type comp_type by blast
  have rc_type: "right_coproj(Y, W) \<circ>\<^sub>c g : V \<rightarrow> Y \<Coprod> W" using g_type right_proj_type comp_type by blast
  show ?thesis using cfunc_bowtie_prod_def2[OF f_type g_type] cfunc_coprod_type[OF lc_type rc_type] by simp
qed

lemma left_coproj_cfunc_bowtie_prod:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  shows "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V) = left_coproj(Y, W) \<circ>\<^sub>c f"
proof -
  have lc_type: "left_coproj(Y, W) \<circ>\<^sub>c f : X \<rightarrow> Y \<Coprod> W" using f_type left_proj_type comp_type by blast
  have rc_type: "right_coproj(Y, W) \<circ>\<^sub>c g : V \<rightarrow> Y \<Coprod> W" using g_type right_proj_type comp_type by blast
  show ?thesis using cfunc_bowtie_prod_def2[OF f_type g_type] left_coproj_cfunc_coprod[OF lc_type rc_type] by simp
qed

lemma right_coproj_cfunc_bowtie_prod:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  shows "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V) = right_coproj(Y, W) \<circ>\<^sub>c g"
proof -
  have lc_type: "left_coproj(Y, W) \<circ>\<^sub>c f : X \<rightarrow> Y \<Coprod> W" using f_type left_proj_type comp_type by blast
  have rc_type: "right_coproj(Y, W) \<circ>\<^sub>c g : V \<rightarrow> Y \<Coprod> W" using g_type right_proj_type comp_type by blast
  show ?thesis using cfunc_bowtie_prod_def2[OF f_type g_type] right_coproj_cfunc_coprod[OF lc_type rc_type] by simp
qed

lemma cfunc_bowtie_prod_unique:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W" and h_type: "h : X \<Coprod> V \<rightarrow> Y \<Coprod> W"
  assumes h_left: "h \<circ>\<^sub>c left_coproj(X, V) = left_coproj(Y, W) \<circ>\<^sub>c f"
  assumes h_right: "h \<circ>\<^sub>c right_coproj(X, V) = right_coproj(Y, W) \<circ>\<^sub>c g"
  shows "h = f \<bowtie>\<^sub>f g"
proof -
  have lc_type: "left_coproj(Y, W) \<circ>\<^sub>c f : X \<rightarrow> Y \<Coprod> W" using f_type left_proj_type comp_type by blast
  have rc_type: "right_coproj(Y, W) \<circ>\<^sub>c g : V \<rightarrow> Y \<Coprod> W" using g_type right_proj_type comp_type by blast
  show ?thesis
    using cfunc_bowtie_prod_def2[OF f_type g_type] cfunc_coprod_unique[OF lc_type rc_type h_type h_left h_right] by simp
qed

text \<open>The lemma below is dual to Proposition 2.1.11 in Halvorson.\<close>
lemma identity_distributes_across_composition_dual:
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C"
  shows "(g \<circ>\<^sub>c f) \<bowtie>\<^sub>f id(X) = (g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id(X))"
proof -
  have gf_type: "g \<circ>\<^sub>c f : A \<rightarrow> C" using f_type g_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have fX_type: "f \<bowtie>\<^sub>f id(X) : A \<Coprod> X \<rightarrow> B \<Coprod> X" using cfunc_bowtie_prod_type[OF f_type idX_type] by simp
  have gX_type: "g \<bowtie>\<^sub>f id(X) : B \<Coprod> X \<rightarrow> C \<Coprod> X" using cfunc_bowtie_prod_type[OF g_type idX_type] by simp
  have comp_type_h: "(g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id(X)) : A \<Coprod> X \<rightarrow> C \<Coprod> X" using fX_type gX_type comp_type by blast
  have left_eq: "((g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id(X))) \<circ>\<^sub>c left_coproj(A, X) = left_coproj(C, X) \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
  proof -
    have s1: "((g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id(X))) \<circ>\<^sub>c left_coproj(A, X)
        = (g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c left_coproj(A, X))"
      using comp_associative2[OF left_proj_type fX_type gX_type] by simp
    have s2: "(f \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c left_coproj(A, X) = left_coproj(B, X) \<circ>\<^sub>c f"
      using left_coproj_cfunc_bowtie_prod[OF f_type idX_type] by simp
    have s3: "(g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (left_coproj(B, X) \<circ>\<^sub>c f) = ((g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c left_coproj(B, X)) \<circ>\<^sub>c f"
      using comp_associative2[OF f_type left_proj_type gX_type] by simp
    have s4: "(g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c left_coproj(B, X) = left_coproj(C, X) \<circ>\<^sub>c g"
      using left_coproj_cfunc_bowtie_prod[OF g_type idX_type] by simp
    have s5: "(left_coproj(C, X) \<circ>\<^sub>c g) \<circ>\<^sub>c f = left_coproj(C, X) \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
      using comp_associative2[OF f_type g_type left_proj_type] by simp
    show ?thesis using s1 s2 s3 s4 s5 by simp
  qed
  have right_eq: "((g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id(X))) \<circ>\<^sub>c right_coproj(A, X) = right_coproj(C, X) \<circ>\<^sub>c id(X)"
  proof -
    have s1: "((g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id(X))) \<circ>\<^sub>c right_coproj(A, X)
        = (g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c right_coproj(A, X))"
      using comp_associative2[OF right_proj_type fX_type gX_type] by simp
    have s2: "(f \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c right_coproj(A, X) = right_coproj(B, X) \<circ>\<^sub>c id(X)"
      using right_coproj_cfunc_bowtie_prod[OF f_type idX_type] by simp
    have s2b: "right_coproj(B, X) \<circ>\<^sub>c id(X) = right_coproj(B, X)" using id_right_unit2[OF right_proj_type] by simp
    have s3: "(g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c right_coproj(B, X) = right_coproj(C, X) \<circ>\<^sub>c id(X)"
      using right_coproj_cfunc_bowtie_prod[OF g_type idX_type] by simp
    show ?thesis using s1 s2 s2b s3 by simp
  qed
  show ?thesis using cfunc_bowtie_prod_unique[OF gf_type idX_type comp_type_h left_eq right_eq] by simp
qed

lemma coproduct_of_beta:
  "\<beta>\<^bsub>X\<^esub> \<amalg> \<beta>\<^bsub>Y\<^esub> = \<beta>\<^bsub>X \<Coprod> Y\<^esub>"
proof -
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have bY_type: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by (rule terminal_func_type)
  have h_type: "\<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> \<one>" by (rule terminal_func_type)
  have h_left: "\<beta>\<^bsub>X \<Coprod> Y\<^esub> \<circ>\<^sub>c left_coproj(X, Y) = \<beta>\<^bsub>X\<^esub>" using terminal_func_comp[OF left_proj_type] by simp
  have h_right: "\<beta>\<^bsub>X \<Coprod> Y\<^esub> \<circ>\<^sub>c right_coproj(X, Y) = \<beta>\<^bsub>Y\<^esub>" using terminal_func_comp[OF right_proj_type] by simp
  show ?thesis using cfunc_coprod_unique[OF bX_type bY_type h_type h_left h_right] by simp
qed

lemma cfunc_bowtieprod_comp_cfunc_coprod:
  assumes a_type: "a : Y \<rightarrow> Z" and b_type: "b : W \<rightarrow> Z"
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  shows "(a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) = (a \<circ>\<^sub>c f) \<amalg> (b \<circ>\<^sub>c g)"
proof -
  have af_type: "a \<circ>\<^sub>c f : X \<rightarrow> Z" using f_type a_type comp_type by blast
  have bg_type: "b \<circ>\<^sub>c g : V \<rightarrow> Z" using g_type b_type comp_type by blast
  have ab_type: "a \<amalg> b : Y \<Coprod> W \<rightarrow> Z" using cfunc_coprod_type[OF a_type b_type] by simp
  have fg_type: "f \<bowtie>\<^sub>f g : X \<Coprod> V \<rightarrow> Y \<Coprod> W" using cfunc_bowtie_prod_type[OF f_type g_type] by simp
  have h_type: "(a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) : X \<Coprod> V \<rightarrow> Z" using fg_type ab_type comp_type by blast
  have left_eq: "((a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V) = a \<circ>\<^sub>c f"
  proof -
    have s1: "((a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V) = (a \<amalg> b) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V))"
      using comp_associative2[OF left_proj_type fg_type ab_type] by simp
    have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V) = left_coproj(Y, W) \<circ>\<^sub>c f"
      using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
    have s3: "(a \<amalg> b) \<circ>\<^sub>c (left_coproj(Y, W) \<circ>\<^sub>c f) = ((a \<amalg> b) \<circ>\<^sub>c left_coproj(Y, W)) \<circ>\<^sub>c f"
      using comp_associative2[OF f_type left_proj_type ab_type] by simp
    have s4: "(a \<amalg> b) \<circ>\<^sub>c left_coproj(Y, W) = a" using left_coproj_cfunc_coprod[OF a_type b_type] by simp
    show ?thesis using s1 s2 s3 s4 by simp
  qed
  have right_eq: "((a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V) = b \<circ>\<^sub>c g"
  proof -
    have s1: "((a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V) = (a \<amalg> b) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V))"
      using comp_associative2[OF right_proj_type fg_type ab_type] by simp
    have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V) = right_coproj(Y, W) \<circ>\<^sub>c g"
      using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
    have s3: "(a \<amalg> b) \<circ>\<^sub>c (right_coproj(Y, W) \<circ>\<^sub>c g) = ((a \<amalg> b) \<circ>\<^sub>c right_coproj(Y, W)) \<circ>\<^sub>c g"
      using comp_associative2[OF g_type right_proj_type ab_type] by simp
    have s4: "(a \<amalg> b) \<circ>\<^sub>c right_coproj(Y, W) = b" using right_coproj_cfunc_coprod[OF a_type b_type] by simp
    show ?thesis using s1 s2 s3 s4 by simp
  qed
  show ?thesis using cfunc_coprod_unique[OF af_type bg_type h_type left_eq right_eq] by simp
qed

lemma id_bowtie_prod: "id(X) \<bowtie>\<^sub>f id(Y) = id(X \<Coprod> Y)"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have idXY_type: "id(X \<Coprod> Y) : X \<Coprod> Y \<rightarrow> X \<Coprod> Y" by (rule id_type)
  have left_eq: "id(X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) = left_coproj(X, Y) \<circ>\<^sub>c id(X)"
  proof -
    have "id(X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) = left_coproj(X, Y)" using id_left_unit2[OF left_proj_type] by simp
    also have "... = left_coproj(X, Y) \<circ>\<^sub>c id(X)" using id_right_unit2[OF left_proj_type] by simp
    finally show ?thesis by simp
  qed
  have right_eq: "id(X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) = right_coproj(X, Y) \<circ>\<^sub>c id(Y)"
  proof -
    have "id(X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) = right_coproj(X, Y)" using id_left_unit2[OF right_proj_type] by simp
    also have "... = right_coproj(X, Y) \<circ>\<^sub>c id(Y)" using id_right_unit2[OF right_proj_type] by simp
    finally show ?thesis by simp
  qed
  show ?thesis using cfunc_bowtie_prod_unique[OF idX_type idY_type idXY_type left_eq right_eq] by simp
qed

lemma cfunc_bowtie_prod_comp_cfunc_bowtie_prod:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W" and x_type: "x : Y \<rightarrow> S" and y_type: "y : W \<rightarrow> T"
  shows "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) = (x \<circ>\<^sub>c f) \<bowtie>\<^sub>f (y \<circ>\<^sub>c g)"
proof -
  have xf_type: "x \<circ>\<^sub>c f : X \<rightarrow> S" using f_type x_type comp_type by blast
  have yg_type: "y \<circ>\<^sub>c g : V \<rightarrow> T" using g_type y_type comp_type by blast
  have xy_type: "x \<bowtie>\<^sub>f y : Y \<Coprod> W \<rightarrow> S \<Coprod> T" using cfunc_bowtie_prod_type[OF x_type y_type] by simp
  have fg_type: "f \<bowtie>\<^sub>f g : X \<Coprod> V \<rightarrow> Y \<Coprod> W" using cfunc_bowtie_prod_type[OF f_type g_type] by simp
  have h_type: "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) : X \<Coprod> V \<rightarrow> S \<Coprod> T" using fg_type xy_type comp_type by blast
  have left_eq: "((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V) = left_coproj(S, T) \<circ>\<^sub>c (x \<circ>\<^sub>c f)"
  proof -
    have s1: "((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V) = (x \<bowtie>\<^sub>f y) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V))"
      using comp_associative2[OF left_proj_type fg_type xy_type] by simp
    have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V) = left_coproj(Y, W) \<circ>\<^sub>c f"
      using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
    have s3: "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (left_coproj(Y, W) \<circ>\<^sub>c f) = ((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c left_coproj(Y, W)) \<circ>\<^sub>c f"
      using comp_associative2[OF f_type left_proj_type xy_type] by simp
    have s4: "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c left_coproj(Y, W) = left_coproj(S, T) \<circ>\<^sub>c x"
      using left_coproj_cfunc_bowtie_prod[OF x_type y_type] by simp
    have s5: "(left_coproj(S, T) \<circ>\<^sub>c x) \<circ>\<^sub>c f = left_coproj(S, T) \<circ>\<^sub>c (x \<circ>\<^sub>c f)"
      using comp_associative2[OF f_type x_type left_proj_type] by simp
    show ?thesis using s1 s2 s3 s4 s5 by simp
  qed
  have right_eq: "((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V) = right_coproj(S, T) \<circ>\<^sub>c (y \<circ>\<^sub>c g)"
  proof -
    have s1: "((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V) = (x \<bowtie>\<^sub>f y) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V))"
      using comp_associative2[OF right_proj_type fg_type xy_type] by simp
    have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V) = right_coproj(Y, W) \<circ>\<^sub>c g"
      using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
    have s3: "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (right_coproj(Y, W) \<circ>\<^sub>c g) = ((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c right_coproj(Y, W)) \<circ>\<^sub>c g"
      using comp_associative2[OF g_type right_proj_type xy_type] by simp
    have s4: "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c right_coproj(Y, W) = right_coproj(S, T) \<circ>\<^sub>c y"
      using right_coproj_cfunc_bowtie_prod[OF x_type y_type] by simp
    have s5: "(right_coproj(S, T) \<circ>\<^sub>c y) \<circ>\<^sub>c g = right_coproj(S, T) \<circ>\<^sub>c (y \<circ>\<^sub>c g)"
      using comp_associative2[OF g_type y_type right_proj_type] by simp
    show ?thesis using s1 s2 s3 s4 s5 by simp
  qed
  show ?thesis using cfunc_bowtie_prod_unique[OF xf_type yg_type h_type left_eq right_eq] by simp
qed

lemma cfunc_bowtieprod_epi:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  assumes f_epi: "epimorphism(f)" and g_epi: "epimorphism(g)"
  shows "epimorphism(f \<bowtie>\<^sub>f g)"
proof -
  have fg_type: "f \<bowtie>\<^sub>f g : X \<Coprod> V \<rightarrow> Y \<Coprod> W" using cfunc_bowtie_prod_type[OF f_type g_type] by simp
  show ?thesis unfolding epimorphism_def3[OF fg_type]
  proof (intro allI impI)
    fix x y A
    assume "x : Y \<Coprod> W \<rightarrow> A \<and> y : Y \<Coprod> W \<rightarrow> A"
    then have x_type: "x : Y \<Coprod> W \<rightarrow> A" and y_type: "y : Y \<Coprod> W \<rightarrow> A" by auto
    assume eqs: "x \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) = y \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)"

    obtain x1 x2 where x_expand: "x = x1 \<amalg> x2" and x1_type: "x1 : Y \<rightarrow> A" and x2_type: "x2 : W \<rightarrow> A"
      using coprod_decomp[OF x_type] by blast
    obtain y1 y2 where y_expand: "y = y1 \<amalg> y2" and y1_type: "y1 : Y \<rightarrow> A" and y2_type: "y2 : W \<rightarrow> A"
      using coprod_decomp[OF y_type] by blast
    have x1x2_type: "x1 \<amalg> x2 : Y \<Coprod> W \<rightarrow> A" using cfunc_coprod_type[OF x1_type x2_type] by simp
    have y1y2_type: "y1 \<amalg> y2 : Y \<Coprod> W \<rightarrow> A" using cfunc_coprod_type[OF y1_type y2_type] by simp

    have x1_eq_y1: "x1 = y1"
    proof -
      have chain_x: "x1 \<circ>\<^sub>c f = ((x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V)"
      proof -
        have a1: "(x1 \<amalg> x2) \<circ>\<^sub>c left_coproj(Y, W) = x1" using left_coproj_cfunc_coprod[OF x1_type x2_type] by simp
        have a2: "((x1 \<amalg> x2) \<circ>\<^sub>c left_coproj(Y, W)) \<circ>\<^sub>c f = x1 \<circ>\<^sub>c f" using a1 by simp
        have a3: "((x1 \<amalg> x2) \<circ>\<^sub>c left_coproj(Y, W)) \<circ>\<^sub>c f = (x1 \<amalg> x2) \<circ>\<^sub>c (left_coproj(Y, W) \<circ>\<^sub>c f)"
          using comp_associative2[OF f_type left_proj_type x1x2_type] by simp
        have a4: "left_coproj(Y, W) \<circ>\<^sub>c f = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V)"
          using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
        have a5: "(x1 \<amalg> x2) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V)) = ((x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V)"
          using comp_associative2[OF left_proj_type fg_type x1x2_type] by simp
        show ?thesis using a2 a3 a4 a5 by simp
      qed
      have xfg_eq: "((x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V) = ((y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V)"
        using eqs x_expand y_expand by simp
      have chain_y: "((y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V) = y1 \<circ>\<^sub>c f"
      proof -
        have b1: "(y1 \<amalg> y2) \<circ>\<^sub>c left_coproj(Y, W) = y1" using left_coproj_cfunc_coprod[OF y1_type y2_type] by simp
        have b2: "((y1 \<amalg> y2) \<circ>\<^sub>c left_coproj(Y, W)) \<circ>\<^sub>c f = y1 \<circ>\<^sub>c f" using b1 by simp
        have b3: "((y1 \<amalg> y2) \<circ>\<^sub>c left_coproj(Y, W)) \<circ>\<^sub>c f = (y1 \<amalg> y2) \<circ>\<^sub>c (left_coproj(Y, W) \<circ>\<^sub>c f)"
          using comp_associative2[OF f_type left_proj_type y1y2_type] by simp
        have b4: "left_coproj(Y, W) \<circ>\<^sub>c f = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V)"
          using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
        have b5: "(y1 \<amalg> y2) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V)) = ((y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c left_coproj(X, V)"
          using comp_associative2[OF left_proj_type fg_type y1y2_type] by simp
        show ?thesis using b2 b3 b4 b5 by simp
      qed
      have x1f_eq_y1f: "x1 \<circ>\<^sub>c f = y1 \<circ>\<^sub>c f" using chain_x xfg_eq chain_y by simp
      show ?thesis using epimorphism_def3[OF f_type] f_epi x1f_eq_y1f x1_type y1_type by auto
    qed

    have x2_eq_y2: "x2 = y2"
    proof -
      have chain_x: "x2 \<circ>\<^sub>c g = ((x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V)"
      proof -
        have a1: "(x1 \<amalg> x2) \<circ>\<^sub>c right_coproj(Y, W) = x2" using right_coproj_cfunc_coprod[OF x1_type x2_type] by simp
        have a2: "((x1 \<amalg> x2) \<circ>\<^sub>c right_coproj(Y, W)) \<circ>\<^sub>c g = x2 \<circ>\<^sub>c g" using a1 by simp
        have a3: "((x1 \<amalg> x2) \<circ>\<^sub>c right_coproj(Y, W)) \<circ>\<^sub>c g = (x1 \<amalg> x2) \<circ>\<^sub>c (right_coproj(Y, W) \<circ>\<^sub>c g)"
          using comp_associative2[OF g_type right_proj_type x1x2_type] by simp
        have a4: "right_coproj(Y, W) \<circ>\<^sub>c g = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V)"
          using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
        have a5: "(x1 \<amalg> x2) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V)) = ((x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V)"
          using comp_associative2[OF right_proj_type fg_type x1x2_type] by simp
        show ?thesis using a2 a3 a4 a5 by simp
      qed
      have xfg_eq: "((x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V) = ((y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V)"
        using eqs x_expand y_expand by simp
      have chain_y: "((y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V) = y2 \<circ>\<^sub>c g"
      proof -
        have b1: "(y1 \<amalg> y2) \<circ>\<^sub>c right_coproj(Y, W) = y2" using right_coproj_cfunc_coprod[OF y1_type y2_type] by simp
        have b2: "((y1 \<amalg> y2) \<circ>\<^sub>c right_coproj(Y, W)) \<circ>\<^sub>c g = y2 \<circ>\<^sub>c g" using b1 by simp
        have b3: "((y1 \<amalg> y2) \<circ>\<^sub>c right_coproj(Y, W)) \<circ>\<^sub>c g = (y1 \<amalg> y2) \<circ>\<^sub>c (right_coproj(Y, W) \<circ>\<^sub>c g)"
          using comp_associative2[OF g_type right_proj_type y1y2_type] by simp
        have b4: "right_coproj(Y, W) \<circ>\<^sub>c g = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V)"
          using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
        have b5: "(y1 \<amalg> y2) \<circ>\<^sub>c ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V)) = ((y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)) \<circ>\<^sub>c right_coproj(X, V)"
          using comp_associative2[OF right_proj_type fg_type y1y2_type] by simp
        show ?thesis using b2 b3 b4 b5 by simp
      qed
      have x2g_eq_y2g: "x2 \<circ>\<^sub>c g = y2 \<circ>\<^sub>c g" using chain_x xfg_eq chain_y by simp
      show ?thesis using epimorphism_def3[OF g_type] g_epi x2g_eq_y2g x2_type y2_type by auto
    qed

    show "x = y" using x_expand y_expand x1_eq_y1 x2_eq_y2 by simp
  qed
qed

lemma cfunc_bowtieprod_inj:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  assumes f_inj: "injective(f)" and g_inj: "injective(g)"
  shows "injective(f \<bowtie>\<^sub>f g)"
proof -
  have fg_type: "f \<bowtie>\<^sub>f g : X \<Coprod> V \<rightarrow> Y \<Coprod> W" using cfunc_bowtie_prod_type[OF f_type g_type] by simp
  have lc_fg: "\<And>a. a \<in>\<^sub>c X \<Longrightarrow> (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, V) \<circ>\<^sub>c a) = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c a)"
  proof -
    fix a assume a_type: "a \<in>\<^sub>c X"
    have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, V) \<circ>\<^sub>c a) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V)) \<circ>\<^sub>c a"
      using comp_associative2[OF a_type left_proj_type fg_type] by simp
    have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, V) = left_coproj(Y, W) \<circ>\<^sub>c f"
      using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
    have s3: "(left_coproj(Y, W) \<circ>\<^sub>c f) \<circ>\<^sub>c a = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c a)"
      using comp_associative2[OF a_type f_type left_proj_type] by simp
    show "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, V) \<circ>\<^sub>c a) = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c a)"
      using s1 s2 s3 by simp
  qed
  have rc_fg: "\<And>b. b \<in>\<^sub>c V \<Longrightarrow> (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, V) \<circ>\<^sub>c b) = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c b)"
  proof -
    fix b assume b_type: "b \<in>\<^sub>c V"
    have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, V) \<circ>\<^sub>c b) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V)) \<circ>\<^sub>c b"
      using comp_associative2[OF b_type right_proj_type fg_type] by simp
    have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, V) = right_coproj(Y, W) \<circ>\<^sub>c g"
      using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
    have s3: "(right_coproj(Y, W) \<circ>\<^sub>c g) \<circ>\<^sub>c b = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c b)"
      using comp_associative2[OF b_type g_type right_proj_type] by simp
    show "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, V) \<circ>\<^sub>c b) = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c b)"
      using s1 s2 s3 by simp
  qed
  show ?thesis unfolding injective_def2[OF fg_type]
  proof (intro allI impI)
    fix z1 z2
    assume "z1 \<in>\<^sub>c X \<Coprod> V \<and> z2 \<in>\<^sub>c X \<Coprod> V \<and> (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1 = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2"
    then have z1_type: "z1 \<in>\<^sub>c X \<Coprod> V" and z2_type: "z2 \<in>\<^sub>c X \<Coprod> V"
      and eqs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1 = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2" by auto
    have z1_disj: "(\<exists>x1. x1 \<in>\<^sub>c X \<and> z1 = left_coproj(X, V) \<circ>\<^sub>c x1) \<or> (\<exists>y1. y1 \<in>\<^sub>c V \<and> z1 = right_coproj(X, V) \<circ>\<^sub>c y1)"
      using coprojs_jointly_surj[OF z1_type] by simp
    have z2_disj: "(\<exists>x2. x2 \<in>\<^sub>c X \<and> z2 = left_coproj(X, V) \<circ>\<^sub>c x2) \<or> (\<exists>y2. y2 \<in>\<^sub>c V \<and> z2 = right_coproj(X, V) \<circ>\<^sub>c y2)"
      using coprojs_jointly_surj[OF z2_type] by simp
    show "z1 = z2"
    proof (cases "\<exists>x1. x1 \<in>\<^sub>c X \<and> z1 = left_coproj(X, V) \<circ>\<^sub>c x1")
      case True
      then obtain x1 where x1_type: "x1 \<in>\<^sub>c X" and z1_eq: "z1 = left_coproj(X, V) \<circ>\<^sub>c x1" by auto
      show "z1 = z2"
      proof (cases "\<exists>x2. x2 \<in>\<^sub>c X \<and> z2 = left_coproj(X, V) \<circ>\<^sub>c x2")
        case True
        then obtain x2 where x2_type: "x2 \<in>\<^sub>c X" and z2_eq: "z2 = left_coproj(X, V) \<circ>\<^sub>c x2" by auto
        have lhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1 = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x1)" using z1_eq lc_fg[OF x1_type] by simp
        have rhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2 = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x2)" using z2_eq lc_fg[OF x2_type] by simp
        have eq2: "left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x1) = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x2)" using eqs lhs rhs by simp
        have fx1_type: "f \<circ>\<^sub>c x1 : \<one> \<rightarrow> Y" using x1_type f_type comp_type by blast
        have fx2_type: "f \<circ>\<^sub>c x2 : \<one> \<rightarrow> Y" using x2_type f_type comp_type by blast
        have lp_type: "left_coproj(Y, W) : Y \<rightarrow> Y \<Coprod> W" by (rule left_proj_type)
        have lp_mono: "monomorphism(left_coproj(Y, W))" by (rule left_coproj_are_monomorphisms)
        have fx_eq: "f \<circ>\<^sub>c x1 = f \<circ>\<^sub>c x2"
          using monomorphism_def3[OF lp_type, THEN iffD1, rule_format, where g="f \<circ>\<^sub>c x1" and h="f \<circ>\<^sub>c x2" and A="\<one>"]
            lp_mono fx1_type fx2_type eq2 by auto
        show "z1 = z2" using z1_eq z2_eq injective_def2[OF f_type] f_inj fx_eq x1_type x2_type by auto
      next
        case False
        then obtain y2 where y2_type: "y2 \<in>\<^sub>c V" and z2_eq: "z2 = right_coproj(X, V) \<circ>\<^sub>c y2" using z2_disj by auto
        have lhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1 = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x1)" using z1_eq lc_fg[OF x1_type] by simp
        have rhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2 = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y2)" using z2_eq rc_fg[OF y2_type] by simp
        have eq2: "left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x1) = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y2)" using eqs lhs rhs by simp
        have fx1_type: "f \<circ>\<^sub>c x1 \<in>\<^sub>c Y" using x1_type f_type comp_type by blast
        have gy2_type: "g \<circ>\<^sub>c y2 \<in>\<^sub>c W" using y2_type g_type comp_type by blast
        have "False" using coproducts_disjoint[OF fx1_type gy2_type] eq2 by simp
        then show "z1 = z2" by simp
      qed
    next
      case False
      then obtain y1 where y1_type: "y1 \<in>\<^sub>c V" and z1_eq: "z1 = right_coproj(X, V) \<circ>\<^sub>c y1" using z1_disj by auto
      show "z1 = z2"
      proof (cases "\<exists>x2. x2 \<in>\<^sub>c X \<and> z2 = left_coproj(X, V) \<circ>\<^sub>c x2")
        case True
        then obtain x2 where x2_type: "x2 \<in>\<^sub>c X" and z2_eq: "z2 = left_coproj(X, V) \<circ>\<^sub>c x2" by auto
        have lhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1 = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y1)" using z1_eq rc_fg[OF y1_type] by simp
        have rhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2 = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x2)" using z2_eq lc_fg[OF x2_type] by simp
        have eq2: "right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y1) = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x2)" using eqs lhs rhs by simp
        have fx2_type: "f \<circ>\<^sub>c x2 \<in>\<^sub>c Y" using x2_type f_type comp_type by blast
        have gy1_type: "g \<circ>\<^sub>c y1 \<in>\<^sub>c W" using y1_type g_type comp_type by blast
        have "False" using coproducts_disjoint[OF fx2_type gy1_type] eq2 by simp
        then show "z1 = z2" by simp
      next
        case False
        then obtain y2 where y2_type: "y2 \<in>\<^sub>c V" and z2_eq: "z2 = right_coproj(X, V) \<circ>\<^sub>c y2" using z2_disj by auto
        have lhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1 = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y1)" using z1_eq rc_fg[OF y1_type] by simp
        have rhs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2 = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y2)" using z2_eq rc_fg[OF y2_type] by simp
        have eq2: "right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y1) = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y2)" using eqs lhs rhs by simp
        have gy1_type: "g \<circ>\<^sub>c y1 : \<one> \<rightarrow> W" using y1_type g_type comp_type by blast
        have gy2_type: "g \<circ>\<^sub>c y2 : \<one> \<rightarrow> W" using y2_type g_type comp_type by blast
        have rp_type: "right_coproj(Y, W) : W \<rightarrow> Y \<Coprod> W" by (rule right_proj_type)
        have rp_mono: "monomorphism(right_coproj(Y, W))" by (rule right_coproj_are_monomorphisms)
        have gy_eq: "g \<circ>\<^sub>c y1 = g \<circ>\<^sub>c y2"
          using monomorphism_def3[OF rp_type, THEN iffD1, rule_format, where g="g \<circ>\<^sub>c y1" and h="g \<circ>\<^sub>c y2" and A="\<one>"]
            rp_mono gy1_type gy2_type eq2 by auto
        show "z1 = z2" using z1_eq z2_eq injective_def2[OF g_type] g_inj gy_eq y1_type y2_type by auto
      qed
    qed
  qed
qed

lemma cfunc_bowtieprod_inj_converse:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : Z \<rightarrow> W"
  assumes inj_fg: "injective(f \<bowtie>\<^sub>f g)"
  shows "injective(f) \<and> injective(g)"
proof -
  have fg_type: "f \<bowtie>\<^sub>f g : X \<Coprod> Z \<rightarrow> Y \<Coprod> W" using cfunc_bowtie_prod_type[OF f_type g_type] by simp
  have fg_mono: "monomorphism(f \<bowtie>\<^sub>f g)" using injective_imp_monomorphism[OF inj_fg] by simp
  have inj_f: "injective(f)"
    unfolding injective_def2[OF f_type]
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X" and eqs: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y" by auto
    have lift: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c x) = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c y)"
    proof -
      have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c x) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, Z)) \<circ>\<^sub>c x"
        using comp_associative2[OF x_type left_proj_type fg_type] by simp
      have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, Z) = left_coproj(Y, W) \<circ>\<^sub>c f"
        using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
      have s3: "(left_coproj(Y, W) \<circ>\<^sub>c f) \<circ>\<^sub>c x = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x)"
        using comp_associative2[OF x_type f_type left_proj_type] by simp
      have s4: "(left_coproj(Y, W) \<circ>\<^sub>c f) \<circ>\<^sub>c y = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c y)"
        using comp_associative2[OF y_type f_type left_proj_type] by simp
      have s5: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c y) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, Z)) \<circ>\<^sub>c y"
        using comp_associative2[OF y_type left_proj_type fg_type] by simp
      show ?thesis using s1 s2 s3 s4 s5 eqs by simp
    qed
    have lx_type: "left_coproj(X, Z) \<circ>\<^sub>c x : \<one> \<rightarrow> X \<Coprod> Z" using x_type left_proj_type comp_type by blast
    have ly_type: "left_coproj(X, Z) \<circ>\<^sub>c y : \<one> \<rightarrow> X \<Coprod> Z" using y_type left_proj_type comp_type by blast
    have lxy_eq: "left_coproj(X, Z) \<circ>\<^sub>c x = left_coproj(X, Z) \<circ>\<^sub>c y"
      using monomorphism_def3[OF fg_type, THEN iffD1, rule_format,
          where g="left_coproj(X, Z) \<circ>\<^sub>c x" and h="left_coproj(X, Z) \<circ>\<^sub>c y" and A="\<one>"]
        fg_mono lx_type ly_type lift by auto
    have lp_type: "left_coproj(X, Z) : X \<rightarrow> X \<Coprod> Z" by (rule left_proj_type)
    have lp_mono: "monomorphism(left_coproj(X, Z))" by (rule left_coproj_are_monomorphisms)
    show "x = y"
      using monomorphism_def3[OF lp_type, THEN iffD1, rule_format, where g=x and h=y and A="\<one>"]
        lp_mono x_type y_type lxy_eq by auto
  qed
  have inj_g: "injective(g)"
    unfolding injective_def2[OF g_type]
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c Z \<and> y \<in>\<^sub>c Z \<and> g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c Z" and y_type: "y \<in>\<^sub>c Z" and eqs: "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y" by auto
    have lift: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c x) = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c y)"
    proof -
      have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c x) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, Z)) \<circ>\<^sub>c x"
        using comp_associative2[OF x_type right_proj_type fg_type] by simp
      have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, Z) = right_coproj(Y, W) \<circ>\<^sub>c g"
        using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
      have s3: "(right_coproj(Y, W) \<circ>\<^sub>c g) \<circ>\<^sub>c x = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c x)"
        using comp_associative2[OF x_type g_type right_proj_type] by simp
      have s4: "(right_coproj(Y, W) \<circ>\<^sub>c g) \<circ>\<^sub>c y = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c y)"
        using comp_associative2[OF y_type g_type right_proj_type] by simp
      have s5: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c y) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, Z)) \<circ>\<^sub>c y"
        using comp_associative2[OF y_type right_proj_type fg_type] by simp
      show ?thesis using s1 s2 s3 s4 s5 eqs by simp
    qed
    have rx_type: "right_coproj(X, Z) \<circ>\<^sub>c x : \<one> \<rightarrow> X \<Coprod> Z" using x_type right_proj_type comp_type by blast
    have ry_type: "right_coproj(X, Z) \<circ>\<^sub>c y : \<one> \<rightarrow> X \<Coprod> Z" using y_type right_proj_type comp_type by blast
    have rxy_eq: "right_coproj(X, Z) \<circ>\<^sub>c x = right_coproj(X, Z) \<circ>\<^sub>c y"
      using monomorphism_def3[OF fg_type, THEN iffD1, rule_format,
          where g="right_coproj(X, Z) \<circ>\<^sub>c x" and h="right_coproj(X, Z) \<circ>\<^sub>c y" and A="\<one>"]
        fg_mono rx_type ry_type lift by auto
    have rp_type: "right_coproj(X, Z) : Z \<rightarrow> X \<Coprod> Z" by (rule right_proj_type)
    have rp_mono: "monomorphism(right_coproj(X, Z))" by (rule right_coproj_are_monomorphisms)
    show "x = y"
      using monomorphism_def3[OF rp_type, THEN iffD1, rule_format, where g=x and h=y and A="\<one>"]
        rp_mono x_type y_type rxy_eq by auto
  qed
  show ?thesis using inj_f inj_g by simp
qed

lemma cfunc_bowtieprod_iso:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  assumes f_iso: "isomorphism(f)" and g_iso: "isomorphism(g)"
  shows "isomorphism(f \<bowtie>\<^sub>f g)"
proof -
  have f_epi: "epimorphism(f)" using iso_imp_epi_and_monic[OF f_iso] by (rule conjunct1)
  have g_epi: "epimorphism(g)" using iso_imp_epi_and_monic[OF g_iso] by (rule conjunct1)
  have f_mono: "monomorphism(f)" using iso_imp_epi_and_monic[OF f_iso] by (rule conjunct2)
  have g_mono: "monomorphism(g)" using iso_imp_epi_and_monic[OF g_iso] by (rule conjunct2)
  have f_inj: "injective(f)" using monomorphism_imp_injective[OF f_mono] by simp
  have g_inj: "injective(g)" using monomorphism_imp_injective[OF g_mono] by simp
  have fg_epi: "epimorphism(f \<bowtie>\<^sub>f g)" using cfunc_bowtieprod_epi[OF f_type g_type f_epi g_epi] by simp
  have fg_inj: "injective(f \<bowtie>\<^sub>f g)" using cfunc_bowtieprod_inj[OF f_type g_type f_inj g_inj] by simp
  have fg_mono: "monomorphism(f \<bowtie>\<^sub>f g)" using injective_imp_monomorphism[OF fg_inj] by simp
  show ?thesis using epi_mon_is_iso[OF fg_epi fg_mono] by simp
qed

lemma cfunc_bowtieprod_surj_converse:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : Z \<rightarrow> W"
  assumes surj_fg: "surjective(f \<bowtie>\<^sub>f g)"
  shows "surjective(f) \<and> surjective(g)"
proof -
  have fg_type: "f \<bowtie>\<^sub>f g : X \<Coprod> Z \<rightarrow> Y \<Coprod> W" using cfunc_bowtie_prod_type[OF f_type g_type] by simp
  have surj_f: "surjective(f)"
    unfolding surjective_def2[OF f_type]
  proof (intro allI impI)
    fix y
    assume y_type: "y \<in>\<^sub>c Y"
    have ly_type: "left_coproj(Y, W) \<circ>\<^sub>c y \<in>\<^sub>c Y \<Coprod> W" using y_type left_proj_type comp_type by blast
    obtain xz where xz_type: "xz \<in>\<^sub>c X \<Coprod> Z" and xz_eq: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c xz = left_coproj(Y, W) \<circ>\<^sub>c y"
      using surjective_def2[OF fg_type] surj_fg ly_type by auto
    have xz_disj: "(\<exists>x. x \<in>\<^sub>c X \<and> xz = left_coproj(X, Z) \<circ>\<^sub>c x) \<or> (\<exists>z. z \<in>\<^sub>c Z \<and> xz = right_coproj(X, Z) \<circ>\<^sub>c z)"
      using coprojs_jointly_surj[OF xz_type] by simp
    show "\<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = y"
    proof (cases "\<exists>x. x \<in>\<^sub>c X \<and> xz = left_coproj(X, Z) \<circ>\<^sub>c x")
      case True
      then obtain x where x_type: "x \<in>\<^sub>c X" and xz_eq2: "xz = left_coproj(X, Z) \<circ>\<^sub>c x" by auto
      have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c x) = left_coproj(Y, W) \<circ>\<^sub>c y" using xz_eq xz_eq2 by simp
      have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c x) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, Z)) \<circ>\<^sub>c x"
        using comp_associative2[OF x_type left_proj_type fg_type] by simp
      have s3: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, Z) = left_coproj(Y, W) \<circ>\<^sub>c f"
        using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
      have s4: "(left_coproj(Y, W) \<circ>\<^sub>c f) \<circ>\<^sub>c x = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x)"
        using comp_associative2[OF x_type f_type left_proj_type] by simp
      have eq2: "left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x) = left_coproj(Y, W) \<circ>\<^sub>c y" using s1 s2 s3 s4 by simp
      have fx_type: "f \<circ>\<^sub>c x : \<one> \<rightarrow> Y" using x_type f_type comp_type by blast
      have lp_type: "left_coproj(Y, W) : Y \<rightarrow> Y \<Coprod> W" by (rule left_proj_type)
      have lp_mono: "monomorphism(left_coproj(Y, W))" by (rule left_coproj_are_monomorphisms)
      have fx_eq_y: "f \<circ>\<^sub>c x = y"
        using monomorphism_def3[OF lp_type, THEN iffD1, rule_format, where g="f \<circ>\<^sub>c x" and h=y and A="\<one>"]
          lp_mono fx_type y_type eq2 by auto
      show ?thesis using x_type fx_eq_y by auto
    next
      case False
      then obtain z where z_type: "z \<in>\<^sub>c Z" and xz_eq2: "xz = right_coproj(X, Z) \<circ>\<^sub>c z" using xz_disj by auto
      have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c z) = left_coproj(Y, W) \<circ>\<^sub>c y" using xz_eq xz_eq2 by simp
      have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c z) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, Z)) \<circ>\<^sub>c z"
        using comp_associative2[OF z_type right_proj_type fg_type] by simp
      have s3: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, Z) = right_coproj(Y, W) \<circ>\<^sub>c g"
        using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
      have s4: "(right_coproj(Y, W) \<circ>\<^sub>c g) \<circ>\<^sub>c z = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c z)"
        using comp_associative2[OF z_type g_type right_proj_type] by simp
      have eq2: "left_coproj(Y, W) \<circ>\<^sub>c y = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c z)" using s1 s2 s3 s4 by simp
      have gz_type: "g \<circ>\<^sub>c z \<in>\<^sub>c W" using z_type g_type comp_type by blast
      have "False" using coproducts_disjoint[OF y_type gz_type] eq2 by simp
      then show ?thesis by simp
    qed
  qed
  have surj_g: "surjective(g)"
    unfolding surjective_def2[OF g_type]
  proof (intro allI impI)
    fix y
    assume y_type: "y \<in>\<^sub>c W"
    have ry_type: "right_coproj(Y, W) \<circ>\<^sub>c y \<in>\<^sub>c Y \<Coprod> W" using y_type right_proj_type comp_type by blast
    obtain xz where xz_type: "xz \<in>\<^sub>c X \<Coprod> Z" and xz_eq: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c xz = right_coproj(Y, W) \<circ>\<^sub>c y"
      using surjective_def2[OF fg_type] surj_fg ry_type by auto
    have xz_disj: "(\<exists>x. x \<in>\<^sub>c X \<and> xz = left_coproj(X, Z) \<circ>\<^sub>c x) \<or> (\<exists>z. z \<in>\<^sub>c Z \<and> xz = right_coproj(X, Z) \<circ>\<^sub>c z)"
      using coprojs_jointly_surj[OF xz_type] by simp
    show "\<exists>x. x \<in>\<^sub>c Z \<and> g \<circ>\<^sub>c x = y"
    proof (cases "\<exists>x. x \<in>\<^sub>c X \<and> xz = left_coproj(X, Z) \<circ>\<^sub>c x")
      case True
      then obtain x where x_type: "x \<in>\<^sub>c X" and xz_eq2: "xz = left_coproj(X, Z) \<circ>\<^sub>c x" by auto
      have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c x) = right_coproj(Y, W) \<circ>\<^sub>c y" using xz_eq xz_eq2 by simp
      have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj(X, Z) \<circ>\<^sub>c x) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, Z)) \<circ>\<^sub>c x"
        using comp_associative2[OF x_type left_proj_type fg_type] by simp
      have s3: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj(X, Z) = left_coproj(Y, W) \<circ>\<^sub>c f"
        using left_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
      have s4: "(left_coproj(Y, W) \<circ>\<^sub>c f) \<circ>\<^sub>c x = left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x)"
        using comp_associative2[OF x_type f_type left_proj_type] by simp
      have eq2: "left_coproj(Y, W) \<circ>\<^sub>c (f \<circ>\<^sub>c x) = right_coproj(Y, W) \<circ>\<^sub>c y" using s1 s2 s3 s4 by simp
      have fx_type: "f \<circ>\<^sub>c x \<in>\<^sub>c Y" using x_type f_type comp_type by blast
      have "False" using coproducts_disjoint[OF fx_type y_type] eq2 by simp
      then show ?thesis by simp
    next
      case False
      then obtain z where z_type: "z \<in>\<^sub>c Z" and xz_eq2: "xz = right_coproj(X, Z) \<circ>\<^sub>c z" using xz_disj by auto
      have s1: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c z) = right_coproj(Y, W) \<circ>\<^sub>c y" using xz_eq xz_eq2 by simp
      have s2: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj(X, Z) \<circ>\<^sub>c z) = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, Z)) \<circ>\<^sub>c z"
        using comp_associative2[OF z_type right_proj_type fg_type] by simp
      have s3: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj(X, Z) = right_coproj(Y, W) \<circ>\<^sub>c g"
        using right_coproj_cfunc_bowtie_prod[OF f_type g_type] by simp
      have s4: "(right_coproj(Y, W) \<circ>\<^sub>c g) \<circ>\<^sub>c z = right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c z)"
        using comp_associative2[OF z_type g_type right_proj_type] by simp
      have eq2: "right_coproj(Y, W) \<circ>\<^sub>c (g \<circ>\<^sub>c z) = right_coproj(Y, W) \<circ>\<^sub>c y" using s1 s2 s3 s4 by simp
      have gz_type: "g \<circ>\<^sub>c z : \<one> \<rightarrow> W" using z_type g_type comp_type by blast
      have rp_type: "right_coproj(Y, W) : W \<rightarrow> Y \<Coprod> W" by (rule right_proj_type)
      have rp_mono: "monomorphism(right_coproj(Y, W))" by (rule right_coproj_are_monomorphisms)
      have gz_eq_y: "g \<circ>\<^sub>c z = y"
        using monomorphism_def3[OF rp_type, THEN iffD1, rule_format, where g="g \<circ>\<^sub>c z" and h=y and A="\<one>"]
          rp_mono gz_type y_type eq2 by auto
      show ?thesis using z_type gz_eq_y by auto
    qed
  qed
  show ?thesis using surj_f surj_g by simp
qed

subsection \<open>Boolean Cases\<close>

text \<open>HOL defines @{text case_bool} via @{text THE}, which has no FOL equivalent; but since @{text
  "\<t> \<amalg> \<f>"} is already known to be an isomorphism (@{thm truth_value_set_iso_1u1}), and @{text Cfunc.thy}
  already provides a generic two-sided inverse @{text inverse}/@{text "_\<^bold>\<inverse>"} for any isomorphism
  (Skolemized once, off the already-proven @{text "\<exists>!"} fact), @{text case_bool} is simply DEFINED
  as @{text "(\<t> \<amalg> \<f>)\<^bold>\<inverse>"} directly, with no fresh Skolemization needed here at all.\<close>
definition case_bool :: "cfunc" where
  "case_bool = (\<t> \<amalg> \<f>)\<^bold>\<inverse>"

lemma case_bool_def2:
  "case_bool : \<Omega> \<rightarrow> (\<one> \<Coprod> \<one>) \<and> (\<t> \<amalg> \<f>) \<circ>\<^sub>c case_bool = id(\<Omega>) \<and> case_bool \<circ>\<^sub>c (\<t> \<amalg> \<f>) = id(\<one> \<Coprod> \<one>)"
proof -
  have tf_type: "\<t> \<amalg> \<f> : \<one> \<Coprod> \<one> \<rightarrow> \<Omega>" using cfunc_coprod_type[OF true_func_type false_func_type] by simp
  have tf_iso: "isomorphism(\<t> \<amalg> \<f>)" by (rule truth_value_set_iso_1u1)
  have spec: "(\<t> \<amalg> \<f>)\<^bold>\<inverse> : codomain(\<t> \<amalg> \<f>) \<rightarrow> domain(\<t> \<amalg> \<f>) \<and> (\<t> \<amalg> \<f>)\<^bold>\<inverse> \<circ>\<^sub>c (\<t> \<amalg> \<f>) = id(domain(\<t> \<amalg> \<f>))
      \<and> (\<t> \<amalg> \<f>) \<circ>\<^sub>c (\<t> \<amalg> \<f>)\<^bold>\<inverse> = id(codomain(\<t> \<amalg> \<f>))"
    using inverse_def2[OF tf_iso] by simp
  have dom_tf: "domain(\<t> \<amalg> \<f>) = \<one> \<Coprod> \<one>" using tf_type unfolding cfunc_type_def by auto
  have cod_tf: "codomain(\<t> \<amalg> \<f>) = \<Omega>" using tf_type unfolding cfunc_type_def by auto
  show ?thesis unfolding case_bool_def using spec dom_tf cod_tf by simp
qed

lemma case_bool_type[type_rule]:
  "case_bool : \<Omega> \<rightarrow> \<one> \<Coprod> \<one>"
  using case_bool_def2 by auto

lemma case_bool_true_coprod_false:
  "case_bool \<circ>\<^sub>c (\<t> \<amalg> \<f>) = id(\<one> \<Coprod> \<one>)"
  using case_bool_def2 by auto

lemma true_coprod_false_case_bool:
  "(\<t> \<amalg> \<f>) \<circ>\<^sub>c case_bool = id(\<Omega>)"
  using case_bool_def2 by auto

lemma case_bool_iso:
  "isomorphism(case_bool)"
proof -
  have tf_type: "\<t> \<amalg> \<f> : \<one> \<Coprod> \<one> \<rightarrow> \<Omega>" using cfunc_coprod_type[OF true_func_type false_func_type] by simp
  show ?thesis unfolding isomorphism_def3[OF case_bool_type]
    using tf_type true_coprod_false_case_bool case_bool_true_coprod_false by auto
qed

lemma case_bool_true_and_false:
  "(case_bool \<circ>\<^sub>c \<t> = left_coproj(\<one>, \<one>)) \<and> (case_bool \<circ>\<^sub>c \<f> = right_coproj(\<one>, \<one>))"
proof -
  have ct_type: "case_bool \<circ>\<^sub>c \<t> : \<one> \<rightarrow> \<one> \<Coprod> \<one>" using true_func_type case_bool_type comp_type by blast
  have cf_type: "case_bool \<circ>\<^sub>c \<f> : \<one> \<rightarrow> \<one> \<Coprod> \<one>" using false_func_type case_bool_type comp_type by blast
  have s1: "left_coproj(\<one>, \<one>) \<amalg> right_coproj(\<one>, \<one>) = id(\<one> \<Coprod> \<one>)" using id_coprod by simp
  have s2: "id(\<one> \<Coprod> \<one>) = case_bool \<circ>\<^sub>c (\<t> \<amalg> \<f>)" using case_bool_true_coprod_false by simp
  have s3: "case_bool \<circ>\<^sub>c (\<t> \<amalg> \<f>) = (case_bool \<circ>\<^sub>c \<t>) \<amalg> (case_bool \<circ>\<^sub>c \<f>)"
    using cfunc_coprod_comp[OF case_bool_type true_func_type false_func_type] by simp
  have eq: "left_coproj(\<one>, \<one>) \<amalg> right_coproj(\<one>, \<one>) = (case_bool \<circ>\<^sub>c \<t>) \<amalg> (case_bool \<circ>\<^sub>c \<f>)"
    using s1 s2 s3 by simp
  show ?thesis using coprod_eq2[OF left_proj_type right_proj_type ct_type cf_type] eq by auto
qed

lemma case_bool_true:
  "case_bool \<circ>\<^sub>c \<t> = left_coproj(\<one>, \<one>)"
  using case_bool_true_and_false by simp

lemma case_bool_false:
  "case_bool \<circ>\<^sub>c \<f> = right_coproj(\<one>, \<one>)"
  using case_bool_true_and_false by simp

lemma coprod_case_bool_true:
  assumes x1_type: "x1 \<in>\<^sub>c X" and x2_type: "x2 \<in>\<^sub>c X"
  shows "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<t> = x1"
proof -
  have x1x2_type: "x1 \<amalg> x2 : \<one> \<Coprod> \<one> \<rightarrow> X" using cfunc_coprod_type[OF x1_type x2_type] by simp
  have s1: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<t> = (x1 \<amalg> x2) \<circ>\<^sub>c (case_bool \<circ>\<^sub>c \<t>)"
    using comp_associative2[OF true_func_type case_bool_type x1x2_type] by simp
  have s2: "(x1 \<amalg> x2) \<circ>\<^sub>c (case_bool \<circ>\<^sub>c \<t>) = (x1 \<amalg> x2) \<circ>\<^sub>c left_coproj(\<one>, \<one>)" using case_bool_true by simp
  have s3: "(x1 \<amalg> x2) \<circ>\<^sub>c left_coproj(\<one>, \<one>) = x1" using left_coproj_cfunc_coprod[OF x1_type x2_type] by simp
  show ?thesis using s1 s2 s3 by simp
qed

lemma coprod_case_bool_false:
  assumes x1_type: "x1 \<in>\<^sub>c X" and x2_type: "x2 \<in>\<^sub>c X"
  shows "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<f> = x2"
proof -
  have x1x2_type: "x1 \<amalg> x2 : \<one> \<Coprod> \<one> \<rightarrow> X" using cfunc_coprod_type[OF x1_type x2_type] by simp
  have s1: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<f> = (x1 \<amalg> x2) \<circ>\<^sub>c (case_bool \<circ>\<^sub>c \<f>)"
    using comp_associative2[OF false_func_type case_bool_type x1x2_type] by simp
  have s2: "(x1 \<amalg> x2) \<circ>\<^sub>c (case_bool \<circ>\<^sub>c \<f>) = (x1 \<amalg> x2) \<circ>\<^sub>c right_coproj(\<one>, \<one>)" using case_bool_false by simp
  have s3: "(x1 \<amalg> x2) \<circ>\<^sub>c right_coproj(\<one>, \<one>) = x2" using right_coproj_cfunc_coprod[OF x1_type x2_type] by simp
  show ?thesis using s1 s2 s3 by simp
qed

subsection \<open>Distribution of Products over Coproducts\<close>

subsubsection \<open>Factor Product over Coproduct on Left\<close>

definition factor_prod_coprod_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "factor_prod_coprod_left(A, B, C) = (id(A) \<times>\<^sub>f left_coproj(B, C)) \<amalg> (id(A) \<times>\<^sub>f right_coproj(B, C))"

lemma factor_prod_coprod_left_type[type_rule]:
  "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
proof -
  have idA_type: "id(A) : A \<rightarrow> A" by (rule id_type)
  have l1_type: "id(A) \<times>\<^sub>f left_coproj(B, C) : A \<times>\<^sub>c B \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    using cfunc_cross_prod_type[OF idA_type left_proj_type] by simp
  have l2_type: "id(A) \<times>\<^sub>f right_coproj(B, C) : A \<times>\<^sub>c C \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    using cfunc_cross_prod_type[OF idA_type right_proj_type] by simp
  show ?thesis unfolding factor_prod_coprod_left_def using cfunc_coprod_type[OF l1_type l2_type] by simp
qed

lemma factor_prod_coprod_left_ap_left:
  assumes a_type: "a \<in>\<^sub>c A" and b_type: "b \<in>\<^sub>c B"
  shows "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>) = \<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle>"
proof -
  have idA_type: "id(A) : A \<rightarrow> A" by (rule id_type)
  have l1_type: "id(A) \<times>\<^sub>f left_coproj(B, C) : A \<times>\<^sub>c B \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    using cfunc_cross_prod_type[OF idA_type left_proj_type] by simp
  have l2_type: "id(A) \<times>\<^sub>f right_coproj(B, C) : A \<times>\<^sub>c C \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    using cfunc_cross_prod_type[OF idA_type right_proj_type] by simp
  have ab_type: "\<langle>a, b\<rangle> \<in>\<^sub>c A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
  have s1: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>)
      = (factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>a, b\<rangle>"
    using comp_associative2[OF ab_type left_proj_type factor_prod_coprod_left_type] by simp
  have s2: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) = id(A) \<times>\<^sub>f left_coproj(B, C)"
    unfolding factor_prod_coprod_left_def using left_coproj_cfunc_coprod[OF l1_type l2_type] by simp
  have s3: "(id(A) \<times>\<^sub>f left_coproj(B, C)) \<circ>\<^sub>c \<langle>a, b\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF a_type b_type idA_type left_proj_type] by simp
  have s4: "id(A) \<circ>\<^sub>c a = a" using id_left_unit2[OF a_type] by simp
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma factor_prod_coprod_left_ap_right:
  assumes a_type: "a \<in>\<^sub>c A" and c_type: "c \<in>\<^sub>c C"
  shows "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>) = \<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle>"
proof -
  have idA_type: "id(A) : A \<rightarrow> A" by (rule id_type)
  have l1_type: "id(A) \<times>\<^sub>f left_coproj(B, C) : A \<times>\<^sub>c B \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    using cfunc_cross_prod_type[OF idA_type left_proj_type] by simp
  have l2_type: "id(A) \<times>\<^sub>f right_coproj(B, C) : A \<times>\<^sub>c C \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    using cfunc_cross_prod_type[OF idA_type right_proj_type] by simp
  have ac_type: "\<langle>a, c\<rangle> \<in>\<^sub>c A \<times>\<^sub>c C" using a_type c_type cfunc_prod_type by auto
  have s1: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)
      = (factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>a, c\<rangle>"
    using comp_associative2[OF ac_type right_proj_type factor_prod_coprod_left_type] by simp
  have s2: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) = id(A) \<times>\<^sub>f right_coproj(B, C)"
    unfolding factor_prod_coprod_left_def using right_coproj_cfunc_coprod[OF l1_type l2_type] by simp
  have s3: "(id(A) \<times>\<^sub>f right_coproj(B, C)) \<circ>\<^sub>c \<langle>a, c\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF a_type c_type idA_type right_proj_type] by simp
  have s4: "id(A) \<circ>\<^sub>c a = a" using id_left_unit2[OF a_type] by simp
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma factor_prod_coprod_left_mono:
  "monomorphism(factor_prod_coprod_left(A, B, C))"
proof -
  have fpcl_type: "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by (rule factor_prod_coprod_left_type)
  have inj: "injective(factor_prod_coprod_left(A, B, C))"
    unfolding injective_def2[OF fpcl_type]
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<and> y \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<and>
        factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c x = factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)" and y_type: "y \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
      and eqs: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c x = factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c y" by auto
    have x_disj: "(\<exists>x'. x' \<in>\<^sub>c A \<times>\<^sub>c B \<and> x = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c x')
        \<or> (\<exists>x'. x' \<in>\<^sub>c A \<times>\<^sub>c C \<and> x = right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c x')"
      using coprojs_jointly_surj[OF x_type] by simp
    have y_disj: "(\<exists>y'. y' \<in>\<^sub>c A \<times>\<^sub>c B \<and> y = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y')
        \<or> (\<exists>y'. y' \<in>\<^sub>c A \<times>\<^sub>c C \<and> y = right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y')"
      using coprojs_jointly_surj[OF y_type] by simp
    show "x = y"
    proof (cases "\<exists>x'. x' \<in>\<^sub>c A \<times>\<^sub>c B \<and> x = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c x'")
      case True
      then obtain x' where x'_type: "x' \<in>\<^sub>c A \<times>\<^sub>c B" and x_eq: "x = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c x'" by auto
      obtain a b where a_type: "a \<in>\<^sub>c A" and b_type: "b \<in>\<^sub>c B" and x'_eq: "x' = \<langle>a, b\<rangle>"
        using cart_prod_decomp[OF x'_type] by blast
      show "x = y"
      proof (cases "\<exists>y'. y' \<in>\<^sub>c A \<times>\<^sub>c B \<and> y = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y'")
        case True
        then obtain y' where y'_type: "y' \<in>\<^sub>c A \<times>\<^sub>c B" and y_eq: "y = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y'" by auto
        obtain a' b' where a'_type: "a' \<in>\<^sub>c A" and b'_type: "b' \<in>\<^sub>c B" and y'_eq: "y' = \<langle>a', b'\<rangle>"
          using cart_prod_decomp[OF y'_type] by blast
        have lx_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c x = \<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle>"
          using x_eq x'_eq factor_prod_coprod_left_ap_left[OF a_type b_type] by simp
        have ly_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c y = \<langle>a', left_coproj(B, C) \<circ>\<^sub>c b'\<rangle>"
          using y_eq y'_eq factor_prod_coprod_left_ap_left[OF a'_type b'_type] by simp
        have eq_pair: "\<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle> = \<langle>a', left_coproj(B, C) \<circ>\<^sub>c b'\<rangle>" using eqs lx_eq ly_eq by simp
        have lb_type: "left_coproj(B, C) \<circ>\<^sub>c b : \<one> \<rightarrow> B \<Coprod> C" using b_type left_proj_type comp_type by blast
        have lb'_type: "left_coproj(B, C) \<circ>\<^sub>c b' : \<one> \<rightarrow> B \<Coprod> C" using b'_type left_proj_type comp_type by blast
        have split_eq: "a = a' \<and> left_coproj(B, C) \<circ>\<^sub>c b = left_coproj(B, C) \<circ>\<^sub>c b'"
          using eq_pair cart_prod_eq2[OF a_type lb_type a'_type lb'_type] by auto
        have a_eq: "a = a'" using split_eq by simp
        have lb_eq: "left_coproj(B, C) \<circ>\<^sub>c b = left_coproj(B, C) \<circ>\<^sub>c b'" using split_eq by simp
        have lp_type: "left_coproj(B, C) : B \<rightarrow> B \<Coprod> C" by (rule left_proj_type)
        have lp_mono: "monomorphism(left_coproj(B, C))" by (rule left_coproj_are_monomorphisms)
        have b_eq: "b = b'"
          using monomorphism_def3[OF lp_type, THEN iffD1, rule_format, where g=b and h=b' and A="\<one>"]
            lp_mono b_type b'_type lb_eq by auto
        show "x = y" using x_eq y_eq x'_eq y'_eq a_eq b_eq by simp
      next
        case False
        then obtain y' where y'_type: "y' \<in>\<^sub>c A \<times>\<^sub>c C" and y_eq: "y = right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
          using y_disj by auto
        obtain a' c' where a'_type: "a' \<in>\<^sub>c A" and c'_type: "c' \<in>\<^sub>c C" and y'_eq: "y' = \<langle>a', c'\<rangle>"
          using cart_prod_decomp[OF y'_type] by blast
        have lx_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c x = \<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle>"
          using x_eq x'_eq factor_prod_coprod_left_ap_left[OF a_type b_type] by simp
        have ly_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c y = \<langle>a', right_coproj(B, C) \<circ>\<^sub>c c'\<rangle>"
          using y_eq y'_eq factor_prod_coprod_left_ap_right[OF a'_type c'_type] by simp
        have eq_pair: "\<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle> = \<langle>a', right_coproj(B, C) \<circ>\<^sub>c c'\<rangle>" using eqs lx_eq ly_eq by simp
        have lb_type: "left_coproj(B, C) \<circ>\<^sub>c b \<in>\<^sub>c B \<Coprod> C" using b_type left_proj_type comp_type by blast
        have rc'_type: "right_coproj(B, C) \<circ>\<^sub>c c' \<in>\<^sub>c B \<Coprod> C" using c'_type right_proj_type comp_type by blast
        have "left_coproj(B, C) \<circ>\<^sub>c b = right_coproj(B, C) \<circ>\<^sub>c c'"
          using eq_pair cart_prod_eq2[OF a_type lb_type a'_type rc'_type] by auto
        then have "False" using coproducts_disjoint[OF b_type c'_type] by simp
        then show "x = y" by simp
      qed
    next
      case False
      then obtain x' where x'_type: "x' \<in>\<^sub>c A \<times>\<^sub>c C" and x_eq: "x = right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c x'" using x_disj by auto
      obtain a c where a_type: "a \<in>\<^sub>c A" and c_type: "c \<in>\<^sub>c C" and x'_eq: "x' = \<langle>a, c\<rangle>"
        using cart_prod_decomp[OF x'_type] by blast
      show "x = y"
      proof (cases "\<exists>y'. y' \<in>\<^sub>c A \<times>\<^sub>c B \<and> y = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y'")
        case True
        then obtain y' where y'_type: "y' \<in>\<^sub>c A \<times>\<^sub>c B" and y_eq: "y = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y'" by auto
        obtain a' b' where a'_type: "a' \<in>\<^sub>c A" and b'_type: "b' \<in>\<^sub>c B" and y'_eq: "y' = \<langle>a', b'\<rangle>"
          using cart_prod_decomp[OF y'_type] by blast
        have lx_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c x = \<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle>"
          using x_eq x'_eq factor_prod_coprod_left_ap_right[OF a_type c_type] by simp
        have ly_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c y = \<langle>a', left_coproj(B, C) \<circ>\<^sub>c b'\<rangle>"
          using y_eq y'_eq factor_prod_coprod_left_ap_left[OF a'_type b'_type] by simp
        have eq_pair: "\<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle> = \<langle>a', left_coproj(B, C) \<circ>\<^sub>c b'\<rangle>" using eqs lx_eq ly_eq by simp
        have rc_type: "right_coproj(B, C) \<circ>\<^sub>c c \<in>\<^sub>c B \<Coprod> C" using c_type right_proj_type comp_type by blast
        have lb'_type: "left_coproj(B, C) \<circ>\<^sub>c b' \<in>\<^sub>c B \<Coprod> C" using b'_type left_proj_type comp_type by blast
        have "right_coproj(B, C) \<circ>\<^sub>c c = left_coproj(B, C) \<circ>\<^sub>c b'"
          using eq_pair cart_prod_eq2[OF a_type rc_type a'_type lb'_type] by auto
        then have "False" using coproducts_disjoint[OF b'_type c_type] by simp
        then show "x = y" by simp
      next
        case False
        then obtain y' where y'_type: "y' \<in>\<^sub>c A \<times>\<^sub>c C" and y_eq: "y = right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
          using y_disj by auto
        obtain a' c' where a'_type: "a' \<in>\<^sub>c A" and c'_type: "c' \<in>\<^sub>c C" and y'_eq: "y' = \<langle>a', c'\<rangle>"
          using cart_prod_decomp[OF y'_type] by blast
        have lx_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c x = \<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle>"
          using x_eq x'_eq factor_prod_coprod_left_ap_right[OF a_type c_type] by simp
        have ly_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c y = \<langle>a', right_coproj(B, C) \<circ>\<^sub>c c'\<rangle>"
          using y_eq y'_eq factor_prod_coprod_left_ap_right[OF a'_type c'_type] by simp
        have eq_pair: "\<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle> = \<langle>a', right_coproj(B, C) \<circ>\<^sub>c c'\<rangle>" using eqs lx_eq ly_eq by simp
        have rc_type: "right_coproj(B, C) \<circ>\<^sub>c c : \<one> \<rightarrow> B \<Coprod> C" using c_type right_proj_type comp_type by blast
        have rc'_type: "right_coproj(B, C) \<circ>\<^sub>c c' : \<one> \<rightarrow> B \<Coprod> C" using c'_type right_proj_type comp_type by blast
        have split_eq: "a = a' \<and> right_coproj(B, C) \<circ>\<^sub>c c = right_coproj(B, C) \<circ>\<^sub>c c'"
          using eq_pair cart_prod_eq2[OF a_type rc_type a'_type rc'_type] by auto
        have a_eq: "a = a'" using split_eq by simp
        have rc_eq: "right_coproj(B, C) \<circ>\<^sub>c c = right_coproj(B, C) \<circ>\<^sub>c c'" using split_eq by simp
        have rp_type: "right_coproj(B, C) : C \<rightarrow> B \<Coprod> C" by (rule right_proj_type)
        have rp_mono: "monomorphism(right_coproj(B, C))" by (rule right_coproj_are_monomorphisms)
        have c_eq: "c = c'"
          using monomorphism_def3[OF rp_type, THEN iffD1, rule_format, where g=c and h=c' and A="\<one>"]
            rp_mono c_type c'_type rc_eq by auto
        show "x = y" using x_eq y_eq x'_eq y'_eq a_eq c_eq by simp
      qed
    qed
  qed
  show ?thesis using injective_imp_monomorphism[OF inj] by simp
qed

lemma factor_prod_coprod_left_epi:
  "epimorphism(factor_prod_coprod_left(A, B, C))"
proof -
  have fpcl_type: "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by (rule factor_prod_coprod_left_type)
  have surj: "surjective(factor_prod_coprod_left(A, B, C))"
    unfolding surjective_def2[OF fpcl_type]
  proof (intro allI impI)
    fix y
    assume y_type: "y \<in>\<^sub>c A \<times>\<^sub>c (B \<Coprod> C)"
    obtain a bc where a_type: "a \<in>\<^sub>c A" and bc_type: "bc \<in>\<^sub>c B \<Coprod> C" and y_eq: "y = \<langle>a, bc\<rangle>"
      using cart_prod_decomp[OF y_type] by blast
    have bc_disj: "(\<exists>b. b \<in>\<^sub>c B \<and> bc = left_coproj(B, C) \<circ>\<^sub>c b) \<or> (\<exists>c. c \<in>\<^sub>c C \<and> bc = right_coproj(B, C) \<circ>\<^sub>c c)"
      using coprojs_jointly_surj[OF bc_type] by simp
    show "\<exists>x. x \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<and> factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c x = y"
    proof (cases "\<exists>b. b \<in>\<^sub>c B \<and> bc = left_coproj(B, C) \<circ>\<^sub>c b")
      case True
      then obtain b where b_type: "b \<in>\<^sub>c B" and bc_eq: "bc = left_coproj(B, C) \<circ>\<^sub>c b" by auto
      have ab_type: "\<langle>a, b\<rangle> \<in>\<^sub>c A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
      have lx_type: "left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
        using ab_type left_proj_type comp_type by blast
      have h_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>) = \<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle>"
        using factor_prod_coprod_left_ap_left[OF a_type b_type] by simp
      have y_eq2: "y = \<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle>" using y_eq bc_eq by simp
      show ?thesis using lx_type h_eq y_eq2 by auto
    next
      case False
      then obtain c where c_type: "c \<in>\<^sub>c C" and bc_eq: "bc = right_coproj(B, C) \<circ>\<^sub>c c" using bc_disj by auto
      have ac_type: "\<langle>a, c\<rangle> \<in>\<^sub>c A \<times>\<^sub>c C" using a_type c_type cfunc_prod_type by auto
      have rx_type: "right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
        using ac_type right_proj_type comp_type by blast
      have h_eq: "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>) = \<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle>"
        using factor_prod_coprod_left_ap_right[OF a_type c_type] by simp
      have y_eq2: "y = \<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle>" using y_eq bc_eq by simp
      show ?thesis using rx_type h_eq y_eq2 by auto
    qed
  qed
  show ?thesis using surjective_is_epimorphism[OF surj] by simp
qed

lemma dist_prod_coprod_iso:
  "isomorphism(factor_prod_coprod_left(A, B, C))"
  using epi_mon_is_iso[OF factor_prod_coprod_left_epi factor_prod_coprod_left_mono] by simp

text \<open>The lemma below corresponds to Proposition 2.5.10 in Halvorson.\<close>
lemma prod_distribute_coprod:
  "A \<times>\<^sub>c (X \<Coprod> Y) \<cong> (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y)"
proof -
  have iso: "isomorphism(factor_prod_coprod_left(A, X, Y))" by (rule dist_prod_coprod_iso)
  have ty: "factor_prod_coprod_left(A, X, Y) : (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y) \<rightarrow> A \<times>\<^sub>c (X \<Coprod> Y)"
    by (rule factor_prod_coprod_left_type)
  have "(A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y) \<cong> A \<times>\<^sub>c (X \<Coprod> Y)" unfolding is_isomorphic_def using ty iso by auto
  then show ?thesis using isomorphic_is_symmetric by auto
qed

subsubsection \<open>Distribute Product over Coproduct on Left\<close>

text \<open>As with @{text case_bool}, HOL's @{text THE} is avoided entirely by defining @{text
  dist_prod_coprod_left} directly as the generic two-sided inverse of the already-established
  isomorphism @{text factor_prod_coprod_left}.\<close>
definition dist_prod_coprod_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "dist_prod_coprod_left(A, B, C) = (factor_prod_coprod_left(A, B, C))\<^bold>\<inverse>"

lemma dist_prod_coprod_left_def2:
  "dist_prod_coprod_left(A, B, C) : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)
    \<and> dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C) = id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))
    \<and> factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c dist_prod_coprod_left(A, B, C) = id(A \<times>\<^sub>c (B \<Coprod> C))"
proof -
  have fpcl_type: "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by (rule factor_prod_coprod_left_type)
  have fpcl_iso: "isomorphism(factor_prod_coprod_left(A, B, C))" by (rule dist_prod_coprod_iso)
  have spec: "(factor_prod_coprod_left(A, B, C))\<^bold>\<inverse> :
        codomain(factor_prod_coprod_left(A, B, C)) \<rightarrow> domain(factor_prod_coprod_left(A, B, C))
      \<and> (factor_prod_coprod_left(A, B, C))\<^bold>\<inverse> \<circ>\<^sub>c factor_prod_coprod_left(A, B, C)
          = id(domain(factor_prod_coprod_left(A, B, C)))
      \<and> factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (factor_prod_coprod_left(A, B, C))\<^bold>\<inverse>
          = id(codomain(factor_prod_coprod_left(A, B, C)))"
    using inverse_def2[OF fpcl_iso] by simp
  have dom_fpcl: "domain(factor_prod_coprod_left(A, B, C)) = (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
    using fpcl_type unfolding cfunc_type_def by auto
  have cod_fpcl: "codomain(factor_prod_coprod_left(A, B, C)) = A \<times>\<^sub>c (B \<Coprod> C)"
    using fpcl_type unfolding cfunc_type_def by auto
  show ?thesis unfolding dist_prod_coprod_left_def using spec dom_fpcl cod_fpcl by simp
qed

lemma dist_prod_coprod_left_type[type_rule]:
  "dist_prod_coprod_left(A, B, C) : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
  using dist_prod_coprod_left_def2 by auto

lemma dist_factor_prod_coprod_left:
  "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C) = id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))"
  using dist_prod_coprod_left_def2 by auto

lemma factor_dist_prod_coprod_left:
  "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c dist_prod_coprod_left(A, B, C) = id(A \<times>\<^sub>c (B \<Coprod> C))"
  using dist_prod_coprod_left_def2 by auto

lemma dist_prod_coprod_left_iso:
  "isomorphism(dist_prod_coprod_left(A, B, C))"
proof -
  have t: "dist_prod_coprod_left(A, B, C) : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
    by (rule dist_prod_coprod_left_type)
  have witness: "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)
      \<and> factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c dist_prod_coprod_left(A, B, C) = id(A \<times>\<^sub>c (B \<Coprod> C))
      \<and> dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C) = id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))"
  proof (intro conjI)
    show "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
      by (rule factor_prod_coprod_left_type)
  next
    show "factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c dist_prod_coprod_left(A, B, C) = id(A \<times>\<^sub>c (B \<Coprod> C))"
      by (rule factor_dist_prod_coprod_left)
  next
    show "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C) = id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))"
      by (rule dist_factor_prod_coprod_left)
  qed
  show ?thesis unfolding isomorphism_def3[OF t] using witness by blast
qed

lemma dist_prod_coprod_left_ap_left:
  assumes a_type: "a \<in>\<^sub>c A" and b_type: "b \<in>\<^sub>c B"
  shows "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c \<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle> = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>"
proof -
  have ab_type: "\<langle>a, b\<rangle> \<in>\<^sub>c A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
  have lab_type: "left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
    using ab_type left_proj_type comp_type by blast
  have dpcl_type: "dist_prod_coprod_left(A, B, C) : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
    by (rule dist_prod_coprod_left_type)
  have fpcl_type: "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by (rule factor_prod_coprod_left_type)
  have s1: "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c \<langle>a, left_coproj(B, C) \<circ>\<^sub>c b\<rangle>
      = dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c (factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>))"
    using factor_prod_coprod_left_ap_left[OF a_type b_type] by simp
  have s2: "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c (factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>))
      = (dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C)) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>)"
    using comp_associative2[OF lab_type fpcl_type dpcl_type] by simp
  have s3: "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C) = id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))"
    by (rule dist_factor_prod_coprod_left)
  have s4: "id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>) = left_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>"
    using id_left_unit2[OF lab_type] by simp
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma dist_prod_coprod_left_ap_right:
  assumes a_type: "a \<in>\<^sub>c A" and c_type: "c \<in>\<^sub>c C"
  shows "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c \<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle> = right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>"
proof -
  have ac_type: "\<langle>a, c\<rangle> \<in>\<^sub>c A \<times>\<^sub>c C" using a_type c_type cfunc_prod_type by auto
  have rac_type: "right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
    using ac_type right_proj_type comp_type by blast
  have dpcl_type: "dist_prod_coprod_left(A, B, C) : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
    by (rule dist_prod_coprod_left_type)
  have fpcl_type: "factor_prod_coprod_left(A, B, C) : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by (rule factor_prod_coprod_left_type)
  have s1: "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c \<langle>a, right_coproj(B, C) \<circ>\<^sub>c c\<rangle>
      = dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c (factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>))"
    using factor_prod_coprod_left_ap_right[OF a_type c_type] by simp
  have s2: "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c (factor_prod_coprod_left(A, B, C) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>))
      = (dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C)) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)"
    using comp_associative2[OF rac_type fpcl_type dpcl_type] by simp
  have s3: "dist_prod_coprod_left(A, B, C) \<circ>\<^sub>c factor_prod_coprod_left(A, B, C) = id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))"
    by (rule dist_factor_prod_coprod_left)
  have s4: "id((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>) = right_coproj(A \<times>\<^sub>c B, A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>"
    using id_left_unit2[OF rac_type] by simp
  show ?thesis using s1 s2 s3 s4 by simp
qed

subsubsection \<open>Factor Product over Coproduct on Right\<close>

text \<open>Derived algebraically from the left-distribution family via @{text swap}, reusing all of the
  already-proven left-hand lemmas rather than re-deriving injectivity/surjectivity from scratch.\<close>
definition factor_prod_coprod_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "factor_prod_coprod_right(A, B, C) =
    swap(C, A \<Coprod> B) \<circ>\<^sub>c factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))"

lemma factor_prod_coprod_right_type[type_rule]:
  "factor_prod_coprod_right(A, B, C) : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C"
proof -
  have bw_type: "swap(A, C) \<bowtie>\<^sub>f swap(B, C) : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have fpcl_type: "factor_prod_coprod_left(C, A, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    by (rule factor_prod_coprod_left_type)
  have inner_type: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))
      : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    using comp_type[OF bw_type fpcl_type] by simp
  have sw_type: "swap(C, A \<Coprod> B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C" by (rule swap_type)
  show ?thesis unfolding factor_prod_coprod_right_def using comp_type[OF inner_type sw_type] by simp
qed

lemma factor_prod_coprod_right_ap_left:
  assumes a_type: "a \<in>\<^sub>c A" and c_type: "c \<in>\<^sub>c C"
  shows "factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>) = \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>"
proof -
  have bw_type: "swap(A, C) \<bowtie>\<^sub>f swap(B, C) : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have fpcl_type: "factor_prod_coprod_left(C, A, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    by (rule factor_prod_coprod_left_type)
  have sw_type: "swap(C, A \<Coprod> B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C" by (rule swap_type)
  have fpcl_bw_type: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))
      : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    using comp_type[OF bw_type fpcl_type] by simp
  have ac_type: "\<langle>a, c\<rangle> \<in>\<^sub>c A \<times>\<^sub>c C" using a_type c_type cfunc_prod_type by auto
  have lac_type: "left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    using ac_type left_proj_type comp_type by blast

  have s1: "factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)
      = (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))))
          \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)"
    unfolding factor_prod_coprod_right_def by simp
  have s2: "(swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))))
        \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)
      = swap(C, A \<Coprod> B) \<circ>\<^sub>c ((factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C)))
          \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>))"
    using comp_associative2[OF lac_type fpcl_bw_type sw_type] by simp
  have s3: "(factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C)))
        \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)
      = factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c ((swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>))"
    using comp_associative2[OF lac_type bw_type fpcl_type] by simp
  have s4: "(swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c (left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)
      = ((swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>a, c\<rangle>"
    using comp_associative2[OF ac_type left_proj_type bw_type] by simp
  have s5: "(swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) = left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c swap(A, C)"
    using left_coproj_cfunc_bowtie_prod[OF swap_type swap_type] by simp
  have s6: "(left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c swap(A, C)) \<circ>\<^sub>c \<langle>a, c\<rangle> = left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c (swap(A, C) \<circ>\<^sub>c \<langle>a, c\<rangle>)"
    using comp_associative2[OF ac_type swap_type left_proj_type] by simp
  have s7: "swap(A, C) \<circ>\<^sub>c \<langle>a, c\<rangle> = \<langle>c, a\<rangle>" using swap_ap[OF a_type c_type] by simp
  have s8: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, a\<rangle>) = \<langle>c, left_coproj(A, B) \<circ>\<^sub>c a\<rangle>"
    using factor_prod_coprod_left_ap_left[OF c_type a_type] by simp
  have la_type: "left_coproj(A, B) \<circ>\<^sub>c a \<in>\<^sub>c A \<Coprod> B" using a_type left_proj_type comp_type by blast
  have s9: "swap(C, A \<Coprod> B) \<circ>\<^sub>c \<langle>c, left_coproj(A, B) \<circ>\<^sub>c a\<rangle> = \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>"
    using swap_ap[OF c_type la_type] by simp
  show ?thesis using s1 s2 s3 s4 s5 s6 s7 s8 s9 by simp
qed

lemma factor_prod_coprod_right_ap_right:
  assumes b_type: "b \<in>\<^sub>c B" and c_type: "c \<in>\<^sub>c C"
  shows "factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>) = \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>"
proof -
  have bw_type: "swap(A, C) \<bowtie>\<^sub>f swap(B, C) : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have fpcl_type: "factor_prod_coprod_left(C, A, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    by (rule factor_prod_coprod_left_type)
  have sw_type: "swap(C, A \<Coprod> B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C" by (rule swap_type)
  have fpcl_bw_type: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))
      : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    using comp_type[OF bw_type fpcl_type] by simp
  have bc_type: "\<langle>b, c\<rangle> \<in>\<^sub>c B \<times>\<^sub>c C" using b_type c_type cfunc_prod_type by auto
  have rbc_type: "right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    using bc_type right_proj_type comp_type by blast

  have s1: "factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>)
      = (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))))
          \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>)"
    unfolding factor_prod_coprod_right_def by simp
  have s2: "(swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))))
        \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>)
      = swap(C, A \<Coprod> B) \<circ>\<^sub>c ((factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C)))
          \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>))"
    using comp_associative2[OF rbc_type fpcl_bw_type sw_type] by simp
  have s3: "(factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C)))
        \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>)
      = factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c ((swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>))"
    using comp_associative2[OF rbc_type bw_type fpcl_type] by simp
  have s4: "(swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c (right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>)
      = ((swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>b, c\<rangle>"
    using comp_associative2[OF bc_type right_proj_type bw_type] by simp
  have s5: "(swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) = right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c swap(B, C)"
    using right_coproj_cfunc_bowtie_prod[OF swap_type swap_type] by simp
  have s6: "(right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c swap(B, C)) \<circ>\<^sub>c \<langle>b, c\<rangle> = right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c (swap(B, C) \<circ>\<^sub>c \<langle>b, c\<rangle>)"
    using comp_associative2[OF bc_type swap_type right_proj_type] by simp
  have s7: "swap(B, C) \<circ>\<^sub>c \<langle>b, c\<rangle> = \<langle>c, b\<rangle>" using swap_ap[OF b_type c_type] by simp
  have s8: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, b\<rangle>) = \<langle>c, right_coproj(A, B) \<circ>\<^sub>c b\<rangle>"
    using factor_prod_coprod_left_ap_right[OF c_type b_type] by simp
  have rb_type: "right_coproj(A, B) \<circ>\<^sub>c b \<in>\<^sub>c A \<Coprod> B" using b_type right_proj_type comp_type by blast
  have s9: "swap(C, A \<Coprod> B) \<circ>\<^sub>c \<langle>c, right_coproj(A, B) \<circ>\<^sub>c b\<rangle> = \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>"
    using swap_ap[OF c_type rb_type] by simp
  show ?thesis using s1 s2 s3 s4 s5 s6 s7 s8 s9 by simp
qed

subsubsection \<open>Distribute Product over Coproduct on Right\<close>

definition dist_prod_coprod_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "dist_prod_coprod_right(A, B, C) =
    (swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)"

lemma dist_prod_coprod_right_type[type_rule]:
  "dist_prod_coprod_right(A, B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
proof -
  have sw_type: "swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)" by (rule swap_type)
  have dpcl_type: "dist_prod_coprod_left(C, A, B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    by (rule dist_prod_coprod_left_type)
  have inner_type: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using comp_type[OF sw_type dpcl_type] by simp
  have bw_type: "swap(C, A) \<bowtie>\<^sub>f swap(C, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  show ?thesis unfolding dist_prod_coprod_right_def using comp_type[OF inner_type bw_type] by simp
qed

lemma dist_prod_coprod_right_ap_left:
  assumes a_type: "a \<in>\<^sub>c A" and c_type: "c \<in>\<^sub>c C"
  shows "dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle> = left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>"
proof -
  have sw_type: "swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)" by (rule swap_type)
  have dpcl_type: "dist_prod_coprod_left(C, A, B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    by (rule dist_prod_coprod_left_type)
  have dpcl_sw_type: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using comp_type[OF sw_type dpcl_type] by simp
  have bw_type: "swap(C, A) \<bowtie>\<^sub>f swap(C, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have la_type: "left_coproj(A, B) \<circ>\<^sub>c a \<in>\<^sub>c A \<Coprod> B" using a_type left_proj_type comp_type by blast
  have lac_type: "\<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle> \<in>\<^sub>c (A \<Coprod> B) \<times>\<^sub>c C" using la_type c_type cfunc_prod_type by auto
  have ca_type: "\<langle>c, a\<rangle> \<in>\<^sub>c C \<times>\<^sub>c A" using c_type a_type cfunc_prod_type by auto

  have s1: "dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>
      = ((swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>"
    unfolding dist_prod_coprod_right_def by simp
  have s2: "((swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>
      = (swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c ((dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>)"
    using comp_associative2[OF lac_type dpcl_sw_type bw_type] by simp
  have s3: "(dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>
      = dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A \<Coprod> B, C) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle>)"
    using comp_associative2[OF lac_type sw_type dpcl_type] by simp
  have s4: "swap(A \<Coprod> B, C) \<circ>\<^sub>c \<langle>left_coproj(A, B) \<circ>\<^sub>c a, c\<rangle> = \<langle>c, left_coproj(A, B) \<circ>\<^sub>c a\<rangle>"
    using swap_ap[OF la_type c_type] by simp
  have s5: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c \<langle>c, left_coproj(A, B) \<circ>\<^sub>c a\<rangle> = left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, a\<rangle>"
    using dist_prod_coprod_left_ap_left[OF c_type a_type] by simp
  have s6: "(swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, a\<rangle>)
      = ((swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B)) \<circ>\<^sub>c \<langle>c, a\<rangle>"
    using comp_associative2[OF ca_type left_proj_type bw_type] by simp
  have s7: "(swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c left_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) = left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c swap(C, A)"
    using left_coproj_cfunc_bowtie_prod[OF swap_type swap_type] by simp
  have s8: "(left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c swap(C, A)) \<circ>\<^sub>c \<langle>c, a\<rangle> = left_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c (swap(C, A) \<circ>\<^sub>c \<langle>c, a\<rangle>)"
    using comp_associative2[OF ca_type swap_type left_proj_type] by simp
  have s9: "swap(C, A) \<circ>\<^sub>c \<langle>c, a\<rangle> = \<langle>a, c\<rangle>" using swap_ap[OF c_type a_type] by simp
  show ?thesis using s1 s2 s3 s4 s5 s6 s7 s8 s9 by simp
qed

lemma dist_prod_coprod_right_ap_right:
  assumes b_type: "b \<in>\<^sub>c B" and c_type: "c \<in>\<^sub>c C"
  shows "dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle> = right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>"
proof -
  have sw_type: "swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)" by (rule swap_type)
  have dpcl_type: "dist_prod_coprod_left(C, A, B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    by (rule dist_prod_coprod_left_type)
  have dpcl_sw_type: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using comp_type[OF sw_type dpcl_type] by simp
  have bw_type: "swap(C, A) \<bowtie>\<^sub>f swap(C, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have rb_type: "right_coproj(A, B) \<circ>\<^sub>c b \<in>\<^sub>c A \<Coprod> B" using b_type right_proj_type comp_type by blast
  have rbc_type: "\<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle> \<in>\<^sub>c (A \<Coprod> B) \<times>\<^sub>c C" using rb_type c_type cfunc_prod_type by auto
  have cb_type: "\<langle>c, b\<rangle> \<in>\<^sub>c C \<times>\<^sub>c B" using c_type b_type cfunc_prod_type by auto

  have s1: "dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>
      = ((swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>"
    unfolding dist_prod_coprod_right_def by simp
  have s2: "((swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>
      = (swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c ((dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>)"
    using comp_associative2[OF rbc_type dpcl_sw_type bw_type] by simp
  have s3: "(dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>
      = dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A \<Coprod> B, C) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle>)"
    using comp_associative2[OF rbc_type sw_type dpcl_type] by simp
  have s4: "swap(A \<Coprod> B, C) \<circ>\<^sub>c \<langle>right_coproj(A, B) \<circ>\<^sub>c b, c\<rangle> = \<langle>c, right_coproj(A, B) \<circ>\<^sub>c b\<rangle>"
    using swap_ap[OF rb_type c_type] by simp
  have s5: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c \<langle>c, right_coproj(A, B) \<circ>\<^sub>c b\<rangle> = right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, b\<rangle>"
    using dist_prod_coprod_left_ap_right[OF c_type b_type] by simp
  have s6: "(swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, b\<rangle>)
      = ((swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B)) \<circ>\<^sub>c \<langle>c, b\<rangle>"
    using comp_associative2[OF cb_type right_proj_type bw_type] by simp
  have s7: "(swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c right_coproj(C \<times>\<^sub>c A, C \<times>\<^sub>c B) = right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c swap(C, B)"
    using right_coproj_cfunc_bowtie_prod[OF swap_type swap_type] by simp
  have s8: "(right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c swap(C, B)) \<circ>\<^sub>c \<langle>c, b\<rangle> = right_coproj(A \<times>\<^sub>c C, B \<times>\<^sub>c C) \<circ>\<^sub>c (swap(C, B) \<circ>\<^sub>c \<langle>c, b\<rangle>)"
    using comp_associative2[OF cb_type swap_type right_proj_type] by simp
  have s9: "swap(C, B) \<circ>\<^sub>c \<langle>c, b\<rangle> = \<langle>b, c\<rangle>" using swap_ap[OF c_type b_type] by simp
  show ?thesis using s1 s2 s3 s4 s5 s6 s7 s8 s9 by simp
qed

lemma dist_prod_coprod_right_left_coproj:
  "dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (left_coproj(X, Y) \<times>\<^sub>f id(H)) = left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H)"
proof -
  have lid_type: "left_coproj(X, Y) \<times>\<^sub>f id(H) : X \<times>\<^sub>c H \<rightarrow> (X \<Coprod> Y) \<times>\<^sub>c H"
    using cfunc_cross_prod_type[OF left_proj_type id_type] by simp
  have dpr_type: "dist_prod_coprod_right(X, Y, H) : (X \<Coprod> Y) \<times>\<^sub>c H \<rightarrow> (X \<times>\<^sub>c H) \<Coprod> (Y \<times>\<^sub>c H)"
    by (rule dist_prod_coprod_right_type)
  have lhs_type: "dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (left_coproj(X, Y) \<times>\<^sub>f id(H)) : X \<times>\<^sub>c H \<rightarrow> (X \<times>\<^sub>c H) \<Coprod> (Y \<times>\<^sub>c H)"
    using comp_type[OF lid_type dpr_type] by simp
  have rhs_type: "left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) : X \<times>\<^sub>c H \<rightarrow> (X \<times>\<^sub>c H) \<Coprod> (Y \<times>\<^sub>c H)" by (rule left_proj_type)
  show ?thesis
  proof (rule one_separator[OF lhs_type rhs_type])
    fix z
    assume z_type: "z : \<one> \<rightarrow> X \<times>\<^sub>c H"
    obtain x h where x_type: "x \<in>\<^sub>c X" and h_type: "h \<in>\<^sub>c H" and z_eq: "z = \<langle>x, h\<rangle>"
      using cart_prod_decomp[OF z_type] by blast
    have s1: "(dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (left_coproj(X, Y) \<times>\<^sub>f id(H))) \<circ>\<^sub>c z
        = dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c ((left_coproj(X, Y) \<times>\<^sub>f id(H)) \<circ>\<^sub>c \<langle>x, h\<rangle>)"
      using comp_associative2[OF z_type lid_type dpr_type] z_eq by simp
    have s2: "(left_coproj(X, Y) \<times>\<^sub>f id(H)) \<circ>\<^sub>c \<langle>x, h\<rangle> = \<langle>left_coproj(X, Y) \<circ>\<^sub>c x, id(H) \<circ>\<^sub>c h\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF x_type h_type left_proj_type id_type] by simp
    have s3: "id(H) \<circ>\<^sub>c h = h" using id_left_unit2[OF h_type] by simp
    have s4: "dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c \<langle>left_coproj(X, Y) \<circ>\<^sub>c x, h\<rangle> = left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c \<langle>x, h\<rangle>"
      using dist_prod_coprod_right_ap_left[OF x_type h_type] by simp
    have s5: "left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c z = left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c \<langle>x, h\<rangle>" using z_eq by simp
    show "(dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (left_coproj(X, Y) \<times>\<^sub>f id(H))) \<circ>\<^sub>c z = left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c z"
      using s1 s2 s3 s4 s5 by simp
  qed
qed

lemma dist_prod_coprod_right_right_coproj:
  "dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (right_coproj(X, Y) \<times>\<^sub>f id(H)) = right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H)"
proof -
  have rid_type: "right_coproj(X, Y) \<times>\<^sub>f id(H) : Y \<times>\<^sub>c H \<rightarrow> (X \<Coprod> Y) \<times>\<^sub>c H"
    using cfunc_cross_prod_type[OF right_proj_type id_type] by simp
  have dpr_type: "dist_prod_coprod_right(X, Y, H) : (X \<Coprod> Y) \<times>\<^sub>c H \<rightarrow> (X \<times>\<^sub>c H) \<Coprod> (Y \<times>\<^sub>c H)"
    by (rule dist_prod_coprod_right_type)
  have lhs_type: "dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (right_coproj(X, Y) \<times>\<^sub>f id(H)) : Y \<times>\<^sub>c H \<rightarrow> (X \<times>\<^sub>c H) \<Coprod> (Y \<times>\<^sub>c H)"
    using comp_type[OF rid_type dpr_type] by simp
  have rhs_type: "right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) : Y \<times>\<^sub>c H \<rightarrow> (X \<times>\<^sub>c H) \<Coprod> (Y \<times>\<^sub>c H)" by (rule right_proj_type)
  show ?thesis
  proof (rule one_separator[OF lhs_type rhs_type])
    fix z
    assume z_type: "z : \<one> \<rightarrow> Y \<times>\<^sub>c H"
    obtain y h where y_type: "y \<in>\<^sub>c Y" and h_type: "h \<in>\<^sub>c H" and z_eq: "z = \<langle>y, h\<rangle>"
      using cart_prod_decomp[OF z_type] by blast
    have s1: "(dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (right_coproj(X, Y) \<times>\<^sub>f id(H))) \<circ>\<^sub>c z
        = dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c ((right_coproj(X, Y) \<times>\<^sub>f id(H)) \<circ>\<^sub>c \<langle>y, h\<rangle>)"
      using comp_associative2[OF z_type rid_type dpr_type] z_eq by simp
    have s2: "(right_coproj(X, Y) \<times>\<^sub>f id(H)) \<circ>\<^sub>c \<langle>y, h\<rangle> = \<langle>right_coproj(X, Y) \<circ>\<^sub>c y, id(H) \<circ>\<^sub>c h\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF y_type h_type right_proj_type id_type] by simp
    have s3: "id(H) \<circ>\<^sub>c h = h" using id_left_unit2[OF h_type] by simp
    have s4: "dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c \<langle>right_coproj(X, Y) \<circ>\<^sub>c y, h\<rangle> = right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c \<langle>y, h\<rangle>"
      using dist_prod_coprod_right_ap_right[OF y_type h_type] by simp
    have s5: "right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c z = right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c \<langle>y, h\<rangle>" using z_eq by simp
    show "(dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c (right_coproj(X, Y) \<times>\<^sub>f id(H))) \<circ>\<^sub>c z = right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H) \<circ>\<^sub>c z"
      using s1 s2 s3 s4 s5 by simp
  qed
qed

lemma factor_dist_prod_coprod_right:
  "factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c dist_prod_coprod_right(A, B, C) = id((A \<Coprod> B) \<times>\<^sub>c C)"
proof -
  define bwR where bwR_def: "bwR = swap(A, C) \<bowtie>\<^sub>f swap(B, C)"
  define bwL where bwL_def: "bwL = swap(C, A) \<bowtie>\<^sub>f swap(C, B)"
  have bwR_type: "bwR : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    unfolding bwR_def using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have bwL_type: "bwL : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    unfolding bwL_def using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have fpcl_type: "factor_prod_coprod_left(C, A, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    by (rule factor_prod_coprod_left_type)
  have dpcl_type: "dist_prod_coprod_left(C, A, B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    by (rule dist_prod_coprod_left_type)
  have swR_type: "swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)" by (rule swap_type)
  have swL_type: "swap(C, A \<Coprod> B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C" by (rule swap_type)

  have bwR_bwL: "bwR \<circ>\<^sub>c bwL = id((C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B))"
  proof -
    have swAC_type: "swap(A, C) : A \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c A" by (rule swap_type)
    have swCA_type: "swap(C, A) : C \<times>\<^sub>c A \<rightarrow> A \<times>\<^sub>c C" by (rule swap_type)
    have swBC_type: "swap(B, C) : B \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c B" by (rule swap_type)
    have swCB_type: "swap(C, B) : C \<times>\<^sub>c B \<rightarrow> B \<times>\<^sub>c C" by (rule swap_type)
    have u1: "bwR \<circ>\<^sub>c bwL = (swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c (swap(C, A) \<bowtie>\<^sub>f swap(C, B))"
      unfolding bwR_def bwL_def by simp
    have u2: "(swap(A, C) \<bowtie>\<^sub>f swap(B, C)) \<circ>\<^sub>c (swap(C, A) \<bowtie>\<^sub>f swap(C, B))
        = (swap(A, C) \<circ>\<^sub>c swap(C, A)) \<bowtie>\<^sub>f (swap(B, C) \<circ>\<^sub>c swap(C, B))"
      using cfunc_bowtie_prod_comp_cfunc_bowtie_prod[OF swCA_type swCB_type swAC_type swBC_type] by simp
    have u3: "swap(A, C) \<circ>\<^sub>c swap(C, A) = id(C \<times>\<^sub>c A)" using swap_idempotent by simp
    have u4: "swap(B, C) \<circ>\<^sub>c swap(C, B) = id(C \<times>\<^sub>c B)" using swap_idempotent by simp
    have u5: "id(C \<times>\<^sub>c A) \<bowtie>\<^sub>f id(C \<times>\<^sub>c B) = id((C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B))" using id_bowtie_prod by simp
    show ?thesis using u1 u2 u3 u4 u5 by simp
  qed

  have F_eq: "factor_prod_coprod_right(A, B, C) = swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR)"
    unfolding factor_prod_coprod_right_def bwR_def by simp
  have D_eq: "dist_prod_coprod_right(A, B, C) = bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))"
    unfolding dist_prod_coprod_right_def bwL_def by simp
  have fpcl_bwR_type: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    using comp_type[OF bwR_type fpcl_type] by simp
  have dpcl_swR_type: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using comp_type[OF swR_type dpcl_type] by simp
  have bwL_dpcl_swR_type: "bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    using comp_type[OF dpcl_swR_type bwL_type] by simp

  have t1: "factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c dist_prod_coprod_right(A, B, C)
      = (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR))
          \<circ>\<^sub>c (bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)))"
    using F_eq D_eq by simp
  have t2: "(swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR))
        \<circ>\<^sub>c (bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)))
      = swap(C, A \<Coprod> B) \<circ>\<^sub>c ((factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR)
          \<circ>\<^sub>c (bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))))"
    using comp_associative2[OF bwL_dpcl_swR_type fpcl_bwR_type swL_type] by simp
  have t3: "(factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR) \<circ>\<^sub>c (bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)))
      = factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (bwR \<circ>\<^sub>c (bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))))"
    using comp_associative2[OF bwL_dpcl_swR_type bwR_type fpcl_type] by simp
  have t4: "bwR \<circ>\<^sub>c (bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)))
      = (bwR \<circ>\<^sub>c bwL) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))"
    using comp_associative2[OF dpcl_swR_type bwL_type bwR_type] by simp
  have t5: "(bwR \<circ>\<^sub>c bwL) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))
      = id((C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))"
    using bwR_bwL by simp
  have t6: "id((C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))
      = dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)"
    using id_left_unit2[OF dpcl_swR_type] by simp
  have t7: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))
      = (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c dist_prod_coprod_left(C, A, B)) \<circ>\<^sub>c swap(A \<Coprod> B, C)"
    using comp_associative2[OF swR_type dpcl_type fpcl_type] by simp
  have t8: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c dist_prod_coprod_left(C, A, B) = id(C \<times>\<^sub>c (A \<Coprod> B))"
    by (rule factor_dist_prod_coprod_left)
  have t9: "id(C \<times>\<^sub>c (A \<Coprod> B)) \<circ>\<^sub>c swap(A \<Coprod> B, C) = swap(A \<Coprod> B, C)" using id_left_unit2[OF swR_type] by simp
  have t10: "swap(C, A \<Coprod> B) \<circ>\<^sub>c swap(A \<Coprod> B, C) = id((A \<Coprod> B) \<times>\<^sub>c C)" using swap_idempotent by simp
  show ?thesis using t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 by simp
qed

lemma dist_factor_prod_coprod_right:
  "dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c factor_prod_coprod_right(A, B, C) = id((A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C))"
proof -
  define bwR where bwR_def: "bwR = swap(A, C) \<bowtie>\<^sub>f swap(B, C)"
  define bwL where bwL_def: "bwL = swap(C, A) \<bowtie>\<^sub>f swap(C, B)"
  have bwR_type: "bwR : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    unfolding bwR_def using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have bwL_type: "bwL : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    unfolding bwL_def using cfunc_bowtie_prod_type[OF swap_type swap_type] by simp
  have fpcl_type: "factor_prod_coprod_left(C, A, B) : (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    by (rule factor_prod_coprod_left_type)
  have dpcl_type: "dist_prod_coprod_left(C, A, B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    by (rule dist_prod_coprod_left_type)
  have swR_type: "swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)" by (rule swap_type)
  have swL_type: "swap(C, A \<Coprod> B) : C \<times>\<^sub>c (A \<Coprod> B) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C" by (rule swap_type)

  have bwL_bwR: "bwL \<circ>\<^sub>c bwR = id((A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C))"
  proof -
    have swAC_type: "swap(A, C) : A \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c A" by (rule swap_type)
    have swCA_type: "swap(C, A) : C \<times>\<^sub>c A \<rightarrow> A \<times>\<^sub>c C" by (rule swap_type)
    have swBC_type: "swap(B, C) : B \<times>\<^sub>c C \<rightarrow> C \<times>\<^sub>c B" by (rule swap_type)
    have swCB_type: "swap(C, B) : C \<times>\<^sub>c B \<rightarrow> B \<times>\<^sub>c C" by (rule swap_type)
    have u1: "bwL \<circ>\<^sub>c bwR = (swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))"
      unfolding bwR_def bwL_def by simp
    have u2: "(swap(C, A) \<bowtie>\<^sub>f swap(C, B)) \<circ>\<^sub>c (swap(A, C) \<bowtie>\<^sub>f swap(B, C))
        = (swap(C, A) \<circ>\<^sub>c swap(A, C)) \<bowtie>\<^sub>f (swap(C, B) \<circ>\<^sub>c swap(B, C))"
      using cfunc_bowtie_prod_comp_cfunc_bowtie_prod[OF swAC_type swBC_type swCA_type swCB_type] by simp
    have u3: "swap(C, A) \<circ>\<^sub>c swap(A, C) = id(A \<times>\<^sub>c C)" using swap_idempotent by simp
    have u4: "swap(C, B) \<circ>\<^sub>c swap(B, C) = id(B \<times>\<^sub>c C)" using swap_idempotent by simp
    have u5: "id(A \<times>\<^sub>c C) \<bowtie>\<^sub>f id(B \<times>\<^sub>c C) = id((A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C))" using id_bowtie_prod by simp
    show ?thesis using u1 u2 u3 u4 u5 by simp
  qed

  have F_eq: "factor_prod_coprod_right(A, B, C) = swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR)"
    unfolding factor_prod_coprod_right_def bwR_def by simp
  have D_eq: "dist_prod_coprod_right(A, B, C) = bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))"
    unfolding dist_prod_coprod_right_def bwL_def by simp
  have fpcl_bwR_type: "factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> C \<times>\<^sub>c (A \<Coprod> B)"
    using comp_type[OF bwR_type fpcl_type] by simp
  have dpcl_swR_type: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using comp_type[OF swR_type dpcl_type] by simp
  have swL_fpcl_bwR_type: "swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR) : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C"
    using comp_type[OF fpcl_bwR_type swL_type] by simp

  have t1: "dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c factor_prod_coprod_right(A, B, C)
      = (bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)))
          \<circ>\<^sub>c (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR))"
    using F_eq D_eq by simp
  have t2: "(bwL \<circ>\<^sub>c (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)))
        \<circ>\<^sub>c (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR))
      = bwL \<circ>\<^sub>c ((dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C))
          \<circ>\<^sub>c (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR)))"
    using comp_associative2[OF swL_fpcl_bwR_type dpcl_swR_type bwL_type] by simp
  have t3: "(dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c swap(A \<Coprod> B, C)) \<circ>\<^sub>c (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR))
      = dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c (swap(A \<Coprod> B, C) \<circ>\<^sub>c (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR)))"
    using comp_associative2[OF swL_fpcl_bwR_type swR_type dpcl_type] by simp
  have t4: "swap(A \<Coprod> B, C) \<circ>\<^sub>c (swap(C, A \<Coprod> B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR))
      = (swap(A \<Coprod> B, C) \<circ>\<^sub>c swap(C, A \<Coprod> B)) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR)"
    using comp_associative2[OF fpcl_bwR_type swL_type swR_type] by simp
  have t5: "swap(A \<Coprod> B, C) \<circ>\<^sub>c swap(C, A \<Coprod> B) = id(C \<times>\<^sub>c (A \<Coprod> B))" using swap_idempotent by simp
  have t6: "id(C \<times>\<^sub>c (A \<Coprod> B)) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR) = factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR"
    using id_left_unit2[OF fpcl_bwR_type] by simp
  have t7: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c (factor_prod_coprod_left(C, A, B) \<circ>\<^sub>c bwR)
      = (dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c factor_prod_coprod_left(C, A, B)) \<circ>\<^sub>c bwR"
    using comp_associative2[OF bwR_type fpcl_type dpcl_type] by simp
  have t8: "dist_prod_coprod_left(C, A, B) \<circ>\<^sub>c factor_prod_coprod_left(C, A, B) = id((C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B))"
    by (rule dist_factor_prod_coprod_left)
  have t9: "id((C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)) \<circ>\<^sub>c bwR = bwR" using id_left_unit2[OF bwR_type] by simp
  have t10: "bwL \<circ>\<^sub>c bwR = id((A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C))" using bwL_bwR by simp
  show ?thesis using t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 by simp
qed

lemma factor_prod_coprod_right_iso:
  "isomorphism(factor_prod_coprod_right(A, B, C))"
proof -
  have t: "factor_prod_coprod_right(A, B, C) : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C"
    by (rule factor_prod_coprod_right_type)
  have witness: "dist_prod_coprod_right(A, B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)
      \<and> dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c factor_prod_coprod_right(A, B, C) = id((A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C))
      \<and> factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c dist_prod_coprod_right(A, B, C) = id((A \<Coprod> B) \<times>\<^sub>c C)"
  proof (intro conjI)
    show "dist_prod_coprod_right(A, B, C) : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
      by (rule dist_prod_coprod_right_type)
  next
    show "dist_prod_coprod_right(A, B, C) \<circ>\<^sub>c factor_prod_coprod_right(A, B, C) = id((A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C))"
      by (rule dist_factor_prod_coprod_right)
  next
    show "factor_prod_coprod_right(A, B, C) \<circ>\<^sub>c dist_prod_coprod_right(A, B, C) = id((A \<Coprod> B) \<times>\<^sub>c C)"
      by (rule factor_dist_prod_coprod_right)
  qed
  show ?thesis unfolding isomorphism_def3[OF t] using witness by blast
qed

subsection \<open>Casting between Sets\<close>

subsubsection \<open>Going from a Set or its Complement to the Superset\<close>

text \<open>This subsection corresponds to Proposition 2.4.5 in Halvorson.\<close>
definition into_super :: "cfunc \<Rightarrow> cfunc" where
  "into_super(m) = m \<amalg> m\<^sup>c"

lemma into_super_type[type_rule]:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y"
proof -
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  show ?thesis unfolding into_super_def using cfunc_coprod_type[OF m_type mc_type] by simp
qed

lemma into_super_mono:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "monomorphism(into_super(m))"
proof -
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  have mc_mono: "monomorphism(m\<^sup>c)" using complement_morphism_mono[OF m_type m_mono] by simp
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have is_left: "into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m)) = m"
    using left_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have is_right: "into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m)) = m\<^sup>c"
    using right_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have inj: "injective(into_super(m))"
    unfolding injective_def2[OF is_type]
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c X \<Coprod> set_subtraction(m) \<and> y \<in>\<^sub>c X \<Coprod> set_subtraction(m) \<and> into_super(m) \<circ>\<^sub>c x = into_super(m) \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c X \<Coprod> set_subtraction(m)" and y_type: "y \<in>\<^sub>c X \<Coprod> set_subtraction(m)"
      and eqs: "into_super(m) \<circ>\<^sub>c x = into_super(m) \<circ>\<^sub>c y" by auto
    have x_disj: "(\<exists>x'. x' \<in>\<^sub>c X \<and> x = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x')
        \<or> (\<exists>x'. x' \<in>\<^sub>c set_subtraction(m) \<and> x = right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x')"
      using coprojs_jointly_surj[OF x_type] by simp
    have y_disj: "(\<exists>y'. y' \<in>\<^sub>c X \<and> y = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y')
        \<or> (\<exists>y'. y' \<in>\<^sub>c set_subtraction(m) \<and> y = right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y')"
      using coprojs_jointly_surj[OF y_type] by simp
    show "x = y"
    proof (cases "\<exists>x'. x' \<in>\<^sub>c X \<and> x = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x'")
      case True
      then obtain x' where x'_type: "x' \<in>\<^sub>c X" and x_eq: "x = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x'" by auto
      show "x = y"
      proof (cases "\<exists>y'. y' \<in>\<^sub>c X \<and> y = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y'")
        case True
        then obtain y' where y'_type: "y' \<in>\<^sub>c X" and y_eq: "y = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y'" by auto
        have s1: "into_super(m) \<circ>\<^sub>c x = m \<circ>\<^sub>c x'"
        proof -
          have "into_super(m) \<circ>\<^sub>c x = into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x')" using x_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x'"
            using comp_associative2[OF x'_type left_proj_type is_type] by simp
          also have "... = m \<circ>\<^sub>c x'" using is_left by simp
          finally show ?thesis by simp
        qed
        have s2: "into_super(m) \<circ>\<^sub>c y = m \<circ>\<^sub>c y'"
        proof -
          have "into_super(m) \<circ>\<^sub>c y = into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y')" using y_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m))) \<circ>\<^sub>c y'"
            using comp_associative2[OF y'_type left_proj_type is_type] by simp
          also have "... = m \<circ>\<^sub>c y'" using is_left by simp
          finally show ?thesis by simp
        qed
        have mx_eq: "m \<circ>\<^sub>c x' = m \<circ>\<^sub>c y'" using eqs s1 s2 by simp
        have x'_eq_y': "x' = y'"
          using monomorphism_def3[OF m_type, THEN iffD1, rule_format, where g=x' and h=y' and A="\<one>"]
            m_mono x'_type y'_type mx_eq by auto
        show "x = y" using x_eq y_eq x'_eq_y' by simp
      next
        case False
        then obtain y' where y'_type: "y' \<in>\<^sub>c set_subtraction(m)" and y_eq: "y = right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y'"
          using y_disj by auto
        have s1: "into_super(m) \<circ>\<^sub>c x = m \<circ>\<^sub>c x'"
        proof -
          have "into_super(m) \<circ>\<^sub>c x = into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x')" using x_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x'"
            using comp_associative2[OF x'_type left_proj_type is_type] by simp
          also have "... = m \<circ>\<^sub>c x'" using is_left by simp
          finally show ?thesis by simp
        qed
        have s2: "into_super(m) \<circ>\<^sub>c y = m\<^sup>c \<circ>\<^sub>c y'"
        proof -
          have "into_super(m) \<circ>\<^sub>c y = into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y')" using y_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m))) \<circ>\<^sub>c y'"
            using comp_associative2[OF y'_type right_proj_type is_type] by simp
          also have "... = m\<^sup>c \<circ>\<^sub>c y'" using is_right by simp
          finally show ?thesis by simp
        qed
        have "m \<circ>\<^sub>c x' = m\<^sup>c \<circ>\<^sub>c y'" using eqs s1 s2 by simp
        then have "False" using complement_disjoint[OF m_type m_mono x'_type y'_type] by simp
        then show "x = y" by simp
      qed
    next
      case False
      then obtain x' where x'_type: "x' \<in>\<^sub>c set_subtraction(m)" and x_eq: "x = right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x'"
        using x_disj by auto
      show "x = y"
      proof (cases "\<exists>y'. y' \<in>\<^sub>c X \<and> y = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y'")
        case True
        then obtain y' where y'_type: "y' \<in>\<^sub>c X" and y_eq: "y = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y'" by auto
        have s1: "into_super(m) \<circ>\<^sub>c x = m\<^sup>c \<circ>\<^sub>c x'"
        proof -
          have "into_super(m) \<circ>\<^sub>c x = into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x')" using x_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x'"
            using comp_associative2[OF x'_type right_proj_type is_type] by simp
          also have "... = m\<^sup>c \<circ>\<^sub>c x'" using is_right by simp
          finally show ?thesis by simp
        qed
        have s2: "into_super(m) \<circ>\<^sub>c y = m \<circ>\<^sub>c y'"
        proof -
          have "into_super(m) \<circ>\<^sub>c y = into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y')" using y_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m))) \<circ>\<^sub>c y'"
            using comp_associative2[OF y'_type left_proj_type is_type] by simp
          also have "... = m \<circ>\<^sub>c y'" using is_left by simp
          finally show ?thesis by simp
        qed
        have "m\<^sup>c \<circ>\<^sub>c x' = m \<circ>\<^sub>c y'" using eqs s1 s2 by simp
        then have "m \<circ>\<^sub>c y' = m\<^sup>c \<circ>\<^sub>c x'" by simp
        then have "False" using complement_disjoint[OF m_type m_mono y'_type x'_type] by simp
        then show "x = y" by simp
      next
        case False
        then obtain y' where y'_type: "y' \<in>\<^sub>c set_subtraction(m)" and y_eq: "y = right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y'"
          using y_disj by auto
        have s1: "into_super(m) \<circ>\<^sub>c x = m\<^sup>c \<circ>\<^sub>c x'"
        proof -
          have "into_super(m) \<circ>\<^sub>c x = into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x')" using x_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x'"
            using comp_associative2[OF x'_type right_proj_type is_type] by simp
          also have "... = m\<^sup>c \<circ>\<^sub>c x'" using is_right by simp
          finally show ?thesis by simp
        qed
        have s2: "into_super(m) \<circ>\<^sub>c y = m\<^sup>c \<circ>\<^sub>c y'"
        proof -
          have "into_super(m) \<circ>\<^sub>c y = into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c y')" using y_eq by simp
          also have "... = (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m))) \<circ>\<^sub>c y'"
            using comp_associative2[OF y'_type right_proj_type is_type] by simp
          also have "... = m\<^sup>c \<circ>\<^sub>c y'" using is_right by simp
          finally show ?thesis by simp
        qed
        have mcx_eq: "m\<^sup>c \<circ>\<^sub>c x' = m\<^sup>c \<circ>\<^sub>c y'" using eqs s1 s2 by simp
        have x'_eq_y': "x' = y'"
          using monomorphism_def3[OF mc_type, THEN iffD1, rule_format, where g=x' and h=y' and A="\<one>"]
            mc_mono x'_type y'_type mcx_eq by auto
        show "x = y" using x_eq y_eq x'_eq_y' by simp
      qed
    qed
  qed
  show ?thesis using injective_imp_monomorphism[OF inj] by simp
qed

lemma into_super_epi:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "epimorphism(into_super(m))"
proof -
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have is_left: "into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m)) = m"
    using left_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have is_right: "into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m)) = m\<^sup>c"
    using right_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have surj: "surjective(into_super(m))"
    unfolding surjective_def2[OF is_type]
  proof (intro allI impI)
    fix y
    assume y_type: "y \<in>\<^sub>c Y"
    have chi_type: "characteristic_func(m) : Y \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
    have chiy_type: "characteristic_func(m) \<circ>\<^sub>c y \<in>\<^sub>c \<Omega>" using y_type chi_type comp_type by blast
    have y_cases: "characteristic_func(m) \<circ>\<^sub>c y = \<t> \<or> characteristic_func(m) \<circ>\<^sub>c y = \<f>"
      using true_false_only_truth_values[OF chiy_type] by auto
    show "\<exists>x. x \<in>\<^sub>c X \<Coprod> set_subtraction(m) \<and> into_super(m) \<circ>\<^sub>c x = y"
    proof (cases "characteristic_func(m) \<circ>\<^sub>c y = \<t>")
      case True
      have y_mem: "relative_member(y, Y, X, m)"
        using characteristic_func_true_relative_member[OF m_type m_mono y_type True] by simp
      have y_ft: "y factorsthru m" using y_mem unfolding relative_member_def by auto
      obtain x where x_type: "x : \<one> \<rightarrow> X" and x_eq: "m \<circ>\<^sub>c x = y"
        using factors_through_def2[OF y_type m_type] y_ft by auto
      have lx_type: "left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x \<in>\<^sub>c X \<Coprod> set_subtraction(m)"
        using x_type left_proj_type comp_type by blast
      have h_eq: "into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x) = y"
      proof -
        have "into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x)
            = (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x"
          using comp_associative2[OF x_type left_proj_type is_type] by simp
        also have "... = m \<circ>\<^sub>c x" using is_left by simp
        also have "... = y" using x_eq by simp
        finally show ?thesis by simp
      qed
      show ?thesis using lx_type h_eq by auto
    next
      case False
      have y_eq_f: "characteristic_func(m) \<circ>\<^sub>c y = \<f>" using y_cases False by auto
      have not_mem: "\<not> relative_member(y, Y, X, m)"
        using characteristic_func_false_not_relative_member[OF m_type m_mono y_type y_eq_f] by simp
      have y_mem2: "relative_member(y, Y, set_subtraction(m), m\<^sup>c)"
        using not_in_subset_in_complement[OF m_type m_mono y_type not_mem] by simp
      have y_ft2: "y factorsthru m\<^sup>c" using y_mem2 unfolding relative_member_def by auto
      obtain x' where x'_type: "x' : \<one> \<rightarrow> set_subtraction(m)" and x'_eq: "m\<^sup>c \<circ>\<^sub>c x' = y"
        using factors_through_def2[OF y_type mc_type] y_ft2 by auto
      have rx'_type: "right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x' \<in>\<^sub>c X \<Coprod> set_subtraction(m)"
        using x'_type right_proj_type comp_type by blast
      have h_eq: "into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x') = y"
      proof -
        have "into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x')
            = (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x'"
          using comp_associative2[OF x'_type right_proj_type is_type] by simp
        also have "... = m\<^sup>c \<circ>\<^sub>c x'" using is_right by simp
        also have "... = y" using x'_eq by simp
        finally show ?thesis by simp
      qed
      show ?thesis using rx'_type h_eq by auto
    qed
  qed
  show ?thesis using surjective_is_epimorphism[OF surj] by simp
qed

lemma into_super_iso:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "isomorphism(into_super(m))"
  using epi_mon_is_iso[OF into_super_epi[OF m_mono m_type] into_super_mono[OF m_mono m_type]] by simp

subsubsection \<open>Going from a Set to a Subset or its Complement\<close>

text \<open>As with @{text case_bool}/@{text dist_prod_coprod_left}, defined directly as the generic
  inverse of the already-established isomorphism @{text into_super}, avoiding HOL's @{text THE}.\<close>
definition try_cast :: "cfunc \<Rightarrow> cfunc" where
  "try_cast(m) = (into_super(m))\<^bold>\<inverse>"

lemma try_cast_def2:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)
    \<and> try_cast(m) \<circ>\<^sub>c into_super(m) = id(X \<Coprod> set_subtraction(m))
    \<and> into_super(m) \<circ>\<^sub>c try_cast(m) = id(Y)"
proof -
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have is_iso: "isomorphism(into_super(m))" using into_super_iso[OF m_mono m_type] by simp
  have spec: "(into_super(m))\<^bold>\<inverse> : codomain(into_super(m)) \<rightarrow> domain(into_super(m))
      \<and> (into_super(m))\<^bold>\<inverse> \<circ>\<^sub>c into_super(m) = id(domain(into_super(m)))
      \<and> into_super(m) \<circ>\<^sub>c (into_super(m))\<^bold>\<inverse> = id(codomain(into_super(m)))"
    using inverse_def2[OF is_iso] by simp
  have dom_is: "domain(into_super(m)) = X \<Coprod> set_subtraction(m)" using is_type unfolding cfunc_type_def by auto
  have cod_is: "codomain(into_super(m)) = Y" using is_type unfolding cfunc_type_def by auto
  show ?thesis unfolding try_cast_def using spec dom_is cod_is by simp
qed

lemma try_cast_type[type_rule]:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)"
  using try_cast_def2[OF m_mono m_type] by auto

lemma try_cast_into_super:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "try_cast(m) \<circ>\<^sub>c into_super(m) = id(X \<Coprod> set_subtraction(m))"
  using try_cast_def2[OF m_mono m_type] by auto

lemma into_super_try_cast:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "into_super(m) \<circ>\<^sub>c try_cast(m) = id(Y)"
  using try_cast_def2[OF m_mono m_type] by auto

lemma try_cast_in_X:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  assumes y_in_X: "relative_member(y, Y, X, m)"
  shows "\<exists>x. x \<in>\<^sub>c X \<and> try_cast(m) \<circ>\<^sub>c y = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x"
proof -
  have y_type: "y \<in>\<^sub>c Y" using y_in_X unfolding relative_member_def by auto
  have y_ft: "y factorsthru m" using y_in_X unfolding relative_member_def by auto
  obtain x where x_type: "x \<in>\<^sub>c X" and x_eq: "m \<circ>\<^sub>c x = y"
    using factors_through_def2[OF y_type m_type] y_ft by auto
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  have lx_type: "left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x \<in>\<^sub>c X \<Coprod> set_subtraction(m)"
    using x_type left_proj_type comp_type by blast
  have is_left: "into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m)) = m"
    using left_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have s1: "into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x)
      = (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x"
    using comp_associative2[OF x_type left_proj_type is_type] by simp
  have s2: "y = into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x)" using s1 is_left x_eq by simp
  have tc_type: "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)" using try_cast_type[OF m_mono m_type] by simp
  have s3: "try_cast(m) \<circ>\<^sub>c y = try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x))"
    using s2 by simp
  have s4: "try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x))
      = (try_cast(m) \<circ>\<^sub>c into_super(m)) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x)"
    using comp_associative2[OF lx_type is_type tc_type] by simp
  have s5: "try_cast(m) \<circ>\<^sub>c into_super(m) = id(X \<Coprod> set_subtraction(m))" using try_cast_into_super[OF m_mono m_type] by simp
  have s6: "id(X \<Coprod> set_subtraction(m)) \<circ>\<^sub>c (left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x) = left_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x"
    using id_left_unit2[OF lx_type] by simp
  show ?thesis using x_type s3 s4 s5 s6 by auto
qed

lemma try_cast_not_in_X:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  assumes y_not_in_X: "\<not> relative_member(y, Y, X, m)" and y_type: "y \<in>\<^sub>c Y"
  shows "\<exists>x. x \<in>\<^sub>c set_subtraction(m) \<and> try_cast(m) \<circ>\<^sub>c y = right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x"
proof -
  have y_in_comp: "relative_member(y, Y, set_subtraction(m), m\<^sup>c)"
    using not_in_subset_in_complement[OF m_type m_mono y_type y_not_in_X] by simp
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  have y_ft: "y factorsthru m\<^sup>c" using y_in_comp unfolding relative_member_def by auto
  obtain x where x_type: "x \<in>\<^sub>c set_subtraction(m)" and x_eq: "m\<^sup>c \<circ>\<^sub>c x = y"
    using factors_through_def2[OF y_type mc_type] y_ft by auto
  have rx_type: "right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x \<in>\<^sub>c X \<Coprod> set_subtraction(m)"
    using x_type right_proj_type comp_type by blast
  have is_right: "into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m)) = m\<^sup>c"
    using right_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have s1: "into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x)
      = (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m))) \<circ>\<^sub>c x"
    using comp_associative2[OF x_type right_proj_type is_type] by simp
  have s2: "y = into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x)" using s1 is_right x_eq by simp
  have tc_type: "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)" using try_cast_type[OF m_mono m_type] by simp
  have s3: "try_cast(m) \<circ>\<^sub>c y = try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x))"
    using s2 by simp
  have s4: "try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x))
      = (try_cast(m) \<circ>\<^sub>c into_super(m)) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x)"
    using comp_associative2[OF rx_type is_type tc_type] by simp
  have s5: "try_cast(m) \<circ>\<^sub>c into_super(m) = id(X \<Coprod> set_subtraction(m))" using try_cast_into_super[OF m_mono m_type] by simp
  have s6: "id(X \<Coprod> set_subtraction(m)) \<circ>\<^sub>c (right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x) = right_coproj(X, set_subtraction(m)) \<circ>\<^sub>c x"
    using id_left_unit2[OF rx_type] by simp
  show ?thesis using x_type s3 s4 s5 s6 by auto
qed

lemma try_cast_m_m:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "try_cast(m) \<circ>\<^sub>c m = left_coproj(X, set_subtraction(m))"
proof -
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have is_left: "into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m)) = m"
    using left_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have tc_type: "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)" using try_cast_type[OF m_mono m_type] by simp
  have lx_type: "left_coproj(X, set_subtraction(m)) : X \<rightarrow> X \<Coprod> set_subtraction(m)" by (rule left_proj_type)
  have s1: "try_cast(m) \<circ>\<^sub>c m = try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m)))" using is_left by simp
  have s2: "try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c left_coproj(X, set_subtraction(m)))
      = (try_cast(m) \<circ>\<^sub>c into_super(m)) \<circ>\<^sub>c left_coproj(X, set_subtraction(m))"
    using comp_associative2[OF lx_type is_type tc_type] by simp
  have s3: "try_cast(m) \<circ>\<^sub>c into_super(m) = id(X \<Coprod> set_subtraction(m))" using try_cast_into_super[OF m_mono m_type] by simp
  have s4: "id(X \<Coprod> set_subtraction(m)) \<circ>\<^sub>c left_coproj(X, set_subtraction(m)) = left_coproj(X, set_subtraction(m))"
    using id_left_unit2[OF lx_type] by simp
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma try_cast_m_m':
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "try_cast(m) \<circ>\<^sub>c m\<^sup>c = right_coproj(X, set_subtraction(m))"
proof -
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have is_right: "into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m)) = m\<^sup>c"
    using right_coproj_cfunc_coprod[OF m_type mc_type] unfolding into_super_def by simp
  have tc_type: "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)" using try_cast_type[OF m_mono m_type] by simp
  have rx_type: "right_coproj(X, set_subtraction(m)) : set_subtraction(m) \<rightarrow> X \<Coprod> set_subtraction(m)"
    by (rule right_proj_type)
  have s1: "try_cast(m) \<circ>\<^sub>c m\<^sup>c = try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m)))" using is_right by simp
  have s2: "try_cast(m) \<circ>\<^sub>c (into_super(m) \<circ>\<^sub>c right_coproj(X, set_subtraction(m)))
      = (try_cast(m) \<circ>\<^sub>c into_super(m)) \<circ>\<^sub>c right_coproj(X, set_subtraction(m))"
    using comp_associative2[OF rx_type is_type tc_type] by simp
  have s3: "try_cast(m) \<circ>\<^sub>c into_super(m) = id(X \<Coprod> set_subtraction(m))" using try_cast_into_super[OF m_mono m_type] by simp
  have s4: "id(X \<Coprod> set_subtraction(m)) \<circ>\<^sub>c right_coproj(X, set_subtraction(m)) = right_coproj(X, set_subtraction(m))"
    using id_left_unit2[OF rx_type] by simp
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma try_cast_mono:
  assumes m_mono: "monomorphism(m)" and m_type: "m : X \<rightarrow> Y"
  shows "monomorphism(try_cast(m))"
proof -
  have tc_type: "try_cast(m) : Y \<rightarrow> X \<Coprod> set_subtraction(m)" using try_cast_type[OF m_mono m_type] by simp
  have is_type: "into_super(m) : X \<Coprod> set_subtraction(m) \<rightarrow> Y" using into_super_type[OF m_mono m_type] by simp
  have comp_eq: "into_super(m) \<circ>\<^sub>c try_cast(m) = id(Y)" using into_super_try_cast[OF m_mono m_type] by simp
  have idY_mono: "monomorphism(id(Y))" using iso_imp_epi_and_monic[OF id_isomorphism] by (rule conjunct2)
  have comp_mono: "monomorphism(into_super(m) \<circ>\<^sub>c try_cast(m))" using comp_eq idY_mono by simp
  show ?thesis using comp_monic_imp_monic'[OF tc_type is_type comp_mono] by simp
qed

subsection \<open>Cases\<close>

definition cases :: "cfunc \<Rightarrow> cfunc" where
  "cases(f) = (right_cart_proj(\<one>, domain(f)) \<bowtie>\<^sub>f right_cart_proj(\<one>, domain(f)))
      \<circ>\<^sub>c (dist_prod_coprod_right(\<one>, \<one>, domain(f)) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(domain(f))\<rangle>)"

lemma cases_def2:
  assumes f_type: "f : X \<rightarrow> \<Omega>"
  shows "cases(f) = (right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X))
      \<circ>\<^sub>c (dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>)"
proof -
  have dom_f: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
  show ?thesis unfolding cases_def using dom_f by simp
qed

lemma cases_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> \<Omega>"
  shows "cases(f) : X \<rightarrow> X \<Coprod> X"
proof -
  have cb_type: "case_bool \<circ>\<^sub>c f : X \<rightarrow> \<one> \<Coprod> \<one>" using f_type case_bool_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have pair_type: "\<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> : X \<rightarrow> (\<one> \<Coprod> \<one>) \<times>\<^sub>c X" using cb_type idX_type cfunc_prod_type by auto
  have dpr_type: "dist_prod_coprod_right(\<one>, \<one>, X) : (\<one> \<Coprod> \<one>) \<times>\<^sub>c X \<rightarrow> (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X)"
    by (rule dist_prod_coprod_right_type)
  have inner_type: "dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> : X \<rightarrow> (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X)"
    using comp_type[OF pair_type dpr_type] by simp
  have rp_type: "right_cart_proj(\<one>, X) : \<one> \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)
  have bw_type: "right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X) : (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X) \<rightarrow> X \<Coprod> X"
    using cfunc_bowtie_prod_type[OF rp_type rp_type] by simp
  show ?thesis unfolding cases_def2[OF f_type] using comp_type[OF inner_type bw_type] by simp
qed

lemma true_case:
  assumes x_type: "x \<in>\<^sub>c X" and f_type: "f : X \<rightarrow> \<Omega>" and true_case: "f \<circ>\<^sub>c x = \<t>"
  shows "cases(f) \<circ>\<^sub>c x = left_coproj(X, X) \<circ>\<^sub>c x"
proof -
  have cb_type: "case_bool \<circ>\<^sub>c f : X \<rightarrow> \<one> \<Coprod> \<one>" using f_type case_bool_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have pair_type: "\<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> : X \<rightarrow> (\<one> \<Coprod> \<one>) \<times>\<^sub>c X" using cb_type idX_type cfunc_prod_type by auto
  have dpr_type: "dist_prod_coprod_right(\<one>, \<one>, X) : (\<one> \<Coprod> \<one>) \<times>\<^sub>c X \<rightarrow> (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X)"
    by (rule dist_prod_coprod_right_type)
  have rp_type: "right_cart_proj(\<one>, X) : \<one> \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)
  have bw_type: "right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X) : (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X) \<rightarrow> X \<Coprod> X"
    using cfunc_bowtie_prod_type[OF rp_type rp_type] by simp
  have inner_type: "dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> : X \<rightarrow> (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X)"
    using comp_type[OF pair_type dpr_type] by simp
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have id1x_type: "\<langle>id(\<one>), x\<rangle> \<in>\<^sub>c \<one> \<times>\<^sub>c X" using id1_type x_type cfunc_prod_type by auto

  have s1: "cases(f) \<circ>\<^sub>c x
      = ((right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X))
          \<circ>\<^sub>c (dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>)) \<circ>\<^sub>c x"
    unfolding cases_def2[OF f_type] by simp
  have s2: "((right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X))
        \<circ>\<^sub>c (dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>)) \<circ>\<^sub>c x
      = (right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X))
          \<circ>\<^sub>c ((dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>) \<circ>\<^sub>c x)"
    using comp_associative2[OF x_type inner_type bw_type] by simp
  have s3: "(dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>) \<circ>\<^sub>c x
      = dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c (\<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> \<circ>\<^sub>c x)"
    using comp_associative2[OF x_type pair_type dpr_type] by simp
  have s4: "\<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> \<circ>\<^sub>c x = \<langle>(case_bool \<circ>\<^sub>c f) \<circ>\<^sub>c x, id(X) \<circ>\<^sub>c x\<rangle>"
    using cfunc_prod_comp[OF x_type cb_type idX_type] by simp
  have s5: "(case_bool \<circ>\<^sub>c f) \<circ>\<^sub>c x = case_bool \<circ>\<^sub>c (f \<circ>\<^sub>c x)"
    using comp_associative2[OF x_type f_type case_bool_type] by simp
  have s6: "case_bool \<circ>\<^sub>c (f \<circ>\<^sub>c x) = case_bool \<circ>\<^sub>c \<t>" using true_case by simp
  have s7: "case_bool \<circ>\<^sub>c \<t> = left_coproj(\<one>, \<one>)" by (rule case_bool_true)
  have s8: "id(X) \<circ>\<^sub>c x = x" using id_left_unit2[OF x_type] by simp
  have s9: "dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>left_coproj(\<one>, \<one>), x\<rangle> = left_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>"
  proof -
    have h_eq: "dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>left_coproj(\<one>, \<one>) \<circ>\<^sub>c id(\<one>), x\<rangle>
        = left_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>"
      using dist_prod_coprod_right_ap_left[OF id1_type x_type] by simp
    have id1_eq: "left_coproj(\<one>, \<one>) \<circ>\<^sub>c id(\<one>) = left_coproj(\<one>, \<one>)" using id_right_unit2[OF left_proj_type] by simp
    show ?thesis using h_eq id1_eq by simp
  qed
  have s10: "(right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X)) \<circ>\<^sub>c (left_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>)
      = ((right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X)) \<circ>\<^sub>c left_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X)) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>"
    using comp_associative2[OF id1x_type left_proj_type bw_type] by simp
  have s11: "(right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X)) \<circ>\<^sub>c left_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X)
      = left_coproj(X, X) \<circ>\<^sub>c right_cart_proj(\<one>, X)"
    using left_coproj_cfunc_bowtie_prod[OF rp_type rp_type] by simp
  have s12: "(left_coproj(X, X) \<circ>\<^sub>c right_cart_proj(\<one>, X)) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>
      = left_coproj(X, X) \<circ>\<^sub>c (right_cart_proj(\<one>, X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>)"
    using comp_associative2[OF id1x_type rp_type left_proj_type] by simp
  have s13: "right_cart_proj(\<one>, X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle> = x" using right_cart_proj_cfunc_prod[OF id1_type x_type] by simp
  show ?thesis using s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 by simp
qed

lemma false_case:
  assumes x_type: "x \<in>\<^sub>c X" and f_type: "f : X \<rightarrow> \<Omega>" and false_case: "f \<circ>\<^sub>c x = \<f>"
  shows "cases(f) \<circ>\<^sub>c x = right_coproj(X, X) \<circ>\<^sub>c x"
proof -
  have cb_type: "case_bool \<circ>\<^sub>c f : X \<rightarrow> \<one> \<Coprod> \<one>" using f_type case_bool_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have pair_type: "\<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> : X \<rightarrow> (\<one> \<Coprod> \<one>) \<times>\<^sub>c X" using cb_type idX_type cfunc_prod_type by auto
  have dpr_type: "dist_prod_coprod_right(\<one>, \<one>, X) : (\<one> \<Coprod> \<one>) \<times>\<^sub>c X \<rightarrow> (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X)"
    by (rule dist_prod_coprod_right_type)
  have rp_type: "right_cart_proj(\<one>, X) : \<one> \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)
  have bw_type: "right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X) : (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X) \<rightarrow> X \<Coprod> X"
    using cfunc_bowtie_prod_type[OF rp_type rp_type] by simp
  have inner_type: "dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> : X \<rightarrow> (\<one> \<times>\<^sub>c X) \<Coprod> (\<one> \<times>\<^sub>c X)"
    using comp_type[OF pair_type dpr_type] by simp
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have id1x_type: "\<langle>id(\<one>), x\<rangle> \<in>\<^sub>c \<one> \<times>\<^sub>c X" using id1_type x_type cfunc_prod_type by auto

  have s1: "cases(f) \<circ>\<^sub>c x
      = ((right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X))
          \<circ>\<^sub>c (dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>)) \<circ>\<^sub>c x"
    unfolding cases_def2[OF f_type] by simp
  have s2: "((right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X))
        \<circ>\<^sub>c (dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>)) \<circ>\<^sub>c x
      = (right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X))
          \<circ>\<^sub>c ((dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>) \<circ>\<^sub>c x)"
    using comp_associative2[OF x_type inner_type bw_type] by simp
  have s3: "(dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle>) \<circ>\<^sub>c x
      = dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c (\<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> \<circ>\<^sub>c x)"
    using comp_associative2[OF x_type pair_type dpr_type] by simp
  have s4: "\<langle>case_bool \<circ>\<^sub>c f, id(X)\<rangle> \<circ>\<^sub>c x = \<langle>(case_bool \<circ>\<^sub>c f) \<circ>\<^sub>c x, id(X) \<circ>\<^sub>c x\<rangle>"
    using cfunc_prod_comp[OF x_type cb_type idX_type] by simp
  have s5: "(case_bool \<circ>\<^sub>c f) \<circ>\<^sub>c x = case_bool \<circ>\<^sub>c (f \<circ>\<^sub>c x)"
    using comp_associative2[OF x_type f_type case_bool_type] by simp
  have s6: "case_bool \<circ>\<^sub>c (f \<circ>\<^sub>c x) = case_bool \<circ>\<^sub>c \<f>" using false_case by simp
  have s7: "case_bool \<circ>\<^sub>c \<f> = right_coproj(\<one>, \<one>)" by (rule case_bool_false)
  have s8: "id(X) \<circ>\<^sub>c x = x" using id_left_unit2[OF x_type] by simp
  have s9: "dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>right_coproj(\<one>, \<one>), x\<rangle> = right_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>"
  proof -
    have h_eq: "dist_prod_coprod_right(\<one>, \<one>, X) \<circ>\<^sub>c \<langle>right_coproj(\<one>, \<one>) \<circ>\<^sub>c id(\<one>), x\<rangle>
        = right_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>"
      using dist_prod_coprod_right_ap_right[OF id1_type x_type] by simp
    have id1_eq: "right_coproj(\<one>, \<one>) \<circ>\<^sub>c id(\<one>) = right_coproj(\<one>, \<one>)" using id_right_unit2[OF right_proj_type] by simp
    show ?thesis using h_eq id1_eq by simp
  qed
  have s10: "(right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X)) \<circ>\<^sub>c (right_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>)
      = ((right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X)) \<circ>\<^sub>c right_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X)) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>"
    using comp_associative2[OF id1x_type right_proj_type bw_type] by simp
  have s11: "(right_cart_proj(\<one>, X) \<bowtie>\<^sub>f right_cart_proj(\<one>, X)) \<circ>\<^sub>c right_coproj(\<one> \<times>\<^sub>c X, \<one> \<times>\<^sub>c X)
      = right_coproj(X, X) \<circ>\<^sub>c right_cart_proj(\<one>, X)"
    using right_coproj_cfunc_bowtie_prod[OF rp_type rp_type] by simp
  have s12: "(right_coproj(X, X) \<circ>\<^sub>c right_cart_proj(\<one>, X)) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>
      = right_coproj(X, X) \<circ>\<^sub>c (right_cart_proj(\<one>, X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle>)"
    using comp_associative2[OF id1x_type rp_type right_proj_type] by simp
  have s13: "right_cart_proj(\<one>, X) \<circ>\<^sub>c \<langle>id(\<one>), x\<rangle> = x" using right_cart_proj_cfunc_prod[OF id1_type x_type] by simp
  show ?thesis using s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 by simp
qed

subsection \<open>Coproduct Set Properties\<close>

lemma coproduct_commutes:
  "A \<Coprod> B \<cong> B \<Coprod> A"
proof -
  have f_type: "right_coproj(A, B) \<amalg> left_coproj(A, B) : B \<Coprod> A \<rightarrow> A \<Coprod> B"
    using cfunc_coprod_type[OF right_proj_type left_proj_type] by simp
  have g_type: "right_coproj(B, A) \<amalg> left_coproj(B, A) : A \<Coprod> B \<rightarrow> B \<Coprod> A"
    using cfunc_coprod_type[OF right_proj_type left_proj_type] by simp
  have id_AB: "(right_coproj(A, B) \<amalg> left_coproj(A, B)) \<circ>\<^sub>c (right_coproj(B, A) \<amalg> left_coproj(B, A)) = id(A \<Coprod> B)"
  proof -
    have s1: "(right_coproj(A, B) \<amalg> left_coproj(A, B)) \<circ>\<^sub>c (right_coproj(B, A) \<amalg> left_coproj(B, A))
        = ((right_coproj(A, B) \<amalg> left_coproj(A, B)) \<circ>\<^sub>c right_coproj(B, A))
            \<amalg> ((right_coproj(A, B) \<amalg> left_coproj(A, B)) \<circ>\<^sub>c left_coproj(B, A))"
      using cfunc_coprod_comp[OF f_type right_proj_type left_proj_type] by simp
    have s2: "(right_coproj(A, B) \<amalg> left_coproj(A, B)) \<circ>\<^sub>c right_coproj(B, A) = left_coproj(A, B)"
      using right_coproj_cfunc_coprod[OF right_proj_type left_proj_type] by simp
    have s3: "(right_coproj(A, B) \<amalg> left_coproj(A, B)) \<circ>\<^sub>c left_coproj(B, A) = right_coproj(A, B)"
      using left_coproj_cfunc_coprod[OF right_proj_type left_proj_type] by simp
    have s4: "left_coproj(A, B) \<amalg> right_coproj(A, B) = id(A \<Coprod> B)" using id_coprod by simp
    show ?thesis using s1 s2 s3 s4 by simp
  qed
  have id_BA: "(right_coproj(B, A) \<amalg> left_coproj(B, A)) \<circ>\<^sub>c (right_coproj(A, B) \<amalg> left_coproj(A, B)) = id(B \<Coprod> A)"
  proof -
    have s1: "(right_coproj(B, A) \<amalg> left_coproj(B, A)) \<circ>\<^sub>c (right_coproj(A, B) \<amalg> left_coproj(A, B))
        = ((right_coproj(B, A) \<amalg> left_coproj(B, A)) \<circ>\<^sub>c right_coproj(A, B))
            \<amalg> ((right_coproj(B, A) \<amalg> left_coproj(B, A)) \<circ>\<^sub>c left_coproj(A, B))"
      using cfunc_coprod_comp[OF g_type right_proj_type left_proj_type] by simp
    have s2: "(right_coproj(B, A) \<amalg> left_coproj(B, A)) \<circ>\<^sub>c right_coproj(A, B) = left_coproj(B, A)"
      using right_coproj_cfunc_coprod[OF right_proj_type left_proj_type] by simp
    have s3: "(right_coproj(B, A) \<amalg> left_coproj(B, A)) \<circ>\<^sub>c left_coproj(A, B) = right_coproj(B, A)"
      using left_coproj_cfunc_coprod[OF right_proj_type left_proj_type] by simp
    have s4: "left_coproj(B, A) \<amalg> right_coproj(B, A) = id(B \<Coprod> A)" using id_coprod by simp
    show ?thesis using s1 s2 s3 s4 by simp
  qed
  have g_iso: "isomorphism(right_coproj(B, A) \<amalg> left_coproj(B, A))"
    using isomorphism_def3[OF g_type] f_type id_AB id_BA by auto
  show ?thesis unfolding is_isomorphic_def using g_type g_iso by auto
qed

lemma coproduct_associates:
  "A \<Coprod> (B \<Coprod> C) \<cong> (A \<Coprod> B) \<Coprod> C"
proof -
  define q where q_def: "q = left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c right_coproj(A, B)"
  have q_type: "q : B \<rightarrow> (A \<Coprod> B) \<Coprod> C" unfolding q_def using comp_type[OF right_proj_type left_proj_type] by simp
  define f where f_def: "f = q \<amalg> right_coproj(A \<Coprod> B, C)"
  have f_type: "f : B \<Coprod> C \<rightarrow> (A \<Coprod> B) \<Coprod> C" unfolding f_def using cfunc_coprod_type[OF q_type right_proj_type] by simp
  have f_prop1: "f \<circ>\<^sub>c left_coproj(B, C) = q"
    unfolding f_def using left_coproj_cfunc_coprod[OF q_type right_proj_type] by simp
  have f_prop2: "f \<circ>\<^sub>c right_coproj(B, C) = right_coproj(A \<Coprod> B, C)"
    unfolding f_def using right_coproj_cfunc_coprod[OF q_type right_proj_type] by simp

  define m where m_def: "m = left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c left_coproj(A, B)"
  have m_type: "m : A \<rightarrow> (A \<Coprod> B) \<Coprod> C" unfolding m_def using comp_type[OF left_proj_type left_proj_type] by simp
  define g where g_def: "g = m \<amalg> f"
  have g_type: "g : A \<Coprod> (B \<Coprod> C) \<rightarrow> (A \<Coprod> B) \<Coprod> C" unfolding g_def using cfunc_coprod_type[OF m_type f_type] by simp
  have g_prop1: "g \<circ>\<^sub>c left_coproj(A, B \<Coprod> C) = m"
    unfolding g_def using left_coproj_cfunc_coprod[OF m_type f_type] by simp
  have g_prop2: "g \<circ>\<^sub>c right_coproj(A, B \<Coprod> C) = f"
    unfolding g_def using right_coproj_cfunc_coprod[OF m_type f_type] by simp

  define p where p_def: "p = right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c left_coproj(B, C)"
  have p_type: "p : B \<rightarrow> A \<Coprod> (B \<Coprod> C)" unfolding p_def using comp_type[OF left_proj_type right_proj_type] by simp
  define h where h_def: "h = left_coproj(A, B \<Coprod> C) \<amalg> p"
  have h_type: "h : A \<Coprod> B \<rightarrow> A \<Coprod> (B \<Coprod> C)" unfolding h_def using cfunc_coprod_type[OF left_proj_type p_type] by simp
  have h_prop1: "h \<circ>\<^sub>c left_coproj(A, B) = left_coproj(A, B \<Coprod> C)"
    unfolding h_def using left_coproj_cfunc_coprod[OF left_proj_type p_type] by simp
  have h_prop2: "h \<circ>\<^sub>c right_coproj(A, B) = p"
    unfolding h_def using right_coproj_cfunc_coprod[OF left_proj_type p_type] by simp

  define j where j_def: "j = right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c right_coproj(B, C)"
  have j_type: "j : C \<rightarrow> A \<Coprod> (B \<Coprod> C)" unfolding j_def using comp_type[OF right_proj_type right_proj_type] by simp
  define k where k_def: "k = h \<amalg> j"
  have k_type: "k : (A \<Coprod> B) \<Coprod> C \<rightarrow> A \<Coprod> (B \<Coprod> C)" unfolding k_def using cfunc_coprod_type[OF h_type j_type] by simp
  have k_prop1: "k \<circ>\<^sub>c left_coproj(A \<Coprod> B, C) = h"
    unfolding k_def using left_coproj_cfunc_coprod[OF h_type j_type] by simp
  have k_prop2: "k \<circ>\<^sub>c right_coproj(A \<Coprod> B, C) = j"
    unfolding k_def using right_coproj_cfunc_coprod[OF h_type j_type] by simp

  have kg_type: "k \<circ>\<^sub>c g : A \<Coprod> (B \<Coprod> C) \<rightarrow> A \<Coprod> (B \<Coprod> C)" using g_type k_type comp_type by blast
  have gk_type: "g \<circ>\<^sub>c k : (A \<Coprod> B) \<Coprod> C \<rightarrow> (A \<Coprod> B) \<Coprod> C" using k_type g_type comp_type by blast

  have fact1: "(k \<circ>\<^sub>c g) \<circ>\<^sub>c left_coproj(A, B \<Coprod> C) = left_coproj(A, B \<Coprod> C)"
  proof -
    have t1: "(k \<circ>\<^sub>c g) \<circ>\<^sub>c left_coproj(A, B \<Coprod> C) = k \<circ>\<^sub>c (g \<circ>\<^sub>c left_coproj(A, B \<Coprod> C))"
      using comp_associative2[OF left_proj_type g_type k_type] by simp
    have t2: "k \<circ>\<^sub>c (g \<circ>\<^sub>c left_coproj(A, B \<Coprod> C)) = k \<circ>\<^sub>c m" using g_prop1 by simp
    have t3: "k \<circ>\<^sub>c m = k \<circ>\<^sub>c (left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c left_coproj(A, B))" using m_def by simp
    have t4: "k \<circ>\<^sub>c (left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c left_coproj(A, B)) = (k \<circ>\<^sub>c left_coproj(A \<Coprod> B, C)) \<circ>\<^sub>c left_coproj(A, B)"
      using comp_associative2[OF left_proj_type left_proj_type k_type] by simp
    have t5: "(k \<circ>\<^sub>c left_coproj(A \<Coprod> B, C)) \<circ>\<^sub>c left_coproj(A, B) = h \<circ>\<^sub>c left_coproj(A, B)" using k_prop1 by simp
    have t6: "h \<circ>\<^sub>c left_coproj(A, B) = left_coproj(A, B \<Coprod> C)" using h_prop1 by simp
    show ?thesis using t1 t2 t3 t4 t5 t6 by simp
  qed

  have fact4: "(k \<circ>\<^sub>c g) \<circ>\<^sub>c right_coproj(A, B \<Coprod> C) = right_coproj(A, B \<Coprod> C)"
  proof -
    have t1: "(k \<circ>\<^sub>c g) \<circ>\<^sub>c right_coproj(A, B \<Coprod> C) = k \<circ>\<^sub>c (g \<circ>\<^sub>c right_coproj(A, B \<Coprod> C))"
      using comp_associative2[OF right_proj_type g_type k_type] by simp
    have t2: "k \<circ>\<^sub>c (g \<circ>\<^sub>c right_coproj(A, B \<Coprod> C)) = k \<circ>\<^sub>c f" using g_prop2 by simp

    have kf_type: "k \<circ>\<^sub>c f : B \<Coprod> C \<rightarrow> A \<Coprod> (B \<Coprod> C)" using f_type k_type comp_type by blast
    have u1: "(k \<circ>\<^sub>c f) \<circ>\<^sub>c left_coproj(B, C) = k \<circ>\<^sub>c (f \<circ>\<^sub>c left_coproj(B, C))"
      using comp_associative2[OF left_proj_type f_type k_type] by simp
    have u2: "k \<circ>\<^sub>c (f \<circ>\<^sub>c left_coproj(B, C)) = k \<circ>\<^sub>c q" using f_prop1 by simp
    have u3: "k \<circ>\<^sub>c q = k \<circ>\<^sub>c (left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c right_coproj(A, B))" using q_def by simp
    have u4: "k \<circ>\<^sub>c (left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c right_coproj(A, B)) = (k \<circ>\<^sub>c left_coproj(A \<Coprod> B, C)) \<circ>\<^sub>c right_coproj(A, B)"
      using comp_associative2[OF right_proj_type left_proj_type k_type] by simp
    have u5: "(k \<circ>\<^sub>c left_coproj(A \<Coprod> B, C)) \<circ>\<^sub>c right_coproj(A, B) = h \<circ>\<^sub>c right_coproj(A, B)" using k_prop1 by simp
    have u6: "h \<circ>\<^sub>c right_coproj(A, B) = p" using h_prop2 by simp
    have u7: "p = right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c left_coproj(B, C)" using p_def by simp
    have left_agree: "(k \<circ>\<^sub>c f) \<circ>\<^sub>c left_coproj(B, C) = right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c left_coproj(B, C)"
      using u1 u2 u3 u4 u5 u6 u7 by simp

    have v1: "(k \<circ>\<^sub>c f) \<circ>\<^sub>c right_coproj(B, C) = k \<circ>\<^sub>c (f \<circ>\<^sub>c right_coproj(B, C))"
      using comp_associative2[OF right_proj_type f_type k_type] by simp
    have v2: "k \<circ>\<^sub>c (f \<circ>\<^sub>c right_coproj(B, C)) = k \<circ>\<^sub>c right_coproj(A \<Coprod> B, C)" using f_prop2 by simp
    have v3: "k \<circ>\<^sub>c right_coproj(A \<Coprod> B, C) = j" using k_prop2 by simp
    have v4: "j = right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c right_coproj(B, C)" using j_def by simp
    have right_agree: "(k \<circ>\<^sub>c f) \<circ>\<^sub>c right_coproj(B, C) = right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c right_coproj(B, C)"
      using v1 v2 v3 v4 by simp

    have rc_type: "right_coproj(A, B \<Coprod> C) : B \<Coprod> C \<rightarrow> A \<Coprod> (B \<Coprod> C)" by (rule right_proj_type)
    have t3: "k \<circ>\<^sub>c f = right_coproj(A, B \<Coprod> C)"
      using coprod_eq[OF kf_type rc_type] left_agree right_agree by auto
    show ?thesis using t1 t2 t3 by simp
  qed

  have fact2: "(g \<circ>\<^sub>c k) \<circ>\<^sub>c left_coproj(A \<Coprod> B, C) = left_coproj(A \<Coprod> B, C)"
  proof -
    have t1: "(g \<circ>\<^sub>c k) \<circ>\<^sub>c left_coproj(A \<Coprod> B, C) = g \<circ>\<^sub>c (k \<circ>\<^sub>c left_coproj(A \<Coprod> B, C))"
      using comp_associative2[OF left_proj_type k_type g_type] by simp
    have t2: "g \<circ>\<^sub>c (k \<circ>\<^sub>c left_coproj(A \<Coprod> B, C)) = g \<circ>\<^sub>c h" using k_prop1 by simp

    have gh_type: "g \<circ>\<^sub>c h : A \<Coprod> B \<rightarrow> (A \<Coprod> B) \<Coprod> C" using h_type g_type comp_type by blast
    have u1: "(g \<circ>\<^sub>c h) \<circ>\<^sub>c left_coproj(A, B) = g \<circ>\<^sub>c (h \<circ>\<^sub>c left_coproj(A, B))"
      using comp_associative2[OF left_proj_type h_type g_type] by simp
    have u2: "g \<circ>\<^sub>c (h \<circ>\<^sub>c left_coproj(A, B)) = g \<circ>\<^sub>c left_coproj(A, B \<Coprod> C)" using h_prop1 by simp
    have u3: "g \<circ>\<^sub>c left_coproj(A, B \<Coprod> C) = m" using g_prop1 by simp
    have u4: "m = left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c left_coproj(A, B)" using m_def by simp
    have left_agree: "(g \<circ>\<^sub>c h) \<circ>\<^sub>c left_coproj(A, B) = left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c left_coproj(A, B)"
      using u1 u2 u3 u4 by simp

    have v1: "(g \<circ>\<^sub>c h) \<circ>\<^sub>c right_coproj(A, B) = g \<circ>\<^sub>c (h \<circ>\<^sub>c right_coproj(A, B))"
      using comp_associative2[OF right_proj_type h_type g_type] by simp
    have v2: "g \<circ>\<^sub>c (h \<circ>\<^sub>c right_coproj(A, B)) = g \<circ>\<^sub>c p" using h_prop2 by simp
    have v3: "p = right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c left_coproj(B, C)" using p_def by simp
    have v4: "g \<circ>\<^sub>c (right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c left_coproj(B, C)) = (g \<circ>\<^sub>c right_coproj(A, B \<Coprod> C)) \<circ>\<^sub>c left_coproj(B, C)"
      using comp_associative2[OF left_proj_type right_proj_type g_type] by simp
    have v5: "(g \<circ>\<^sub>c right_coproj(A, B \<Coprod> C)) \<circ>\<^sub>c left_coproj(B, C) = f \<circ>\<^sub>c left_coproj(B, C)" using g_prop2 by simp
    have v6: "f \<circ>\<^sub>c left_coproj(B, C) = q" using f_prop1 by simp
    have v7: "q = left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c right_coproj(A, B)" using q_def by simp
    have right_agree: "(g \<circ>\<^sub>c h) \<circ>\<^sub>c right_coproj(A, B) = left_coproj(A \<Coprod> B, C) \<circ>\<^sub>c right_coproj(A, B)"
      using v1 v2 v3 v4 v5 v6 v7 by simp

    have lc_type: "left_coproj(A \<Coprod> B, C) : A \<Coprod> B \<rightarrow> (A \<Coprod> B) \<Coprod> C" by (rule left_proj_type)
    have t3: "g \<circ>\<^sub>c h = left_coproj(A \<Coprod> B, C)"
      using coprod_eq[OF gh_type lc_type] left_agree right_agree by auto
    show ?thesis using t1 t2 t3 by simp
  qed

  have fact3: "(g \<circ>\<^sub>c k) \<circ>\<^sub>c right_coproj(A \<Coprod> B, C) = right_coproj(A \<Coprod> B, C)"
  proof -
    have t1: "(g \<circ>\<^sub>c k) \<circ>\<^sub>c right_coproj(A \<Coprod> B, C) = g \<circ>\<^sub>c (k \<circ>\<^sub>c right_coproj(A \<Coprod> B, C))"
      using comp_associative2[OF right_proj_type k_type g_type] by simp
    have t2: "g \<circ>\<^sub>c (k \<circ>\<^sub>c right_coproj(A \<Coprod> B, C)) = g \<circ>\<^sub>c j" using k_prop2 by simp
    have t3: "g \<circ>\<^sub>c j = g \<circ>\<^sub>c (right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c right_coproj(B, C))" using j_def by simp
    have t4: "g \<circ>\<^sub>c (right_coproj(A, B \<Coprod> C) \<circ>\<^sub>c right_coproj(B, C)) = (g \<circ>\<^sub>c right_coproj(A, B \<Coprod> C)) \<circ>\<^sub>c right_coproj(B, C)"
      using comp_associative2[OF right_proj_type right_proj_type g_type] by simp
    have t5: "(g \<circ>\<^sub>c right_coproj(A, B \<Coprod> C)) \<circ>\<^sub>c right_coproj(B, C) = f \<circ>\<^sub>c right_coproj(B, C)" using g_prop2 by simp
    have t6: "f \<circ>\<^sub>c right_coproj(B, C) = right_coproj(A \<Coprod> B, C)" using f_prop2 by simp
    show ?thesis using t1 t2 t3 t4 t5 t6 by simp
  qed

  have fact5: "k \<circ>\<^sub>c g = id(A \<Coprod> (B \<Coprod> C))"
  proof -
    have kg_eq: "k \<circ>\<^sub>c g = left_coproj(A, B \<Coprod> C) \<amalg> right_coproj(A, B \<Coprod> C)"
      using cfunc_coprod_unique[OF left_proj_type right_proj_type kg_type fact1 fact4] by simp
    have id_eq: "id(A \<Coprod> (B \<Coprod> C)) = left_coproj(A, B \<Coprod> C) \<amalg> right_coproj(A, B \<Coprod> C)" using id_coprod by simp
    show ?thesis using kg_eq id_eq by simp
  qed

  have fact6: "g \<circ>\<^sub>c k = id((A \<Coprod> B) \<Coprod> C)"
  proof -
    have gk_eq: "g \<circ>\<^sub>c k = left_coproj(A \<Coprod> B, C) \<amalg> right_coproj(A \<Coprod> B, C)"
      using cfunc_coprod_unique[OF left_proj_type right_proj_type gk_type fact2 fact3] by simp
    have id_eq: "id((A \<Coprod> B) \<Coprod> C) = left_coproj(A \<Coprod> B, C) \<amalg> right_coproj(A \<Coprod> B, C)" using id_coprod by simp
    show ?thesis using gk_eq id_eq by simp
  qed

  have g_iso: "isomorphism(g)" using isomorphism_def3[OF g_type] k_type fact5 fact6 by auto
  show ?thesis unfolding is_isomorphic_def using g_type g_iso by auto
qed

text \<open>The lemma below corresponds to Proposition 2.5.10.\<close>
lemma product_distribute_over_coproduct_left:
  "A \<times>\<^sub>c (X \<Coprod> Y) \<cong> (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y)"
  using prod_distribute_coprod by simp

lemma prod_pres_iso:
  assumes AC: "A \<cong> C" and BD: "B \<cong> D"
  shows "A \<times>\<^sub>c B \<cong> C \<times>\<^sub>c D"
proof -
  obtain f where f_type: "f : A \<rightarrow> C" and f_iso: "isomorphism(f)" using AC unfolding is_isomorphic_def by auto
  obtain g where g_type: "g : B \<rightarrow> D" and g_iso: "isomorphism(g)" using BD unfolding is_isomorphic_def by auto
  have f_spec: "f\<^bold>\<inverse> : codomain(f) \<rightarrow> domain(f) \<and> f\<^bold>\<inverse> \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c f\<^bold>\<inverse> = id(codomain(f))"
    using inverse_def2[OF f_iso] by simp
  have g_spec: "g\<^bold>\<inverse> : codomain(g) \<rightarrow> domain(g) \<and> g\<^bold>\<inverse> \<circ>\<^sub>c g = id(domain(g)) \<and> g \<circ>\<^sub>c g\<^bold>\<inverse> = id(codomain(g))"
    using inverse_def2[OF g_iso] by simp
  have dom_f: "domain(f) = A" using f_type unfolding cfunc_type_def by auto
  have cod_f: "codomain(f) = C" using f_type unfolding cfunc_type_def by auto
  have dom_g: "domain(g) = B" using g_type unfolding cfunc_type_def by auto
  have cod_g: "codomain(g) = D" using g_type unfolding cfunc_type_def by auto
  have finv_type: "f\<^bold>\<inverse> : C \<rightarrow> A" using f_spec dom_f cod_f by simp
  have ginv_type: "g\<^bold>\<inverse> : D \<rightarrow> B" using g_spec dom_g cod_g by simp
  have finv_f: "f\<^bold>\<inverse> \<circ>\<^sub>c f = id(A)" using f_spec dom_f by simp
  have f_finv: "f \<circ>\<^sub>c f\<^bold>\<inverse> = id(C)" using f_spec cod_f by simp
  have ginv_g: "g\<^bold>\<inverse> \<circ>\<^sub>c g = id(B)" using g_spec dom_g by simp
  have g_ginv: "g \<circ>\<^sub>c g\<^bold>\<inverse> = id(D)" using g_spec cod_g by simp

  have fg_type: "f \<times>\<^sub>f g : A \<times>\<^sub>c B \<rightarrow> C \<times>\<^sub>c D" using cfunc_cross_prod_type[OF f_type g_type] by simp
  have fginv_type: "f\<^bold>\<inverse> \<times>\<^sub>f g\<^bold>\<inverse> : C \<times>\<^sub>c D \<rightarrow> A \<times>\<^sub>c B" using cfunc_cross_prod_type[OF finv_type ginv_type] by simp

  have left_eq: "(f\<^bold>\<inverse> \<times>\<^sub>f g\<^bold>\<inverse>) \<circ>\<^sub>c (f \<times>\<^sub>f g) = id(A \<times>\<^sub>c B)"
  proof -
    have s1: "(f\<^bold>\<inverse> \<times>\<^sub>f g\<^bold>\<inverse>) \<circ>\<^sub>c (f \<times>\<^sub>f g) = (f\<^bold>\<inverse> \<circ>\<^sub>c f) \<times>\<^sub>f (g\<^bold>\<inverse> \<circ>\<^sub>c g)"
      using cfunc_cross_prod_comp_cfunc_cross_prod[OF f_type g_type finv_type ginv_type] by simp
    have s2: "(f\<^bold>\<inverse> \<circ>\<^sub>c f) \<times>\<^sub>f (g\<^bold>\<inverse> \<circ>\<^sub>c g) = id(A) \<times>\<^sub>f id(B)" using finv_f ginv_g by simp
    have s3: "id(A) \<times>\<^sub>f id(B) = id(A \<times>\<^sub>c B)" using id_cross_prod by simp
    show ?thesis using s1 s2 s3 by simp
  qed
  have right_eq: "(f \<times>\<^sub>f g) \<circ>\<^sub>c (f\<^bold>\<inverse> \<times>\<^sub>f g\<^bold>\<inverse>) = id(C \<times>\<^sub>c D)"
  proof -
    have s1: "(f \<times>\<^sub>f g) \<circ>\<^sub>c (f\<^bold>\<inverse> \<times>\<^sub>f g\<^bold>\<inverse>) = (f \<circ>\<^sub>c f\<^bold>\<inverse>) \<times>\<^sub>f (g \<circ>\<^sub>c g\<^bold>\<inverse>)"
      using cfunc_cross_prod_comp_cfunc_cross_prod[OF finv_type ginv_type f_type g_type] by simp
    have s2: "(f \<circ>\<^sub>c f\<^bold>\<inverse>) \<times>\<^sub>f (g \<circ>\<^sub>c g\<^bold>\<inverse>) = id(C) \<times>\<^sub>f id(D)" using f_finv g_ginv by simp
    have s3: "id(C) \<times>\<^sub>f id(D) = id(C \<times>\<^sub>c D)" using id_cross_prod by simp
    show ?thesis using s1 s2 s3 by simp
  qed
  have fg_iso: "isomorphism(f \<times>\<^sub>f g)" unfolding isomorphism_def3[OF fg_type] using fginv_type left_eq right_eq by auto
  show ?thesis unfolding is_isomorphic_def using fg_type fg_iso by auto
qed

lemma coprod_pres_iso:
  assumes AC: "A \<cong> C" and BD: "B \<cong> D"
  shows "A \<Coprod> B \<cong> C \<Coprod> D"
proof -
  obtain f where f_type: "f : A \<rightarrow> C" and f_iso: "isomorphism(f)" using AC unfolding is_isomorphic_def by auto
  obtain g where g_type: "g : B \<rightarrow> D" and g_iso: "isomorphism(g)" using BD unfolding is_isomorphic_def by auto
  have f_spec: "f\<^bold>\<inverse> : codomain(f) \<rightarrow> domain(f) \<and> f\<^bold>\<inverse> \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c f\<^bold>\<inverse> = id(codomain(f))"
    using inverse_def2[OF f_iso] by simp
  have g_spec: "g\<^bold>\<inverse> : codomain(g) \<rightarrow> domain(g) \<and> g\<^bold>\<inverse> \<circ>\<^sub>c g = id(domain(g)) \<and> g \<circ>\<^sub>c g\<^bold>\<inverse> = id(codomain(g))"
    using inverse_def2[OF g_iso] by simp
  have dom_f: "domain(f) = A" using f_type unfolding cfunc_type_def by auto
  have cod_f: "codomain(f) = C" using f_type unfolding cfunc_type_def by auto
  have dom_g: "domain(g) = B" using g_type unfolding cfunc_type_def by auto
  have cod_g: "codomain(g) = D" using g_type unfolding cfunc_type_def by auto
  have finv_type: "f\<^bold>\<inverse> : C \<rightarrow> A" using f_spec dom_f cod_f by simp
  have ginv_type: "g\<^bold>\<inverse> : D \<rightarrow> B" using g_spec dom_g cod_g by simp
  have finv_f: "f\<^bold>\<inverse> \<circ>\<^sub>c f = id(A)" using f_spec dom_f by simp
  have f_finv: "f \<circ>\<^sub>c f\<^bold>\<inverse> = id(C)" using f_spec cod_f by simp
  have ginv_g: "g\<^bold>\<inverse> \<circ>\<^sub>c g = id(B)" using g_spec dom_g by simp
  have g_ginv: "g \<circ>\<^sub>c g\<^bold>\<inverse> = id(D)" using g_spec cod_g by simp

  define \<phi> where phi_def: "\<phi> = (left_coproj(C, D) \<circ>\<^sub>c f) \<amalg> (right_coproj(C, D) \<circ>\<^sub>c g)"
  define \<psi> where psi_def: "\<psi> = (left_coproj(A, B) \<circ>\<^sub>c f\<^bold>\<inverse>) \<amalg> (right_coproj(A, B) \<circ>\<^sub>c g\<^bold>\<inverse>)"

  have lcf_type: "left_coproj(C, D) \<circ>\<^sub>c f : A \<rightarrow> C \<Coprod> D" using f_type left_proj_type comp_type by blast
  have rcg_type: "right_coproj(C, D) \<circ>\<^sub>c g : B \<rightarrow> C \<Coprod> D" using g_type right_proj_type comp_type by blast
  have phi_type: "\<phi> : A \<Coprod> B \<rightarrow> C \<Coprod> D" unfolding phi_def using cfunc_coprod_type[OF lcf_type rcg_type] by simp
  have phi_left: "\<phi> \<circ>\<^sub>c left_coproj(A, B) = left_coproj(C, D) \<circ>\<^sub>c f"
    unfolding phi_def using left_coproj_cfunc_coprod[OF lcf_type rcg_type] by simp
  have phi_right: "\<phi> \<circ>\<^sub>c right_coproj(A, B) = right_coproj(C, D) \<circ>\<^sub>c g"
    unfolding phi_def using right_coproj_cfunc_coprod[OF lcf_type rcg_type] by simp

  have lcfinv_type: "left_coproj(A, B) \<circ>\<^sub>c f\<^bold>\<inverse> : C \<rightarrow> A \<Coprod> B" using finv_type left_proj_type comp_type by blast
  have rcginv_type: "right_coproj(A, B) \<circ>\<^sub>c g\<^bold>\<inverse> : D \<rightarrow> A \<Coprod> B" using ginv_type right_proj_type comp_type by blast
  have psi_type: "\<psi> : C \<Coprod> D \<rightarrow> A \<Coprod> B" unfolding psi_def using cfunc_coprod_type[OF lcfinv_type rcginv_type] by simp
  have psi_left: "\<psi> \<circ>\<^sub>c left_coproj(C, D) = left_coproj(A, B) \<circ>\<^sub>c f\<^bold>\<inverse>"
    unfolding psi_def using left_coproj_cfunc_coprod[OF lcfinv_type rcginv_type] by simp
  have psi_right: "\<psi> \<circ>\<^sub>c right_coproj(C, D) = right_coproj(A, B) \<circ>\<^sub>c g\<^bold>\<inverse>"
    unfolding psi_def using right_coproj_cfunc_coprod[OF lcfinv_type rcginv_type] by simp

  have psiphi_type: "\<psi> \<circ>\<^sub>c \<phi> : A \<Coprod> B \<rightarrow> A \<Coprod> B" using phi_type psi_type comp_type by blast
  have phipsi_type: "\<phi> \<circ>\<^sub>c \<psi> : C \<Coprod> D \<rightarrow> C \<Coprod> D" using psi_type phi_type comp_type by blast

  have fact1: "(\<psi> \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c left_coproj(A, B) = left_coproj(A, B)"
  proof -
    have t1: "(\<psi> \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c left_coproj(A, B) = \<psi> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c left_coproj(A, B))"
      using comp_associative2[OF left_proj_type phi_type psi_type] by simp
    have t2: "\<psi> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c left_coproj(A, B)) = \<psi> \<circ>\<^sub>c (left_coproj(C, D) \<circ>\<^sub>c f)" using phi_left by simp
    have t3: "\<psi> \<circ>\<^sub>c (left_coproj(C, D) \<circ>\<^sub>c f) = (\<psi> \<circ>\<^sub>c left_coproj(C, D)) \<circ>\<^sub>c f"
      using comp_associative2[OF f_type left_proj_type psi_type] by simp
    have t4: "(\<psi> \<circ>\<^sub>c left_coproj(C, D)) \<circ>\<^sub>c f = (left_coproj(A, B) \<circ>\<^sub>c f\<^bold>\<inverse>) \<circ>\<^sub>c f" using psi_left by simp
    have t5: "(left_coproj(A, B) \<circ>\<^sub>c f\<^bold>\<inverse>) \<circ>\<^sub>c f = left_coproj(A, B) \<circ>\<^sub>c (f\<^bold>\<inverse> \<circ>\<^sub>c f)"
      using comp_associative2[OF f_type finv_type left_proj_type] by simp
    have t6: "left_coproj(A, B) \<circ>\<^sub>c (f\<^bold>\<inverse> \<circ>\<^sub>c f) = left_coproj(A, B) \<circ>\<^sub>c id(A)" using finv_f by simp
    have t7: "left_coproj(A, B) \<circ>\<^sub>c id(A) = left_coproj(A, B)" using id_right_unit2[OF left_proj_type] by simp
    show ?thesis using t1 t2 t3 t4 t5 t6 t7 by simp
  qed
  have fact2: "(\<psi> \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c right_coproj(A, B) = right_coproj(A, B)"
  proof -
    have t1: "(\<psi> \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c right_coproj(A, B) = \<psi> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c right_coproj(A, B))"
      using comp_associative2[OF right_proj_type phi_type psi_type] by simp
    have t2: "\<psi> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c right_coproj(A, B)) = \<psi> \<circ>\<^sub>c (right_coproj(C, D) \<circ>\<^sub>c g)" using phi_right by simp
    have t3: "\<psi> \<circ>\<^sub>c (right_coproj(C, D) \<circ>\<^sub>c g) = (\<psi> \<circ>\<^sub>c right_coproj(C, D)) \<circ>\<^sub>c g"
      using comp_associative2[OF g_type right_proj_type psi_type] by simp
    have t4: "(\<psi> \<circ>\<^sub>c right_coproj(C, D)) \<circ>\<^sub>c g = (right_coproj(A, B) \<circ>\<^sub>c g\<^bold>\<inverse>) \<circ>\<^sub>c g" using psi_right by simp
    have t5: "(right_coproj(A, B) \<circ>\<^sub>c g\<^bold>\<inverse>) \<circ>\<^sub>c g = right_coproj(A, B) \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c g)"
      using comp_associative2[OF g_type ginv_type right_proj_type] by simp
    have t6: "right_coproj(A, B) \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c g) = right_coproj(A, B) \<circ>\<^sub>c id(B)" using ginv_g by simp
    have t7: "right_coproj(A, B) \<circ>\<^sub>c id(B) = right_coproj(A, B)" using id_right_unit2[OF right_proj_type] by simp
    show ?thesis using t1 t2 t3 t4 t5 t6 t7 by simp
  qed
  have psiphi_eq: "\<psi> \<circ>\<^sub>c \<phi> = id(A \<Coprod> B)"
  proof -
    have e1: "\<psi> \<circ>\<^sub>c \<phi> = left_coproj(A, B) \<amalg> right_coproj(A, B)"
      using cfunc_coprod_unique[OF left_proj_type right_proj_type psiphi_type fact1 fact2] by simp
    have e2: "id(A \<Coprod> B) = left_coproj(A, B) \<amalg> right_coproj(A, B)" using id_coprod by simp
    show ?thesis using e1 e2 by simp
  qed

  have fact3: "(\<phi> \<circ>\<^sub>c \<psi>) \<circ>\<^sub>c left_coproj(C, D) = left_coproj(C, D)"
  proof -
    have t1: "(\<phi> \<circ>\<^sub>c \<psi>) \<circ>\<^sub>c left_coproj(C, D) = \<phi> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c left_coproj(C, D))"
      using comp_associative2[OF left_proj_type psi_type phi_type] by simp
    have t2: "\<phi> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c left_coproj(C, D)) = \<phi> \<circ>\<^sub>c (left_coproj(A, B) \<circ>\<^sub>c f\<^bold>\<inverse>)" using psi_left by simp
    have t3: "\<phi> \<circ>\<^sub>c (left_coproj(A, B) \<circ>\<^sub>c f\<^bold>\<inverse>) = (\<phi> \<circ>\<^sub>c left_coproj(A, B)) \<circ>\<^sub>c f\<^bold>\<inverse>"
      using comp_associative2[OF finv_type left_proj_type phi_type] by simp
    have t4: "(\<phi> \<circ>\<^sub>c left_coproj(A, B)) \<circ>\<^sub>c f\<^bold>\<inverse> = (left_coproj(C, D) \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse>" using phi_left by simp
    have t5: "(left_coproj(C, D) \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse> = left_coproj(C, D) \<circ>\<^sub>c (f \<circ>\<^sub>c f\<^bold>\<inverse>)"
      using comp_associative2[OF finv_type f_type left_proj_type] by simp
    have t6: "left_coproj(C, D) \<circ>\<^sub>c (f \<circ>\<^sub>c f\<^bold>\<inverse>) = left_coproj(C, D) \<circ>\<^sub>c id(C)" using f_finv by simp
    have t7: "left_coproj(C, D) \<circ>\<^sub>c id(C) = left_coproj(C, D)" using id_right_unit2[OF left_proj_type] by simp
    show ?thesis using t1 t2 t3 t4 t5 t6 t7 by simp
  qed
  have fact4: "(\<phi> \<circ>\<^sub>c \<psi>) \<circ>\<^sub>c right_coproj(C, D) = right_coproj(C, D)"
  proof -
    have t1: "(\<phi> \<circ>\<^sub>c \<psi>) \<circ>\<^sub>c right_coproj(C, D) = \<phi> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c right_coproj(C, D))"
      using comp_associative2[OF right_proj_type psi_type phi_type] by simp
    have t2: "\<phi> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c right_coproj(C, D)) = \<phi> \<circ>\<^sub>c (right_coproj(A, B) \<circ>\<^sub>c g\<^bold>\<inverse>)" using psi_right by simp
    have t3: "\<phi> \<circ>\<^sub>c (right_coproj(A, B) \<circ>\<^sub>c g\<^bold>\<inverse>) = (\<phi> \<circ>\<^sub>c right_coproj(A, B)) \<circ>\<^sub>c g\<^bold>\<inverse>"
      using comp_associative2[OF ginv_type right_proj_type phi_type] by simp
    have t4: "(\<phi> \<circ>\<^sub>c right_coproj(A, B)) \<circ>\<^sub>c g\<^bold>\<inverse> = (right_coproj(C, D) \<circ>\<^sub>c g) \<circ>\<^sub>c g\<^bold>\<inverse>" using phi_right by simp
    have t5: "(right_coproj(C, D) \<circ>\<^sub>c g) \<circ>\<^sub>c g\<^bold>\<inverse> = right_coproj(C, D) \<circ>\<^sub>c (g \<circ>\<^sub>c g\<^bold>\<inverse>)"
      using comp_associative2[OF ginv_type g_type right_proj_type] by simp
    have t6: "right_coproj(C, D) \<circ>\<^sub>c (g \<circ>\<^sub>c g\<^bold>\<inverse>) = right_coproj(C, D) \<circ>\<^sub>c id(D)" using g_ginv by simp
    have t7: "right_coproj(C, D) \<circ>\<^sub>c id(D) = right_coproj(C, D)" using id_right_unit2[OF right_proj_type] by simp
    show ?thesis using t1 t2 t3 t4 t5 t6 t7 by simp
  qed
  have phipsi_eq: "\<phi> \<circ>\<^sub>c \<psi> = id(C \<Coprod> D)"
  proof -
    have e1: "\<phi> \<circ>\<^sub>c \<psi> = left_coproj(C, D) \<amalg> right_coproj(C, D)"
      using cfunc_coprod_unique[OF left_proj_type right_proj_type phipsi_type fact3 fact4] by simp
    have e2: "id(C \<Coprod> D) = left_coproj(C, D) \<amalg> right_coproj(C, D)" using id_coprod by simp
    show ?thesis using e1 e2 by simp
  qed

  have phi_iso: "isomorphism(\<phi>)" unfolding isomorphism_def3[OF phi_type] using psi_type psiphi_eq phipsi_eq by auto
  show ?thesis unfolding is_isomorphic_def using phi_type phi_iso by auto
qed

lemma product_distribute_over_coproduct_right:
  "(A \<Coprod> B) \<times>\<^sub>c C \<cong> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
proof -
  have s1: "(A \<Coprod> B) \<times>\<^sub>c C \<cong> C \<times>\<^sub>c (A \<Coprod> B)" using product_commutes by simp
  have s2: "C \<times>\<^sub>c (A \<Coprod> B) \<cong> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)" using product_distribute_over_coproduct_left by simp
  have s12: "(A \<Coprod> B) \<times>\<^sub>c C \<cong> (C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B)"
    using mp[OF isomorphic_is_transitive conjI[OF s1 s2]] by simp
  have cA_AC: "C \<times>\<^sub>c A \<cong> A \<times>\<^sub>c C" using product_commutes by simp
  have cB_BC: "C \<times>\<^sub>c B \<cong> B \<times>\<^sub>c C" using product_commutes by simp
  have s3: "(C \<times>\<^sub>c A) \<Coprod> (C \<times>\<^sub>c B) \<cong> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
    using coprod_pres_iso[OF cA_AC cB_BC] by simp
  show ?thesis using mp[OF isomorphic_is_transitive conjI[OF s12 s3]] by simp
qed

lemma coproduct_with_self_iso:
  "X \<Coprod> X \<cong> X \<times>\<^sub>c \<Omega>"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have tb_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using terminal_func_type[of X] true_func_type comp_type by blast
  have fb_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using terminal_func_type[of X] false_func_type comp_type by blast
  have pt_type: "\<langle>id(X), \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c \<Omega>" using idX_type tb_type cfunc_prod_type by auto
  have pf_type: "\<langle>id(X), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c \<Omega>" using idX_type fb_type cfunc_prod_type by auto
  define \<rho> where rho_def: "\<rho> = \<langle>id(X), \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> \<langle>id(X), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
  have rho_type: "\<rho> : X \<Coprod> X \<rightarrow> X \<times>\<^sub>c \<Omega>" unfolding rho_def using cfunc_coprod_type[OF pt_type pf_type] by simp
  have rho_left: "\<rho> \<circ>\<^sub>c left_coproj(X, X) = \<langle>id(X), \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
    unfolding rho_def using left_coproj_cfunc_coprod[OF pt_type pf_type] by simp
  have rho_right: "\<rho> \<circ>\<^sub>c right_coproj(X, X) = \<langle>id(X), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
    unfolding rho_def using right_coproj_cfunc_coprod[OF pt_type pf_type] by simp

  have rho_at_left: "\<And>lx. lx \<in>\<^sub>c X \<Longrightarrow> \<rho> \<circ>\<^sub>c (left_coproj(X, X) \<circ>\<^sub>c lx) = \<langle>lx, \<t>\<rangle>"
  proof -
    fix lx assume lx_type: "lx \<in>\<^sub>c X"
    have s1: "\<rho> \<circ>\<^sub>c (left_coproj(X, X) \<circ>\<^sub>c lx) = (\<rho> \<circ>\<^sub>c left_coproj(X, X)) \<circ>\<^sub>c lx"
      using comp_associative2[OF lx_type left_proj_type rho_type] by simp
    have s2: "(\<rho> \<circ>\<^sub>c left_coproj(X, X)) \<circ>\<^sub>c lx = \<langle>id(X), \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c lx" using rho_left by simp
    have s3: "\<langle>id(X), \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c lx = \<langle>lx, \<t>\<rangle>" using cart_prod_extract_left[OF lx_type true_func_type] by simp
    show "\<rho> \<circ>\<^sub>c (left_coproj(X, X) \<circ>\<^sub>c lx) = \<langle>lx, \<t>\<rangle>" using s1 s2 s3 by simp
  qed
  have rho_at_right: "\<And>rx. rx \<in>\<^sub>c X \<Longrightarrow> \<rho> \<circ>\<^sub>c (right_coproj(X, X) \<circ>\<^sub>c rx) = \<langle>rx, \<f>\<rangle>"
  proof -
    fix rx assume rx_type: "rx \<in>\<^sub>c X"
    have s1: "\<rho> \<circ>\<^sub>c (right_coproj(X, X) \<circ>\<^sub>c rx) = (\<rho> \<circ>\<^sub>c right_coproj(X, X)) \<circ>\<^sub>c rx"
      using comp_associative2[OF rx_type right_proj_type rho_type] by simp
    have s2: "(\<rho> \<circ>\<^sub>c right_coproj(X, X)) \<circ>\<^sub>c rx = \<langle>id(X), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c rx" using rho_right by simp
    have s3: "\<langle>id(X), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c rx = \<langle>rx, \<f>\<rangle>" using cart_prod_extract_left[OF rx_type false_func_type] by simp
    show "\<rho> \<circ>\<^sub>c (right_coproj(X, X) \<circ>\<^sub>c rx) = \<langle>rx, \<f>\<rangle>" using s1 s2 s3 by simp
  qed

  have inj: "injective(\<rho>)"
    unfolding injective_def2[OF rho_type]
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c X \<Coprod> X \<and> y \<in>\<^sub>c X \<Coprod> X \<and> \<rho> \<circ>\<^sub>c x = \<rho> \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c X \<Coprod> X" and y_type: "y \<in>\<^sub>c X \<Coprod> X" and eqs: "\<rho> \<circ>\<^sub>c x = \<rho> \<circ>\<^sub>c y" by auto
    have x_disj: "(\<exists>lx. lx \<in>\<^sub>c X \<and> x = left_coproj(X, X) \<circ>\<^sub>c lx) \<or> (\<exists>rx. rx \<in>\<^sub>c X \<and> x = right_coproj(X, X) \<circ>\<^sub>c rx)"
      using coprojs_jointly_surj[OF x_type] by simp
    have y_disj: "(\<exists>ly. ly \<in>\<^sub>c X \<and> y = left_coproj(X, X) \<circ>\<^sub>c ly) \<or> (\<exists>ry. ry \<in>\<^sub>c X \<and> y = right_coproj(X, X) \<circ>\<^sub>c ry)"
      using coprojs_jointly_surj[OF y_type] by simp
    show "x = y"
    proof (cases "\<exists>lx. lx \<in>\<^sub>c X \<and> x = left_coproj(X, X) \<circ>\<^sub>c lx")
      case True
      then obtain lx where lx_type: "lx \<in>\<^sub>c X" and x_eq: "x = left_coproj(X, X) \<circ>\<^sub>c lx" by auto
      show "x = y"
      proof (cases "\<exists>ly. ly \<in>\<^sub>c X \<and> y = left_coproj(X, X) \<circ>\<^sub>c ly")
        case True
        then obtain ly where ly_type: "ly \<in>\<^sub>c X" and y_eq: "y = left_coproj(X, X) \<circ>\<^sub>c ly" by auto
        have px: "\<rho> \<circ>\<^sub>c x = \<langle>lx, \<t>\<rangle>" using x_eq rho_at_left[OF lx_type] by simp
        have py: "\<rho> \<circ>\<^sub>c y = \<langle>ly, \<t>\<rangle>" using y_eq rho_at_left[OF ly_type] by simp
        have "\<langle>lx, \<t>\<rangle> = \<langle>ly, \<t>\<rangle>" using eqs px py by simp
        then have "lx = ly \<and> \<t> = \<t>" using cart_prod_eq2[OF lx_type true_func_type ly_type true_func_type] by auto
        then show "x = y" using x_eq y_eq by simp
      next
        case False
        then obtain ry where ry_type: "ry \<in>\<^sub>c X" and y_eq: "y = right_coproj(X, X) \<circ>\<^sub>c ry" using y_disj by auto
        have px: "\<rho> \<circ>\<^sub>c x = \<langle>lx, \<t>\<rangle>" using x_eq rho_at_left[OF lx_type] by simp
        have py: "\<rho> \<circ>\<^sub>c y = \<langle>ry, \<f>\<rangle>" using y_eq rho_at_right[OF ry_type] by simp
        have "\<langle>lx, \<t>\<rangle> = \<langle>ry, \<f>\<rangle>" using eqs px py by simp
        then have "\<t> = \<f>" using cart_prod_eq2[OF lx_type true_func_type ry_type false_func_type] by auto
        then show "x = y" using true_false_distinct by simp
      qed
    next
      case False
      then obtain rx where rx_type: "rx \<in>\<^sub>c X" and x_eq: "x = right_coproj(X, X) \<circ>\<^sub>c rx" using x_disj by auto
      show "x = y"
      proof (cases "\<exists>ly. ly \<in>\<^sub>c X \<and> y = left_coproj(X, X) \<circ>\<^sub>c ly")
        case True
        then obtain ly where ly_type: "ly \<in>\<^sub>c X" and y_eq: "y = left_coproj(X, X) \<circ>\<^sub>c ly" by auto
        have px: "\<rho> \<circ>\<^sub>c x = \<langle>rx, \<f>\<rangle>" using x_eq rho_at_right[OF rx_type] by simp
        have py: "\<rho> \<circ>\<^sub>c y = \<langle>ly, \<t>\<rangle>" using y_eq rho_at_left[OF ly_type] by simp
        have "\<langle>rx, \<f>\<rangle> = \<langle>ly, \<t>\<rangle>" using eqs px py by simp
        then have "\<f> = \<t>" using cart_prod_eq2[OF rx_type false_func_type ly_type true_func_type] by auto
        then show "x = y" using true_false_distinct by simp
      next
        case False
        then obtain ry where ry_type: "ry \<in>\<^sub>c X" and y_eq: "y = right_coproj(X, X) \<circ>\<^sub>c ry" using y_disj by auto
        have px: "\<rho> \<circ>\<^sub>c x = \<langle>rx, \<f>\<rangle>" using x_eq rho_at_right[OF rx_type] by simp
        have py: "\<rho> \<circ>\<^sub>c y = \<langle>ry, \<f>\<rangle>" using y_eq rho_at_right[OF ry_type] by simp
        have "\<langle>rx, \<f>\<rangle> = \<langle>ry, \<f>\<rangle>" using eqs px py by simp
        then have "rx = ry \<and> \<f> = \<f>" using cart_prod_eq2[OF rx_type false_func_type ry_type false_func_type] by auto
        then show "x = y" using x_eq y_eq by simp
      qed
    qed
  qed

  have surj: "surjective(\<rho>)"
    unfolding surjective_def2[OF rho_type]
  proof (intro allI impI)
    fix y
    assume y_type: "y \<in>\<^sub>c X \<times>\<^sub>c \<Omega>"
    obtain x w where x_type: "x \<in>\<^sub>c X" and w_type: "w \<in>\<^sub>c \<Omega>" and y_eq: "y = \<langle>x, w\<rangle>"
      using cart_prod_decomp[OF y_type] by blast
    have w_cases: "w = \<f> \<or> w = \<t>" using true_false_only_truth_values[OF w_type] by simp
    show "\<exists>z. z \<in>\<^sub>c X \<Coprod> X \<and> \<rho> \<circ>\<^sub>c z = y"
    proof (cases "w = \<t>")
      case True
      have lx_type: "left_coproj(X, X) \<circ>\<^sub>c x \<in>\<^sub>c X \<Coprod> X" using x_type left_proj_type comp_type by blast
      have "\<rho> \<circ>\<^sub>c (left_coproj(X, X) \<circ>\<^sub>c x) = y" using rho_at_left[OF x_type] True y_eq by simp
      then show ?thesis using lx_type by auto
    next
      case False
      then have w_eq_f: "w = \<f>" using w_cases by auto
      have rx_type: "right_coproj(X, X) \<circ>\<^sub>c x \<in>\<^sub>c X \<Coprod> X" using x_type right_proj_type comp_type by blast
      have "\<rho> \<circ>\<^sub>c (right_coproj(X, X) \<circ>\<^sub>c x) = y" using rho_at_right[OF x_type] w_eq_f y_eq by simp
      then show ?thesis using rx_type by auto
    qed
  qed

  have rho_mono: "monomorphism(\<rho>)" using injective_imp_monomorphism[OF inj] by simp
  have rho_epi: "epimorphism(\<rho>)" using surjective_is_epimorphism[OF surj] by simp
  have rho_iso: "isomorphism(\<rho>)" using epi_mon_is_iso[OF rho_epi rho_mono] by simp
  show ?thesis unfolding is_isomorphic_def using rho_type rho_iso by auto
qed

lemma oneUone_iso_\<Omega>:
  "\<Omega> \<cong> \<one> \<Coprod> \<one>"
proof -
  have cb_type: "case_bool : \<Omega> \<rightarrow> \<one> \<Coprod> \<one>" by (rule case_bool_type)
  have cb_iso: "isomorphism(case_bool)" by (rule case_bool_iso)
  show ?thesis unfolding is_isomorphic_def using cb_type cb_iso by auto
qed

text \<open>The lemma below is dual to Proposition 2.2.2 in Halvorson. HOL states it as the unnamed fact
  @{text "card {x. x \<in>\<^sub>c \<Omega> \<Coprod> \<Omega>} = 4"} — omitted here, matching the precedent set for the analogous
  unnamed @{text "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"} fact in @{text Truth.thy}: no @{text card}/set-comprehension
  theory exists in plain FOL, the fact is unnamed in HOL so nothing downstream can reference it by
  name, and nothing in this port depends on it.\<close>

end
