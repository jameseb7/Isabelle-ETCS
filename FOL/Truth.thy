section \<open>Truth Values and Characteristic Functions\<close>

theory Truth
  imports Equalizer
begin

text \<open>The axiomatization below corresponds to Axiom 5 (Truth-Value Object) in Halvorson.\<close>
axiomatization
  true_func :: "cfunc" ("\<t>") and
  false_func  :: "cfunc" ("\<f>") and
  truth_value_set :: "cset" ("\<Omega>")
where
  true_func_type[type_rule]: "\<t> \<in>\<^sub>c \<Omega>" and
  false_func_type[type_rule]: "\<f> \<in>\<^sub>c \<Omega>" and
  true_false_distinct: "\<t> \<noteq> \<f>" and
  true_false_only_truth_values: "x \<in>\<^sub>c \<Omega> \<Longrightarrow> x = \<f> \<or> x = \<t>" and
  characteristic_function_exists:
    "m : B \<rightarrow> X \<Longrightarrow> monomorphism(m) \<Longrightarrow> \<exists>! \<chi>. is_pullback(B, \<one>, X, \<Omega>, \<beta>\<^bsub>B\<^esub>, \<t>, m, \<chi>)"

text \<open>HOL's @{text characteristic_func} is defined via @{text THE}, which has no FOL equivalent;
  following the pattern used for @{text inverse}/@{text "f\<^bold>\<inverse>"} in @{text Cfunc.thy}, we axiomatize
  it directly as the (Skolemized) witness of the existence half of
  @{text characteristic_function_exists} -- a conservative extension.\<close>
axiomatization
  characteristic_func :: "cfunc \<Rightarrow> cfunc"
where
  characteristic_func_spec: "m : B \<rightarrow> X \<Longrightarrow> monomorphism(m) \<Longrightarrow>
    is_pullback(B, \<one>, X, \<Omega>, \<beta>\<^bsub>B\<^esub>, \<t>, m, characteristic_func(m))"

lemma characteristic_func_is_pullback:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "is_pullback(B, \<one>, X, \<Omega>, \<beta>\<^bsub>B\<^esub>, \<t>, m, characteristic_func(m))"
  using characteristic_func_spec[OF m_type m_mono] by simp

lemma characteristic_func_type[type_rule]:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "characteristic_func(m) : X \<rightarrow> \<Omega>"
proof -
  have "is_pullback(B, \<one>, X, \<Omega>, \<beta>\<^bsub>B\<^esub>, \<t>, m, characteristic_func(m))"
    using characteristic_func_is_pullback[OF m_type m_mono] by simp
  then show ?thesis unfolding is_pullback_def by auto
qed

lemma characteristic_func_eq:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "characteristic_func(m) \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>"
  using characteristic_func_is_pullback[OF m_type m_mono] unfolding is_pullback_def by auto

lemma monomorphism_equalizes_char_func:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "equalizer(B, m, characteristic_func(m), \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
proof -
  have chi_type: "characteristic_func(m) : X \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have tbX_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using bX_type true_func_type comp_type by blast
  have comm: "characteristic_func(m) \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m"
  proof -
    have eq0: "characteristic_func(m) \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>" using characteristic_func_eq[OF m_type m_mono] by simp
    have bB_eq: "\<beta>\<^bsub>B\<^esub> = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c m" using terminal_func_comp[OF m_type] by simp
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c m)" using comp_associative2[OF m_type bX_type true_func_type] by simp
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>" using bB_eq by simp
    finally show ?thesis using eq0 by simp
  qed
  have uniq: "\<forall> h F. ((h : F \<rightarrow> X) \<and> (characteristic_func(m) \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> B) \<and> m \<circ>\<^sub>c k = h)"
  proof (intro allI impI)
    fix h F
    assume "h : F \<rightarrow> X \<and> characteristic_func(m) \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h"
    then have h_type: "h : F \<rightarrow> X" and h_eq: "characteristic_func(m) \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h" by auto
    have pb: "is_pullback(B, \<one>, X, \<Omega>, \<beta>\<^bsub>B\<^esub>, \<t>, m, characteristic_func(m))"
      using characteristic_func_is_pullback[OF m_type m_mono] by simp
    have pb_uniq: "\<forall>Z k' h'. (k' : Z \<rightarrow> \<one> \<and> h' : Z \<rightarrow> X \<and> \<t> \<circ>\<^sub>c k' = characteristic_func(m) \<circ>\<^sub>c h') \<longrightarrow>
        (\<exists>!j. j : Z \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j = k' \<and> m \<circ>\<^sub>c j = h')"
      using pb unfolding is_pullback_def by auto
    have bF_type: "\<beta>\<^bsub>F\<^esub> : F \<rightarrow> \<one>" by (rule terminal_func_type)
    have bXh_eq_bF: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = \<beta>\<^bsub>F\<^esub>" using terminal_func_comp[OF h_type] by simp
    have t_bF_eq: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>F\<^esub> = characteristic_func(m) \<circ>\<^sub>c h"
    proof -
      have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c h = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h)" using comp_associative2[OF h_type bX_type true_func_type] by simp
      also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>F\<^esub>" using bXh_eq_bF by simp
      finally show ?thesis using h_eq by simp
    qed
    have ex1j: "\<exists>!j. j : F \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j = \<beta>\<^bsub>F\<^esub> \<and> m \<circ>\<^sub>c j = h"
      using pb_uniq[rule_format, where Z=F and k'="\<beta>\<^bsub>F\<^esub>" and h'=h] bF_type h_type t_bF_eq by auto
    then obtain j where j_type: "j : F \<rightarrow> B" and j_eq: "m \<circ>\<^sub>c j = h"
        and j_unique: "\<forall>j'. (j' : F \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j' = \<beta>\<^bsub>F\<^esub> \<and> m \<circ>\<^sub>c j' = h) \<longrightarrow> j' = j"
      by auto
    show "\<exists>! k. (k : F \<rightarrow> B) \<and> m \<circ>\<^sub>c k = h"
    proof (rule ex1I[where a=j])
      show "j : F \<rightarrow> B \<and> m \<circ>\<^sub>c j = h" using j_type j_eq by simp
    next
      fix k' assume "k' : F \<rightarrow> B \<and> m \<circ>\<^sub>c k' = h"
      then have k'_type: "k' : F \<rightarrow> B" and k'_eq: "m \<circ>\<^sub>c k' = h" by auto
      have bB_k'_eq: "\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c k' = \<beta>\<^bsub>F\<^esub>" using terminal_func_comp[OF k'_type] by simp
      show "k' = j" using j_unique k'_type bB_k'_eq k'_eq by auto
    qed
  qed
  show ?thesis
    unfolding equalizer_def
    using chi_type tbX_type m_type comm uniq by auto
qed

lemma characteristic_func_unique_from_equalizer:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)" and chi_type: "\<chi> : X \<rightarrow> \<Omega>"
  assumes chi_eq: "equalizer(B, m, \<chi>, \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
  shows "\<chi> = characteristic_func(m)"
proof (rule one_separator[where X=X and Y="\<Omega>"])
  show "\<chi> : X \<rightarrow> \<Omega>" by (rule chi_type)
  show "characteristic_func(m) : X \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  fix x assume x_type: "x : \<one> \<rightarrow> X"
  have eqB: "equalizer(B, m, characteristic_func(m), \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
    using monomorphism_equalizes_char_func[OF m_type m_mono] by simp
  have chartype: "characteristic_func(m) : X \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have tbX_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using terminal_func_type true_func_type comp_type by blast
  have iff1: "x factorsthru m \<longleftrightarrow> \<chi> \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x"
    using xfactorthru_equalizer_iff_fx_eq_gx[OF chi_type tbX_type chi_eq x_type] by simp
  have iff2: "x factorsthru m \<longleftrightarrow> characteristic_func(m) \<circ>\<^sub>c x = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x"
    using xfactorthru_equalizer_iff_fx_eq_gx[OF chartype tbX_type eqB x_type] by simp
  have tbXx_eq_t: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = \<t>"
  proof -
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)"
      using comp_associative2[OF x_type terminal_func_type true_func_type] by simp
    also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF x_type] by simp
    also have "... = \<t>" using id_right_unit2[OF true_func_type] by simp
    finally show ?thesis by simp
  qed
  have iff1': "x factorsthru m \<longleftrightarrow> \<chi> \<circ>\<^sub>c x = \<t>" using iff1 tbXx_eq_t by simp
  have iff2': "x factorsthru m \<longleftrightarrow> characteristic_func(m) \<circ>\<^sub>c x = \<t>" using iff2 tbXx_eq_t by simp
  have chix_type: "\<chi> \<circ>\<^sub>c x \<in>\<^sub>c \<Omega>" using x_type chi_type comp_type by blast
  have charx_type: "characteristic_func(m) \<circ>\<^sub>c x \<in>\<^sub>c \<Omega>" using x_type chartype comp_type by blast
  show "\<chi> \<circ>\<^sub>c x = characteristic_func(m) \<circ>\<^sub>c x"
  proof (cases "x factorsthru m")
    case True
    then have "\<chi> \<circ>\<^sub>c x = \<t>" using iff1' by simp
    moreover have "characteristic_func(m) \<circ>\<^sub>c x = \<t>" using True iff2' by simp
    ultimately show ?thesis by simp
  next
    case False
    then have chix_ne_t: "\<chi> \<circ>\<^sub>c x \<noteq> \<t>" using iff1' by simp
    then have chix_eq_f: "\<chi> \<circ>\<^sub>c x = \<f>" using true_false_only_truth_values[OF chix_type] by auto
    have charx_ne_t: "characteristic_func(m) \<circ>\<^sub>c x \<noteq> \<t>" using False iff2' by simp
    then have charx_eq_f: "characteristic_func(m) \<circ>\<^sub>c x = \<f>" using true_false_only_truth_values[OF charx_type] by auto
    show ?thesis using chix_eq_f charx_eq_f by simp
  qed
qed

lemma characteristic_func_true_relative_member:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c X"
  assumes characteristic_func_true: "characteristic_func(m) \<circ>\<^sub>c x = \<t>"
  shows "relative_member(x, X, B, m)"
proof -
  have pb: "is_pullback(B, \<one>, X, \<Omega>, \<beta>\<^bsub>B\<^esub>, \<t>, m, characteristic_func(m))"
    using characteristic_func_is_pullback[OF m_type m_mono] by simp
  have pb_uniq: "\<forall>Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> X \<and> \<t> \<circ>\<^sub>c k = characteristic_func(m) \<circ>\<^sub>c h) \<longrightarrow>
      (\<exists>!j. j : Z \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j = k \<and> m \<circ>\<^sub>c j = h)"
    using pb unfolding is_pullback_def by auto
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have t_id1_eq: "\<t> \<circ>\<^sub>c id(\<one>) = characteristic_func(m) \<circ>\<^sub>c x"
    using id_right_unit2[OF true_func_type] characteristic_func_true by simp
  have ex1j: "\<exists>!j. j : \<one> \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> m \<circ>\<^sub>c j = x"
    using pb_uniq[rule_format, where Z="\<one>" and k="id(\<one>)" and h=x] id1_type x_type t_id1_eq by auto
  then obtain j where j_type: "j : \<one> \<rightarrow> B" and j_eq: "m \<circ>\<^sub>c j = x" by auto
  have x_factorsthru: "x factorsthru m" using factors_through_def2[OF x_type m_type] j_type j_eq by auto
  show "relative_member(x, X, B, m)" unfolding relative_member_def using x_type m_mono m_type x_factorsthru by auto
qed

lemma characteristic_func_false_not_relative_member:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c X"
  assumes characteristic_func_false: "characteristic_func(m) \<circ>\<^sub>c x = \<f>"
  shows "\<not> relative_member(x, X, B, m)"
proof
  assume "relative_member(x, X, B, m)"
  then have x_factorsthru: "x factorsthru m" unfolding relative_member_def by auto
  obtain h where h_type: "h : \<one> \<rightarrow> B" and x_def: "m \<circ>\<^sub>c h = x"
    using factors_through_def2[OF x_type m_type] x_factorsthru by auto

  have char_m_true: "characteristic_func(m) \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>"
    using characteristic_func_eq[OF m_type m_mono] by simp
  have m_type2: "characteristic_func(m) : X \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp

  have "characteristic_func(m) \<circ>\<^sub>c (m \<circ>\<^sub>c h) = \<f>" using x_def characteristic_func_false by simp
  then have step1: "(characteristic_func(m) \<circ>\<^sub>c m) \<circ>\<^sub>c h = \<f>"
    using comp_associative2[OF h_type m_type m_type2] by simp
  then have step2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c h = \<f>" using char_m_true by simp
  have step3: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c h = \<t>"
  proof -
    have bB_type: "\<beta>\<^bsub>B\<^esub> : B \<rightarrow> \<one>" by (rule terminal_func_type)
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c h = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c h)" using comp_associative2[OF h_type bB_type true_func_type] by simp
    also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF h_type] by simp
    also have "... = \<t>" using id_right_unit2[OF true_func_type] by simp
    finally show ?thesis by simp
  qed
  have "\<t> = \<f>" using step2 step3 by simp
  then show False using true_false_distinct by simp
qed

lemma rel_mem_char_func_true:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c X"
  assumes rel_mem: "relative_member(x, X, B, m)"
  shows "characteristic_func(m) \<circ>\<^sub>c x = \<t>"
proof (rule ccontr)
  assume ne_t: "characteristic_func(m) \<circ>\<^sub>c x \<noteq> \<t>"
  have charx_type: "characteristic_func(m) \<circ>\<^sub>c x \<in>\<^sub>c \<Omega>"
    using x_type characteristic_func_type[OF m_type m_mono] comp_type by blast
  have eq_f: "characteristic_func(m) \<circ>\<^sub>c x = \<f>" using true_false_only_truth_values[OF charx_type] ne_t by auto
  have "\<not> relative_member(x, X, B, m)"
    using characteristic_func_false_not_relative_member[OF m_type m_mono x_type eq_f] by simp
  then show False using rel_mem by simp
qed

lemma not_rel_mem_char_func_false:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c X"
  assumes not_rel_mem: "\<not> relative_member(x, X, B, m)"
  shows "characteristic_func(m) \<circ>\<^sub>c x = \<f>"
proof (rule ccontr)
  assume ne_f: "characteristic_func(m) \<circ>\<^sub>c x \<noteq> \<f>"
  have charx_type: "characteristic_func(m) \<circ>\<^sub>c x \<in>\<^sub>c \<Omega>"
    using x_type characteristic_func_type[OF m_type m_mono] comp_type by blast
  have eq_t: "characteristic_func(m) \<circ>\<^sub>c x = \<t>" using true_false_only_truth_values[OF charx_type] ne_f by auto
  have "relative_member(x, X, B, m)"
    using characteristic_func_true_relative_member[OF m_type m_mono x_type eq_t] by simp
  then show False using not_rel_mem by simp
qed

text \<open>HOL's Proposition 2.2.2 (@{text "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"}) is deliberately not ported:
  it relies on HOL's @{text card}/finite-set machinery applied to the meta-level collection of
  elements of a @{text cset}, which has no counterpart in this development at all (plain FOL has no
  set-comprehension or cardinality theory, and nothing else in the file depends on this fact by
  name). The four-element-ness of @{text "\<Omega> \<times>\<^sub>c \<Omega>"} isn't otherwise used downstream.\<close>

subsection \<open>Equality Predicate\<close>

text \<open>HOL's @{text eq_pred} is its own separate @{text THE}-defined constant, but since
  @{text "diagonal(X)"} is always monic (@{text diag_mono}), it is literally an instance of
  @{text characteristic_func} -- no fresh Skolemization is needed at all here.\<close>
definition eq_pred :: "cset \<Rightarrow> cfunc" where
  "eq_pred(X) = characteristic_func(diagonal(X))"

lemma eq_pred_pullback: "is_pullback(X, \<one>, X \<times>\<^sub>c X, \<Omega>, \<beta>\<^bsub>X\<^esub>, \<t>, diagonal(X), eq_pred(X))"
proof -
  have diag_type: "diagonal(X) : X \<rightarrow> X \<times>\<^sub>c X" by (rule diagonal_type)
  have diag_mono': "monomorphism(diagonal(X))" by (rule diag_mono)
  have "is_pullback(X, \<one>, X \<times>\<^sub>c X, \<Omega>, \<beta>\<^bsub>X\<^esub>, \<t>, diagonal(X), characteristic_func(diagonal(X)))"
    using characteristic_func_is_pullback[OF diag_type diag_mono'] by simp
  then show ?thesis unfolding eq_pred_def by simp
qed

lemma eq_pred_type[type_rule]: "eq_pred(X) : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
  using eq_pred_pullback unfolding is_pullback_def by auto

lemma eq_pred_square: "eq_pred(X) \<circ>\<^sub>c diagonal(X) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
  using eq_pred_pullback unfolding is_pullback_def by auto

lemma eq_pred_iff_eq:
  assumes x_type: "x : \<one> \<rightarrow> X" and y_type: "y : \<one> \<rightarrow> X"
  shows "(x = y) \<longleftrightarrow> (eq_pred(X) \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>)"
proof (rule iffI)
  assume x_eq_y: "x = y"
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have idXidX_type: "\<langle>id(X),id(X)\<rangle> : X \<rightarrow> X \<times>\<^sub>c X" using idX_type cfunc_prod_type by auto
  have step0: "(eq_pred(X) \<circ>\<^sub>c \<langle>id(X),id(X)\<rangle>) \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using eq_pred_square unfolding diagonal_def by simp
  have step1: "eq_pred(X) \<circ>\<^sub>c (\<langle>id(X),id(X)\<rangle> \<circ>\<^sub>c y) = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
  proof -
    have "(eq_pred(X) \<circ>\<^sub>c \<langle>id(X),id(X)\<rangle>) \<circ>\<^sub>c y = eq_pred(X) \<circ>\<^sub>c (\<langle>id(X),id(X)\<rangle> \<circ>\<^sub>c y)"
      using comp_associative2[OF y_type idXidX_type eq_pred_type] by simp
    then show ?thesis using step0 by simp
  qed
  have prod_eq: "\<langle>id(X),id(X)\<rangle> \<circ>\<^sub>c y = \<langle>y, y\<rangle>"
    using cfunc_prod_comp[OF y_type idX_type idX_type] id_left_unit2[OF y_type] by simp
  have step2: "eq_pred(X) \<circ>\<^sub>c \<langle>y, y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using step1 prod_eq by simp
  have step3: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y = \<t>"
  proof -
    have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c y)" using comp_associative2[OF y_type bX_type true_func_type] by simp
    also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF y_type] by simp
    also have "... = \<t>" using id_right_unit2[OF true_func_type] by simp
    finally show ?thesis by simp
  qed
  have "eq_pred(X) \<circ>\<^sub>c \<langle>y,y\<rangle> = \<t>" using step2 step3 by simp
  then show "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>" using x_eq_y by simp
next
  assume eq_t: "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>"
  have xy_type: "\<langle>x,y\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c X" using x_type y_type cfunc_prod_type by auto
  have eq_id: "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t> \<circ>\<^sub>c id(\<one>)" using eq_t id_right_unit2[OF true_func_type] by simp
  have pb: "is_pullback(X, \<one>, X \<times>\<^sub>c X, \<Omega>, \<beta>\<^bsub>X\<^esub>, \<t>, diagonal(X), eq_pred(X))" by (rule eq_pred_pullback)
  have pb_uniq: "\<forall>Z k h. (k : Z \<rightarrow> \<one> \<and> h : Z \<rightarrow> X \<times>\<^sub>c X \<and> \<t> \<circ>\<^sub>c k = eq_pred(X) \<circ>\<^sub>c h) \<longrightarrow>
      (\<exists>!j. j : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c j = k \<and> diagonal(X) \<circ>\<^sub>c j = h)"
    using pb unfolding is_pullback_def by auto
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have ex1j: "\<exists>!j. j : \<one> \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c j = id(\<one>) \<and> diagonal(X) \<circ>\<^sub>c j = \<langle>x,y\<rangle>"
    using pb_uniq[rule_format, where Z="\<one>" and k="id(\<one>)" and h="\<langle>x,y\<rangle>"] id1_type xy_type eq_id by auto
  then obtain j where j_type: "j : \<one> \<rightarrow> X" and j_eq: "diagonal(X) \<circ>\<^sub>c j = \<langle>x,y\<rangle>" by auto
  have jj_eq_xy: "\<langle>j,j\<rangle> = \<langle>x,y\<rangle>" using diag_on_elements[OF j_type] j_eq by simp
  have "j = x \<and> j = y" using element_pair_eq[OF j_type x_type j_type y_type] jj_eq_xy by auto
  then show "x = y" by auto
qed

lemma eq_pred_iff_eq_conv:
  assumes x_type: "x : \<one> \<rightarrow> X" and y_type: "y : \<one> \<rightarrow> X"
  shows "(x \<noteq> y) \<longleftrightarrow> (eq_pred(X) \<circ>\<^sub>c \<langle>x, y\<rangle> = \<f>)"
proof (rule iffI)
  assume xney: "x \<noteq> y"
  have xy_type: "\<langle>x,y\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c X" using x_type y_type cfunc_prod_type by auto
  have exyt_type: "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> \<in>\<^sub>c \<Omega>" using xy_type eq_pred_type comp_type by blast
  have ne_t: "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> \<noteq> \<t>" using eq_pred_iff_eq[OF x_type y_type] xney by auto
  show "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<f>" using true_false_only_truth_values[OF exyt_type] ne_t by auto
next
  assume eq_f: "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<f>"
  show "x \<noteq> y"
  proof
    assume x_eq_y: "x = y"
    then have "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>" using eq_pred_iff_eq[OF x_type y_type] by auto
    then show False using eq_f true_false_distinct by simp
  qed
qed

lemma eq_pred_iff_eq_conv2:
  assumes x_type: "x : \<one> \<rightarrow> X" and y_type: "y : \<one> \<rightarrow> X"
  shows "(x \<noteq> y) \<longleftrightarrow> (eq_pred(X) \<circ>\<^sub>c \<langle>x, y\<rangle> \<noteq> \<t>)"
  using eq_pred_iff_eq[OF x_type y_type] by auto

lemma eq_pred_of_monomorphism:
  assumes m_type: "m : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m) = eq_pred(X)"
proof (rule one_separator[where X="X \<times>\<^sub>c X" and Y="\<Omega>"])
  have mm_type: "m \<times>\<^sub>f m : X \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Y" using m_type cfunc_cross_prod_type by auto
  show "eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m) : X \<times>\<^sub>c X \<rightarrow> \<Omega>" using mm_type eq_pred_type comp_type by blast
  show "eq_pred(X) : X \<times>\<^sub>c X \<rightarrow> \<Omega>" by (rule eq_pred_type)
  fix x assume x_type: "x : \<one> \<rightarrow> X \<times>\<^sub>c X"
  obtain x1 x2 where x_def: "x = \<langle>x1, x2\<rangle>" and x1_type: "x1 : \<one> \<rightarrow> X" and x2_type: "x2 : \<one> \<rightarrow> X"
    using cart_prod_decomp[OF x_type] by blast
  show "(eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m)) \<circ>\<^sub>c x = eq_pred(X) \<circ>\<^sub>c x"
    unfolding x_def
  proof (cases "(eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>")
    case True
    have x1x2_type: "\<langle>x1,x2\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c X" using x1_type x2_type cfunc_prod_type by auto
    have step1: "eq_pred(Y) \<circ>\<^sub>c ((m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle>) = \<t>"
      using comp_associative2[OF x1x2_type mm_type eq_pred_type] True by simp
    have step2: "(m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF x1_type x2_type m_type m_type] by simp
    have step3: "eq_pred(Y) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle> = \<t>" using step1 step2 by simp
    have mx1_type: "m \<circ>\<^sub>c x1 : \<one> \<rightarrow> Y" using x1_type m_type comp_type by blast
    have mx2_type: "m \<circ>\<^sub>c x2 : \<one> \<rightarrow> Y" using x2_type m_type comp_type by blast
    have "m \<circ>\<^sub>c x1 = m \<circ>\<^sub>c x2" using eq_pred_iff_eq[OF mx1_type mx2_type] step3 by simp
    then have x1_eq_x2: "x1 = x2"
      using m_mono monomorphism_def3[OF m_type] x1_type x2_type by auto
    have "eq_pred(X) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<t>" using eq_pred_iff_eq[OF x1_type x2_type] x1_eq_x2 by auto
    then show "(eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = eq_pred(X) \<circ>\<^sub>c \<langle>x1,x2\<rangle>" using True by simp
  next
    case False
    have x1x2_type: "\<langle>x1,x2\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c X" using x1_type x2_type cfunc_prod_type by auto
    have eyxx_type: "(eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>x1,x2\<rangle> \<in>\<^sub>c \<Omega>"
      using x1x2_type mm_type eq_pred_type comp_type by blast
    have LHS: "(eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>"
      using true_false_only_truth_values[OF eyxx_type] False by auto
    have step1: "eq_pred(Y) \<circ>\<^sub>c ((m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle>) = \<f>"
      using comp_associative2[OF x1x2_type mm_type eq_pred_type] LHS by simp
    have step2: "(m \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF x1_type x2_type m_type m_type] by simp
    have step3: "eq_pred(Y) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c x1, m \<circ>\<^sub>c x2\<rangle> = \<f>" using step1 step2 by simp
    have mx1_type: "m \<circ>\<^sub>c x1 : \<one> \<rightarrow> Y" using x1_type m_type comp_type by blast
    have mx2_type: "m \<circ>\<^sub>c x2 : \<one> \<rightarrow> Y" using x2_type m_type comp_type by blast
    have "m \<circ>\<^sub>c x1 \<noteq> m \<circ>\<^sub>c x2" using eq_pred_iff_eq_conv[OF mx1_type mx2_type] step3 by simp
    then have x1_ne_x2: "x1 \<noteq> x2" by auto
    have "eq_pred(X) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = \<f>" using eq_pred_iff_eq_conv[OF x1_type x2_type] x1_ne_x2 by simp
    then show "(eq_pred(Y) \<circ>\<^sub>c (m \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>x1,x2\<rangle> = eq_pred(X) \<circ>\<^sub>c \<langle>x1,x2\<rangle>" using LHS by simp
  qed
qed

lemma eq_pred_true_extract_right:
  assumes x_type: "x \<in>\<^sub>c X"
  shows "eq_pred(X) \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id(X)\<rangle> \<circ>\<^sub>c x = \<t>"
proof -
  have eq1: "\<langle>x,x\<rangle> = \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id(X)\<rangle> \<circ>\<^sub>c x" using cart_prod_extract_right[OF x_type x_type] by simp
  have "eq_pred(X) \<circ>\<^sub>c \<langle>x,x\<rangle> = \<t>" using eq_pred_iff_eq[OF x_type x_type] by simp
  then show ?thesis using eq1 by simp
qed

lemma eq_pred_false_extract_right:
  assumes x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X" and xney: "x \<noteq> y"
  shows "eq_pred(X) \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id(X)\<rangle> \<circ>\<^sub>c y = \<f>"
proof -
  have eq1: "\<langle>x,y\<rangle> = \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id(X)\<rangle> \<circ>\<^sub>c y" using cart_prod_extract_right[OF x_type y_type] by simp
  have "eq_pred(X) \<circ>\<^sub>c \<langle>x,y\<rangle> = \<f>" using eq_pred_iff_eq_conv[OF x_type y_type] xney by simp
  then show ?thesis using eq1 by simp
qed

subsection \<open>Properties of Monomorphisms and Epimorphisms\<close>

text \<open>The lemma below corresponds to Exercise 2.2.3 in Halvorson.\<close>
lemma regmono_is_mono:
  assumes regmono: "regular_monomorphism(m)"
  shows "monomorphism(m)"
proof -
  obtain g h where "equalizer(domain(m), m, g, h)" using regmono unfolding regular_monomorphism_def by auto
  then show ?thesis using equalizer_is_monomorphism by blast
qed

text \<open>The lemma below corresponds to Proposition 2.2.4 in Halvorson.\<close>
lemma mono_is_regmono:
  assumes m_mono: "monomorphism(m)"
  shows "regular_monomorphism(m)"
proof -
  have m_type: "m : domain(m) \<rightarrow> codomain(m)" unfolding cfunc_type_def by simp
  have eq: "equalizer(domain(m), m, characteristic_func(m), \<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub>)"
    using monomorphism_equalizes_char_func[OF m_type m_mono] by simp
  have chi_type: "characteristic_func(m) : codomain(m) \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have bcm_type: "\<beta>\<^bsub>codomain(m)\<^esub> : codomain(m) \<rightarrow> \<one>" by (rule terminal_func_type)
  have tbcm_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub> : codomain(m) \<rightarrow> \<Omega>" using bcm_type true_func_type comp_type by blast
  have dom_chi: "domain(characteristic_func(m)) = codomain(m)" using chi_type unfolding cfunc_type_def by auto
  have dom_tbcm: "domain(\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub>) = codomain(m)" using tbcm_type unfolding cfunc_type_def by auto
  show ?thesis
    unfolding regular_monomorphism_def
    using dom_chi dom_tbcm eq by auto
qed

text \<open>The lemma below corresponds to Proposition 2.2.5 in Halvorson.\<close>
lemma epi_mon_is_iso:
  assumes f_epi: "epimorphism(f)" and f_mono: "monomorphism(f)"
  shows "isomorphism(f)"
  using epi_regmon_is_iso[OF f_epi mono_is_regmono[OF f_mono]] by simp

text \<open>The lemma below corresponds to Proposition 2.2.8 in Halvorson.\<close>
lemma epi_is_surj:
  assumes p_type: "p : X \<rightarrow> Y" and p_epi: "epimorphism(p)"
  shows "surjective(p)"
  unfolding surjective_def
proof (rule ccontr)
  assume a1: "\<not> (\<forall>y. y \<in>\<^sub>c codomain(p) \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain(p) \<and> p \<circ>\<^sub>c x = y))"
  have cod_p: "codomain(p) = Y" using p_type unfolding cfunc_type_def by auto
  have dom_p: "domain(p) = X" using p_type unfolding cfunc_type_def by auto
  have "\<exists>y. y \<in>\<^sub>c Y \<and> \<not>(\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y)" using a1 cod_p dom_p by auto
  then obtain y0 where y0_type: "y0 \<in>\<^sub>c Y" and y0_prop: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> y0"
    by auto

  define g where "g = eq_pred(Y) \<circ>\<^sub>c \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>"
  have bY_type: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by (rule terminal_func_type)
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have y0bY_type: "y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> Y" using bY_type y0_type comp_type by blast
  have g_right_arg_type: "\<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> : Y \<rightarrow> Y \<times>\<^sub>c Y" using y0bY_type idY_type cfunc_prod_type by auto
  have g_type: "g : Y \<rightarrow> \<Omega>" unfolding g_def using g_right_arg_type eq_pred_type comp_type by blast

  have gpx_Eqs_f: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> g \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<f>"
  proof (rule ccontr)
    assume "\<not> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> g \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<f>)"
    then obtain x where x_type: "x \<in>\<^sub>c X" and bwoc: "g \<circ>\<^sub>c (p \<circ>\<^sub>c x) \<noteq> \<f>"
      by auto
    have px_type: "p \<circ>\<^sub>c x \<in>\<^sub>c Y" using x_type p_type comp_type by blast
    have y0_ne_px: "y0 \<noteq> p \<circ>\<^sub>c x" using y0_prop x_type by auto
    have "g \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<f>"
    proof -
      have "g \<circ>\<^sub>c (p \<circ>\<^sub>c x) = (eq_pred(Y) \<circ>\<^sub>c \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>) \<circ>\<^sub>c (p \<circ>\<^sub>c x)" unfolding g_def by simp
      also have "... = eq_pred(Y) \<circ>\<^sub>c \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> \<circ>\<^sub>c (p \<circ>\<^sub>c x)"
        using comp_associative2[OF px_type g_right_arg_type eq_pred_type] by simp
      also have "... = \<f>" using eq_pred_false_extract_right[OF y0_type px_type] y0_ne_px by simp
      finally show ?thesis by simp
    qed
    then show False using bwoc by simp
  qed

  define h where "h = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
  have h_type: "h : Y \<rightarrow> \<Omega>" unfolding h_def using bY_type false_func_type comp_type by blast

  have hpx_eqs_f: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> h \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<f>"
  proof (intro allI impI)
    fix x assume x_type: "x \<in>\<^sub>c X"
    have px_type: "p \<circ>\<^sub>c x \<in>\<^sub>c Y" using x_type p_type comp_type by blast
    have "h \<circ>\<^sub>c (p \<circ>\<^sub>c x) = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c (p \<circ>\<^sub>c x)" unfolding h_def by simp
    also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c (p \<circ>\<^sub>c x))" using comp_associative2[OF px_type bY_type false_func_type] by simp
    also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF px_type] by simp
    also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
    finally show "h \<circ>\<^sub>c (p \<circ>\<^sub>c x) = \<f>" by simp
  qed

  have gp_eqs_hp: "g \<circ>\<^sub>c p = h \<circ>\<^sub>c p"
  proof (rule one_separator[where X=X and Y="\<Omega>"])
    show "g \<circ>\<^sub>c p : X \<rightarrow> \<Omega>" using g_type p_type comp_type by blast
    show "h \<circ>\<^sub>c p : X \<rightarrow> \<Omega>" using h_type p_type comp_type by blast
    fix x assume x_type: "x : \<one> \<rightarrow> X"
    have x_type2: "x \<in>\<^sub>c X" using x_type by simp
    have "(g \<circ>\<^sub>c p) \<circ>\<^sub>c x = g \<circ>\<^sub>c (p \<circ>\<^sub>c x)" using comp_associative2[OF x_type p_type g_type] by simp
    also have "... = \<f>" using gpx_Eqs_f x_type2 by simp
    also have "... = h \<circ>\<^sub>c (p \<circ>\<^sub>c x)" using hpx_eqs_f x_type2 by simp
    also have "... = (h \<circ>\<^sub>c p) \<circ>\<^sub>c x" using comp_associative2[OF x_type p_type h_type] by simp
    finally show "(g \<circ>\<^sub>c p) \<circ>\<^sub>c x = (h \<circ>\<^sub>c p) \<circ>\<^sub>c x" by simp
  qed

  have g_not_h: "g \<noteq> h"
  proof -
    have g_y0_eq_t: "g \<circ>\<^sub>c y0 = \<t>"
    proof -
      have assoc: "(eq_pred(Y) \<circ>\<^sub>c \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>) \<circ>\<^sub>c y0 = eq_pred(Y) \<circ>\<^sub>c (\<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> \<circ>\<^sub>c y0)"
        using comp_associative2[OF y0_type g_right_arg_type eq_pred_type] by simp
      show ?thesis unfolding g_def using assoc eq_pred_true_extract_right[OF y0_type] by simp
    qed
    have h_y0_eq_f: "h \<circ>\<^sub>c y0 = \<f>"
    proof -
      have "h \<circ>\<^sub>c y0 = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y0" unfolding h_def by simp
      also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c y0)" using comp_associative2[OF y0_type bY_type false_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF y0_type] by simp
      also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
      finally show ?thesis by simp
    qed
    show ?thesis
    proof
      assume g_eq_h: "g = h"
      have "\<t> = \<f>" using g_y0_eq_t h_y0_eq_f g_eq_h by simp
      then show False using true_false_distinct by simp
    qed
  qed

  have epi_prop: "\<forall>g' h'. domain(g') = codomain(p) \<and> domain(h') = codomain(p) \<longrightarrow> (g' \<circ>\<^sub>c p = h' \<circ>\<^sub>c p \<longrightarrow> g' = h')"
    using p_epi unfolding epimorphism_def by auto
  have dom_g: "domain(g) = Y" using g_type unfolding cfunc_type_def by auto
  have dom_h: "domain(h) = Y" using h_type unfolding cfunc_type_def by auto
  have "g = h" using epi_prop[rule_format, where g'=g and h'=h] dom_g dom_h cod_p gp_eqs_hp by auto
  then show False using g_not_h by simp
qed

text \<open>The lemma below corresponds to Proposition 2.2.9 in Halvorson.\<close>
lemma pullback_of_epi_is_epi1:
  assumes f_type: "f : Y \<rightarrow> Z" and f_epi: "epimorphism(f)"
  assumes pb: "is_pullback(A, Y, X, Z, q1, f, q0, g)"
  shows "epimorphism(q0)"
proof -
  have surj_f: "surjective(f)" using epi_is_surj[OF f_type f_epi] by simp
  have q1_type: "q1 : A \<rightarrow> Y" using pb unfolding is_pullback_def by auto
  have q0_type: "q0 : A \<rightarrow> X" using pb unfolding is_pullback_def by auto
  have g_type: "g : X \<rightarrow> Z" using pb unfolding is_pullback_def by auto
  have pb_uniq: "\<forall>Z' k h. k : Z' \<rightarrow> Y \<and> h : Z' \<rightarrow> X \<and> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h \<longrightarrow>
      (\<exists>!j. j : Z' \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = k \<and> q0 \<circ>\<^sub>c j = h)"
    using pb unfolding is_pullback_def by auto

  have surj_q0: "surjective(q0)"
    unfolding surjective_def
  proof (intro allI impI)
    fix y assume y_type: "y \<in>\<^sub>c codomain(q0)"
    have dom_q0: "domain(q0) = A" using q0_type unfolding cfunc_type_def by auto
    have cod_q0: "codomain(q0) = X" using q0_type unfolding cfunc_type_def by auto
    have y_type2: "y \<in>\<^sub>c X" using y_type cod_q0 by simp
    have gy_type: "g \<circ>\<^sub>c y \<in>\<^sub>c Z" using y_type2 g_type comp_type by blast
    have surj_f_prop: "\<forall>y'. y' \<in>\<^sub>c Z \<longrightarrow> (\<exists>z. z \<in>\<^sub>c Y \<and> f \<circ>\<^sub>c z = y')"
      using surj_f surjective_def2[OF f_type] by auto
    obtain z where z_type: "z \<in>\<^sub>c Y" and z_eq: "f \<circ>\<^sub>c z = g \<circ>\<^sub>c y"
      using surj_f_prop[rule_format, where y'="g \<circ>\<^sub>c y"] gy_type by auto
    have ex1k: "\<exists>!k. k : \<one> \<rightarrow> A \<and> q1 \<circ>\<^sub>c k = z \<and> q0 \<circ>\<^sub>c k = y"
      using pb_uniq[rule_format, where Z'="\<one>" and k=z and h=y] z_type y_type2 z_eq by auto
    then obtain k where k_type: "k : \<one> \<rightarrow> A" and k_eq: "q0 \<circ>\<^sub>c k = y" by auto
    show "\<exists>x. x \<in>\<^sub>c domain(q0) \<and> q0 \<circ>\<^sub>c x = y"
      using k_type k_eq dom_q0 by auto
  qed
  show ?thesis using surjective_is_epimorphism[OF surj_q0] by simp
qed

text \<open>The lemma below corresponds to Proposition 2.2.9b in Halvorson.\<close>
lemma pullback_of_epi_is_epi2:
  assumes g_type: "g : X \<rightarrow> Z" and g_epi: "epimorphism(g)"
  assumes pb: "is_pullback(A, Y, X, Z, q1, f, q0, g)"
  shows "epimorphism(q1)"
proof -
  have surj_g: "surjective(g)" using epi_is_surj[OF g_type g_epi] by simp
  have q1_type: "q1 : A \<rightarrow> Y" using pb unfolding is_pullback_def by auto
  have q0_type: "q0 : A \<rightarrow> X" using pb unfolding is_pullback_def by auto
  have f_type: "f : Y \<rightarrow> Z" using pb unfolding is_pullback_def by auto
  have pb_uniq: "\<forall>Z' k h. k : Z' \<rightarrow> Y \<and> h : Z' \<rightarrow> X \<and> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h \<longrightarrow>
      (\<exists>!j. j : Z' \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = k \<and> q0 \<circ>\<^sub>c j = h)"
    using pb unfolding is_pullback_def by auto

  have surj_q1: "surjective(q1)"
    unfolding surjective_def
  proof (intro allI impI)
    fix y assume y_type: "y \<in>\<^sub>c codomain(q1)"
    have dom_q1: "domain(q1) = A" using q1_type unfolding cfunc_type_def by auto
    have cod_q1: "codomain(q1) = Y" using q1_type unfolding cfunc_type_def by auto
    have y_type2: "y \<in>\<^sub>c Y" using y_type cod_q1 by simp
    have fy_type: "f \<circ>\<^sub>c y \<in>\<^sub>c Z" using y_type2 f_type comp_type by blast
    have surj_g_prop: "\<forall>y'. y' \<in>\<^sub>c Z \<longrightarrow> (\<exists>z. z \<in>\<^sub>c X \<and> g \<circ>\<^sub>c z = y')"
      using surj_g surjective_def2[OF g_type] by auto
    obtain z where z_type: "z \<in>\<^sub>c X" and z_eq: "g \<circ>\<^sub>c z = f \<circ>\<^sub>c y"
      using surj_g_prop[rule_format, where y'="f \<circ>\<^sub>c y"] fy_type by auto
    have z_eq': "f \<circ>\<^sub>c y = g \<circ>\<^sub>c z" using z_eq by simp
    have ex1k: "\<exists>!k. k : \<one> \<rightarrow> A \<and> q1 \<circ>\<^sub>c k = y \<and> q0 \<circ>\<^sub>c k = z"
      using pb_uniq[rule_format, where Z'="\<one>" and k=y and h=z] y_type2 z_type z_eq' by auto
    then obtain k where k_type: "k : \<one> \<rightarrow> A" and k_eq: "q1 \<circ>\<^sub>c k = y" by auto
    show "\<exists>x. x \<in>\<^sub>c domain(q1) \<and> q1 \<circ>\<^sub>c x = y"
      using k_type k_eq dom_q1 by auto
  qed
  show ?thesis using surjective_is_epimorphism[OF surj_q1] by simp
qed

text \<open>The lemma below corresponds to Proposition 2.2.9c in Halvorson.\<close>
lemma pullback_of_mono_is_mono1:
  assumes g_type: "g : X \<rightarrow> Z" and f_mono: "monomorphism(f)"
  assumes pb: "is_pullback(A, Y, X, Z, q1, f, q0, g)"
  shows "monomorphism(q0)"
proof -
  have q1_type: "q1 : A \<rightarrow> Y" using pb unfolding is_pullback_def by auto
  have q0_type: "q0 : A \<rightarrow> X" using pb unfolding is_pullback_def by auto
  have f_type: "f : Y \<rightarrow> Z" using pb unfolding is_pullback_def by auto
  have comm: "f \<circ>\<^sub>c q1 = g \<circ>\<^sub>c q0" using pb unfolding is_pullback_def by auto
  have pb_uniq: "\<forall>Z' k h. k : Z' \<rightarrow> Y \<and> h : Z' \<rightarrow> X \<and> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h \<longrightarrow>
      (\<exists>!j. j : Z' \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = k \<and> q0 \<circ>\<^sub>c j = h)"
    using pb unfolding is_pullback_def by auto
  show ?thesis
    unfolding monomorphism_def3[OF q0_type]
  proof (intro allI impI)
    fix u v Q
    assume "u : Q \<rightarrow> A \<and> v : Q \<rightarrow> A"
    then have u_type: "u : Q \<rightarrow> A" and v_type: "v : Q \<rightarrow> A" by auto
    assume equals: "q0 \<circ>\<^sub>c u = q0 \<circ>\<^sub>c v"

    have q1u_type: "q1 \<circ>\<^sub>c u : Q \<rightarrow> Y" using u_type q1_type comp_type by blast
    have q1v_type: "q1 \<circ>\<^sub>c v : Q \<rightarrow> Y" using v_type q1_type comp_type by blast
    have q0u_type: "q0 \<circ>\<^sub>c u : Q \<rightarrow> X" using u_type q0_type comp_type by blast
    have q0v_type: "q0 \<circ>\<^sub>c v : Q \<rightarrow> X" using v_type q0_type comp_type by blast

    have f_q1u_eq: "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u)"
    proof -
      have "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = (f \<circ>\<^sub>c q1) \<circ>\<^sub>c u" using comp_associative2[OF u_type q1_type f_type] by simp
      also have "... = (g \<circ>\<^sub>c q0) \<circ>\<^sub>c u" using comm by simp
      also have "... = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u)" using comp_associative2[OF u_type q0_type g_type] by simp
      finally show ?thesis by simp
    qed
    have f_q1v_eq: "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v) = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)"
    proof -
      have "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v) = (f \<circ>\<^sub>c q1) \<circ>\<^sub>c v" using comp_associative2[OF v_type q1_type f_type] by simp
      also have "... = (g \<circ>\<^sub>c q0) \<circ>\<^sub>c v" using comm by simp
      also have "... = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)" using comp_associative2[OF v_type q0_type g_type] by simp
      finally show ?thesis by simp
    qed

    have eqn1: "g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u) = f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v)"
      using f_q1u_eq equals f_q1v_eq by simp

    have f_mono_prop: "\<forall>a b. a : Q \<rightarrow> Y \<and> b : Q \<rightarrow> Y \<longrightarrow> (f \<circ>\<^sub>c a = f \<circ>\<^sub>c b \<longrightarrow> a = b)"
      using f_mono monomorphism_def3[OF f_type] by auto
    have f_q1u_eq_f_q1v: "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v)" using f_q1u_eq eqn1 by simp
    have eqn2: "q1 \<circ>\<^sub>c u = q1 \<circ>\<^sub>c v"
      using f_mono_prop[rule_format] q1u_type q1v_type f_q1u_eq_f_q1v by auto

    have uniq_v: "\<exists>!j. j : Q \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = q1 \<circ>\<^sub>c v \<and> q0 \<circ>\<^sub>c j = q0 \<circ>\<^sub>c v"
      using pb_uniq[rule_format, where Z'=Q and k="q1 \<circ>\<^sub>c v" and h="q0 \<circ>\<^sub>c v"] q1v_type q0v_type f_q1v_eq by auto
    then obtain j where j_type: "j : Q \<rightarrow> A"
        and j_unique: "\<forall>j'. (j' : Q \<rightarrow> A \<and> q1 \<circ>\<^sub>c j' = q1 \<circ>\<^sub>c v \<and> q0 \<circ>\<^sub>c j' = q0 \<circ>\<^sub>c v) \<longrightarrow> j' = j"
      by auto
    have v_matches: "v = j" using j_unique v_type by auto
    have u_matches: "u = j" using j_unique u_type eqn2 equals by auto
    show "u = v" using u_matches v_matches by simp
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.2.9d in Halvorson.\<close>
lemma pullback_of_mono_is_mono2:
  assumes g_type: "g : X \<rightarrow> Z" and g_mono: "monomorphism(g)"
  assumes pb: "is_pullback(A, Y, X, Z, q1, f, q0, g)"
  shows "monomorphism(q1)"
proof -
  have q1_type: "q1 : A \<rightarrow> Y" using pb unfolding is_pullback_def by auto
  have q0_type: "q0 : A \<rightarrow> X" using pb unfolding is_pullback_def by auto
  have f_type: "f : Y \<rightarrow> Z" using pb unfolding is_pullback_def by auto
  have comm: "f \<circ>\<^sub>c q1 = g \<circ>\<^sub>c q0" using pb unfolding is_pullback_def by auto
  have pb_uniq: "\<forall>Z' k h. k : Z' \<rightarrow> Y \<and> h : Z' \<rightarrow> X \<and> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h \<longrightarrow>
      (\<exists>!j. j : Z' \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = k \<and> q0 \<circ>\<^sub>c j = h)"
    using pb unfolding is_pullback_def by auto
  show ?thesis
    unfolding monomorphism_def3[OF q1_type]
  proof (intro allI impI)
    fix u v Q
    assume "u : Q \<rightarrow> A \<and> v : Q \<rightarrow> A"
    then have u_type: "u : Q \<rightarrow> A" and v_type: "v : Q \<rightarrow> A" by auto
    assume equals: "q1 \<circ>\<^sub>c u = q1 \<circ>\<^sub>c v"

    have q1u_type: "q1 \<circ>\<^sub>c u : Q \<rightarrow> Y" using u_type q1_type comp_type by blast
    have q1v_type: "q1 \<circ>\<^sub>c v : Q \<rightarrow> Y" using v_type q1_type comp_type by blast
    have q0u_type: "q0 \<circ>\<^sub>c u : Q \<rightarrow> X" using u_type q0_type comp_type by blast
    have q0v_type: "q0 \<circ>\<^sub>c v : Q \<rightarrow> X" using v_type q0_type comp_type by blast

    have f_q1u_eq: "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u)"
    proof -
      have "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c u) = (f \<circ>\<^sub>c q1) \<circ>\<^sub>c u" using comp_associative2[OF u_type q1_type f_type] by simp
      also have "... = (g \<circ>\<^sub>c q0) \<circ>\<^sub>c u" using comm by simp
      also have "... = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u)" using comp_associative2[OF u_type q0_type g_type] by simp
      finally show ?thesis by simp
    qed
    have f_q1v_eq: "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v) = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)"
    proof -
      have "f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v) = (f \<circ>\<^sub>c q1) \<circ>\<^sub>c v" using comp_associative2[OF v_type q1_type f_type] by simp
      also have "... = (g \<circ>\<^sub>c q0) \<circ>\<^sub>c v" using comm by simp
      also have "... = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)" using comp_associative2[OF v_type q0_type g_type] by simp
      finally show ?thesis by simp
    qed

    have eqn1: "g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u) = f \<circ>\<^sub>c (q1 \<circ>\<^sub>c v)"
      using f_q1u_eq equals f_q1v_eq by simp

    have g_mono_prop: "\<forall>a b. a : Q \<rightarrow> X \<and> b : Q \<rightarrow> X \<longrightarrow> (g \<circ>\<^sub>c a = g \<circ>\<^sub>c b \<longrightarrow> a = b)"
      using g_mono monomorphism_def3[OF g_type] by auto
    have g_q0u_eq_g_q0v: "g \<circ>\<^sub>c (q0 \<circ>\<^sub>c u) = g \<circ>\<^sub>c (q0 \<circ>\<^sub>c v)" using eqn1 f_q1v_eq by simp
    have eqn2: "q0 \<circ>\<^sub>c u = q0 \<circ>\<^sub>c v"
      using g_mono_prop[rule_format] q0u_type q0v_type g_q0u_eq_g_q0v by auto

    have uniq_v: "\<exists>!j. j : Q \<rightarrow> A \<and> q1 \<circ>\<^sub>c j = q1 \<circ>\<^sub>c v \<and> q0 \<circ>\<^sub>c j = q0 \<circ>\<^sub>c v"
      using pb_uniq[rule_format, where Z'=Q and k="q1 \<circ>\<^sub>c v" and h="q0 \<circ>\<^sub>c v"] q1v_type q0v_type f_q1v_eq by auto
    then obtain j where j_type: "j : Q \<rightarrow> A"
        and j_unique: "\<forall>j'. (j' : Q \<rightarrow> A \<and> q1 \<circ>\<^sub>c j' = q1 \<circ>\<^sub>c v \<and> q0 \<circ>\<^sub>c j' = q0 \<circ>\<^sub>c v) \<longrightarrow> j' = j"
      by auto
    have v_matches: "v = j" using j_unique v_type by auto
    have u_matches: "u = j" using j_unique u_type eqn2 equals by auto
    show "u = v" using u_matches v_matches by simp
  qed
qed

subsection \<open>Fiber Over an Element and its Connection to the Fibered Product\<close>

text \<open>The definition below corresponds to Definition 2.2.6 in Halvorson.\<close>
definition fiber :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1{_}" [100,100]100) where
  "f\<^sup>-\<^sup>1{y} = f\<^sup>-\<^sup>1\<lparr>\<one>\<rparr>\<^bsub>y\<^esub>"

definition fiber_morphism :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "fiber_morphism(f, y) = left_cart_proj(domain(f), \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y)"

lemma fiber_morphism_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Y" and y_type: "y \<in>\<^sub>c Y"
  shows "fiber_morphism(f, y) : f\<^sup>-\<^sup>1{y} \<rightarrow> X"
proof -
  have y_mono: "monomorphism(y)" using element_monomorphism[OF y_type] by simp
  have subobj: "subobject_of(inverse_image(f, \<one>, y), inverse_image_subobject_mapping(f, \<one>, y), X)"
    using inverse_image_subobject[OF y_type f_type y_mono] by simp
  have subobj_type: "inverse_image_subobject_mapping(f, \<one>, y) : inverse_image(f, \<one>, y) \<rightarrow> X"
    using subobj unfolding subobject_of_def by auto
  have eq3: "fiber_morphism(f, y) = inverse_image_subobject_mapping(f, \<one>, y)"
    unfolding fiber_morphism_def inverse_image_subobject_mapping_def by simp
  show ?thesis unfolding fiber_def using subobj_type eq3 by simp
qed

lemma fiber_subset:
  assumes f_type: "f : X \<rightarrow> Y" and y_type: "y \<in>\<^sub>c Y"
  shows "subobject_of(f\<^sup>-\<^sup>1{y}, fiber_morphism(f, y), X)"
proof -
  have y_mono: "monomorphism(y)" using element_monomorphism[OF y_type] by simp
  have subobj: "subobject_of(inverse_image(f, \<one>, y), inverse_image_subobject_mapping(f, \<one>, y), X)"
    using inverse_image_subobject[OF y_type f_type y_mono] by simp
  have eq3: "fiber_morphism(f, y) = inverse_image_subobject_mapping(f, \<one>, y)"
    unfolding fiber_morphism_def inverse_image_subobject_mapping_def by simp
  show ?thesis unfolding fiber_def using subobj eq3 by simp
qed

lemma fiber_morphism_monomorphism:
  assumes f_type: "f : X \<rightarrow> Y" and y_type: "y \<in>\<^sub>c Y"
  shows "monomorphism(fiber_morphism(f, y))"
  using fiber_subset[OF f_type y_type] unfolding subobject_of_def by auto

lemma fiber_morphism_eq:
  assumes f_type: "f : X \<rightarrow> Y" and y_type: "y \<in>\<^sub>c Y"
  shows "f \<circ>\<^sub>c fiber_morphism(f, y) = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
proof -
  have y_mono: "monomorphism(y)" using element_monomorphism[OF y_type] by simp
  have dom_f: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
  have k_type: "inverse_image_mapping(f, \<one>, y) : (inverse_image(f, \<one>, y)) \<rightarrow> X \<times>\<^sub>c \<one>"
    using inverse_image_mapping_type[OF y_type f_type y_mono] by simp
  have lp_type: "left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<one>" by (rule right_cart_proj_type)

  have step1: "f \<circ>\<^sub>c fiber_morphism(f, y) = f \<circ>\<^sub>c (left_cart_proj(X, \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y))"
    unfolding fiber_morphism_def using dom_f by simp
  have step2: "f \<circ>\<^sub>c (left_cart_proj(X, \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y))
      = y \<circ>\<^sub>c (right_cart_proj(X, \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y))"
    using inverse_image_mapping_eq[OF y_type f_type y_mono] by simp
  have rpk_type: "right_cart_proj(X, \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y) : (inverse_image(f, \<one>, y)) \<rightarrow> \<one>"
    using rp_type k_type comp_type by blast
  have eq_via_term: "right_cart_proj(X, \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y) = \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
  proof -
    have same_dom: "right_cart_proj(X, \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y) : f\<^sup>-\<^sup>1{y} \<rightarrow> \<one>"
      using rpk_type unfolding fiber_def by simp
    show ?thesis using same_dom terminal_func_unique by auto
  qed
  have step3: "y \<circ>\<^sub>c (right_cart_proj(X, \<one>) \<circ>\<^sub>c inverse_image_mapping(f, \<one>, y)) = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
    using eq_via_term by simp
  show ?thesis using step1 step2 step3 by simp
qed

text \<open>The lemma below corresponds to Proposition 2.2.7 in Halvorson.\<close>
lemma not_surjective_has_some_empty_preimage:
  assumes p_type: "p : X \<rightarrow> Y" and p_not_surj: "\<not> surjective(p)"
  shows "\<exists>y. y \<in>\<^sub>c Y \<and> is_empty(p\<^sup>-\<^sup>1{y})"
proof -
  have surj_iff: "surjective(p) \<longleftrightarrow> (\<forall>y. y \<in>\<^sub>c Y \<longrightarrow> (\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y))"
    using surjective_def2[OF p_type] by simp
  have "\<not> (\<forall>y. y \<in>\<^sub>c Y \<longrightarrow> (\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y))" using p_not_surj surj_iff by simp
  then have "\<exists>y. y \<in>\<^sub>c Y \<and> \<not>(\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y)" by auto
  then obtain y0 where y0_type: "y0 \<in>\<^sub>c Y" and y0_prop: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> y0"
    by auto

  have not_nonempty: "\<not> nonempty(p\<^sup>-\<^sup>1{y0})"
  proof
    assume a1: "nonempty(p\<^sup>-\<^sup>1{y0})"
    obtain z where z_type: "z \<in>\<^sub>c p\<^sup>-\<^sup>1{y0}" using a1 nonempty_def by auto
    have fm_type: "fiber_morphism(p, y0) : p\<^sup>-\<^sup>1{y0} \<rightarrow> X" using fiber_morphism_type[OF p_type y0_type] by simp
    have fiber_z_type: "fiber_morphism(p, y0) \<circ>\<^sub>c z \<in>\<^sub>c X" using z_type fm_type comp_type by blast
    have contradiction: "p \<circ>\<^sub>c (fiber_morphism(p, y0) \<circ>\<^sub>c z) = y0"
    proof -
      have "p \<circ>\<^sub>c (fiber_morphism(p, y0) \<circ>\<^sub>c z) = (p \<circ>\<^sub>c fiber_morphism(p, y0)) \<circ>\<^sub>c z"
        using comp_associative2[OF z_type fm_type p_type] by simp
      also have "... = (y0 \<circ>\<^sub>c \<beta>\<^bsub>p\<^sup>-\<^sup>1{y0}\<^esub>) \<circ>\<^sub>c z" using fiber_morphism_eq[OF p_type y0_type] by simp
      also have "... = y0 \<circ>\<^sub>c (\<beta>\<^bsub>p\<^sup>-\<^sup>1{y0}\<^esub> \<circ>\<^sub>c z)"
        using comp_associative2[OF z_type terminal_func_type y0_type] by simp
      also have "... = y0 \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF z_type] by simp
      also have "... = y0" using id_right_unit2[OF y0_type] by simp
      finally show ?thesis by simp
    qed
    have "p \<circ>\<^sub>c (fiber_morphism(p, y0) \<circ>\<^sub>c z) \<noteq> y0" using y0_prop fiber_z_type by auto
    then show False using contradiction by simp
  qed
  have is_empty_fib: "is_empty(p\<^sup>-\<^sup>1{y0})" using not_nonempty unfolding nonempty_def is_empty_def by simp
  show ?thesis using y0_type is_empty_fib by auto
qed

lemma fiber_iso_fibered_prod:
  assumes f_type: "f : X \<rightarrow> Y" and y_type: "y : \<one> \<rightarrow> Y"
  shows "f\<^sup>-\<^sup>1{y} \<cong> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>y\<^esub> \<one>"
proof -
  have y_mono: "monomorphism(y)" using element_monomorphism[OF y_type] by simp
  have eq1: "equalizer(inverse_image(f, \<one>, y), inverse_image_mapping(f, \<one>, y), f \<circ>\<^sub>c left_cart_proj(X, \<one>), y \<circ>\<^sub>c right_cart_proj(X, \<one>))"
    using inverse_image_spec[OF y_type f_type y_mono] by simp
  have eq2: "equalizer(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>y\<^esub> \<one>, fibered_product_morphism(X, f, y, \<one>), f \<circ>\<^sub>c left_cart_proj(X, \<one>), y \<circ>\<^sub>c right_cart_proj(X, \<one>))"
    using fibered_product_spec[OF f_type y_type] by simp
  have "\<exists>k. k : inverse_image(f, \<one>, y) \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>y\<^esub> \<one>) \<and> isomorphism(k) \<and> inverse_image_mapping(f, \<one>, y) = fibered_product_morphism(X, f, y, \<one>) \<circ>\<^sub>c k"
    using equalizers_isomorphic[OF eq1 eq2] by simp
  then obtain k where k_type: "k : inverse_image(f, \<one>, y) \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>y\<^esub> \<one>)" and k_iso: "isomorphism(k)" by auto
  show ?thesis unfolding fiber_def is_isomorphic_def using k_type k_iso by auto
qed

lemma fib_prod_left_id_iso:
  assumes g_type: "g : Y \<rightarrow> X"
  shows "(X \<^bsub>id(X)\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<cong> Y"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have pb: "is_pullback(X \<^bsub>id(X)\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, Y, X, X,
      fibered_product_right_proj(X, id(X), g, Y), g, fibered_product_left_proj(X, id(X), g, Y), id(X))"
    using fibered_product_is_pullback[OF idX_type g_type] by simp
  have idX_iso: "isomorphism(id(X))" by (rule id_isomorphism)
  have idX_mono: "monomorphism(id(X))" using idX_iso iso_imp_epi_and_monic by auto
  have idX_epi: "epimorphism(id(X))" using idX_iso iso_imp_epi_and_monic by auto
  have mono: "monomorphism(fibered_product_right_proj(X, id(X), g, Y))"
    using pullback_of_mono_is_mono2[OF idX_type idX_mono pb] by simp
  have epi: "epimorphism(fibered_product_right_proj(X, id(X), g, Y))"
    using pullback_of_epi_is_epi2[OF idX_type idX_epi pb] by simp
  have iso: "isomorphism(fibered_product_right_proj(X, id(X), g, Y))"
    using epi_mon_is_iso[OF epi mono] by simp
  have rp_type: "fibered_product_right_proj(X, id(X), g, Y) : (X \<^bsub>id(X)\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> Y"
    using fibered_product_right_proj_type[OF idX_type g_type] by simp
  show ?thesis unfolding is_isomorphic_def using rp_type iso by auto
qed

lemma fib_prod_right_id_iso:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>id(Y)\<^esub> Y) \<cong> X"
proof -
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have pb: "is_pullback(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>id(Y)\<^esub> Y, Y, X, Y,
      fibered_product_right_proj(X, f, id(Y), Y), id(Y), fibered_product_left_proj(X, f, id(Y), Y), f)"
    using fibered_product_is_pullback[OF f_type idY_type] by simp
  have idY_iso: "isomorphism(id(Y))" by (rule id_isomorphism)
  have idY_mono: "monomorphism(id(Y))" using idY_iso iso_imp_epi_and_monic by auto
  have idY_epi: "epimorphism(id(Y))" using idY_iso iso_imp_epi_and_monic by auto
  have mono: "monomorphism(fibered_product_left_proj(X, f, id(Y), Y))"
    using pullback_of_mono_is_mono1[OF f_type idY_mono pb] by simp
  have epi: "epimorphism(fibered_product_left_proj(X, f, id(Y), Y))"
    using pullback_of_epi_is_epi1[OF idY_type idY_epi pb] by simp
  have iso: "isomorphism(fibered_product_left_proj(X, f, id(Y), Y))"
    using epi_mon_is_iso[OF epi mono] by simp
  have lp_type: "fibered_product_left_proj(X, f, id(Y), Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>id(Y)\<^esub> Y) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type idY_type] by simp
  show ?thesis unfolding is_isomorphic_def using lp_type iso by auto
qed

text \<open>The lemma below corresponds to the discussion at the top of page 42 in Halvorson.\<close>
lemma kernel_pair_connection:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> E"
  assumes g_epi: "epimorphism(g)"
  assumes h_g_eq_f: "h \<circ>\<^sub>c g = f"
  assumes g_eq: "g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
  assumes h_type: "h : E \<rightarrow> Y"
  shows "\<exists>! b. b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and>
    fibered_product_left_proj(E, h, h, E) \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) \<and>
    fibered_product_right_proj(E, h, h, E) \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) \<and>
    epimorphism(b)"
proof -
  have lpEE_type: "left_cart_proj(E, E) : E \<times>\<^sub>c E \<rightarrow> E" by (rule left_cart_proj_type)
  have rpEE_type: "right_cart_proj(E, E) : E \<times>\<^sub>c E \<rightarrow> E" by (rule right_cart_proj_type)
  have lpXX_type: "left_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXX_type: "right_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)
  have gg_type: "g \<times>\<^sub>f g : X \<times>\<^sub>c X \<rightarrow> E \<times>\<^sub>c E" using g_type cfunc_cross_prod_type by auto
  have m_type: "fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<times>\<^sub>c X"
    using fibered_product_morphism_type[OF f_type f_type] by simp
  have ggm_type: "(g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> E \<times>\<^sub>c E"
    using gg_type m_type comp_type by blast
  have fpmh_type: "fibered_product_morphism(E, h, h, E) : (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<rightarrow> E \<times>\<^sub>c E"
    using fibered_product_morphism_type[OF h_type h_type] by simp

  have lpXXm_type: "left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using lpXX_type m_type comp_type by blast
  have rpXXm_type: "right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using rpXX_type m_type comp_type by blast

  have left_chain: "(h \<circ>\<^sub>c left_cart_proj(E, E)) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)
      = f \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)"
  proof -
    have "(h \<circ>\<^sub>c left_cart_proj(E, E)) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))
        = h \<circ>\<^sub>c (left_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)))"
      using comp_associative2[OF ggm_type lpEE_type h_type] by simp
    also have "... = h \<circ>\<^sub>c ((left_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using comp_associative2[OF m_type gg_type lpEE_type] by simp
    also have "... = h \<circ>\<^sub>c ((g \<circ>\<^sub>c left_cart_proj(X, X)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using left_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
    also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)))"
      using comp_associative2[OF m_type lpXX_type g_type] by simp
    also have "... = (h \<circ>\<^sub>c g) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using comp_associative2[OF lpXXm_type g_type h_type] by simp
    also have "... = f \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using h_g_eq_f by simp
    also have "... = f \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)"
      unfolding fibered_product_left_proj_def by simp
    finally show ?thesis by simp
  qed

  have right_chain: "(h \<circ>\<^sub>c right_cart_proj(E, E)) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)
      = f \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
  proof -
    have "(h \<circ>\<^sub>c right_cart_proj(E, E)) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))
        = h \<circ>\<^sub>c (right_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)))"
      using comp_associative2[OF ggm_type rpEE_type h_type] by simp
    also have "... = h \<circ>\<^sub>c ((right_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using comp_associative2[OF m_type gg_type rpEE_type] by simp
    also have "... = h \<circ>\<^sub>c ((g \<circ>\<^sub>c right_cart_proj(X, X)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using right_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
    also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)))"
      using comp_associative2[OF m_type rpXX_type g_type] by simp
    also have "... = (h \<circ>\<^sub>c g) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using comp_associative2[OF rpXXm_type g_type h_type] by simp
    also have "... = f \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using h_g_eq_f by simp
    also have "... = f \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
      unfolding fibered_product_right_proj_def by simp
    finally show ?thesis by simp
  qed

  have gxg_fpmorph_eq: "(h \<circ>\<^sub>c left_cart_proj(E, E)) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)
          = (h \<circ>\<^sub>c right_cart_proj(E, E)) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
  proof -
    have f_fpl_eq_f_fpr: "f \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = f \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
      using fibered_product_proj_eq[OF f_type f_type] by simp
    show ?thesis using left_chain right_chain f_fpl_eq_f_fpr by simp
  qed

  have hlpEE_type: "h \<circ>\<^sub>c left_cart_proj(E, E) : E \<times>\<^sub>c E \<rightarrow> Y" using lpEE_type h_type comp_type by blast
  have hrpEE_type: "h \<circ>\<^sub>c right_cart_proj(E, E) : E \<times>\<^sub>c E \<rightarrow> Y" using rpEE_type h_type comp_type by blast

  have h_equalizer: "equalizer(E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E, fibered_product_morphism(E, h, h, E), h \<circ>\<^sub>c left_cart_proj(E, E), h \<circ>\<^sub>c right_cart_proj(E, E))"
    using fibered_product_morphism_equalizer[OF h_type h_type] by simp

  have h_uniq: "\<forall>j F. j : F \<rightarrow> E \<times>\<^sub>c E \<and> (h \<circ>\<^sub>c left_cart_proj(E, E)) \<circ>\<^sub>c j = (h \<circ>\<^sub>c right_cart_proj(E, E)) \<circ>\<^sub>c j \<longrightarrow>
      (\<exists>!k. k : F \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and> fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c k = j)"
    using h_equalizer equalizer_def2[OF hlpEE_type hrpEE_type fpmh_type] by auto

  have ex1b: "\<exists>!b. b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and>
      fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
    using h_uniq[rule_format, where F="X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" and j="(g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"]
      ggm_type gxg_fpmorph_eq by auto
  then obtain b where b_type: "b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E)"
      and b_eq: "fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
      and b_unique: "\<forall>b2. (b2 : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and>
          fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b2 = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<longrightarrow> b2 = b"
    by auto

  have fpl_Ehh_b_eq: "fibered_product_left_proj(E, h, h, E) \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)"
  proof -
    have "fibered_product_left_proj(E, h, h, E) \<circ>\<^sub>c b = (left_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c b"
      unfolding fibered_product_left_proj_def by simp
    also have "... = left_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b)"
      using comp_associative2[OF b_type fpmh_type lpEE_type] by simp
    also have "... = left_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using b_eq by simp
    also have "... = (left_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
      using comp_associative2[OF m_type gg_type lpEE_type] by simp
    also have "... = (g \<circ>\<^sub>c left_cart_proj(X, X)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
      using left_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
    also have "... = g \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using comp_associative2[OF m_type lpXX_type g_type] by simp
    also have "... = g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)"
      unfolding fibered_product_left_proj_def by simp
    finally show ?thesis by simp
  qed

  have fpr_Ehh_b_eq: "fibered_product_right_proj(E, h, h, E) \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
  proof -
    have "fibered_product_right_proj(E, h, h, E) \<circ>\<^sub>c b = (right_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c b"
      unfolding fibered_product_right_proj_def by simp
    also have "... = right_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b)"
      using comp_associative2[OF b_type fpmh_type rpEE_type] by simp
    also have "... = right_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using b_eq by simp
    also have "... = (right_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
      using comp_associative2[OF m_type gg_type rpEE_type] by simp
    also have "... = (g \<circ>\<^sub>c right_cart_proj(X, X)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
      using right_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
    also have "... = g \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      using comp_associative2[OF m_type rpXX_type g_type] by simp
    also have "... = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
      unfolding fibered_product_right_proj_def by simp
    finally show ?thesis by simp
  qed

  have surj_g: "surjective(g)" using epi_is_surj[OF g_type g_epi] by simp
  have surj_gg: "surjective(g \<times>\<^sub>f g)" using cfunc_cross_prod_surj[OF g_type g_type surj_g surj_g] by simp
  have epi_gg: "epimorphism(g \<times>\<^sub>f g)" using surjective_is_epimorphism[OF surj_gg] by simp

  have big_pb: "is_pullback(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, X \<times>\<^sub>c X, E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E, E \<times>\<^sub>c E,
      fibered_product_morphism(X, f, f, X), g \<times>\<^sub>f g, b, fibered_product_morphism(E, h, h, E))"
    unfolding is_pullback_def
  proof (intro conjI)
    show "fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<times>\<^sub>c X" by (rule m_type)
    show "g \<times>\<^sub>f g : X \<times>\<^sub>c X \<rightarrow> E \<times>\<^sub>c E" by (rule gg_type)
    show "b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E)" by (rule b_type)
    show "fibered_product_morphism(E, h, h, E) : (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<rightarrow> E \<times>\<^sub>c E" by (rule fpmh_type)
    show "(g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X) = fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b"
      using b_eq by simp
    show "\<forall> Z k j. (k : Z \<rightarrow> X \<times>\<^sub>c X \<and> j : Z \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and> (g \<times>\<^sub>f g) \<circ>\<^sub>c k = fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j) \<longrightarrow>
        (\<exists>! l. l : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c l = k \<and> b \<circ>\<^sub>c l = j)"
    proof (intro allI impI)
      fix Z k j
      assume "k : Z \<rightarrow> X \<times>\<^sub>c X \<and> j : Z \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and> (g \<times>\<^sub>f g) \<circ>\<^sub>c k = fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j"
      then have k_type: "k : Z \<rightarrow> X \<times>\<^sub>c X" and j_type: "j : Z \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E)"
          and k_h_eq: "(g \<times>\<^sub>f g) \<circ>\<^sub>c k = fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j" by auto

      have lpXXk_type: "left_cart_proj(X, X) \<circ>\<^sub>c k : Z \<rightarrow> X" using k_type lpXX_type comp_type by blast
      have rpXXk_type: "right_cart_proj(X, X) \<circ>\<^sub>c k : Z \<rightarrow> X" using k_type rpXX_type comp_type by blast
      have ggk_type: "(g \<times>\<^sub>f g) \<circ>\<^sub>c k : Z \<rightarrow> E \<times>\<^sub>c E" using k_type gg_type comp_type by blast
      have fpmhj_type: "fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j : Z \<rightarrow> E \<times>\<^sub>c E" using j_type fpmh_type comp_type by blast

      have lpEEfpmh_type: "left_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E) : (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<rightarrow> E"
        using lpEE_type fpmh_type comp_type by blast
      have rpEEfpmh_type: "right_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E) : (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<rightarrow> E"
        using rpEE_type fpmh_type comp_type by blast

      have left_k_right_k_eq: "f \<circ>\<^sub>c left_cart_proj(X, X) \<circ>\<^sub>c k = f \<circ>\<^sub>c right_cart_proj(X, X) \<circ>\<^sub>c k"
      proof -
        have h_eq_core: "(h \<circ>\<^sub>c left_cart_proj(E, E)) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)
            = (h \<circ>\<^sub>c right_cart_proj(E, E)) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)"
          using equalizer_eq[OF hlpEE_type hrpEE_type fpmh_type h_equalizer] by simp

        have inner_l: "g \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c k) = left_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c k)"
        proof -
          have "left_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c k) = (left_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c k"
            using comp_associative2[OF k_type gg_type lpEE_type] by simp
          also have "... = (g \<circ>\<^sub>c left_cart_proj(X, X)) \<circ>\<^sub>c k"
            using left_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
          also have "... = g \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c k)"
            using comp_associative2[OF k_type lpXX_type g_type] by simp
          finally show ?thesis by simp
        qed

        have inner_r: "right_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c k) = g \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c k)"
        proof -
          have "right_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c k) = (right_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c k"
            using comp_associative2[OF k_type gg_type rpEE_type] by simp
          also have "... = (g \<circ>\<^sub>c right_cart_proj(X, X)) \<circ>\<^sub>c k"
            using right_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
          also have "... = g \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c k)"
            using comp_associative2[OF k_type rpXX_type g_type] by simp
          finally show ?thesis by simp
        qed

        have "f \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c k) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c k)"
          using h_g_eq_f by simp
        also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c k))"
          using comp_associative2[OF lpXXk_type g_type h_type] by simp
        also have "... = h \<circ>\<^sub>c (left_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c k))"
          using inner_l by simp
        also have "... = h \<circ>\<^sub>c (left_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j))"
          using k_h_eq by simp
        also have "... = h \<circ>\<^sub>c ((left_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c j)"
          using comp_associative2[OF j_type fpmh_type lpEE_type] by simp
        also have "... = (h \<circ>\<^sub>c (left_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E))) \<circ>\<^sub>c j"
          using comp_associative2[OF j_type lpEEfpmh_type h_type] by simp
        also have "... = ((h \<circ>\<^sub>c left_cart_proj(E, E)) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c j"
          using comp_associative2[OF fpmh_type lpEE_type h_type] by simp
        also have "... = ((h \<circ>\<^sub>c right_cart_proj(E, E)) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c j"
          using h_eq_core by simp
        also have "... = (h \<circ>\<^sub>c (right_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E))) \<circ>\<^sub>c j"
          using comp_associative2[OF fpmh_type rpEE_type h_type] by simp
        also have "... = h \<circ>\<^sub>c ((right_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c j)"
          using comp_associative2[OF j_type rpEEfpmh_type h_type] by simp
        also have "... = h \<circ>\<^sub>c (right_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j))"
          using comp_associative2[OF j_type fpmh_type rpEE_type] by simp
        also have "... = h \<circ>\<^sub>c (right_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c k))"
          using k_h_eq by simp
        also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c k))"
          using inner_r by simp
        also have "... = (h \<circ>\<^sub>c g) \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c k)"
          using comp_associative2[OF rpXXk_type g_type h_type] by simp
        also have "... = f \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c k)"
          using h_g_eq_f by simp
        finally show ?thesis by simp
      qed

      have X_kern_pb: "is_pullback(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, X, X, Y,
          fibered_product_right_proj(X, f, f, X), f, fibered_product_left_proj(X, f, f, X), f)"
        using fibered_product_is_pullback[OF f_type f_type] by simp
      have X_kern_uniq: "\<forall>Z' k' h'. k' : Z' \<rightarrow> X \<and> h' : Z' \<rightarrow> X \<and> f \<circ>\<^sub>c k' = f \<circ>\<^sub>c h' \<longrightarrow>
          (\<exists>!l. l : Z' \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c l = k' \<and> fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c l = h')"
        using X_kern_pb unfolding is_pullback_def by auto

      have left_k_right_k_eq': "f \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c k) = f \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c k)"
        using left_k_right_k_eq by simp
      have ex1z: "\<exists>!l. l : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c l = right_cart_proj(X, X) \<circ>\<^sub>c k
          \<and> fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c l = left_cart_proj(X, X) \<circ>\<^sub>c k"
        using X_kern_uniq[rule_format, where Z'=Z and k'="right_cart_proj(X, X) \<circ>\<^sub>c k" and h'="left_cart_proj(X, X) \<circ>\<^sub>c k"]
          rpXXk_type lpXXk_type left_k_right_k_eq' by auto
      then obtain z where z_type: "z : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
          and k_right_eq: "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c z = right_cart_proj(X, X) \<circ>\<^sub>c k"
          and k_left_eq: "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c z = left_cart_proj(X, X) \<circ>\<^sub>c k"
        by auto

      have k_eq: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z = k"
      proof -
        have mz_type: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z : Z \<rightarrow> X \<times>\<^sub>c X" using z_type m_type comp_type by blast
        have lp_mz: "left_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z) = left_cart_proj(X, X) \<circ>\<^sub>c k"
        proof -
          have "left_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z) = (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c z"
            using comp_associative2[OF z_type m_type lpXX_type] by simp
          also have "... = fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c z" unfolding fibered_product_left_proj_def by simp
          also have "... = left_cart_proj(X, X) \<circ>\<^sub>c k" using k_left_eq by simp
          finally show ?thesis by simp
        qed
        have rp_mz: "right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z) = right_cart_proj(X, X) \<circ>\<^sub>c k"
        proof -
          have "right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z) = (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c z"
            using comp_associative2[OF z_type m_type rpXX_type] by simp
          also have "... = fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c z" unfolding fibered_product_right_proj_def by simp
          also have "... = right_cart_proj(X, X) \<circ>\<^sub>c k" using k_right_eq by simp
          finally show ?thesis by simp
        qed
        show ?thesis using cart_prod_eq[OF mz_type k_type] lp_mz rp_mz by auto
      qed

      have bz_eq_j: "b \<circ>\<^sub>c z = j"
      proof -
        have bz_type: "b \<circ>\<^sub>c z : Z \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E)" using z_type b_type comp_type by blast
        have fpm_bz_eq: "fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c (b \<circ>\<^sub>c z) = fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j"
        proof -
          have "fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c (b \<circ>\<^sub>c z) = (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b) \<circ>\<^sub>c z"
            using comp_associative2[OF z_type b_type fpmh_type] by simp
          also have "... = ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c z" using b_eq by simp
          also have "... = (g \<times>\<^sub>f g) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z)"
            using comp_associative2[OF z_type m_type gg_type] by simp
          also have "... = (g \<times>\<^sub>f g) \<circ>\<^sub>c k" using k_eq by simp
          also have "... = fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c j" using k_h_eq by simp
          finally show ?thesis by simp
        qed
        have fpmh_mono: "monomorphism(fibered_product_morphism(E, h, h, E))"
          using fibered_product_morphism_monomorphism[OF h_type h_type] by simp
        have fpmh_mono_prop: "\<forall>a b'. a : Z \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and> b' : Z \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<longrightarrow>
            (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c a = fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b' \<longrightarrow> a = b')"
          using fpmh_mono monomorphism_def3[OF fpmh_type] by auto
        show ?thesis using fpmh_mono_prop[rule_format] bz_type j_type fpm_bz_eq by auto
      qed

      show "\<exists>!l. l : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c l = k \<and> b \<circ>\<^sub>c l = j"
      proof (rule ex1I[where a=z])
        show "z : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z = k \<and> b \<circ>\<^sub>c z = j"
          using z_type k_eq bz_eq_j by simp
      next
        fix y assume "y : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c y = k \<and> b \<circ>\<^sub>c y = j"
        then have y_type: "y : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)" and y_eq: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c y = k" by auto
        have m_mono: "monomorphism(fibered_product_morphism(X, f, f, X))"
          using fibered_product_morphism_monomorphism[OF f_type f_type] by simp
        have m_mono_prop: "\<forall>a b'. a : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> b' : Z \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<longrightarrow>
            (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c a = fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c b' \<longrightarrow> a = b')"
          using m_mono monomorphism_def3[OF m_type] by auto
        have "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c y = fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z"
          using y_eq k_eq by simp
        then show "y = z" using m_mono_prop[rule_format] y_type z_type by auto
      qed
    qed
  qed

  have b_epi: "epimorphism(b)" using pullback_of_epi_is_epi1[OF gg_type epi_gg big_pb] by simp

  show ?thesis
  proof (rule ex1I[where a=b])
    show "b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and>
        fibered_product_left_proj(E, h, h, E) \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) \<and>
        fibered_product_right_proj(E, h, h, E) \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) \<and>
        epimorphism(b)"
      using b_type fpl_Ehh_b_eq fpr_Ehh_b_eq b_epi by simp
  next
    fix b'
    assume "b' : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) \<and>
        fibered_product_left_proj(E, h, h, E) \<circ>\<^sub>c b' = g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) \<and>
        fibered_product_right_proj(E, h, h, E) \<circ>\<^sub>c b' = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) \<and>
        epimorphism(b')"
    then have b'_type: "b' : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E)"
        and b'_left: "fibered_product_left_proj(E, h, h, E) \<circ>\<^sub>c b' = g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)"
        and b'_right: "fibered_product_right_proj(E, h, h, E) \<circ>\<^sub>c b' = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
      by auto

    have fpmb'_eq: "fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b' = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
    proof -
      have lp_eq: "left_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b')
          = left_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      proof -
        have "left_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b') = (left_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c b'"
          using comp_associative2[OF b'_type fpmh_type lpEE_type] by simp
        also have "... = fibered_product_left_proj(E, h, h, E) \<circ>\<^sub>c b'" unfolding fibered_product_left_proj_def by simp
        also have "... = g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)" using b'_left by simp
        also have "... = g \<circ>\<^sub>c (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
          unfolding fibered_product_left_proj_def by simp
        also have "... = (g \<circ>\<^sub>c left_cart_proj(X, X)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
          using comp_associative2[OF m_type lpXX_type g_type] by simp
        also have "... = (left_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
          using left_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
        also have "... = left_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
          using comp_associative2[OF m_type gg_type lpEE_type] by simp
        finally show ?thesis by simp
      qed
      have rp_eq: "right_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b')
          = right_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
      proof -
        have "right_cart_proj(E, E) \<circ>\<^sub>c (fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b') = (right_cart_proj(E, E) \<circ>\<^sub>c fibered_product_morphism(E, h, h, E)) \<circ>\<^sub>c b'"
          using comp_associative2[OF b'_type fpmh_type rpEE_type] by simp
        also have "... = fibered_product_right_proj(E, h, h, E) \<circ>\<^sub>c b'" unfolding fibered_product_right_proj_def by simp
        also have "... = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)" using b'_right by simp
        also have "... = g \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
          unfolding fibered_product_right_proj_def by simp
        also have "... = (g \<circ>\<^sub>c right_cart_proj(X, X)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
          using comp_associative2[OF m_type rpXX_type g_type] by simp
        also have "... = (right_cart_proj(E, E) \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)"
          using right_cart_proj_cfunc_cross_prod[OF g_type g_type] by simp
        also have "... = right_cart_proj(E, E) \<circ>\<^sub>c ((g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X))"
          using comp_associative2[OF m_type gg_type rpEE_type] by simp
        finally show ?thesis by simp
      qed
      have fpmb'_ty: "fibered_product_morphism(E, h, h, E) \<circ>\<^sub>c b' : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> E \<times>\<^sub>c E"
        using b'_type fpmh_type comp_type by blast
      show ?thesis using cart_prod_eq[OF fpmb'_ty ggm_type] lp_eq rp_eq by auto
    qed
    show "b' = b" using b_unique b'_type fpmb'_eq by auto
  qed
qed

subsection \<open>Set Subtraction\<close>

text \<open>HOL's @{text set_subtraction} and @{text complement_morphism} are defined via @{text SOME}
  applied to @{text "Y \<setminus> (X,m)"}, a @{text "cset \<times> (cset \<times> cfunc)"} bundle with no FOL equivalent;
  following the tuple-flattening convention used throughout this file we drop the redundant @{text
  Y}/@{text X} components (recoverable as the domain/codomain of @{text m}, exactly as @{text
  graph}/@{text graph_morph} already do). Crucially, HOL's @{text SOME} expression depends only on
  @{text Y} and @{text "characteristic_func (snd X)"} -- NOT on @{text X} or @{text m} themselves --
  so two different monics sharing the same characteristic function are guaranteed the same @{text
  "SOME"}-witness (this is exactly what @{text set_subtraction_right_iso} below exploits). To
  preserve this extensionality property under Skolemization, @{text set_subtraction}/@{text
  complement_morphism} are NOT axiomatized directly as functions of the mono @{text m} (which would
  only give a witness per-@{text m}, with no guarantee of agreement across different @{text m}'s
  sharing a characteristic function); instead the primitive Skolemization is over the characteristic
  function @{text \<chi>} itself, and @{text set_subtraction}/@{text complement_morphism} are then defined
  as the composition of that primitive with @{text characteristic_func}.\<close>
axiomatization
  set_subtraction_chi :: "cfunc \<Rightarrow> cset" and
  complement_chi :: "cfunc \<Rightarrow> cfunc"
where
  complement_chi_spec: "\<chi> : Y \<rightarrow> \<Omega> \<Longrightarrow>
    equalizer(set_subtraction_chi(\<chi>), complement_chi(\<chi>), \<chi>, \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)"

definition set_subtraction :: "cfunc \<Rightarrow> cset" where
  "set_subtraction(m) = set_subtraction_chi(characteristic_func(m))"

definition complement_morphism :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>c" [1000]) where
  "m\<^sup>c = complement_chi(characteristic_func(m))"

lemma set_subtraction_cong:
  assumes "characteristic_func(m1) = characteristic_func(m2)"
  shows "set_subtraction(m1) = set_subtraction(m2)"
  unfolding set_subtraction_def using assms by simp

lemma complement_morphism_cong:
  assumes "characteristic_func(m1) = characteristic_func(m2)"
  shows "m1\<^sup>c = m2\<^sup>c"
  unfolding complement_morphism_def using assms by simp

lemma complement_morphism_equalizer:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "equalizer(set_subtraction(m), m\<^sup>c, characteristic_func(m), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
  unfolding set_subtraction_def complement_morphism_def
  using complement_chi_spec[OF characteristic_func_type[OF m_type m_mono]] by simp

lemma complement_morphism_type[type_rule]:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "m\<^sup>c : set_subtraction(m) \<rightarrow> X"
proof -
  have chi_type: "characteristic_func(m) : X \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have eq: "equalizer(set_subtraction(m), m\<^sup>c, characteristic_func(m), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
    using complement_morphism_equalizer[OF m_type m_mono] by simp
  obtain X' Y' where chi_type': "characteristic_func(m) : X' \<rightarrow> Y'" and mc_type': "m\<^sup>c : set_subtraction(m) \<rightarrow> X'"
    using eq unfolding equalizer_def by auto
  have "X' = X" using chi_type chi_type' unfolding cfunc_type_def by auto
  then show ?thesis using mc_type' by simp
qed

lemma complement_morphism_mono:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "monomorphism(m\<^sup>c)"
  using complement_morphism_equalizer[OF m_type m_mono] equalizer_is_monomorphism by blast

lemma complement_morphism_eq:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
  shows "characteristic_func(m) \<circ>\<^sub>c m\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m\<^sup>c"
  using complement_morphism_equalizer[OF m_type m_mono] unfolding equalizer_def by auto

lemma characteristic_func_true_not_complement_member:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c X"
  assumes chi_true: "characteristic_func(m) \<circ>\<^sub>c x = \<t>"
  shows "\<not> relative_member(x, X, set_subtraction(m), m\<^sup>c)"
proof
  assume in_complement: "relative_member(x, X, set_subtraction(m), m\<^sup>c)"
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> X" using complement_morphism_type[OF m_type m_mono] by simp
  have chi_type: "characteristic_func(m) : X \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have fbX_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using terminal_func_type false_func_type comp_type by blast
  have x_factorsthru: "x factorsthru m\<^sup>c" using in_complement unfolding relative_member_def by auto
  obtain x' where x'_type: "x' \<in>\<^sub>c set_subtraction(m)" and x'_def: "m\<^sup>c \<circ>\<^sub>c x' = x"
    using factors_through_def2[OF x_type mc_type] x_factorsthru by auto
  have chi_mc_eq: "characteristic_func(m) \<circ>\<^sub>c m\<^sup>c = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m\<^sup>c"
    using complement_morphism_eq[OF m_type m_mono] by simp
  have "characteristic_func(m) \<circ>\<^sub>c x = characteristic_func(m) \<circ>\<^sub>c (m\<^sup>c \<circ>\<^sub>c x')" using x'_def by simp
  also have "... = (characteristic_func(m) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
    using comp_associative2[OF x'_type mc_type chi_type] by simp
  also have "... = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'" using chi_mc_eq by simp
  also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c (m\<^sup>c \<circ>\<^sub>c x')"
    using comp_associative2[OF x'_type mc_type fbX_type] by simp
  also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x" using x'_def by simp
  also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)"
    using comp_associative2[OF x_type terminal_func_type false_func_type] by simp
  also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF x_type] by simp
  also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
  finally have chi_x_eq_f: "characteristic_func(m) \<circ>\<^sub>c x = \<f>" by simp
  show False using chi_true chi_x_eq_f true_false_distinct by simp
qed

lemma characteristic_func_false_complement_member:
  assumes m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c X"
  assumes chi_false: "characteristic_func(m) \<circ>\<^sub>c x = \<f>"
  shows "relative_member(x, X, set_subtraction(m), m\<^sup>c)"
proof -
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> X" using complement_morphism_type[OF m_type m_mono] by simp
  have mc_mono: "monomorphism(m\<^sup>c)" using complement_morphism_mono[OF m_type m_mono] by simp
  have chi_type: "characteristic_func(m) : X \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have fbX_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<Omega>" using terminal_func_type false_func_type comp_type by blast
  have x_equalizes: "characteristic_func(m) \<circ>\<^sub>c x = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x"
  proof -
    have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)"
      using comp_associative2[OF x_type terminal_func_type false_func_type] by simp
    also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF x_type] by simp
    also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
    finally show ?thesis using chi_false by simp
  qed
  have eq: "equalizer(set_subtraction(m), m\<^sup>c, characteristic_func(m), \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)"
    using complement_morphism_equalizer[OF m_type m_mono] by simp
  have ex1: "\<exists>! k. k : \<one> \<rightarrow> set_subtraction(m) \<and> m\<^sup>c \<circ>\<^sub>c k = x"
    using similar_equalizers[OF chi_type fbX_type mc_type eq x_type x_equalizes] by simp
  then obtain x' where x'_type: "x' \<in>\<^sub>c set_subtraction(m)" and x'_def: "m\<^sup>c \<circ>\<^sub>c x' = x" by auto
  have x_factorsthru: "x factorsthru m\<^sup>c" using factors_through_def2[OF x_type mc_type] x'_type x'_def by auto
  show ?thesis unfolding relative_member_def using x_type mc_mono mc_type x_factorsthru by auto
qed

lemma in_complement_not_in_subset:
  assumes m_type: "m : X \<rightarrow> Y" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c Y"
  assumes in_comp: "relative_member(x, Y, set_subtraction(m), m\<^sup>c)"
  shows "\<not> relative_member(x, Y, X, m)"
proof
  assume in_sub: "relative_member(x, Y, X, m)"
  have chi_true: "characteristic_func(m) \<circ>\<^sub>c x = \<t>"
    using rel_mem_char_func_true[OF m_type m_mono x_type in_sub] by simp
  have "\<not> relative_member(x, Y, set_subtraction(m), m\<^sup>c)"
    using characteristic_func_true_not_complement_member[OF m_type m_mono x_type chi_true] by simp
  then show False using in_comp by simp
qed

lemma not_in_subset_in_complement:
  assumes m_type: "m : X \<rightarrow> Y" and m_mono: "monomorphism(m)" and x_type: "x \<in>\<^sub>c Y"
  assumes not_in_sub: "\<not> relative_member(x, Y, X, m)"
  shows "relative_member(x, Y, set_subtraction(m), m\<^sup>c)"
proof -
  have chi_false: "characteristic_func(m) \<circ>\<^sub>c x = \<f>"
    using not_rel_mem_char_func_false[OF m_type m_mono x_type not_in_sub] by simp
  show ?thesis using characteristic_func_false_complement_member[OF m_type m_mono x_type chi_false] by simp
qed

lemma complement_disjoint:
  assumes m_type: "m : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  assumes x_type: "x \<in>\<^sub>c X" and x'_type: "x' \<in>\<^sub>c set_subtraction(m)"
  shows "m \<circ>\<^sub>c x \<noteq> m\<^sup>c \<circ>\<^sub>c x'"
proof
  assume eq: "m \<circ>\<^sub>c x = m\<^sup>c \<circ>\<^sub>c x'"
  have chi_type: "characteristic_func(m) : Y \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> Y" using complement_morphism_type[OF m_type m_mono] by simp
  have mcx'_type: "m\<^sup>c \<circ>\<^sub>c x' : \<one> \<rightarrow> Y" using x'_type mc_type comp_type by blast
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have bY_type: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by (rule terminal_func_type)
  have fbYmc_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<Omega>" using bY_type false_func_type comp_type by blast
  have s1: "(characteristic_func(m) \<circ>\<^sub>c m) \<circ>\<^sub>c x = (characteristic_func(m) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
  proof -
    have l: "characteristic_func(m) \<circ>\<^sub>c (m \<circ>\<^sub>c x) = (characteristic_func(m) \<circ>\<^sub>c m) \<circ>\<^sub>c x"
      using comp_associative2[OF x_type m_type chi_type] by simp
    have r: "characteristic_func(m) \<circ>\<^sub>c (m\<^sup>c \<circ>\<^sub>c x') = (characteristic_func(m) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
      using comp_associative2[OF x'_type mc_type chi_type] by simp
    have "characteristic_func(m) \<circ>\<^sub>c (m \<circ>\<^sub>c x) = characteristic_func(m) \<circ>\<^sub>c (m\<^sup>c \<circ>\<^sub>c x')" using eq by simp
    then show ?thesis using l r by simp
  qed
  have s2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x'"
    using s1 characteristic_func_eq[OF m_type m_mono] complement_morphism_eq[OF m_type m_mono] by simp
  have l2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = \<t>"
  proof -
    have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c x = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)" using comp_associative2[OF x_type bX_type true_func_type] by simp
    also have "... = \<t> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF x_type] by simp
    also have "... = \<t>" using id_right_unit2[OF true_func_type] by simp
    finally show ?thesis by simp
  qed
  have r2: "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x' = \<f>"
  proof -
    have "((\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c x' = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c (m\<^sup>c \<circ>\<^sub>c x')"
      using comp_associative2[OF x'_type mc_type fbYmc_type] by simp
    also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c (m\<^sup>c \<circ>\<^sub>c x'))"
      using comp_associative2[OF mcx'_type bY_type false_func_type] by simp
    also have "... = \<f> \<circ>\<^sub>c id(\<one>)" using terminal_func_comp_elem[OF mcx'_type] by simp
    also have "... = \<f>" using id_right_unit2[OF false_func_type] by simp
    finally show ?thesis by simp
  qed
  have "\<t> = \<f>" using s2 l2 r2 by simp
  then show False using true_false_distinct by simp
qed

lemma set_subtraction_right_iso:
  assumes m_type: "m : A \<rightarrow> C" and m_mono: "monomorphism(m)"
  assumes i_type: "i : B \<rightarrow> A" and i_iso: "isomorphism(i)"
  shows "set_subtraction(m) = set_subtraction(m \<circ>\<^sub>c i)"
proof -
  have i_mono: "monomorphism(i)" using i_iso iso_imp_epi_and_monic by auto
  have mi_type: "m \<circ>\<^sub>c i : B \<rightarrow> C" using i_type m_type comp_type by blast
  have cod_dom: "codomain(i) = domain(m)" using i_type m_type unfolding cfunc_type_def by auto
  have mi_mono: "monomorphism(m \<circ>\<^sub>c i)"
    using composition_of_monic_pair_is_monic[OF cod_dom i_mono m_mono] by simp
  have chim_type: "characteristic_func(m) : C \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have chimi_type: "characteristic_func(m \<circ>\<^sub>c i) : C \<rightarrow> \<Omega>" using characteristic_func_type[OF mi_type mi_mono] by simp

  have main_iff: "\<And>c. c \<in>\<^sub>c C \<Longrightarrow> (characteristic_func(m) \<circ>\<^sub>c c = \<t>) \<longleftrightarrow> (characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c = \<t>)"
  proof -
    fix c assume c_type: "c \<in>\<^sub>c C"
    have step1: "(characteristic_func(m) \<circ>\<^sub>c c = \<t>) \<longleftrightarrow> relative_member(c, C, A, m)"
    proof (rule iffI)
      assume "characteristic_func(m) \<circ>\<^sub>c c = \<t>"
      then show "relative_member(c, C, A, m)"
        using characteristic_func_true_relative_member[OF m_type m_mono c_type] by simp
    next
      assume "relative_member(c, C, A, m)"
      then show "characteristic_func(m) \<circ>\<^sub>c c = \<t>"
        using rel_mem_char_func_true[OF m_type m_mono c_type] by simp
    qed
    have step2: "relative_member(c, C, A, m) \<longleftrightarrow> (\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a)"
    proof (rule iffI)
      assume "relative_member(c, C, A, m)"
      then have "c factorsthru m" unfolding relative_member_def by auto
      then obtain a where a_type: "a : \<one> \<rightarrow> A" and a_eq: "m \<circ>\<^sub>c a = c"
        using factors_through_def2[OF c_type m_type] by auto
      show "\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a" using a_type a_eq by auto
    next
      assume "\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a"
      then obtain a where a_type: "a \<in>\<^sub>c A" and a_eq: "c = m \<circ>\<^sub>c a" by auto
      have "c factorsthru m" using factors_through_def2[OF c_type m_type] a_type a_eq by auto
      then show "relative_member(c, C, A, m)" unfolding relative_member_def using c_type m_mono m_type by auto
    qed
    have step3: "(\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a) \<longleftrightarrow> (\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b))"
    proof (rule iffI)
      assume "\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a"
      then obtain a where a_type: "a \<in>\<^sub>c A" and a_eq: "c = m \<circ>\<^sub>c a" by auto
      have iinv_type: "i\<^bold>\<inverse> : A \<rightarrow> B" using inverse_type[OF i_iso i_type] by simp
      obtain b where b_def: "b = i\<^bold>\<inverse> \<circ>\<^sub>c a" by simp
      have b_type: "b \<in>\<^sub>c B" unfolding b_def using a_type iinv_type comp_type by blast
      have "i \<circ>\<^sub>c b = i \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c a)" using b_def by simp
      also have "... = (i \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c a" using comp_associative2[OF a_type iinv_type i_type] by simp
      also have "... = id(A) \<circ>\<^sub>c a" using inv_right[OF i_iso i_type] by simp
      also have "... = a" using id_left_unit2[OF a_type] by simp
      finally have ib_eq_a: "i \<circ>\<^sub>c b = a" by simp
      have "c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)" using a_eq ib_eq_a by simp
      then show "\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)" using b_type by auto
    next
      assume "\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)"
      then obtain b where b_type: "b \<in>\<^sub>c B" and c_eq: "c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)" by auto
      have ib_type: "i \<circ>\<^sub>c b \<in>\<^sub>c A" using b_type i_type comp_type by blast
      show "\<exists> a. a \<in>\<^sub>c A \<and> c = m \<circ>\<^sub>c a" using ib_type c_eq by auto
    qed
    have step4: "(\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)) \<longleftrightarrow> (\<exists> b. b \<in>\<^sub>c B \<and> c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b)"
    proof (rule iffI)
      assume "\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)"
      then obtain b where b_type: "b \<in>\<^sub>c B" and c_eq: "c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)" by auto
      have assoc: "m \<circ>\<^sub>c (i \<circ>\<^sub>c b) = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b" using comp_associative2[OF b_type i_type m_type] by simp
      show "\<exists> b. b \<in>\<^sub>c B \<and> c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b" using b_type c_eq assoc by auto
    next
      assume "\<exists> b. b \<in>\<^sub>c B \<and> c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b"
      then obtain b where b_type: "b \<in>\<^sub>c B" and c_eq: "c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b" by auto
      have assoc: "m \<circ>\<^sub>c (i \<circ>\<^sub>c b) = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b" using comp_associative2[OF b_type i_type m_type] by simp
      show "\<exists> b. b \<in>\<^sub>c B \<and> c = m \<circ>\<^sub>c (i \<circ>\<^sub>c b)" using b_type c_eq assoc by auto
    qed
    have step5: "(\<exists> b. b \<in>\<^sub>c B \<and> c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b) \<longleftrightarrow> relative_member(c, C, B, m \<circ>\<^sub>c i)"
    proof (rule iffI)
      assume "\<exists> b. b \<in>\<^sub>c B \<and> c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b"
      then obtain b where b_type: "b \<in>\<^sub>c B" and c_eq: "c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b" by auto
      have "c factorsthru (m \<circ>\<^sub>c i)" using factors_through_def2[OF c_type mi_type] b_type c_eq by auto
      then show "relative_member(c, C, B, m \<circ>\<^sub>c i)" unfolding relative_member_def using c_type mi_mono mi_type by auto
    next
      assume "relative_member(c, C, B, m \<circ>\<^sub>c i)"
      then have "c factorsthru (m \<circ>\<^sub>c i)" unfolding relative_member_def by auto
      then obtain b where b_type: "b : \<one> \<rightarrow> B" and b_eq: "(m \<circ>\<^sub>c i) \<circ>\<^sub>c b = c"
        using factors_through_def2[OF c_type mi_type] by auto
      show "\<exists> b. b \<in>\<^sub>c B \<and> c = (m \<circ>\<^sub>c i) \<circ>\<^sub>c b" using b_type b_eq by auto
    qed
    have step6: "relative_member(c, C, B, m \<circ>\<^sub>c i) \<longleftrightarrow> (characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c = \<t>)"
    proof (rule iffI)
      assume "relative_member(c, C, B, m \<circ>\<^sub>c i)"
      then show "characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c = \<t>"
        using rel_mem_char_func_true[OF mi_type mi_mono c_type] by simp
    next
      assume "characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c = \<t>"
      then show "relative_member(c, C, B, m \<circ>\<^sub>c i)"
        using characteristic_func_true_relative_member[OF mi_type mi_mono c_type] by simp
    qed
    show "(characteristic_func(m) \<circ>\<^sub>c c = \<t>) \<longleftrightarrow> (characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c = \<t>)"
      using step1 step2 step3 step4 step5 step6 by simp
  qed

  have chi_eq: "characteristic_func(m) = characteristic_func(m \<circ>\<^sub>c i)"
  proof (rule one_separator[where X=C and Y="\<Omega>"])
    show "characteristic_func(m) : C \<rightarrow> \<Omega>" by (rule chim_type)
    show "characteristic_func(m \<circ>\<^sub>c i) : C \<rightarrow> \<Omega>" by (rule chimi_type)
    fix c assume c_type: "c : \<one> \<rightarrow> C"
    have chc_type: "characteristic_func(m) \<circ>\<^sub>c c \<in>\<^sub>c \<Omega>" using c_type chim_type comp_type by blast
    have chic_type: "characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c \<in>\<^sub>c \<Omega>" using c_type chimi_type comp_type by blast
    show "characteristic_func(m) \<circ>\<^sub>c c = characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c"
    proof (cases "characteristic_func(m) \<circ>\<^sub>c c = \<t>")
      case True
      then have "characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c = \<t>" using main_iff[OF c_type] by simp
      then show ?thesis using True by simp
    next
      case False
      then have f1: "characteristic_func(m) \<circ>\<^sub>c c = \<f>" using true_false_only_truth_values[OF chc_type] by auto
      have "characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c \<noteq> \<t>" using False main_iff[OF c_type] by simp
      then have f2: "characteristic_func(m \<circ>\<^sub>c i) \<circ>\<^sub>c c = \<f>" using true_false_only_truth_values[OF chic_type] by auto
      show ?thesis using f1 f2 by simp
    qed
  qed
  show ?thesis using set_subtraction_cong[OF chi_eq] by simp
qed

lemma set_subtraction_left_iso:
  assumes m_type: "m : C \<rightarrow> A" and m_mono: "monomorphism(m)"
  assumes i_type: "i : A \<rightarrow> B" and i_iso: "isomorphism(i)"
  shows "set_subtraction(m) \<cong> set_subtraction(i \<circ>\<^sub>c m)"
proof -
  have i_mono: "monomorphism(i)" using i_iso iso_imp_epi_and_monic by auto
  have im_type: "i \<circ>\<^sub>c m : C \<rightarrow> B" using m_type i_type comp_type by blast
  have cod_dom: "codomain(m) = domain(i)" using m_type i_type unfolding cfunc_type_def by auto
  have im_mono: "monomorphism(i \<circ>\<^sub>c m)"
    using composition_of_monic_pair_is_monic[OF cod_dom m_mono i_mono] by simp
  have chim_type: "characteristic_func(m) : A \<rightarrow> \<Omega>" using characteristic_func_type[OF m_type m_mono] by simp
  have chiim_type: "characteristic_func(i \<circ>\<^sub>c m) : B \<rightarrow> \<Omega>" using characteristic_func_type[OF im_type im_mono] by simp
  have mc_type: "m\<^sup>c : set_subtraction(m) \<rightarrow> A" using complement_morphism_type[OF m_type m_mono] by simp
  have imc_type2: "(i \<circ>\<^sub>c m)\<^sup>c : set_subtraction(i \<circ>\<^sub>c m) \<rightarrow> B" using complement_morphism_type[OF im_type im_mono] by simp
  have iinv_type: "i\<^bold>\<inverse> : B \<rightarrow> A" using inverse_type[OF i_iso i_type] by simp

  have chi_im_i_eq_chi_m: "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i = characteristic_func(m)"
  proof -
    have chiim_i_type: "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i : A \<rightarrow> \<Omega>" using i_type chiim_type comp_type by blast
    have tbA_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> : A \<rightarrow> \<Omega>" using terminal_func_type true_func_type comp_type by blast
    have comm: "(characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c m"
    proof -
      have l: "(characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c m = characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c m)"
        using comp_associative2[OF m_type i_type chiim_type] by simp
      have chi_im_eq: "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c m) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>C\<^esub>"
        using characteristic_func_eq[OF im_type im_mono] by simp
      have r: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c m)"
        using comp_associative2[OF m_type terminal_func_type true_func_type] by simp
      have bA_m_eq: "\<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c m = \<beta>\<^bsub>C\<^esub>" using terminal_func_comp[OF m_type] by simp
      show ?thesis using l chi_im_eq r bA_m_eq by simp
    qed
    have uniq: "\<forall> h F. (h : F \<rightarrow> A \<and> (characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c h) \<longrightarrow>
        (\<exists>!k. k : F \<rightarrow> C \<and> m \<circ>\<^sub>c k = h)"
    proof (intro allI impI)
      fix h F
      assume "h : F \<rightarrow> A \<and> (characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c h"
      then have h_type: "h : F \<rightarrow> A" and h_eq: "(characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c h = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c h" by auto
      have ih_type: "i \<circ>\<^sub>c h : F \<rightarrow> B" using h_type i_type comp_type by blast
      have h_eq': "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c h) = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c (i \<circ>\<^sub>c h)"
      proof -
        have s1: "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c h) = (characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c h"
          using comp_associative2[OF h_type i_type chiim_type] by simp
        have s2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c (i \<circ>\<^sub>c h) = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c (i \<circ>\<^sub>c h))"
          using comp_associative2[OF ih_type terminal_func_type true_func_type] by simp
        have s3: "\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c (i \<circ>\<^sub>c h) = \<beta>\<^bsub>F\<^esub>"
        proof -
          have "\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c (i \<circ>\<^sub>c h) = (\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c i) \<circ>\<^sub>c h" using comp_associative2[OF h_type i_type terminal_func_type] by simp
          also have "... = \<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c h" using terminal_func_comp[OF i_type] by simp
          also have "... = \<beta>\<^bsub>F\<^esub>" using terminal_func_comp[OF h_type] by simp
          finally show ?thesis by simp
        qed
        have s4: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c h = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c h)"
          using comp_associative2[OF h_type terminal_func_type true_func_type] by simp
        have s5: "\<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c h = \<beta>\<^bsub>F\<^esub>" using terminal_func_comp[OF h_type] by simp
        show ?thesis using s1 s2 s3 s4 s5 h_eq by simp
      qed
      have eqB: "equalizer(C, i \<circ>\<^sub>c m, characteristic_func(i \<circ>\<^sub>c m), \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>)"
        using monomorphism_equalizes_char_func[OF im_type im_mono] by simp
      have tbB_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub> : B \<rightarrow> \<Omega>" using terminal_func_type true_func_type comp_type by blast
      have uniqB: "\<forall> h' F'. (h' : F' \<rightarrow> B \<and> characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c h' = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c h') \<longrightarrow>
          (\<exists>! k. k : F' \<rightarrow> C \<and> (i \<circ>\<^sub>c m) \<circ>\<^sub>c k = h')"
        using eqB equalizer_def2[OF chiim_type tbB_type im_type] by simp
      have ex1j: "\<exists>! j. j : F \<rightarrow> C \<and> (i \<circ>\<^sub>c m) \<circ>\<^sub>c j = i \<circ>\<^sub>c h"
        using uniqB[rule_format, where F'=F and h'="i \<circ>\<^sub>c h"] ih_type h_eq' by auto
      then obtain j where j_type: "j : F \<rightarrow> C" and j_eq: "(i \<circ>\<^sub>c m) \<circ>\<^sub>c j = i \<circ>\<^sub>c h"
          and j_unique: "\<forall> j'. (j' : F \<rightarrow> C \<and> (i \<circ>\<^sub>c m) \<circ>\<^sub>c j' = i \<circ>\<^sub>c h) \<longrightarrow> j' = j" by auto
      have mj_type: "m \<circ>\<^sub>c j : F \<rightarrow> A" using j_type m_type comp_type by blast
      have i_mj_eq_ih: "i \<circ>\<^sub>c (m \<circ>\<^sub>c j) = i \<circ>\<^sub>c h"
      proof -
        have "i \<circ>\<^sub>c (m \<circ>\<^sub>c j) = (i \<circ>\<^sub>c m) \<circ>\<^sub>c j" using comp_associative2[OF j_type m_type i_type] by simp
        also have "... = i \<circ>\<^sub>c h" using j_eq by simp
        finally show ?thesis by simp
      qed
      have i_mono_uniq: "\<forall> g h' Ann. g : Ann \<rightarrow> A \<and> h' : Ann \<rightarrow> A \<longrightarrow> (i \<circ>\<^sub>c g = i \<circ>\<^sub>c h' \<longrightarrow> g = h')"
        using monomorphism_def3[OF i_type] i_mono by simp
      have mj_eq_h: "m \<circ>\<^sub>c j = h"
        using i_mono_uniq[rule_format, where g="m \<circ>\<^sub>c j" and h'=h and Ann=F] mj_type h_type i_mj_eq_ih by auto
      show "\<exists>! k. k : F \<rightarrow> C \<and> m \<circ>\<^sub>c k = h"
      proof (rule ex1I[where a=j])
        show "j : F \<rightarrow> C \<and> m \<circ>\<^sub>c j = h" using j_type mj_eq_h by simp
      next
        fix k assume "k : F \<rightarrow> C \<and> m \<circ>\<^sub>c k = h"
        then have k_type: "k : F \<rightarrow> C" and k_eq: "m \<circ>\<^sub>c k = h" by auto
        have "(i \<circ>\<^sub>c m) \<circ>\<^sub>c k = i \<circ>\<^sub>c h"
        proof -
          have "(i \<circ>\<^sub>c m) \<circ>\<^sub>c k = i \<circ>\<^sub>c (m \<circ>\<^sub>c k)" using comp_associative2[OF k_type m_type i_type] by simp
          also have "... = i \<circ>\<^sub>c h" using k_eq by simp
          finally show ?thesis by simp
        qed
        then show "k = j" using j_unique k_type by auto
      qed
    qed
    have target_eq: "equalizer(C, m, characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i, \<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>)"
      unfolding equalizer_def using chiim_i_type tbA_type m_type comm uniq by auto
    show ?thesis
      using characteristic_func_unique_from_equalizer[OF m_type m_mono chiim_i_type target_eq] by simp
  qed

  have step_eq: "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c) = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c)"
  proof -
    have lhs: "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c) = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>"
    proof -
      have "characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c) = (characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c m\<^sup>c"
        using comp_associative2[OF mc_type i_type chiim_type] by simp
      also have "... = characteristic_func(m) \<circ>\<^sub>c m\<^sup>c" using chi_im_i_eq_chi_m by simp
      also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c m\<^sup>c" using complement_morphism_eq[OF m_type m_mono] by simp
      also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c m\<^sup>c)" using comp_associative2[OF mc_type terminal_func_type false_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>" using terminal_func_comp[OF mc_type] by simp
      finally show ?thesis by simp
    qed
    have rhs: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c) = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>"
    proof -
      have imc_type: "i \<circ>\<^sub>c m\<^sup>c : set_subtraction(m) \<rightarrow> B" using mc_type i_type comp_type by blast
      have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c) = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c))"
        using comp_associative2[OF imc_type terminal_func_type false_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c ((\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c i) \<circ>\<^sub>c m\<^sup>c)" using comp_associative2[OF mc_type i_type terminal_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c m\<^sup>c)" using terminal_func_comp[OF i_type] by simp
      also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(m)\<^esub>" using terminal_func_comp[OF mc_type] by simp
      finally show ?thesis by simp
    qed
    show ?thesis using lhs rhs by simp
  qed

  have imc_type: "i \<circ>\<^sub>c m\<^sup>c : set_subtraction(m) \<rightarrow> B" using mc_type i_type comp_type by blast
  have im_equalizer: "equalizer(set_subtraction(i \<circ>\<^sub>c m), (i \<circ>\<^sub>c m)\<^sup>c, characteristic_func(i \<circ>\<^sub>c m), \<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>)"
    using complement_morphism_equalizer[OF im_type im_mono] by simp
  have fbB_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub> : B \<rightarrow> \<Omega>" using terminal_func_type false_func_type comp_type by blast
  have im_uniq: "\<forall> h F. (h : F \<rightarrow> B \<and> characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c h = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c h) \<longrightarrow>
      (\<exists>! k. k : F \<rightarrow> set_subtraction(i \<circ>\<^sub>c m) \<and> (i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c k = h)"
    using im_equalizer equalizer_def2[OF chiim_type fbB_type imc_type2] by simp
  have ex1i': "\<exists>! i'. i' : set_subtraction(m) \<rightarrow> set_subtraction(i \<circ>\<^sub>c m) \<and> (i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c i' = i \<circ>\<^sub>c m\<^sup>c"
    using im_uniq[rule_format, where F="set_subtraction(m)" and h="i \<circ>\<^sub>c m\<^sup>c"] imc_type step_eq by auto
  then obtain i' where i'_type: "i' : set_subtraction(m) \<rightarrow> set_subtraction(i \<circ>\<^sub>c m)"
      and i'_def: "(i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c i' = i \<circ>\<^sub>c m\<^sup>c" by auto

  have step_eq2: "characteristic_func(m) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c) = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)"
  proof -
    have iinvimc_type: "i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c : set_subtraction(i \<circ>\<^sub>c m) \<rightarrow> A" using imc_type2 iinv_type comp_type by blast
    have lhs: "characteristic_func(m) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c) = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(i \<circ>\<^sub>c m)\<^esub>"
    proof -
      have "characteristic_func(m) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)
          = (characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c i) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)"
        using chi_im_i_eq_chi_m by simp
      also have "... = characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c))"
        using comp_associative2[OF iinvimc_type i_type chiim_type] by simp
      also have "... = characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c ((i \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)"
        using comp_associative2[OF imc_type2 iinv_type i_type] by simp
      also have "... = characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (id(B) \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)"
        using inv_right[OF i_iso i_type] by simp
      also have "... = characteristic_func(i \<circ>\<^sub>c m) \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c"
        using id_left_unit2[OF imc_type2] by simp
      also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub>) \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c"
        using complement_morphism_eq[OF im_type im_mono] by simp
      also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)"
        using comp_associative2[OF imc_type2 terminal_func_type false_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(i \<circ>\<^sub>c m)\<^esub>"
        using terminal_func_comp[OF imc_type2] by simp
      finally show ?thesis by simp
    qed
    have rhs: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c) = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(i \<circ>\<^sub>c m)\<^esub>"
    proof -
      have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c) = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>A\<^esub> \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c))"
        using comp_associative2[OF iinvimc_type terminal_func_type false_func_type] by simp
      also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>set_subtraction(i \<circ>\<^sub>c m)\<^esub>" using terminal_func_comp[OF iinvimc_type] by simp
      finally show ?thesis by simp
    qed
    show ?thesis using lhs rhs by simp
  qed

  have m_equalizer: "equalizer(set_subtraction(m), m\<^sup>c, characteristic_func(m), \<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>)"
    using complement_morphism_equalizer[OF m_type m_mono] by simp
  have fbA_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub> : A \<rightarrow> \<Omega>" using terminal_func_type false_func_type comp_type by blast
  have m_uniq: "\<forall> h F. (h : F \<rightarrow> A \<and> characteristic_func(m) \<circ>\<^sub>c h = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>) \<circ>\<^sub>c h) \<longrightarrow>
      (\<exists>! k. k : F \<rightarrow> set_subtraction(m) \<and> m\<^sup>c \<circ>\<^sub>c k = h)"
    using m_equalizer equalizer_def2[OF chim_type fbA_type mc_type] by simp
  have iinvimc_type: "i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c : set_subtraction(i \<circ>\<^sub>c m) \<rightarrow> A" using imc_type2 iinv_type comp_type by blast
  have ex1i'inv: "\<exists>! i'_inv. i'_inv : set_subtraction(i \<circ>\<^sub>c m) \<rightarrow> set_subtraction(m) \<and> m\<^sup>c \<circ>\<^sub>c i'_inv = i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c"
    using m_uniq[rule_format, where F="set_subtraction(i \<circ>\<^sub>c m)" and h="i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c"] iinvimc_type step_eq2 by auto
  then obtain i'_inv where i'_inv_type: "i'_inv : set_subtraction(i \<circ>\<^sub>c m) \<rightarrow> set_subtraction(m)"
      and i'_inv_def: "m\<^sup>c \<circ>\<^sub>c i'_inv = i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c" by auto

  have i'_inv_i'_eq: "i'_inv \<circ>\<^sub>c i' = id(set_subtraction(m))"
  proof -
    have mc_mono: "monomorphism(m\<^sup>c)" using complement_morphism_mono[OF m_type m_mono] by simp
    have i'i'inv_type: "i'_inv \<circ>\<^sub>c i' : set_subtraction(m) \<rightarrow> set_subtraction(m)" using i'_type i'_inv_type comp_type by blast
    have idsm_type: "id(set_subtraction(m)) : set_subtraction(m) \<rightarrow> set_subtraction(m)" by (rule id_type)
    have key: "m\<^sup>c \<circ>\<^sub>c (i'_inv \<circ>\<^sub>c i') = m\<^sup>c \<circ>\<^sub>c id(set_subtraction(m))"
    proof -
      have "m\<^sup>c \<circ>\<^sub>c (i'_inv \<circ>\<^sub>c i') = (m\<^sup>c \<circ>\<^sub>c i'_inv) \<circ>\<^sub>c i'"
        using comp_associative2[OF i'_type i'_inv_type mc_type] by simp
      also have "... = (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c) \<circ>\<^sub>c i'" using i'_inv_def by simp
      also have "... = i\<^bold>\<inverse> \<circ>\<^sub>c ((i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c i')"
        using comp_associative2[OF i'_type imc_type2 iinv_type] by simp
      also have "... = i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m\<^sup>c)" using i'_def by simp
      also have "... = (i\<^bold>\<inverse> \<circ>\<^sub>c i) \<circ>\<^sub>c m\<^sup>c" using comp_associative2[OF mc_type i_type iinv_type] by simp
      also have "... = id(A) \<circ>\<^sub>c m\<^sup>c" using inv_left[OF i_iso i_type] by simp
      also have "... = m\<^sup>c" using id_left_unit2[OF mc_type] by simp
      also have "... = m\<^sup>c \<circ>\<^sub>c id(set_subtraction(m))" using id_right_unit2[OF mc_type] by simp
      finally show ?thesis by simp
    qed
    have mono_rule: "\<forall> g h Ann. g : Ann \<rightarrow> set_subtraction(m) \<and> h : Ann \<rightarrow> set_subtraction(m) \<longrightarrow>
        (m\<^sup>c \<circ>\<^sub>c g = m\<^sup>c \<circ>\<^sub>c h \<longrightarrow> g = h)"
      using monomorphism_def3[OF mc_type] mc_mono by simp
    show ?thesis
      using mono_rule[rule_format, where g="i'_inv \<circ>\<^sub>c i'" and h="id(set_subtraction(m))" and Ann="set_subtraction(m)"]
        i'i'inv_type idsm_type key by auto
  qed

  have i'_i'inv_eq: "i' \<circ>\<^sub>c i'_inv = id(set_subtraction(i \<circ>\<^sub>c m))"
  proof -
    have imc_mono: "monomorphism((i \<circ>\<^sub>c m)\<^sup>c)" using complement_morphism_mono[OF im_type im_mono] by simp
    have i'i'inv_type2: "i' \<circ>\<^sub>c i'_inv : set_subtraction(i \<circ>\<^sub>c m) \<rightarrow> set_subtraction(i \<circ>\<^sub>c m)"
      using i'_inv_type i'_type comp_type by blast
    have idsim_type: "id(set_subtraction(i \<circ>\<^sub>c m)) : set_subtraction(i \<circ>\<^sub>c m) \<rightarrow> set_subtraction(i \<circ>\<^sub>c m)" by (rule id_type)
    have key2: "(i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c (i' \<circ>\<^sub>c i'_inv) = (i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c id(set_subtraction(i \<circ>\<^sub>c m))"
    proof -
      have "(i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c (i' \<circ>\<^sub>c i'_inv) = ((i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c i') \<circ>\<^sub>c i'_inv"
        using comp_associative2[OF i'_inv_type i'_type imc_type2] by simp
      also have "... = (i \<circ>\<^sub>c m\<^sup>c) \<circ>\<^sub>c i'_inv" using i'_def by simp
      also have "... = i \<circ>\<^sub>c (m\<^sup>c \<circ>\<^sub>c i'_inv)" using comp_associative2[OF i'_inv_type mc_type i_type] by simp
      also have "... = i \<circ>\<^sub>c (i\<^bold>\<inverse> \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c)" using i'_inv_def by simp
      also have "... = (i \<circ>\<^sub>c i\<^bold>\<inverse>) \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c" using comp_associative2[OF imc_type2 iinv_type i_type] by simp
      also have "... = id(B) \<circ>\<^sub>c (i \<circ>\<^sub>c m)\<^sup>c" using inv_right[OF i_iso i_type] by simp
      also have "... = (i \<circ>\<^sub>c m)\<^sup>c" using id_left_unit2[OF imc_type2] by simp
      also have "... = (i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c id(set_subtraction(i \<circ>\<^sub>c m))" using id_right_unit2[OF imc_type2] by simp
      finally show ?thesis by simp
    qed
    have mono_rule2: "\<forall> g h Ann. g : Ann \<rightarrow> set_subtraction(i \<circ>\<^sub>c m) \<and> h : Ann \<rightarrow> set_subtraction(i \<circ>\<^sub>c m) \<longrightarrow>
        ((i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c g = (i \<circ>\<^sub>c m)\<^sup>c \<circ>\<^sub>c h \<longrightarrow> g = h)"
      using monomorphism_def3[OF imc_type2] imc_mono by simp
    show ?thesis
      using mono_rule2[rule_format, where g="i' \<circ>\<^sub>c i'_inv" and h="id(set_subtraction(i \<circ>\<^sub>c m))" and Ann="set_subtraction(i \<circ>\<^sub>c m)"]
        i'i'inv_type2 idsim_type key2 by auto
  qed

  have i'_iso: "isomorphism(i')"
    using isomorphism_def3[OF i'_type] i'_inv_type i'_inv_i'_eq i'_i'inv_eq by auto
  show ?thesis
    unfolding is_isomorphic_def using i'_type i'_iso by auto
qed

subsection \<open>Graphs\<close>

text \<open>HOL's @{text functional_on} bundles the relation's underlying set and monomorphism into a
  @{text "cset \<times> cfunc"} pair; flattened here to a 4-argument predicate, matching @{text
  subobject_of}/@{text relative_member}'s convention.\<close>
definition functional_on :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> o" where
  "functional_on(X, Y, R, m) \<longleftrightarrow> (subobject_of(R, m, X \<times>\<^sub>c Y) \<and>
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<exists>! y. y \<in>\<^sub>c Y \<and> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, R, m))))"

text \<open>HOL's @{text graph}/@{text graph_morph} are @{text SOME}-defined off @{text "domain f"}/
  @{text "codomain f"}; following the same conservative-Skolemization technique used throughout
  this file, they are axiomatized directly here (single @{text cfunc} argument, typed premise).\<close>
axiomatization
  graph :: "cfunc \<Rightarrow> cset" and
  graph_morph :: "cfunc \<Rightarrow> cfunc"
where
  graph_morph_spec: "f : X \<rightarrow> Y \<Longrightarrow>
    equalizer(graph(f), graph_morph(f), f \<circ>\<^sub>c left_cart_proj(X, Y), right_cart_proj(X, Y))"

lemma graph_equalizer4:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "equalizer(graph(f), graph_morph(f), f \<circ>\<^sub>c left_cart_proj(X, Y), right_cart_proj(X, Y))"
  using graph_morph_spec[OF f_type] by simp

lemma graph_subobject:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "subobject_of(graph(f), graph_morph(f), X \<times>\<^sub>c Y)"
proof -
  have eq: "equalizer(graph(f), graph_morph(f), f \<circ>\<^sub>c left_cart_proj(X, Y), right_cart_proj(X, Y))"
    using graph_equalizer4[OF f_type] by simp
  have mono: "monomorphism(graph_morph(f))" using equalizer_is_monomorphism[OF eq] by simp
  have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have gm_type: "graph_morph(f) : graph(f) \<rightarrow> X \<times>\<^sub>c Y"
  proof -
    obtain X' Y' where rp_type': "right_cart_proj(X, Y) : X' \<rightarrow> Y'" and gm_type': "graph_morph(f) : graph(f) \<rightarrow> X'"
      using eq unfolding equalizer_def by auto
    have "X' = X \<times>\<^sub>c Y" using rp_type rp_type' unfolding cfunc_type_def by auto
    then show ?thesis using gm_type' by simp
  qed
  show ?thesis unfolding subobject_of_def using gm_type mono by simp
qed

lemma graph_morph_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "graph_morph(f) : graph(f) \<rightarrow> X \<times>\<^sub>c Y"
  using graph_subobject[OF f_type] unfolding subobject_of_def by auto

text \<open>The lemma below corresponds to Exercise 2.3.13 in Halvorson.\<close>
lemma graphs_are_functional:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "functional_on(X, Y, graph(f), graph_morph(f))"
  unfolding functional_on_def
proof (rule conjI)
  show "subobject_of(graph(f), graph_morph(f), X \<times>\<^sub>c Y)" using graph_subobject[OF f_type] by simp
next
  have gm_type: "graph_morph(f) : graph(f) \<rightarrow> X \<times>\<^sub>c Y" using graph_morph_type[OF f_type] by simp
  have gm_mono: "monomorphism(graph_morph(f))" using graph_subobject[OF f_type] unfolding subobject_of_def by auto
  have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" using lp_type f_type comp_type by blast
  have graph_eq: "equalizer(graph(f), graph_morph(f), f \<circ>\<^sub>c left_cart_proj(X, Y), right_cart_proj(X, Y))"
    using graph_equalizer4[OF f_type] by simp
  show "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<exists>! y. y \<in>\<^sub>c Y \<and> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f)))"
  proof (intro allI impI)
    fix x assume x_type: "x \<in>\<^sub>c X"
    have mem_iff_feq: "\<And>y. y \<in>\<^sub>c Y \<Longrightarrow> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f)) \<longleftrightarrow> f \<circ>\<^sub>c x = y"
    proof -
      fix y assume y_type: "y \<in>\<^sub>c Y"
      have xy_type: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
      have assoc1: "(f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>x,y\<rangle> = f \<circ>\<^sub>c x"
      proof -
        have "(f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>x,y\<rangle> = f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>)"
          using comp_associative2[OF xy_type lp_type f_type] by simp
        also have "... = f \<circ>\<^sub>c x" using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
        finally show ?thesis by simp
      qed
      have assoc2: "right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle> = y" using right_cart_proj_cfunc_prod[OF x_type y_type] by simp
      have iff1: "\<langle>x,y\<rangle> factorsthru graph_morph(f) \<longleftrightarrow> (f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>x,y\<rangle> = right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>"
        using xfactorthru_equalizer_iff_fx_eq_gx[OF flp_type rp_type graph_eq xy_type] by simp
      have iff2: "\<langle>x,y\<rangle> factorsthru graph_morph(f) \<longleftrightarrow> f \<circ>\<^sub>c x = y" using iff1 assoc1 assoc2 by simp
      show "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f)) \<longleftrightarrow> f \<circ>\<^sub>c x = y"
      proof (rule iffI)
        assume "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f))"
        then have "\<langle>x,y\<rangle> factorsthru graph_morph(f)" unfolding relative_member_def by auto
        then show "f \<circ>\<^sub>c x = y" using iff2 by simp
      next
        assume "f \<circ>\<^sub>c x = y"
        then have "\<langle>x,y\<rangle> factorsthru graph_morph(f)" using iff2 by simp
        then show "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f))"
          unfolding relative_member_def using xy_type gm_mono gm_type by auto
      qed
    qed
    have fx_type: "f \<circ>\<^sub>c x \<in>\<^sub>c Y" using x_type f_type comp_type by blast
    show "\<exists>! y. y \<in>\<^sub>c Y \<and> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f))"
    proof (rule ex1I[where a="f \<circ>\<^sub>c x"])
      show "f \<circ>\<^sub>c x \<in>\<^sub>c Y \<and> relative_member(\<langle>x, f \<circ>\<^sub>c x\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f))"
        using fx_type mem_iff_feq[OF fx_type] by simp
    next
      fix y assume "y \<in>\<^sub>c Y \<and> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f))"
      then have y_type: "y \<in>\<^sub>c Y" and y_mem: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, graph(f), graph_morph(f))" by auto
      show "y = f \<circ>\<^sub>c x" using mem_iff_feq[OF y_type] y_mem by simp
    qed
  qed
qed

lemma functional_on_isomorphism:
  assumes func: "functional_on(X, Y, R, m)"
  shows "isomorphism(left_cart_proj(X, Y) \<circ>\<^sub>c m)"
proof -
  have subobj: "subobject_of(R, m, X \<times>\<^sub>c Y)" using func unfolding functional_on_def by auto
  have m_type: "m : R \<rightarrow> X \<times>\<^sub>c Y" using subobj unfolding subobject_of_def by auto
  have m_mono: "monomorphism(m)" using subobj unfolding subobject_of_def by auto
  have func_prop: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<exists>! y. y \<in>\<^sub>c Y \<and> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, R, m))"
    using func unfolding functional_on_def by auto
  have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have pi0m_type: "left_cart_proj(X, Y) \<circ>\<^sub>c m : R \<rightarrow> X" using m_type lp_type comp_type by blast

  have surj: "surjective(left_cart_proj(X, Y) \<circ>\<^sub>c m)"
  proof -
    have goal: "\<forall> x. x \<in>\<^sub>c X \<longrightarrow> (\<exists>z. z \<in>\<^sub>c R \<and> (left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c z = x)"
    proof (intro allI impI)
      fix x assume x_type: "x \<in>\<^sub>c X"
      obtain y where y_type: "y \<in>\<^sub>c Y" and xy_mem: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, R, m)"
        using func_prop[rule_format, OF x_type] by auto
      have xy_type: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
      have "\<langle>x,y\<rangle> factorsthru m" using xy_mem unfolding relative_member_def by auto
      then obtain z where z_type: "z \<in>\<^sub>c R" and mz_eq: "m \<circ>\<^sub>c z = \<langle>x,y\<rangle>"
        using factors_through_def2[OF xy_type m_type] by auto
      have "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c z = x"
      proof -
        have "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c z = left_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c z)"
          using comp_associative2[OF z_type m_type lp_type] by simp
        also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>" using mz_eq by simp
        also have "... = x" using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
        finally show ?thesis by simp
      qed
      then show "\<exists>z. z \<in>\<^sub>c R \<and> (left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c z = x" using z_type by auto
    qed
    show ?thesis using surjective_def2[OF pi0m_type] goal by simp
  qed

  have inj: "injective(left_cart_proj(X, Y) \<circ>\<^sub>c m)"
  proof -
    have goal: "\<forall> r1 r2. r1 \<in>\<^sub>c R \<and> r2 \<in>\<^sub>c R \<and> (left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r1 = (left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r2 \<longrightarrow> r1 = r2"
    proof (intro allI impI)
      fix r1 r2
      assume "r1 \<in>\<^sub>c R \<and> r2 \<in>\<^sub>c R \<and> (left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r1 = (left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r2"
      then have r1_type: "r1 \<in>\<^sub>c R" and r2_type: "r2 \<in>\<^sub>c R"
          and eq: "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r1 = (left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r2" by auto
      have mr1_type: "m \<circ>\<^sub>c r1 \<in>\<^sub>c X \<times>\<^sub>c Y" using r1_type m_type comp_type by blast
      have mr2_type: "m \<circ>\<^sub>c r2 \<in>\<^sub>c X \<times>\<^sub>c Y" using r2_type m_type comp_type by blast
      obtain x1 y1 where mr1_eq: "m \<circ>\<^sub>c r1 = \<langle>x1, y1\<rangle>" and x1_type: "x1 \<in>\<^sub>c X" and y1_type: "y1 \<in>\<^sub>c Y"
        using cart_prod_decomp[OF mr1_type] by auto
      obtain x2 y2 where mr2_eq: "m \<circ>\<^sub>c r2 = \<langle>x2, y2\<rangle>" and x2_type: "x2 \<in>\<^sub>c X" and y2_type: "y2 \<in>\<^sub>c Y"
        using cart_prod_decomp[OF mr2_type] by auto
      have x_equal: "x1 = x2"
      proof -
        have l1: "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r1 = x1"
        proof -
          have "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r1 = left_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c r1)"
            using comp_associative2[OF r1_type m_type lp_type] by simp
          also have "... = x1" using mr1_eq left_cart_proj_cfunc_prod[OF x1_type y1_type] by simp
          finally show ?thesis by simp
        qed
        have l2: "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r2 = x2"
        proof -
          have "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c r2 = left_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c r2)"
            using comp_associative2[OF r2_type m_type lp_type] by simp
          also have "... = x2" using mr2_eq left_cart_proj_cfunc_prod[OF x2_type y2_type] by simp
          finally show ?thesis by simp
        qed
        show ?thesis using eq l1 l2 by simp
      qed
      have xy1_type: "\<langle>x1,y1\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" using x1_type y1_type cfunc_prod_type by auto
      have xy1_factorsthru: "\<langle>x1,y1\<rangle> factorsthru m"
        using factors_through_def2[OF xy1_type m_type] r1_type mr1_eq by auto
      have xy1_mem: "relative_member(\<langle>x1,y1\<rangle>, X \<times>\<^sub>c Y, R, m)"
        unfolding relative_member_def using xy1_type m_mono m_type xy1_factorsthru by auto
      have xy2_type: "\<langle>x2,y2\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" using x2_type y2_type cfunc_prod_type by auto
      have xy2_factorsthru: "\<langle>x2,y2\<rangle> factorsthru m"
        using factors_through_def2[OF xy2_type m_type] r2_type mr2_eq by auto
      have xy2_mem: "relative_member(\<langle>x2,y2\<rangle>, X \<times>\<^sub>c Y, R, m)"
        unfolding relative_member_def using xy2_type m_mono m_type xy2_factorsthru by auto
      have xy2_mem': "relative_member(\<langle>x1,y2\<rangle>, X \<times>\<^sub>c Y, R, m)" using xy2_mem x_equal by simp
      have ex1y: "\<exists>! y. y \<in>\<^sub>c Y \<and> relative_member(\<langle>x1,y\<rangle>, X \<times>\<^sub>c Y, R, m)"
        using func_prop[rule_format, OF x1_type] by simp
      then obtain yy where yy_unique: "\<forall> y'. (y' \<in>\<^sub>c Y \<and> relative_member(\<langle>x1,y'\<rangle>, X \<times>\<^sub>c Y, R, m)) \<longrightarrow> y' = yy" by auto
      have y1_eq_yy: "y1 = yy" using yy_unique[rule_format, where y'=y1] y1_type xy1_mem by auto
      have y2_eq_yy: "y2 = yy" using yy_unique[rule_format, where y'=y2] y2_type xy2_mem' by auto
      have y_equal: "y1 = y2" using y1_eq_yy y2_eq_yy by simp
      have mr1_eq_mr2: "m \<circ>\<^sub>c r1 = m \<circ>\<^sub>c r2" using mr1_eq mr2_eq x_equal y_equal by simp
      have m_mono_rule: "\<forall> g h ZZ. g : ZZ \<rightarrow> R \<and> h : ZZ \<rightarrow> R \<longrightarrow> (m \<circ>\<^sub>c g = m \<circ>\<^sub>c h \<longrightarrow> g = h)"
        using monomorphism_def3[OF m_type] m_mono by simp
      show "r1 = r2"
        using m_mono_rule[rule_format, where g=r1 and h=r2 and ZZ="\<one>"] r1_type r2_type mr1_eq_mr2 by auto
    qed
    show ?thesis using injective_def2[OF pi0m_type] goal by simp
  qed

  show "isomorphism(left_cart_proj(X, Y) \<circ>\<^sub>c m)"
    using epi_mon_is_iso[OF surjective_is_epimorphism[OF surj] injective_imp_monomorphism[OF inj]] by simp
qed

text \<open>The lemma below corresponds to Proposition 2.3.14 in Halvorson.\<close>
lemma functional_relations_are_graphs:
  assumes func: "functional_on(X, Y, R, m)"
  shows "\<exists>! f. f : X \<rightarrow> Y \<and> (\<exists> i. i : R \<rightarrow> graph(f) \<and> isomorphism(i) \<and> m = graph_morph(f) \<circ>\<^sub>c i)"
proof -
  have subobj: "subobject_of(R, m, X \<times>\<^sub>c Y)" using func unfolding functional_on_def by auto
  have m_type: "m : R \<rightarrow> X \<times>\<^sub>c Y" using subobj unfolding subobject_of_def by auto
  have m_mono: "monomorphism(m)" using subobj unfolding subobject_of_def by auto
  have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have pi0m_type: "left_cart_proj(X, Y) \<circ>\<^sub>c m : R \<rightarrow> X" using m_type lp_type comp_type by blast
  have iso_pi0m: "isomorphism(left_cart_proj(X, Y) \<circ>\<^sub>c m)" using functional_on_isomorphism[OF func] by simp

  define h where "h = (left_cart_proj(X, Y) \<circ>\<^sub>c m)\<^bold>\<inverse>"
  have h_type: "h : X \<rightarrow> R" unfolding h_def using inverse_type[OF iso_pi0m pi0m_type] by simp
  have mh_type: "m \<circ>\<^sub>c h : X \<rightarrow> X \<times>\<^sub>c Y" using h_type m_type comp_type by blast
  define f where "f = right_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c h)"
  have f_type: "f : X \<rightarrow> Y" unfolding f_def using mh_type rp_type comp_type by blast

  have pi0mh_eq: "(left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c h = id(X)"
    using h_def inv_right[OF iso_pi0m pi0m_type] by simp

  have eq: "f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m) = right_cart_proj(X, Y) \<circ>\<^sub>c m"
  proof -
    have "f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m) = (right_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c h)) \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m)"
      using f_def by simp
    also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c ((m \<circ>\<^sub>c h) \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m))"
      using comp_associative2[OF pi0m_type mh_type rp_type] by simp
    also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c (h \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m)))"
      using comp_associative2[OF pi0m_type h_type m_type] by simp
    also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c id(R))"
      using h_def inv_left[OF iso_pi0m pi0m_type] by simp
    also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c m" using id_right_unit2[OF m_type] by simp
    finally show ?thesis by simp
  qed

  have eq': "(f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c m = right_cart_proj(X, Y) \<circ>\<^sub>c m"
    using eq comp_associative2[OF m_type lp_type f_type] by simp

  have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" using lp_type f_type comp_type by blast
  have graph_eq: "equalizer(graph(f), graph_morph(f), f \<circ>\<^sub>c left_cart_proj(X, Y), right_cart_proj(X, Y))"
    using graph_equalizer4[OF f_type] by simp
  have gm_type: "graph_morph(f) : graph(f) \<rightarrow> X \<times>\<^sub>c Y" using graph_morph_type[OF f_type] by simp
  have gm_mono: "monomorphism(graph_morph(f))" using equalizer_is_monomorphism[OF graph_eq] by simp
  have graph_uniq: "\<forall> h' F. (h' : F \<rightarrow> X \<times>\<^sub>c Y \<and> (f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c h' = right_cart_proj(X, Y) \<circ>\<^sub>c h') \<longrightarrow>
      (\<exists>! k. k : F \<rightarrow> graph(f) \<and> graph_morph(f) \<circ>\<^sub>c k = h')"
    using graph_eq equalizer_def2[OF flp_type rp_type gm_type] by simp
  have ex1i: "\<exists>! i. i : R \<rightarrow> graph(f) \<and> graph_morph(f) \<circ>\<^sub>c i = m"
    using graph_uniq[rule_format, where F=R and h'=m] m_type eq' by auto
  then obtain i where i_type: "i : R \<rightarrow> graph(f)" and i_eq: "graph_morph(f) \<circ>\<^sub>c i = m" by auto

  have core_eq: "\<And>z. z : \<one> \<rightarrow> graph(f) \<Longrightarrow>
      f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)) = right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)"
  proof -
    fix z assume z_type: "z : \<one> \<rightarrow> graph(f)"
    have core: "(f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c graph_morph(f) = right_cart_proj(X, Y) \<circ>\<^sub>c graph_morph(f)"
      using equalizer_eq[OF flp_type rp_type gm_type graph_eq] by simp
    have gmz_type: "graph_morph(f) \<circ>\<^sub>c z : \<one> \<rightarrow> X \<times>\<^sub>c Y" using z_type gm_type comp_type by blast
    have "f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)) = (f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)"
      using comp_associative2[OF gmz_type lp_type f_type] by simp
    also have "... = ((f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c graph_morph(f)) \<circ>\<^sub>c z"
      using comp_associative2[OF z_type gm_type flp_type] by simp
    also have "... = (right_cart_proj(X, Y) \<circ>\<^sub>c graph_morph(f)) \<circ>\<^sub>c z" using core by simp
    also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)"
      using comp_associative2[OF z_type gm_type rp_type] by simp
    finally show "f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)) = right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)" by simp
  qed

  have i_surj: "surjective(i)"
  proof -
    have goal: "\<forall> y'. y' \<in>\<^sub>c graph(f) \<longrightarrow> (\<exists>x'. x' \<in>\<^sub>c R \<and> i \<circ>\<^sub>c x' = y')"
    proof (intro allI impI)
      fix y' assume y'_type: "y' \<in>\<^sub>c graph(f)"
      have gmy'_type: "graph_morph(f) \<circ>\<^sub>c y' \<in>\<^sub>c X \<times>\<^sub>c Y" using y'_type gm_type comp_type by blast
      define x where "x = left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c y')"
      have x_type: "x \<in>\<^sub>c X" unfolding x_def using gmy'_type lp_type comp_type by blast
      have ex1y: "\<exists>! y. y \<in>\<^sub>c Y \<and> relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, R, m)"
        using func x_type unfolding functional_on_def by auto
      then obtain y where y_type: "y \<in>\<^sub>c Y" and xy_mem: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c Y, R, m)" by auto
      have xy_type: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
      have "\<langle>x,y\<rangle> factorsthru m" using xy_mem unfolding relative_member_def by auto
      then obtain x' where x'_type: "x' \<in>\<^sub>c R" and x'_eq: "m \<circ>\<^sub>c x' = \<langle>x,y\<rangle>"
        using factors_through_def2[OF xy_type m_type] by auto
      have ix'_type: "i \<circ>\<^sub>c x' : \<one> \<rightarrow> graph(f)" using x'_type i_type comp_type by blast

      have left_eq: "left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x')) = left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c y')"
      proof -
        have "left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x')) = left_cart_proj(X, Y) \<circ>\<^sub>c ((graph_morph(f) \<circ>\<^sub>c i) \<circ>\<^sub>c x')"
          using comp_associative2[OF x'_type i_type gm_type] by simp
        also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c (m \<circ>\<^sub>c x')" using i_eq by simp
        also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>" using x'_eq by simp
        also have "... = x" using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
        also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c y')" using x_def by simp
        finally show ?thesis by simp
      qed
      have right_eq: "right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x')) = right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c y')"
      proof -
        have s1: "right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x')) = f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x')))"
          using core_eq[OF ix'_type] by simp
        have s2: "left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x')) = left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c y')"
          using left_eq by simp
        have s3: "f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c y')) = right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c y')"
          using core_eq[OF y'_type] by simp
        show ?thesis using s1 s2 s3 by simp
      qed

      have gmix'_type: "graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x') : \<one> \<rightarrow> X \<times>\<^sub>c Y" using ix'_type gm_type comp_type by blast
      have gmy'_type2: "graph_morph(f) \<circ>\<^sub>c y' : \<one> \<rightarrow> X \<times>\<^sub>c Y" using y'_type gm_type comp_type by blast
      have gmix'_eq: "graph_morph(f) \<circ>\<^sub>c (i \<circ>\<^sub>c x') = graph_morph(f) \<circ>\<^sub>c y'"
        using cart_prod_eqI[OF gmix'_type gmy'_type2 conjI[OF left_eq right_eq]] by simp

      have gm_mono_rule: "\<forall> g h' ZZ. g : ZZ \<rightarrow> graph(f) \<and> h' : ZZ \<rightarrow> graph(f) \<longrightarrow> (graph_morph(f) \<circ>\<^sub>c g = graph_morph(f) \<circ>\<^sub>c h' \<longrightarrow> g = h')"
        using monomorphism_def3[OF gm_type] gm_mono by simp
      have ix'_eq_y': "i \<circ>\<^sub>c x' = y'"
        using gm_mono_rule[rule_format, where g="i \<circ>\<^sub>c x'" and h'=y' and ZZ="\<one>"] ix'_type y'_type gmix'_eq by auto
      show "\<exists>x'. x' \<in>\<^sub>c R \<and> i \<circ>\<^sub>c x' = y'" using x'_type ix'_eq_y' by auto
    qed
    show ?thesis using surjective_def2[OF i_type] goal by simp
  qed

  have i_iso: "isomorphism(i)"
  proof -
    have i_epi: "epimorphism(i)" using surjective_is_epimorphism[OF i_surj] by simp
    have gmi_mono: "monomorphism(graph_morph(f) \<circ>\<^sub>c i)" using i_eq m_mono by simp
    have i_mono: "monomorphism(i)" using comp_monic_imp_monic'[OF i_type gm_type gmi_mono] by simp
    show ?thesis using epi_mon_is_iso[OF i_epi i_mono] by simp
  qed

  show ?thesis
  proof (rule ex1I[where a=f])
    show "f : X \<rightarrow> Y \<and> (\<exists> i. i : R \<rightarrow> graph(f) \<and> isomorphism(i) \<and> m = graph_morph(f) \<circ>\<^sub>c i)"
      using f_type i_type i_iso i_eq by auto
  next
    fix f2 assume f2_props: "f2 : X \<rightarrow> Y \<and> (\<exists> i2. i2 : R \<rightarrow> graph(f2) \<and> isomorphism(i2) \<and> m = graph_morph(f2) \<circ>\<^sub>c i2)"
    have f2_type: "f2 : X \<rightarrow> Y" using f2_props by auto
    obtain i2 where i2_type: "i2 : R \<rightarrow> graph(f2)" and i2_iso: "isomorphism(i2)" and i2_eq: "m = graph_morph(f2) \<circ>\<^sub>c i2"
      using f2_props by auto

    have gm2_type: "graph_morph(f2) : graph(f2) \<rightarrow> X \<times>\<^sub>c Y" using graph_morph_type[OF f2_type] by simp
    have graph_eq2: "equalizer(graph(f2), graph_morph(f2), f2 \<circ>\<^sub>c left_cart_proj(X, Y), right_cart_proj(X, Y))"
      using graph_equalizer4[OF f2_type] by simp
    have flp2_type: "f2 \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" using lp_type f2_type comp_type by blast
    have core2: "(f2 \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c graph_morph(f2) = right_cart_proj(X, Y) \<circ>\<^sub>c graph_morph(f2)"
      using equalizer_eq[OF flp2_type rp_type gm2_type graph_eq2] by simp

    have f2_lpm_eq: "f2 \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m) = right_cart_proj(X, Y) \<circ>\<^sub>c m"
    proof -
      have lpgm2_type: "left_cart_proj(X, Y) \<circ>\<^sub>c graph_morph(f2) : graph(f2) \<rightarrow> X" using gm2_type lp_type comp_type by blast
      have "f2 \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m) = f2 \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f2) \<circ>\<^sub>c i2))"
        using i2_eq by simp
      also have "... = f2 \<circ>\<^sub>c ((left_cart_proj(X, Y) \<circ>\<^sub>c graph_morph(f2)) \<circ>\<^sub>c i2)"
        using comp_associative2[OF i2_type gm2_type lp_type] by simp
      also have "... = (f2 \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c graph_morph(f2))) \<circ>\<^sub>c i2"
        using comp_associative2[OF i2_type lpgm2_type f2_type] by simp
      also have "... = ((f2 \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c graph_morph(f2)) \<circ>\<^sub>c i2"
        using comp_associative2[OF gm2_type lp_type f2_type] by simp
      also have "... = (right_cart_proj(X, Y) \<circ>\<^sub>c graph_morph(f2)) \<circ>\<^sub>c i2" using core2 by simp
      also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c (graph_morph(f2) \<circ>\<^sub>c i2)"
        using comp_associative2[OF i2_type gm2_type rp_type] by simp
      also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c m" using i2_eq by simp
      finally show ?thesis by simp
    qed

    have flpm_eq_f2lpm: "f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m) = f2 \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m)"
      using eq f2_lpm_eq by simp

    have f_eq_f2: "f = f2"
    proof -
      have "f = f \<circ>\<^sub>c id(X)" using id_right_unit2[OF f_type] by simp
      also have "... = f \<circ>\<^sub>c ((left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c h)" using pi0mh_eq by simp
      also have "... = (f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m)) \<circ>\<^sub>c h"
        using comp_associative2[OF h_type pi0m_type f_type] by simp
      also have "... = (f2 \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c m)) \<circ>\<^sub>c h" using flpm_eq_f2lpm by simp
      also have "... = f2 \<circ>\<^sub>c ((left_cart_proj(X, Y) \<circ>\<^sub>c m) \<circ>\<^sub>c h)"
        using comp_associative2[OF h_type pi0m_type f2_type] by simp
      also have "... = f2 \<circ>\<^sub>c id(X)" using pi0mh_eq by simp
      also have "... = f2" using id_right_unit2[OF f2_type] by simp
      finally show ?thesis by simp
    qed
    show "f2 = f" using f_eq_f2 by simp
  qed
qed

end
