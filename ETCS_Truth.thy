theory ETCS_Truth
  imports ETCS_Equalizer
begin

section  \<open>Axiom 5: Truth-Value Object\<close>

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
    "m : B \<rightarrow> X \<Longrightarrow> monomorphism m \<Longrightarrow> \<exists>! \<chi>. is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi>"


definition eq_pred :: "cset \<Rightarrow> cfunc" where
  "eq_pred X = (THE \<chi>. is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> (diagonal X) \<chi>)"




find_theorems "(THE x. ?P x)"

lemma eq_pred_pullback: "is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> (diagonal X) (eq_pred X)"
  unfolding eq_pred_def
  by (rule the1I2, simp_all add: characteristic_function_exists diag_mono diagonal_type)

lemma eq_pred_type[type_rule]:
  "eq_pred X : X \<times>\<^sub>c X \<rightarrow> \<Omega>"
  using eq_pred_pullback unfolding is_pullback_def square_commutes_def by auto

lemma eq_pred_square: "eq_pred X \<circ>\<^sub>c diagonal X = \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>"
  using eq_pred_pullback unfolding is_pullback_def square_commutes_def by auto

lemma eq_pred_iff_eq:
  assumes "x : one \<rightarrow> X" "y : one \<rightarrow> X"
  shows "(x = y) = (eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>)"
proof auto
  assume x_eq_y: "x = y"

  have "(eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,id\<^sub>c X\<rangle>) \<circ>\<^sub>c y = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using eq_pred_square unfolding diagonal_def by auto
  then have "eq_pred X \<circ>\<^sub>c \<langle>y, y\<rangle> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c y"
    using assms diagonal_type id_type
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 diagonal_def id_left_unit2)
  then show "eq_pred X \<circ>\<^sub>c \<langle>y, y\<rangle> = \<t>"
    using assms id_type
    by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp terminal_func_type terminal_func_unique id_right_unit2)
next
  assume "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>"
  then have "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t> \<circ>\<^sub>c id one"
    using id_right_unit2 true_func_type by auto
  then obtain j  where j_type: "j : one \<rightarrow> X" and "diagonal X \<circ>\<^sub>c j = \<langle>x,y\<rangle>"
    using eq_pred_pullback assms unfolding is_pullback_def by (metis cfunc_prod_type id_type)
  then have "\<langle>j,j\<rangle> = \<langle>x,y\<rangle>"
    using diag_on_elements by auto
  then show "x = y"
    using assms element_pair_eq j_type by auto
qed

(* Proposition 2.2.1: see under Axiom 8 *)

(* Proposition 2.2.2 *)
lemma "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
proof -
  have "{x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = {\<langle>\<t>,\<t>\<rangle>, \<langle>\<t>,\<f>\<rangle>, \<langle>\<f>,\<t>\<rangle>, \<langle>\<f>,\<f>\<rangle>}"
    apply (auto simp add: cfunc_prod_type true_func_type false_func_type)
    by (smt cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type true_false_only_truth_values)
  then show "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
    using element_pair_eq false_func_type true_false_distinct true_func_type by auto
qed

(* Exercise 2.2.3 *)
lemma regmono_is_mono: "regular_monomorphism(m) \<Longrightarrow> monomorphism(m)"
  using equalizer_is_monomorphism regular_monomorphism_def by blast

(* Proposition 2.2.4 *)
lemma mono_is_regmono:
  assumes "m \<in> ETCS_func"
  shows "monomorphism(m) \<Longrightarrow> regular_monomorphism(m)"
  unfolding regular_monomorphism_def
proof - 
  assume m_mono: "monomorphism(m)"
  then obtain \<chi> where chi_pullback: "is_pullback (domain(m)) one  (codomain(m)) \<Omega> (\<beta>\<^bsub>domain(m)\<^esub>) \<t> m \<chi> "
    using assms cfunc_type_def characteristic_function_exists by blast

  have pullback: "\<And>k h Z. k : Z \<rightarrow> one \<and> h : Z \<rightarrow> codomain m \<and> \<t> \<circ>\<^sub>c k = \<chi> \<circ>\<^sub>c h \<longrightarrow>
     (\<exists>!j. j : Z \<rightarrow> domain m \<and> \<beta>\<^bsub>domain m\<^esub> \<circ>\<^sub>c j = k \<and> m \<circ>\<^sub>c j = h)"
    using chi_pullback unfolding is_pullback_def by auto

  have "equalizer (domain(m)) m (\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub>) \<chi>"
    unfolding equalizer_def
  proof (rule_tac x="codomain(m)" in exI, rule_tac x="\<Omega>" in exI, auto)
    show tbeta_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub> : codomain(m) \<rightarrow>  \<Omega>"
      using comp_type terminal_func_type true_func_type by blast
    show chi_type: "\<chi> : codomain(m) \<rightarrow>  \<Omega>"
      using chi_pullback is_pullback_def square_commutes_def by auto
    show m_type: "m : domain m \<rightarrow> codomain m"
      by (simp add: assms cfunc_type_def)

    have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>domain m\<^esub> = \<chi> \<circ>\<^sub>c m"
      using chi_pullback unfolding is_pullback_def square_commutes_def by auto
    then have "\<beta>\<^bsub>domain m\<^esub> = \<beta>\<^bsub>codomain m\<^esub> \<circ>\<^sub>c m"
      by (metis (mono_tags, hide_lams) cfunc_type_def codomain_comp domain_comp terminal_func_type terminal_func_unique true_func_type)
    then show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>) \<circ>\<^sub>c m = \<chi> \<circ>\<^sub>c m"
      using cfunc_type_def comm comp_associative terminal_func_type true_func_type by auto
  next
    fix h F
    assume  "h : F \<rightarrow> codomain m" "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>) \<circ>\<^sub>c h = \<chi> \<circ>\<^sub>c h"
    then show "\<exists>k. k : F \<rightarrow> domain m \<and> m \<circ>\<^sub>c k = h"
      by (metis cfunc_type_def comp_associative pullback terminal_func_comp terminal_func_type true_func_type)
  next
    fix F k y
    assume "k : F \<rightarrow> domain m" "y : F \<rightarrow> domain m"
    then show "m \<circ>\<^sub>c y = m \<circ>\<^sub>c k \<Longrightarrow> k = y"
      using m_mono unfolding monomorphism_def by (simp add: cfunc_type_def)
  qed
  then show "\<exists>g h. domain g = codomain m \<and> domain h = codomain m \<and> equalizer (domain m) m g h"
    by (metis cfunc_type_def equalizer_def)
qed

(*Proposition 2.2.5*)
lemma epi_mon_is_iso:
  assumes "f \<in> ETCS_func"
  assumes "epimorphism(f)" "monomorphism(f)"
  shows "isomorphism(f)"
  using assms epi_regmon_is_iso mono_is_regmono by auto

(* Definition 2.2.6 *)
definition fiber :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1{_}" [100,100]100) where
  "f\<^sup>-\<^sup>1{y} = (f\<^sup>-\<^sup>1[one]\<^bsub>y\<^esub>)"

definition fiber_morphism :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "fiber_morphism f y = left_cart_proj (domain f) one \<circ>\<^sub>c inverse_image_mapping f one y"

lemma fiber_morphism_type[type_rule]:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "fiber_morphism f y : f\<^sup>-\<^sup>1{y} \<rightarrow> X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject subobject_of_def2
  by auto

lemma fiber_subset: 
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "(f\<^sup>-\<^sup>1{y}, fiber_morphism f y) \<subseteq>\<^sub>c X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject
  by auto

lemma fiber_morphism_monomorphism:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "monomorphism (fiber_morphism f y)"
  using assms cfunc_type_def element_monomorphism fiber_morphism_def inverse_image_monomorphism by auto

lemma fiber_morphism_eq:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "f \<circ>\<^sub>c fiber_morphism f y  = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
proof -
  have "f \<circ>\<^sub>c fiber_morphism f y = f \<circ>\<^sub>c left_cart_proj (domain f) one \<circ>\<^sub>c inverse_image_mapping f one y"
    unfolding fiber_morphism_def by auto
  also have "... = y \<circ>\<^sub>c right_cart_proj X one \<circ>\<^sub>c inverse_image_mapping f one y"
    using assms cfunc_type_def element_monomorphism inverse_image_mapping_eq by auto
  also have "... = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1[one]\<^bsub>y\<^esub>\<^esub>"
    using assms by (typecheck_cfuncs, metis element_monomorphism terminal_func_unique)
  also have "... = y \<circ>\<^sub>c \<beta>\<^bsub>f\<^sup>-\<^sup>1{y}\<^esub>"
    unfolding fiber_def by auto
  then show ?thesis
    using calculation by auto
qed

(* Proposition 2.2.7 *)
lemma not_surjective_has_some_empty_preimage:
  assumes "p: X \<rightarrow> Y" "\<not>surjective(p)"
  shows "\<exists> y. (y\<in>\<^sub>c Y \<and>  \<not>nonempty(p\<^sup>-\<^sup>1{y}))"
proof -
  have nonempty: "nonempty(Y)"
    using assms(1) assms(2) cfunc_type_def nonempty_def surjective_def by auto
  obtain y0 where y0_type: "(y0\<in>\<^sub>c Y)\<and>(\<forall> x. (x\<in>\<^sub>c X \<longrightarrow> p\<circ>\<^sub>c x \<noteq> y0))"
    using assms(1) assms(2) cfunc_type_def surjective_def by auto
  (* then have "is_pullback (p\<^sup>-\<^sup>1{y0}) one X Y (\<beta>\<^bsub>p\<^sup>-\<^sup>1{y0}\<^esub>) (y0) m p" *)
  have "\<not>nonempty(p\<^sup>-\<^sup>1{y0})"
  proof (rule ccontr,auto)
    assume a1: "nonempty(p\<^sup>-\<^sup>1{y0})"
    obtain z where z_type: "z \<in>\<^sub>c p\<^sup>-\<^sup>1{y0}"
      using a1 nonempty_def by blast
    have fiber_z_type: "fiber_morphism p y0 \<circ>\<^sub>c z \<in>\<^sub>c X"
      using assms(1) comp_type fiber_morphism_type y0_type z_type by auto
    have contradiction: "p \<circ>\<^sub>c (fiber_morphism p y0 \<circ>\<^sub>c z) = y0"
      by (smt assms(1) cfunc_type_def comp_associative2 element_monomorphism fiber_morphism_def fiber_morphism_eq id_right_unit2 id_type inverse_image_subobject subobject_of_def2 terminal_func_comp terminal_func_type terminal_func_unique y0_type z_type)
    have "p \<circ>\<^sub>c (fiber_morphism p y0 \<circ>\<^sub>c z) \<noteq> y0"
      by (simp add: fiber_z_type y0_type)
    then show False
      using contradiction by blast
  qed
  then show ?thesis
    using y0_type by blast
qed


lemma char_of_singleton1: 
    assumes "x \<in>\<^sub>c X" 
    shows  "eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id X\<rangle> \<circ>\<^sub>c x = \<t>"
    using assms cart_prod_extract_right eq_pred_iff_eq by fastforce

lemma char_of_singleton2: 
    assumes "x \<in>\<^sub>c X"  "y \<in>\<^sub>c X" "x \<noteq> y"
    shows  "eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, id X\<rangle> \<circ>\<^sub>c y = \<f>"
    using assms cart_prod_extract_right eq_pred_iff_eq true_false_only_truth_values  by (typecheck_cfuncs, fastforce)




(* Proposition 2.2.8 *)
lemma epi_is_surj:
  assumes "p: X \<rightarrow> Y" "epimorphism(p)"
  shows "surjective(p)"
  unfolding surjective_def
proof(rule ccontr)
  assume a1: "\<not> (\<forall>y. y \<in>\<^sub>c codomain p \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain p \<and> p \<circ>\<^sub>c x = y))"
  have "\<exists>y. y \<in>\<^sub>c Y \<and> \<not>(\<exists>x. x \<in>\<^sub>c X \<and> p \<circ>\<^sub>c x = y)"
    using a1 assms(1) cfunc_type_def by auto
  then obtain y0 where y_def: "y0 \<in>\<^sub>c Y \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> p \<circ>\<^sub>c x \<noteq> y0)"
    by auto
  have mono: "monomorphism(y0)"
    using element_monomorphism y_def by blast
  obtain g where g_def: "g = eq_pred Y \<circ>\<^sub>c \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle>"
    by simp
  have g_right_arg_type: "\<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> : Y \<rightarrow> (Y\<times>\<^sub>cY)"
    by (meson cfunc_prod_type comp_type id_type terminal_func_type y_def)
  then have g_type: "g: Y \<rightarrow> \<Omega>"
    using comp_type eq_pred_type g_def by blast

  have gpx_Eqs_f: "\<forall>x. (x \<in>\<^sub>c X \<longrightarrow> g \<circ>\<^sub>c p \<circ>\<^sub>c x = \<f>)"
  proof(rule ccontr, auto)
    fix x
    assume x_type: "x \<in>\<^sub>c X" 
    assume bwoc: "g \<circ>\<^sub>c p \<circ>\<^sub>c x \<noteq> \<f>"
    (*
    have contradiction: "\<exists>s. s \<in>\<^sub>c p\<^sup>-\<^sup>1{y0}"
      by (smt assms(1) bwoc cfunc_type_def char_of_singleton2 comp_associative comp_type eq_pred_type g_def g_right_arg_type x_type y_def)
    *)
    (*Incidently the above is not necessary and the justification is the same in both cases.*)
    then show False
      by (smt assms(1) bwoc cfunc_type_def char_of_singleton2 comp_associative comp_type eq_pred_type g_def g_right_arg_type x_type y_def)
  qed
  obtain h where h_def: "h = \<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    by simp
  have h_type: "h: Y \<rightarrow> \<Omega>"
    using comp_type false_func_type h_def terminal_func_type by blast
  have hpx_eqs_f: "\<forall>x. (x \<in>\<^sub>c X \<longrightarrow> h \<circ>\<^sub>c p \<circ>\<^sub>c x = \<f>)"
    by (smt assms(1) cfunc_type_def codomain_comp comp_associative false_func_type h_def id_right_unit2 id_type terminal_func_comp terminal_func_type terminal_func_unique)
  have gp_eqs_hp: "g \<circ>\<^sub>c p = h \<circ>\<^sub>c p"
  proof(rule one_separator[where X=X,where Y=\<Omega>])
    show "g \<circ>\<^sub>c p : X \<rightarrow> \<Omega>"
      using assms(1) comp_type g_type by auto
    show "h \<circ>\<^sub>c p : X \<rightarrow> \<Omega>"
      using assms(1) comp_type h_type by blast
    show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> (g \<circ>\<^sub>c p) \<circ>\<^sub>c x = (h \<circ>\<^sub>c p) \<circ>\<^sub>c x"
      using assms(1) comp_associative2 g_type gpx_Eqs_f h_type hpx_eqs_f by auto
  qed
  have g_not_h: "g \<noteq> h"
  proof -
   have f1: "\<forall>c. \<beta>\<^bsub>codomain c\<^esub> \<circ>\<^sub>c c = \<beta>\<^bsub>domain c\<^esub>"
    by (simp add: cfunc_type_def terminal_func_comp)
   have f2: "domain \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>,id\<^sub>c Y\<rangle> = Y"
    using cfunc_type_def g_right_arg_type by blast
  have f3: "codomain \<langle>y0 \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>,id\<^sub>c Y\<rangle> = Y \<times>\<^sub>c Y"
    using cfunc_type_def g_right_arg_type by blast
  have f4: "codomain y0 = Y"
    using cfunc_type_def y_def by presburger
  have "\<forall>c. domain (eq_pred c) = c \<times>\<^sub>c c"
    using cfunc_type_def eq_pred_type by auto
  then have "g \<circ>\<^sub>c y0 \<noteq> \<f>"
    using f4 f3 f2 by (metis (no_types) char_of_singleton1 comp_associative g_def true_false_distinct y_def)
  then show ?thesis
    using f1 by (metis (no_types) cfunc_type_def comp_associative false_func_type h_def id_right_unit2 id_type one_unique_element terminal_func_type y_def)
qed
  then show False
    using gp_eqs_hp assms(1) assms(2) cfunc_type_def epimorphism_def g_type h_type by auto
qed


  

end