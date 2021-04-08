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

thm subobject_of_def

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
    obtain z where z_type: "z\<in>\<^sub>c p\<^sup>-\<^sup>1{y0}"
      using a1 nonempty_def by blast
    then have contradiction: "p \<circ>\<^sub>c (m \<circ>\<^sub>c z) = y0"
      oops

end