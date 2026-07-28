section \<open>Terminal Objects and Elements\<close>

theory Terminal
  imports Cfunc Product
begin

text \<open>The axiomatization below corresponds to Axiom 3 (Terminal Object) in Halvorson.\<close>
axiomatization
  terminal_func :: "cset \<Rightarrow> cfunc" ("\<beta>\<^bsub>_\<^esub>" 100) and
  one_set :: "cset" ("\<one>")
where
  terminal_func_type[type_rule]: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" and
  terminal_func_unique: "h : X \<rightarrow> \<one> \<Longrightarrow> h = \<beta>\<^bsub>X\<^esub>" and
  one_separator: "f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> (\<And> x. x : \<one> \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x) \<Longrightarrow> f = g"

lemma one_separator_contrapos:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and neq: "f \<noteq> g"
  shows "\<exists> x. x : \<one> \<rightarrow> X \<and> f \<circ>\<^sub>c x \<noteq> g \<circ>\<^sub>c x"
proof (rule ccontr)
  assume "\<not> (\<exists> x. x : \<one> \<rightarrow> X \<and> f \<circ>\<^sub>c x \<noteq> g \<circ>\<^sub>c x)"
  then have all_eq: "\<forall> x. x : \<one> \<rightarrow> X \<longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x" by auto
  have meta: "\<And>x. x : \<one> \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x" using all_eq by auto
  have "f = g" using f_type g_type meta by (rule one_separator)
  then show False using neq by simp
qed

lemma terminal_func_comp:
  assumes x_type: "x : X \<rightarrow> Y"
  shows "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c x = \<beta>\<^bsub>X\<^esub>"
proof -
  have comp_type': "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c x : X \<rightarrow> \<one>" using x_type terminal_func_type comp_type by blast
  show ?thesis using comp_type' terminal_func_unique by auto
qed

lemma terminal_func_comp_elem:
  assumes x_type: "x : \<one> \<rightarrow> X"
  shows "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = id(\<one>)"
proof -
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = \<beta>\<^bsub>\<one>\<^esub>" using x_type terminal_func_comp by auto
  also have "... = id(\<one>)" using id1_type terminal_func_unique by auto
  finally show ?thesis by simp
qed

subsection \<open>Set Membership and Emptiness\<close>

text \<open>The abbreviation below captures Definition 2.1.16 in Halvorson.\<close>
abbreviation member :: "cfunc \<Rightarrow> cset \<Rightarrow> o" (infix "\<in>\<^sub>c" 50) where
  "x \<in>\<^sub>c X \<equiv> (x : \<one> \<rightarrow> X)"

lemma element_of_1:
  assumes x_type: "x \<in>\<^sub>c \<one>"
  shows "x = id(\<one>)"
proof -
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have "x = \<beta>\<^bsub>\<one>\<^esub>" using x_type terminal_func_unique by auto
  also have "... = id(\<one>)" using id1_type terminal_func_unique by auto
  finally show ?thesis by simp
qed

definition nonempty :: "cset \<Rightarrow> o" where
  "nonempty(X) \<longleftrightarrow> (\<exists>x. x \<in>\<^sub>c X)"

definition is_empty :: "cset \<Rightarrow> o" where
  "is_empty(X) \<longleftrightarrow> \<not>(\<exists>x. x \<in>\<^sub>c X)"

text \<open>The lemma below corresponds to Exercise 2.1.18 in Halvorson.\<close>
lemma element_monomorphism:
  assumes x_type: "x \<in>\<^sub>c X"
  shows "monomorphism(x)"
  unfolding monomorphism_def
proof (intro allI impI)
  fix g h
  assume "codomain(g) = domain(x) \<and> codomain(h) = domain(x)"
  then have cg: "codomain(g) = domain(x)" and ch: "codomain(h) = domain(x)" by auto
  assume xg_eq_xh: "x \<circ>\<^sub>c g = x \<circ>\<^sub>c h"
  have dom_x: "domain(x) = \<one>" using x_type unfolding cfunc_type_def by auto
  have dg: "domain(x \<circ>\<^sub>c g) = domain(g)" using cg domain_comp by auto
  have dh: "domain(x \<circ>\<^sub>c h) = domain(h)" using ch domain_comp by auto
  have dom_gh: "domain(g) = domain(h)" using dg dh xg_eq_xh by simp
  have g_type: "g : domain(g) \<rightarrow> \<one>" unfolding cfunc_type_def using cg dom_x by auto
  have h_type: "h : domain(h) \<rightarrow> \<one>" unfolding cfunc_type_def using ch dom_x by auto
  have g_eq: "g = \<beta>\<^bsub>domain(g)\<^esub>" using g_type terminal_func_unique by auto
  have h_eq: "h = \<beta>\<^bsub>domain(h)\<^esub>" using h_type terminal_func_unique by auto
  show "g = h" using g_eq h_eq dom_gh by simp
qed

lemma one_unique_element: "\<exists>! x. x \<in>\<^sub>c \<one>"
proof (rule ex1I[where a="id(\<one>)"])
  show "id(\<one>) \<in>\<^sub>c \<one>" by (rule id_type)
next
  fix x
  assume "x \<in>\<^sub>c \<one>"
  then show "x = id(\<one>)" using element_of_1 by auto
qed

lemma prod_with_empty_is_empty1:
  assumes A_empty: "is_empty(A)"
  shows "is_empty(A \<times>\<^sub>c B)"
proof (rule ccontr)
  assume "\<not> is_empty(A \<times>\<^sub>c B)"
  then have "\<exists>z. z \<in>\<^sub>c A \<times>\<^sub>c B" using is_empty_def by auto
  then obtain z where z_type: "z \<in>\<^sub>c A \<times>\<^sub>c B" by auto
  have lp_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by (rule left_cart_proj_type)
  have "left_cart_proj(A, B) \<circ>\<^sub>c z \<in>\<^sub>c A" using z_type lp_type comp_type by blast
  then have "\<exists>a. a \<in>\<^sub>c A" by auto
  then show False using A_empty is_empty_def by auto
qed

lemma prod_with_empty_is_empty2:
  assumes B_empty: "is_empty(B)"
  shows "is_empty(A \<times>\<^sub>c B)"
proof (rule ccontr)
  assume "\<not> is_empty(A \<times>\<^sub>c B)"
  then have "\<exists>z. z \<in>\<^sub>c A \<times>\<^sub>c B" using is_empty_def by auto
  then obtain z where z_type: "z \<in>\<^sub>c A \<times>\<^sub>c B" by auto
  obtain a b where z_decomp: "z = \<langle>a, b\<rangle>" and a_type: "a \<in>\<^sub>c A" and b_type: "b \<in>\<^sub>c B"
    using cart_prod_decomp[OF z_type] by blast
  then have "\<exists>b. b \<in>\<^sub>c B" by auto
  then show False using B_empty is_empty_def by auto
qed

subsection \<open>Terminal Objects (sets with one element)\<close>

definition terminal_object :: "cset \<Rightarrow> o" where
  "terminal_object(X) \<longleftrightarrow> (\<forall> Y. \<exists>! f. f : Y \<rightarrow> X)"

lemma one_terminal_object: "terminal_object(\<one>)"
  unfolding terminal_object_def
proof (intro allI)
  fix Y
  show "\<exists>! f. f : Y \<rightarrow> \<one>"
  proof (rule ex1I[where a="\<beta>\<^bsub>Y\<^esub>"])
    show "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by (rule terminal_func_type)
  next
    fix f assume "f : Y \<rightarrow> \<one>" then show "f = \<beta>\<^bsub>Y\<^esub>" using terminal_func_unique by auto
  qed
qed

text \<open>The lemma below is a generalisation of @{thm element_monomorphism}\<close>
lemma terminal_el_monomorphism:
  assumes x_type: "x : T \<rightarrow> X"
  assumes term_T: "terminal_object(T)"
  shows "monomorphism(x)"
  unfolding monomorphism_def
proof (intro allI impI)
  fix g h
  assume "codomain(g) = domain(x) \<and> codomain(h) = domain(x)"
  then have cg: "codomain(g) = domain(x)" and ch: "codomain(h) = domain(x)" by auto
  assume xg_eq_xh: "x \<circ>\<^sub>c g = x \<circ>\<^sub>c h"
  have dom_x: "domain(x) = T" using x_type unfolding cfunc_type_def by auto
  have dg: "domain(x \<circ>\<^sub>c g) = domain(g)" using cg domain_comp by auto
  have dh: "domain(x \<circ>\<^sub>c h) = domain(h)" using ch domain_comp by auto
  have dom_gh: "domain(g) = domain(h)" using dg dh xg_eq_xh by simp
  have g_type: "g : domain(g) \<rightarrow> T" unfolding cfunc_type_def using cg dom_x by auto
  have h_type: "h : domain(g) \<rightarrow> T" unfolding cfunc_type_def using ch dom_x dom_gh by auto
  have uniq: "\<exists>! f. f : domain(g) \<rightarrow> T" using term_T unfolding terminal_object_def by auto
  then obtain f where f_type: "f : domain(g) \<rightarrow> T" and f_unique: "\<forall>f'. f' : domain(g) \<rightarrow> T \<longrightarrow> f' = f" by auto
  have "g = f" using g_type f_unique by auto
  moreover have "h = f" using h_type f_unique by auto
  ultimately show "g = h" by simp
qed

text \<open>The lemma below corresponds to Exercise 2.1.15 in Halvorson.\<close>
lemma terminal_objects_isomorphic:
  assumes term_X: "terminal_object(X)" and term_Y: "terminal_object(Y)"
  shows "X \<cong> Y"
  unfolding is_isomorphic_def
proof -
  have exuf: "\<exists>! f. f : X \<rightarrow> Y" using term_Y unfolding terminal_object_def by auto
  then obtain f where f_type: "f : X \<rightarrow> Y" and f_unique: "\<forall>f'. f' : X \<rightarrow> Y \<longrightarrow> f' = f" by auto
  have exug: "\<exists>! g. g : Y \<rightarrow> X" using term_X unfolding terminal_object_def by auto
  then obtain g where g_type: "g : Y \<rightarrow> X" and g_unique: "\<forall>g'. g' : Y \<rightarrow> X \<longrightarrow> g' = g" by auto
  have gf_type: "g \<circ>\<^sub>c f : X \<rightarrow> X" using f_type g_type comp_type by blast
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have exuhX: "\<exists>! h. h : X \<rightarrow> X" using term_X unfolding terminal_object_def by auto
  then obtain hX where hX_type: "hX : X \<rightarrow> X" and hX_unique: "\<forall>h'. h' : X \<rightarrow> X \<longrightarrow> h' = hX" by auto
  have g_f_is_id: "g \<circ>\<^sub>c f = id(X)"
    using gf_type idX_type hX_unique by auto
  have fg_type: "f \<circ>\<^sub>c g : Y \<rightarrow> Y" using f_type g_type comp_type by blast
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have exuhY: "\<exists>! h. h : Y \<rightarrow> Y" using term_Y unfolding terminal_object_def by auto
  then obtain hY where hY_type: "hY : Y \<rightarrow> Y" and hY_unique: "\<forall>h'. h' : Y \<rightarrow> Y \<longrightarrow> h' = hY" by auto
  have f_g_is_id: "f \<circ>\<^sub>c g = id(Y)"
    using fg_type idY_type hY_unique by auto
  have f_iso: "isomorphism(f)"
    unfolding isomorphism_def3[OF f_type]
    using g_type g_f_is_id f_g_is_id by auto
  show "\<exists>f. f : X \<rightarrow> Y \<and> isomorphism(f)" using f_type f_iso by auto
qed

text \<open>Helper lemma (not present in the HOL original): a set with a unique element is terminal.
  Both @{text iso_to1_is_term} and the forward direction of @{text single_elem_iso_one} reduce to
  this same construction, so it is factored out once here.\<close>
lemma unique_elem_gives_terminal:
  assumes x_type: "x \<in>\<^sub>c X"
  assumes x_unique: "\<forall>y. y \<in>\<^sub>c X \<longrightarrow> x = y"
  shows "terminal_object(X)"
  unfolding terminal_object_def
proof (intro allI)
  fix Y
  have xbY_type: "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X" using x_type terminal_func_type comp_type by blast
  show "\<exists>!h. h : Y \<rightarrow> X"
  proof (rule ex1I[where a="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"])
    show "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X" using xbY_type by simp
  next
    fix h
    assume h_type: "h : Y \<rightarrow> X"
    show "h = x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
    proof (rule one_separator[OF h_type xbY_type])
      fix z assume z_type: "z : \<one> \<rightarrow> Y"
      have hz_type: "h \<circ>\<^sub>c z \<in>\<^sub>c X" using h_type z_type comp_type by blast
      have step1: "h \<circ>\<^sub>c z = x" using hz_type x_unique by auto
      have step2: "(x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c z = x \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c z)"
        using comp_associative2[OF z_type terminal_func_type x_type] by simp
      have step3: "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c z = id(\<one>)" using z_type terminal_func_comp_elem by auto
      have step4: "x \<circ>\<^sub>c id(\<one>) = x" using x_type id_right_unit2 by auto
      show "h \<circ>\<^sub>c z = (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c z" using step1 step2 step3 step4 by simp
    qed
  qed
qed

text \<open>The two lemmas below show the converse to Exercise 2.1.15 in Halvorson.\<close>
lemma iso_to1_is_term:
  assumes X_iso_1: "X \<cong> \<one>"
  shows "terminal_object(X)"
proof -
  obtain f where f_type: "f : X \<rightarrow> \<one>" and f_iso: "isomorphism(f)"
    using X_iso_1 is_isomorphic_def by auto
  have f_inv_type: "f\<^bold>\<inverse> : \<one> \<rightarrow> X" using f_iso f_type inverse_type by auto
  have f_mono: "monomorphism(f)" using f_iso iso_imp_epi_and_monic by auto
  have x_type: "f\<^bold>\<inverse> \<in>\<^sub>c X" using f_inv_type by auto
  have x_unique: "\<forall>y. y \<in>\<^sub>c X \<longrightarrow> f\<^bold>\<inverse> = y"
  proof (intro allI impI)
    fix y assume y_type: "y \<in>\<^sub>c X"
    have fy_type: "f \<circ>\<^sub>c y : \<one> \<rightarrow> \<one>" using f_type y_type comp_type by blast
    have fx_type: "f \<circ>\<^sub>c f\<^bold>\<inverse> : \<one> \<rightarrow> \<one>" using f_type x_type comp_type by blast
    have fy_eq: "f \<circ>\<^sub>c y = \<beta>\<^bsub>\<one>\<^esub>" using fy_type terminal_func_unique by auto
    have fx_eq: "f \<circ>\<^sub>c f\<^bold>\<inverse> = \<beta>\<^bsub>\<one>\<^esub>" using fx_type terminal_func_unique by auto
    have fx_eq_fy: "f \<circ>\<^sub>c f\<^bold>\<inverse> = f \<circ>\<^sub>c y" using fx_eq fy_eq by simp
    have mono_iff: "\<forall>g h A. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h)"
      using f_mono monomorphism_def3[OF f_type] by auto
    have both_type: "f\<^bold>\<inverse> : \<one> \<rightarrow> X \<and> y : \<one> \<rightarrow> X" using x_type y_type by auto
    show "f\<^bold>\<inverse> = y"
      using mono_iff[rule_format, where g="f\<^bold>\<inverse>" and h=y and A="\<one>"] both_type fx_eq_fy by auto
  qed
  show ?thesis using x_type x_unique unique_elem_gives_terminal by auto
qed

lemma iso_to_term_is_term:
  assumes X_iso_Y: "X \<cong> Y"
  assumes term_Y: "terminal_object(Y)"
  shows "terminal_object(X)"
proof -
  have Y_iso_1: "Y \<cong> \<one>" using term_Y one_terminal_object terminal_objects_isomorphic by auto
  have conj: "X \<cong> Y \<and> Y \<cong> \<one>" using X_iso_Y Y_iso_1 by auto
  have X_iso_1: "X \<cong> \<one>" using mp[OF isomorphic_is_transitive conj] by simp
  show ?thesis using X_iso_1 iso_to1_is_term by auto
qed

text \<open>The lemma below corresponds to Proposition 2.1.19 in Halvorson.\<close>
lemma single_elem_iso_one:
  "(\<exists>! x. x \<in>\<^sub>c X) \<longleftrightarrow> X \<cong> \<one>"
proof (rule iffI)
  assume ex1: "\<exists>! x. x \<in>\<^sub>c X"
  then obtain x where x_type: "x \<in>\<^sub>c X" and x_unique: "\<forall>y. y \<in>\<^sub>c X \<longrightarrow> x = y" by auto
  have term_X: "terminal_object(X)" using x_type x_unique unique_elem_gives_terminal by auto
  show "X \<cong> \<one>" using term_X one_terminal_object terminal_objects_isomorphic by auto
next
  assume X_iso_1: "X \<cong> \<one>"
  have term_X: "terminal_object(X)" using X_iso_1 iso_to1_is_term by auto
  show "\<exists>! x. x \<in>\<^sub>c X" using term_X unfolding terminal_object_def by auto
qed

subsection \<open>Injectivity\<close>

text \<open>The definition below corresponds to Definition 2.1.24 in Halvorson.\<close>
definition injective :: "cfunc \<Rightarrow> o" where
 "injective(f) \<longleftrightarrow> (\<forall> x y. (x \<in>\<^sub>c domain(f) \<and> y \<in>\<^sub>c domain(f) \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y) \<longrightarrow> x = y)"

lemma injective_def2:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "injective(f) \<longleftrightarrow> (\<forall> x y. (x \<in>\<^sub>c X \<and> y \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y) \<longrightarrow> x = y)"
proof -
  have dom_f: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
  show ?thesis unfolding injective_def using dom_f by auto
qed

text \<open>The lemma below corresponds to Exercise 2.1.26 in Halvorson.\<close>
lemma monomorphism_imp_injective:
  assumes f_mono: "monomorphism(f)"
  shows "injective(f)"
  unfolding injective_def
proof (intro allI impI)
  fix x y
  assume "x \<in>\<^sub>c domain(f) \<and> y \<in>\<^sub>c domain(f) \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
  then have x_type: "x \<in>\<^sub>c domain(f)" and y_type: "y \<in>\<^sub>c domain(f)" and eq: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y" by auto
  have cx: "codomain(x) = domain(f)" using x_type unfolding cfunc_type_def by auto
  have cy: "codomain(y) = domain(f)" using y_type unfolding cfunc_type_def by auto
  have mono_prop: "\<forall>g h. codomain(g) = domain(f) \<and> codomain(h) = domain(f) \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h)"
    using f_mono unfolding monomorphism_def by auto
  show "x = y" using mono_prop[rule_format, where g=x and h=y] cx cy eq by auto
qed

text \<open>The lemma below corresponds to Proposition 2.1.27 in Halvorson.\<close>
lemma injective_imp_monomorphism:
  assumes f_inj: "injective(f)"
  shows "monomorphism(f)"
  unfolding monomorphism_def
proof (intro allI impI)
  fix g h
  assume "codomain(g) = domain(f) \<and> codomain(h) = domain(f)"
  then have cd_g_eq_d_f: "codomain(g) = domain(f)" and cd_h_eq_d_f: "codomain(h) = domain(f)" by auto
  assume fg_eq_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
  obtain X Y where f_type: "f : X \<rightarrow> Y" unfolding cfunc_type_def by auto
  have dom_f_eq_X: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
  have dg: "domain(f \<circ>\<^sub>c g) = domain(g)" using cd_g_eq_d_f domain_comp by auto
  have dh: "domain(f \<circ>\<^sub>c h) = domain(h)" using cd_h_eq_d_f domain_comp by auto
  have dom_gh: "domain(g) = domain(h)" using dg dh fg_eq_fh by simp
  have g_type: "g : domain(g) \<rightarrow> X" unfolding cfunc_type_def using cd_g_eq_d_f dom_f_eq_X by auto
  have h_type: "h : domain(g) \<rightarrow> X" unfolding cfunc_type_def using cd_h_eq_d_f dom_f_eq_X dom_gh by auto
  have f_inj_prop: "\<forall>x y. x \<in>\<^sub>c domain(f) \<and> y \<in>\<^sub>c domain(f) \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y \<longrightarrow> x = y"
    using f_inj unfolding injective_def by auto
  have gx_eq_hx: "\<forall>x. x \<in>\<^sub>c domain(g) \<longrightarrow> g \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
  proof (intro allI impI)
    fix x assume x_in_A: "x \<in>\<^sub>c domain(g)"
    have gx_type: "g \<circ>\<^sub>c x : \<one> \<rightarrow> X" using g_type x_in_A comp_type by blast
    have hx_type: "h \<circ>\<^sub>c x : \<one> \<rightarrow> X" using h_type x_in_A comp_type by blast
    have assoc1: "f \<circ>\<^sub>c (g \<circ>\<^sub>c x) = (f \<circ>\<^sub>c g) \<circ>\<^sub>c x"
      using comp_associative2[OF x_in_A g_type f_type] by simp
    have assoc2: "f \<circ>\<^sub>c (h \<circ>\<^sub>c x) = (f \<circ>\<^sub>c h) \<circ>\<^sub>c x"
      using comp_associative2[OF x_in_A h_type f_type] by simp
    have fgx_eq_fhx: "f \<circ>\<^sub>c (g \<circ>\<^sub>c x) = f \<circ>\<^sub>c (h \<circ>\<^sub>c x)"
      using assoc1 assoc2 fg_eq_fh by simp
    have gx_hx_type: "g \<circ>\<^sub>c x \<in>\<^sub>c domain(f) \<and> h \<circ>\<^sub>c x \<in>\<^sub>c domain(f)" using gx_type hx_type dom_f_eq_X by auto
    show "g \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
      using f_inj_prop[rule_format, where x="g \<circ>\<^sub>c x" and y="h \<circ>\<^sub>c x"] gx_hx_type fgx_eq_fhx by auto
  qed
  have meta: "\<And>x. x : \<one> \<rightarrow> domain(g) \<Longrightarrow> g \<circ>\<^sub>c x = h \<circ>\<^sub>c x" using gx_eq_hx by auto
  show "g = h" using g_type h_type meta by (rule one_separator)
qed

lemma cfunc_cross_prod_inj:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes inj_assms: "injective(f) \<and> injective(g)"
  shows "injective(f \<times>\<^sub>f g)"
proof -
  have f_inj: "injective(f)" and g_inj: "injective(g)" using inj_assms by auto
  have f_mono: "monomorphism(f)" using f_inj injective_imp_monomorphism by auto
  have g_mono: "monomorphism(g)" using g_inj injective_imp_monomorphism by auto
  have fg_mono: "monomorphism(f \<times>\<^sub>f g)"
    using cfunc_cross_prod_mono[OF type_assms(1) type_assms(2) f_mono g_mono] by simp
  show ?thesis using fg_mono monomorphism_imp_injective by auto
qed

lemma cfunc_cross_prod_mono_converse:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes fg_inject: "injective(f \<times>\<^sub>f g)"
  assumes nonempty_assms: "nonempty(X)" "nonempty(Z)"
  shows "injective(f) \<and> injective(g)"
proof -
  have fg_type: "f \<times>\<^sub>f g : X \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c W" using type_assms cfunc_cross_prod_type by auto
  have dom_fg: "domain(f \<times>\<^sub>f g) = X \<times>\<^sub>c Z" using fg_type unfolding cfunc_type_def by auto
  have fg_inj_prop: "\<forall>p q. p \<in>\<^sub>c domain(f \<times>\<^sub>f g) \<and> q \<in>\<^sub>c domain(f \<times>\<^sub>f g) \<and> (f \<times>\<^sub>f g) \<circ>\<^sub>c p = (f \<times>\<^sub>f g) \<circ>\<^sub>c q \<longrightarrow> p = q"
    using fg_inject unfolding injective_def by auto
  have f_inj: "injective(f)"
    unfolding injective_def
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c domain(f) \<and> y \<in>\<^sub>c domain(f) \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c domain(f)" and y_type: "y \<in>\<^sub>c domain(f)" and equals: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y" by auto
    have dom_f: "domain(f) = X" using type_assms(1) unfolding cfunc_type_def by auto
    have x_type2: "x \<in>\<^sub>c X" using x_type dom_f by simp
    have y_type2: "y \<in>\<^sub>c X" using y_type dom_f by simp
    obtain b where b_def: "b \<in>\<^sub>c Z" using nonempty_assms(2) nonempty_def by auto
    have xb_type: "\<langle>x,b\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using x_type2 b_def cfunc_prod_type by auto
    have yb_type: "\<langle>y,b\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using y_type2 b_def cfunc_prod_type by auto
    have step1: "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x,b\<rangle> = \<langle>f \<circ>\<^sub>c x, g \<circ>\<^sub>c b\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF x_type2 b_def type_assms(1) type_assms(2)] by simp
    have step2: "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>y,b\<rangle> = \<langle>f \<circ>\<^sub>c y, g \<circ>\<^sub>c b\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF y_type2 b_def type_assms(1) type_assms(2)] by simp
    have xb_yb_eq: "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x,b\<rangle> = (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>y,b\<rangle>" using step1 step2 equals by simp
    have xb_dom: "\<langle>x,b\<rangle> \<in>\<^sub>c domain(f \<times>\<^sub>f g) \<and> \<langle>y,b\<rangle> \<in>\<^sub>c domain(f \<times>\<^sub>f g)" using xb_type yb_type dom_fg by auto
    have "\<langle>x,b\<rangle> = \<langle>y,b\<rangle>"
      using fg_inj_prop[rule_format, where p="\<langle>x,b\<rangle>" and q="\<langle>y,b\<rangle>"] xb_dom xb_yb_eq by auto
    then show "x = y" using x_type2 y_type2 b_def cart_prod_eq2 by auto
  qed
  have g_inj: "injective(g)"
    unfolding injective_def
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c domain(g) \<and> y \<in>\<^sub>c domain(g) \<and> g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c domain(g)" and y_type: "y \<in>\<^sub>c domain(g)" and equals: "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y" by auto
    have dom_g: "domain(g) = Z" using type_assms(2) unfolding cfunc_type_def by auto
    have x_type2: "x \<in>\<^sub>c Z" using x_type dom_g by simp
    have y_type2: "y \<in>\<^sub>c Z" using y_type dom_g by simp
    obtain b where b_def: "b \<in>\<^sub>c X" using nonempty_assms(1) nonempty_def by auto
    have bx_type: "\<langle>b,x\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using b_def x_type2 cfunc_prod_type by auto
    have by_type: "\<langle>b,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z" using b_def y_type2 cfunc_prod_type by auto
    have step1: "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>b,x\<rangle> = \<langle>f \<circ>\<^sub>c b, g \<circ>\<^sub>c x\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF b_def x_type2 type_assms(1) type_assms(2)] by simp
    have step2: "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>b,y\<rangle> = \<langle>f \<circ>\<^sub>c b, g \<circ>\<^sub>c y\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF b_def y_type2 type_assms(1) type_assms(2)] by simp
    have bx_by_eq: "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>b,x\<rangle> = (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>b,y\<rangle>" using step1 step2 equals by simp
    have bx_dom: "\<langle>b,x\<rangle> \<in>\<^sub>c domain(f \<times>\<^sub>f g) \<and> \<langle>b,y\<rangle> \<in>\<^sub>c domain(f \<times>\<^sub>f g)" using bx_type by_type dom_fg by auto
    have "\<langle>b,x\<rangle> = \<langle>b,y\<rangle>"
      using fg_inj_prop[rule_format, where p="\<langle>b,x\<rangle>" and q="\<langle>b,y\<rangle>"] bx_dom bx_by_eq by auto
    then show "x = y" using x_type2 y_type2 b_def cart_prod_eq2 by auto
  qed
  show ?thesis using f_inj g_inj by auto
qed

text \<open>The next lemma shows that unless both domains are nonempty we gain no new information.
That is, it will be the case that $f \times g$ is injective, and we cannot infer from this that $f$ or $g$ are
injective since $f \times g$ will be injective no matter what.\<close>
lemma the_nonempty_assumption_above_is_always_required:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes empty_assm: "\<not>nonempty(X) \<or> \<not>nonempty(Z)"
  shows "injective(f \<times>\<^sub>f g)"
  unfolding injective_def
proof (intro allI impI)
  fix x y
  assume "x \<in>\<^sub>c domain(f \<times>\<^sub>f g) \<and> y \<in>\<^sub>c domain(f \<times>\<^sub>f g) \<and> (f \<times>\<^sub>f g) \<circ>\<^sub>c x = (f \<times>\<^sub>f g) \<circ>\<^sub>c y"
  then have x_type: "x \<in>\<^sub>c domain(f \<times>\<^sub>f g)" by auto
  have fg_type: "f \<times>\<^sub>f g : X \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c W" using type_assms cfunc_cross_prod_type by auto
  have dom_fg: "domain(f \<times>\<^sub>f g) = X \<times>\<^sub>c Z" using fg_type unfolding cfunc_type_def by auto
  have x_type2: "x \<in>\<^sub>c X \<times>\<^sub>c Z" using x_type dom_fg by simp
  have XZ_empty: "is_empty(X \<times>\<^sub>c Z)"
  proof (cases "nonempty(X)")
    case True
    then have "\<not>nonempty(Z)" using empty_assm by auto
    then have Z_empty: "is_empty(Z)" using nonempty_def is_empty_def by auto
    show ?thesis using prod_with_empty_is_empty2[OF Z_empty] by simp
  next
    case False
    then have X_empty: "is_empty(X)" using nonempty_def is_empty_def by auto
    show ?thesis using prod_with_empty_is_empty1[OF X_empty] by simp
  qed
  then have "\<not>(\<exists>z. z \<in>\<^sub>c X \<times>\<^sub>c Z)" using is_empty_def by auto
  then have False using x_type2 by auto
  then show "x = y" by simp
qed

subsection \<open>Surjectivity\<close>

text \<open>The definition below corresponds to Definition 2.1.28 in Halvorson.\<close>
definition surjective :: "cfunc \<Rightarrow> o" where
 "surjective(f) \<longleftrightarrow> (\<forall>y. y \<in>\<^sub>c codomain(f) \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain(f) \<and> f \<circ>\<^sub>c x = y))"

lemma surjective_def2:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "surjective(f) \<longleftrightarrow> (\<forall>y. y \<in>\<^sub>c Y \<longrightarrow> (\<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x = y))"
proof -
  have dom_f: "domain(f) = X" and cod_f: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  show ?thesis unfolding surjective_def using dom_f cod_f by auto
qed

text \<open>The lemma below corresponds to Exercise 2.1.30 in Halvorson.\<close>
lemma surjective_is_epimorphism:
  assumes f_surj: "surjective(f)"
  shows "epimorphism(f)"
  unfolding epimorphism_def
proof (intro allI impI)
  fix g h
  assume "domain(g) = codomain(f) \<and> domain(h) = codomain(f)"
  then have d_g_eq_cd_f: "domain(g) = codomain(f)" and d_h_eq_cd_f: "domain(h) = codomain(f)" by auto
  assume gf_eq_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
  obtain X Y where f_type: "f : X \<rightarrow> Y" unfolding cfunc_type_def by auto
  have cod_f_eq_Y: "codomain(f) = Y" using f_type unfolding cfunc_type_def by auto
  have codomain_gf: "codomain(g \<circ>\<^sub>c f) = codomain(g)" using d_g_eq_cd_f codomain_comp by auto
  have codomain_hf: "codomain(h \<circ>\<^sub>c f) = codomain(h)" using d_h_eq_cd_f codomain_comp by auto
  have cod_gh: "codomain(g) = codomain(h)" using codomain_gf codomain_hf gf_eq_hf by simp
  have g_type: "g : Y \<rightarrow> codomain(g)" unfolding cfunc_type_def using d_g_eq_cd_f cod_f_eq_Y by auto
  have h_type: "h : Y \<rightarrow> codomain(g)" unfolding cfunc_type_def using d_h_eq_cd_f cod_f_eq_Y cod_gh by auto
  have f_surj_prop: "\<forall>y. y \<in>\<^sub>c codomain(f) \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain(f) \<and> f \<circ>\<^sub>c x = y)"
    using f_surj unfolding surjective_def by auto
  have meta: "\<And>y. y : \<one> \<rightarrow> Y \<Longrightarrow> g \<circ>\<^sub>c y = h \<circ>\<^sub>c y"
  proof -
    fix y assume y_type: "y : \<one> \<rightarrow> Y"
    have y_cod: "y \<in>\<^sub>c codomain(f)" using y_type cod_f_eq_Y by simp
    obtain x where x_type: "x \<in>\<^sub>c domain(f)" and fx_eq_y: "f \<circ>\<^sub>c x = y"
      using f_surj_prop[rule_format, where y=y] y_cod by auto
    have x_type2: "x : \<one> \<rightarrow> X" using x_type f_type unfolding cfunc_type_def by auto
    have assoc1: "g \<circ>\<^sub>c (f \<circ>\<^sub>c x) = (g \<circ>\<^sub>c f) \<circ>\<^sub>c x" using comp_associative2[OF x_type2 f_type g_type] by simp
    have assoc2: "h \<circ>\<^sub>c (f \<circ>\<^sub>c x) = (h \<circ>\<^sub>c f) \<circ>\<^sub>c x" using comp_associative2[OF x_type2 f_type h_type] by simp
    have "g \<circ>\<^sub>c (f \<circ>\<^sub>c x) = h \<circ>\<^sub>c (f \<circ>\<^sub>c x)" using assoc1 assoc2 gf_eq_hf by simp
    then show "g \<circ>\<^sub>c y = h \<circ>\<^sub>c y" using fx_eq_y by simp
  qed
  show "g = h" using g_type h_type meta by (rule one_separator)
qed

text \<open>The lemma below corresponds to Proposition 2.2.10 in Halvorson.\<close>
lemma cfunc_cross_prod_surj:
  assumes type_assms: "f : A \<rightarrow> C" "g : B \<rightarrow> D"
  assumes f_surj: "surjective(f)" and g_surj: "surjective(g)"
  shows "surjective(f \<times>\<^sub>f g)"
  unfolding surjective_def
proof (intro allI impI)
  fix y
  assume y_type: "y \<in>\<^sub>c codomain(f \<times>\<^sub>f g)"
  have fg_type: "f \<times>\<^sub>f g : A \<times>\<^sub>c B \<rightarrow> C \<times>\<^sub>c D" using type_assms cfunc_cross_prod_type by auto
  have cod_fg: "codomain(f \<times>\<^sub>f g) = C \<times>\<^sub>c D" using fg_type unfolding cfunc_type_def by auto
  have y_type2: "y \<in>\<^sub>c C \<times>\<^sub>c D" using y_type cod_fg by simp
  obtain c d where y_def: "y = \<langle>c,d\<rangle>" and c_type: "c \<in>\<^sub>c C" and d_type: "d \<in>\<^sub>c D"
    using cart_prod_decomp[OF y_type2] by blast
  have f_surj_prop: "\<forall>y. y \<in>\<^sub>c C \<longrightarrow> (\<exists>x. x \<in>\<^sub>c A \<and> f \<circ>\<^sub>c x = y)"
    using f_surj surjective_def2[OF type_assms(1)] by auto
  have g_surj_prop: "\<forall>y. y \<in>\<^sub>c D \<longrightarrow> (\<exists>x. x \<in>\<^sub>c B \<and> g \<circ>\<^sub>c x = y)"
    using g_surj surjective_def2[OF type_assms(2)] by auto
  obtain a where a_type: "a \<in>\<^sub>c A" and fa_eq_c: "f \<circ>\<^sub>c a = c"
    using f_surj_prop[rule_format, where y=c] c_type by auto
  obtain b where b_type: "b \<in>\<^sub>c B" and gb_eq_d: "g \<circ>\<^sub>c b = d"
    using g_surj_prop[rule_format, where y=d] d_type by auto
  define x where "x = \<langle>a,b\<rangle>"
  have x_type: "x \<in>\<^sub>c domain(f \<times>\<^sub>f g)"
  proof -
    have "x \<in>\<^sub>c A \<times>\<^sub>c B" unfolding x_def using a_type b_type cfunc_prod_type by auto
    then show ?thesis using fg_type unfolding cfunc_type_def by auto
  qed
  have "(f \<times>\<^sub>f g) \<circ>\<^sub>c x = y"
  proof -
    have "(f \<times>\<^sub>f g) \<circ>\<^sub>c x = \<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle>"
      unfolding x_def using cfunc_cross_prod_comp_cfunc_prod[OF a_type b_type type_assms(1) type_assms(2)] by simp
    also have "... = \<langle>c, d\<rangle>" using fa_eq_c gb_eq_d by simp
    also have "... = y" using y_def by simp
    finally show ?thesis by simp
  qed
  then show "\<exists>x. x \<in>\<^sub>c domain(f \<times>\<^sub>f g) \<and> (f \<times>\<^sub>f g) \<circ>\<^sub>c x = y" using x_type by auto
qed

lemma cfunc_cross_prod_surj_converse:
  assumes type_assms: "f : A \<rightarrow> C" "g : B \<rightarrow> D"
  assumes nonempty_assms: "nonempty(C) \<and> nonempty(D)"
  assumes fg_surj: "surjective(f \<times>\<^sub>f g)"
  shows "surjective(f) \<and> surjective(g)"
proof -
  have fg_type: "f \<times>\<^sub>f g : A \<times>\<^sub>c B \<rightarrow> C \<times>\<^sub>c D" using type_assms cfunc_cross_prod_type by auto
  have fg_surj_prop: "\<forall>y. y \<in>\<^sub>c C \<times>\<^sub>c D \<longrightarrow> (\<exists>ab. ab \<in>\<^sub>c A \<times>\<^sub>c B \<and> (f \<times>\<^sub>f g) \<circ>\<^sub>c ab = y)"
    using fg_surj surjective_def2[OF fg_type] by auto
  have f_surj: "surjective(f)"
    unfolding surjective_def2[OF type_assms(1)]
  proof (intro allI impI)
    fix c assume c_type: "c \<in>\<^sub>c C"
    obtain d where d_type: "d \<in>\<^sub>c D" using nonempty_assms nonempty_def by auto
    have cd_type: "\<langle>c,d\<rangle> \<in>\<^sub>c C \<times>\<^sub>c D" using c_type d_type cfunc_prod_type by auto
    obtain ab where ab_type: "ab \<in>\<^sub>c A \<times>\<^sub>c B" and ab_def: "(f \<times>\<^sub>f g) \<circ>\<^sub>c ab = \<langle>c,d\<rangle>"
      using fg_surj_prop[rule_format, where y="\<langle>c,d\<rangle>"] cd_type by auto
    obtain a b where ab_def2: "ab = \<langle>a,b\<rangle>" and a_type: "a \<in>\<^sub>c A" and b_type: "b \<in>\<^sub>c B"
      using cart_prod_decomp[OF ab_type] by blast
    have fab_eq: "\<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle> = \<langle>c,d\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF a_type b_type type_assms(1) type_assms(2)] ab_def ab_def2 by simp
    have fa_type: "f \<circ>\<^sub>c a \<in>\<^sub>c C" using a_type type_assms(1) comp_type by blast
    have gb_type: "g \<circ>\<^sub>c b \<in>\<^sub>c D" using b_type type_assms(2) comp_type by blast
    have "f \<circ>\<^sub>c a = c \<and> g \<circ>\<^sub>c b = d"
      using fab_eq fa_type gb_type c_type d_type cart_prod_eq2 by auto
    then show "\<exists>x. x \<in>\<^sub>c A \<and> f \<circ>\<^sub>c x = c" using a_type by auto
  qed
  have g_surj: "surjective(g)"
    unfolding surjective_def2[OF type_assms(2)]
  proof (intro allI impI)
    fix d assume d_type: "d \<in>\<^sub>c D"
    obtain c where c_type: "c \<in>\<^sub>c C" using nonempty_assms nonempty_def by auto
    have cd_type: "\<langle>c,d\<rangle> \<in>\<^sub>c C \<times>\<^sub>c D" using c_type d_type cfunc_prod_type by auto
    obtain ab where ab_type: "ab \<in>\<^sub>c A \<times>\<^sub>c B" and ab_def: "(f \<times>\<^sub>f g) \<circ>\<^sub>c ab = \<langle>c,d\<rangle>"
      using fg_surj_prop[rule_format, where y="\<langle>c,d\<rangle>"] cd_type by auto
    obtain a b where ab_def2: "ab = \<langle>a,b\<rangle>" and a_type: "a \<in>\<^sub>c A" and b_type: "b \<in>\<^sub>c B"
      using cart_prod_decomp[OF ab_type] by blast
    have fab_eq: "\<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle> = \<langle>c,d\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF a_type b_type type_assms(1) type_assms(2)] ab_def ab_def2 by simp
    have fa_type: "f \<circ>\<^sub>c a \<in>\<^sub>c C" using a_type type_assms(1) comp_type by blast
    have gb_type: "g \<circ>\<^sub>c b \<in>\<^sub>c D" using b_type type_assms(2) comp_type by blast
    have "f \<circ>\<^sub>c a = c \<and> g \<circ>\<^sub>c b = d"
      using fab_eq fa_type gb_type c_type d_type cart_prod_eq2 by auto
    then show "\<exists>x. x \<in>\<^sub>c B \<and> g \<circ>\<^sub>c x = d" using b_type by auto
  qed
  show ?thesis using f_surj g_surj by auto
qed

subsection \<open>Interactions of Cartesian Products with Terminal Objects\<close>

lemma diag_on_elements:
  assumes x_type: "x \<in>\<^sub>c X"
  shows "diagonal(X) \<circ>\<^sub>c x = \<langle>x,x\<rangle>"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have "diagonal(X) \<circ>\<^sub>c x = \<langle>id(X),id(X)\<rangle> \<circ>\<^sub>c x" unfolding diagonal_def by simp
  also have "... = \<langle>id(X) \<circ>\<^sub>c x, id(X) \<circ>\<^sub>c x\<rangle>"
    using cfunc_prod_comp[OF x_type idX_type idX_type] by simp
  also have "... = \<langle>x,x\<rangle>" using id_left_unit2[OF x_type] by simp
  finally show ?thesis by simp
qed

lemma one_cross_one_unique_element: "\<exists>! x. x \<in>\<^sub>c \<one> \<times>\<^sub>c \<one>"
proof (rule ex1I[where a="diagonal(\<one>)"])
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  show "diagonal(\<one>) \<in>\<^sub>c \<one> \<times>\<^sub>c \<one>" unfolding diagonal_def using cfunc_prod_type[OF id1_type id1_type] by simp
next
  fix x
  assume x_type: "x \<in>\<^sub>c \<one> \<times>\<^sub>c \<one>"
  have lp_type: "left_cart_proj(\<one>, \<one>) : \<one> \<times>\<^sub>c \<one> \<rightarrow> \<one>" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(\<one>, \<one>) : \<one> \<times>\<^sub>c \<one> \<rightarrow> \<one>" by (rule right_cart_proj_type)
  have left_eq: "left_cart_proj(\<one>, \<one>) \<circ>\<^sub>c x = id(\<one>)"
  proof -
    have "left_cart_proj(\<one>, \<one>) \<circ>\<^sub>c x \<in>\<^sub>c \<one>" using x_type lp_type comp_type by blast
    then show ?thesis using element_of_1 by auto
  qed
  have right_eq: "right_cart_proj(\<one>, \<one>) \<circ>\<^sub>c x = id(\<one>)"
  proof -
    have "right_cart_proj(\<one>, \<one>) \<circ>\<^sub>c x \<in>\<^sub>c \<one>" using x_type rp_type comp_type by blast
    then show ?thesis using element_of_1 by auto
  qed
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  show "x = diagonal(\<one>)"
    unfolding diagonal_def
  proof (rule cfunc_prod_unique)
    show "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id1_type)
    show "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id1_type)
    show "x : \<one> \<rightarrow> \<one> \<times>\<^sub>c \<one>" by (rule x_type)
    show "left_cart_proj(\<one>, \<one>) \<circ>\<^sub>c x = id(\<one>)" by (rule left_eq)
    show "right_cart_proj(\<one>, \<one>) \<circ>\<^sub>c x = id(\<one>)" by (rule right_eq)
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.1.20 in Halvorson.\<close>
lemma X_is_cart_prod1:
  "is_cart_prod(X, id(X), \<beta>\<^bsub>X\<^esub>, X, \<one>)"
  unfolding is_cart_prod_def
proof (intro conjI)
  show "id(X) : X \<rightarrow> X" by (rule id_type)
  show "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  show "\<forall>f g Y. (f : Y \<rightarrow> X \<and> g : Y \<rightarrow> \<one>) \<longrightarrow>
    (\<exists>h. h : Y \<rightarrow> X \<and> id(X) \<circ>\<^sub>c h = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = g \<and>
      (\<forall>h2. (h2 : Y \<rightarrow> X \<and> id(X) \<circ>\<^sub>c h2 = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h))"
  proof (intro allI impI)
    fix f g Y
    assume "f : Y \<rightarrow> X \<and> g : Y \<rightarrow> \<one>"
    then have f_type: "f : Y \<rightarrow> X" and g_type: "g : Y \<rightarrow> \<one>" by auto
    have idXf_eq: "id(X) \<circ>\<^sub>c f = f" using id_left_unit2[OF f_type] by simp
    have betaf_eq: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f = g"
    proof -
      have "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f : Y \<rightarrow> \<one>" using f_type terminal_func_type comp_type by blast
      then show ?thesis using g_type terminal_func_unique by auto
    qed
    have uniq: "\<forall>h2. (h2 : Y \<rightarrow> X \<and> id(X) \<circ>\<^sub>c h2 = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = f"
    proof (intro allI impI)
      fix h2 assume "h2 : Y \<rightarrow> X \<and> id(X) \<circ>\<^sub>c h2 = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = g"
      then have h2_type: "h2 : Y \<rightarrow> X" and h2_eq: "id(X) \<circ>\<^sub>c h2 = f" by auto
      have "h2 = id(X) \<circ>\<^sub>c h2" using id_left_unit2[OF h2_type] by simp
      then show "h2 = f" using h2_eq by simp
    qed
    show "\<exists>h. h : Y \<rightarrow> X \<and> id(X) \<circ>\<^sub>c h = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = g \<and>
      (\<forall>h2. (h2 : Y \<rightarrow> X \<and> id(X) \<circ>\<^sub>c h2 = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h)"
      using f_type idXf_eq betaf_eq uniq by auto
  qed
qed

lemma X_is_cart_prod2:
  "is_cart_prod(X, \<beta>\<^bsub>X\<^esub>, id(X), \<one>, X)"
  unfolding is_cart_prod_def
proof (intro conjI)
  show "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  show "id(X) : X \<rightarrow> X" by (rule id_type)
  show "\<forall>f g Z. (f : Z \<rightarrow> \<one> \<and> g : Z \<rightarrow> X) \<longrightarrow>
    (\<exists>h. h : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = f \<and> id(X) \<circ>\<^sub>c h = g \<and>
      (\<forall>h2. (h2 : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = f \<and> id(X) \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h))"
  proof (intro allI impI)
    fix f g Z
    assume "f : Z \<rightarrow> \<one> \<and> g : Z \<rightarrow> X"
    then have f_type: "f : Z \<rightarrow> \<one>" and g_type: "g : Z \<rightarrow> X" by auto
    have idXg_eq: "id(X) \<circ>\<^sub>c g = g" using id_left_unit2[OF g_type] by simp
    have betag_eq: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g = f"
    proof -
      have "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g : Z \<rightarrow> \<one>" using g_type terminal_func_type comp_type by blast
      then show ?thesis using f_type terminal_func_unique by auto
    qed
    have uniq: "\<forall>h2. (h2 : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = f \<and> id(X) \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = g"
    proof (intro allI impI)
      fix h2 assume "h2 : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = f \<and> id(X) \<circ>\<^sub>c h2 = g"
      then have h2_type: "h2 : Z \<rightarrow> X" and h2_eq: "id(X) \<circ>\<^sub>c h2 = g" by auto
      have "h2 = id(X) \<circ>\<^sub>c h2" using id_left_unit2[OF h2_type] by simp
      then show "h2 = g" using h2_eq by simp
    qed
    show "\<exists>h. h : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = f \<and> id(X) \<circ>\<^sub>c h = g \<and>
      (\<forall>h2. (h2 : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = f \<and> id(X) \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h)"
      using g_type betag_eq idXg_eq uniq by auto
  qed
qed

lemma A_x_one_iso_A: "X \<times>\<^sub>c \<one> \<cong> X"
proof -
  have h1: "is_cart_prod(X, id(X), \<beta>\<^bsub>X\<^esub>, X, \<one>)" by (rule X_is_cart_prod1)
  have h2: "is_cart_prod(X \<times>\<^sub>c \<one>, left_cart_proj(X, \<one>), right_cart_proj(X, \<one>), X, \<one>)"
    by (rule canonical_cart_prod_is_cart_prod)
  obtain f where f_def: "f : X \<times>\<^sub>c \<one> \<rightarrow> X \<and> isomorphism(f) \<and> id(X) \<circ>\<^sub>c f = left_cart_proj(X, \<one>) \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f = right_cart_proj(X, \<one>)"
    using cart_prods_isomorphic[OF h2 h1] by blast
  show ?thesis unfolding is_isomorphic_def using f_def by auto
qed

lemma one_x_A_iso_A: "\<one> \<times>\<^sub>c X \<cong> X"
proof -
  have h1: "\<one> \<times>\<^sub>c X \<cong> X \<times>\<^sub>c \<one>" by (rule product_commutes)
  have h2: "X \<times>\<^sub>c \<one> \<cong> X" by (rule A_x_one_iso_A)
  have conj: "\<one> \<times>\<^sub>c X \<cong> X \<times>\<^sub>c \<one> \<and> X \<times>\<^sub>c \<one> \<cong> X" using h1 h2 by auto
  show ?thesis using mp[OF isomorphic_is_transitive conj] by simp
qed

text \<open>The following four lemmas provide some concrete examples of the above isomorphisms\<close>
lemma left_cart_proj_one_left_inverse:
  "\<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>) = id(X \<times>\<^sub>c \<one>)"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have pair_type: "\<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c \<one>" using idX_type bX_type cfunc_prod_type by auto
  have lp_type: "left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<one>" by (rule right_cart_proj_type)
  have T_type: "\<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X \<times>\<^sub>c \<one>"
    using lp_type pair_type comp_type by blast
  have idXone_type: "id(X \<times>\<^sub>c \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X \<times>\<^sub>c \<one>" by (rule id_type)
  have left_eq: "left_cart_proj(X, \<one>) \<circ>\<^sub>c (\<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>)) = left_cart_proj(X, \<one>)"
  proof -
    have "left_cart_proj(X, \<one>) \<circ>\<^sub>c (\<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>))
      = (left_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>)"
      using comp_associative2[OF lp_type pair_type lp_type] by simp
    also have "... = id(X) \<circ>\<^sub>c left_cart_proj(X, \<one>)"
      using left_cart_proj_cfunc_prod[OF idX_type bX_type] by simp
    also have "... = left_cart_proj(X, \<one>)"
      using id_left_unit2[OF lp_type] by simp
    finally show ?thesis by simp
  qed
  have right_eq: "right_cart_proj(X, \<one>) \<circ>\<^sub>c (\<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>)) = right_cart_proj(X, \<one>)"
  proof -
    have "right_cart_proj(X, \<one>) \<circ>\<^sub>c (\<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>))
      = (right_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>)"
      using comp_associative2[OF lp_type pair_type rp_type] by simp
    also have "... = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, \<one>)"
      using right_cart_proj_cfunc_prod[OF idX_type bX_type] by simp
    also have "... = right_cart_proj(X, \<one>)"
    proof -
      have e_type: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<one>" using lp_type bX_type comp_type by blast
      have e_eq: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, \<one>) = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>" using e_type terminal_func_unique by auto
      have rp_eq: "right_cart_proj(X, \<one>) = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>" using rp_type terminal_func_unique by auto
      show ?thesis using e_eq rp_eq by simp
    qed
    finally show ?thesis by simp
  qed
  have left_eq2: "left_cart_proj(X, \<one>) \<circ>\<^sub>c id(X \<times>\<^sub>c \<one>) = left_cart_proj(X, \<one>)"
    using id_right_unit2[OF lp_type] by simp
  have right_eq2: "right_cart_proj(X, \<one>) \<circ>\<^sub>c id(X \<times>\<^sub>c \<one>) = right_cart_proj(X, \<one>)"
    using id_right_unit2[OF rp_type] by simp
  show ?thesis
    using cart_prod_eq[OF T_type idXone_type] left_eq right_eq left_eq2 right_eq2 by auto
qed

lemma left_cart_proj_one_right_inverse:
  "left_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>id(X),\<beta>\<^bsub>X\<^esub>\<rangle> = id(X)"
  using left_cart_proj_cfunc_prod[OF id_type terminal_func_type] by simp

lemma right_cart_proj_one_left_inverse:
  "\<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> \<circ>\<^sub>c right_cart_proj(\<one>, X) = id(\<one> \<times>\<^sub>c X)"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have pair_type: "\<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> : X \<rightarrow> \<one> \<times>\<^sub>c X" using bX_type idX_type cfunc_prod_type by auto
  have lp_type: "left_cart_proj(\<one>, X) : \<one> \<times>\<^sub>c X \<rightarrow> \<one>" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(\<one>, X) : \<one> \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)
  have T_type: "\<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> \<circ>\<^sub>c right_cart_proj(\<one>, X) : \<one> \<times>\<^sub>c X \<rightarrow> \<one> \<times>\<^sub>c X"
    using rp_type pair_type comp_type by blast
  have id1X_type: "id(\<one> \<times>\<^sub>c X) : \<one> \<times>\<^sub>c X \<rightarrow> \<one> \<times>\<^sub>c X" by (rule id_type)
  have left_eq: "left_cart_proj(\<one>, X) \<circ>\<^sub>c (\<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> \<circ>\<^sub>c right_cart_proj(\<one>, X)) = left_cart_proj(\<one>, X)"
  proof -
    have "left_cart_proj(\<one>, X) \<circ>\<^sub>c (\<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> \<circ>\<^sub>c right_cart_proj(\<one>, X))
      = (left_cart_proj(\<one>, X) \<circ>\<^sub>c \<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle>) \<circ>\<^sub>c right_cart_proj(\<one>, X)"
      using comp_associative2[OF rp_type pair_type lp_type] by simp
    also have "... = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c right_cart_proj(\<one>, X)"
      using left_cart_proj_cfunc_prod[OF bX_type idX_type] by simp
    also have "... = left_cart_proj(\<one>, X)"
    proof -
      have e_type: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c right_cart_proj(\<one>, X) : \<one> \<times>\<^sub>c X \<rightarrow> \<one>" using rp_type bX_type comp_type by blast
      have e_eq: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c right_cart_proj(\<one>, X) = \<beta>\<^bsub>\<one> \<times>\<^sub>c X\<^esub>" using e_type terminal_func_unique by auto
      have lp_eq: "left_cart_proj(\<one>, X) = \<beta>\<^bsub>\<one> \<times>\<^sub>c X\<^esub>" using lp_type terminal_func_unique by auto
      show ?thesis using e_eq lp_eq by simp
    qed
    finally show ?thesis by simp
  qed
  have right_eq: "right_cart_proj(\<one>, X) \<circ>\<^sub>c (\<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> \<circ>\<^sub>c right_cart_proj(\<one>, X)) = right_cart_proj(\<one>, X)"
  proof -
    have "right_cart_proj(\<one>, X) \<circ>\<^sub>c (\<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> \<circ>\<^sub>c right_cart_proj(\<one>, X))
      = (right_cart_proj(\<one>, X) \<circ>\<^sub>c \<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle>) \<circ>\<^sub>c right_cart_proj(\<one>, X)"
      using comp_associative2[OF rp_type pair_type rp_type] by simp
    also have "... = id(X) \<circ>\<^sub>c right_cart_proj(\<one>, X)"
      using right_cart_proj_cfunc_prod[OF bX_type idX_type] by simp
    also have "... = right_cart_proj(\<one>, X)"
      using id_left_unit2[OF rp_type] by simp
    finally show ?thesis by simp
  qed
  have left_eq2: "left_cart_proj(\<one>, X) \<circ>\<^sub>c id(\<one> \<times>\<^sub>c X) = left_cart_proj(\<one>, X)"
    using id_right_unit2[OF lp_type] by simp
  have right_eq2: "right_cart_proj(\<one>, X) \<circ>\<^sub>c id(\<one> \<times>\<^sub>c X) = right_cart_proj(\<one>, X)"
    using id_right_unit2[OF rp_type] by simp
  show ?thesis
    using cart_prod_eq[OF T_type id1X_type] left_eq right_eq left_eq2 right_eq2 by auto
qed

lemma right_cart_proj_one_right_inverse:
  "right_cart_proj(\<one>, X) \<circ>\<^sub>c \<langle>\<beta>\<^bsub>X\<^esub>,id(X)\<rangle> = id(X)"
  using right_cart_proj_cfunc_prod[OF terminal_func_type id_type] by simp

lemma cfunc_cross_prod_right_terminal_decomp:
  assumes f_type: "f : X \<rightarrow> Y" and x_type: "x : \<one> \<rightarrow> Z"
  shows "f \<times>\<^sub>f x = \<langle>f, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>)"
proof -
  have lp_type: "left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<one>" by (rule right_cart_proj_type)
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have xbX_type: "x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> Z" using bX_type x_type comp_type by blast
  have "f \<times>\<^sub>f x = \<langle>f \<circ>\<^sub>c left_cart_proj(X, \<one>), x \<circ>\<^sub>c right_cart_proj(X, \<one>)\<rangle>"
    using cfunc_cross_prod_def2[OF f_type x_type] by simp
  moreover have "\<langle>f, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>) = \<langle>f \<circ>\<^sub>c left_cart_proj(X, \<one>), x \<circ>\<^sub>c right_cart_proj(X, \<one>)\<rangle>"
  proof -
    have "\<langle>f, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(X, \<one>) = \<langle>f \<circ>\<^sub>c left_cart_proj(X, \<one>), (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c left_cart_proj(X, \<one>)\<rangle>"
      using cfunc_prod_comp[OF lp_type f_type xbX_type] by simp
    also have "... = \<langle>f \<circ>\<^sub>c left_cart_proj(X, \<one>), x \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, \<one>))\<rangle>"
      using comp_associative2[OF lp_type bX_type x_type] by simp
    also have "... = \<langle>f \<circ>\<^sub>c left_cart_proj(X, \<one>), x \<circ>\<^sub>c right_cart_proj(X, \<one>)\<rangle>"
    proof -
      have e_type: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> \<one>" using lp_type bX_type comp_type by blast
      have e_eq: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c left_cart_proj(X, \<one>) = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>" using e_type terminal_func_unique by auto
      have rp_eq: "right_cart_proj(X, \<one>) = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>" using rp_type terminal_func_unique by auto
      show ?thesis using e_eq rp_eq by simp
    qed
    finally show ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

text \<open>The lemma below corresponds to Proposition 2.1.21 in Halvorson.\<close>
lemma cart_prod_elem_eq:
  assumes a_type: "a \<in>\<^sub>c X \<times>\<^sub>c Y" and b_type: "b \<in>\<^sub>c X \<times>\<^sub>c Y"
  shows "a = b \<longleftrightarrow>
    (left_cart_proj(X, Y) \<circ>\<^sub>c a = left_cart_proj(X, Y) \<circ>\<^sub>c b
      \<and> right_cart_proj(X, Y) \<circ>\<^sub>c a = right_cart_proj(X, Y) \<circ>\<^sub>c b)"
  using cart_prod_eq[OF a_type b_type] by simp

text \<open>The lemma below corresponds to Note 2.1.22 in Halvorson.\<close>
lemma element_pair_eq:
  assumes x_type: "x \<in>\<^sub>c X" and x'_type: "x' \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c Y" and y'_type: "y' \<in>\<^sub>c Y"
  shows "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle> \<longleftrightarrow> x = x' \<and> y = y'"
  using cart_prod_eq2[OF x_type y_type x'_type y'_type] by simp

text \<open>The lemma below corresponds to Proposition 2.1.23 in Halvorson.\<close>
lemma nonempty_right_imp_left_proj_epimorphism:
  assumes Y_nonempty: "nonempty(Y)"
  shows "epimorphism(left_cart_proj(X, Y))"
proof -
  obtain y where y_in_Y: "y : \<one> \<rightarrow> Y" using Y_nonempty nonempty_def by auto
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have ybX_type: "y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> Y" using bX_type y_in_Y comp_type by blast
  have cp_type: "\<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c Y" using idX_type ybX_type cfunc_prod_type by auto
  have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have id_eq: "left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> = id(X)"
    using left_cart_proj_cfunc_prod[OF idX_type ybX_type] by simp
  show ?thesis
    unfolding epimorphism_def
  proof (intro allI impI)
    fix g h
    assume "domain(g) = codomain(left_cart_proj(X, Y)) \<and> domain(h) = codomain(left_cart_proj(X, Y))"
    then have domain_g: "domain(g) = codomain(left_cart_proj(X, Y))"
      and domain_h: "domain(h) = codomain(left_cart_proj(X, Y))" by auto
    assume gp_eq_hp: "g \<circ>\<^sub>c left_cart_proj(X, Y) = h \<circ>\<^sub>c left_cart_proj(X, Y)"
    have cod_lp: "codomain(left_cart_proj(X, Y)) = X" using lp_type unfolding cfunc_type_def by auto
    have g_type: "g : X \<rightarrow> codomain(g)" unfolding cfunc_type_def using domain_g cod_lp by auto
    have h_type: "h : X \<rightarrow> codomain(h)" unfolding cfunc_type_def using domain_h cod_lp by auto
    have assoc1: "g \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) = (g \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
      using comp_associative2[OF cp_type lp_type g_type] by simp
    have assoc2: "h \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) = (h \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
      using comp_associative2[OF cp_type lp_type h_type] by simp
    have "g \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) = h \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>id(X), y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"
      using assoc1 assoc2 gp_eq_hp by simp
    then have "g \<circ>\<^sub>c id(X) = h \<circ>\<^sub>c id(X)" using id_eq by simp
    then show "g = h" using id_right_unit2[OF g_type] id_right_unit2[OF h_type] by simp
  qed
qed

text \<open>The lemma below is the dual of Proposition 2.1.23 in Halvorson.\<close>
lemma nonempty_left_imp_right_proj_epimorphism:
  assumes X_nonempty: "nonempty(X)"
  shows "epimorphism(right_cart_proj(X, Y))"
proof -
  obtain y where y_in_X: "y : \<one> \<rightarrow> X" using X_nonempty nonempty_def by auto
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have bY_type: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by (rule terminal_func_type)
  have ybY_type: "y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X" using bY_type y_in_X comp_type by blast
  have cp_type: "\<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> : Y \<rightarrow> X \<times>\<^sub>c Y" using ybY_type idY_type cfunc_prod_type by auto
  have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have id_eq: "right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> = id(Y)"
    using right_cart_proj_cfunc_prod[OF ybY_type idY_type] by simp
  show ?thesis
    unfolding epimorphism_def
  proof (intro allI impI)
    fix g h
    assume "domain(g) = codomain(right_cart_proj(X, Y)) \<and> domain(h) = codomain(right_cart_proj(X, Y))"
    then have domain_g: "domain(g) = codomain(right_cart_proj(X, Y))"
      and domain_h: "domain(h) = codomain(right_cart_proj(X, Y))" by auto
    assume gp_eq_hp: "g \<circ>\<^sub>c right_cart_proj(X, Y) = h \<circ>\<^sub>c right_cart_proj(X, Y)"
    have cod_rp: "codomain(right_cart_proj(X, Y)) = Y" using rp_type unfolding cfunc_type_def by auto
    have g_type: "g : Y \<rightarrow> codomain(g)" unfolding cfunc_type_def using domain_g cod_rp by auto
    have h_type: "h : Y \<rightarrow> codomain(h)" unfolding cfunc_type_def using domain_h cod_rp by auto
    have assoc1: "g \<circ>\<^sub>c (right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>) = (g \<circ>\<^sub>c right_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>"
      using comp_associative2[OF cp_type rp_type g_type] by simp
    have assoc2: "h \<circ>\<^sub>c (right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>) = (h \<circ>\<^sub>c right_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>"
      using comp_associative2[OF cp_type rp_type h_type] by simp
    have "g \<circ>\<^sub>c (right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>) = h \<circ>\<^sub>c (right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle>)"
      using assoc1 assoc2 gp_eq_hp by simp
    then have "g \<circ>\<^sub>c id(Y) = h \<circ>\<^sub>c id(Y)" using id_eq by simp
    then show "g = h" using id_right_unit2[OF g_type] id_right_unit2[OF h_type] by simp
  qed
qed

lemma cart_prod_extract_left:
  assumes f_type: "f : \<one> \<rightarrow> X" and g_type: "g : \<one> \<rightarrow> Y"
  shows "\<langle>f, g\<rangle> = \<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c f"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have bX_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<one>" by (rule terminal_func_type)
  have bXf_type: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f : \<one> \<rightarrow> \<one>" using f_type bX_type comp_type by blast
  have bXf_eq: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f = id(\<one>)"
  proof -
    have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
    have "\<exists>! z. z \<in>\<^sub>c \<one>" by (rule one_unique_element)
    then obtain z where z_type: "z \<in>\<^sub>c \<one>" and z_unique: "\<forall>w. w \<in>\<^sub>c \<one> \<longrightarrow> z = w" by auto
    have "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f = z" using bXf_type z_unique by auto
    moreover have "id(\<one>) = z" using id1_type z_unique by auto
    ultimately show ?thesis by simp
  qed
  have "\<langle>f, g\<rangle> = \<langle>id(X) \<circ>\<^sub>c f, g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f\<rangle>"
  proof -
    have step1: "id(X) \<circ>\<^sub>c f = f" using id_left_unit2[OF f_type] by simp
    have step2: "g \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f) = g" using bXf_eq id_right_unit2[OF g_type] by simp
    show ?thesis using step1 step2 by simp
  qed
  also have "... = \<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c f"
  proof -
    have gbX_type: "g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> Y" using bX_type g_type comp_type by blast
    have "\<langle>id(X), g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c f = \<langle>id(X) \<circ>\<^sub>c f, (g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c f\<rangle>"
      using cfunc_prod_comp[OF f_type idX_type gbX_type] by simp
    also have "... = \<langle>id(X) \<circ>\<^sub>c f, g \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f)\<rangle>"
      using comp_associative2[OF f_type bX_type g_type] by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

lemma cart_prod_extract_right:
  assumes f_type: "f : \<one> \<rightarrow> X" and g_type: "g : \<one> \<rightarrow> Y"
  shows "\<langle>f, g\<rangle> = \<langle>f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> \<circ>\<^sub>c g"
proof -
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have bY_type: "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> \<one>" by (rule terminal_func_type)
  have bYg_type: "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g : \<one> \<rightarrow> \<one>" using g_type bY_type comp_type by blast
  have bYg_eq: "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g = id(\<one>)"
  proof -
    have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
    have "\<exists>! z. z \<in>\<^sub>c \<one>" by (rule one_unique_element)
    then obtain z where z_type: "z \<in>\<^sub>c \<one>" and z_unique: "\<forall>w. w \<in>\<^sub>c \<one> \<longrightarrow> z = w" by auto
    have "\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g = z" using bYg_type z_unique by auto
    moreover have "id(\<one>) = z" using id1_type z_unique by auto
    ultimately show ?thesis by simp
  qed
  have "\<langle>f, g\<rangle> = \<langle>f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g, id(Y) \<circ>\<^sub>c g\<rangle>"
  proof -
    have step1: "f \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g) = f" using bYg_eq id_right_unit2[OF f_type] by simp
    have step2: "id(Y) \<circ>\<^sub>c g = g" using id_left_unit2[OF g_type] by simp
    show ?thesis using step1 step2 by simp
  qed
  also have "... = \<langle>f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> \<circ>\<^sub>c g"
  proof -
    have fbY_type: "f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X" using bY_type f_type comp_type by blast
    have "\<langle>f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id(Y)\<rangle> \<circ>\<^sub>c g = \<langle>(f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c g, id(Y) \<circ>\<^sub>c g\<rangle>"
      using cfunc_prod_comp[OF g_type fbY_type idY_type] by simp
    also have "... = \<langle>f \<circ>\<^sub>c (\<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g), id(Y) \<circ>\<^sub>c g\<rangle>"
      using comp_associative2[OF g_type bY_type f_type] by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

subsubsection \<open>Cartesian Products as Pullbacks\<close>

text \<open>The definition below corresponds to a definition stated between Definition 2.1.42 and Definition 2.1.43 in Halvorson.\<close>
definition is_pullback :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> o" where
  "is_pullback(A, B, C, D, ab, bd, ac, cd) \<longleftrightarrow>
    (ab : A \<rightarrow> B \<and> bd : B \<rightarrow> D \<and> ac : A \<rightarrow> C \<and> cd : C \<rightarrow> D \<and> bd \<circ>\<^sub>c ab = cd \<circ>\<^sub>c ac \<and>
    (\<forall> Z k h. (k : Z \<rightarrow> B \<and> h : Z \<rightarrow> C \<and> bd \<circ>\<^sub>c k = cd \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> A \<and> ab \<circ>\<^sub>c j = k \<and> ac \<circ>\<^sub>c j = h)))"

lemma pullback_unique:
  assumes ab_type: "ab : A \<rightarrow> B" and bd_type: "bd : B \<rightarrow> D" and ac_type: "ac : A \<rightarrow> C" and cd_type: "cd : C \<rightarrow> D"
  assumes k_type: "k : Z \<rightarrow> B" and h_type: "h : Z \<rightarrow> C"
  assumes pb: "is_pullback(A, B, C, D, ab, bd, ac, cd)"
  shows "bd \<circ>\<^sub>c k = cd \<circ>\<^sub>c h \<Longrightarrow> (\<exists>! j. j : Z \<rightarrow> A \<and> ab \<circ>\<^sub>c j = k \<and> ac \<circ>\<^sub>c j = h)"
  using assms unfolding is_pullback_def by auto

lemma pullback_iff_product:
  assumes term_T: "terminal_object(T)"
  assumes f_type: "f : Y \<rightarrow> T"
  assumes g_type: "g : X \<rightarrow> T"
  shows "is_pullback(P, Y, X, T, pY, f, pX, g) \<longleftrightarrow> is_cart_prod(P, pX, pY, X, Y)"
proof (rule iffI)
  assume pullback: "is_pullback(P, Y, X, T, pY, f, pX, g)"
  have pY_type: "pY : P \<rightarrow> Y" using pullback unfolding is_pullback_def by auto
  have pX_type: "pX : P \<rightarrow> X" using pullback unfolding is_pullback_def by auto
  have pb_uniq: "\<forall>Z k h. (k : Z \<rightarrow> Y \<and> h : Z \<rightarrow> X \<and> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h) \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j = k \<and> pX \<circ>\<^sub>c j = h)"
    using pullback unfolding is_pullback_def by auto
  show "is_cart_prod(P, pX, pY, X, Y)"
    unfolding is_cart_prod_def
  proof (intro conjI)
    show "pX : P \<rightarrow> X" by (rule pX_type)
    show "pY : P \<rightarrow> Y" by (rule pY_type)
    show "\<forall>x y Z. (x : Z \<rightarrow> X \<and> y : Z \<rightarrow> Y) \<longrightarrow>
      (\<exists>h. h : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h = x \<and> pY \<circ>\<^sub>c h = y \<and>
        (\<forall>h2. (h2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h2 = x \<and> pY \<circ>\<^sub>c h2 = y) \<longrightarrow> h2 = h))"
    proof (intro allI impI)
      fix x y Z
      assume "x : Z \<rightarrow> X \<and> y : Z \<rightarrow> Y"
      then have x_type: "x : Z \<rightarrow> X" and y_type: "y : Z \<rightarrow> Y" by auto
      have fy_type: "f \<circ>\<^sub>c y : Z \<rightarrow> T" using y_type f_type comp_type by blast
      have gx_type: "g \<circ>\<^sub>c x : Z \<rightarrow> T" using x_type g_type comp_type by blast
      have exuh: "\<exists>! h. h : Z \<rightarrow> T" using term_T unfolding terminal_object_def by auto
      then obtain hh where hh_type: "hh : Z \<rightarrow> T" and hh_unique: "\<forall>h'. h' : Z \<rightarrow> T \<longrightarrow> h' = hh" by auto
      have fy_eq: "f \<circ>\<^sub>c y = hh" using fy_type hh_unique by auto
      have gx_eq: "g \<circ>\<^sub>c x = hh" using gx_type hh_unique by auto
      have fy_eq_gx: "f \<circ>\<^sub>c y = g \<circ>\<^sub>c x" using fy_eq gx_eq by simp
      have ex1j: "\<exists>! j. j : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j = y \<and> pX \<circ>\<^sub>c j = x"
        using pb_uniq[rule_format, where k=y and h=x and Z=Z] y_type x_type fy_eq_gx by auto
      then obtain j where j_type: "j : Z \<rightarrow> P" and j_eq1: "pY \<circ>\<^sub>c j = y" and j_eq2: "pX \<circ>\<^sub>c j = x"
        and j_unique: "\<forall>j'. (j' : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j' = y \<and> pX \<circ>\<^sub>c j' = x) \<longrightarrow> j' = j" by auto
      show "\<exists>h. h : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h = x \<and> pY \<circ>\<^sub>c h = y \<and>
        (\<forall>h2. (h2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h2 = x \<and> pY \<circ>\<^sub>c h2 = y) \<longrightarrow> h2 = h)"
      proof (intro exI[where x=j] conjI)
        show "j : Z \<rightarrow> P" by (rule j_type)
        show "pX \<circ>\<^sub>c j = x" by (rule j_eq2)
        show "pY \<circ>\<^sub>c j = y" by (rule j_eq1)
        show "\<forall>h2. (h2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h2 = x \<and> pY \<circ>\<^sub>c h2 = y) \<longrightarrow> h2 = j"
        proof (intro allI impI)
          fix h2 assume "h2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h2 = x \<and> pY \<circ>\<^sub>c h2 = y"
          then have h2_type: "h2 : Z \<rightarrow> P" and h2_eq2: "pX \<circ>\<^sub>c h2 = x" and h2_eq1: "pY \<circ>\<^sub>c h2 = y" by auto
          show "h2 = j" using j_unique h2_type h2_eq1 h2_eq2 by auto
        qed
      qed
    qed
  qed
next
  assume prod: "is_cart_prod(P, pX, pY, X, Y)"
  have pX_type: "pX : P \<rightarrow> X" using prod unfolding is_cart_prod_def by auto
  have pY_type: "pY : P \<rightarrow> Y" using prod unfolding is_cart_prod_def by auto
  have prod_uniq: "\<forall>x y Z. (x : Z \<rightarrow> X \<and> y : Z \<rightarrow> Y) \<longrightarrow>
      (\<exists>h. h : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h = x \<and> pY \<circ>\<^sub>c h = y \<and>
        (\<forall>h2. (h2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c h2 = x \<and> pY \<circ>\<^sub>c h2 = y) \<longrightarrow> h2 = h))"
    using prod unfolding is_cart_prod_def by auto
  show "is_pullback(P, Y, X, T, pY, f, pX, g)"
    unfolding is_pullback_def
  proof (intro conjI)
    show "pY : P \<rightarrow> Y" by (rule pY_type)
    show "f : Y \<rightarrow> T" by (rule f_type)
    show "pX : P \<rightarrow> X" by (rule pX_type)
    show "g : X \<rightarrow> T" by (rule g_type)
    show "f \<circ>\<^sub>c pY = g \<circ>\<^sub>c pX"
    proof -
      have fpY_type: "f \<circ>\<^sub>c pY : P \<rightarrow> T" using pY_type f_type comp_type by blast
      have gpX_type: "g \<circ>\<^sub>c pX : P \<rightarrow> T" using pX_type g_type comp_type by blast
      have exuh: "\<exists>! h. h : P \<rightarrow> T" using term_T unfolding terminal_object_def by auto
      then obtain hh where hh_type: "hh : P \<rightarrow> T" and hh_unique: "\<forall>h'. h' : P \<rightarrow> T \<longrightarrow> h' = hh" by auto
      have "f \<circ>\<^sub>c pY = hh" using fpY_type hh_unique by auto
      moreover have "g \<circ>\<^sub>c pX = hh" using gpX_type hh_unique by auto
      ultimately show ?thesis by simp
    qed
    show "\<forall>Z k h. (k : Z \<rightarrow> Y \<and> h : Z \<rightarrow> X \<and> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h) \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j = k \<and> pX \<circ>\<^sub>c j = h)"
    proof (intro allI impI)
      fix Z k h
      assume "k : Z \<rightarrow> Y \<and> h : Z \<rightarrow> X \<and> f \<circ>\<^sub>c k = g \<circ>\<^sub>c h"
      then have k_type: "k : Z \<rightarrow> Y" and h_type: "h : Z \<rightarrow> X" by auto
      have ex_j: "\<exists>j. j : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c j = h \<and> pY \<circ>\<^sub>c j = k \<and>
          (\<forall>j2. (j2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c j2 = h \<and> pY \<circ>\<^sub>c j2 = k) \<longrightarrow> j2 = j)"
        using prod_uniq[rule_format, where x=h and y=k and Z=Z] h_type k_type by auto
      then obtain j where j_type: "j : Z \<rightarrow> P" and j_eq2: "pX \<circ>\<^sub>c j = h" and j_eq1: "pY \<circ>\<^sub>c j = k"
        and j_unique: "\<forall>j2. (j2 : Z \<rightarrow> P \<and> pX \<circ>\<^sub>c j2 = h \<and> pY \<circ>\<^sub>c j2 = k) \<longrightarrow> j2 = j" by auto
      show "\<exists>! j. j : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j = k \<and> pX \<circ>\<^sub>c j = h"
      proof (rule ex1I[where a=j])
        show "j : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j = k \<and> pX \<circ>\<^sub>c j = h" using j_type j_eq1 j_eq2 by auto
      next
        fix j'
        assume "j' : Z \<rightarrow> P \<and> pY \<circ>\<^sub>c j' = k \<and> pX \<circ>\<^sub>c j' = h"
        then have "j' : Z \<rightarrow> P" and "pX \<circ>\<^sub>c j' = h" and "pY \<circ>\<^sub>c j' = k" by auto
        then show "j' = j" using j_unique by auto
      qed
    qed
  qed
qed

end
