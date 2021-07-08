theory ETCS_Terminal
  imports ETCS_Cartesian
begin

section \<open>Axiom 3: Terminal Objects\<close>

axiomatization
  terminal_func :: "cset \<Rightarrow> cfunc" ("\<beta>\<^bsub>_\<^esub>" 100) and
  one :: "cset"
where
  terminal_func_type[type_rule]: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> one" and
  terminal_func_unique: "h :  X \<rightarrow> one \<Longrightarrow> h = \<beta>\<^bsub>X\<^esub>" and
  one_separator: "f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> (\<And> x. x : one \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x) \<Longrightarrow> f = g"

lemma terminal_func_comp:
  "x : X \<rightarrow> Y \<Longrightarrow> \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c x = \<beta>\<^bsub>X\<^esub>"
  by (simp add: comp_type terminal_func_type terminal_func_unique)

(* Definition 2.1.16 *)
abbreviation member :: "cfunc \<Rightarrow> cset \<Rightarrow> bool" (infix "\<in>\<^sub>c" 50) where
  "x \<in>\<^sub>c X \<equiv> (x : one \<rightarrow> X)"

definition nonempty :: "cset \<Rightarrow> bool" where
  "nonempty X \<equiv> (\<exists>x. x \<in>\<^sub>c X)"
  
definition terminal_object :: "cset \<Rightarrow> bool" where
  "terminal_object(X) \<longleftrightarrow> (\<forall> Y. \<exists>! f. f : Y \<rightarrow> X)"

lemma diag_on_elements:
  assumes "x \<in>\<^sub>c X"
  shows "diagonal(X) \<circ>\<^sub>c x = \<langle>x,x\<rangle>"
using assms cfunc_prod_comp cfunc_type_def diagonal_def id_left_unit id_type by auto

lemma one_separator_contrapos:
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> Y"
  shows "f \<noteq> g \<Longrightarrow> \<exists> x. x : one \<rightarrow> X \<and> f \<circ>\<^sub>c x \<noteq> g \<circ>\<^sub>c x"
proof -
  have "(\<forall> x. x : one \<rightarrow> X \<longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x) \<longrightarrow> f = g"
    using assms(1) assms(2) one_separator by blast
  then show "f \<noteq> g \<Longrightarrow> \<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x \<noteq> g \<circ>\<^sub>c x"
    by blast
qed
    

lemma one_terminal_object: "terminal_object(one)"
  unfolding terminal_object_def
proof auto
  fix Y
  have "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> one"
    using terminal_func_type by simp
  then show "\<exists>f. (f : Y \<rightarrow> one)"
    by auto
next
  fix Y f y
  assume "f : Y \<rightarrow> one" "y : Y \<rightarrow> one"
  then have "f = \<beta>\<^bsub>Y\<^esub> \<and> y = \<beta>\<^bsub>Y\<^esub>"
    using terminal_func_unique by auto
  then show "f = y"
    by simp
qed


(* Exercise 2.1.15 *)
lemma terminal_objects_isomorphic:
  assumes "terminal_object X" "terminal_object Y"
  shows "X \<cong> Y"
  unfolding is_isomorphic_def
proof -

  obtain f where f_type: "f : X \<rightarrow> Y" and f_unique: "\<forall>g. g : X \<rightarrow> Y \<longrightarrow> f = g"
    using assms(2) terminal_object_def by force

  obtain g where g_type: "g : Y \<rightarrow> X" and g_unique: "\<forall>f. f : Y \<rightarrow> X \<longrightarrow> g = f"
    using assms(1) terminal_object_def by force

  have g_f_is_id: "g \<circ>\<^sub>c f = id X"
    using assms(1) comp_type f_type g_type id_type terminal_object_def by blast

  have f_g_is_id: "f \<circ>\<^sub>c g = id Y"
    using assms(2) comp_type f_type g_type id_type terminal_object_def by blast

  have f_isomorphism: "isomorphism f"
    unfolding isomorphism_def
    using cfunc_type_def f_type g_type g_f_is_id f_g_is_id
    by (rule_tac x=g in exI, auto)

  show "\<exists>f. f : X \<rightarrow> Y \<and> isomorphism f"
    using f_isomorphism f_type by auto
qed

(* Exercise 2.1.18 *)
lemma element_monomorphism:
  "x \<in>\<^sub>c X \<Longrightarrow> monomorphism x"
  unfolding monomorphism_def
  by (metis cfunc_type_def domain_comp terminal_func_unique)


lemma one_unique_element:
  "\<exists>! x. x \<in>\<^sub>c one"
proof (rule_tac a="id one" in ex1I)
  show "id\<^sub>c one \<in>\<^sub>c one"
    by (simp add: id_type)
next
  fix x
  assume "x \<in>\<^sub>c one"
  then show "x = id\<^sub>c one"
    by (metis id_type terminal_func_unique)
qed

lemma one_cross_one_unique_element:
  "\<exists>! x. x \<in>\<^sub>c one \<times>\<^sub>c one"
proof (rule_tac a="diagonal one" in ex1I)
  show "diagonal one \<in>\<^sub>c one \<times>\<^sub>c one"
    by (simp add: cfunc_prod_type diagonal_def id_type)
next
  fix x
  assume x_type: "x \<in>\<^sub>c one \<times>\<^sub>c one"
  
  have left_eq: "left_cart_proj one one \<circ>\<^sub>c x = id one"
    using x_type one_unique_element by (typecheck_cfuncs, blast)
  have right_eq: "right_cart_proj one one \<circ>\<^sub>c x = id one"
    using x_type one_unique_element by (typecheck_cfuncs, blast)

  then show "x = diagonal one"
    unfolding diagonal_def using cfunc_prod_unique id_type left_eq x_type by blast
qed

(* Proposition 2.1.19 *)
lemma single_elem_iso_one:
  "(\<exists>! x. x \<in>\<^sub>c X) \<longleftrightarrow> X \<cong> one"
proof
  assume X_iso_one: "X \<cong> one"
  then have "one \<cong> X"
    by (simp add: isomorphic_is_symmetric)
  then obtain f where f_type: "f : one \<rightarrow> X" and f_iso: "isomorphism f"
    using is_isomorphic_def by blast

  show "\<exists>!x. x \<in>\<^sub>c X"
  proof (rule_tac a=f in ex1I, auto simp add: f_type)
    fix x
    assume x_type: "x \<in>\<^sub>c X"
    then have \<beta>x_eq_\<beta>f: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f"
      using f_type terminal_func_comp by auto
    have "isomorphism (\<beta>\<^bsub>X\<^esub>)"
      using X_iso_one is_isomorphic_def terminal_func_unique by blast
    then have "monomorphism (\<beta>\<^bsub>X\<^esub>)"
      by (simp add: iso_imp_epi_and_monic)
    then show "x = f"
      unfolding monomorphism_def using \<beta>x_eq_\<beta>f x_type cfunc_type_def f_type terminal_func_type by auto 
  qed
next
  assume "\<exists>!x. x \<in>\<^sub>c X"
  then obtain x where x_type: "x : one \<rightarrow> X" and x_unique: "\<forall> y. y : one \<rightarrow> X \<longrightarrow> x = y"
    by blast

  have "terminal_object X"
    unfolding terminal_object_def
  proof 
    fix Y
    show "\<exists>!f. f : Y \<rightarrow> X"
    proof (rule_tac a="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" in ex1I)
      show "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X"
        using comp_type terminal_func_type x_type by blast
    next
      fix xa
      assume xa_type: "xa : Y \<rightarrow> X"
      show "xa = x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
      proof (rule ccontr)
        assume "xa \<noteq> x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
        then obtain y where elems_neq: "xa \<circ>\<^sub>c y \<noteq> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y" and y_type: "y : one \<rightarrow> Y"
          using one_separator_contrapos[where f=xa, where g="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>", where X=Y, where Y=X]
          using comp_type terminal_func_type x_type xa_type by blast
        have elem1: "xa \<circ>\<^sub>c y \<in>\<^sub>c X"
          using comp_type xa_type y_type by auto
        have elem2: "(x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y \<in>\<^sub>c X"
          using comp_type terminal_func_type x_type y_type by blast
        show False
          using elem1 elem2 elems_neq x_unique by blast
      qed
    qed
  qed
  then show "X \<cong> one"
    by (simp add: one_terminal_object terminal_objects_isomorphic)
qed





(* Converse to Exercise 2.1.15: Part 1 *)
lemma iso_to1_is_term:
  assumes "X \<cong> one"
  shows "terminal_object X"
  unfolding terminal_object_def
proof 
   fix Y
   obtain x where x_type: "x : one \<rightarrow> X" and x_unique: "\<forall> y. y : one \<rightarrow> X \<longrightarrow> x = y"
      using assms single_elem_iso_one by fastforce 
   show  "\<exists>!f. f : Y \<rightarrow> X"
      proof (rule_tac a="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" in ex1I)
         show "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X"
           using comp_type terminal_func_type x_type by blast
      next
         fix xa
         assume xa_type: "xa : Y \<rightarrow> X"
         show "xa = x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
         proof (rule ccontr)
           assume "xa \<noteq> x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
           then obtain y where elems_neq: "xa \<circ>\<^sub>c y \<noteq> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y" and y_type: "y : one \<rightarrow> Y"
             using one_separator_contrapos[where f=xa, where g="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>", where X=Y, where Y=X]
             using comp_type terminal_func_type x_type xa_type by blast
           have elem1: "xa \<circ>\<^sub>c y \<in>\<^sub>c X"
             using comp_type xa_type y_type by auto
           have elem2: "(x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y \<in>\<^sub>c X"
             using comp_type terminal_func_type x_type y_type by blast
           show False
             using elem1 elem2 elems_neq x_unique by blast
         qed
      qed
qed 

(* Converse to Exercise 2.1.15: Part 2 *)

lemma iso_to_term_is_term:
  assumes "X \<cong> Y"
  assumes "terminal_object Y"
  shows "terminal_object X"
  by (meson assms iso_to1_is_term isomorphic_is_transitive one_terminal_object terminal_objects_isomorphic)

(* Proposition 2.1.20 *)
lemma X_is_cart_prod1:
  "is_cart_prod X (id X) (\<beta>\<^bsub>X\<^esub>) X one"
  unfolding is_cart_prod_def
proof auto
  show "id\<^sub>c X : X \<rightarrow> X"
    by (simp add: id_type)
next
  show "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> one"
    by (simp add: terminal_func_type)
next
  fix f g Y
  assume f_type: "f : Y \<rightarrow> X" and g_type: "g : Y \<rightarrow> one"
  then show "\<exists>h. h : Y \<rightarrow> X \<and>
           id\<^sub>c X \<circ>\<^sub>c h = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = g \<and> (\<forall>h2. h2 : Y \<rightarrow> X \<and> id\<^sub>c X \<circ>\<^sub>c h2 = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = g \<longrightarrow> h2 = h)"
  proof (rule_tac x=f in exI, auto)
    show "id X \<circ>\<^sub>c f = f"
      using cfunc_type_def f_type id_left_unit by auto
    show "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f = g"
      by (metis comp_type f_type g_type terminal_func_type terminal_func_unique)
    show "\<And>h2. h2 : Y \<rightarrow> X \<Longrightarrow> h2 = id\<^sub>c X \<circ>\<^sub>c h2"
      using cfunc_type_def id_left_unit by auto
  qed
qed

lemma X_is_cart_prod2:
  "is_cart_prod X (\<beta>\<^bsub>X\<^esub>) (id X) one X"
  unfolding is_cart_prod_def
proof auto
  show "id\<^sub>c X : X \<rightarrow> X"
    by (simp add: id_type)
next
  show "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> one"
    by (simp add: terminal_func_type)
next
  fix f g Z
  assume f_type: "f : Z \<rightarrow> one" and g_type: "g : Z \<rightarrow> X"
  then show "\<exists>h. h : Z \<rightarrow> X \<and>
           \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = f \<and> id\<^sub>c X \<circ>\<^sub>c h = g \<and> (\<forall>h2. h2 : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = f \<and> id\<^sub>c X \<circ>\<^sub>c h2 = g \<longrightarrow> h2 = h)"
  proof (rule_tac x=g in exI, auto)
    show "id\<^sub>c X \<circ>\<^sub>c g = g"
      using cfunc_type_def g_type id_left_unit by auto
    show "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g = f"
      by (metis comp_type f_type g_type terminal_func_type terminal_func_unique)
    show "\<And>h2. h2 : Z \<rightarrow> X \<Longrightarrow> h2 = id\<^sub>c X \<circ>\<^sub>c h2"
      using cfunc_type_def id_left_unit by auto
  qed
qed

lemma A_x_one_iso_A:
  "X \<times>\<^sub>c one \<cong> X"
  by (metis X_is_cart_prod1 canonical_cart_prod_is_cart_prod cart_prods_isomorphic fst_conv is_isomorphic_def snd_conv)

lemma one_x_A_iso_A:
  "one \<times>\<^sub>c X \<cong> X"
  by (meson A_x_one_iso_A isomorphic_is_transitive product_commutes)

(* Proposition 2.1.21 *)
lemma cart_prod_elem_eq:
  assumes "a \<in>\<^sub>c X \<times>\<^sub>c Y" "b \<in>\<^sub>c X \<times>\<^sub>c Y"
  shows "a = b \<longleftrightarrow> 
    (left_cart_proj X Y \<circ>\<^sub>c a = left_cart_proj X Y \<circ>\<^sub>c b 
      \<and> right_cart_proj X Y \<circ>\<^sub>c a = right_cart_proj X Y \<circ>\<^sub>c b)"
  by (metis (full_types) assms cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type)

(* Note 2.1.22 *)
lemma  element_pair_eq:
  assumes "x \<in>\<^sub>c X" "x' \<in>\<^sub>c X" "y \<in>\<^sub>c Y" "y' \<in>\<^sub>c Y"
  shows "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle> \<longleftrightarrow> x = x' \<and> y = y'"
  by (metis assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)

(* Proposition 2.1.23 *)
lemma nonempty_right_imp_left_proj_epimorphism:
  "nonempty Y \<Longrightarrow> epimorphism (left_cart_proj X Y)"
proof -
  assume "nonempty Y"
  then obtain y where y_in_Y: "y : one \<rightarrow> Y"
    using nonempty_def by blast
  then have id_eq: "(left_cart_proj X Y) \<circ>\<^sub>c \<langle>id X, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> = id X"
    using comp_type id_type left_cart_proj_cfunc_prod terminal_func_type by blast
  then show "epimorphism (left_cart_proj X Y)"
    unfolding epimorphism_def
  proof auto
    fix g h
    assume domain_g: "domain g = codomain (left_cart_proj X Y)"
    assume domain_h: "domain h = codomain (left_cart_proj X Y)"

    assume "g \<circ>\<^sub>c left_cart_proj X Y = h \<circ>\<^sub>c left_cart_proj X Y"
    then have "g \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c \<langle>id X, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> = h \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c \<langle>id X, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
      using y_in_Y by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative domain_g domain_h)
    then show "g = h"
      by (metis cfunc_type_def domain_g domain_h id_eq id_right_unit left_cart_proj_type)
  qed
qed

(*Dual to Proposition 2.1.23 *)
lemma nonempty_left_imp_right_proj_epimorphism:
  "nonempty X \<Longrightarrow> epimorphism (right_cart_proj X Y)"
proof - 
  assume "nonempty X"
  then obtain y where y_in_Y: "y: one \<rightarrow> X"
    using nonempty_def by blast
  then have id_eq: "(right_cart_proj X Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> = id Y"
     using comp_type id_type right_cart_proj_cfunc_prod terminal_func_type by blast
  then show "epimorphism (right_cart_proj X Y)"
    unfolding epimorphism_def
  proof auto
    fix g h
    assume domain_g: "domain g = codomain (right_cart_proj X Y)"
    assume domain_h: "domain h = codomain (right_cart_proj X Y)"

    assume "g \<circ>\<^sub>c right_cart_proj X Y = h \<circ>\<^sub>c right_cart_proj X Y"
    then have "g \<circ>\<^sub>c right_cart_proj X Y \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> = h \<circ>\<^sub>c right_cart_proj X Y \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle>"
      using y_in_Y by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative domain_g domain_h)
    then show "g = h"
      by (metis cfunc_type_def domain_g domain_h id_eq id_right_unit right_cart_proj_type)
  qed
qed


lemma prod_with_empty_is_empty1:
  assumes "\<not>(nonempty A)"
  shows "\<not>(nonempty (A \<times>\<^sub>c B))"
  by (meson assms comp_type left_cart_proj_type nonempty_def)

lemma prod_with_empty_is_empty2:
  assumes "\<not>(nonempty B)"
  shows "\<not>(nonempty (A \<times>\<^sub>c B))"
  using assms cart_prod_decomp nonempty_def by blast





(* Definition 2.1.24 *)
definition injective :: "cfunc \<Rightarrow> bool" where
 "injective f  \<longleftrightarrow> (\<forall> x y. (x \<in>\<^sub>c domain f \<and> y \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y) \<longrightarrow> x = y)"

  


(* Exercise 2.1.26 *)
lemma monomorphism_imp_injective:
  "monomorphism f \<Longrightarrow> injective f"
  by (simp add: cfunc_type_def injective_def monomorphism_def)

(* Proposition 2.1.27 *)
lemma injective_imp_monomorphism:
  assumes "f \<in> ETCS_func"
  shows "injective f \<Longrightarrow> monomorphism f"
  unfolding monomorphism_def injective_def
proof safe
  fix g h
  assume f_inj: "\<forall>x y. x \<in>\<^sub>c domain f \<and> y \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y \<longrightarrow> x = y"
  assume cd_g_eq_d_f: "codomain g = domain f"
  assume cd_h_eq_d_f: "codomain h = domain f"
  assume fg_eq_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"

  obtain X Y where f_type: "f : X \<rightarrow> Y"
    using assms cfunc_type_def by blast
  obtain A where g_type: "g : A \<rightarrow> X" and h_type: "h : A \<rightarrow> X"
    by (metis cd_g_eq_d_f cd_h_eq_d_f cfunc_type_def domain_comp f_type fg_eq_fh)

  have "(\<forall>x. x \<in>\<^sub>c A \<longrightarrow> g \<circ>\<^sub>c x = h \<circ>\<^sub>c x)"
  proof auto
    fix x
    assume x_in_A: "x \<in>\<^sub>c A"

    have "f \<circ>\<^sub>c (g \<circ>\<^sub>c x) = f \<circ>\<^sub>c (h \<circ>\<^sub>c x)"
      using g_type h_type x_in_A f_type comp_associative2 fg_eq_fh by (typecheck_cfuncs, auto)
    then show "g \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
      using cd_h_eq_d_f cfunc_type_def comp_type f_inj g_type h_type x_in_A by presburger
  qed
  then show "g = h"
    using g_type h_type one_separator by auto
qed

(* Definition 2.1.28 *)
definition surjective :: "cfunc \<Rightarrow> bool" where
 "surjective f  \<longleftrightarrow> (\<forall>y. y \<in>\<^sub>c codomain f \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = y))"


(* Exercise 2.1.30 *)
lemma surjective_is_epimorphism:
  "surjective f \<Longrightarrow> epimorphism f"
  unfolding surjective_def epimorphism_def
proof (cases "nonempty (codomain f)", auto)
  fix g h
  assume f_surj: "\<forall>y. y \<in>\<^sub>c codomain f \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = y)"
  assume d_g_eq_cd_f: "domain g = codomain f"
  assume d_h_eq_cd_f: "domain h = codomain f"
  assume gf_eq_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
  assume nonempty: "nonempty (codomain f)"

  obtain X Y where f_type: "f : X \<rightarrow> Y"
    using nonempty cfunc_type_def f_surj nonempty_def by auto
  obtain A where g_type: "g : Y \<rightarrow> A" and h_type: "h : Y \<rightarrow> A"
    by (metis cfunc_type_def codomain_comp d_g_eq_cd_f d_h_eq_cd_f f_type gf_eq_hf)

  show "g = h"
  proof (rule ccontr)
    assume "g \<noteq> h"
    then obtain y where y_in_X: "y \<in>\<^sub>c Y" and gy_neq_hy: "g \<circ>\<^sub>c y \<noteq> h \<circ>\<^sub>c y"
      using g_type h_type one_separator by blast
    then obtain x where "x \<in>\<^sub>c X" and "f \<circ>\<^sub>c x = y"
      using cfunc_type_def f_surj f_type by auto
    then have "g \<circ>\<^sub>c f \<noteq> h \<circ>\<^sub>c f"
      using comp_associative2 f_type g_type gy_neq_hy h_type by auto
    then show False
      using gf_eq_hf by auto
  qed
next
  fix g h
  assume empty: "\<not> nonempty (codomain f)"
  assume "domain g = codomain f" "domain h = codomain f"
  then show "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<Longrightarrow> g = h"
    by (metis empty cfunc_type_def codomain_comp nonempty_def one_separator)
qed

lemma cart_prod_extract_left:
  assumes "f : one \<rightarrow> X" "g : one \<rightarrow> Y"
  shows "\<langle>f, g\<rangle> = \<langle>id X, g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c f"
proof -
  have "\<langle>f, g\<rangle> = \<langle>id X \<circ>\<^sub>c f, g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f\<rangle>"
    using assms by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
  also have "... = \<langle>id X, g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c f"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  then show ?thesis
    using calculation by auto
qed

lemma cart_prod_extract_right:
  assumes "f : one \<rightarrow> X" "g : one \<rightarrow> Y"
  shows "\<langle>f, g\<rangle> = \<langle>f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> \<circ>\<^sub>c g"
proof -
  have "\<langle>f, g\<rangle> = \<langle>f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> \<circ>\<^sub>c g, id Y \<circ>\<^sub>c g\<rangle>"
    using assms by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
  also have "... = \<langle>f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> \<circ>\<^sub>c g"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  then show ?thesis
    using calculation by auto
qed

subsection \<open>More Results on Cartesian Products\<close>

lemma cfunc_cross_prod_surj:
  assumes type_assms: "f : A \<rightarrow> C" "g : B \<rightarrow> D"
  assumes f_surj: "surjective f" and g_surj: "surjective g"
  shows "surjective (f \<times>\<^sub>f g)"
  unfolding surjective_def
proof(auto)
  fix y
  assume y_type: "y \<in>\<^sub>c codomain (f \<times>\<^sub>f g)"
  have fg_type: "f \<times>\<^sub>f g: (A \<times>\<^sub>c  B) \<rightarrow> (C \<times>\<^sub>c D)"
    using assms by typecheck_cfuncs
  then have "y \<in>\<^sub>c (C \<times>\<^sub>c D)"
    using cfunc_type_def y_type by auto
  then have "\<exists> c d. c \<in>\<^sub>c C \<and> d \<in>\<^sub>c D \<and> y = \<langle>c,d\<rangle>"
    using cart_prod_decomp by blast
  then obtain c d where y_def: "c \<in>\<^sub>c C \<and> d \<in>\<^sub>c D \<and> y = \<langle>c,d\<rangle>"
    by blast
  then have "\<exists> a b. a \<in>\<^sub>c A \<and> b \<in>\<^sub>c B \<and> f \<circ>\<^sub>c a = c \<and> g \<circ>\<^sub>c b = d"
    by (metis cfunc_type_def f_surj g_surj surjective_def type_assms)
  then obtain a b where ab_def: "a \<in>\<^sub>c A \<and> b \<in>\<^sub>c B \<and> f \<circ>\<^sub>c a = c \<and> g \<circ>\<^sub>c b = d"
    by blast
  then obtain x where x_def: "x = \<langle>a,b\<rangle>"
    by auto
  have x_type: "x \<in>\<^sub>c domain (f \<times>\<^sub>f g)"
    using ab_def cfunc_prod_type cfunc_type_def fg_type x_def by auto
  have "(f \<times>\<^sub>f g) \<circ>\<^sub>c x = y"
    using ab_def cfunc_cross_prod_comp_cfunc_prod type_assms(1) type_assms(2) x_def y_def by blast
  then show "\<exists>x. x \<in>\<^sub>c domain (f \<times>\<^sub>f g) \<and> (f \<times>\<^sub>f g) \<circ>\<^sub>c x = y"
    using x_type by blast
qed



lemma cfunc_cross_prod_surj_converse:
  assumes type_assms: "f : A \<rightarrow> C" "g : B \<rightarrow> D"
  assumes "surjective (f \<times>\<^sub>f g)"
  shows "(surjective (f)) \<and> (surjective (g))"
  unfolding surjective_def
proof(auto)
  fix y 
  assume y_type: "y \<in>\<^sub>c codomain f"
  then have y_type2:  "y \<in>\<^sub>c C"
    using cfunc_type_def type_assms(1) by auto
  oops


lemma cfunc_cross_prod_mono_converse:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes fg_inject: "injective (f \<times>\<^sub>f g)"
  assumes nonempty: "nonempty(X)" "nonempty(Z)"
  shows "injective f \<and> injective g"
  unfolding injective_def
proof (auto)
  fix x y 
  assume x_type: "x \<in>\<^sub>c domain f"
  assume y_type: "y \<in>\<^sub>c domain f"
  assume equals: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
  have fg_type: "(f \<times>\<^sub>f g) : (X \<times>\<^sub>c Z) \<rightarrow> (Y \<times>\<^sub>c W)"
    by (simp add: cfunc_cross_prod_type type_assms)
  have x_type2: "x \<in>\<^sub>c X"
    using cfunc_type_def type_assms(1) x_type by auto
  have y_type2: "y \<in>\<^sub>c X"
    using cfunc_type_def type_assms(1) y_type by auto
  show "x = y"
        proof - 
          obtain b where b_def: "b \<in>\<^sub>c Z"
            using nonempty(2) nonempty_def by blast

          have xb_type: "\<langle>x,b\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z"
            by (simp add: b_def cfunc_prod_type x_type2)
          have yb_type: "\<langle>y,b\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z"
            by (simp add: b_def cfunc_prod_type y_type2)
          have "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x,b\<rangle> = \<langle>f \<circ>\<^sub>c x,g \<circ>\<^sub>c b\<rangle>"
            using b_def cfunc_cross_prod_comp_cfunc_prod type_assms(1) type_assms(2) x_type2 by blast
          also have "... = \<langle>f \<circ>\<^sub>c y,g \<circ>\<^sub>c b\<rangle>"
            by (simp add: equals)
          also have "... = (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>y,b\<rangle>"
            using b_def cfunc_cross_prod_comp_cfunc_prod type_assms(1) type_assms(2) y_type2 by auto
          then have "\<langle>x,b\<rangle> = \<langle>y,b\<rangle>"
            by (metis calculation cfunc_type_def fg_inject fg_type injective_def xb_type yb_type)
          then show "x = y"
            using b_def element_pair_eq x_type2 y_type2 by auto
        qed
      next
fix x y 
  assume x_type: "x \<in>\<^sub>c domain g"
  assume y_type: "y \<in>\<^sub>c domain g"
  assume equals: "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
  have fg_type: "(f \<times>\<^sub>f g) : (X \<times>\<^sub>c Z) \<rightarrow> (Y \<times>\<^sub>c W)"
    by (simp add: cfunc_cross_prod_type type_assms)
  have x_type2: "x \<in>\<^sub>c Z"
    using cfunc_type_def type_assms(2) x_type by auto
   have y_type2: "y \<in>\<^sub>c Z"
    using cfunc_type_def type_assms(2) y_type by auto
show "x = y"
        proof - 
          obtain b where b_def: "b \<in>\<^sub>c X"
            using nonempty(1) nonempty_def by blast
          have xb_type: "\<langle>b,x\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z"
            by (simp add: b_def cfunc_prod_type x_type2)
          have yb_type: "\<langle>b,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Z"
            by (simp add: b_def cfunc_prod_type y_type2)
          have "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>b,x\<rangle> = \<langle>f \<circ>\<^sub>c b,g \<circ>\<^sub>c x\<rangle>"
            using b_def cfunc_cross_prod_comp_cfunc_prod type_assms(1) type_assms(2) x_type2 by blast
          also have "... = \<langle>f \<circ>\<^sub>c b,g \<circ>\<^sub>c x\<rangle>"
            by (simp add: equals)
          also have "... = (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>b,y\<rangle>"
            using b_def cfunc_cross_prod_comp_cfunc_prod equals type_assms(1) type_assms(2) y_type2 by auto
          then have "\<langle>b,x\<rangle> = \<langle>b,y\<rangle>"
            by (metis \<open>(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>b,x\<rangle> = \<langle>f \<circ>\<^sub>c b,g \<circ>\<^sub>c x\<rangle>\<close> cfunc_type_def fg_inject fg_type injective_def xb_type yb_type)
          then show "x = y"
            using b_def element_pair_eq x_type2 y_type2 by auto
        qed
      qed


(*The next lemma shows us that unless 
  both domains are nonempty we gain no new information.
 That is, it will be the case that f\<times>g is injective, and we
cannot infer from this that f or g are injective since 
 f\<times>g will be injective no matter what.*)

lemma the_nonempty_assumption_above_is_always_required:
  assumes "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes "\<not>(nonempty(X)) \<or> \<not>(nonempty(Z))"
  shows "injective (f \<times>\<^sub>f g)"
  unfolding injective_def 
proof(cases "nonempty(X)", auto)
  fix x y
  assume nonempty:  "nonempty X"
  assume x_type: "x  \<in>\<^sub>c domain (f \<times>\<^sub>f g)"
  assume "y \<in>\<^sub>c domain (f \<times>\<^sub>f g)"
  then have "\<not>(nonempty(Z))"
    using nonempty assms(3) by blast
  have fg_type: "(f \<times>\<^sub>f g) : (X \<times>\<^sub>c Z) \<rightarrow> (Y \<times>\<^sub>c W)"
    by (typecheck_cfuncs, simp add: assms(1) assms(2))
  then have "x  \<in>\<^sub>c (X \<times>\<^sub>c Z)"
    using x_type cfunc_type_def by auto
  then have "\<exists>z. z\<in>\<^sub>c Z"
    using cart_prod_decomp by blast
  then have False
    using assms(3) nonempty nonempty_def by blast
  then show "x=y"
    by auto
next
  fix x y
  assume X_is_empty: "\<not> nonempty X"
  assume x_type: "x  \<in>\<^sub>c domain (f \<times>\<^sub>f g)"
  assume "y \<in>\<^sub>c domain (f \<times>\<^sub>f g)"
  have fg_type: "(f \<times>\<^sub>f g) : (X \<times>\<^sub>c Z) \<rightarrow> (Y \<times>\<^sub>c W)"
    by (typecheck_cfuncs, simp add: assms(1) assms(2))
  then have "x  \<in>\<^sub>c (X \<times>\<^sub>c Z)"
    using x_type cfunc_type_def by auto
  then have "\<exists>z. z\<in>\<^sub>c X"
    using cart_prod_decomp by blast
  then have False
    using assms(3) X_is_empty nonempty_def by blast
  then show "x=y"
    by auto
qed




  
  

end