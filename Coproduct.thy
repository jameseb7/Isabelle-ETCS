theory Coproduct
  imports Equivalence
begin


section  \<open>Axiom 7: Coproducts\<close>

hide_const case_bool

axiomatization
  coprod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<Coprod>" 65) and
  left_coproj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_coproj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_coprod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<amalg>" 65)
where
  left_proj_type[type_rule]: "left_coproj X Y : X \<rightarrow> X\<Coprod>Y" and
  right_proj_type[type_rule]: "right_coproj X Y : Y \<rightarrow> X\<Coprod>Y" and
  cfunc_coprod_type[type_rule]: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> f\<amalg>g :  X\<Coprod>Y \<rightarrow> Z" and
  left_coproj_cfunc_coprod: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> f\<amalg>g \<circ>\<^sub>c (left_coproj X Y)  = f" and
  right_coproj_cfunc_coprod: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> f\<amalg>g \<circ>\<^sub>c (right_coproj X Y)  = g" and
  cfunc_coprod_unique: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> h : X \<Coprod> Y \<rightarrow> Z \<Longrightarrow> 
    h \<circ>\<^sub>c left_coproj X Y = f \<Longrightarrow> h \<circ>\<^sub>c right_coproj X Y = g \<Longrightarrow> h = f\<amalg>g"

subsection  \<open>Coproduct Function Properities\<close>

lemma cfunc_coprod_comp:
  assumes "a : Y \<rightarrow> Z" "b : X \<rightarrow> Y" "c : W \<rightarrow> Y"
  shows "(a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c) = a \<circ>\<^sub>c (b \<amalg> c)"
proof -
  have "((a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c)) \<circ>\<^sub>c (left_coproj X W) = a \<circ>\<^sub>c (b \<amalg> c) \<circ>\<^sub>c (left_coproj X W)"
    using assms by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
  then have left_coproj_eq: "((a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c)) \<circ>\<^sub>c (left_coproj X W) = (a \<circ>\<^sub>c (b \<amalg> c)) \<circ>\<^sub>c (left_coproj X W)"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  have "((a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c)) \<circ>\<^sub>c (right_coproj X W) = a \<circ>\<^sub>c (b \<amalg> c) \<circ>\<^sub>c (right_coproj X W)"
    using assms by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
  then have right_coproj_eq: "((a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c)) \<circ>\<^sub>c (right_coproj X W) = (a \<circ>\<^sub>c (b \<amalg> c)) \<circ>\<^sub>c (right_coproj X W)"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)

  show "(a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c) = a \<circ>\<^sub>c (b \<amalg> c)"
    using assms left_coproj_eq right_coproj_eq
    by (typecheck_cfuncs, smt cfunc_coprod_unique left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
qed

lemma id_coprod:
  "id(A \<Coprod> B) = (left_coproj A B) \<amalg> (right_coproj A B)"
    by (typecheck_cfuncs, simp add: cfunc_coprod_unique id_left_unit2)

(* Proposition 2.4.1 *)
lemma coproducts_disjoint:
  " x\<in>\<^sub>c X \<Longrightarrow>  y \<in>\<^sub>c Y \<Longrightarrow>  (left_coproj X Y) \<circ>\<^sub>c x \<noteq> (right_coproj X Y) \<circ>\<^sub>c y"
proof (rule ccontr, auto)
  assume x_type[type_rule]: "x\<in>\<^sub>c X" 
  assume y_type[type_rule]: "y \<in>\<^sub>c Y"
  assume BWOC: "((left_coproj X Y) \<circ>\<^sub>c x = (right_coproj X Y) \<circ>\<^sub>c y)"
  obtain g where g_def: "g factorsthru  \<t>" and g_type[type_rule]: "g: X \<rightarrow> \<Omega>"
    by (typecheck_cfuncs, meson comp_type factors_through_def2 terminal_func_type)
  then have fact1: "\<t> = g \<circ>\<^sub>c x"
    by (metis cfunc_type_def comp_associative factors_through_def id_right_unit2 id_type
        terminal_func_comp terminal_func_unique true_func_type x_type)
     
  obtain h where h_def: "h factorsthru \<f>" and h_type[type_rule]: "h: Y \<rightarrow> \<Omega>"
    by (typecheck_cfuncs, meson comp_type factors_through_def2 one_terminal_object terminal_object_def)
  then have gUh_type[type_rule]: "g \<amalg> h: X \<Coprod> Y \<rightarrow> \<Omega>" and 
                        gUh_def: "(g \<amalg> h) \<circ>\<^sub>c (left_coproj X Y) = g \<and>  (g \<amalg> h) \<circ>\<^sub>c (right_coproj X Y) = h"
    using left_coproj_cfunc_coprod right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
  then have fact2: "\<f> = ((g \<amalg> h) \<circ>\<^sub>c (right_coproj X Y)) \<circ>\<^sub>c y"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) comp_associative2 factors_through_def2 gUh_def h_def id_right_unit2 terminal_func_comp_elem terminal_func_unique)
  also have "... = ((g \<amalg> h) \<circ>\<^sub>c (left_coproj X Y)) \<circ>\<^sub>c x"
    by (smt BWOC comp_associative2 gUh_type left_proj_type right_proj_type x_type y_type) 
  also have "... = \<t>"
    by (simp add: fact1 gUh_def)
  then show False
    using calculation true_false_distinct by auto
qed

(*Proposition 2.4.2*)
lemma left_coproj_are_monomorphisms:
  "monomorphism(left_coproj X Y)"
proof (cases "\<exists>x. x \<in>\<^sub>c X")
  assume X_nonempty: "\<exists>x. x \<in>\<^sub>c X"
  then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X"
    by auto
  then have "(id X \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj X Y = id X"
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
  then show "monomorphism (left_coproj X Y)"
    by (typecheck_cfuncs, metis (mono_tags) cfunc_coprod_type comp_monic_imp_monic'
        comp_type id_isomorphism id_type iso_imp_epi_and_monic terminal_func_type x_type)
next
  show "\<nexists>x. x \<in>\<^sub>c X \<Longrightarrow> monomorphism (left_coproj X Y)"
    by (typecheck_cfuncs, metis cfunc_type_def injective_def injective_imp_monomorphism singletonI)
qed

lemma right_coproj_are_monomorphisms:
  "monomorphism(right_coproj X Y)"
proof (cases "\<exists>y. y \<in>\<^sub>c Y")
  assume Y_nonempty: "\<exists>y. y \<in>\<^sub>c Y"
  then obtain y where y_type[type_rule]:  "y \<in>\<^sub>c Y"
    by auto
  have "((y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> id Y) \<circ>\<^sub>c right_coproj X Y = id Y"
    by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
  then show "monomorphism (right_coproj X Y)"
    by (typecheck_cfuncs, metis (mono_tags) cfunc_coprod_type comp_monic_imp_monic'
        comp_type id_isomorphism id_type iso_imp_epi_and_monic terminal_func_type y_type)
next
  show "\<nexists>y. y \<in>\<^sub>c Y \<Longrightarrow> monomorphism (right_coproj X Y)"
    by (typecheck_cfuncs, metis cfunc_type_def injective_def injective_imp_monomorphism singletonI)
qed

(*Proposition 2.4.3*)
lemma coprojs_jointly_surj:
  assumes "z \<in>\<^sub>c X \<Coprod> Y"
  shows "(\<exists> x. (x \<in>\<^sub>c X \<and> z = (left_coproj X Y) \<circ>\<^sub>c x))
      \<or>  (\<exists> y. (y \<in>\<^sub>c Y \<and> z = (right_coproj X Y) \<circ>\<^sub>c y))"
proof (rule ccontr, auto)
  assume not_in_left_image: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> z \<noteq> left_coproj X Y \<circ>\<^sub>c x"
  assume not_in_right_image: "\<forall>y. y \<in>\<^sub>c Y \<longrightarrow> z \<noteq> right_coproj X Y \<circ>\<^sub>c y"
  
  obtain h where h_def: "h = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>" and h_type[type_rule]: "h : X \<Coprod> Y \<rightarrow> \<Omega>"
    by typecheck_cfuncs

  have fact1: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj X Y = h \<circ>\<^sub>c left_coproj X Y"
  proof(rule one_separator[where X=X, where Y = \<Omega>])
    show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj X Y : X \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "h \<circ>\<^sub>c left_coproj X Y : X \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> ((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x =
                          (h \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x"
    proof - 
      fix x
      assume x_type: "x \<in>\<^sub>c X"
      have "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x = 
              eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c  x)"
             using x_type by (typecheck_cfuncs, metis assms cfunc_type_def comp_associative)
      also have "... = \<f>"
             using x_type by (typecheck_cfuncs, simp add: assms  eq_pred_false_extract_right not_in_left_image)
      also have "... = h \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x)"
             using x_type by (typecheck_cfuncs, smt comp_associative2 h_def id_right_unit2 id_type terminal_func_comp terminal_func_type terminal_func_unique)
      also have "... = (h \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x"
             using x_type cfunc_type_def comp_associative comp_type false_func_type h_def terminal_func_type by (typecheck_cfuncs, force)
      then show "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x  = (h \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x"
             by (simp add: calculation)
    qed
  qed

  have fact2: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj X Y = h \<circ>\<^sub>c right_coproj X Y"
  proof(rule one_separator[where X = Y, where Y = \<Omega>])
    show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj X Y : Y \<rightarrow> \<Omega>"
       by (meson assms cfunc_prod_type comp_type eq_pred_type id_type right_proj_type terminal_func_type)
    show "h \<circ>\<^sub>c right_coproj X Y : Y \<rightarrow> \<Omega>"
       using cfunc_type_def codomain_comp domain_comp false_func_type h_def right_proj_type terminal_func_type by presburger
    show "\<And>x. x \<in>\<^sub>c Y \<Longrightarrow>
           ((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x =
           (h \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x"
    proof - 
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c Y"
      have "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x = \<f>"
        by (typecheck_cfuncs, smt (verit) assms cfunc_type_def eq_pred_false_extract_right comp_associative comp_type not_in_right_image)
      also have "... = (h \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x"
        by (etcs_assocr,typecheck_cfuncs, metis cfunc_type_def comp_associative h_def id_right_unit2 terminal_func_comp_elem terminal_func_type)
      then show "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c  x = (h \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x"
         by (simp add: calculation)
    qed
  qed
  have indicator_is_false:"eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle> = h"
  proof(rule one_separator[where X = "X \<Coprod> Y", where Y = \<Omega>])
    show "h : X \<Coprod> Y \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    then show "\<And>x. x \<in>\<^sub>c X \<Coprod> Y \<Longrightarrow> (eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
      by (typecheck_cfuncs, smt (z3) cfunc_coprod_comp fact1 fact2 id_coprod id_right_unit2 left_proj_type right_proj_type)
  qed

  have hz_gives_false: "h \<circ>\<^sub>c z = \<f>"
    using assms by (typecheck_cfuncs, smt comp_associative2 h_def id_right_unit2 id_type terminal_func_comp terminal_func_type terminal_func_unique)
  then have indicator_z_gives_false: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c z = \<f>"
    using assms indicator_is_false  by (typecheck_cfuncs, blast)
  then have indicator_z_gives_true: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c z = \<t>"
    using assms by (typecheck_cfuncs, smt (verit, del_insts) comp_associative2 eq_pred_true_extract_right)
  then show False
    using indicator_z_gives_false true_false_distinct by auto
qed

lemma maps_into_1u1:
  assumes x_type:  "x\<in>\<^sub>c (one \<Coprod> one)"
  shows "(x = left_coproj one one) \<or> (x = right_coproj one one)"
  using assms by (typecheck_cfuncs, metis coprojs_jointly_surj terminal_func_unique)

lemma coprod_preserves_left_epi:
  assumes "f: X \<rightarrow> Z" "g: Y \<rightarrow> Z"
  assumes "surjective(f)"
  shows "surjective(f \<amalg> g)"
  unfolding surjective_def
proof(auto)
  fix z
  assume y_type[type_rule]: "z \<in>\<^sub>c codomain (f \<amalg> g)"
  then obtain x where x_def: "x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x  = z"
    using assms cfunc_coprod_type cfunc_type_def cfunc_type_def surjective_def by auto
  have "(f \<amalg> g) \<circ>\<^sub>c  ((left_coproj X Y)  \<circ>\<^sub>c x ) = z"
    by (typecheck_cfuncs, smt assms comp_associative2 left_coproj_cfunc_coprod x_def)
  then show "\<exists>x. x \<in>\<^sub>c domain (f \<amalg> g) \<and> f \<amalg> g \<circ>\<^sub>c x = z"
    by (typecheck_cfuncs, metis  assms(1,2) cfunc_type_def codomain_comp domain_comp left_proj_type x_def)
qed

lemma coprod_preserves_right_epi:
  assumes "f: X \<rightarrow> Z" "g: Y \<rightarrow> Z"
  assumes "surjective(g)"
  shows "surjective(f \<amalg> g)"
  unfolding surjective_def
proof(auto)
  fix z
  assume y_type: "z \<in>\<^sub>c codomain (f \<amalg> g)"
  have fug_type: "(f \<amalg> g) : (X \<Coprod> Y) \<rightarrow> Z"
    by (typecheck_cfuncs, simp add: assms)
  then have y_type2: "z \<in>\<^sub>c Z"
    using cfunc_type_def y_type by auto
  then have "\<exists> y. y \<in>\<^sub>c Y \<and> g \<circ>\<^sub>c y  = z"
    using assms(2) assms(3) cfunc_type_def surjective_def by auto
  then obtain y where y_def: "y \<in>\<^sub>c Y \<and> g \<circ>\<^sub>c y  = z"
    by blast
  have coproj_x_type: "(right_coproj X Y)  \<circ>\<^sub>c y  \<in>\<^sub>c (X \<Coprod> Y)"
    using comp_type right_proj_type y_def by blast
  have "(f \<amalg> g) \<circ>\<^sub>c  ((right_coproj X Y)  \<circ>\<^sub>c y ) = z"
    using assms(1) assms(2) cfunc_type_def comp_associative fug_type right_coproj_cfunc_coprod right_proj_type y_def by auto
  then show "\<exists>y. y \<in>\<^sub>c domain (f \<amalg> g) \<and> f \<amalg> g \<circ>\<^sub>c y = z"
    using cfunc_type_def coproj_x_type fug_type by auto
qed

lemma coprod_eq:
  assumes "a : X \<Coprod> Y \<rightarrow> Z" "b : X \<Coprod> Y \<rightarrow>  Z"
  shows "a = b \<longleftrightarrow> 
    (a \<circ>\<^sub>c left_coproj X Y   = b \<circ>\<^sub>c left_coproj X Y 
      \<and> a \<circ>\<^sub>c right_coproj X Y  = b \<circ>\<^sub>c right_coproj X Y)"
  by (smt assms cfunc_coprod_unique cfunc_type_def codomain_comp domain_comp left_proj_type right_proj_type)

lemma coprod_eqI:
  assumes "a : X \<Coprod> Y \<rightarrow> Z" "b : X \<Coprod> Y \<rightarrow> Z"
  assumes "(a \<circ>\<^sub>c left_coproj X Y   = b \<circ>\<^sub>c left_coproj X Y 
      \<and> a \<circ>\<^sub>c right_coproj X Y  = b \<circ>\<^sub>c right_coproj X Y)"
  shows "a = b"
  using assms coprod_eq  by blast

lemma coprod_eq2:
  assumes "a : X \<rightarrow> Z" "b : Y \<rightarrow> Z" "c : X \<rightarrow>  Z" "d : Y \<rightarrow>  Z"
  shows "(a \<amalg> b) = (c \<amalg> d) \<longleftrightarrow> (a = c \<and> b = d)"
  by (metis assms left_coproj_cfunc_coprod right_coproj_cfunc_coprod)

lemma coprod_decomp:
  assumes "a : X \<Coprod> Y \<rightarrow> A"
  shows "\<exists> x y. a = (x \<amalg> y) \<and> x : X \<rightarrow> A \<and> y : Y \<rightarrow> A"
proof (rule_tac x="a \<circ>\<^sub>c left_coproj X Y" in exI, rule_tac x="a \<circ>\<^sub>c right_coproj X Y" in exI, auto)
  show "a = (a \<circ>\<^sub>c left_coproj X Y) \<amalg> (a \<circ>\<^sub>c right_coproj X Y)"
    using assms cfunc_coprod_unique cfunc_type_def codomain_comp domain_comp left_proj_type right_proj_type by auto
  show "a \<circ>\<^sub>c left_coproj X Y : X \<rightarrow> A"
    by (meson assms comp_type left_proj_type)
  show "a \<circ>\<^sub>c right_coproj X Y : Y \<rightarrow> A"
    by (meson assms comp_type right_proj_type)
qed

(*Proposition 2.4.4*)
lemma truth_value_set_iso_1u1:
  "isomorphism(\<t>\<amalg>\<f>)"
  by (typecheck_cfuncs, smt (verit, best) CollectI epi_mon_is_iso injective_def2
      injective_imp_monomorphism left_coproj_cfunc_coprod left_proj_type maps_into_1u1
      right_coproj_cfunc_coprod right_proj_type surjective_def2 surjective_is_epimorphism 
      true_false_distinct true_false_only_truth_values)


subsubsection  \<open>Equality Predicate with Coproduct Properities\<close>

lemma eq_pred_left_coproj:
  assumes u_type[type_rule]: "u \<in>\<^sub>c X \<Coprod> Y" and x_type[type_rule]: "x \<in>\<^sub>c X"
  shows "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj X Y \<circ>\<^sub>c x\<rangle> = ((eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c u"
proof (cases "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj X Y \<circ>\<^sub>c x\<rangle>= \<t>", auto)
  assume "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj X Y \<circ>\<^sub>c x\<rangle> = \<t>"
  then have u_is_left_coproj: "u = left_coproj X Y \<circ>\<^sub>c x"
    using eq_pred_iff_eq by (typecheck_cfuncs_prems, presburger)
  
  show "\<t> = (eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c u"
  proof -
    have "((eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c u
        = ((eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c x"
      using u_is_left_coproj by auto
    also have "... =  (eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x "
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
    also have "... = eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle>"
      by (typecheck_cfuncs, metis cart_prod_extract_left cfunc_type_def comp_associative)
    also have "... = \<t>"
      using eq_pred_iff_eq by (typecheck_cfuncs, blast)
    then show ?thesis
      by (simp add: calculation)
  qed
next
  assume "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u,left_coproj X Y \<circ>\<^sub>c x\<rangle> \<noteq> \<t>"
  then have eq_pred_false: "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u,left_coproj X Y \<circ>\<^sub>c x\<rangle> = \<f>"
    using true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have u_not_left_coproj_x: "u  \<noteq> left_coproj X Y \<circ>\<^sub>c x"
    using eq_pred_iff_eq_conv by (typecheck_cfuncs_prems, presburger)
  show "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u,left_coproj X Y \<circ>\<^sub>c x\<rangle> = (eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c u"
  proof (insert eq_pred_false, cases "\<exists> g. g : one \<rightarrow> X \<and> u = left_coproj X Y \<circ>\<^sub>c g", auto)  
    fix g
    assume g_type[type_rule]: "g \<in>\<^sub>c X"
    assume u_right_coproj: "u = left_coproj X Y \<circ>\<^sub>c g"
    then have x_not_g: "x \<noteq> g"
      using u_not_left_coproj_x by auto
    show "\<f> = (eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c g"
    proof -
      have "(eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c g
          = (eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c g"
        using comp_associative2 left_coproj_cfunc_coprod by (typecheck_cfuncs, force)
      also have "... = eq_pred X \<circ>\<^sub>c \<langle>g,x\<rangle>"
        by (typecheck_cfuncs, simp add: cart_prod_extract_left comp_associative2)
      also have "... = \<f>"
        using eq_pred_iff_eq_conv x_not_g by (typecheck_cfuncs, blast)
      then show ?thesis
        by (simp add: calculation)
    qed
  next
    assume "\<forall>g. g \<in>\<^sub>c X \<longrightarrow> u \<noteq> left_coproj X Y \<circ>\<^sub>c g"
    then obtain g where g_type[type_rule]: "g \<in>\<^sub>c Y" and u_right_coproj: "u = right_coproj X Y \<circ>\<^sub>c g"
      by (meson coprojs_jointly_surj u_type)

    show "\<f> = (eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c u"  
    proof -
      have "(eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c u
          = (eq_pred X \<circ>\<^sub>c \<langle>id\<^sub>c X,x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)  \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c g"
        using u_right_coproj by auto
      also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c g"
        by (typecheck_cfuncs, simp add: comp_associative2 right_coproj_cfunc_coprod)
      also have "... = \<f>"
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 id_type terminal_func_comp terminal_func_unique)
      then show ?thesis
        using calculation by auto
    qed
  qed
qed

lemma eq_pred_right_coproj:
  assumes u_type[type_rule]: "u \<in>\<^sub>c X \<Coprod> Y" and y_type[type_rule]: "y \<in>\<^sub>c Y"
  shows "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj X Y \<circ>\<^sub>c y\<rangle> = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id Y, y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u"
proof (cases "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj X Y \<circ>\<^sub>c y\<rangle> = \<t>", auto)
  assume "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u,right_coproj X Y \<circ>\<^sub>c y\<rangle> = \<t>"
  then have u_is_right_coproj: "u = right_coproj X Y \<circ>\<^sub>c y"
    using eq_pred_iff_eq by (typecheck_cfuncs_prems, presburger)
  
  show "\<t> = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c u"
  proof -
    have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c u
        = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y"
      using u_is_right_coproj by auto
    also have "... = (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c y"
      by (typecheck_cfuncs, simp add: comp_associative2 right_coproj_cfunc_coprod)
    also have "... = eq_pred Y \<circ>\<^sub>c \<langle>y,y\<rangle>"
      by (typecheck_cfuncs, smt cart_prod_extract_left comp_associative2)
    also have "... = \<t>"
      using eq_pred_iff_eq y_type by auto
    then show ?thesis
      using calculation by auto
  qed
next
  assume "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u,right_coproj X Y \<circ>\<^sub>c y\<rangle> \<noteq> \<t>"
  then have eq_pred_false: "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u,right_coproj X Y \<circ>\<^sub>c y\<rangle> = \<f>"
    using true_false_only_truth_values by (typecheck_cfuncs, blast)
  then have u_not_right_coproj_y: "u  \<noteq> right_coproj X Y \<circ>\<^sub>c y"
    using eq_pred_iff_eq_conv by (typecheck_cfuncs_prems, presburger)

  show "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u,right_coproj X Y \<circ>\<^sub>c y\<rangle> = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c u"
  proof (insert eq_pred_false, cases "\<exists> g. g : one \<rightarrow> Y \<and> u = right_coproj X Y \<circ>\<^sub>c g", auto)
    fix g
    assume g_type[type_rule]: "g \<in>\<^sub>c Y"
    assume u_right_coproj: "u = right_coproj X Y \<circ>\<^sub>c g"
    then have y_not_g: "y \<noteq> g"
      using u_not_right_coproj_y by auto

    show "\<f> = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c g"
    proof -
      have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c g
          = (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c g"
        by (typecheck_cfuncs, simp add: comp_associative2 right_coproj_cfunc_coprod)
      also have "... = eq_pred Y \<circ>\<^sub>c \<langle>g,y\<rangle>"
        using cart_prod_extract_left comp_associative2 by (typecheck_cfuncs, auto)
      also have "... = \<f>"
        using eq_pred_iff_eq_conv y_not_g y_type g_type by blast
      then show ?thesis
        using calculation by auto
    qed
  next
    assume "\<forall>g. g \<in>\<^sub>c Y \<longrightarrow> u \<noteq> right_coproj X Y \<circ>\<^sub>c g"
    then obtain g where g_type[type_rule]: "g \<in>\<^sub>c X" and u_left_coproj: "u = left_coproj X Y \<circ>\<^sub>c g"
      by (meson coprojs_jointly_surj u_type)

    show "\<f> = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c u"
    proof -
      have "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c u
          = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c g"
        using u_left_coproj by auto
      also have "... = (\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c g"
        by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
      also have "... = \<f>"
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 id_type terminal_func_comp terminal_func_unique)
      then show ?thesis
        using calculation by auto
    qed
  qed
qed

subsection  \<open>Bowtie Product\<close>

definition cfunc_bowtie_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<bowtie>\<^sub>f" 55) where
  "f \<bowtie>\<^sub>f g = ((left_coproj (codomain f) (codomain g)) \<circ>\<^sub>c f) \<amalg> ((right_coproj (codomain f) (codomain g)) \<circ>\<^sub>c g)"

lemma cfunc_bowtie_prod_def2: 
  assumes "f : X \<rightarrow> Y" "g : V\<rightarrow> W"
  shows "f \<bowtie>\<^sub>f g = (left_coproj Y W \<circ>\<^sub>c f) \<amalg> (right_coproj Y W \<circ>\<^sub>c g)"
  using assms cfunc_bowtie_prod_def cfunc_type_def by auto

lemma cfunc_bowtie_prod_type[type_rule]:
  "f : X \<rightarrow> Y \<Longrightarrow> g : V \<rightarrow> W \<Longrightarrow> f \<bowtie>\<^sub>f g : X \<Coprod> V \<rightarrow> Y \<Coprod> W"
  unfolding cfunc_bowtie_prod_def
  using cfunc_coprod_type cfunc_type_def comp_type left_proj_type right_proj_type by auto

lemma left_coproj_cfunc_bowtie_prod:
  "f : X \<rightarrow> Y \<Longrightarrow> g : V \<rightarrow> W \<Longrightarrow> (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X V) = (left_coproj Y W) \<circ>\<^sub>c f"
  unfolding cfunc_bowtie_prod_def2
  by (meson comp_type left_coproj_cfunc_coprod left_proj_type right_proj_type)

 lemma right_coproj_cfunc_bowtie_prod:
  "f : X \<rightarrow> Y \<Longrightarrow> g : V \<rightarrow> W \<Longrightarrow> (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X V) = (right_coproj Y W) \<circ>\<^sub>c g"
  unfolding cfunc_bowtie_prod_def2
  by (meson comp_type right_coproj_cfunc_coprod right_proj_type left_proj_type)

lemma cfunc_bowtie_prod_unique: "f : X \<rightarrow> Y \<Longrightarrow> g : V \<rightarrow> W \<Longrightarrow> h : X \<Coprod> V \<rightarrow> Y \<Coprod> W \<Longrightarrow>
    h \<circ>\<^sub>c left_coproj X V   = (left_coproj Y W) \<circ>\<^sub>c f \<Longrightarrow>
    h \<circ>\<^sub>c right_coproj X V = (right_coproj Y W) \<circ>\<^sub>c g \<Longrightarrow> h = f \<bowtie>\<^sub>f g"
  unfolding cfunc_bowtie_prod_def
  using cfunc_coprod_unique cfunc_type_def codomain_comp domain_comp left_proj_type right_proj_type by auto

(*Dual to Proposition 2.1.11*)
lemma identity_distributes_across_composition_dual:
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C"
  shows "(g  \<circ>\<^sub>c f) \<bowtie>\<^sub>f id(X)  = (g \<bowtie>\<^sub>f id(X)) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id(X))"
proof - 
  from cfunc_bowtie_prod_unique
  have uniqueness: "\<forall>h. h : A \<Coprod>  X \<rightarrow> C \<Coprod> X \<and>
    h \<circ>\<^sub>c left_coproj A X  =   left_coproj C X \<circ>\<^sub>c (g \<circ>\<^sub>c f) \<and>
    h \<circ>\<^sub>c right_coproj A X = right_coproj C X \<circ>\<^sub>c  id(X) \<longrightarrow>
    h =  (g \<circ>\<^sub>c f) \<bowtie>\<^sub>f  id\<^sub>c X"
    using assms by (typecheck_cfuncs, simp add: cfunc_bowtie_prod_unique)
    
  have left_eq: " ((g \<bowtie>\<^sub>f id\<^sub>c X) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id\<^sub>c X)) \<circ>\<^sub>c left_coproj A X = left_coproj C X \<circ>\<^sub>c (g  \<circ>\<^sub>c f)"
    by (typecheck_cfuncs, smt comp_associative2 left_coproj_cfunc_bowtie_prod left_proj_type assms)

  have right_eq: " ((g \<bowtie>\<^sub>f id\<^sub>c X) \<circ>\<^sub>c (f \<bowtie>\<^sub>f id\<^sub>c X)) \<circ>\<^sub>c right_coproj A X = right_coproj C X \<circ>\<^sub>c id X"
    by(typecheck_cfuncs, smt comp_associative2 id_right_unit2 right_coproj_cfunc_bowtie_prod right_proj_type assms)

  show ?thesis
    using assms left_eq right_eq uniqueness by (typecheck_cfuncs, auto)
qed

lemma coproduct_of_beta:
  "\<beta>\<^bsub>X\<^esub> \<amalg> \<beta>\<^bsub>Y\<^esub> = \<beta>\<^bsub>X\<Coprod>Y\<^esub>"
  by (metis (full_types) cfunc_coprod_unique left_proj_type right_proj_type terminal_func_comp terminal_func_type)

lemma cfunc_bowtieprod_comp_cfunc_coprod:
  assumes a_type: "a : Y \<rightarrow> Z" and b_type: "b : W \<rightarrow> Z"
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : V \<rightarrow> W"
  shows "(a \<amalg> b) \<circ>\<^sub>c  (f \<bowtie>\<^sub>f g)   = (a \<circ>\<^sub>c f) \<amalg> (b \<circ>\<^sub>c g)"
proof - 
  from cfunc_bowtie_prod_unique have uniqueness:
    "\<forall>h. h : X \<Coprod> V \<rightarrow> Z \<and> h \<circ>\<^sub>c left_coproj X V   = a \<circ>\<^sub>c f \<and> h \<circ>\<^sub>c right_coproj X V  = b \<circ>\<^sub>c g \<longrightarrow> 
      h = (a \<circ>\<^sub>c f) \<amalg> (b \<circ>\<^sub>c g)"
    using assms comp_type by (metis (full_types) cfunc_coprod_unique) 

  have left_eq: "(a \<amalg> b \<circ>\<^sub>c f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj X V = (a \<circ>\<^sub>c f)"
  proof - 
    have "(a \<amalg> b \<circ>\<^sub>c f \<bowtie>\<^sub>f g)  \<circ>\<^sub>c left_coproj X V = (a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)  \<circ>\<^sub>c left_coproj X V"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (a \<amalg> b)  \<circ>\<^sub>c left_coproj Y W \<circ>\<^sub>c f"
      using f_type g_type left_coproj_cfunc_bowtie_prod by auto
    also have "... = ((a \<amalg> b)  \<circ>\<^sub>c left_coproj Y W) \<circ>\<^sub>c f"
      using a_type assms(2) cfunc_type_def comp_associative f_type by (typecheck_cfuncs, auto)
    also have "... = (a \<circ>\<^sub>c f)"
      using a_type b_type left_coproj_cfunc_coprod by presburger
    then show  "(a \<amalg> b \<circ>\<^sub>c f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj X V = (a \<circ>\<^sub>c f)"
      by (simp add: calculation)
  qed

  have right_eq: "(a \<amalg> b \<circ>\<^sub>c f \<bowtie>\<^sub>f g)  \<circ>\<^sub>c right_coproj X V = (b \<circ>\<^sub>c g)"
  proof - 
    have "(a \<amalg> b \<circ>\<^sub>c f \<bowtie>\<^sub>f g)  \<circ>\<^sub>c right_coproj X V = (a \<amalg> b) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g)  \<circ>\<^sub>c right_coproj X V"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (a \<amalg> b)  \<circ>\<^sub>c right_coproj Y W \<circ>\<^sub>c g"
      using f_type g_type right_coproj_cfunc_bowtie_prod by auto
    also have "... = ((a \<amalg> b)  \<circ>\<^sub>c right_coproj Y W) \<circ>\<^sub>c g"
      using a_type assms(2) cfunc_type_def comp_associative g_type by (typecheck_cfuncs, auto)
    also have "... = (b \<circ>\<^sub>c g)"
      using a_type b_type right_coproj_cfunc_coprod by auto
    then show "(a \<amalg> b \<circ>\<^sub>c f \<bowtie>\<^sub>f g)  \<circ>\<^sub>c right_coproj X V = (b \<circ>\<^sub>c g)"
      by (simp add: calculation)
  qed

  show "(a \<amalg> b) \<circ>\<^sub>c  (f \<bowtie>\<^sub>f g)   = (a \<circ>\<^sub>c f) \<amalg> (b \<circ>\<^sub>c g)"
    using uniqueness left_eq right_eq assms
    by (typecheck_cfuncs, erule_tac x="(a \<amalg> b) \<circ>\<^sub>c  (f \<bowtie>\<^sub>f g)" in allE, auto)
qed

lemma id_bowtie_prod: "id(X) \<bowtie>\<^sub>f id(Y) = id(X \<Coprod> Y)"
  by (metis cfunc_bowtie_prod_def id_codomain id_coprod id_right_unit2 left_proj_type right_proj_type)

lemma cfunc_bowtie_prod_comp_cfunc_bowtie_prod:
  assumes "f : X \<rightarrow> Y" "g : V \<rightarrow> W" "x : Y \<rightarrow> S" "y : W \<rightarrow> T"
  shows "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) = (x \<circ>\<^sub>c f) \<bowtie>\<^sub>f (y \<circ>\<^sub>c g)"
proof- 
  have "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c ((left_coproj Y W \<circ>\<^sub>c f) \<amalg> (right_coproj Y W \<circ>\<^sub>c g))
      = ((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c left_coproj Y W \<circ>\<^sub>c f) \<amalg> ((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c right_coproj Y W \<circ>\<^sub>c g)"
    using assms by (typecheck_cfuncs, simp add: cfunc_coprod_comp)
  also have "... = (((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c left_coproj Y W) \<circ>\<^sub>c f) \<amalg> (((x \<bowtie>\<^sub>f y) \<circ>\<^sub>c right_coproj Y W) \<circ>\<^sub>c g)"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = ((left_coproj S T \<circ>\<^sub>c x) \<circ>\<^sub>c f) \<amalg> ((right_coproj S T \<circ>\<^sub>c y) \<circ>\<^sub>c g)"
    using assms(3) assms(4) left_coproj_cfunc_bowtie_prod right_coproj_cfunc_bowtie_prod by auto
  also have "... = (left_coproj S T \<circ>\<^sub>c x \<circ>\<^sub>c f) \<amalg> (right_coproj S T \<circ>\<^sub>c y \<circ>\<^sub>c g)"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = (x \<circ>\<^sub>c f) \<bowtie>\<^sub>f (y \<circ>\<^sub>c g)"
    using assms cfunc_bowtie_prod_def cfunc_type_def codomain_comp by auto
  then show "(x \<bowtie>\<^sub>f y) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) = (x \<circ>\<^sub>c f) \<bowtie>\<^sub>f (y \<circ>\<^sub>c g)"
    using assms(1) assms(2) calculation cfunc_bowtie_prod_def2 by auto
qed


lemma cfunc_bowtieprod_epi:
  assumes type_assms: "f : X \<rightarrow> Y" "g : V \<rightarrow> W"
  assumes f_epi: "epimorphism f" and g_epi: "epimorphism g"
  shows "epimorphism (f \<bowtie>\<^sub>f g)"
  using type_assms
proof (typecheck_cfuncs, unfold epimorphism_def3, auto)
  fix x y A
  assume x_type: "x: Y \<Coprod> W \<rightarrow> A"
  assume y_type: "y: Y \<Coprod> W \<rightarrow> A"
  assume eqs: "x \<circ>\<^sub>c f \<bowtie>\<^sub>f g = y \<circ>\<^sub>c f \<bowtie>\<^sub>f g"

  obtain x1 x2 where x_expand: "x = x1 \<amalg> x2" and x1_x2_type: "x1 : Y \<rightarrow> A" "x2 : W \<rightarrow> A"
    using coprod_decomp x_type by blast
  obtain y1 y2 where y_expand: "y = y1 \<amalg> y2" and y1_y2_type: "y1 : Y \<rightarrow> A" "y2 : W \<rightarrow> A"
    using coprod_decomp y_type by blast

  have "(x1 = y1) \<and> (x2 = y2)"
  proof(auto)
    have "x1 \<circ>\<^sub>c f = ((x1 \<amalg> x2) \<circ>\<^sub>c (left_coproj Y W)) \<circ>\<^sub>c f"
      using x1_x2_type left_coproj_cfunc_coprod by auto 
    also have "... = (x1 \<amalg> x2) \<circ>\<^sub>c (left_coproj Y W) \<circ>\<^sub>c f"
      using assms comp_associative2 x_expand x_type by (typecheck_cfuncs, auto)
    also have "... = (x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X V)"
      using left_coproj_cfunc_bowtie_prod type_assms by force
    also have "... = (y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X V)"
      using assms cfunc_type_def comp_associative eqs x_expand x_type y_expand y_type by (typecheck_cfuncs, auto)
    also have "... = (y1 \<amalg> y2) \<circ>\<^sub>c (left_coproj Y W) \<circ>\<^sub>c f"
      using assms by (typecheck_cfuncs, simp add: left_coproj_cfunc_bowtie_prod)
    also have "... = ((y1 \<amalg> y2) \<circ>\<^sub>c (left_coproj Y W)) \<circ>\<^sub>c f"
      using assms comp_associative2 y_expand y_type by (typecheck_cfuncs, blast)
    also have "... = y1 \<circ>\<^sub>c f"
      using y1_y2_type left_coproj_cfunc_coprod by auto 
    then show "x1 = y1"
      using calculation epimorphism_def3 f_epi type_assms(1) x1_x2_type(1) y1_y2_type(1) by fastforce
  next
    have "x2 \<circ>\<^sub>c g = ((x1 \<amalg> x2) \<circ>\<^sub>c (right_coproj Y W)) \<circ>\<^sub>c g"
      using x1_x2_type right_coproj_cfunc_coprod by auto 
    also have "... = (x1 \<amalg> x2) \<circ>\<^sub>c (right_coproj Y W) \<circ>\<^sub>c g"
      using assms comp_associative2 x_expand x_type by (typecheck_cfuncs, auto)
    also have "... = (x1 \<amalg> x2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X V)"
      using right_coproj_cfunc_bowtie_prod type_assms by force
    also have "... = (y1 \<amalg> y2) \<circ>\<^sub>c (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X V)"
      using assms cfunc_type_def comp_associative eqs x_expand x_type y_expand y_type by (typecheck_cfuncs, auto)
    also have "... = (y1 \<amalg> y2) \<circ>\<^sub>c (right_coproj Y W) \<circ>\<^sub>c g"
      using assms by (typecheck_cfuncs, simp add: right_coproj_cfunc_bowtie_prod)
    also have "... = ((y1 \<amalg> y2) \<circ>\<^sub>c (right_coproj Y W)) \<circ>\<^sub>c g"
      using assms comp_associative2 y_expand y_type by (typecheck_cfuncs, blast)
    also have "... = y2 \<circ>\<^sub>c g"
      using right_coproj_cfunc_coprod y1_y2_type(1) y1_y2_type(2) by auto
    then show "x2 = y2"
      using calculation epimorphism_def3 g_epi type_assms(2) x1_x2_type(2) y1_y2_type(2) by fastforce
  qed
  then show "x = y"
    by (simp add: x_expand y_expand)
qed

lemma cfunc_bowtieprod_inj:
  assumes type_assms: "f : X \<rightarrow> Y" "g : V \<rightarrow> W"
  assumes f_epi: "injective f" and g_epi: "injective g"
  shows "injective (f \<bowtie>\<^sub>f g)"
  unfolding injective_def
proof(auto)
  fix z1 z2 
  assume x_type: "z1 \<in>\<^sub>c domain (f \<bowtie>\<^sub>f g)"
  assume y_type: "z2 \<in>\<^sub>c domain (f \<bowtie>\<^sub>f g)"
  assume eqs: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1 = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2"

  have f_bowtie_g_type: "(f \<bowtie>\<^sub>f g) : X \<Coprod> V \<rightarrow> Y \<Coprod> W"
    by (simp add: cfunc_bowtie_prod_type type_assms(1) type_assms(2))

  have x_type2: "z1 \<in>\<^sub>c X \<Coprod> V"
    using cfunc_type_def f_bowtie_g_type x_type by auto
  have y_type2: "z2 \<in>\<^sub>c X \<Coprod> V"
    using cfunc_type_def f_bowtie_g_type y_type by auto

  have z1_decomp: "(\<exists> x1. (x1 \<in>\<^sub>c X \<and> z1 = (left_coproj X V) \<circ>\<^sub>c x1))
      \<or>  (\<exists> y1. (y1 \<in>\<^sub>c V \<and> z1 = (right_coproj X V) \<circ>\<^sub>c y1))"
    by (simp add: coprojs_jointly_surj x_type2)

  have z2_decomp: "(\<exists> x2. (x2 \<in>\<^sub>c X \<and> z2 = (left_coproj X V) \<circ>\<^sub>c x2))
      \<or>  (\<exists> y2. (y2 \<in>\<^sub>c V \<and> z2 = (right_coproj X V) \<circ>\<^sub>c y2))"
    by (simp add: coprojs_jointly_surj y_type2)

  show "z1 = z2"
  proof(cases "(\<exists> x1. (x1 \<in>\<^sub>c X \<and> z1 = (left_coproj X V) \<circ>\<^sub>c x1))")
    assume case1: "\<exists>x1. x1 \<in>\<^sub>c X \<and> z1 = left_coproj X V \<circ>\<^sub>c x1"
    obtain x1 where x1_def: "x1 \<in>\<^sub>c X \<and> z1 = left_coproj X V \<circ>\<^sub>c x1"
          using case1 by blast
    show "z1 = z2"
    proof(cases "(\<exists> x2. (x2 \<in>\<^sub>c X \<and> z2 = (left_coproj X V) \<circ>\<^sub>c x2))")
      assume caseA: "\<exists>x2. x2 \<in>\<^sub>c X \<and> z2 = left_coproj X V \<circ>\<^sub>c x2"
      show "z1 = z2"
      proof - 
        obtain x2 where x2_def: "x2 \<in>\<^sub>c X \<and> z2 = left_coproj X V \<circ>\<^sub>c x2"
          using caseA by blast
        have "x1 = x2"
        proof - 
          have "(left_coproj Y W) \<circ>\<^sub>c f  \<circ>\<^sub>c x1  = ((left_coproj Y W) \<circ>\<^sub>c f) \<circ>\<^sub>c x1"
            using cfunc_type_def comp_associative left_proj_type type_assms(1) x1_def by auto            
          also have "... = 
                ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V)) \<circ>\<^sub>c x1"
            using cfunc_bowtie_prod_def2 left_coproj_cfunc_bowtie_prod type_assms(1) type_assms(2) by auto
          also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V) \<circ>\<^sub>c x1"
            using comp_associative2 type_assms(1) type_assms(2) x1_def by (typecheck_cfuncs, fastforce)
          also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1"
            using cfunc_bowtie_prod_def2 type_assms x1_def by auto
          also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2"
            by (meson eqs)
          also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V) \<circ>\<^sub>c x2"
            using cfunc_bowtie_prod_def2 type_assms(1) type_assms(2) x2_def by auto
          also have "... = ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V)) \<circ>\<^sub>c x2"
            by (typecheck_cfuncs, meson comp_associative2 type_assms(1) type_assms(2) x2_def)
          also have "... = ((left_coproj Y W) \<circ>\<^sub>c f) \<circ>\<^sub>c x2"
            using cfunc_bowtie_prod_def2 left_coproj_cfunc_bowtie_prod type_assms by auto
          also have "... = (left_coproj Y W) \<circ>\<^sub>c f  \<circ>\<^sub>c x2"
            by (metis comp_associative2 left_proj_type type_assms(1) x2_def)
          then have "f  \<circ>\<^sub>c x1 = f  \<circ>\<^sub>c x2"
            using  calculation cfunc_type_def left_coproj_are_monomorphisms
            left_proj_type monomorphism_def type_assms(1) x1_def x2_def by (typecheck_cfuncs,auto)
          then show "x1 = x2"
            by (metis cfunc_type_def f_epi injective_def type_assms(1) x1_def x2_def)
        qed
        then show "z1 = z2"
          by (simp add: x1_def x2_def)
      qed
    next 
      assume caseB: "\<nexists>x2. x2 \<in>\<^sub>c X \<and> z2 = left_coproj X V \<circ>\<^sub>c x2"
      then obtain y2 where y2_def: "(y2 \<in>\<^sub>c V \<and> z2 = (right_coproj X V) \<circ>\<^sub>c y2)"
        using z2_decomp by blast
      have "(left_coproj Y W) \<circ>\<^sub>c f  \<circ>\<^sub>c x1  = ((left_coproj Y W) \<circ>\<^sub>c f) \<circ>\<^sub>c x1"
            using cfunc_type_def comp_associative left_proj_type type_assms(1) x1_def by auto            
      also have "... = 
            ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V)) \<circ>\<^sub>c x1"
        using cfunc_bowtie_prod_def2 left_coproj_cfunc_bowtie_prod type_assms(1) type_assms(2) by auto
      also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V) \<circ>\<^sub>c x1"
        using comp_associative2 type_assms(1,2) x1_def by (typecheck_cfuncs, fastforce)
      also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1"
        using cfunc_bowtie_prod_def2 type_assms x1_def by auto
      also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2"
        by (meson eqs)
      also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V) \<circ>\<^sub>c y2"
        using cfunc_bowtie_prod_def2 type_assms(1) type_assms(2) y2_def by auto
      also have "... = ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V)) \<circ>\<^sub>c y2"
        by (typecheck_cfuncs, meson comp_associative2 type_assms(1) type_assms(2) y2_def)
      also have "... = ((right_coproj Y W) \<circ>\<^sub>c g) \<circ>\<^sub>c y2"
        using right_coproj_cfunc_coprod type_assms by (typecheck_cfuncs, fastforce)
      also have "... = (right_coproj Y W) \<circ>\<^sub>c g  \<circ>\<^sub>c y2"
        using comp_associative2 type_assms(2) y2_def by (typecheck_cfuncs, auto)
      then have False
        using calculation comp_type coproducts_disjoint type_assms x1_def y2_def by auto
      then show "z1 = z2"
        by simp
    qed
  next
    assume case2: "\<nexists>x1. x1 \<in>\<^sub>c X \<and> z1 = left_coproj X V \<circ>\<^sub>c x1"
    then obtain y1 where y1_def: "(y1 \<in>\<^sub>c V \<and> z1 = (right_coproj X V) \<circ>\<^sub>c y1)"
      using z1_decomp by blast
    show "z1 = z2"
    proof(cases "(\<exists> x2. (x2 \<in>\<^sub>c X \<and> z2 = (left_coproj X V) \<circ>\<^sub>c x2))")
      assume caseA: "\<exists>x2. x2 \<in>\<^sub>c X \<and> z2 = left_coproj X V \<circ>\<^sub>c x2"
      show "z1 = z2"
      proof - 
        obtain x2 where x2_def: "x2 \<in>\<^sub>c X \<and> z2 = left_coproj X V \<circ>\<^sub>c x2"
          using caseA by blast
        have "(left_coproj Y W) \<circ>\<^sub>c f  \<circ>\<^sub>c x2  = ((left_coproj Y W) \<circ>\<^sub>c f) \<circ>\<^sub>c x2"
          using comp_associative2 type_assms(1) x2_def by (typecheck_cfuncs, auto)
        also have "... =
              ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V)) \<circ>\<^sub>c x2"
          using cfunc_bowtie_prod_def2 left_coproj_cfunc_bowtie_prod type_assms by auto
        also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (left_coproj X V) \<circ>\<^sub>c x2"
          using comp_associative2 type_assms x2_def by (typecheck_cfuncs, fastforce)
        also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2"
          using cfunc_bowtie_prod_def2 type_assms x2_def by auto
        also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1"
          by (simp add: eqs)
        also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V) \<circ>\<^sub>c y1"
          using cfunc_bowtie_prod_def2 type_assms y1_def by auto
        also have "... = ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V)) \<circ>\<^sub>c y1"
          by (typecheck_cfuncs, meson comp_associative2 type_assms(1) type_assms(2) y1_def)
        also have "... = ((right_coproj Y W) \<circ>\<^sub>c g) \<circ>\<^sub>c y1"
          using right_coproj_cfunc_coprod type_assms  by (typecheck_cfuncs, fastforce)
        also have "... = (right_coproj Y W) \<circ>\<^sub>c g  \<circ>\<^sub>c y1"
          using comp_associative2 type_assms(2) y1_def by (typecheck_cfuncs, auto)
        then have False
          using calculation comp_type coproducts_disjoint type_assms x2_def y1_def by auto
        then show "z1 = z2"
          by simp
      qed
    next
      assume caseB: "\<nexists>x2. x2 \<in>\<^sub>c X \<and> z2 = left_coproj X V \<circ>\<^sub>c x2"
      then obtain y2 where y2_def: "(y2 \<in>\<^sub>c V \<and> z2 = (right_coproj X V) \<circ>\<^sub>c y2)"
        using z2_decomp by blast
        have "y1 = y2"
        proof - 
          have "(right_coproj Y W) \<circ>\<^sub>c g  \<circ>\<^sub>c y1  = ((right_coproj Y W) \<circ>\<^sub>c g) \<circ>\<^sub>c y1"
            using comp_associative2 type_assms(2) y1_def by (typecheck_cfuncs, auto)
          also have "... =
                ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V)) \<circ>\<^sub>c y1"
            using right_coproj_cfunc_coprod type_assms by (typecheck_cfuncs, fastforce)
          also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V) \<circ>\<^sub>c y1"
            using comp_associative2 type_assms  y1_def by (typecheck_cfuncs, fastforce)
          also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z1"
            using cfunc_bowtie_prod_def2 type_assms y1_def by auto
          also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c z2"
            by (meson eqs)
          also have "... = (((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V) \<circ>\<^sub>c y2"
            using cfunc_bowtie_prod_def2 type_assms y2_def by auto
          also have "... = ((((left_coproj Y W) \<circ>\<^sub>c f) \<amalg> ((right_coproj Y W) \<circ>\<^sub>c g)) \<circ>\<^sub>c (right_coproj X V)) \<circ>\<^sub>c y2"
            by (typecheck_cfuncs, meson comp_associative2 type_assms  y2_def)
          also have "... = ((right_coproj Y W) \<circ>\<^sub>c g) \<circ>\<^sub>c y2"
            using right_coproj_cfunc_coprod type_assms by (typecheck_cfuncs, fastforce)
          also have "... = (right_coproj Y W) \<circ>\<^sub>c g  \<circ>\<^sub>c y2"
            using comp_associative2 type_assms(2) y2_def by (typecheck_cfuncs, auto)
          then have "g  \<circ>\<^sub>c y1 = g  \<circ>\<^sub>c y2"
            using  calculation cfunc_type_def right_coproj_are_monomorphisms
            right_proj_type monomorphism_def type_assms(2) y1_def y2_def by (typecheck_cfuncs,auto)
          then show "y1 = y2"
            by (metis cfunc_type_def g_epi injective_def type_assms(2) y1_def y2_def)
        qed
        then show "z1 = z2"
          by (simp add: y1_def y2_def)
      qed
   qed
 qed

lemma cfunc_bowtieprod_inj_converse:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes inj_f_bowtie_g: "injective (f \<bowtie>\<^sub>f g)"
  shows "(injective f)\<and> (injective g)"
  unfolding injective_def
proof(auto)
  fix x y 
  assume x_type: "x \<in>\<^sub>c domain f" 
  assume y_type: "y \<in>\<^sub>c domain f"
  assume eqs:    "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"

  have x_type2: "x \<in>\<^sub>c X"
    using cfunc_type_def type_assms(1) x_type by auto
  have y_type2: "y \<in>\<^sub>c X"
    using cfunc_type_def type_assms(1) y_type by auto
  have fg_bowtie_tyepe: "(f \<bowtie>\<^sub>f g) : (X \<Coprod> Z) \<rightarrow> (Y \<Coprod> W)"
    using assms by typecheck_cfuncs
  have lift: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X Z) \<circ>\<^sub>c x = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X Z) \<circ>\<^sub>c y"
  proof - 
    have "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X Z) \<circ>\<^sub>c x = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X Z)) \<circ>\<^sub>c x"
      using x_type2 comp_associative2 fg_bowtie_tyepe by (typecheck_cfuncs, auto)
    also have  "... =  ((left_coproj Y W) \<circ>\<^sub>c f) \<circ>\<^sub>c x"
      using left_coproj_cfunc_bowtie_prod type_assms(1) type_assms(2) by auto
    also have "... = (left_coproj Y W) \<circ>\<^sub>c f \<circ>\<^sub>c x"
      using x_type2 comp_associative2 type_assms(1) by (typecheck_cfuncs, auto)
    also have "... = (left_coproj Y W) \<circ>\<^sub>c f \<circ>\<^sub>c y"
      by (simp add: eqs)
    also have "... = ((left_coproj Y W) \<circ>\<^sub>c f) \<circ>\<^sub>c y"
      using y_type2 comp_associative2 type_assms(1) by (typecheck_cfuncs, auto)
    also have "... = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X Z)) \<circ>\<^sub>c y"
      using left_coproj_cfunc_bowtie_prod type_assms(1) type_assms(2) by auto
    also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (left_coproj X Z) \<circ>\<^sub>c y"
      using y_type2 comp_associative2 fg_bowtie_tyepe by (typecheck_cfuncs, auto)
    then show ?thesis using calculation by auto
  qed
  then have "monomorphism((f \<bowtie>\<^sub>f g))"
    using inj_f_bowtie_g injective_imp_monomorphism by auto
  then have "(left_coproj X Z) \<circ>\<^sub>c x = (left_coproj X Z) \<circ>\<^sub>c y"
    by (typecheck_cfuncs, metis cfunc_type_def fg_bowtie_tyepe inj_f_bowtie_g injective_def lift x_type2 y_type2)
  then show "x = y"
    using x_type2 y_type2 cfunc_type_def left_coproj_are_monomorphisms left_proj_type monomorphism_def by auto
next
  fix x y 
  assume x_type: "x \<in>\<^sub>c domain g" 
  assume y_type: "y \<in>\<^sub>c domain g"
  assume eqs:    "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"

  have x_type2: "x \<in>\<^sub>c Z"
    using cfunc_type_def type_assms(2) x_type by auto
  have y_type2: "y \<in>\<^sub>c Z"
    using cfunc_type_def type_assms(2) y_type by auto
  have fg_bowtie_tyepe: "(f \<bowtie>\<^sub>f g) : (X \<Coprod> Z) \<rightarrow> (Y \<Coprod> W)"
    using assms by typecheck_cfuncs
  have lift: "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X Z) \<circ>\<^sub>c x = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X Z) \<circ>\<^sub>c y"
  proof - 
    have "(f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X Z) \<circ>\<^sub>c x = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X Z)) \<circ>\<^sub>c x"
      using x_type2 comp_associative2 fg_bowtie_tyepe by (typecheck_cfuncs, auto)
    also have  "... =  ((right_coproj Y W) \<circ>\<^sub>c g) \<circ>\<^sub>c x"
      using right_coproj_cfunc_bowtie_prod type_assms(1) type_assms(2) by auto
    also have "... = (right_coproj Y W) \<circ>\<^sub>c g \<circ>\<^sub>c x"
      using x_type2 comp_associative2 type_assms(2) by (typecheck_cfuncs, auto)
    also have "... = (right_coproj Y W) \<circ>\<^sub>c g \<circ>\<^sub>c y"
      by (simp add: eqs)
    also have "... = ((right_coproj Y W) \<circ>\<^sub>c g) \<circ>\<^sub>c y"
      using y_type2 comp_associative2 type_assms(2) by (typecheck_cfuncs, auto)
    also have "... = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X Z)) \<circ>\<^sub>c y"
      using right_coproj_cfunc_bowtie_prod type_assms(1) type_assms(2) by auto
    also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (right_coproj X Z) \<circ>\<^sub>c y"
      using y_type2 comp_associative2 fg_bowtie_tyepe by (typecheck_cfuncs, auto)
    then show ?thesis using calculation by auto
  qed
  then have "monomorphism((f \<bowtie>\<^sub>f g))"
    using inj_f_bowtie_g injective_imp_monomorphism by auto
  then have "(right_coproj X Z) \<circ>\<^sub>c x = (right_coproj X Z) \<circ>\<^sub>c y"
    by (typecheck_cfuncs, metis cfunc_type_def fg_bowtie_tyepe inj_f_bowtie_g injective_def lift x_type2 y_type2)
  then show "x = y"
    using x_type2 y_type2 cfunc_type_def right_coproj_are_monomorphisms right_proj_type monomorphism_def by auto
qed

lemma cfunc_bowtieprod_iso:
  assumes type_assms: "f : X \<rightarrow> Y" "g : V \<rightarrow> W"
  assumes f_iso: "isomorphism f" and g_iso: "isomorphism g"
  shows "isomorphism (f \<bowtie>\<^sub>f g)"
  by (typecheck_cfuncs, meson cfunc_bowtieprod_epi cfunc_bowtieprod_inj epi_mon_is_iso f_iso g_iso injective_imp_monomorphism iso_imp_epi_and_monic monomorphism_imp_injective singletonI assms)

lemma cfunc_bowtieprod_surj_converse:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes inj_f_bowtie_g: "surjective (f \<bowtie>\<^sub>f g)"
  shows "(surjective f)\<and> (surjective g)"
  unfolding surjective_def
proof(auto)
  fix y 
  assume y_type: "y \<in>\<^sub>c codomain f" 
  then have y_type2: "y \<in>\<^sub>c Y"
    using cfunc_type_def type_assms(1) by auto
  then have coproj_y_type: "(left_coproj Y W) \<circ>\<^sub>c y \<in>\<^sub>c (Y \<Coprod> W)" 
    by typecheck_cfuncs
  have fg_type: "(f \<bowtie>\<^sub>f g) : (X \<Coprod> Z) \<rightarrow> (Y \<Coprod> W)"
    using assms by typecheck_cfuncs
  obtain xz where xz_def: "xz \<in>\<^sub>c (X \<Coprod> Z) \<and> (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (xz) =  (left_coproj Y W) \<circ>\<^sub>c y"
    using fg_type y_type2 cfunc_type_def inj_f_bowtie_g surjective_def by (typecheck_cfuncs, auto)
  then have xz_form: "(\<exists> x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x =   xz) \<or>  
                      (\<exists> z. z \<in>\<^sub>c Z \<and> right_coproj X Z \<circ>\<^sub>c z =  xz)"
    using coprojs_jointly_surj xz_def by (typecheck_cfuncs, blast)
  show "\<exists> x. x \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = y"
  proof(cases "(\<exists> x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x =   xz)")
    assume "(\<exists> x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x =   xz)"
    then obtain x where x_def: "x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x = xz"
      by blast
    have "f \<circ>\<^sub>c x = y"
    proof - 
      have "left_coproj Y W \<circ>\<^sub>c y = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (xz)"
        by (simp add: xz_def)
      also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj X Z \<circ>\<^sub>c x"
        by (simp add: x_def)
      also have "... = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj X Z) \<circ>\<^sub>c x"
        using  comp_associative2 fg_type x_def by (typecheck_cfuncs, auto)
      also have "... = (left_coproj Y W \<circ>\<^sub>c f) \<circ>\<^sub>c x"
        using left_coproj_cfunc_bowtie_prod type_assms by auto
      also have "... = left_coproj Y W \<circ>\<^sub>c f \<circ>\<^sub>c x"
        using comp_associative2 type_assms(1) x_def by (typecheck_cfuncs, auto)
      then show "f \<circ>\<^sub>c x = y"
        using type_assms(1) x_def y_type2  
        by (typecheck_cfuncs, metis calculation cfunc_type_def left_coproj_are_monomorphisms left_proj_type monomorphism_def x_def)
    qed
    then show ?thesis
      using cfunc_type_def type_assms(1) x_def by auto
 next
   assume "\<nexists>x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x = xz"
   then obtain z where z_def: "z \<in>\<^sub>c Z \<and> right_coproj X Z \<circ>\<^sub>c z = xz"
     using xz_form by blast
   have False
    proof - 
      have "left_coproj Y W \<circ>\<^sub>c y = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (xz)"
        by (simp add: xz_def)         
      also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj X Z \<circ>\<^sub>c z"
        by (simp add: z_def)
      also have "... = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj X Z) \<circ>\<^sub>c z"
        using comp_associative2 fg_type z_def by (typecheck_cfuncs, auto)
      also have "... = (right_coproj Y W \<circ>\<^sub>c g) \<circ>\<^sub>c z"
        using right_coproj_cfunc_bowtie_prod type_assms by auto
      also have "... = right_coproj Y W \<circ>\<^sub>c g \<circ>\<^sub>c z"
        using comp_associative2 type_assms(2) z_def by (typecheck_cfuncs, auto)
      then show False
        using calculation comp_type coproducts_disjoint type_assms(2) y_type2 z_def by auto
   qed
   then show ?thesis
     by simp
 qed
next
  fix y
  assume y_type: "y \<in>\<^sub>c codomain g"
  then have y_type2: "y \<in>\<^sub>c W"
    using cfunc_type_def type_assms(2) by auto 
  then have coproj_y_type: "(right_coproj Y W) \<circ>\<^sub>c y \<in>\<^sub>c (Y \<Coprod> W)" 
    using cfunc_type_def comp_type right_proj_type type_assms(2) by auto
  have fg_type: "(f \<bowtie>\<^sub>f g) : (X \<Coprod> Z) \<rightarrow> (Y \<Coprod> W)"
    by (simp add: cfunc_bowtie_prod_type type_assms)
  obtain xz where xz_def: "xz \<in>\<^sub>c (X \<Coprod> Z) \<and> (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (xz) =  (right_coproj Y W) \<circ>\<^sub>c y"
    using fg_type y_type2 cfunc_type_def inj_f_bowtie_g surjective_def by (typecheck_cfuncs, auto)
  then have xz_form: "(\<exists> x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x =   xz) \<or>  
                      (\<exists> z. z \<in>\<^sub>c Z \<and> right_coproj X Z \<circ>\<^sub>c z =  xz)"
    using coprojs_jointly_surj xz_def by (typecheck_cfuncs, blast)
  show "\<exists>x. x \<in>\<^sub>c domain g \<and> g \<circ>\<^sub>c x = y"
  proof(cases "(\<exists> x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x =   xz)")
    assume "(\<exists> x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x =   xz)"
    then obtain x where x_def: "x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x = xz"
      by blast
    have False
    proof - 
      have "right_coproj Y W \<circ>\<^sub>c y = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (xz)"
        by (simp add: xz_def)
      also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj X Z \<circ>\<^sub>c x"
        by (simp add: x_def)
      also have "... = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c left_coproj X Z) \<circ>\<^sub>c x"
        using  comp_associative2 fg_type x_def by (typecheck_cfuncs, auto)
      also have "... = (left_coproj Y W \<circ>\<^sub>c f) \<circ>\<^sub>c x"
        using left_coproj_cfunc_bowtie_prod type_assms by auto
      also have "... = left_coproj Y W \<circ>\<^sub>c f \<circ>\<^sub>c x"
        using comp_associative2 type_assms(1) x_def by (typecheck_cfuncs, auto)
      then show False
        by (metis calculation comp_type coproducts_disjoint type_assms(1) x_def y_type2)
    qed
    then show ?thesis
      by simp
next
  assume "\<nexists>x. x \<in>\<^sub>c X \<and> left_coproj X Z \<circ>\<^sub>c x = xz"
  then obtain z where z_def: "z \<in>\<^sub>c Z \<and> right_coproj X Z \<circ>\<^sub>c z = xz"
    using xz_form by blast
  have "g \<circ>\<^sub>c z = y"
    proof - 
      have "right_coproj Y W \<circ>\<^sub>c y = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c (xz)"
        by (simp add: xz_def)         
      also have "... = (f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj X Z \<circ>\<^sub>c z"
        by (simp add: z_def)
      also have "... = ((f \<bowtie>\<^sub>f g) \<circ>\<^sub>c right_coproj X Z) \<circ>\<^sub>c z"
        using comp_associative2 fg_type z_def by (typecheck_cfuncs, auto)
      also have "... = (right_coproj Y W \<circ>\<^sub>c g) \<circ>\<^sub>c z"
        using right_coproj_cfunc_bowtie_prod type_assms by auto
      also have "... = right_coproj Y W \<circ>\<^sub>c g \<circ>\<^sub>c z"
        using comp_associative2 type_assms(2) z_def by (typecheck_cfuncs, auto)
      then show ?thesis
        by (metis calculation cfunc_type_def codomain_comp monomorphism_def 
           right_coproj_are_monomorphisms right_proj_type type_assms(2) y_type2 z_def)
    qed
    then show ?thesis
      using cfunc_type_def type_assms(2) z_def by auto
 qed
qed

subsection  \<open>Case Bool\<close>

definition case_bool :: "cfunc" where
  "case_bool = (THE f. f : \<Omega> \<rightarrow> (one \<Coprod> one) \<and>  
    (\<t> \<amalg> \<f>) \<circ>\<^sub>c f = id(\<Omega>) \<and> f \<circ>\<^sub>c (\<t> \<amalg> \<f>) = id (one \<Coprod> one))"

lemma case_bool_def2:
  "case_bool : \<Omega> \<rightarrow> (one \<Coprod> one) \<and>  
    (\<t> \<amalg> \<f>) \<circ>\<^sub>c case_bool = id(\<Omega>) \<and> case_bool \<circ>\<^sub>c (\<t> \<amalg> \<f>) = id (one \<Coprod> one)"
proof (unfold case_bool_def, rule theI', auto)
  show "\<exists>x. x : \<Omega> \<rightarrow> one \<Coprod> one \<and> \<t> \<amalg> \<f> \<circ>\<^sub>c x = id\<^sub>c \<Omega> \<and> x \<circ>\<^sub>c \<t> \<amalg> \<f> = id\<^sub>c (one \<Coprod> one)"
    using truth_value_set_iso_1u1 unfolding isomorphism_def
    by (auto, rule_tac x=g in exI, typecheck_cfuncs, simp add: cfunc_type_def)
next
  fix x y
  assume x_type[type_rule]: "x : \<Omega> \<rightarrow> one \<Coprod> one" and y_type[type_rule]: "y : \<Omega> \<rightarrow> one \<Coprod> one"
  assume x_left_inv: "\<t> \<amalg> \<f> \<circ>\<^sub>c x = id\<^sub>c \<Omega>"
  assume "x \<circ>\<^sub>c \<t> \<amalg> \<f> = id\<^sub>c (one \<Coprod> one)" "y \<circ>\<^sub>c \<t> \<amalg> \<f> = id\<^sub>c (one \<Coprod> one)"
  then have "x \<circ>\<^sub>c \<t> \<amalg> \<f> = y \<circ>\<^sub>c \<t> \<amalg> \<f>"
    by auto
  then have "x \<circ>\<^sub>c \<t> \<amalg> \<f> \<circ>\<^sub>c x = y \<circ>\<^sub>c \<t> \<amalg> \<f> \<circ>\<^sub>c x"
    by (typecheck_cfuncs, auto simp add: comp_associative2)
  then show "x = y"
    using id_right_unit2 x_left_inv by (typecheck_cfuncs_prems, auto)
qed

lemma case_bool_type[type_rule]: 
  "case_bool : \<Omega> \<rightarrow> (one \<Coprod> one)"
  using case_bool_def2 by auto

lemma case_bool_true_coprod_false:
  "case_bool \<circ>\<^sub>c (\<t> \<amalg> \<f>) = id (one \<Coprod> one)"
  using case_bool_def2 by auto

lemma true_coprod_false_case_bool:
  "(\<t> \<amalg> \<f>) \<circ>\<^sub>c case_bool = id \<Omega>"
  using case_bool_def2 by auto

lemma case_bool_iso:
  "isomorphism(case_bool)"
  using case_bool_def2 unfolding isomorphism_def
  by (rule_tac x="\<t> \<amalg> \<f>" in exI, typecheck_cfuncs, auto simp add: cfunc_type_def)

lemma case_bool_true_and_false:
  "(case_bool \<circ>\<^sub>c \<t> = left_coproj one one) \<and> (case_bool \<circ>\<^sub>c \<f> = right_coproj one one)"
proof -
  have "(left_coproj one one) \<amalg>  (right_coproj one one) = id(one \<Coprod> one)"
    by (simp add: id_coprod)
  also have "... = (case_bool) \<circ>\<^sub>c (\<t> \<amalg> \<f>)"
    by (simp add: case_bool_def2)
  also have "...  = (case_bool \<circ>\<^sub>c \<t>) \<amalg> (case_bool \<circ>\<^sub>c \<f>)"
    using case_bool_def2 cfunc_coprod_comp false_func_type true_func_type by auto
  then show ?thesis 
    using  calculation coprod_eq2 by (typecheck_cfuncs, auto)
qed

lemma case_bool_true:
  "case_bool \<circ>\<^sub>c \<t> = left_coproj one one"
  by (simp add: case_bool_true_and_false)

lemma case_bool_false:
  "case_bool \<circ>\<^sub>c \<f> = right_coproj one one"
  by (simp add: case_bool_true_and_false)

lemma coprod_case_bool_true:
  assumes "x1 \<in>\<^sub>c X"
  assumes "x2 \<in>\<^sub>c X"
  shows   "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<t> = x1"
proof - 
  have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<t> = (x1 \<amalg> x2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<t>"
    using assms by (typecheck_cfuncs , simp add: comp_associative2)
  also have "... = (x1 \<amalg> x2) \<circ>\<^sub>c  (left_coproj one one)"
    using assms case_bool_true by presburger
  also have "... = x1"
    using assms left_coproj_cfunc_coprod by force
  then show ?thesis
    by (simp add: calculation)
qed

lemma coprod_case_bool_false:
  assumes "x1 \<in>\<^sub>c X"
  assumes "x2 \<in>\<^sub>c X"
  shows   "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<f> = x2"
proof - 
  have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<f> = (x1 \<amalg> x2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<f>"
    using assms by (typecheck_cfuncs , simp add: comp_associative2)
  also have "... = (x1 \<amalg> x2) \<circ>\<^sub>c  (right_coproj one one)"
    using assms case_bool_false by presburger
  also have "... = x2"
    using assms right_coproj_cfunc_coprod by force
  then show ?thesis
    by (simp add: calculation)
qed

subsection  \<open>Distribute Product Over Coproduct Auxillary Mapping\<close>


definition dist_prod_coprod :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "dist_prod_coprod A B C = (id(A) \<times>\<^sub>f (left_coproj B C)) \<amalg> (id(A) \<times>\<^sub>f (right_coproj B C))"

lemma dist_prod_coprod_type[type_rule]:
  "dist_prod_coprod A B C : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
  unfolding dist_prod_coprod_def by typecheck_cfuncs

lemma dist_prod_coprod_left_ap:
  assumes "a \<in>\<^sub>c A" "b \<in>\<^sub>c B"
  shows "dist_prod_coprod A B C \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, b\<rangle>) = \<langle>a, left_coproj B C \<circ>\<^sub>c b\<rangle>"
  unfolding dist_prod_coprod_def using assms 
  by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 left_coproj_cfunc_coprod)

lemma dist_prod_coprod_right_ap:
  assumes "a \<in>\<^sub>c A" "c \<in>\<^sub>c C"
  shows "dist_prod_coprod A B C \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>) = \<langle>a, right_coproj B C \<circ>\<^sub>c c\<rangle>"
  unfolding dist_prod_coprod_def using assms 
  by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 right_coproj_cfunc_coprod)

lemma dist_prod_coprod_mono:
  "monomorphism (dist_prod_coprod A B C)"
proof -
  obtain \<phi> where \<phi>_def: "\<phi> = (id(A) \<times>\<^sub>f (left_coproj B C)) \<amalg> (id(A) \<times>\<^sub>f (right_coproj B C))" and
                 \<phi>_type[type_rule]: "\<phi> : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by typecheck_cfuncs

  have injective: "injective(\<phi>)"
    unfolding injective_def
  proof(auto) 
    fix x y
    assume x_type: "x \<in>\<^sub>c domain \<phi>"
    assume y_type: "y \<in>\<^sub>c domain \<phi>"
    assume equal: "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c y"

    have x_type[type_rule]: "x \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
      using cfunc_type_def \<phi>_type x_type by auto
    then have x_form: "(\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> x = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))
      \<or>  (\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> x = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))"
      by (simp add: coprojs_jointly_surj)
    have y_type[type_rule]: "y \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
      using cfunc_type_def \<phi>_type y_type by auto
    then have y_form: "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))
      \<or>  (\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> y = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
      by (simp add: coprojs_jointly_surj)
    
    show "x = y" 
    proof(cases "(\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> x = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))")
      assume "(\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> x = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))"
      then obtain x' where x'_def[type_rule]: "x' \<in>\<^sub>c A \<times>\<^sub>c B" "x = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c x'"
        by blast
      then have ab_exists: "\<exists> a b. a \<in>\<^sub>c A \<and> b \<in>\<^sub>c B \<and> x' =\<langle>a,b\<rangle>"
        using cart_prod_decomp by blast
      then obtain a b where ab_def[type_rule]: "a \<in>\<^sub>c A" "b \<in>\<^sub>c B"  "x' =\<langle>a,b\<rangle>"
        by blast
      show "x = y"  
      proof(cases "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))")
        assume "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
        then obtain y' where y'_def: "y' \<in>\<^sub>c (A \<times>\<^sub>c B)" "y = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
          by blast
        then have ab_exists: "\<exists> a' b'. a' \<in>\<^sub>c A \<and> b' \<in>\<^sub>c B \<and> y' =\<langle>a',b'\<rangle>"
          using cart_prod_decomp by blast
        then obtain a' b' where a'b'_def[type_rule]: "a' \<in>\<^sub>c A" "b' \<in>\<^sub>c B" "y' =\<langle>a',b'\<rangle>"
          by blast
        have equal_pair: "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
        proof - 
          have "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (left_coproj B C) \<circ>\<^sub>c b\<rangle>"
            using ab_def id_left_unit2 by force
          also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a,  b\<rangle>"
            by (smt ab_def cfunc_cross_prod_comp_cfunc_prod id_type left_proj_type)
          also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, b\<rangle>"
            unfolding \<phi>_def using  left_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = \<phi> \<circ>\<^sub>c x"
            using ab_def comp_associative2 x'_def by (typecheck_cfuncs, fastforce)
          also have "... = \<phi> \<circ>\<^sub>c y"
            by (simp add: local.equal)
          also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', b'\<rangle>"
            using a'b'_def comp_associative2 \<phi>_type y'_def by (typecheck_cfuncs, blast)
          also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a',  b'\<rangle>"
            unfolding \<phi>_def using left_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = \<langle>id(A) \<circ>\<^sub>c a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
            using a'b'_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
          also have "... =  \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
            using a'b'_def id_left_unit2 by force
          then show "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
            by (simp add: calculation)
        qed
        then have a_equal: "(a = a') \<and> (((left_coproj B C) \<circ>\<^sub>c b) = ((left_coproj B C) \<circ>\<^sub>c b'))"
          using a'b'_def ab_def cart_prod_eq2 equal_pair by (typecheck_cfuncs, blast)
        then have b_equal: "b = b'"
          using a'b'_def a_equal ab_def left_coproj_are_monomorphisms left_proj_type monomorphism_def3 by blast
        then show "x = y"
          by (simp add: a'b'_def a_equal ab_def x'_def y'_def)
    next 
      assume "\<nexists>y'. y' \<in>\<^sub>c A \<times>\<^sub>c B \<and> y = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
      then obtain y' where y'_def: "y' \<in>\<^sub>c (A \<times>\<^sub>c C)" "y = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'"
        using  y_form by blast
      then obtain a' c' where a'c'_def: "a' \<in>\<^sub>c A" "c' \<in>\<^sub>c C" "y' =\<langle>a',c'\<rangle>"
        by (meson cart_prod_decomp)
      have equal_pair: "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
      proof - 
        have "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (left_coproj B C) \<circ>\<^sub>c b\<rangle>"
          using ab_def id_left_unit2 by force
        also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a,  b\<rangle>"
          by (smt ab_def cfunc_cross_prod_comp_cfunc_prod id_type left_proj_type)
        also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, b\<rangle>"
          unfolding \<phi>_def using left_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
        also have "... = \<phi> \<circ>\<^sub>c x"
          using ab_def comp_associative2 \<phi>_type x'_def by (typecheck_cfuncs, fastforce)
        also have "... = \<phi> \<circ>\<^sub>c y"
          by (simp add: local.equal)
        also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', c'\<rangle>"
          using a'c'_def comp_associative2 y'_def by (typecheck_cfuncs, blast)
          also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle> a',  c'\<rangle>"
          unfolding \<phi>_def using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
        also have "... = \<langle>id(A) \<circ>\<^sub>c a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
          using a'c'_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs,auto)
        also have "... =  \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
          using a'c'_def id_left_unit2 by force
        then show "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
          by (simp add: calculation)
      qed        
      then have impossible: "(left_coproj B C) \<circ>\<^sub>c b = (right_coproj B C) \<circ>\<^sub>c c'"
        using a'c'_def ab_def element_pair_eq equal_pair by (typecheck_cfuncs, blast)
      then show "x = y"
        using a'c'_def ab_def coproducts_disjoint  by blast
    qed
  next
    assume "\<nexists>x'. x' \<in>\<^sub>c A \<times>\<^sub>c B \<and> x = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c x'"
    then obtain x' where x'_def: "x' \<in>\<^sub>c A \<times>\<^sub>c C" "x = right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c x'"
      using  x_form by blast
    then have ac_exists: "\<exists> a c. a \<in>\<^sub>c A \<and> c \<in>\<^sub>c C \<and> x' =\<langle>a,c\<rangle>"
      using cart_prod_decomp by blast
    then obtain a c where ac_def: "a \<in>\<^sub>c A" "c \<in>\<^sub>c C" "x' =\<langle>a,c\<rangle>"
      by blast
    show "x = y"  
    proof(cases "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))")
      assume "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
      then obtain y' where y'_def: "y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
        by blast
      then obtain a' b' where a'b'_def: "a' \<in>\<^sub>c A \<and> b' \<in>\<^sub>c B \<and> y' =\<langle>a',b'\<rangle>"
        using cart_prod_decomp y'_def by blast
      have equal_pair: "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
      proof - 
        have "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (right_coproj B C) \<circ>\<^sub>c c\<rangle>"
          using ac_def id_left_unit2 by force
        also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle>a,  c\<rangle>"
          by (smt ac_def cfunc_cross_prod_comp_cfunc_prod id_type right_proj_type)
        also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, c\<rangle>"
          unfolding \<phi>_def using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
        also have "... = \<phi> \<circ>\<^sub>c x"
          using ac_def comp_associative2 \<phi>_type x'_def by (typecheck_cfuncs, fastforce)
        also have "... = \<phi> \<circ>\<^sub>c y"
          by (simp add: local.equal)
        also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', b'\<rangle>"
          using a'b'_def comp_associative2 \<phi>_type y'_def by (typecheck_cfuncs, blast)
          also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a',  b'\<rangle>"
          unfolding \<phi>_def using left_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
        also have "... = \<langle>id(A) \<circ>\<^sub>c a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
          using a'b'_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs,auto)
        also have "... =  \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
          using a'b'_def id_left_unit2 by force
        then show "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
          by (simp add: calculation)
      qed        
      then have impossible:  "(right_coproj B C) \<circ>\<^sub>c c = (left_coproj B C) \<circ>\<^sub>c b'"
          using a'b'_def ac_def cart_prod_eq2 equal_pair by (typecheck_cfuncs, blast)
        then show "x = y"
          using a'b'_def ac_def coproducts_disjoint by force
      next 
        assume "\<nexists>y'. y' \<in>\<^sub>c A \<times>\<^sub>c B \<and> y = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
        then obtain y' where y'_def: "y' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> y = right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
          using  y_form by blast
        then obtain a' c' where a'c'_def: "a' \<in>\<^sub>c A" "c' \<in>\<^sub>c C" "y' =\<langle>a',c'\<rangle>"
          using cart_prod_decomp by blast
        have equal_pair: "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
        proof - 
          have "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (right_coproj B C) \<circ>\<^sub>c c\<rangle>"
            using ac_def id_left_unit2 by force
          also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle>a,  c\<rangle>"
            by (smt ac_def cfunc_cross_prod_comp_cfunc_prod id_type right_proj_type)
          also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, c\<rangle>"
            unfolding \<phi>_def using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = \<phi> \<circ>\<^sub>c x"
            using ac_def comp_associative2 \<phi>_type x'_def by (typecheck_cfuncs, fastforce)
          also have "... = \<phi> \<circ>\<^sub>c y"
            by (simp add: local.equal)
          also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', c'\<rangle>"
            using a'c'_def comp_associative2 \<phi>_type y'_def by (typecheck_cfuncs, blast)
          also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle> a',  c'\<rangle>"
            unfolding \<phi>_def using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = \<langle>id(A) \<circ>\<^sub>c a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
            using a'c'_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs,auto)
          also have "... =  \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
            using a'c'_def id_left_unit2 by force
          then show "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
            by (simp add: calculation)
        qed     
        then have a_equal: "(a = a') \<and> ((right_coproj B C) \<circ>\<^sub>c c = (right_coproj B C) \<circ>\<^sub>c c')"
          using a'c'_def ac_def element_pair_eq equal_pair by (typecheck_cfuncs, blast)
        then have c_equal: "c = c'" 
          using a'c'_def a_equal ac_def right_coproj_are_monomorphisms right_proj_type monomorphism_def3 by blast
        then show "x = y"
          by (simp add: a'c'_def a_equal ac_def x'_def y'_def)
      qed
    qed
  qed
  then show "monomorphism (dist_prod_coprod A B C)"
    using \<phi>_def dist_prod_coprod_def injective_imp_monomorphism by fastforce
qed

lemma dist_prod_coprod_epi:
  "epimorphism (dist_prod_coprod A B C)"
proof -
  obtain \<phi> where \<phi>_def: "\<phi> = (id(A) \<times>\<^sub>f (left_coproj B C)) \<amalg> (id(A) \<times>\<^sub>f (right_coproj B C))" and
                 \<phi>_type[type_rule]: "\<phi> : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by typecheck_cfuncs
  have surjective: "surjective((id(A) \<times>\<^sub>f (left_coproj B C)) \<amalg> (id(A) \<times>\<^sub>f (right_coproj B C)))"
    unfolding surjective_def
  proof(auto)
    fix y 
    assume y_type: "y \<in>\<^sub>c codomain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C))"
    then have y_type2: "y \<in>\<^sub>c A \<times>\<^sub>c (B \<Coprod> C)"
      using \<phi>_def \<phi>_type cfunc_type_def by auto
    then obtain a where a_def: "\<exists> bc. a \<in>\<^sub>c A \<and> bc \<in>\<^sub>c (B \<Coprod> C) \<and> y = \<langle>a,bc\<rangle>"
      by (meson cart_prod_decomp)
    then obtain bc where bc_def: "bc \<in>\<^sub>c (B \<Coprod> C) \<and> y = \<langle>a,bc\<rangle>"
      by blast
    have bc_form: "(\<exists> b. b \<in>\<^sub>c B \<and> bc = left_coproj B C  \<circ>\<^sub>c b) \<or> (\<exists> c. c \<in>\<^sub>c C \<and> bc = (right_coproj B C  \<circ>\<^sub>c c))"
      by (simp add: bc_def coprojs_jointly_surj)
    have domain_is: "(A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) = domain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C))"
      by (typecheck_cfuncs, simp add: cfunc_type_def)
    show "\<exists>x. x \<in>\<^sub>c domain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C)) \<and>
             (id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C) \<circ>\<^sub>c x = y"
    proof(cases "(\<exists> b. b \<in>\<^sub>c B \<and> bc = left_coproj B C  \<circ>\<^sub>c b)")
      assume case1: "\<exists>b. b \<in>\<^sub>c B \<and> bc = left_coproj B C \<circ>\<^sub>c b"
      then obtain b where b_def: "b \<in>\<^sub>c B \<and> bc = left_coproj B C \<circ>\<^sub>c b"
        by blast
      then have ab_type: "\<langle>a, b\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c B)"
        using a_def b_def by (typecheck_cfuncs, blast)
      obtain x where x_def: "x = ((left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>a, b\<rangle>)"
        by simp
      have x_type: "x \<in>\<^sub>c domain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C))"
        using ab_type cfunc_type_def codomain_comp domain_comp domain_is left_proj_type x_def by auto
      have y_def2: "y = \<langle>a,left_coproj B C \<circ>\<^sub>c b\<rangle>"
        by (simp add: b_def bc_def)
      have "y = (id(A) \<times>\<^sub>f (left_coproj B C)) \<circ>\<^sub>c \<langle>a,b\<rangle>"
        using a_def b_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 y_def2 by (typecheck_cfuncs, auto)
      also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, b\<rangle>"
        unfolding \<phi>_def by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
      also have "... = \<phi> \<circ>\<^sub>c x"
        using \<phi>_type x_def ab_type comp_associative2 by (typecheck_cfuncs, auto)
      then show "\<exists>x. x \<in>\<^sub>c domain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C)) \<and>
        (id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C) \<circ>\<^sub>c x = y"
        using \<phi>_def calculation x_type by auto
    next
      assume "\<nexists>b. b \<in>\<^sub>c B \<and> bc = left_coproj B C \<circ>\<^sub>c b"
      then have case2: "(\<exists> c. c \<in>\<^sub>c C \<and> bc = (right_coproj B C  \<circ>\<^sub>c c))"
        using bc_form by blast
      then obtain c where c_def: "c \<in>\<^sub>c C \<and> bc = (right_coproj B C  \<circ>\<^sub>c c)"
        by blast
      then have ac_type: "\<langle>a, c\<rangle> \<in>\<^sub>c (A \<times>\<^sub>c C)"
        using a_def c_def by (typecheck_cfuncs, blast)
      obtain x where x_def: "x = ((right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>a, c\<rangle>)"
        by simp
      have x_type: "x \<in>\<^sub>c domain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C))"
        using ac_type cfunc_type_def codomain_comp domain_comp domain_is right_proj_type x_def by auto
      have y_def2: "y = \<langle>a,right_coproj B C \<circ>\<^sub>c c\<rangle>"
        by (simp add: c_def bc_def)
      have "y = (id(A) \<times>\<^sub>f (right_coproj B C)) \<circ>\<^sub>c \<langle>a,c\<rangle>"
        using a_def c_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 y_def2 by (typecheck_cfuncs, auto)
      also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, c\<rangle>"
        unfolding \<phi>_def using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
      also have "... = \<phi> \<circ>\<^sub>c x"
        using \<phi>_type x_def ac_type comp_associative2 by (typecheck_cfuncs, auto)
      then show "\<exists>x. x \<in>\<^sub>c domain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C)) \<and>
        (id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C) \<circ>\<^sub>c x = y"
        using \<phi>_def calculation x_type by auto
    qed
  qed
  then show "epimorphism (dist_prod_coprod A B C)"
    by (simp add: dist_prod_coprod_def surjective_is_epimorphism)
qed

lemma dist_prod_coprod_iso:
  "isomorphism(dist_prod_coprod A B C)"
  by (simp add: dist_prod_coprod_epi dist_prod_coprod_mono epi_mon_is_iso)

subsection  \<open>Inverse Distribute Product Over Coproduct Auxillary Mapping\<close>

definition dist_prod_coprod_inv :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "dist_prod_coprod_inv A B C = (THE f. f : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)
    \<and> f \<circ>\<^sub>c dist_prod_coprod A B C = id ((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))
    \<and> dist_prod_coprod A B C \<circ>\<^sub>c f = id (A \<times>\<^sub>c (B \<Coprod> C)))"

lemma dist_prod_coprod_inv_def2:
  shows "dist_prod_coprod_inv A B C : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)
    \<and> dist_prod_coprod_inv A B C \<circ>\<^sub>c dist_prod_coprod A B C = id ((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))
    \<and> dist_prod_coprod A B C \<circ>\<^sub>c dist_prod_coprod_inv A B C = id (A \<times>\<^sub>c (B \<Coprod> C))"
  unfolding dist_prod_coprod_inv_def
proof (rule theI', auto)
  show "\<exists>x. x : A \<times>\<^sub>c B \<Coprod> C \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C \<and>
        x \<circ>\<^sub>c dist_prod_coprod A B C = id\<^sub>c ((A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C) \<and>
        dist_prod_coprod A B C \<circ>\<^sub>c x = id\<^sub>c (A \<times>\<^sub>c B \<Coprod> C)"
    using dist_prod_coprod_iso[where A=A, where B=B, where C=C] unfolding isomorphism_def
    by (typecheck_cfuncs, auto simp add: cfunc_type_def)
  then obtain inv where inv_type: "inv : A \<times>\<^sub>c B \<Coprod> C \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C" and
        inv_left: "inv \<circ>\<^sub>c dist_prod_coprod A B C = id\<^sub>c ((A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C)" and
        inv_right: "dist_prod_coprod A B C \<circ>\<^sub>c inv = id\<^sub>c (A \<times>\<^sub>c B \<Coprod> C)"
    by auto

  fix x y
  assume x_type: "x : A \<times>\<^sub>c B \<Coprod> C \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C"
  assume y_type: "y : A \<times>\<^sub>c B \<Coprod> C \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C"

  assume "x \<circ>\<^sub>c dist_prod_coprod A B C = id\<^sub>c ((A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C)"
    and "y \<circ>\<^sub>c dist_prod_coprod A B C = id\<^sub>c ((A \<times>\<^sub>c B) \<Coprod> A \<times>\<^sub>c C)"
  then have "x \<circ>\<^sub>c dist_prod_coprod A B C = y \<circ>\<^sub>c dist_prod_coprod A B C"
    by auto
  then have "(x \<circ>\<^sub>c dist_prod_coprod A B C) \<circ>\<^sub>c inv = (y \<circ>\<^sub>c dist_prod_coprod A B C) \<circ>\<^sub>c inv"
    by auto
  then have "x \<circ>\<^sub>c dist_prod_coprod A B C \<circ>\<^sub>c inv = y \<circ>\<^sub>c dist_prod_coprod A B C \<circ>\<^sub>c inv"
    using inv_type x_type y_type by (typecheck_cfuncs, auto simp add: comp_associative2)
  then have "x \<circ>\<^sub>c id\<^sub>c (A \<times>\<^sub>c B \<Coprod> C) = y \<circ>\<^sub>c id\<^sub>c (A \<times>\<^sub>c B \<Coprod> C)"
    by (simp add: inv_right)
  then show "x = y"
    using id_right_unit2 x_type y_type by auto
qed

lemma dist_prod_coprod_inv_type[type_rule]:
  "dist_prod_coprod_inv A B C : A \<times>\<^sub>c (B \<Coprod> C) \<rightarrow> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
  by (simp add: dist_prod_coprod_inv_def2)

lemma dist_prod_coprod_inv_left:
  "dist_prod_coprod_inv A B C \<circ>\<^sub>c dist_prod_coprod A B C = id ((A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C))"
  by (simp add: dist_prod_coprod_inv_def2)

lemma dist_prod_coprod_inv_right:
  "dist_prod_coprod A B C \<circ>\<^sub>c dist_prod_coprod_inv A B C = id (A \<times>\<^sub>c (B \<Coprod> C))"
  by (simp add: dist_prod_coprod_inv_def2)

lemma dist_prod_coprod_inv_iso:
  "isomorphism(dist_prod_coprod_inv A B C)"
  by (metis dist_prod_coprod_inv_right dist_prod_coprod_inv_type dist_prod_coprod_iso dist_prod_coprod_type id_isomorphism id_right_unit2 id_type isomorphism_sandwich)

lemma dist_prod_coprod_inv_left_ap:
  assumes "a \<in>\<^sub>c A" "b \<in>\<^sub>c B"
  shows "dist_prod_coprod_inv A B C \<circ>\<^sub>c \<langle>a,left_coproj B C \<circ>\<^sub>c b\<rangle> = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a,b\<rangle>"
  using assms by (typecheck_cfuncs, smt comp_associative2 dist_prod_coprod_inv_def2 dist_prod_coprod_left_ap dist_prod_coprod_type id_left_unit2)

lemma dist_prod_coprod_inv_right_ap:
  assumes "a \<in>\<^sub>c A" "c \<in>\<^sub>c C"
  shows "dist_prod_coprod_inv A B C \<circ>\<^sub>c \<langle>a,right_coproj B C \<circ>\<^sub>c c\<rangle> = right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a,c\<rangle>"
  using assms by (typecheck_cfuncs, smt comp_associative2 dist_prod_coprod_inv_def2 dist_prod_coprod_right_ap dist_prod_coprod_type id_left_unit2)

subsection  \<open>Distribute Product Over Coproduct Auxillary Mapping 2\<close>
definition dist_prod_coprod2 :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "dist_prod_coprod2 A B C = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c (swap A C \<bowtie>\<^sub>f swap B C)"

lemma dist_prod_coprod2_type[type_rule]:
  "dist_prod_coprod2 A B C : (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C) \<rightarrow> (A \<Coprod> B) \<times>\<^sub>c C"
  unfolding dist_prod_coprod2_def by typecheck_cfuncs

lemma dist_prod_coprod2_left_ap:
  assumes "a \<in>\<^sub>c A" "c \<in>\<^sub>c C"
  shows "dist_prod_coprod2 A B C \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>) = \<langle>left_coproj A B \<circ>\<^sub>c a, c\<rangle>"
proof -
  have "dist_prod_coprod2 A B C \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)
    = (swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c (swap A C \<bowtie>\<^sub>f swap B C)) \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>)"
    unfolding dist_prod_coprod2_def by auto
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c ((swap A C \<bowtie>\<^sub>f swap B C) \<circ>\<^sub>c left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>a, c\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c (left_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c swap A C) \<circ>\<^sub>c \<langle>a, c\<rangle>"
    using assms by (typecheck_cfuncs, auto simp add: left_coproj_cfunc_bowtie_prod)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c left_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c swap A C \<circ>\<^sub>c \<langle>a, c\<rangle>"
    using assms by (typecheck_cfuncs, auto simp add: comp_associative2)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c left_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, a\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c \<langle>c, left_coproj A B \<circ>\<^sub>c a\<rangle>"
    using assms by (typecheck_cfuncs, simp add: dist_prod_coprod_left_ap)
  also have "... = \<langle>left_coproj A B \<circ>\<^sub>c a, c\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  then show ?thesis
    using calculation by auto
qed

lemma dist_prod_coprod2_right_ap:
  assumes "b \<in>\<^sub>c B" "c \<in>\<^sub>c C"
  shows "dist_prod_coprod2 A B C \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>) = \<langle>right_coproj A B \<circ>\<^sub>c b, c\<rangle>"
proof -
  have "dist_prod_coprod2 A B C \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>)
    = (swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c (swap A C \<bowtie>\<^sub>f swap B C)) \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>)"
    unfolding dist_prod_coprod2_def by auto
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c ((swap A C \<bowtie>\<^sub>f swap B C) \<circ>\<^sub>c right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C)) \<circ>\<^sub>c \<langle>b, c\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c (right_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c swap B C) \<circ>\<^sub>c \<langle>b, c\<rangle>"
    using assms by (typecheck_cfuncs, auto simp add: right_coproj_cfunc_bowtie_prod)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c right_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c swap B C \<circ>\<^sub>c \<langle>b, c\<rangle>"
    using assms by (typecheck_cfuncs, auto simp add: comp_associative2)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c dist_prod_coprod C A B \<circ>\<^sub>c right_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, b\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  also have "... = swap C (A \<Coprod> B) \<circ>\<^sub>c \<langle>c, right_coproj A B \<circ>\<^sub>c b\<rangle>"
    using assms by (typecheck_cfuncs, simp add: dist_prod_coprod_right_ap)
  also have "... = \<langle>right_coproj A B \<circ>\<^sub>c b, c\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  then show ?thesis
    using calculation by auto
qed

subsection  \<open>Inverse Distribute Product Over Coproduct Auxillary Mapping 2\<close>

definition dist_prod_coprod_inv2 :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "dist_prod_coprod_inv2 A B C = (swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c dist_prod_coprod_inv C A B \<circ>\<^sub>c swap (A \<Coprod> B) C"

lemma dist_prod_coprod_inv2_type[type_rule]:
  "dist_prod_coprod_inv2 A B C : (A \<Coprod> B) \<times>\<^sub>c C \<rightarrow> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
  unfolding dist_prod_coprod_inv2_def by typecheck_cfuncs

lemma dist_prod_coprod_inv2_left_ap:
  assumes "a \<in>\<^sub>c A" "c \<in>\<^sub>c C"
  shows "dist_prod_coprod_inv2 A B C \<circ>\<^sub>c \<langle>left_coproj A B \<circ>\<^sub>c a, c\<rangle> = left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>"
proof -
  have "dist_prod_coprod_inv2 A B C \<circ>\<^sub>c \<langle>left_coproj A B \<circ>\<^sub>c a, c\<rangle>
    = ((swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c dist_prod_coprod_inv C A B \<circ>\<^sub>c swap (A \<Coprod> B) C) \<circ>\<^sub>c \<langle>left_coproj A B \<circ>\<^sub>c a, c\<rangle>"
    unfolding dist_prod_coprod_inv2_def by auto
  also have "... = (swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c dist_prod_coprod_inv C A B \<circ>\<^sub>c swap (A \<Coprod> B) C \<circ>\<^sub>c \<langle>left_coproj A B \<circ>\<^sub>c a, c\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2)
  also have "... = (swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c dist_prod_coprod_inv C A B \<circ>\<^sub>c \<langle>c, left_coproj A B \<circ>\<^sub>c a\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  also have "... = (swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c left_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, a\<rangle>"
    using assms by (typecheck_cfuncs, simp add: dist_prod_coprod_inv_left_ap)
  also have "... = ((swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c left_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B)) \<circ>\<^sub>c \<langle>c, a\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2)
  also have "... = (left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c swap C A) \<circ>\<^sub>c \<langle>c, a\<rangle>"
    using assms left_coproj_cfunc_bowtie_prod by (typecheck_cfuncs, auto)
  also have "... = left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c swap C A \<circ>\<^sub>c \<langle>c, a\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2)
  also have "... = left_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>a, c\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  then show ?thesis
    using calculation by auto
qed

lemma dist_prod_coprod_inv2_right_ap:
  assumes "b \<in>\<^sub>c B" "c \<in>\<^sub>c C"
  shows "dist_prod_coprod_inv2 A B C \<circ>\<^sub>c \<langle>right_coproj A B \<circ>\<^sub>c b, c\<rangle> = right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>"
proof -
  have "dist_prod_coprod_inv2 A B C \<circ>\<^sub>c \<langle>right_coproj A B \<circ>\<^sub>c b, c\<rangle>
    = ((swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c dist_prod_coprod_inv C A B \<circ>\<^sub>c swap (A \<Coprod> B) C) \<circ>\<^sub>c \<langle>right_coproj A B \<circ>\<^sub>c b, c\<rangle>"
    unfolding dist_prod_coprod_inv2_def by auto
  also have "... = (swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c dist_prod_coprod_inv C A B \<circ>\<^sub>c swap (A \<Coprod> B) C \<circ>\<^sub>c \<langle>right_coproj A B \<circ>\<^sub>c b, c\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2)
  also have "... = (swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c dist_prod_coprod_inv C A B \<circ>\<^sub>c \<langle>c, right_coproj A B \<circ>\<^sub>c b\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  also have "... = (swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c right_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B) \<circ>\<^sub>c \<langle>c, b\<rangle>"
    using assms by (typecheck_cfuncs, simp add: dist_prod_coprod_inv_right_ap)
  also have "... = ((swap C A \<bowtie>\<^sub>f swap C B) \<circ>\<^sub>c right_coproj (C \<times>\<^sub>c A) (C \<times>\<^sub>c B)) \<circ>\<^sub>c \<langle>c, b\<rangle>"
    using assms by (typecheck_cfuncs, auto simp add: comp_associative2)
  also have "... = (right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c swap C B) \<circ>\<^sub>c \<langle>c, b\<rangle>"
    using assms by (typecheck_cfuncs, auto simp add: right_coproj_cfunc_bowtie_prod)
  also have "... = right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c swap C B \<circ>\<^sub>c \<langle>c, b\<rangle>"
    using assms by (typecheck_cfuncs, auto simp add: comp_associative2)
  also have "... = right_coproj (A \<times>\<^sub>c C) (B \<times>\<^sub>c C) \<circ>\<^sub>c \<langle>b, c\<rangle>"
    using assms swap_ap by (typecheck_cfuncs, auto)
  then show ?thesis
    using calculation by auto
qed

lemma dist_prod_coprod_inv2_left_coproj:
  "dist_prod_coprod_inv2 X Y H \<circ>\<^sub>c (left_coproj X Y \<times>\<^sub>f id H) = left_coproj (X \<times>\<^sub>c H) (Y \<times>\<^sub>c H)"
  by (typecheck_cfuncs, smt (z3) one_separator cart_prod_decomp cfunc_cross_prod_comp_cfunc_prod comp_associative2 dist_prod_coprod_inv2_left_ap id_left_unit2)

lemma dist_prod_coprod_inv2_right_coproj:
  "dist_prod_coprod_inv2 X Y H \<circ>\<^sub>c (right_coproj X Y \<times>\<^sub>f id H) = right_coproj (X \<times>\<^sub>c H) (Y \<times>\<^sub>c H)"
  by (typecheck_cfuncs, smt (z3) one_separator cart_prod_decomp cfunc_cross_prod_comp_cfunc_prod comp_associative2 dist_prod_coprod_inv2_right_ap id_left_unit2)

lemma dist_prod_coprod2_inv2_id:
"dist_prod_coprod2 A B C \<circ>\<^sub>c dist_prod_coprod_inv2 A B C = id ((A \<Coprod> B) \<times>\<^sub>c C)"
  unfolding dist_prod_coprod2_def dist_prod_coprod_inv2_def by(-,typecheck_cfuncs,
  smt (z3) cfunc_bowtie_prod_comp_cfunc_bowtie_prod comp_associative2 dist_prod_coprod_inv_right id_bowtie_prod id_right_unit2 swap_idempotent)
   
lemma dist_prod_coprod_inv2_inv_id:
"dist_prod_coprod_inv2 A B C \<circ>\<^sub>c dist_prod_coprod2 A B C = id ((A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C))"
  unfolding dist_prod_coprod2_def dist_prod_coprod_inv2_def by(-,typecheck_cfuncs,
  smt (z3) cfunc_bowtie_prod_comp_cfunc_bowtie_prod comp_associative2 dist_prod_coprod_inv_left id_bowtie_prod id_right_unit2 swap_idempotent)


lemma dist_prod_coprod2_iso:
  "isomorphism(dist_prod_coprod2 A B C)"
  by (metis cfunc_type_def dist_prod_coprod2_inv2_id dist_prod_coprod2_type dist_prod_coprod_inv2_inv_id dist_prod_coprod_inv2_type isomorphism_def)

subsection  \<open>Into Super or Proposition 2.4.5\<close>
(*This entire section IS Proposition 2.4.5*)
definition into_super :: "cfunc \<Rightarrow> cfunc" where
  "into_super m = m \<amalg> m\<^sup>c"

lemma into_super_type[type_rule]:
  "monomorphism m \<Longrightarrow> m : X \<rightarrow> Y \<Longrightarrow> into_super m : X \<Coprod> (Y \<setminus> (X,m)) \<rightarrow> Y"
  unfolding into_super_def by typecheck_cfuncs

lemma into_super_mono:
  assumes "monomorphism m" "m : X \<rightarrow> Y"
  shows "monomorphism (into_super m)"
proof (rule injective_imp_monomorphism, unfold injective_def, auto)
  fix x y
  assume "x \<in>\<^sub>c domain (into_super m)"  then have x_type: "x \<in>\<^sub>c X \<Coprod> (Y \<setminus> (X,m))"
    using assms cfunc_type_def into_super_type by auto
  
  assume "y \<in>\<^sub>c domain (into_super m)"  then have y_type: "y \<in>\<^sub>c X \<Coprod> (Y \<setminus> (X,m))"
    using assms cfunc_type_def into_super_type by auto

  assume into_super_eq: "into_super m \<circ>\<^sub>c x = into_super m \<circ>\<^sub>c y"

  have x_cases: "(\<exists> x'. (x' \<in>\<^sub>c X \<and> x = (left_coproj X (Y \<setminus> (X,m))) \<circ>\<^sub>c x'))
    \<or>  (\<exists> x'. (x' \<in>\<^sub>c Y \<setminus> (X,m) \<and> x = (right_coproj X (Y \<setminus> (X,m))) \<circ>\<^sub>c x'))"
    by (simp add: coprojs_jointly_surj x_type)

  have y_cases: "(\<exists> y'. (y' \<in>\<^sub>c X \<and> y = (left_coproj X (Y \<setminus> (X,m))) \<circ>\<^sub>c y'))
    \<or>  (\<exists> y'. (y' \<in>\<^sub>c Y \<setminus> (X,m) \<and> y = (right_coproj X (Y \<setminus> (X,m))) \<circ>\<^sub>c y'))"
    by (simp add: coprojs_jointly_surj y_type)

  show "x = y"
    using x_cases y_cases
  proof auto
    fix x' y'
    assume x'_type: "x' \<in>\<^sub>c X" and x_def: "x = left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x'"
    assume y'_type: "y' \<in>\<^sub>c X" and y_def: "y = left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"

    have "into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      using into_super_eq unfolding x_def y_def by auto
    then have "(into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c x' = (into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c y'"
      using assms x'_type y'_type comp_associative2 by (typecheck_cfuncs, auto)
    then have "m \<circ>\<^sub>c x' = m \<circ>\<^sub>c y'"
      using assms unfolding into_super_def
      by (simp add: complement_morphism_type left_coproj_cfunc_coprod)
    then have "x' = y'"
      using assms cfunc_type_def monomorphism_def x'_type y'_type by auto
    then show "left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      by simp
  next
    fix x' y'
    assume x'_type: "x' \<in>\<^sub>c X" and x_def: "x = left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x'"
    assume y'_type: "y' \<in>\<^sub>c Y \<setminus> (X, m)" and y_def: "y = right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"

    have "into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      using into_super_eq unfolding x_def y_def by auto
    then have "(into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c x' = (into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c y'"
      using assms x'_type y'_type comp_associative2 by (typecheck_cfuncs, auto)
    then have "m \<circ>\<^sub>c x' = m\<^sup>c \<circ>\<^sub>c y'"
      using assms unfolding into_super_def
      by (simp add: complement_morphism_type left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    then have False
      using assms(1) assms(2) complement_disjoint x'_type y'_type by blast
    then show "left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      by auto
  next
    fix x' y'
    assume x'_type: "x' \<in>\<^sub>c Y \<setminus> (X, m)" and x_def: "x = right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x'"
    assume y'_type: "y' \<in>\<^sub>c X" and y_def: "y = left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"

    have "into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      using into_super_eq unfolding x_def y_def by auto
    then have "(into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c x' = (into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c y'"
      using assms x'_type y'_type comp_associative2 by (typecheck_cfuncs, auto)
    then have "m\<^sup>c \<circ>\<^sub>c x' = m \<circ>\<^sub>c y'"
      using assms unfolding into_super_def
      by (simp add: complement_morphism_type left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    then have False
      using assms(1) assms(2) complement_disjoint x'_type y'_type by fastforce
    then show "right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      by auto
  next
    fix x' y'
    assume x'_type: "x' \<in>\<^sub>c Y \<setminus> (X, m)" and x_def: "x = right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x'"
    assume y'_type: "y' \<in>\<^sub>c Y \<setminus> (X, m)" and y_def: "y = right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"

    have "into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      using into_super_eq unfolding x_def y_def by auto
    then have "(into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c x' = (into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X, m))) \<circ>\<^sub>c y'"
      using assms x'_type y'_type comp_associative2 by (typecheck_cfuncs, auto)
    then have "m\<^sup>c \<circ>\<^sub>c x' = m\<^sup>c \<circ>\<^sub>c y'"
      using assms unfolding into_super_def
      by (simp add: complement_morphism_type right_coproj_cfunc_coprod)
    then have "x' = y'"
      using assms complement_morphism_mono complement_morphism_type monomorphism_def2 x'_type y'_type by blast
    then show "right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x' = right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c y'"
      by simp
  qed
qed

lemma into_super_epi:
  assumes "monomorphism m" "m : X \<rightarrow> Y"
  shows "epimorphism (into_super m)"
proof (rule surjective_is_epimorphism, unfold surjective_def, auto)
  fix y
  assume "y \<in>\<^sub>c codomain (into_super m)"
  then have y_type: "y \<in>\<^sub>c Y"
    using assms cfunc_type_def into_super_type by auto

  have y_cases: "(characteristic_func m \<circ>\<^sub>c y = \<t>) \<or> (characteristic_func m \<circ>\<^sub>c y = \<f>)"
    using y_type assms true_false_only_truth_values by (typecheck_cfuncs, blast)
  then show "\<exists>x. x \<in>\<^sub>c domain (into_super m) \<and> into_super m \<circ>\<^sub>c x = y"
  proof auto
    assume "characteristic_func m \<circ>\<^sub>c y = \<t>"
    then have "y \<in>\<^bsub>Y\<^esub> (X, m)"
      by (simp add: assms characteristic_func_true_relative_member y_type)
    then obtain x where x_type: "x \<in>\<^sub>c X" and x_def: "y = m \<circ>\<^sub>c x"
      by (unfold relative_member_def2, auto, unfold factors_through_def2, auto)
    then show "\<exists>x. x \<in>\<^sub>c domain (into_super m) \<and> into_super m \<circ>\<^sub>c x = y"
      unfolding into_super_def using assms cfunc_type_def comp_associative left_coproj_cfunc_coprod
      by (rule_tac x="left_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x" in exI, typecheck_cfuncs, metis)
  next
    assume "characteristic_func m \<circ>\<^sub>c y = \<f>"
    then have "\<not> y \<in>\<^bsub>Y\<^esub> (X, m)"
      by (simp add: assms characteristic_func_false_not_relative_member y_type)
    then have "y \<in>\<^bsub>Y\<^esub> (Y \<setminus> (X, m), m\<^sup>c)"
      by (simp add: assms not_in_subset_in_complement y_type)
    then obtain x' where x'_type: "x' \<in>\<^sub>c Y \<setminus> (X, m)" and x'_def: "y = m\<^sup>c \<circ>\<^sub>c x'"
      by (unfold relative_member_def2, auto, unfold factors_through_def2, auto)
    then show "\<exists>x. x \<in>\<^sub>c domain (into_super m) \<and> into_super m \<circ>\<^sub>c x = y"
      unfolding into_super_def using assms cfunc_type_def comp_associative right_coproj_cfunc_coprod
      by (rule_tac x="right_coproj X (Y \<setminus> (X, m)) \<circ>\<^sub>c x'" in exI, typecheck_cfuncs, metis)
  qed
qed

lemma into_super_iso:
  assumes "monomorphism m" "m : X \<rightarrow> Y"
  shows "isomorphism (into_super m)"
  using assms epi_mon_is_iso into_super_epi into_super_mono by auto

subsection  \<open>Try Cast\<close>

definition try_cast :: "cfunc \<Rightarrow> cfunc" where
  "try_cast m = (THE m'. m' : (codomain m) \<rightarrow> (domain m) \<Coprod> ((codomain m) \<setminus> ((domain m),m))
    \<and> m' \<circ>\<^sub>c into_super m = id ((domain m) \<Coprod> ((codomain m) \<setminus> ((domain m),m)))
    \<and> into_super m \<circ>\<^sub>c m' = id (codomain m))"

lemma try_cast_def2:
  assumes "monomorphism m" "m : X \<rightarrow> Y"
  shows "try_cast m : (codomain m) \<rightarrow> (domain m) \<Coprod> ((codomain m) \<setminus> ((domain m),m))
    \<and> try_cast m \<circ>\<^sub>c into_super m = id ((domain m) \<Coprod> ((codomain m) \<setminus> ((domain m),m)))
    \<and> into_super m \<circ>\<^sub>c try_cast m = id (codomain m)"
  unfolding try_cast_def
proof (rule theI', auto)
  show "\<exists>x. x : codomain m \<rightarrow> domain m \<Coprod> (codomain m \<setminus> (domain m, m)) \<and>
        x \<circ>\<^sub>c into_super m = id\<^sub>c (domain m \<Coprod> (codomain m \<setminus> (domain m, m))) \<and>
        into_super m \<circ>\<^sub>c x = id\<^sub>c (codomain m)"
    using assms into_super_iso cfunc_type_def into_super_type unfolding isomorphism_def by fastforce
next
  fix x y
  assume x_type: "x : codomain m \<rightarrow> domain m \<Coprod> (codomain m \<setminus> (domain m, m))"
  assume y_type: "y : codomain m \<rightarrow> domain m \<Coprod> (codomain m \<setminus> (domain m, m))"
  assume "into_super m \<circ>\<^sub>c x = id\<^sub>c (codomain m)" and "into_super m \<circ>\<^sub>c y = id\<^sub>c (codomain m)"
  then have "into_super m \<circ>\<^sub>c x = into_super m \<circ>\<^sub>c y"
    by auto
  then show "x = y"
    using into_super_mono unfolding monomorphism_def
    by (metis assms(1) cfunc_type_def into_super_type monomorphism_def x_type y_type)
qed

lemma try_cast_type[type_rule]:
  assumes "monomorphism m" "m : X \<rightarrow> Y"
  shows "try_cast m : Y \<rightarrow> X \<Coprod> (Y \<setminus> (X,m))"
  using assms cfunc_type_def try_cast_def2 by auto 

lemma try_cast_into_super:
  assumes "monomorphism m" "m : X \<rightarrow> Y"
  shows "try_cast m \<circ>\<^sub>c into_super m = id (X \<Coprod> (Y \<setminus> (X,m)))"
  using assms cfunc_type_def try_cast_def2 by auto

lemma into_super_try_cast:
  assumes "monomorphism m" "m : X \<rightarrow> Y"
  shows "into_super m \<circ>\<^sub>c  try_cast m = id Y"
  using assms cfunc_type_def try_cast_def2 by auto

lemma try_cast_in_X:
  assumes m_type: "monomorphism m" "m : X \<rightarrow> Y"
  assumes y_in_X: "y \<in>\<^bsub>Y\<^esub> (X, m)"
  shows "\<exists> x. x \<in>\<^sub>c X \<and> try_cast m \<circ>\<^sub>c y = left_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
proof -
  have y_type: "y \<in>\<^sub>c Y"
    using y_in_X unfolding relative_member_def2 by auto
  obtain x where x_type: "x \<in>\<^sub>c X" and x_def: "y = m \<circ>\<^sub>c x"
    using y_in_X unfolding relative_member_def2 factors_through_def by (auto simp add: cfunc_type_def)
  then have "y = (into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X,m))) \<circ>\<^sub>c x"
    unfolding into_super_def using complement_morphism_type left_coproj_cfunc_coprod m_type by auto
  then have "y = into_super m \<circ>\<^sub>c left_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
    using x_type m_type by (typecheck_cfuncs, simp add:  comp_associative2)
  then have "try_cast m \<circ>\<^sub>c y = (try_cast m \<circ>\<^sub>c into_super m) \<circ>\<^sub>c left_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
    using x_type m_type by (typecheck_cfuncs, smt comp_associative2)
  then have "try_cast m \<circ>\<^sub>c y = left_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
    using m_type x_type by (typecheck_cfuncs, simp add: id_left_unit2 try_cast_into_super)
  then show ?thesis
    using x_type by blast
qed

lemma try_cast_not_in_X:
  assumes m_type: "monomorphism m" "m : X \<rightarrow> Y"
  assumes y_in_X: "\<not> y \<in>\<^bsub>Y\<^esub> (X, m)" and y_type: "y \<in>\<^sub>c Y"  
  shows "\<exists> x. x \<in>\<^sub>c Y \<setminus> (X,m) \<and> try_cast m \<circ>\<^sub>c y = right_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
proof -
  have y_in_complement: "y \<in>\<^bsub>Y\<^esub> (Y \<setminus> (X,m), m\<^sup>c)"
    by (simp add: assms not_in_subset_in_complement)
  then obtain x where x_type: "x \<in>\<^sub>c Y \<setminus> (X,m)" and x_def: "y = m\<^sup>c \<circ>\<^sub>c x"
    unfolding relative_member_def2 factors_through_def by (auto simp add: cfunc_type_def)
  then have "y = (into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X,m))) \<circ>\<^sub>c x"
    unfolding into_super_def using complement_morphism_type m_type right_coproj_cfunc_coprod by auto 
  then have "y = into_super m \<circ>\<^sub>c right_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
    using x_type m_type by (typecheck_cfuncs, simp add:  comp_associative2)
  then have "try_cast m \<circ>\<^sub>c y = (try_cast m \<circ>\<^sub>c into_super m) \<circ>\<^sub>c right_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
    using x_type m_type by (typecheck_cfuncs, smt comp_associative2)
  then have "try_cast m \<circ>\<^sub>c y = right_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x"
    using m_type x_type by (typecheck_cfuncs, simp add: id_left_unit2 try_cast_into_super)
  then show ?thesis
    using x_type by blast
qed

lemma try_cast_m_m:
  assumes m_type: "monomorphism m" "m : X \<rightarrow> Y"
  shows "(try_cast m) \<circ>\<^sub>c m = left_coproj X (Y \<setminus> (X,m))"
  by (smt comp_associative2 complement_morphism_type id_left_unit2 into_super_def into_super_type left_coproj_cfunc_coprod left_proj_type m_type try_cast_into_super try_cast_type)

lemma try_cast_m_m':
  assumes m_type: "monomorphism m" "m : X \<rightarrow> Y"
  shows "(try_cast m) \<circ>\<^sub>c m\<^sup>c = right_coproj X (Y \<setminus> (X,m))"
  by (smt comp_associative2 complement_morphism_type id_left_unit2 into_super_def into_super_type m_type(1) m_type(2) right_coproj_cfunc_coprod right_proj_type try_cast_into_super try_cast_type)

lemma try_cast_mono:
  assumes m_type: "monomorphism m" "m : X \<rightarrow> Y"
  shows "monomorphism(try_cast m)"
  by (smt cfunc_type_def comp_monic_imp_monic' id_isomorphism into_super_type iso_imp_epi_and_monic try_cast_def2 assms)  

subsection  \<open>Coproduct Set Properities\<close>

(* Coproduct commutes *)
lemma coproduct_commutes:
  "A \<Coprod> B \<cong> B \<Coprod> A"
proof -
  have id_AB: "((right_coproj A B)  \<amalg> (left_coproj A B)) \<circ>\<^sub>c ((right_coproj B A) \<amalg> (left_coproj B A)) = id(A \<Coprod> B)"
    by (typecheck_cfuncs, smt (z3) cfunc_coprod_comp id_coprod left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
  have id_BA: " ((right_coproj B A) \<amalg> (left_coproj B A)) \<circ>\<^sub>c ((right_coproj A B)  \<amalg> (left_coproj A B)) = id(B \<Coprod> A)"
    by (typecheck_cfuncs, smt (z3) cfunc_coprod_comp id_coprod right_coproj_cfunc_coprod left_coproj_cfunc_coprod)
  show "A \<Coprod> B \<cong> B \<Coprod> A"
    by (smt (verit, ccfv_threshold) cfunc_coprod_type cfunc_type_def id_AB id_BA is_isomorphic_def isomorphism_def left_proj_type right_proj_type)
qed

(* Coproduct associates *)
lemma coproduct_associates:
  "A \<Coprod> (B \<Coprod> C)  \<cong> (A \<Coprod> B) \<Coprod> C"
proof -

(*Diagram 1*)
  obtain q where q_def: "q = (left_coproj (A \<Coprod> B) C ) \<circ>\<^sub>c (right_coproj A B)" and q_type[type_rule]: "q: B \<rightarrow> (A \<Coprod> B) \<Coprod> C"
    by typecheck_cfuncs  
  obtain f where f_def: "f = q \<amalg> (right_coproj (A \<Coprod> B) C)" and f_type[type_rule]: "(f: (B \<Coprod> C) \<rightarrow> ((A \<Coprod> B) \<Coprod> C))"
    by typecheck_cfuncs
  have f_prop: "(f \<circ>\<^sub>c left_coproj B C = q) \<and> (f \<circ>\<^sub>c right_coproj B C = right_coproj (A \<Coprod> B) C)"
    by (typecheck_cfuncs, simp add: f_def left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
  then have f_unique: "(\<exists>!f. (f: (B \<Coprod> C) \<rightarrow> ((A \<Coprod> B) \<Coprod> C)) \<and> (f \<circ>\<^sub>c left_coproj B C = q) \<and> (f \<circ>\<^sub>c right_coproj B C = right_coproj (A \<Coprod> B) C))"
    by (typecheck_cfuncs, metis cfunc_coprod_unique f_prop f_type)


(*Diagram 2*)
  obtain m where m_def: "m = (left_coproj (A \<Coprod> B) C ) \<circ>\<^sub>c (left_coproj A B)" and m_type[type_rule]: "m : A \<rightarrow> (A \<Coprod> B) \<Coprod> C"
    by typecheck_cfuncs
  obtain g where g_def: "g = m \<amalg> f" and g_type[type_rule]: "g: A \<Coprod> (B \<Coprod> C)  \<rightarrow> (A \<Coprod> B) \<Coprod> C"
    by typecheck_cfuncs
  have g_prop: "(g \<circ>\<^sub>c (left_coproj A (B \<Coprod> C)) = m) \<and> (g \<circ>\<^sub>c (right_coproj A (B \<Coprod> C)) = f)"
    by (typecheck_cfuncs, simp add: g_def left_coproj_cfunc_coprod right_coproj_cfunc_coprod) 
  have g_unique: "\<exists>! g. ((g: A \<Coprod> (B \<Coprod> C)  \<rightarrow> (A \<Coprod> B) \<Coprod> C) \<and> (g \<circ>\<^sub>c (left_coproj A (B \<Coprod> C)) = m) \<and> (g \<circ>\<^sub>c (right_coproj A (B \<Coprod> C)) = f))"
    by (typecheck_cfuncs, metis cfunc_coprod_unique g_prop g_type)

(*Diagram 3*)
  obtain p where p_def: "p = (right_coproj A (B \<Coprod> C)) \<circ>\<^sub>c  (left_coproj B C)" and p_type[type_rule]: "p: B \<rightarrow> A \<Coprod> (B \<Coprod> C)"
    by typecheck_cfuncs
  obtain h where h_def: "h = (left_coproj A (B \<Coprod> C)) \<amalg> p" and h_type[type_rule]: "h: (A \<Coprod> B) \<rightarrow> A \<Coprod> (B \<Coprod> C)"
    by typecheck_cfuncs
  have h_prop1: "h \<circ>\<^sub>c (left_coproj A B)  = (left_coproj A (B \<Coprod> C))"
    by (typecheck_cfuncs, simp add: h_def left_coproj_cfunc_coprod p_type)
  have h_prop2: "h \<circ>\<^sub>c (right_coproj A B) = p"
    using h_def left_proj_type right_coproj_cfunc_coprod by (typecheck_cfuncs, blast)
  have h_unique: "\<exists>! h. ((h: (A \<Coprod> B) \<rightarrow> A \<Coprod> (B \<Coprod> C)) \<and> (h \<circ>\<^sub>c (left_coproj A B)  = (left_coproj A (B \<Coprod> C))) \<and> (h \<circ>\<^sub>c (right_coproj A B) =p))"
    by (typecheck_cfuncs, metis cfunc_coprod_unique h_prop1 h_prop2 h_type)

(*Diagram 4*)
  obtain j where j_def: "j = (right_coproj A (B \<Coprod> C)) \<circ>\<^sub>c  (right_coproj B C)" and j_type[type_rule]: "j : C \<rightarrow> A \<Coprod> (B \<Coprod> C)"
    by typecheck_cfuncs
  obtain k where k_def: "k = h \<amalg> j" and k_type[type_rule]: "k: (A \<Coprod> B) \<Coprod> C \<rightarrow> A \<Coprod> (B \<Coprod> C)"
    by typecheck_cfuncs

(*Master diagram*)
  have fact1: "(k \<circ>\<^sub>c g) \<circ>\<^sub>c (left_coproj A (B \<Coprod> C)) = (left_coproj A (B \<Coprod> C))"
    by (typecheck_cfuncs, smt (z3) comp_associative2 g_prop h_prop1 h_type j_type k_def left_coproj_cfunc_coprod left_proj_type m_def)
  have fact2: "(g \<circ>\<^sub>c k) \<circ>\<^sub>c (left_coproj (A \<Coprod> B) C) = (left_coproj (A \<Coprod> B) C)"
    by (typecheck_cfuncs, smt (verit) cfunc_coprod_comp cfunc_coprod_unique comp_associative2 comp_type f_prop g_prop g_type h_def h_type j_def k_def k_type left_coproj_cfunc_coprod left_proj_type m_def p_def p_type q_def right_proj_type)
  have fact3: "(g \<circ>\<^sub>c k) \<circ>\<^sub>c (right_coproj (A \<Coprod> B) C) = (right_coproj (A \<Coprod> B) C)"
    by (smt comp_associative2 comp_type f_def g_prop g_type h_type j_def k_def k_type q_type right_coproj_cfunc_coprod right_proj_type)
  have fact4: "(k \<circ>\<^sub>c g) \<circ>\<^sub>c (right_coproj A (B \<Coprod> C)) = (right_coproj A (B \<Coprod> C))"
    by (typecheck_cfuncs, smt (verit, ccfv_threshold) cfunc_coprod_unique cfunc_type_def comp_associative comp_type f_prop g_prop h_prop2 h_type j_def k_def left_coproj_cfunc_coprod left_proj_type p_def q_def right_coproj_cfunc_coprod right_proj_type)
  have fact5: "(k \<circ>\<^sub>c g) = id( A \<Coprod> (B \<Coprod> C))"
    by (typecheck_cfuncs, metis cfunc_coprod_unique fact1 fact4 id_coprod left_proj_type right_proj_type)
  have fact6: "(g \<circ>\<^sub>c k) = id((A \<Coprod> B) \<Coprod> C)"
    by (typecheck_cfuncs, metis cfunc_coprod_unique fact2 fact3 id_coprod left_proj_type right_proj_type)
  show ?thesis
    by (metis cfunc_type_def fact5 fact6 g_type is_isomorphic_def isomorphism_def k_type)
qed


(* Proposition 2.5.10 *)
lemma product_distribute_over_coproduct_left:
  "A \<times>\<^sub>c (X \<Coprod> Y) \<cong> (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y)"
  using dist_prod_coprod_type dist_prod_coprod_iso is_isomorphic_def isomorphic_is_symmetric by blast

lemma prod_pres_iso:
  assumes "A \<cong>  C"  "B \<cong> D"
  shows "A \<times>\<^sub>c B \<cong>  C \<times>\<^sub>c D"
proof - 
  obtain f where f_def: "f: A \<rightarrow> C \<and> isomorphism(f)"
    using assms(1) is_isomorphic_def by blast
  obtain g where g_def: "g: B \<rightarrow> D \<and> isomorphism(g)"
    using assms(2) is_isomorphic_def by blast
  have "isomorphism(f\<times>\<^sub>fg)"
    by (meson cfunc_cross_prod_mono cfunc_cross_prod_surj epi_is_surj epi_mon_is_iso f_def g_def iso_imp_epi_and_monic surjective_is_epimorphism)
  then show "A \<times>\<^sub>c B \<cong>  C \<times>\<^sub>c D"
    by (meson cfunc_cross_prod_type f_def g_def is_isomorphic_def)
qed

lemma coprod_pres_iso:
  assumes "A \<cong>  C"  "B \<cong> D"
  shows "A \<Coprod> B \<cong>  C \<Coprod> D"
proof- 
  obtain f where f_def: "f: A \<rightarrow> C" "isomorphism(f)"
    using assms(1) is_isomorphic_def by blast
  obtain g where g_def: "g: B \<rightarrow> D" "isomorphism(g)"
    using assms(2) is_isomorphic_def by blast

  have surj_f: "surjective(f)"
    using epi_is_surj f_def iso_imp_epi_and_monic by blast
  have surj_g: "surjective(g)"
    using epi_is_surj g_def iso_imp_epi_and_monic by blast

  have coproj_f_inject: "injective(((left_coproj C D) \<circ>\<^sub>c f))"
    using cfunc_type_def composition_of_monic_pair_is_monic f_def iso_imp_epi_and_monic left_coproj_are_monomorphisms left_proj_type monomorphism_imp_injective by auto
    
  have coproj_g_inject: "injective(((right_coproj C D) \<circ>\<^sub>c g))"
    using cfunc_type_def composition_of_monic_pair_is_monic g_def iso_imp_epi_and_monic right_coproj_are_monomorphisms right_proj_type monomorphism_imp_injective by auto

  obtain \<phi> where \<phi>_def: "\<phi> = (left_coproj C D \<circ>\<^sub>c f)  \<amalg> (right_coproj C D \<circ>\<^sub>c g)"
    by simp
  then have \<phi>_type: "\<phi>: A \<Coprod> B \<rightarrow>  C \<Coprod> D"
    using cfunc_coprod_type cfunc_type_def codomain_comp domain_comp f_def g_def left_proj_type right_proj_type by auto

  have "surjective(\<phi>)"
    unfolding surjective_def
  proof(auto) 
    fix y 
    assume y_type: "y \<in>\<^sub>c codomain \<phi>"
    then have y_type2: "y \<in>\<^sub>c C \<Coprod> D"
      using \<phi>_type cfunc_type_def by auto
    then have y_form: "(\<exists> c. (c \<in>\<^sub>c C \<and> y = (left_coproj C D) \<circ>\<^sub>c c))
      \<or>  (\<exists> d. (d \<in>\<^sub>c D \<and> y = (right_coproj C D) \<circ>\<^sub>c d))"
      using coprojs_jointly_surj by auto
    show "\<exists>x. x \<in>\<^sub>c domain \<phi> \<and> \<phi> \<circ>\<^sub>c x = y"
    proof(cases "(\<exists> c. (c \<in>\<^sub>c C \<and> y = (left_coproj C D) \<circ>\<^sub>c c))")
      assume "(\<exists> c. (c \<in>\<^sub>c C \<and> y = (left_coproj C D) \<circ>\<^sub>c c))"
      then obtain c where c_def: "(c \<in>\<^sub>c C \<and> y = (left_coproj C D) \<circ>\<^sub>c c)"
        by blast
      then have "\<exists> a. a \<in>\<^sub>c A \<and> f \<circ>\<^sub>c a = c"
        using cfunc_type_def f_def surj_f surjective_def by auto
      then obtain a where a_def: "a \<in>\<^sub>c A \<and> f \<circ>\<^sub>c a = c"
        by blast
      obtain x where x_def: "x = (left_coproj A B) \<circ>\<^sub>c a"
        by blast
      have x_type: "x \<in>\<^sub>c A \<Coprod> B"
        using a_def comp_type left_proj_type x_def by blast
      have "\<phi> \<circ>\<^sub>c x = y"
        using \<phi>_def \<phi>_type a_def c_def cfunc_type_def comp_associative comp_type f_def g_def left_coproj_cfunc_coprod left_proj_type right_proj_type x_def by (smt (verit))
      then show "\<exists>x. x \<in>\<^sub>c domain \<phi> \<and> \<phi> \<circ>\<^sub>c x = y"
        using \<phi>_type cfunc_type_def x_type by auto
    next
      assume "\<nexists>c. c \<in>\<^sub>c C \<and> y = left_coproj C D \<circ>\<^sub>c c"
      then have y_def2: "(\<exists> d. (d \<in>\<^sub>c D \<and> y = (right_coproj C D) \<circ>\<^sub>c d))"
        using y_form by blast
      then obtain d where d_def: "d \<in>\<^sub>c D" "y = (right_coproj C D) \<circ>\<^sub>c d"
        by blast
      then have "\<exists> b. b \<in>\<^sub>c B \<and> g \<circ>\<^sub>c b = d"
        using cfunc_type_def g_def surj_g surjective_def by auto
      then obtain b where b_def: "b \<in>\<^sub>c B" "g \<circ>\<^sub>c b = d"
        by blast
      obtain x where x_def: "x = (right_coproj A B) \<circ>\<^sub>c b"
        by blast
      have x_type: "x \<in>\<^sub>c A \<Coprod> B"
        using b_def comp_type right_proj_type x_def by blast
      have "\<phi> \<circ>\<^sub>c x = y"
        using \<phi>_def \<phi>_type b_def cfunc_type_def comp_associative comp_type d_def f_def g_def left_proj_type right_coproj_cfunc_coprod right_proj_type x_def by (smt (verit))
      then show "\<exists>x. x \<in>\<^sub>c domain \<phi> \<and> \<phi> \<circ>\<^sub>c x = y"
        using \<phi>_type cfunc_type_def x_type by auto
    qed
  qed


  have "injective(\<phi>)"
    unfolding injective_def
  proof(auto)
    fix x y   
    assume x_type: "x \<in>\<^sub>c domain \<phi>"
    assume y_type: "y \<in>\<^sub>c domain \<phi>"
    assume equals: "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c y"
    have x_type2: "x \<in>\<^sub>c A \<Coprod> B"
      using \<phi>_type cfunc_type_def x_type by auto
    have y_type2: "y \<in>\<^sub>c A \<Coprod> B"
      using \<phi>_type cfunc_type_def y_type by auto

    have phix_type: "\<phi> \<circ>\<^sub>c x \<in>\<^sub>c C \<Coprod> D"
      using \<phi>_type comp_type x_type2 by blast
    have phiy_type: "\<phi> \<circ>\<^sub>c y \<in>\<^sub>c C \<Coprod> D"
      using equals phix_type by auto

    have x_form: "(\<exists> a. (a \<in>\<^sub>c A  \<and> x = (left_coproj A B) \<circ>\<^sub>c a))
      \<or>  (\<exists> b. (b \<in>\<^sub>c B \<and> x = (right_coproj A B) \<circ>\<^sub>c b))"
      using cfunc_type_def coprojs_jointly_surj x_type x_type2 y_type by auto
    
    have y_form: "(\<exists> a. (a \<in>\<^sub>c A  \<and> y = (left_coproj A B) \<circ>\<^sub>c a))
      \<or>  (\<exists> b. (b \<in>\<^sub>c B \<and> y = (right_coproj A B) \<circ>\<^sub>c b))"
      using cfunc_type_def coprojs_jointly_surj x_type x_type2 y_type by auto

    show "x=y"
    proof(cases "(\<exists> a. (a \<in>\<^sub>c A  \<and> x = (left_coproj A B) \<circ>\<^sub>c a))")
      assume "(\<exists> a. (a \<in>\<^sub>c A  \<and> x = (left_coproj A B) \<circ>\<^sub>c a))"
      then obtain a where a_def: "a \<in>\<^sub>c A" "x = (left_coproj A B) \<circ>\<^sub>c a"
        by blast
      show "x = y"
      proof(cases "(\<exists> a. (a \<in>\<^sub>c A  \<and> y = (left_coproj A B) \<circ>\<^sub>c a))")
        assume "(\<exists> a. (a \<in>\<^sub>c A  \<and> y = (left_coproj A B) \<circ>\<^sub>c a))"
        then obtain a' where a'_def: "a' \<in>\<^sub>c A" "y = (left_coproj A B) \<circ>\<^sub>c a'"
          by blast
        then have "a = a'"
        proof - 
          have "((left_coproj C D) \<circ>\<^sub>c f) \<circ>\<^sub>c a = \<phi> \<circ>\<^sub>c x"
            using \<phi>_def a_def cfunc_type_def comp_associative comp_type f_def g_def left_coproj_cfunc_coprod left_proj_type right_proj_type x_type by (smt (verit))
          also have "... = \<phi> \<circ>\<^sub>c y"
            by (meson equals)
          also have "... = (\<phi> \<circ>\<^sub>c (left_coproj A B)) \<circ>\<^sub>c a'"
            using \<phi>_type a'_def comp_associative2 by (typecheck_cfuncs, blast)
          also have "... = ((left_coproj C D) \<circ>\<^sub>c f) \<circ>\<^sub>c a'"
            unfolding \<phi>_def using f_def g_def a'_def left_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          then show "a = a'"
            by (smt a'_def a_def calculation cfunc_type_def coproj_f_inject domain_comp f_def injective_def left_proj_type)
        qed
        then show "x=y"
          by (simp add:  a'_def(2) a_def(2))
      next
        assume "\<nexists>a. a \<in>\<^sub>c A \<and> y = left_coproj A B \<circ>\<^sub>c a"
        then have "(\<exists> b. (b \<in>\<^sub>c B \<and> y = (right_coproj A B) \<circ>\<^sub>c b))"
          using y_form by blast
        then obtain b' where b'_def: "b' \<in>\<^sub>c B" "y = (right_coproj A B) \<circ>\<^sub>c b'"
          by blast
        show "x = y"
        proof - 
          have "(left_coproj C D) \<circ>\<^sub>c (f \<circ>\<^sub>c a) = ((left_coproj C D) \<circ>\<^sub>c f) \<circ>\<^sub>c a"
            using a_def cfunc_type_def comp_associative f_def left_proj_type by auto
          also have "...  = \<phi> \<circ>\<^sub>c x"
              using \<phi>_def a_def cfunc_type_def comp_associative comp_type f_def g_def left_coproj_cfunc_coprod left_proj_type right_proj_type x_type by (smt (verit))
          also have "... = \<phi> \<circ>\<^sub>c y"
            by (meson equals)
          also have "... = (\<phi> \<circ>\<^sub>c (right_coproj A B)) \<circ>\<^sub>c b'"
            using \<phi>_type b'_def comp_associative2 by (typecheck_cfuncs, blast)
          also have "... = (right_coproj C D \<circ>\<^sub>c g) \<circ>\<^sub>c b' "
            unfolding \<phi>_def using f_def g_def b'_def right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = (right_coproj C D) \<circ>\<^sub>c (g \<circ>\<^sub>c b')"
              using g_def b'_def by (typecheck_cfuncs, simp add: comp_associative2)
          then show "x = y"
             using  a_def(1) b'_def(1) calculation comp_type coproducts_disjoint f_def(1) g_def(1) by auto
         qed
       qed
     next
         assume "\<nexists>a. a \<in>\<^sub>c A \<and> x = left_coproj A B \<circ>\<^sub>c a"
         then have "(\<exists> b. (b \<in>\<^sub>c B \<and> x = (right_coproj A B) \<circ>\<^sub>c b))"
           using x_form by blast
         then obtain b where b_def: "(b \<in>\<^sub>c B \<and> x = (right_coproj A B) \<circ>\<^sub>c b)"
           by blast
              show "x = y"
              proof(cases "(\<exists> a. (a \<in>\<^sub>c A  \<and> y = (left_coproj A B) \<circ>\<^sub>c a))")
                 assume "(\<exists> a. (a \<in>\<^sub>c A  \<and> y = (left_coproj A B) \<circ>\<^sub>c a))"
                 then obtain a' where a'_def: "a' \<in>\<^sub>c A" "y = (left_coproj A B) \<circ>\<^sub>c a'"
                   by blast
                 show "x = y"
                 proof - 
                  have "(right_coproj C D) \<circ>\<^sub>c (g \<circ>\<^sub>c b) = ((right_coproj C D) \<circ>\<^sub>c g) \<circ>\<^sub>c b"
                    using b_def cfunc_type_def comp_associative g_def right_proj_type by auto
                  also have "...  = \<phi> \<circ>\<^sub>c x"
                    by (smt \<phi>_def \<phi>_type b_def comp_associative2 comp_type f_def(1) g_def(1) left_proj_type right_coproj_cfunc_coprod right_proj_type)
                  also have "... = \<phi> \<circ>\<^sub>c y"
                    by (meson equals)
                  also have "... = (\<phi> \<circ>\<^sub>c (left_coproj A B)) \<circ>\<^sub>c a'"
                    using \<phi>_type a'_def comp_associative2 by (typecheck_cfuncs, blast)
                  also have "... = (left_coproj C D \<circ>\<^sub>c f) \<circ>\<^sub>c a' "
                    unfolding \<phi>_def using f_def g_def a'_def left_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
                  also have "... = (left_coproj C D) \<circ>\<^sub>c (f \<circ>\<^sub>c a')"
                      using f_def a'_def by (typecheck_cfuncs, simp add: comp_associative2)
                  then show "x = y"
                    by (metis a'_def(1) b_def calculation comp_type coproducts_disjoint f_def(1) g_def(1))
                qed
        next
          assume "\<nexists>a. a \<in>\<^sub>c A \<and> y = left_coproj A B \<circ>\<^sub>c a"
          then have "(\<exists> b. (b \<in>\<^sub>c B \<and> y = (right_coproj A B) \<circ>\<^sub>c b))"
            using y_form by blast
        then obtain b' where b'_def: "b' \<in>\<^sub>c B" "y = (right_coproj A B) \<circ>\<^sub>c b'"
          by blast
        then have "b = b'"
        proof - 
          have "((right_coproj C D) \<circ>\<^sub>c g) \<circ>\<^sub>c b = \<phi> \<circ>\<^sub>c x"
            by (smt \<phi>_def \<phi>_type b_def comp_associative2 comp_type f_def(1) g_def(1) left_proj_type right_coproj_cfunc_coprod right_proj_type)
          also have "... = \<phi> \<circ>\<^sub>c y"
            by (meson equals)
          also have "... = (\<phi> \<circ>\<^sub>c (right_coproj A B)) \<circ>\<^sub>c b'"
            using \<phi>_type b'_def comp_associative2 by (typecheck_cfuncs, blast)
          also have "... = ((right_coproj C D) \<circ>\<^sub>c g) \<circ>\<^sub>c b'"
            unfolding \<phi>_def using f_def g_def b'_def right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          then show "b = b'"
            by (smt b'_def b_def calculation cfunc_type_def coproj_g_inject domain_comp g_def injective_def right_proj_type)
        qed
        then show "x = y"
          by (simp add: b'_def(2) b_def)
      qed
    qed
  qed

  have "monomorphism(\<phi>)"
    using \<open>injective \<phi>\<close> injective_imp_monomorphism by blast
  have "epimorphism(\<phi>)"
    by (simp add: \<open>surjective \<phi>\<close> surjective_is_epimorphism)
  have "isomorphism(\<phi>)"
    using \<open>epimorphism \<phi>\<close> \<open>monomorphism \<phi>\<close> epi_mon_is_iso by blast
  then show ?thesis
    using \<phi>_type is_isomorphic_def by blast
qed 

lemma product_distribute_over_coproduct_right:
  "(A \<Coprod> B) \<times>\<^sub>c C  \<cong> (A \<times>\<^sub>c C) \<Coprod> (B \<times>\<^sub>c C)"
  by (meson coprod_pres_iso isomorphic_is_transitive product_commutes product_distribute_over_coproduct_left)

lemma coproduct_with_self_iso:
  "X \<Coprod> X \<cong> X \<times>\<^sub>c \<Omega>"
proof - 
  obtain \<rho> where \<rho>_def: "\<rho> = \<langle>id X, \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> \<langle>id X, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>" and \<rho>_type[type_rule]: "\<rho> : X \<Coprod> X \<rightarrow> X \<times>\<^sub>c \<Omega>"
    by typecheck_cfuncs
  have \<rho>_inj: "injective \<rho>"
    unfolding injective_def
  proof(auto)
    fix x y 
    assume "x \<in>\<^sub>c domain \<rho>" then have x_type[type_rule]: "x \<in>\<^sub>c X \<Coprod> X"
      using \<rho>_type cfunc_type_def by auto
    assume "y \<in>\<^sub>c domain \<rho>" then have y_type[type_rule]: "y \<in>\<^sub>c X \<Coprod> X"
      using \<rho>_type cfunc_type_def by auto
    assume equals: "\<rho> \<circ>\<^sub>c x = \<rho> \<circ>\<^sub>c y"
    show "x = y"
    proof(cases "\<exists> lx. x = left_coproj X X \<circ>\<^sub>c lx \<and> lx \<in>\<^sub>c X")
      assume "\<exists>lx. x = left_coproj X X \<circ>\<^sub>c lx \<and> lx \<in>\<^sub>c X"
      then obtain lx where lx_def: "x = left_coproj X X \<circ>\<^sub>c lx \<and> lx \<in>\<^sub>c X"
        by blast
      have \<rho>x: "\<rho> \<circ>\<^sub>c x = \<langle>lx, \<t>\<rangle>"
      proof - 
        have "\<rho> \<circ>\<^sub>c x = (\<rho> \<circ>\<^sub>c left_coproj X X) \<circ>\<^sub>c lx"
          using comp_associative2 lx_def by (typecheck_cfuncs, blast)
        also have "... = \<langle>id X, \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c lx"
          unfolding \<rho>_def  using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
        also have "... = \<langle>lx, \<t>\<rangle>"
          by (typecheck_cfuncs, metis cart_prod_extract_left lx_def)
        then show ?thesis
          by (simp add: calculation)
      qed
      show "x = y"
      proof(cases "\<exists> ly. y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X")
        assume "\<exists>ly. y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X"
        then obtain ly where ly_def: "y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X"
          by blast
        have "\<rho> \<circ>\<^sub>c y = \<langle>ly, \<t>\<rangle>"
        proof - 
          have "\<rho> \<circ>\<^sub>c y = (\<rho> \<circ>\<^sub>c left_coproj X X) \<circ>\<^sub>c ly"
            using comp_associative2 ly_def by (typecheck_cfuncs, blast)
          also have "... = \<langle>id X, \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c ly"
            unfolding \<rho>_def  using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          also have "... = \<langle>ly, \<t>\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_extract_left ly_def)
          then show ?thesis
            by (simp add: calculation)
        qed
        then show "x = y"
          using \<rho>x cart_prod_eq2 equals lx_def ly_def true_func_type by auto
      next
        assume "\<nexists>ly. y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X"
        then obtain ry where ry_def: "y = right_coproj X X \<circ>\<^sub>c ry" and ry_type[type_rule]: "ry \<in>\<^sub>c X"
          by (meson y_type coprojs_jointly_surj)
        have \<rho>y: "\<rho> \<circ>\<^sub>c y = \<langle>ry, \<f>\<rangle>"
        proof - 
          have "\<rho> \<circ>\<^sub>c y = (\<rho> \<circ>\<^sub>c right_coproj X X) \<circ>\<^sub>c ry"
            using comp_associative2 ry_def by (typecheck_cfuncs, blast)
          also have "... = \<langle>id X, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c ry"
            unfolding \<rho>_def  using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          also have "... = \<langle>ry, \<f>\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_extract_left)
          then show ?thesis
            by (simp add: calculation)
        qed
        then show ?thesis
          using \<rho>x \<rho>y cart_prod_eq2 equals false_func_type lx_def ry_type true_false_distinct true_func_type by force
      qed
    next
      assume "\<nexists>lx. x = left_coproj X X \<circ>\<^sub>c lx \<and> lx \<in>\<^sub>c X"
      then obtain rx where rx_def: "x = right_coproj X X \<circ>\<^sub>c rx \<and> rx \<in>\<^sub>c X"
        by (typecheck_cfuncs, meson coprojs_jointly_surj)
      have \<rho>x: "\<rho> \<circ>\<^sub>c x = \<langle>rx, \<f>\<rangle>"
      proof - 
        have "\<rho> \<circ>\<^sub>c x = (\<rho> \<circ>\<^sub>c right_coproj X X) \<circ>\<^sub>c rx"
          using comp_associative2 rx_def by (typecheck_cfuncs, blast)
        also have "... = \<langle>id X, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c rx"
          unfolding \<rho>_def  using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
        also have "... = \<langle>rx, \<f>\<rangle>"
          by (typecheck_cfuncs, metis cart_prod_extract_left rx_def)
        then show ?thesis
          by (simp add: calculation)
      qed
      show "x = y"
      proof(cases "\<exists> ly. y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X")
        assume "\<exists>ly. y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X"
        then obtain ly where ly_def: "y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X"
          by blast
        have "\<rho> \<circ>\<^sub>c y = \<langle>ly, \<t>\<rangle>"
        proof - 
          have "\<rho> \<circ>\<^sub>c y = (\<rho> \<circ>\<^sub>c left_coproj X X) \<circ>\<^sub>c ly"
            using comp_associative2 ly_def by (typecheck_cfuncs, blast)
          also have "... = \<langle>id X, \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c ly"
            unfolding \<rho>_def  using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          also have "... = \<langle>ly, \<t>\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_extract_left ly_def)
          then show ?thesis
            by (simp add: calculation)
        qed
        then show "x = y"
          using \<rho>x cart_prod_eq2 equals false_func_type ly_def rx_def true_false_distinct true_func_type by force
      next
        assume "\<nexists>ly. y = left_coproj X X \<circ>\<^sub>c ly \<and> ly \<in>\<^sub>c X"
        then obtain ry where ry_def: "y = right_coproj X X \<circ>\<^sub>c ry \<and> ry \<in>\<^sub>c X"
          using  coprojs_jointly_surj by (typecheck_cfuncs, blast)
        have \<rho>y: "\<rho> \<circ>\<^sub>c y = \<langle>ry, \<f>\<rangle>"
        proof - 
          have "\<rho> \<circ>\<^sub>c y = (\<rho> \<circ>\<^sub>c right_coproj X X) \<circ>\<^sub>c ry"
            using comp_associative2 ry_def by (typecheck_cfuncs, blast)
          also have "... = \<langle>id X, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c ry"
            unfolding \<rho>_def  using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          also have "... = \<langle>ry, \<f>\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_extract_left ry_def)
          then show ?thesis
            by (simp add: calculation)
        qed
        show "x = y"
          using \<rho>x \<rho>y cart_prod_eq2 equals false_func_type rx_def ry_def by auto
      qed
    qed
  qed
  have "surjective \<rho>"
    unfolding surjective_def
  proof(auto)
    fix y
    assume "y \<in>\<^sub>c codomain \<rho>" then have y_type[type_rule]: "y \<in>\<^sub>c X \<times>\<^sub>c \<Omega>"
      using \<rho>_type cfunc_type_def by fastforce
    then obtain x w where y_def: "y = \<langle>x,w\<rangle> \<and> x \<in>\<^sub>c X \<and> w \<in>\<^sub>c \<Omega>"
      using cart_prod_decomp by fastforce
    show "\<exists>x. x \<in>\<^sub>c domain \<rho> \<and> \<rho> \<circ>\<^sub>c x = y"
    proof(cases "w = \<t>")
      assume "w = \<t>"
      obtain z where z_def: "z = left_coproj X X \<circ>\<^sub>c x"
        by simp
      have "\<rho> \<circ>\<^sub>c z = y"
      proof - 
        have "\<rho> \<circ>\<^sub>c z = (\<rho> \<circ>\<^sub>c left_coproj X X) \<circ>\<^sub>c x"
          using comp_associative2 y_def z_def by (typecheck_cfuncs, blast)
        also have "... = \<langle>id X, \<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c x"
          unfolding \<rho>_def  using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)        
        also have "... = y"
          using \<open>w = \<t>\<close> cart_prod_extract_left y_def by auto
        then show ?thesis
          by (simp add: calculation)
      qed
      then show ?thesis
        by (metis \<rho>_type cfunc_type_def codomain_comp domain_comp left_proj_type y_def z_def)
    next
      assume "w \<noteq> \<t>" then have "w = \<f>"  
        by (typecheck_cfuncs, meson \<open>w \<noteq> \<t>\<close> true_false_only_truth_values y_def)
      obtain z where z_def: "z = right_coproj X X \<circ>\<^sub>c x"
        by simp
      have "\<rho> \<circ>\<^sub>c z = y"
      proof - 
        have "\<rho> \<circ>\<^sub>c z = (\<rho> \<circ>\<^sub>c right_coproj X X) \<circ>\<^sub>c x"
          using comp_associative2 y_def z_def by (typecheck_cfuncs, blast)
        also have "... = \<langle>id X, \<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>  \<circ>\<^sub>c x"
          unfolding \<rho>_def  using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)        
        also have "... = y"
          using \<open>w = \<f>\<close> cart_prod_extract_left y_def by auto
        then show ?thesis
          by (simp add: calculation)
      qed
      then show ?thesis
        by (metis \<rho>_type cfunc_type_def codomain_comp domain_comp right_proj_type y_def z_def)
    qed
  qed
  then show ?thesis
    by (metis \<rho>_inj \<rho>_type epi_mon_is_iso injective_imp_monomorphism is_isomorphic_def mem_Collect_eq surjective_is_epimorphism)
qed

lemma oneUone_iso_\<Omega>:
  "(one \<Coprod> one) \<cong> \<Omega>"
  by (meson truth_value_set_iso_1u1 cfunc_coprod_type false_func_type is_isomorphic_def true_func_type)

(* Dual to Proposition 2.2.2 *)
lemma "card {x. x \<in>\<^sub>c \<Omega> \<Coprod> \<Omega>} = 4"
proof -
  (*Distinctness*)
  have f1: "(left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t> \<noteq> (right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t>"
    by (typecheck_cfuncs, simp add: coproducts_disjoint)
  have f2: "(left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t> \<noteq> (left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f>"
    by (typecheck_cfuncs, metis cfunc_type_def left_coproj_are_monomorphisms monomorphism_def true_false_distinct)
  have f3: "(left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t> \<noteq> (right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f>"
    by (typecheck_cfuncs, simp add: coproducts_disjoint)
  have f4: "(right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t> \<noteq> (left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f>"
    by (typecheck_cfuncs, metis (no_types) coproducts_disjoint)
  have f5: "(right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t> \<noteq> (right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f>"
    by (typecheck_cfuncs, metis cfunc_type_def monomorphism_def right_coproj_are_monomorphisms true_false_distinct)
  have f6: "(left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f> \<noteq> (right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f>"
    by (typecheck_cfuncs, simp add: coproducts_disjoint)
  (*Upper limit*)
  have "{x. x \<in>\<^sub>c \<Omega> \<Coprod> \<Omega>} = {(left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t> , (right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<t>, (left_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f>, (right_coproj \<Omega> \<Omega>) \<circ>\<^sub>c \<f>}"
    using coprojs_jointly_surj true_false_only_truth_values 
    by (typecheck_cfuncs, auto) 
  then show "card {x. x \<in>\<^sub>c \<Omega> \<Coprod> \<Omega>} = 4"
    by (simp add: f1 f2 f3 f4 f5 f6)
qed

end