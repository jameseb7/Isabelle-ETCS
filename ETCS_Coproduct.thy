theory ETCS_Coproduct
  imports ETCS_Equivalence
begin

section  \<open>Axiom 7: Coproducts\<close>

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

(* Coproduct commutes *)
lemma coproduct_commutes:
  "A \<Coprod> B \<cong> B \<Coprod> A"
proof -
  have j1Uj0_type: "(right_coproj B A) \<amalg> (left_coproj B A) : A \<Coprod> B \<rightarrow> B \<Coprod> A"
    by (simp add: cfunc_coprod_type left_proj_type right_proj_type)
  have i0Ui1_type: "(right_coproj A B)  \<amalg> (left_coproj A B) : B \<Coprod> A \<rightarrow>  A \<Coprod> B"
    by (simp add: cfunc_coprod_type left_proj_type right_proj_type)
  have id_AB: "((right_coproj A B)  \<amalg> (left_coproj A B)) \<circ>\<^sub>c ((right_coproj B A) \<amalg> (left_coproj B A)) = id(A \<Coprod> B)"
    by (smt cfunc_coprod_comp cfunc_coprod_unique cfunc_type_def i0Ui1_type id_left_unit id_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type)
  have id_BA: " ((right_coproj B A) \<amalg> (left_coproj B A)) \<circ>\<^sub>c ((right_coproj A B)  \<amalg> (left_coproj A B)) = id(B \<Coprod> A)"
    by (smt cfunc_coprod_comp cfunc_coprod_unique cfunc_type_def id_left_unit id_type j1Uj0_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type)
  show "A \<Coprod> B \<cong> B \<Coprod> A"
    by (metis cfunc_type_def i0Ui1_type id_AB id_BA is_isomorphic_def isomorphism_def j1Uj0_type)
qed

(* Proposition 2.4.1 *)
lemma coproducts_disjoint:
  "\<forall>x y. (x\<in>\<^sub>c X \<and> y \<in>\<^sub>c Y)  \<longrightarrow>  ((left_coproj X Y) \<circ>\<^sub>c x \<noteq> (right_coproj X Y) \<circ>\<^sub>c y)"
proof (rule ccontr, auto)
  fix x y
  assume x_type: "x\<in>\<^sub>c X" 
  assume y_type: "y \<in>\<^sub>c Y"
  assume BWOC: "((left_coproj X Y) \<circ>\<^sub>c x = (right_coproj X Y) \<circ>\<^sub>c y)"
  obtain g where g_type: "g: X \<rightarrow> \<Omega> \<and> g factorsthru  \<t>"
  proof -
    assume a1: "\<And>g. g : X \<rightarrow> \<Omega> \<and> g factorsthru \<t> \<Longrightarrow> thesis"
    have f2: "\<forall>c. domain (\<t> \<circ>\<^sub>c \<beta>\<^bsub>c\<^esub>) = c"
      by (meson cfunc_type_def comp_type terminal_func_type true_func_type)
    have "domain \<t> = one"
      using cfunc_type_def true_func_type by blast
    then show ?thesis
      using f2 a1 by (metis (no_types) comp_type factors_through_def terminal_func_type true_func_type)
  qed
  then have fact1: "\<t> = g \<circ>\<^sub>c x"
    by (metis cfunc_type_def comp_associative factors_through_def id_right_unit2 id_type
        terminal_func_comp terminal_func_unique true_func_type x_type)
     
  obtain h where h_type: "h: Y \<rightarrow> \<Omega> \<and> h factorsthru \<f>"
      proof -
        assume a1: "\<And>h. h : Y \<rightarrow> \<Omega> \<and> h factorsthru \<f> \<Longrightarrow> thesis"
        have f2: "\<forall>c. domain (\<f> \<circ>\<^sub>c \<beta>\<^bsub>c\<^esub>) = c"
          by (meson cfunc_type_def comp_type false_func_type terminal_func_type)
        have "domain \<f> = one"
          using cfunc_type_def false_func_type by blast
        then show ?thesis
          using f2 a1 by (metis (no_types) comp_type factors_through_def false_func_type terminal_func_type)
      qed
  then have gUh_type: "g \<amalg> h: X \<Coprod> Y \<rightarrow> \<Omega> \<and>
      (g \<amalg> h) \<circ>\<^sub>c (left_coproj X Y) = g \<and>  (g \<amalg> h) \<circ>\<^sub>c (right_coproj X Y) = h"
      proof -
        show ?thesis
          by (meson cfunc_coprod_type g_type h_type left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
      qed
  then have fact2: "\<f> = h \<circ>\<^sub>c y"
    by (metis cfunc_type_def comp_associative factors_through_def false_func_type h_type
        id_right_unit id_type terminal_func_comp terminal_func_unique y_type)
  also have "... = ((g \<amalg> h) \<circ>\<^sub>c (right_coproj X Y)) \<circ>\<^sub>c y"
      by (simp add: gUh_type)
  also have "... = ((g \<amalg> h) \<circ>\<^sub>c (left_coproj X Y)) \<circ>\<^sub>c x"
    by (smt BWOC comp_associative2 gUh_type left_proj_type right_proj_type x_type y_type)
  also have "... =  g \<circ>\<^sub>c x"
      by (simp add: gUh_type)
  also have "... = \<t>"
      by (simp add: fact1)
  then have Contradiction: "\<t> = \<f>"
      by (simp add: calculation)
  show False
      using Contradiction true_false_distinct by auto
qed

(*Proposition 2.4.2*)
lemma left_coproj_are_monomorphisms:
  "monomorphism(left_coproj X Y)"
proof (cases "\<exists>x. x \<in>\<^sub>c X")
  assume X_nonempty: "\<exists>x. x \<in>\<^sub>c X"
  then obtain x where "x \<in>\<^sub>c X"
    by auto
  then have x_beta_type: "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X"
    using comp_type terminal_func_type by blast
  then have "(id X \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj X Y = id X"
    using id_type left_coproj_cfunc_coprod by blast
  then show "monomorphism (left_coproj X Y)"
    by (metis x_beta_type cfunc_coprod_type cfunc_type_def comp_monic_imp_monic id_isomorphism
        id_type iso_imp_epi_and_monic left_proj_type)
next
  assume "\<nexists>x. x \<in>\<^sub>c X"
  then have "injective (left_coproj X Y)"
    using cfunc_type_def injective_def left_proj_type by auto
  then show "monomorphism (left_coproj X Y)"
    using injective_imp_monomorphism by auto
qed

lemma right_coproj_are_monomorphisms:
  "monomorphism(right_coproj X Y)"
proof (cases "\<exists>y. y \<in>\<^sub>c Y")
  assume Y_nonempty: "\<exists>y. y \<in>\<^sub>c Y"
  then obtain y where "y \<in>\<^sub>c Y"
    by auto
  then have y_beta_type: "y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> Y"
    using comp_type terminal_func_type by blast
  then have "((y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> id Y) \<circ>\<^sub>c right_coproj X Y = id Y"
    using id_type right_coproj_cfunc_coprod by blast
  then show "monomorphism (right_coproj X Y)"
    by (metis cfunc_coprod_type cfunc_type_def comp_monic_imp_monic id_isomorphism id_type
        iso_imp_epi_and_monic right_proj_type y_beta_type)
next
  assume "\<nexists>y. y \<in>\<^sub>c Y"
  then have "injective (right_coproj X Y)"
    using cfunc_type_def injective_def right_proj_type by auto
  then show "monomorphism (right_coproj X Y)"
    using injective_imp_monomorphism by auto
qed

(*Fun idea, probably not going to be necessary.*)
(*
definition indicator :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "indicator X x= (THE \<chi>. is_pullback one one X \<Omega> (\<beta>\<^bsub>one\<^esub>) \<t> x \<chi>)"

lemma char_of_singleton3:
  assumes "x \<in>\<^sub>c X"
  shows "(indicator X x) \<circ>\<^sub>c x  = \<t>"
  using assms by (typecheck_cfuncs, smt characteristic_function_exists element_monomorphism indicator_def is_pullback_def square_commutes_def terminal_func_unique the_equality)

lemma char_of_singleton4:
    assumes "x \<in>\<^sub>c X"  "y \<in>\<^sub>c X" "x \<noteq> y"
    shows "(indicator X x) \<circ>\<^sub>c y  = \<f>"
    using assms by (typecheck_cfuncs, smt characteristic_function_exists element_monomorphism id_right_unit2 id_type indicator_def is_pullback_def one_unique_element square_commutes_def the_equality true_false_only_truth_values)
*)



(*Proposition 2.4.3*)
lemma coprojs_jointly_surj:
  assumes "z \<in>\<^sub>c X \<Coprod> Y"
  shows "(\<exists> x. (x \<in>\<^sub>c X \<and> z = (left_coproj X Y) \<circ>\<^sub>c x))
      \<or>  (\<exists> y. (y \<in>\<^sub>c Y \<and> z = (right_coproj X Y) \<circ>\<^sub>c y))"
proof (rule ccontr, auto)
  assume not_in_left_image: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow> z \<noteq> left_coproj X Y \<circ>\<^sub>c x"
  assume not_in_right_image: "\<forall>y. y \<in>\<^sub>c Y \<longrightarrow> z \<noteq> right_coproj X Y \<circ>\<^sub>c y"
  
  have fact1: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow>  ((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x) = \<f>)"
    proof(auto)
      fix x
      assume x_type: "x \<in>\<^sub>c X"
      show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x) = \<f>" 
        using assms by (typecheck_cfuncs, metis cfunc_type_def char_of_singleton2 comp_associative not_in_left_image x_type)
    qed

  have fact2: "\<forall>x. x \<in>\<^sub>c X \<longrightarrow>  ((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x) = \<f>)"
    proof(auto)
      fix y
      assume y_type: "y \<in>\<^sub>c X"
      show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c y) = \<f>" 
        using assms by (typecheck_cfuncs, metis cfunc_type_def char_of_singleton2 comp_associative not_in_left_image y_type)
    qed

    obtain h where h_def: "h = \<f> \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>"
      by simp

    have fact3: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
                 left_coproj X Y = h \<circ>\<^sub>c left_coproj X Y"
    proof(rule one_separator[where X=X, where Y = \<Omega>])
      show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
    left_coproj X Y : X \<rightarrow> \<Omega>"
        by (meson assms cfunc_prod_type comp_type eq_pred_type id_type left_proj_type terminal_func_type)       
      show "h \<circ>\<^sub>c left_coproj X Y : X \<rightarrow> \<Omega>"
        using h_def comp_type false_func_type left_proj_type terminal_func_type by blast
      show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow>
         ((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
          left_coproj X Y) \<circ>\<^sub>c
         x =
         (h \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x"
      proof - 
        fix x
        assume x_type: "x \<in>\<^sub>c X"
        have "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
          left_coproj X Y) \<circ>\<^sub>c
         x = eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> \<circ>\<^sub>c (
          left_coproj X Y \<circ>\<^sub>c
         x)"
               using x_type by (typecheck_cfuncs, metis assms cfunc_type_def comp_associative)
        also have "... = \<f>"
               using x_type by(typecheck_cfuncs, simp add: assms char_of_singleton2 not_in_left_image)
        also have "... = h \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x)"
               using x_type by (typecheck_cfuncs, smt comp_associative2 h_def id_right_unit2 id_type terminal_func_comp terminal_func_type terminal_func_unique)
        also have "... = (h \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x"
               using x_type cfunc_type_def comp_associative comp_type false_func_type h_def terminal_func_type by (typecheck_cfuncs, force)
        then show "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
          left_coproj X Y) \<circ>\<^sub>c
         x  = (h \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x"
               by (simp add: calculation)
           qed
     qed

have fact4: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
                 right_coproj X Y = h \<circ>\<^sub>c right_coproj X Y"
 proof(rule one_separator[where X = Y, where Y = \<Omega>])
   show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c right_coproj X Y : Y \<rightarrow> \<Omega>"
     by (meson assms cfunc_prod_type comp_type eq_pred_type id_type right_proj_type terminal_func_type)
   show "h \<circ>\<^sub>c right_coproj X Y : Y \<rightarrow> \<Omega>"
     using cfunc_type_def codomain_comp domain_comp false_func_type h_def right_proj_type terminal_func_type by presburger
   show "\<And>x. x \<in>\<^sub>c Y \<Longrightarrow>
         ((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
          right_coproj X Y) \<circ>\<^sub>c
         x =
         (h \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x"
   proof - 
     fix x
     assume x_type: "x \<in>\<^sub>c Y"
     have "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
          right_coproj X Y) \<circ>\<^sub>c
         x = eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> \<circ>\<^sub>c (
          right_coproj X Y \<circ>\<^sub>c
         x)"
          using x_type by (typecheck_cfuncs, smt assms comp_associative2)
        also have "... = \<f>"
            using x_type by (typecheck_cfuncs, simp add: assms char_of_singleton2 not_in_right_image)
        also have "... = h \<circ>\<^sub>c (right_coproj X Y \<circ>\<^sub>c x)"
              using x_type by (typecheck_cfuncs, smt comp_associative2 h_def id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
        also have "... = (h \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x"
              using x_type by (typecheck_cfuncs, smt comp_associative2 false_func_type h_def terminal_func_comp terminal_func_type)
        then show "((eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c
          right_coproj X Y) \<circ>\<^sub>c
         x =
         (h \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c x"
          by (simp add: calculation)
      qed
    qed

    have indicator_is_false:"eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle> = h"
      using assms apply (typecheck_cfuncs)
    proof(rule one_separator[where X = "X \<Coprod> Y", where Y = \<Omega>])
      show "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> \<Omega> \<Longrightarrow>
    eq_pred (X \<Coprod> Y) : (X \<Coprod> Y) \<times>\<^sub>c X \<Coprod> Y \<rightarrow> \<Omega> \<Longrightarrow>
    \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> (X \<Coprod> Y) \<times>\<^sub>c X \<Coprod> Y \<Longrightarrow>
    z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> X \<Coprod> Y \<Longrightarrow>
    \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> one \<Longrightarrow>
    id\<^sub>c (X \<Coprod> Y) : X \<Coprod> Y \<rightarrow> X \<Coprod> Y \<Longrightarrow>
    z \<in>\<^sub>c X \<Coprod> Y \<Longrightarrow> eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> \<Omega>"
        by blast
      show "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> \<Omega> \<Longrightarrow>
    eq_pred (X \<Coprod> Y) : (X \<Coprod> Y) \<times>\<^sub>c X \<Coprod> Y \<rightarrow> \<Omega> \<Longrightarrow>
    \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> (X \<Coprod> Y) \<times>\<^sub>c X \<Coprod> Y \<Longrightarrow>
    z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> X \<Coprod> Y \<Longrightarrow>
    \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> one \<Longrightarrow>
    id\<^sub>c (X \<Coprod> Y) : X \<Coprod> Y \<rightarrow> X \<Coprod> Y \<Longrightarrow> z \<in>\<^sub>c X \<Coprod> Y \<Longrightarrow> h : X \<Coprod> Y \<rightarrow> \<Omega>"
        using comp_type false_func_type h_def by blast
      then show "\<And>x. eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> \<Omega> \<Longrightarrow>
         eq_pred (X \<Coprod> Y) : (X \<Coprod> Y) \<times>\<^sub>c X \<Coprod> Y \<rightarrow> \<Omega> \<Longrightarrow>
         \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle> : X \<Coprod> Y \<rightarrow> (X \<Coprod> Y) \<times>\<^sub>c X \<Coprod> Y \<Longrightarrow>
         z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> X \<Coprod> Y \<Longrightarrow>
         \<beta>\<^bsub>X \<Coprod> Y\<^esub> : X \<Coprod> Y \<rightarrow> one \<Longrightarrow>
         id\<^sub>c (X \<Coprod> Y) : X \<Coprod> Y \<rightarrow> X \<Coprod> Y \<Longrightarrow>
         z \<in>\<^sub>c X \<Coprod> Y \<Longrightarrow>
         x \<in>\<^sub>c X \<Coprod> Y \<Longrightarrow>
         (eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>,id\<^sub>c (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
        by (smt cfunc_coprod_unique cfunc_type_def codomain_comp domain_comp fact3 fact4 left_proj_type right_proj_type)
    qed

    have hz_gives_false: "h \<circ>\<^sub>c z = \<f>"
      using assms by (typecheck_cfuncs, smt comp_associative2 h_def id_right_unit2 id_type terminal_func_comp terminal_func_type terminal_func_unique)

    then have indicator_z_gives_false: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c z = \<f>"
      using assms indicator_is_false  by (typecheck_cfuncs, blast)

    then have indicator_z_gives_true: "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>z \<circ>\<^sub>c \<beta>\<^bsub>X \<Coprod> Y\<^esub>, id (X \<Coprod> Y)\<rangle>) \<circ>\<^sub>c z = \<t>"
      using assms by (typecheck_cfuncs, smt char_of_singleton1 comp_associative2)

    then have contradiction: "\<t> = \<f>"
      using indicator_z_gives_false by auto

    then show False
      using true_false_distinct by auto

qed

lemma maps_into_1u1:
  assumes x_type:  "x\<in>\<^sub>c (one \<Coprod> one)"
  shows "(x = left_coproj one one) \<or> (x = right_coproj one one)"
  using assms by (typecheck_cfuncs, metis coprojs_jointly_surj terminal_func_unique)





(*Proposition 2.4.4*)
lemma truth_value_set_iso_1u1:
  "isomorphism(\<t>\<amalg>\<f>)"
proof- 
  have "\<forall>z. z \<in>\<^sub>c (one \<Coprod> one) \<longrightarrow>  (\<exists> x. (x \<in>\<^sub>c one \<and> z = (left_coproj one one) \<circ>\<^sub>c x))
      \<or>  (\<exists> y. (y \<in>\<^sub>c one \<and> z = (right_coproj one one) \<circ>\<^sub>c y))"
    by (simp add: coprojs_jointly_surj)
  have tf_type: "(\<t>\<amalg>\<f>) : (one \<Coprod> one) \<rightarrow> \<Omega>"
    by (simp add: cfunc_coprod_type false_func_type true_func_type)
  have epic: "epimorphism(\<t>\<amalg>\<f>)"
    by (metis cfunc_type_def false_func_type left_coproj_cfunc_coprod left_proj_type right_coproj_cfunc_coprod right_proj_type surjective_def surjective_is_epimorphism tf_type true_false_only_truth_values true_func_type)
  have injective: "injective(\<t>\<amalg>\<f>)"
    unfolding injective_def 
  proof(auto)
    fix x y
    assume x_type: "x \<in>\<^sub>c domain (\<t> \<amalg> \<f>)"
    assume y_type: "y \<in>\<^sub>c domain (\<t> \<amalg> \<f>)"
    assume equals: "\<t> \<amalg> \<f> \<circ>\<^sub>c x = \<t> \<amalg> \<f> \<circ>\<^sub>c y"
    show "x=y"
      by (metis cfunc_type_def equals false_func_type left_coproj_cfunc_coprod maps_into_1u1 right_coproj_cfunc_coprod tf_type true_false_distinct true_func_type x_type y_type)
  qed
  have mono: "monomorphism(\<t>\<amalg>\<f>)"
    using injective injective_imp_monomorphism by auto
  then show ?thesis
    using epi_mon_is_iso epic by auto
qed



(*Proposition 2.5.10 ... Better version*)
lemma product_distribute_over_coproduct_left:
  "A \<times>\<^sub>c (B \<Coprod> C) \<cong> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
proof-
  have type1: "id(A) \<times>\<^sub>f (left_coproj B C) : (A \<times>\<^sub>c B) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by typecheck_cfuncs
 have type2: "id(A) \<times>\<^sub>f (right_coproj B C) : (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
   by typecheck_cfuncs
  obtain \<phi> where \<phi>_def: "\<phi> = (id(A) \<times>\<^sub>f (left_coproj B C)) \<amalg> (id(A) \<times>\<^sub>f (right_coproj B C))"
    by blast
  then have \<phi>_type: "\<phi> : (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<Coprod> C)"
    by (simp add: cfunc_coprod_type type1 type2)


  have surjective: "surjective((id(A) \<times>\<^sub>f (left_coproj B C)) \<amalg> (id(A) \<times>\<^sub>f (right_coproj B C)))"
    unfolding surjective_def
  proof(auto)
    fix y 
    assume y_type: "y \<in>\<^sub>c codomain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C))"
    then have y_type2: "y \<in>\<^sub>c A \<times>\<^sub>c (B \<Coprod> C)"
      using \<phi>_def \<phi>_type cfunc_type_def by auto
    then have "\<exists>a bc. a \<in>\<^sub>c A \<and> bc \<in>\<^sub>c (B \<Coprod> C) \<and> y = \<langle>a,bc\<rangle>"
      using cart_prod_decomp by blast
    then obtain a where a_def: "\<exists> bc. a \<in>\<^sub>c A \<and> bc \<in>\<^sub>c (B \<Coprod> C) \<and> y = \<langle>a,bc\<rangle>"
      by blast
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
        by (typecheck_cfuncs, simp add: \<phi>_def left_coproj_cfunc_coprod type2)
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
        using \<phi>_def right_coproj_cfunc_coprod type1 by (typecheck_cfuncs, auto)
      also have "... = \<phi> \<circ>\<^sub>c x"
        using \<phi>_type x_def ac_type comp_associative2 by (typecheck_cfuncs, auto)
      then show "\<exists>x. x \<in>\<^sub>c domain ((id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C)) \<and>
        (id\<^sub>c A \<times>\<^sub>f left_coproj B C) \<amalg> (id\<^sub>c A \<times>\<^sub>f right_coproj B C) \<circ>\<^sub>c x = y"
        using \<phi>_def calculation x_type by auto
    qed
  qed
  
        
  have injective: "injective(\<phi>)"
    unfolding injective_def
  proof(auto) 
    fix x y
    assume x_type: "x \<in>\<^sub>c domain \<phi>"
    assume y_type: "y \<in>\<^sub>c domain \<phi>"
    assume equal: "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c y"

    have "x \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
      using cfunc_type_def \<phi>_type x_type by auto
    then have x_form: "(\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> x = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))
      \<or>  (\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> x = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))"
      by (simp add: coprojs_jointly_surj)
    have "y \<in>\<^sub>c (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
      using cfunc_type_def \<phi>_type y_type by auto
    then have y_form: "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))
      \<or>  (\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> y = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
      by (simp add: coprojs_jointly_surj)
    
    show "x = y" 
    proof(cases "(\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> x = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))")
      assume "(\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> x = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))"
      then obtain x' where x'_def: "x' \<in>\<^sub>c A \<times>\<^sub>c B \<and> x = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c x'"
        by blast
      then have ab_exists: "\<exists> a b. a \<in>\<^sub>c A \<and> b \<in>\<^sub>c B \<and> x' =\<langle>a,b\<rangle>"
        using cart_prod_decomp by blast
      then obtain a b where ab_def: "a \<in>\<^sub>c A \<and> b \<in>\<^sub>c B \<and> x' =\<langle>a,b\<rangle>"
        by blast
      show "x = y"  
      proof(cases "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))")
        assume "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
        then obtain y' where y'_def: "y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
          by blast
        then have ab_exists: "\<exists> a' b'. a' \<in>\<^sub>c A \<and> b' \<in>\<^sub>c B \<and> y' =\<langle>a',b'\<rangle>"
          using cart_prod_decomp by blast
        then obtain a' b' where a'b'_def: "a' \<in>\<^sub>c A \<and> b' \<in>\<^sub>c B \<and> y' =\<langle>a',b'\<rangle>"
          by blast
        have equal_pair: "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
        proof - 
        have "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (left_coproj B C) \<circ>\<^sub>c b\<rangle>"
          using ab_def id_left_unit2 by force
        also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a,  b\<rangle>"
          by (smt ab_def cfunc_cross_prod_comp_cfunc_prod id_type left_proj_type)
        also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, b\<rangle>"
          using \<phi>_def left_coproj_cfunc_coprod type1 type2 by auto
        also have "... = \<phi> \<circ>\<^sub>c x"
          using ab_def comp_associative2 \<phi>_type x'_def by (typecheck_cfuncs, fastforce)
        also have "... = \<phi> \<circ>\<^sub>c y"
          by (simp add: local.equal)
        also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', b'\<rangle>"
          using a'b'_def comp_associative2 \<phi>_type y'_def by (typecheck_cfuncs, blast)
        also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a',  b'\<rangle>"
          using \<phi>_def left_coproj_cfunc_coprod type1 type2 by auto
        also have "... = \<langle>id(A) \<circ>\<^sub>c a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
          using a'b'_def cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs,auto)
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
      then have "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> y = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
        using y_form by blast
      then obtain y' where y'_def: "(y' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> y = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y')"
        by blast
      then have ab_exists: "\<exists> a' c'. a' \<in>\<^sub>c A \<and> c' \<in>\<^sub>c C \<and> y' =\<langle>a',c'\<rangle>"
          using cart_prod_decomp by blast
      then obtain a' c' where a'c'_def: "a' \<in>\<^sub>c A \<and> c' \<in>\<^sub>c C \<and> y' =\<langle>a',c'\<rangle>"
        by blast 
      have equal_pair: "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
         proof - 
                have "\<langle>a, (left_coproj B C) \<circ>\<^sub>c b\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (left_coproj B C) \<circ>\<^sub>c b\<rangle>"
                  using ab_def id_left_unit2 by force
                also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a,  b\<rangle>"
                  by (smt ab_def cfunc_cross_prod_comp_cfunc_prod id_type left_proj_type)
                also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, b\<rangle>"
                  using \<phi>_def left_coproj_cfunc_coprod type1 type2 by auto
                also have "... = \<phi> \<circ>\<^sub>c x"
                  using ab_def comp_associative2 \<phi>_type x'_def by (typecheck_cfuncs, fastforce)
                also have "... = \<phi> \<circ>\<^sub>c y"
                  by (simp add: local.equal)
                also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', c'\<rangle>"
                  using a'c'_def comp_associative2 \<phi>_type y'_def by (typecheck_cfuncs, blast)
                  also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle> a',  c'\<rangle>"
                  using \<phi>_def right_coproj_cfunc_coprod type1 type2 by auto
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
    then have "(\<exists> x'. (x' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> x = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c x'))"
      using x_form by blast
    then obtain x' where x'_def: "x' \<in>\<^sub>c A \<times>\<^sub>c C \<and> x = right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c x'"
        by blast
      then have ac_exists: "\<exists> a c. a \<in>\<^sub>c A \<and> c \<in>\<^sub>c C \<and> x' =\<langle>a,c\<rangle>"
        using cart_prod_decomp by blast
      then obtain a c where ac_def: "a \<in>\<^sub>c A \<and> c \<in>\<^sub>c C \<and> x' =\<langle>a,c\<rangle>"
        by blast
            show "x = y"  
      proof(cases "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))")
        assume "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
        then obtain y' where y'_def: "y' \<in>\<^sub>c (A \<times>\<^sub>c B) \<and> y = left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
          by blast
        then have ab_exists: "\<exists> a' b'. a' \<in>\<^sub>c A \<and> b' \<in>\<^sub>c B \<and> y' =\<langle>a',b'\<rangle>"
          using cart_prod_decomp by blast
        then obtain a' b' where a'b'_def: "a' \<in>\<^sub>c A \<and> b' \<in>\<^sub>c B \<and> y' =\<langle>a',b'\<rangle>"
          by blast
        have equal_pair: "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>a', (left_coproj B C) \<circ>\<^sub>c b'\<rangle>"
        proof - 
                have "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (right_coproj B C) \<circ>\<^sub>c c\<rangle>"
                  using ac_def id_left_unit2 by force
                also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle>a,  c\<rangle>"
                  by (smt ac_def cfunc_cross_prod_comp_cfunc_prod id_type right_proj_type)
                also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, c\<rangle>"
                  using \<phi>_def right_coproj_cfunc_coprod type1 type2 by auto
                also have "... = \<phi> \<circ>\<^sub>c x"
                  using ac_def comp_associative2 \<phi>_type x'_def by (typecheck_cfuncs, fastforce)
                also have "... = \<phi> \<circ>\<^sub>c y"
                  by (simp add: local.equal)
                also have "... = (\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', b'\<rangle>"
                  using a'b'_def comp_associative2 \<phi>_type y'_def by (typecheck_cfuncs, blast)
                  also have "... = (id(A) \<times>\<^sub>f (left_coproj B C))  \<circ>\<^sub>c \<langle> a',  b'\<rangle>"
                  using \<phi>_def left_coproj_cfunc_coprod type1 type2 by auto
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
      then have "(\<exists> y'. (y' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> y = (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C)) \<circ>\<^sub>c y'))"
        using y_form by blast
      then obtain y' where y'_def: "y' \<in>\<^sub>c (A \<times>\<^sub>c C) \<and> y = right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C) \<circ>\<^sub>c y'"
          by blast
        then have a'c'_exists: "\<exists> a' c'. a' \<in>\<^sub>c A \<and> c' \<in>\<^sub>c C \<and> y' =\<langle>a',c'\<rangle>"
          using cart_prod_decomp by blast
        then obtain a' c' where a'c'_def: "a' \<in>\<^sub>c A \<and> c' \<in>\<^sub>c C \<and> y' =\<langle>a',c'\<rangle>"
          by blast
        have equal_pair: "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>a', (right_coproj B C) \<circ>\<^sub>c c'\<rangle>"
         proof - 
                have "\<langle>a, (right_coproj B C) \<circ>\<^sub>c c\<rangle> = \<langle>id(A) \<circ>\<^sub>c a, (right_coproj B C) \<circ>\<^sub>c c\<rangle>"
                  using ac_def id_left_unit2 by force
                also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle>a,  c\<rangle>"
                  by (smt ac_def cfunc_cross_prod_comp_cfunc_prod id_type right_proj_type)
                also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a, c\<rangle>"
                  using \<phi>_def right_coproj_cfunc_coprod type1 type2 by auto
                also have "... = \<phi> \<circ>\<^sub>c x"
                  using ac_def comp_associative2 \<phi>_type x'_def by (typecheck_cfuncs, fastforce)
                also have "... = \<phi> \<circ>\<^sub>c y"
                  by (simp add: local.equal)
                also have "... = (\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c B) (A \<times>\<^sub>c C))) \<circ>\<^sub>c \<langle>a', c'\<rangle>"
                  using a'c'_def comp_associative2 \<phi>_type y'_def by (typecheck_cfuncs, blast)
                  also have "... = (id(A) \<times>\<^sub>f (right_coproj B C))  \<circ>\<^sub>c \<langle> a',  c'\<rangle>"
                  using \<phi>_def right_coproj_cfunc_coprod type1 type2 by auto
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


  have monomorphism: "monomorphism(\<phi>)"
    using injective injective_imp_monomorphism by auto
  have epimorphism: "epimorphism(\<phi>)"
    by (simp add: \<phi>_def surjective surjective_is_epimorphism)
  have "isomorphism(\<phi>)"
    using epi_mon_is_iso epimorphism monomorphism by auto
  then show "A \<times>\<^sub>c (B \<Coprod> C) \<cong> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"
    using \<phi>_type is_isomorphic_def isomorphic_is_symmetric by blast
qed



lemma prod_pres_iso:
  assumes "A \<cong>  C"  "B \<cong> D"
  shows "A \<times>\<^sub>c B \<cong>  C \<times>\<^sub>c D"
proof - 
  obtain f where f_def: "f: A \<rightarrow> C \<and> isomorphism(f)"
    using assms(1) is_isomorphic_def by blast
  obtain g where g_def: "g: B \<rightarrow> D \<and> isomorphism(g)"
    using assms(2) is_isomorphic_def by blast
  have fg_type: "f\<times>\<^sub>fg : A \<times>\<^sub>c B \<rightarrow>  C \<times>\<^sub>c D"
    by (typecheck_cfuncs, simp add: f_def g_def)
  have mono: "monomorphism(f\<times>\<^sub>fg)"
    using cfunc_cross_prod_mono f_def g_def iso_imp_epi_and_monic by blast
  have epic: "epimorphism(f\<times>\<^sub>fg)"
    using f_def g_def iso_imp_epi_and_monic product_of_epis_is_epi by blast
  have "isomorphism(f\<times>\<^sub>fg)"
    using epic mono epi_mon_is_iso by auto
  then show "A \<times>\<^sub>c B \<cong>  C \<times>\<^sub>c D"
    using fg_type is_isomorphic_def by blast
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
        using \<phi>_def \<phi>_type a_def c_def cfunc_type_def comp_associative comp_type f_def g_def left_coproj_cfunc_coprod left_proj_type right_proj_type x_def by force
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
        using \<phi>_def \<phi>_type b_def cfunc_type_def comp_associative comp_type d_def f_def g_def left_proj_type right_coproj_cfunc_coprod right_proj_type x_def by force
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
            using \<phi>_def a_def cfunc_type_def comp_associative comp_type f_def g_def left_coproj_cfunc_coprod left_proj_type right_proj_type x_type by auto
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
              using \<phi>_def a_def cfunc_type_def comp_associative comp_type f_def g_def left_coproj_cfunc_coprod left_proj_type right_proj_type x_type by auto
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



(* These aren't actually equal... more like "equal up to isomorphism*)
lemma func_product_distribute_over_coproduct_left:
  "f \<times>\<^sub>f (g \<amalg> h) = (f \<times>\<^sub>f g) \<amalg> (f \<times>\<^sub>f h)"
  oops



         
end