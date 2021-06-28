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

lemma product_distribute_over_coproduct_left:
  "A \<times>\<^sub>c (B \<Coprod> C) \<cong> (A \<times>\<^sub>c B) \<Coprod> (A \<times>\<^sub>c C)"


end