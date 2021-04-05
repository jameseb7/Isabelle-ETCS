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
  left_proj_type: "left_coproj X Y : X \<rightarrow> X\<Coprod>Y" and
  right_proj_type: "right_coproj X Y : Y \<rightarrow> X\<Coprod>Y" and
  cfunc_coprod_type: "(f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow> (f\<amalg>g :  X\<Coprod>Y \<rightarrow> Z)" and
  left_coproj_cfunc_coprod: "(f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow> (f\<amalg>g \<circ>\<^sub>c (left_coproj X Y)  = f)" and
  right_coproj_cfunc_coprod: "(f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow> (f\<amalg>g \<circ>\<^sub>c (right_coproj X Y)  = g)" and
  cfunc_coprod_unique: "(f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z) \<longrightarrow> 
    (\<forall> h. (h : X \<Coprod> Y \<rightarrow> Z \<and> (h \<circ>\<^sub>c left_coproj X Y = f) \<and> (h \<circ>\<^sub>c right_coproj X Y = g)) \<longrightarrow> h = f\<amalg>g)"

lemma cfunc_coprod_comp:
  assumes a_type: "a : Y \<rightarrow> Z"
  assumes b_type: "b : X \<rightarrow> Y"
  assumes c_type: "c : W \<rightarrow> Y"
  shows "(a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c) = a \<circ>\<^sub>c (b \<amalg> c)"
proof -
  have type1: "a \<circ>\<^sub>c (b \<amalg> c) :  X\<Coprod>W \<rightarrow> Z"
    using a_type b_type c_type cfunc_coprod_type comp_type by blast
  have type2: "a \<circ>\<^sub>c (b \<amalg> c) \<circ>\<^sub>c left_coproj X W : X \<rightarrow> Z"
    using a_type b_type c_type left_coproj_cfunc_coprod by auto
  have type3: "a \<circ>\<^sub>c (b \<amalg> c) \<circ>\<^sub>c right_coproj X W : W \<rightarrow> Z"
    using a_type b_type c_type right_coproj_cfunc_coprod by auto

  show "(a \<circ>\<^sub>c b) \<amalg> (a \<circ>\<^sub>c c) = a \<circ>\<^sub>c (b \<amalg> c)"
    by (smt b_type c_type cfunc_coprod_unique comp_associative left_coproj_cfunc_coprod right_coproj_cfunc_coprod type1 type2 type3)
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
     by (smt cfunc_type_def comp_associative comp_type factors_through_def one_separator_contrapos one_unique_element true_func_type x_type)
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
      by (metis cfunc_type_def comp_associative comp_type factors_through_def false_func_type h_type id_right_unit id_type one_unique_element y_type)
  also have "... = ((g \<amalg> h) \<circ>\<^sub>c (right_coproj X Y)) \<circ>\<^sub>c y"
      by (simp add: gUh_type)
  also have "... = ((g \<amalg> h) \<circ>\<^sub>c (left_coproj X Y)) \<circ>\<^sub>c x"
      by (metis (full_types) BWOC comp_associative)
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
  then have "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X"
    using comp_type terminal_func_type by blast
  then have "(id X \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c left_coproj X Y = id X"
    using id_type left_coproj_cfunc_coprod by blast
  then show "monomorphism (left_coproj X Y)"
    by (metis comp_monic_imp_monic id_isomorphism iso_imp_epi_and_monic)
next
  assume "\<nexists>x. x \<in>\<^sub>c X"
  then have "injective (left_coproj X Y)"
    using cfunc_type_def injective_def left_proj_type by auto
  then show "monomorphism (left_coproj X Y)"
    using cfunc_type_def injective_imp_monomorphism left_proj_type by auto
qed

lemma right_coproj_are_monomorphisms:
  "monomorphism(right_coproj X Y)"
proof (cases "\<exists>y. y \<in>\<^sub>c Y")
  assume Y_nonempty: "\<exists>y. y \<in>\<^sub>c Y"
  then obtain y where "y \<in>\<^sub>c Y"
    by auto
  then have "y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> : X \<rightarrow> Y"
    using comp_type terminal_func_type by blast
  then have "((y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> id Y) \<circ>\<^sub>c right_coproj X Y = id Y"
    using id_type right_coproj_cfunc_coprod by blast
  then show "monomorphism (right_coproj X Y)"
    by (metis comp_monic_imp_monic id_isomorphism iso_imp_epi_and_monic)
next
  assume "\<nexists>y. y \<in>\<^sub>c Y"
  then have "injective (right_coproj X Y)"
    using cfunc_type_def injective_def right_proj_type by auto
  then show "monomorphism (right_coproj X Y)"
    using cfunc_type_def injective_imp_monomorphism right_proj_type by auto
qed



(*Proposition 2.4.4*)

lemma truth_value_set_iso_1u1:
  "isomorphism(\<t>\<amalg>\<f>)"
  unfolding isomorphism_def
proof 
  oops

end