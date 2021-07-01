theory ETCS_Func
  imports ETCS_Empty
begin

section \<open>Axiom 9: Exponential Objects\<close>

axiomatization
  exp_set :: "cset \<Rightarrow> cset \<Rightarrow> cset" ("_\<^bsup>_\<^esup>" [100,100]100) and
  eval_func  :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  transpose_func :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>\<sharp>" [100]100)
where
  exp_set_inj: "X\<^bsup>A\<^esup> = Y\<^bsup>B\<^esup> \<Longrightarrow> X = Y \<and> A = B" and
  eval_func_type[type_rule]: "eval_func X A : A\<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X" and
  transpose_func_type[type_rule]: "f : A \<times>\<^sub>c Z \<rightarrow> X \<Longrightarrow> f\<^sup>\<sharp> : Z \<rightarrow> X\<^bsup>A\<^esup>" and
  transpose_func_def: "f : A \<times>\<^sub>c Z \<rightarrow> X \<Longrightarrow> (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f\<^sup>\<sharp>) = f" and
  transpose_func_unique: 
    "f : A\<times>\<^sub>cZ \<rightarrow> X \<Longrightarrow> g: Z \<rightarrow> X\<^bsup>A\<^esup> \<Longrightarrow> (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f g) = f \<Longrightarrow> g = f\<^sup>\<sharp>"

(* Definition 2.5.1 *)
definition exp_func :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc" ("(_)\<^bsup>_\<^esup>\<^sub>f" [100,100]100) where
  "exp_func g A = (g \<circ>\<^sub>c eval_func (domain g) A)\<^sup>\<sharp>"

lemma exp_func_def2:
  assumes "g : X \<rightarrow> Y"
  shows "exp_func g A = (g \<circ>\<^sub>c eval_func X A)\<^sup>\<sharp>"
  using assms cfunc_type_def exp_func_def by auto

lemma exp_func_type[type_rule]:
  assumes "g : X \<rightarrow> Y"
  shows "g\<^bsup>A\<^esup>\<^sub>f : X\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
  using assms by (unfold exp_func_def2, typecheck_cfuncs)

(* Note above Definition 2.5.1 *)
lemma exponential_object_identity:
  "(eval_func X A)\<^sup>\<sharp> = id\<^sub>c(X\<^bsup>A\<^esup>)"
  by (metis cfunc_type_def eval_func_type id_cross_prod id_right_unit id_type transpose_func_unique)

(* Note below Definition 2.5.1 *)
lemma exponential_square_diagram:
  assumes "g : Y \<rightarrow> Z"
  shows "square_commutes (A \<times>\<^sub>c Y\<^bsup>A\<^esup>) Y (A \<times>\<^sub>c Z\<^bsup>A\<^esup>) Z (eval_func Y A)  g (id\<^sub>c(A)\<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) (eval_func Z A)"
  unfolding square_commutes_def
  using assms by (typecheck_cfuncs, simp add: exp_func_def2 transpose_func_def)

(* Proposition 2.5.2 *)
lemma transpose_of_comp:
  assumes f_type: "f: A \<times>\<^sub>c X \<rightarrow> Y" and g_type: "g: Y \<rightarrow> Z"
  shows "f: A \<times>\<^sub>c X \<rightarrow> Y \<and> g: Y \<rightarrow> Z  \<Longrightarrow>  (g \<circ>\<^sub>c f)\<^sup>\<sharp> = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>"
proof auto
  have square_commutes: "square_commutes (A \<times>\<^sub>c Y\<^bsup>A\<^esup>) Y (A \<times>\<^sub>c Z\<^bsup>A\<^esup>) Z (eval_func Y A)  g (id(A)\<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) (eval_func Z A)"
    using exponential_square_diagram g_type by blast
  have triangle_commutes: "triangle_commutes (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y\<^bsup>A\<^esup>) Y (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) (eval_func Y A) f"
    unfolding triangle_commutes_def using assms by (typecheck_cfuncs, simp add: transpose_func_def)
  have left_eq: "(eval_func Z A) \<circ>\<^sub>c(id(A) \<times>\<^sub>f (g \<circ>\<^sub>c f)\<^sup>\<sharp>) = (g \<circ>\<^sub>c f)"
    using comp_type f_type g_type transpose_func_def by blast
  have right_eq: "(eval_func Z A) \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>)) = g \<circ>\<^sub>c f"
    using assms by (typecheck_cfuncs, smt comp_associative2 identity_distributes_across_composition square_commutes square_commutes_def triangle_commutes triangle_commutes_def)
  show "(g \<circ>\<^sub>c f)\<^sup>\<sharp> = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, metis right_eq transpose_func_unique)
qed

(*Comments below Proposition 2.5.2 and above Definition 2.5.3*)
lemma eval_of_id_cross_id_sharp1:
  "(eval_func (A \<times>\<^sub>c X) A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (id(A \<times>\<^sub>c X))\<^sup>\<sharp>)  = id(A \<times>\<^sub>c X)"
  using id_type transpose_func_def by blast
lemma eval_of_id_cross_id_sharp2:
  assumes "a : Z \<rightarrow> A" "x : Z \<rightarrow> X"
  shows "((eval_func (A \<times>\<^sub>c X) A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (id(A \<times>\<^sub>c X))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>a,x\<rangle> = \<langle>a,x\<rangle>"
  by (smt assms cfunc_cross_prod_comp_cfunc_prod eval_of_id_cross_id_sharp1 id_cross_prod id_left_unit2 id_type)

(* Definition 2.5.3 *)
definition inv_transpose_func :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>\<flat>" [100]100) where
  "f\<^sup>\<flat> = (SOME g. \<exists> Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f))"

lemma inv_transpose_func_def2:
  assumes "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> = (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f)"
  unfolding inv_transpose_func_def
proof (rule someI2)
  show "\<exists>Z Xa Aa. domain f = Z \<and> codomain f = Xa\<^bsup>Aa\<^esup> \<and> eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f = eval_func Xa Aa \<circ>\<^sub>c id\<^sub>c Aa \<times>\<^sub>f f"
    using assms cfunc_type_def by blast
next
  fix g
  assume "\<exists>Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f"
  then show "g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f"
    by (metis assms cfunc_type_def exp_set_inj)
qed

lemma flat_type[type_rule]:
  assumes f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X"
proof (subst inv_transpose_func_def2[where Z=Z, where X=X, where A=A], simp add: assms)
  have cross_type: "id\<^sub>c A \<times>\<^sub>f f : A \<times>\<^sub>c Z \<rightarrow> A \<times>\<^sub>c X\<^bsup>A\<^esup>"
    by (simp add: cfunc_cross_prod_type f_type id_type)
  have "eval_func X A : A \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X"
    by (simp add: eval_func_type)
  then show "eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f : A \<times>\<^sub>c Z \<rightarrow> X"
    using cross_type comp_type by auto
qed

(* Proposition 2.5.4 *)
lemma inv_transpose_of_composition:
  assumes "f: X \<rightarrow> Y" "g: Y \<rightarrow> Z\<^bsup>A\<^esup>"
  shows "(g \<circ>\<^sub>c f)\<^sup>\<flat> = g\<^sup>\<flat> \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
  using assms comp_associative2 identity_distributes_across_composition
  by (typecheck_cfuncs, unfold inv_transpose_func_def2, typecheck_cfuncs)

(* Proposition 2.5.5 *)
lemma flat_cancels_sharp:
  "f : A \<times>\<^sub>c Z \<rightarrow> X  \<Longrightarrow> (f\<^sup>\<sharp>)\<^sup>\<flat> = f"
  using inv_transpose_func_def2 transpose_func_def transpose_func_type by fastforce

(* Proposition 2.5.6 *)
lemma sharp_cancels_flat:
  shows "f: Z \<rightarrow> X\<^bsup>A\<^esup>  \<Longrightarrow> (f\<^sup>\<flat>)\<^sup>\<sharp> = f"
proof -
  assume f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  then have "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X"
    using flat_type by blast
  then have uniqueness: "\<forall> g. g : Z \<rightarrow> X\<^bsup>A\<^esup> \<longrightarrow> eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f g) = f\<^sup>\<flat> \<longrightarrow> g = (f\<^sup>\<flat>)\<^sup>\<sharp>"
    using transpose_func_unique by blast

  have "eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f f) = f\<^sup>\<flat>"
    by (metis f_type inv_transpose_func_def2)
  then show "f\<^sup>\<flat>\<^sup>\<sharp> = f"
    using f_type uniqueness by auto
qed

lemma same_evals_equal:
  assumes "f : Z \<rightarrow> X\<^bsup>A\<^esup>" "g: Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f f) = eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f g) \<Longrightarrow> f = g"
  by (metis assms inv_transpose_func_def2 sharp_cancels_flat)

lemma sharp_comp:
  assumes "f : A \<times>\<^sub>c Z \<rightarrow> X" "g : W \<rightarrow> Z"
  shows "f\<^sup>\<sharp> \<circ>\<^sub>c g = (f \<circ>\<^sub>c (id A \<times>\<^sub>f g))\<^sup>\<sharp>"
proof (rule same_evals_equal[where Z=W, where X=X, where A=A])
  show "f\<^sup>\<sharp> \<circ>\<^sub>c g : W \<rightarrow> X\<^bsup>A\<^esup>"
    using assms by typecheck_cfuncs
  show "(f \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f g)\<^sup>\<sharp> : W \<rightarrow> X\<^bsup>A\<^esup>"
    using assms by typecheck_cfuncs

  have "eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c g)) = eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (id A \<times>\<^sub>f g)"
    using assms by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
  also have "... = f \<circ>\<^sub>c (id A \<times>\<^sub>f g)"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = eval_func X A \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f (f \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f g))\<^sup>\<sharp>)"
    using assms by (typecheck_cfuncs, simp add: transpose_func_def)

  then show "eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c g)) = eval_func X A \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f (f \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f g))\<^sup>\<sharp>)"
    using calculation by auto
qed

lemma eval_func_X_one_injective:
  "injective (eval_func X one)"
proof (cases "\<exists> x. x \<in>\<^sub>c X")
  assume "\<exists>x. x \<in>\<^sub>c X"
  then obtain x where x_type: "x \<in>\<^sub>c X"
    by auto
  then have "eval_func X one \<circ>\<^sub>c id\<^sub>c one \<times>\<^sub>f (x \<circ>\<^sub>c \<beta>\<^bsub>one \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> = x \<circ>\<^sub>c \<beta>\<^bsub>one \<times>\<^sub>c one\<^esub>"
    using comp_type terminal_func_type transpose_func_def by blast
  
  show "injective (eval_func X one)"
    unfolding injective_def
  proof auto
    fix a b
    assume a_type: "a \<in>\<^sub>c domain (eval_func X one)"
    assume b_type: "b \<in>\<^sub>c domain (eval_func X one)"
    assume evals_equal: "eval_func X one \<circ>\<^sub>c a = eval_func X one \<circ>\<^sub>c b"

    have eval_dom: "domain(eval_func X one) = one \<times>\<^sub>c (X\<^bsup>one\<^esup>)"
      using cfunc_type_def eval_func_type by auto

    obtain A where a_def: "A \<in>\<^sub>c (X\<^bsup>one\<^esup>) \<and> a = \<langle>id(one), A\<rangle>"
      by (typecheck_cfuncs, metis a_type cart_prod_decomp eval_dom terminal_func_unique)

    obtain B where b_def: "B \<in>\<^sub>c (X\<^bsup>one\<^esup>) \<and> b = \<langle>id(one), B\<rangle>"
      by (typecheck_cfuncs, metis b_type cart_prod_decomp eval_dom terminal_func_unique)

    

    have A_doppelganger: "A = (A\<^sup>\<flat>)\<^sup>\<sharp>"
      using a_def sharp_cancels_flat by auto

   have B_doppelganger: "B = (B\<^sup>\<flat>)\<^sup>\<sharp>"
        using b_def sharp_cancels_flat by auto
   have Aflat11eqsBflat11: "A\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle> = B\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle>"
   proof - 
      have "A\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle> = (eval_func X one) \<circ>\<^sub>c (id (one) \<times>\<^sub>f (A\<^sup>\<flat>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle>"
            using A_doppelganger a_def comp_associative2 inv_transpose_func_def2 by (typecheck_cfuncs, fastforce)
      also have "... = eval_func X one \<circ>\<^sub>c a"
            using A_doppelganger a_def cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by (typecheck_cfuncs, auto)
      also have "... = eval_func X one \<circ>\<^sub>c b"
        by (simp add: evals_equal)
      also have "... = (eval_func X one) \<circ>\<^sub>c (id (one) \<times>\<^sub>f (B\<^sup>\<flat>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle>"
            using B_doppelganger b_def cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by (typecheck_cfuncs, auto)
      also have "... = B\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle>"
            using B_doppelganger b_def comp_associative2 inv_transpose_func_def2 by (typecheck_cfuncs, fastforce)
      then show "A\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle> = B\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle>"
        using calculation by auto
    qed
    have "A\<^sup>\<flat> = B\<^sup>\<flat>"
      by (typecheck_cfuncs, smt ETCS_Cartesian.swap_def Aflat11eqsBflat11 a_def b_def cfunc_prod_comp comp_associative2 diagonal_def diagonal_type id_right_unit2 id_type left_cart_proj_type right_cart_proj_type swap_idempotent swap_type terminal_func_comp terminal_func_unique)

    then have "A = B"
      using A_doppelganger B_doppelganger by auto

    then show "a = b"
      by (simp add: a_def b_def)
  qed
next
  assume "\<nexists>x. x \<in>\<^sub>c X"
  then show "injective (eval_func X one)"
    by (typecheck_cfuncs, metis  cfunc_type_def comp_type injective_def)
qed







(* Proposition 2.5.7 *)
lemma set_to_power_one:
   assumes "\<And>X A Y B. X\<^bsup>A\<^esup> = Y\<^bsup>B\<^esup> \<Longrightarrow> X = Y \<and> A = B"
   shows "X\<^bsup>one\<^esup> \<cong> X"
 proof -
  obtain e where e_defn: "e = eval_func X one" and e_type: "e : one \<times>\<^sub>c X\<^bsup>one\<^esup> \<rightarrow> X"
    using eval_func_type by auto
  obtain i where i_type: "i: one \<times>\<^sub>c one \<rightarrow> one"
    using terminal_func_type by blast
  obtain i_inv where i_iso: "i_inv: one\<rightarrow>  one \<times>\<^sub>c one \<and> 
                                  i\<circ>\<^sub>c i_inv = id(one) \<and>  
                                  i_inv\<circ>\<^sub>c i = id(one \<times>\<^sub>c one)"
    by (smt cfunc_cross_prod_comp_cfunc_prod cfunc_cross_prod_comp_diagonal cfunc_cross_prod_def cfunc_prod_type cfunc_type_def diagonal_def i_type id_cross_prod id_left_unit id_type left_cart_proj_type right_cart_proj_cfunc_prod right_cart_proj_type terminal_func_unique)
  then have i_inv_type: "i_inv: one\<rightarrow>  one \<times>\<^sub>c one"
    by auto
        
  have inj: "injective(e)"
    by (simp add: e_defn eval_func_X_one_injective)


  have surj: "surjective(e)"
     unfolding surjective_def
   proof auto
    fix y 
    assume "y \<in>\<^sub>c codomain e"
    then have y_type: "y \<in>\<^sub>c X"
      using cfunc_type_def e_type by auto

      thm e_type

    have witness_type: "(id\<^sub>c one \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>) \<circ>\<^sub>c i_inv \<in>\<^sub>c one \<times>\<^sub>c X\<^bsup>one\<^esup>"
      using y_type i_type i_inv_type by typecheck_cfuncs

    have square: "e \<circ>\<^sub>c (id(one) \<times>\<^sub>f (y\<circ>\<^sub>c i)\<^sup>\<sharp>) = y\<circ>\<^sub>c i"
      using comp_type e_defn i_type transpose_func_def y_type by blast
    then show "\<exists>x. x \<in>\<^sub>c domain e \<and> e \<circ>\<^sub>c x = y" 
      unfolding cfunc_type_def using y_type i_type i_inv_type e_type 
      by (rule_tac x="(id(one) \<times>\<^sub>f (y\<circ>\<^sub>c i)\<^sup>\<sharp>)\<circ>\<^sub>c i_inv" in exI, typecheck_cfuncs, metis cfunc_type_def comp_associative i_iso id_right_unit2)
  qed

  have "isomorphism e"
    using epi_mon_is_iso inj injective_imp_monomorphism surj surjective_is_epimorphism by fastforce
  then show "X\<^bsup>one\<^esup> \<cong> X"
    using e_type is_isomorphic_def isomorphic_is_symmetric isomorphic_is_transitive one_x_A_iso_A by blast
qed

(* Proposition 2.5.8 *)
lemma set_to_power_zero:
  "X\<^bsup>\<emptyset>\<^esup> \<cong> one"
proof - 
  obtain f where f_type: "f = \<alpha>\<^bsub>X\<^esub>\<circ>\<^sub>c (left_cart_proj \<emptyset> one)"
    by simp
  have fsharp_type: "f\<^sup>\<sharp> \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
    using comp_type f_type initial_func_type left_cart_proj_type transpose_func_type by blast
  have uniqueness: "\<forall>z. z \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup> \<longrightarrow> z=f\<^sup>\<sharp>"
  proof auto
    fix z
    assume z_type: "z \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
    have "\<emptyset> \<cong> \<emptyset> \<times>\<^sub>c one"
      by (simp add: A_x_one_iso_A isomorphic_is_symmetric)
    then obtain j where j_iso:"j:\<emptyset> \<rightarrow> \<emptyset> \<times>\<^sub>c one \<and> isomorphism(j)"
      using is_isomorphic_def by blast
    then have j_form: "j= \<alpha>\<^bsub>\<emptyset> \<times>\<^sub>c one\<^esub>"
      using emptyset_is_empty initial_func_type one_separator by blast
    then obtain \<psi> where psi_type: "\<psi> : \<emptyset> \<times>\<^sub>c one \<rightarrow> \<emptyset> \<and> 
                     j \<circ>\<^sub>c \<psi> = id(\<emptyset> \<times>\<^sub>c one) \<and> \<psi> \<circ>\<^sub>c j = id(\<emptyset>)"
      using cfunc_type_def isomorphism_def j_iso by fastforce
    then have \<psi>_type_uniqe: "\<forall>g. (g: \<emptyset> \<times>\<^sub>c one \<rightarrow> \<emptyset>) \<longrightarrow> g=\<psi>"
      using comp_type emptyset_is_empty one_separator by blast
    have "\<emptyset>\<cong> \<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
      by (simp add: isomorphic_is_symmetric zero_times_X)
    then obtain \<phi> where phi_iso: "\<phi>:\<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup> \<rightarrow> \<emptyset> \<and> isomorphism(\<phi>)"
      using is_isomorphic_def zero_times_X by blast
    then have Id0xz_type: "(id(\<emptyset>)\<times>\<^sub>f z):\<emptyset> \<times>\<^sub>c one \<rightarrow> \<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
      by (simp add: cfunc_cross_prod_type id_type z_type)
    then have phiId0xz_typ: "\<phi> \<circ>\<^sub>c (id(\<emptyset>)\<times>\<^sub>f z):\<emptyset> \<times>\<^sub>c one  \<rightarrow>  \<emptyset>"
      using comp_type phi_iso by blast
    then have unique1: "\<phi> \<circ>\<^sub>c (id(\<emptyset>)\<times>\<^sub>f z) = \<psi>"
      using comp_type emptyset_is_empty one_separator_contrapos psi_type by blast
    have Id0xfsharp_type: "(id(\<emptyset>)\<times>\<^sub>f f\<^sup>\<sharp>):\<emptyset> \<times>\<^sub>c one \<rightarrow> \<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
      by (simp add: cfunc_cross_prod_type fsharp_type id_type)
    then have phiId0xfsharp_type: "\<phi> \<circ>\<^sub>c (id(\<emptyset>)\<times>\<^sub>f f\<^sup>\<sharp>):\<emptyset> \<times>\<^sub>c one  \<rightarrow>  \<emptyset>"
      by (meson comp_type phi_iso)
    then have unique2: "\<phi> \<circ>\<^sub>c (id(\<emptyset>)\<times>\<^sub>f f\<^sup>\<sharp>) = \<psi>"
      using comp_type emptyset_is_empty one_separator_contrapos psi_type by blast
    then have PhiId0xZEqsPhiId0xfsharp : "\<phi>\<circ>\<^sub>c (id(\<emptyset>)\<times>\<^sub>f z) = \<phi>\<circ>\<^sub>c(id(\<emptyset>)\<times>\<^sub>f f\<^sup>\<sharp>)"
      using unique1 by auto
    then have Id0xZEqsId0xfsharp : "id(\<emptyset>)\<times>\<^sub>f z = id(\<emptyset>)\<times>\<^sub>f f\<^sup>\<sharp>"
      by (meson Id0xfsharp_type Id0xz_type comp_type emptyset_is_empty left_cart_proj_type one_separator)
    then show "z = f\<^sup>\<sharp>"
      by (smt Id0xfsharp_type comp_type eval_func_type fsharp_type transpose_func_unique z_type)
  qed
  then have "(\<exists>! x. x \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>)"
    by (rule_tac a="f\<^sup>\<sharp>" in ex1I, simp_all add: fsharp_type)
  then show "X\<^bsup>\<emptyset>\<^esup> \<cong> one"
    using single_elem_iso_one by auto
qed

lemma one_to_X_iso_one:
  "one\<^bsup>X\<^esup> \<cong> one"
proof - 
  have nonempty: "nonempty(one\<^bsup>X\<^esup>)"
    using nonempty_def right_cart_proj_type transpose_func_type by blast
  obtain e where e_defn: "e = eval_func one X" and e_type: "e : X \<times>\<^sub>c one\<^bsup>X\<^esup> \<rightarrow> one"
    by (simp add: eval_func_type)
  have uniqueness: "\<forall>y. (y\<in>\<^sub>c one\<^bsup>X\<^esup> \<longrightarrow> e\<circ>\<^sub>c (id(X) \<times>\<^sub>f y) : X \<times>\<^sub>c one  \<rightarrow> one)"
    by (meson cfunc_cross_prod_type comp_type e_type id_type)
  have uniquess_form: "\<forall>y. (y\<in>\<^sub>c one\<^bsup>X\<^esup> \<longrightarrow> e\<circ>\<^sub>c (id(X) \<times>\<^sub>f y) = \<beta>\<^bsub>X \<times>\<^sub>c one\<^esub>)"
    using terminal_func_unique uniqueness by blast
  then have ex1: "(\<exists>! x. x \<in>\<^sub>c one\<^bsup>X\<^esup>)"
    by (metis e_defn nonempty nonempty_def transpose_func_unique uniqueness)
  show "one\<^bsup>X\<^esup> \<cong> one"
    using ex1 single_elem_iso_one by auto
qed

(* Proposition 2.5.9 *)
lemma power_rule:
  assumes "\<And>X A Y B. X\<^bsup>A\<^esup> = Y\<^bsup>B\<^esup> \<Longrightarrow> X = Y \<and> A = B"
  shows "(X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<cong> X\<^bsup>A\<^esup> \<times>\<^sub>c Y\<^bsup>A\<^esup>"
proof - 
  have "is_cart_prod ((X \<times>\<^sub>c Y)\<^bsup>A\<^esup>) ((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) ((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) (X\<^bsup>A\<^esup>) (Y\<^bsup>A\<^esup>)"
    unfolding is_cart_prod_def
  proof auto
    show "(left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f : (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>A\<^esup>"
      by (simp add: exp_func_type left_cart_proj_type)
  next
    show "(right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f : (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
      by (simp add: exp_func_type right_cart_proj_type)
  next
    fix f g Z 
    assume f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
    assume g_type: "g : Z \<rightarrow> Y\<^bsup>A\<^esup>"

    show "\<exists>h. h : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<and>
           left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h = f \<and>
           right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h = g \<and>
           (\<forall>h2. h2 : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<and> left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 = f \<and> right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 = g \<longrightarrow>
                 h2 = h)"
    proof (rule_tac x="\<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp>" in exI, auto)
      have fflat_type: "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X"
        using assms f_type flat_type by blast
      have gflat_type: "g\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> Y"
        using assms flat_type g_type by blast
      then have prod_fflat_gflat_type: "\<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle> : A \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y"
        by (simp add: cfunc_prod_type fflat_type)
      then show sharp_prod_fflat_gflat_type: "\<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup>"
        by (simp add: transpose_func_type)
      then have proj_type: "left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> X"
        using left_cart_proj_type by blast
      then have proj_trans_type: "(left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f : (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>A\<^esup>"
        by (simp add: exp_func_type)
      then have "((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = ((left_cart_proj X Y) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>)\<^sup>\<sharp>"
        using prod_fflat_gflat_type proj_type transpose_of_comp by auto
      also have "... = (f\<^sup>\<flat>)\<^sup>\<sharp>"
        using fflat_type gflat_type left_cart_proj_cfunc_prod by auto
      also have "... = f"
        using assms f_type sharp_cancels_flat by blast
      show projection_property1: "((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = f"
        by (simp add: \<open>f\<^sup>\<flat>\<^sup>\<sharp> = f\<close> calculation)
      have proj2_type: "right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y"
        using right_cart_proj_type by blast
      then have proj2_trans_type: "(right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f : (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
        by (simp add: exp_func_type)
      then show projection_property2: "((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = g"
        by (metis assms fflat_type g_type gflat_type prod_fflat_gflat_type proj2_type right_cart_proj_cfunc_prod sharp_cancels_flat transpose_of_comp)
      show "\<And>h2. h2 : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<Longrightarrow>
          f = left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 \<Longrightarrow>
          g = right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 \<Longrightarrow>
          h2 = \<langle>(left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2)\<^sup>\<flat>,(right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2)\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
      proof -
        fix h
        assume h_type: "h : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup>"
        assume h_property1:  "f = ((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c h"
        assume h_property2:  "g = ((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c h"
    
        have "f = ((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (metis assms h_property1 h_type sharp_cancels_flat)
        also have "... = ((left_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (metis assms flat_type h_type proj_type transpose_of_comp)
        have computation1: "f = ((left_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (simp add: \<open>left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp> = (left_cart_proj X Y \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>\<close> calculation)
        then have unqiueness1: "(left_cart_proj X Y) \<circ>\<^sub>c  h\<^sup>\<flat> =  f\<^sup>\<flat>"
          using h_type f_type by (typecheck_cfuncs, simp add: computation1 flat_cancels_sharp)
        have   "g = ((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (metis assms h_property2 h_type sharp_cancels_flat)
        have "... = ((right_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
           by (metis assms flat_type h_type proj2_type transpose_of_comp)
        have computation2: "g = ((right_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
           by (simp add: \<open>g = right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp>\<close> \<open>right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp> = (right_cart_proj X Y \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>\<close>)
        then have unqiueness2: "(right_cart_proj X Y) \<circ>\<^sub>c  h\<^sup>\<flat> =  g\<^sup>\<flat>"
          using h_type g_type by (typecheck_cfuncs, simp add: computation2 flat_cancels_sharp)
        then have h_flat: "h\<^sup>\<flat> = \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>"
          using assms cfunc_prod_unique fflat_type flat_type gflat_type h_type unqiueness1 by blast
        then have h_is_sharp_prod_fflat_gflat: "h = \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
          by (metis assms h_type sharp_cancels_flat)
        then show "h = \<langle>(left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h)\<^sup>\<flat>,(right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h)\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
          using h_property1 h_property2 by force
      qed
    qed
  qed
  then show "(X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<cong> X\<^bsup>A\<^esup> \<times>\<^sub>c Y\<^bsup>A\<^esup>"
    using canonical_cart_prod_is_cart_prod cart_prods_isomorphic fst_conv is_isomorphic_def by fastforce
qed

lemma zero_to_X:
  assumes "nonempty(X)"
  shows "\<emptyset>\<^bsup>X\<^esup> \<cong> \<emptyset>"
proof-
  obtain j where j_type: "j: \<emptyset>\<^bsup>X\<^esup> \<rightarrow> one\<times>\<^sub>c \<emptyset>\<^bsup>X\<^esup>  \<and> isomorphism(j)"
    using is_isomorphic_def isomorphic_is_symmetric one_x_A_iso_A by presburger
  obtain y where y_type: "y \<in>\<^sub>c X"
    using assms nonempty_def by blast
  have y_id_type: "y \<times>\<^sub>f id(\<emptyset>\<^bsup>X\<^esup>) : one \<times>\<^sub>c \<emptyset>\<^bsup>X\<^esup>  \<rightarrow> X\<times>\<^sub>c \<emptyset>\<^bsup>X\<^esup> "
    by (simp add: cfunc_cross_prod_type id_type y_type)
  obtain e where e_type: "e: X\<times>\<^sub>c \<emptyset>\<^bsup>X\<^esup> \<rightarrow> \<emptyset>"
    using eval_func_type by blast
  have iso_type: "(e \<circ>\<^sub>c y \<times>\<^sub>f id(\<emptyset>\<^bsup>X\<^esup>)) \<circ>\<^sub>c j :  \<emptyset>\<^bsup>X\<^esup> \<rightarrow> \<emptyset>"
    using e_type j_type y_id_type comp_type by auto
  show "\<emptyset>\<^bsup>X\<^esup> \<cong> \<emptyset>"
    using cfunc_type_def function_to_empty_is_iso is_isomorphic_def iso_type by blast
qed


(*Bad version... see Coproduct Theory file for good version*)
(* Proposition 2.5.10 *)
lemma prod_distribute_coprod:
  assumes "\<And>X A Y B. X\<^bsup>A\<^esup> = Y\<^bsup>B\<^esup> \<Longrightarrow> X = Y \<and> A = B"
  shows "A \<times>\<^sub>c (X \<Coprod> Y) \<cong> (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y)"
proof - 
  obtain \<phi> where phi_def: "\<phi> = (id(A) \<times>\<^sub>f left_coproj X Y) \<amalg> (id(A) \<times>\<^sub>f right_coproj X Y)"
    by simp
  obtain \<psi> where psi_def: "\<psi> = ((left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> \<amalg> (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>)\<^sup>\<flat>"
    by simp

  have phi_type: "\<phi> : (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y) \<rightarrow> A \<times>\<^sub>c (X \<Coprod> Y)"
    by (simp add: phi_def cfunc_coprod_type cfunc_cross_prod_type id_type left_proj_type right_proj_type)
  then have phi_A_type: "\<phi>\<^bsup>A\<^esup>\<^sub>f : ((A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y))\<^bsup>A\<^esup> \<rightarrow>  (A \<times>\<^sub>c (X \<Coprod> Y))\<^bsup>A\<^esup>"
    by (simp add: exp_func_type)
  have j0sharp_type:  "(left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> : X  \<rightarrow>  ((A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y))\<^bsup>A\<^esup>"
    by typecheck_cfuncs
  have j1sharp_type:  "(right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> : Y  \<rightarrow>  ((A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y))\<^bsup>A\<^esup>"
    by typecheck_cfuncs
  then have j0sharpUj1sharp_type: "(left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> \<amalg> (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> : X \<Coprod> Y \<rightarrow>  ((A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y))\<^bsup>A\<^esup>"
    by (simp add: cfunc_coprod_type j0sharp_type)
  then have psi_type: "\<psi> : A \<times>\<^sub>c (X \<Coprod> Y) \<rightarrow> (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y)"
    using assms flat_type psi_def by blast
  have idAxi0_type: "id(A)\<times>\<^sub>f left_coproj X Y : (A \<times>\<^sub>c X) \<rightarrow> A \<times>\<^sub>c (X \<Coprod> Y)"
    by (simp add: cfunc_cross_prod_type id_type left_proj_type)
  have idAxi1_type: "id(A)\<times>\<^sub>f right_coproj X Y : (A \<times>\<^sub>c Y) \<rightarrow> A \<times>\<^sub>c (X \<Coprod> Y)"
    by (simp add: cfunc_cross_prod_type id_type right_proj_type)
  then have phi_j0_Eqs_idAxi0: "\<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)) = id(A) \<times>\<^sub>f (left_coproj X Y)"
    using idAxi0_type left_coproj_cfunc_coprod phi_def by auto 
  then have phi_j1_Eqs_idAxi1: "\<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)) = id(A) \<times>\<^sub>f (right_coproj X Y)"
    using idAxi0_type idAxi1_type right_coproj_cfunc_coprod phi_def by blast
  have  gsharp_type:  "(id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> : (X \<Coprod> Y) \<rightarrow> ((A \<times>\<^sub>c (X \<Coprod> Y)))\<^bsup>A\<^esup>"
    by typecheck_cfuncs
   (*Below is first centered eqn on page 52*)
  have FirstCenteredEqn1: "((id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> \<circ>\<^sub>c (left_coproj X Y))\<^sup>\<flat> =  id(A) \<times>\<^sub>f (left_coproj X Y)"
    by (smt assms cfunc_type_def flat_cancels_sharp gsharp_type idAxi0_type id_left_unit id_type inv_transpose_of_composition left_proj_type)
  have FirstCenteredEqn2: "((id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> \<circ>\<^sub>c (right_coproj X Y))\<^sup>\<flat> = id(A) \<times>\<^sub>f (right_coproj X Y)"
    by (metis assms cfunc_type_def eval_of_id_cross_id_sharp1 gsharp_type idAxi1_type id_left_unit inv_transpose_func_def2 inv_transpose_of_composition right_proj_type)
  then have SecondCenteredEqn: "(id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> = ((id(A) \<times>\<^sub>f left_coproj X Y)\<^sup>\<sharp>) \<amalg> ((id(A) \<times>\<^sub>f right_coproj X Y)\<^sup>\<sharp>)"
    by (smt assms cfunc_coprod_unique cfunc_type_def codomain_comp domain_comp FirstCenteredEqn1 gsharp_type left_proj_type right_proj_type sharp_cancels_flat)
  then have AlsoHaveEquation1: "(id(A) \<times>\<^sub>f (left_coproj X Y))\<^sup>\<sharp> = (\<phi>\<^bsup>A\<^esup>\<^sub>f)  \<circ>\<^sub>c  (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    using left_proj_type phi_j0_Eqs_idAxi0 phi_type transpose_of_comp by fastforce
  then have AlsoHaveEquation2: "(id(A) \<times>\<^sub>f (right_coproj X Y))\<^sup>\<sharp> = (\<phi>\<^bsup>A\<^esup>\<^sub>f)  \<circ>\<^sub>c  (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    using phi_j1_Eqs_idAxi1 phi_type right_proj_type transpose_of_comp by fastforce
  then have ThirdCenteredEqn: "(id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> = 
      (\<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>) 
       \<amalg>
      (\<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>) "
    by (simp add: AlsoHaveEquation1 SecondCenteredEqn)
  also have " ... =  \<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c ((left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> \<amalg> (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>)"
    using cfunc_coprod_comp j0sharp_type j1sharp_type phi_A_type by auto
(*below is fourth centered equation:  (phi o psi)# = phi^A o (j0#Uj1#) = g# *)
  then have computation1: 
    "(\<phi> \<circ>\<^sub>c \<psi>)\<^sup>\<sharp> 
      = \<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> \<amalg> (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    by (smt assms psi_def flat_type j0sharpUj1sharp_type phi_type sharp_cancels_flat transpose_of_comp)
  thm calculation
  have computation2:  "... = (id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp>"
    by (simp add: \<open>(\<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)\<^sup>\<sharp>) \<amalg> (\<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)\<^sup>\<sharp>) = \<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)\<^sup>\<sharp> \<amalg> right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)\<^sup>\<sharp>\<close> calculation)
  then have HalfInverse: 
      "\<phi> \<circ>\<^sub>c \<psi> =  id(A \<times>\<^sub>c (X \<Coprod> Y))"
    by (metis (mono_tags, lifting) comp_type computation1 eval_of_id_cross_id_sharp1 phi_type psi_type transpose_func_def)
(*Below is the 5th centered equation: (psi o phi o j0)# = psiA o (phi o j0)# = psiA o g# o i0 = psi# o i0 = j0# *)
(*We got lucky in that we were able to get  (psi o phi o j0)# =  j0# in a single go and avoid the middle bits!*)
  thm psi_def
  have FifthCenteredEquation: 
    "(\<psi> \<circ>\<^sub>c \<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)))\<^sup>\<sharp>  = (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    by (smt assms inv_transpose_of_composition j0sharpUj1sharp_type j0sharp_type j1sharp_type left_coproj_cfunc_coprod left_proj_type phi_j0_Eqs_idAxi0 psi_def sharp_cancels_flat)
  then have PsiPhiJ0EqsJ0 : 
    "\<psi> \<circ>\<^sub>c \<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)) = left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)"
    by (metis comp_type flat_cancels_sharp idAxi0_type left_proj_type phi_j0_Eqs_idAxi0 psi_type)
    
  then have PsiPhiJ1EqsJ1: 
    "\<psi> \<circ>\<^sub>c \<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)) = right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)"
    by (metis flat_cancels_sharp inv_transpose_of_composition j0sharpUj1sharp_type j0sharp_type
        j1sharp_type phi_j1_Eqs_idAxi1 psi_def right_coproj_cfunc_coprod right_proj_type)
    
  have psiphi_type: "\<psi> \<circ>\<^sub>c \<phi> : (A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y \<rightarrow> (A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y"
    using comp_type phi_type psi_type by auto
    thm phi_type psi_type
    then have fullinverse: "\<psi> \<circ>\<^sub>c \<phi> = id((A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y)"
      by (smt PsiPhiJ0EqsJ0 PsiPhiJ1EqsJ1 cfunc_coprod_comp cfunc_coprod_unique idAxi0_type
          idAxi1_type id_left_unit2 id_type left_proj_type phi_def phi_j0_Eqs_idAxi0
          phi_j1_Eqs_idAxi1 psi_type right_proj_type)
      
  show "A \<times>\<^sub>c X \<Coprod> Y \<cong> (A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y"
    unfolding is_isomorphic_def isomorphism_def
    using psi_type phi_type fullinverse HalfInverse cfunc_type_def
    by (rule_tac x="\<psi>" in exI, auto)
qed




(* Definition 2.5.11 *)
definition powerset :: "cset \<Rightarrow> cset" ("\<P>_" [101]100) where
  "\<P> X = \<Omega>\<^bsup>X\<^esup>"

(* Definition 2.6.1: Finite and Infinite Sets *)
definition is_finite :: "cset \<Rightarrow> bool"  where
   "is_finite(X) \<longleftrightarrow> (\<forall>m. (m : X \<rightarrow> X \<and> monomorphism(m)) \<longrightarrow>  isomorphism(m))"

definition is_infinite :: "cset \<Rightarrow> bool"  where
   "is_infinite(X) \<longleftrightarrow> (\<exists> m. (m : X \<rightarrow> X \<and> monomorphism(m) \<and> \<not>surjective(m)))"





(* Definition 2.6.2 *)
definition is_smaller_than :: "cset \<Rightarrow> cset \<Rightarrow> bool" (infix "\<le>\<^sub>c" 50) where
   "X \<le>\<^sub>c Y \<longleftrightarrow> (\<exists> m. m : X \<rightarrow> Y \<and> monomorphism(m))"

(*Proposition 2.6.3*)

lemma smaller_than_coproduct1:
  "X \<le>\<^sub>c (X\<Coprod>Y)"
  using is_smaller_than_def left_coproj_are_monomorphisms left_proj_type by blast

lemma  smaller_than_coproduct2:
  "X \<le>\<^sub>c (Y\<Coprod>X)"
  using is_smaller_than_def right_coproj_are_monomorphisms right_proj_type by blast

(*Proposition 2.6.4*)
lemma smaller_than_product1:
  assumes "nonempty(Y)"
  shows "X \<le>\<^sub>c (X \<times>\<^sub>c Y)"
  unfolding is_smaller_than_def  
proof-
  obtain y where y_type: "y \<in>\<^sub>c Y"
  using assms nonempty_def by blast
  have map_type: "\<langle>id(X),y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> (X \<times>\<^sub>c Y)"
   using y_type cfunc_prod_type cfunc_type_def codomain_comp domain_comp id_type terminal_func_type by auto
  have mono: "monomorphism(\<langle> id(X),y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"
    using map_type
  proof (unfold monomorphism_def3, auto)
    fix g h A
    assume g_h_types: "g : A \<rightarrow> X" "h : A \<rightarrow> X"
    
    assume "\<langle>id\<^sub>c X,y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g = \<langle>id\<^sub>c X,y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c h"
    then have "\<langle>id\<^sub>c X \<circ>\<^sub>c g, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g\<rangle>  = \<langle>id\<^sub>c X \<circ>\<^sub>c h, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h\<rangle>"
      using y_type g_h_types by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 comp_type)
    then have "\<langle>g, y \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>\<rangle>  = \<langle>h, y \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>\<rangle>"
      using y_type g_h_types id_left_unit2 terminal_func_comp by (typecheck_cfuncs, auto)
    then show "g = h"
      using g_h_types y_type
      by (metis (full_types) comp_type left_cart_proj_cfunc_prod terminal_func_type)
  qed


  show "\<exists>m. m : X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism m"
    using mono map_type by auto
qed

lemma smaller_than_product2:
  assumes "nonempty(Y)"
  shows "X \<le>\<^sub>c (Y \<times>\<^sub>c X)"
  unfolding is_smaller_than_def  
proof - 
  have "X \<le>\<^sub>c (X \<times>\<^sub>c Y)"
    by (simp add: assms smaller_than_product1)
  then obtain m where m_def: "m : X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism m"
    using is_smaller_than_def by blast
  obtain i  where "i : (X \<times>\<^sub>c Y) \<rightarrow> (Y \<times>\<^sub>c X) \<and> isomorphism i"
    using is_isomorphic_def product_commutes by blast
  then have "i \<circ>\<^sub>c m : X \<rightarrow>  (Y \<times>\<^sub>c X) \<and> monomorphism(i \<circ>\<^sub>c m)"
    using cfunc_type_def comp_type composition_of_monic_pair_is_monic iso_imp_epi_and_monic m_def by auto
  then show "\<exists>m. m : X \<rightarrow> Y \<times>\<^sub>c X \<and> monomorphism m"
    by blast
qed





lemma all_emptysets_are_finite:
  assumes "\<not>(nonempty(X))"
  shows "is_finite(X)"
  by (metis CollectI assms epi_mon_is_iso epimorphism_def3 is_finite_def nonempty_def one_separator)





lemma emptyset_is_smallest_set:
  "\<emptyset> \<le>\<^sub>c X"
  using empty_subset is_smaller_than_def subobject_of_def2 by auto


lemma smaller_than_finite_is_finite:
  assumes "X \<le>\<^sub>c Y" "is_finite(Y)" "nonempty(X)"
  shows "is_finite(X)"
  unfolding _is_finite_def
proof(auto)
  fix m
  assume m_type: "m : X \<rightarrow> X"
  assume m_mono: "monomorphism m"

  have j_exists: "\<exists>j. j: X \<rightarrow> Y \<and> monomorphism j"
    using assms(1) is_smaller_than_def by blast
  then obtain j where j_def: "j: X \<rightarrow> Y \<and> monomorphism j"
    by blast
  show "isomorphism m"
  proof(rule ccontr)
    assume not_iso: "\<not> isomorphism m"
    have not_surj: "\<not> surjective m"
      by (meson CollectI epi_mon_is_iso m_mono not_iso surjective_is_epimorphism)

    then have not_surj0: "\<not>(\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<exists>z. (z \<in>\<^sub>c X \<and> m \<circ>\<^sub>c z = x)))"
      using cfunc_type_def m_type surjective_def by auto
    then have not_surj1: "(\<exists>x. x \<in>\<^sub>c X \<longrightarrow> (\<forall> z. (z \<in>\<^sub>c X \<and> m \<circ>\<^sub>c z \<noteq> x)))"
      by auto
    then have not_surj2: "(\<exists>x. x \<in>\<^sub>c X \<and> (\<forall> z. (z \<in>\<^sub>c X \<and> m \<circ>\<^sub>c z \<noteq> x)))"
      apply typecheck_cfuncs
      oops
    (*then obtain x where x_def: "x \<in>\<^sub>c X \<and> (\<forall> z. (z \<in>\<^sub>c X \<and> m \<circ>\<^sub>c z \<noteq> x))"
      apply typecheck_cfuncs
*)



end