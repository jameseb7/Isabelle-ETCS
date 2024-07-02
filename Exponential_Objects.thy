theory Exponential_Objects
  imports Empty
begin


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


section \<open>Sharp, Flat, Evaluation, and Exponentiation Operators\<close>


lemma eval_func_surj:
  assumes "nonempty(A)"
  shows "surjective((eval_func X A))"
  unfolding surjective_def
proof(auto)
  fix x
  assume x_type: "x \<in>\<^sub>c codomain (eval_func X A)"
  then have x_type2[type_rule]: "x \<in>\<^sub>c X"
    using cfunc_type_def eval_func_type by auto
  obtain a where a_def[type_rule]: "a \<in>\<^sub>c A"
    using assms nonempty_def by auto
  have needed_type: "\<langle>a, (x \<circ>\<^sub>c right_cart_proj A one)\<^sup>\<sharp>\<rangle> \<in>\<^sub>c domain (eval_func X A)"
    using cfunc_type_def by (typecheck_cfuncs, auto)
  have "(eval_func X A) \<circ>\<^sub>c  \<langle>a, (x \<circ>\<^sub>c right_cart_proj A one)\<^sup>\<sharp>\<rangle> =    
        (eval_func X A) \<circ>\<^sub>c ((id(A) \<times>\<^sub>f (x \<circ>\<^sub>c right_cart_proj A one)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a, id(one)\<rangle>)"
    by (typecheck_cfuncs, smt a_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 x_type2)
  also have "... = ((eval_func X A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (x \<circ>\<^sub>c right_cart_proj A one)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>a, id(one)\<rangle>"
    by (typecheck_cfuncs, meson a_def comp_associative2 x_type2)
  also have "... = (x \<circ>\<^sub>c right_cart_proj A one) \<circ>\<^sub>c \<langle>a, id(one)\<rangle>"
    by (metis comp_type right_cart_proj_type transpose_func_def x_type2) 
  also have "... = x \<circ>\<^sub>c (right_cart_proj A one \<circ>\<^sub>c \<langle>a, id(one)\<rangle>)"
    using a_def cfunc_type_def comp_associative x_type2 by (typecheck_cfuncs, auto)
  also have "... = x"
    using a_def id_right_unit2 right_cart_proj_cfunc_prod x_type2 by (typecheck_cfuncs, auto)
  then show "\<exists>y. y \<in>\<^sub>c domain (eval_func X A) \<and> eval_func X A \<circ>\<^sub>c y = x"
    using calculation needed_type by (typecheck_cfuncs, auto)
qed





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

lemma exp_of_id_is_id_of_exp:
  "id(X\<^bsup>A\<^esup>) = (id(X))\<^bsup>A\<^esup>\<^sub>f"
  by (metis (no_types) eval_func_type exp_func_def exponential_object_identity id_domain id_left_unit2)


(* Note below Definition 2.5.1 *)
lemma exponential_square_diagram:
  assumes "g : Y \<rightarrow> Z"
  shows "(eval_func Z A) \<circ>\<^sub>c (id\<^sub>c(A)\<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f)  = g \<circ>\<^sub>c (eval_func Y A)"
  using assms by (typecheck_cfuncs, simp add: exp_func_def2 transpose_func_def)

(* Proposition 2.5.2 *)
lemma transpose_of_comp:
  assumes f_type: "f: A \<times>\<^sub>c X \<rightarrow> Y" and g_type: "g: Y \<rightarrow> Z"
  shows "f: A \<times>\<^sub>c X \<rightarrow> Y \<and> g: Y \<rightarrow> Z  \<Longrightarrow>  (g \<circ>\<^sub>c f)\<^sup>\<sharp> = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>"
proof auto
  have left_eq: "(eval_func Z A) \<circ>\<^sub>c(id(A) \<times>\<^sub>f (g \<circ>\<^sub>c f)\<^sup>\<sharp>) = g \<circ>\<^sub>c f"
    using comp_type f_type g_type transpose_func_def by blast
  have right_eq: "(eval_func Z A) \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>)) = g \<circ>\<^sub>c f"
  proof - 
    have "(eval_func Z A) \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>)) =
                   (eval_func Z A) \<circ>\<^sub>c ((id\<^sub>c A \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f)) \<circ>\<^sub>c  (id\<^sub>c A \<times>\<^sub>f f\<^sup>\<sharp>))"
      by (typecheck_cfuncs, smt identity_distributes_across_composition assms)
    also have "... = (g \<circ>\<^sub>c eval_func Y A) \<circ>\<^sub>c  (id\<^sub>c A \<times>\<^sub>f f\<^sup>\<sharp>)"
      by (typecheck_cfuncs, smt comp_associative2 exp_func_def2 transpose_func_def assms)
    also have "... = g \<circ>\<^sub>c f"
      by (typecheck_cfuncs, smt (verit, best) comp_associative2 transpose_func_def assms)
    then show ?thesis
      by (simp add: calculation)
  qed
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
  "f\<^sup>\<flat> = (THE g. \<exists> Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f))"


(*
lemma inv_transpose_func_def2:
  assumes f_type[type_rule]: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> = (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f)"
  unfolding inv_transpose_func_def
proof (rule theI)
  show "(THE g. \<exists>Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f) =
    eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f"
    by (smt (verit, ccfv_SIG) cfunc_type_def exp_set_inj the_equality assms)
  show "\<And>x. (THE g. \<exists>Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f) =
         eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f \<Longrightarrow>
         x = (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f)"
    using assms apply typecheck_cfuncs
*)


lemma inv_transpose_func_def2:
  assumes "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> = (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f)"
  unfolding inv_transpose_func_def
proof (rule theI2)
  show "\<exists>Z Y B. domain f = Z \<and> codomain f = Y\<^bsup>B\<^esup> \<and> eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f = eval_func Y B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f f"
    using assms cfunc_type_def by blast
next
  fix g
  assume "\<exists>Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f"
  then show "g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f"
    by (metis assms cfunc_type_def exp_set_inj)
next
  fix g 
  assume "\<exists>Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f"
  then show "g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f"
    by (metis assms cfunc_type_def exp_set_inj)
qed




(*
(*We changed the definition above... and it is easily proved!*)
(*Indeed the inv_transpose is uniquely defined*)
lemma inv_transpose_func_unique: 
  assumes "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> = (THE g. \<exists> Z X A. domain f = Z \<and> codomain f = X\<^bsup>A\<^esup> \<and> g = (eval_func X A) \<circ>\<^sub>c (id A \<times>\<^sub>f f))"
  by (smt (verit, best) assms cfunc_type_def inv_transpose_func_def2 theI)
*)



lemma flat_type[type_rule]:
  assumes f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X"
  by (subst inv_transpose_func_def2[where Z=Z, where X=X, where A=A], simp add: assms,
      meson cfunc_cross_prod_type comp_type eval_func_type f_type id_type)






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
 "f: Z \<rightarrow> X\<^bsup>A\<^esup>  \<Longrightarrow> (f\<^sup>\<flat>)\<^sup>\<sharp> = f"
proof - 
  assume f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  then have uniqueness: "\<forall> g. g : Z \<rightarrow> X\<^bsup>A\<^esup> \<longrightarrow> eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f g) = f\<^sup>\<flat> \<longrightarrow> g = (f\<^sup>\<flat>)\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: transpose_func_unique)
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




lemma exponential_object_identity2: 
  "id(X)\<^bsup>A\<^esup>\<^sub>f = id\<^sub>c(X\<^bsup>A\<^esup>)"
  by (metis eval_func_type exp_func_def exponential_object_identity id_domain id_left_unit2)

lemma transpose_factors: 
  assumes "f: X \<rightarrow> Y"
  assumes "g: Y \<rightarrow> Z"
  shows "(g \<circ>\<^sub>c f)\<^bsup>A\<^esup>\<^sub>f = (g\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (f\<^bsup>A\<^esup>\<^sub>f)"
  using assms by (typecheck_cfuncs, smt comp_associative2 comp_type eval_func_type exp_func_def2 transpose_of_comp)


lemma eval_func_X_empty_injective:
  assumes "is_empty Y"
  shows "injective (eval_func X Y)"
  unfolding injective_def
  by (typecheck_cfuncs,metis assms cfunc_type_def comp_type left_cart_proj_type is_empty_def)
  
lemma flat_pres_epi:
  assumes "nonempty(A)"
  assumes "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  assumes "epimorphism(f)"
  shows "epimorphism(f\<^sup>\<flat>)"
proof - 
  have equals: "f\<^sup>\<flat> = (eval_func X A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
    using assms(2) inv_transpose_func_def2 by auto
  have idA_f_epi: "epimorphism((id(A) \<times>\<^sub>f f))"
    using assms(2) assms(3) cfunc_cross_prod_surj epi_is_surj id_isomorphism id_type iso_imp_epi_and_monic surjective_is_epimorphism by blast
  have eval_epi: "epimorphism((eval_func X A))"
    by (simp add: assms(1) eval_func_surj surjective_is_epimorphism)
  have "codomain ((id(A) \<times>\<^sub>f f)) = domain ((eval_func X A))"
    using assms(2) cfunc_type_def by (typecheck_cfuncs, auto)
  then show ?thesis
    by (simp add: composition_of_epi_pair_is_epi equals eval_epi idA_f_epi)
qed









lemma transpose_inj_is_inj:
  assumes "g: X \<rightarrow> Y"
  assumes "injective(g)"
  shows "injective(g\<^bsup>A\<^esup>\<^sub>f)"
  unfolding injective_def
proof(auto)
  fix x y 
  assume x_type[type_rule]: "x \<in>\<^sub>c domain (g\<^bsup>A\<^esup>\<^sub>f)" 
  assume y_type[type_rule]:"y \<in>\<^sub>c domain (g\<^bsup>A\<^esup>\<^sub>f)"
  assume eqs: "g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c x = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c y"
  have mono_g: "monomorphism g"
    by (meson CollectI assms(2) injective_imp_monomorphism) 
  have x_type'[type_rule]: "x \<in>\<^sub>c  X\<^bsup>A\<^esup>"
    using assms(1) cfunc_type_def exp_func_type by (typecheck_cfuncs, force)
  have y_type'[type_rule]: "y \<in>\<^sub>c  X\<^bsup>A\<^esup>"
    using cfunc_type_def x_type x_type' y_type by presburger  
  have "(g \<circ>\<^sub>c eval_func X A)\<^sup>\<sharp> \<circ>\<^sub>c x = (g \<circ>\<^sub>c eval_func X A)\<^sup>\<sharp> \<circ>\<^sub>c y"
    unfolding exp_func_def using assms eqs exp_func_def2 by force 
  then have "g \<circ>\<^sub>c (eval_func X A \<circ>\<^sub>c(id(A) \<times>\<^sub>f  x)) = g \<circ>\<^sub>c (eval_func X A \<circ>\<^sub>c (id(A) \<times>\<^sub>f  y))"
    by (smt (z3) assms(1) comp_type eqs flat_cancels_sharp flat_type inv_transpose_func_def2 sharp_cancels_flat transpose_of_comp x_type' y_type')
  then have "eval_func X A \<circ>\<^sub>c(id(A) \<times>\<^sub>f  x) =   eval_func X A \<circ>\<^sub>c (id(A) \<times>\<^sub>f  y)"  
    by (metis assms(1) mono_g flat_type inv_transpose_func_def2  monomorphism_def2 x_type' y_type')
  then show "x = y"
    by (meson same_evals_equal x_type' y_type')
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
    have "A\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle> = B\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(one), id(one)\<rangle>"
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
    then have "A\<^sup>\<flat> = B\<^sup>\<flat>"
      by (typecheck_cfuncs, smt swap_def a_def b_def cfunc_prod_comp comp_associative2 diagonal_def diagonal_type id_right_unit2 id_type left_cart_proj_type right_cart_proj_type swap_idempotent swap_type terminal_func_comp terminal_func_unique)

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



lemma sharp_pres_mono:
  assumes "f : A \<times>\<^sub>c Z \<rightarrow> X"
  assumes "monomorphism(f)"
  assumes "nonempty A"
  shows   "monomorphism(f\<^sup>\<sharp>)"
  unfolding monomorphism_def2
proof(auto)
  fix g h U Y x
  assume g_type[type_rule]: "g : U \<rightarrow> Y"
  assume h_type[type_rule]: "h : U \<rightarrow> Y"
  assume f_sharp_type[type_rule]: "f\<^sup>\<sharp> : Y \<rightarrow> x"
  assume equals: "f\<^sup>\<sharp> \<circ>\<^sub>c g = f\<^sup>\<sharp> \<circ>\<^sub>c h"



  have f_sharp_type2: "f\<^sup>\<sharp> : Z \<rightarrow> X\<^bsup>A\<^esup>"
    by (simp add: assms(1) transpose_func_type)
  have Y_is_Z: "Y = Z"
    using cfunc_type_def f_sharp_type f_sharp_type2 by auto
  have x_is_XA: "x = X\<^bsup>A\<^esup>"
    using cfunc_type_def f_sharp_type f_sharp_type2 by auto
  have g_type2: "g : U \<rightarrow> Z"
    using Y_is_Z g_type by blast
  have h_type2: "h : U \<rightarrow> Z"
    using Y_is_Z h_type by blast
  have idg_type: "(id(A) \<times>\<^sub>f g) : A \<times>\<^sub>c U \<rightarrow> A \<times>\<^sub>c Z"
    by (simp add: cfunc_cross_prod_type g_type2 id_type)
  have idh_type: "(id(A) \<times>\<^sub>f h) : A \<times>\<^sub>c U \<rightarrow> A \<times>\<^sub>c Z"
    by (simp add: cfunc_cross_prod_type h_type2 id_type)


   then  have epic: "epimorphism(right_cart_proj A U)"
     using assms(3) nonempty_left_imp_right_proj_epimorphism by blast



   have fIdg_is_fIdh: "f \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) = f \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)"
   proof - 
    have "f \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) = (eval_func X A \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g)"
      using assms(1) transpose_func_def by auto
    also have "... = eval_func X A \<circ>\<^sub>c ((id(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g))"
      using comp_associative2 f_sharp_type2 idg_type by (typecheck_cfuncs, fastforce)
    also have "... = eval_func X A \<circ>\<^sub>c (id(A) \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c g))"
      using f_sharp_type2 g_type2 identity_distributes_across_composition by auto
    also have "... = eval_func X A \<circ>\<^sub>c (id(A) \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c h))"
      by (simp add: equals)
    also have "... = eval_func X A \<circ>\<^sub>c ((id(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (id(A) \<times>\<^sub>f h))"
      using f_sharp_type h_type identity_distributes_across_composition by auto
    also have "... = (eval_func X A \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)"
      by (metis Y_is_Z assms(1) calculation equals f_sharp_type2 g_type h_type inv_transpose_func_def2 inv_transpose_of_composition transpose_func_def)
    also have "... = f \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)"
      using assms(1) transpose_func_def by auto
    then show ?thesis
      by (simp add: calculation)   
   qed
   then have idg_is_idh: "(id(A) \<times>\<^sub>f g) = (id(A) \<times>\<^sub>f h)"
    using assms fIdg_is_fIdh idg_type idh_type monomorphism_def3 by blast
   then have "g \<circ>\<^sub>c (right_cart_proj A U) = h \<circ>\<^sub>c (right_cart_proj A U)"
    by (smt g_type2 h_type2 id_type right_cart_proj_cfunc_cross_prod)
   then show "g = h"
    using epic epimorphism_def2 g_type2 h_type2 right_cart_proj_type by blast
qed


(*non empty is required, consider when X = Omega and A = empty set*)




section \<open>Metafunctions and the Cnufatems\<close>

subsection \<open>Metafunctions\<close>


(*Meta-function Definition *)
definition metafunc :: "cfunc \<Rightarrow> cfunc" where
  "metafunc f \<equiv> (f \<circ>\<^sub>c (left_cart_proj (domain f) one))\<^sup>\<sharp>"

lemma metafunc_def2:
  assumes "f : X \<rightarrow> Y"
  shows "metafunc f = (f \<circ>\<^sub>c (left_cart_proj X one))\<^sup>\<sharp>"
  using assms unfolding metafunc_def cfunc_type_def by auto




lemma metafunc_type[type_rule]:
  assumes "f : X \<rightarrow> Y"
  shows "metafunc f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  using assms by (unfold metafunc_def2, typecheck_cfuncs)

lemma eval_lemma:
  assumes "f : X \<rightarrow> Y"
  assumes "x  \<in>\<^sub>c X"
  shows "eval_func Y X \<circ>\<^sub>c \<langle>x, metafunc f\<rangle> = f \<circ>\<^sub>c x"
proof - 
  have "eval_func Y X \<circ>\<^sub>c \<langle>x, metafunc f\<rangle> = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f \<circ>\<^sub>c (left_cart_proj X one))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x, id one\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 metafunc_def2)
  also have "... = (eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (f \<circ>\<^sub>c (left_cart_proj X one))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, id one\<rangle>"
    using assms comp_associative2 by (typecheck_cfuncs, blast)
  also have "... =   (f \<circ>\<^sub>c (left_cart_proj X one)) \<circ>\<^sub>c \<langle>x, id one\<rangle>"
    using assms by (typecheck_cfuncs, metis transpose_func_def)
  also have "... = f \<circ>\<^sub>c x"
    by (typecheck_cfuncs, metis assms cfunc_type_def comp_associative left_cart_proj_cfunc_prod)
  then show "eval_func Y X \<circ>\<^sub>c \<langle>x, metafunc f\<rangle> = f \<circ>\<^sub>c x"
    by (simp add: calculation)
qed

subsection \<open>Cnufatems\<close>

(*Noitcnuf-atem Definition*)

definition cnufatem :: "cfunc \<Rightarrow> cfunc" where
  "cnufatem f = (THE g. \<forall> Y X. f : one \<rightarrow> Y\<^bsup>X\<^esup> \<longrightarrow> g = eval_func Y X \<circ>\<^sub>c \<langle>id X, f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"


lemma cnufatem_def2:
  assumes "f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "cnufatem f = eval_func Y X \<circ>\<^sub>c \<langle>id X, f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
  using assms unfolding cnufatem_def cfunc_type_def
  by (smt (verit, ccfv_threshold) exp_set_inj theI') 

lemma cnufatem_type[type_rule]:
  assumes "f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "cnufatem f : X  \<rightarrow> Y"
  using assms cnufatem_def2 
  by (auto, typecheck_cfuncs)


  

lemma cnufatem_metafunc:
  assumes "f : X \<rightarrow> Y"
  shows "cnufatem (metafunc f) = f"
proof(rule one_separator[where X = X, where Y = Y])
  show "cnufatem (metafunc f) : X \<rightarrow> Y"
    using assms by typecheck_cfuncs
  show "f : X \<rightarrow> Y"
    using assms by simp
  show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> cnufatem (metafunc f) \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
  proof -
    fix x
    assume x_type[type_rule]: "x \<in>\<^sub>c X"

    have "cnufatem (metafunc f) \<circ>\<^sub>c x =  eval_func Y X \<circ>\<^sub>c \<langle>id X, (metafunc f) \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      using assms cnufatem_def2 comp_associative2 by (typecheck_cfuncs, fastforce)
    also have "... = eval_func Y X \<circ>\<^sub>c \<langle>x, (metafunc f)\<rangle>"
      by (typecheck_cfuncs, metis assms cart_prod_extract_left)
    also have "... = f \<circ>\<^sub>c x"
      using assms eval_lemma by (typecheck_cfuncs, presburger)
    then show "cnufatem (metafunc f) \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
      by (simp add: calculation)
  qed
qed


lemma metafunc_cnufatem:
  assumes "f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "metafunc (cnufatem f) = f"
proof
(rule same_evals_equal[where Z = one, where X = Y, where A = X])
  show "metafunc (cnufatem f) \<in>\<^sub>c Y\<^bsup>X\<^esup>"
    using assms by typecheck_cfuncs
  show "f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
    using assms by simp 
  show "eval_func Y X \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f (metafunc (cnufatem f))) = eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f"
  proof(rule one_separator[where X = "X \<times>\<^sub>c one", where Y = Y])
    show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f (metafunc (cnufatem f)) : X \<times>\<^sub>c one \<rightarrow> Y"
      using assms by (typecheck_cfuncs)
    show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f : X \<times>\<^sub>c one \<rightarrow> Y"
      using assms by typecheck_cfuncs
  next 
    fix x1
    assume x1_type[type_rule]: "x1 \<in>\<^sub>c X \<times>\<^sub>c one"
    then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and x_def: " x1 = \<langle>x, id one\<rangle>"
      by (typecheck_cfuncs, metis cart_prod_decomp one_unique_element)
    have "(eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f metafunc (cnufatem f)) \<circ>\<^sub>c \<langle>x, id one\<rangle> =
           eval_func Y X \<circ>\<^sub>c \<langle>x , metafunc (cnufatem f)\<rangle>"
      using assms by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2)
    also have "... = (cnufatem f) \<circ>\<^sub>c x"
      using assms eval_lemma by (typecheck_cfuncs, presburger)
    also have "... = (eval_func Y X \<circ>\<^sub>c \<langle>id X, f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x"
      using assms cnufatem_def2 by presburger
    also have "... = eval_func Y X \<circ>\<^sub>c \<langle>id X, f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      by (typecheck_cfuncs, metis assms comp_associative2)
    also have "... = eval_func Y X \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x , f \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x)\<rangle>"
      by (typecheck_cfuncs, metis assms cart_prod_extract_left id_left_unit2 id_right_unit2 terminal_func_comp_elem)
    also have "... = eval_func Y X \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x , f \<circ>\<^sub>c id one\<rangle>"
      by (simp add: terminal_func_comp_elem x_type)
    also have "... = eval_func Y X \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>x, id one\<rangle>"
      using assms cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
    also have "... = (eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f) \<circ>\<^sub>c x1"
      by (typecheck_cfuncs,metis assms comp_associative2 x_def)
    then show "(eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f metafunc (cnufatem f)) \<circ>\<^sub>c x1 = (eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f) \<circ>\<^sub>c x1"
      using  calculation x_def by presburger
  qed
qed


subsection \<open>Meta Composition\<close>


(*Meta-function Composition *)

definition meta_comp :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc"  where 
  "meta_comp X Y Z  =  (eval_func Z Y \<circ>\<^sub>c swap  (Z\<^bsup>Y\<^esup>) Y    \<circ>\<^sub>c (id(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func Y X \<circ>\<^sub>c  swap (Y\<^bsup>X\<^esup>)  X )  )  \<circ>\<^sub>c (associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X)  \<circ>\<^sub>c swap X ((Z\<^bsup>Y\<^esup>) \<times>\<^sub>c (Y\<^bsup>X\<^esup>)) )\<^sup>\<sharp> "

lemma meta_comp_type[type_rule]:
  "meta_comp X Y Z : Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Z\<^bsup>X\<^esup>"
  unfolding meta_comp_def by typecheck_cfuncs





definition meta_comp2 :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<box>" 55)
  where "meta_comp2 f g = (THE h. \<exists> W X Y. g : W \<rightarrow> Y\<^bsup>X\<^esup> \<and> h = (f\<^sup>\<flat>  \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp>)"


lemma meta_comp2_def2: 
  assumes "f: W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g: W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "f \<box> g  = (f\<^sup>\<flat>  \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp>"
  using assms unfolding meta_comp2_def
  by (smt (z3) cfunc_type_def exp_set_inj the_equality)
  
 

lemma meta_comp2_type[type_rule]: 
  assumes "f: W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g: W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "f \<box> g : W \<rightarrow> Z\<^bsup>X\<^esup>"
proof - 
  have "(f\<^sup>\<flat>  \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp> : W \<rightarrow> Z\<^bsup>X\<^esup>"
    using assms by typecheck_cfuncs
  then show ?thesis 
    using assms by (simp add: meta_comp2_def2)
qed



lemma meta_comp2_elements_aux: 
  assumes "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>"
  assumes "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  assumes "x \<in>\<^sub>c X"
  shows "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>)  \<circ>\<^sub>c \<langle>x, id\<^sub>c one\<rangle> = eval_func Z Y \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c \<langle>x,g\<rangle>,f\<rangle>"
proof-
    have "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>)  \<circ>\<^sub>c \<langle>x, id\<^sub>c one\<rangle>=  f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>  \<circ>\<^sub>c \<langle>x, id\<^sub>c one\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat> \<circ>\<^sub>c \<langle>x, id\<^sub>c one\<rangle>,right_cart_proj X one \<circ>\<^sub>c \<langle>x, id\<^sub>c one\<rangle> \<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat> \<circ>\<^sub>c \<langle>x, id\<^sub>c one\<rangle>,id\<^sub>c one\<rangle>"
      using assms by (typecheck_cfuncs, metis one_unique_element)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>(eval_func Y X) \<circ>\<^sub>c (id X \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x, id\<^sub>c one\<rangle>,id\<^sub>c one\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>(eval_func Y X) \<circ>\<^sub>c  \<langle>x, g\<rangle>,id\<^sub>c one\<rangle>"
      using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs,force)
    also have "... = (eval_func Z Y) \<circ>\<^sub>c (id Y \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>(eval_func Y X) \<circ>\<^sub>c  \<langle>x, g\<rangle>,id\<^sub>c one\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2)
    also have "... = (eval_func Z Y) \<circ>\<^sub>c  \<langle>(eval_func Y X) \<circ>\<^sub>c  \<langle>x, g\<rangle>,f\<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
    then show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>) \<circ>\<^sub>c \<langle>x,id\<^sub>c one\<rangle> = eval_func Z Y \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c \<langle>x,g\<rangle>,f\<rangle>"
      by (simp add: calculation)
qed





lemma meta_comp2_def3: 
  assumes "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>"
  assumes "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "f \<box> g = metafunc ((cnufatem f) \<circ>\<^sub>c (cnufatem g))"
  using assms
proof(unfold meta_comp2_def2 cnufatem_def2 metafunc_def meta_comp_def)          
  have "f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle> = ((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c  left_cart_proj X one"
  proof(rule one_separator[where X = "X \<times>\<^sub>c one", where Y = Z])
    show "f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle> : X \<times>\<^sub>c one \<rightarrow> Z"
      using assms by typecheck_cfuncs
    show "((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one : X \<times>\<^sub>c one \<rightarrow> Z"
      using assms by typecheck_cfuncs
  next
    fix x1 
    assume x1_type[type_rule]: "x1  \<in>\<^sub>c (X \<times>\<^sub>c one)"
    then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and x_def: "x1 = \<langle>x, id\<^sub>c one\<rangle>"
      by (metis cart_prod_decomp id_type terminal_func_unique)
    then have "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>) \<circ>\<^sub>c x1 = eval_func Z Y \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c \<langle>x,g\<rangle>,f\<rangle>"
      using assms meta_comp2_elements_aux x_def by blast
    also have "... = eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      using assms by (typecheck_cfuncs, metis cart_prod_extract_left)
    also have "... =  (eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      using assms by (typecheck_cfuncs, meson comp_associative2)
    also have "... = ((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one \<circ>\<^sub>c x1"
      using assms id_type left_cart_proj_cfunc_prod x_def by (typecheck_cfuncs, presburger)
    also have "... = (((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one) \<circ>\<^sub>c x1"
      using assms by (typecheck_cfuncs, meson comp_associative2)
    then show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>) \<circ>\<^sub>c x1 = (((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one) \<circ>\<^sub>c x1"
      by (simp add: calculation)
  qed
  then show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>)\<^sup>\<sharp> = (((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj (domain ((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)) one)\<^sup>\<sharp>"
    using assms cfunc_type_def cnufatem_def2 cnufatem_type domain_comp by force
qed




lemma meta_comp2_def4:
  assumes "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>"
  assumes "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "f \<box> g   = meta_comp X Y Z \<circ>\<^sub>c \<langle>f,g\<rangle>"
  using assms 
proof(unfold meta_comp2_def2 cnufatem_def2 metafunc_def meta_comp_def)          
  have "(((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one) =  
          (eval_func Z Y \<circ>\<^sub>c  swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c  (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X)) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (id (X)  \<times>\<^sub>f  \<langle>f,g\<rangle>)"
  proof(rule one_separator[where X = "X \<times>\<^sub>c one", where Y = Z])
    show "((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one : X \<times>\<^sub>c one \<rightarrow> Z"
      by (typecheck_cfuncs, meson assms)
    show "(eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f \<langle>f,g\<rangle> : X \<times>\<^sub>c one \<rightarrow> Z"
      using assms by typecheck_cfuncs
  next
    fix x1 
    assume x1_type[type_rule]: "x1  \<in>\<^sub>c (X \<times>\<^sub>c one)"
    then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and x_def: "x1 = \<langle>x, id\<^sub>c one\<rangle>"
      by (metis cart_prod_decomp id_type terminal_func_unique)
    have "(((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one) \<circ>\<^sub>c x1 = 
           ((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one \<circ>\<^sub>c x1"
      by (typecheck_cfuncs, metis assms cfunc_type_def comp_associative)
    also have "... = ((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x"
      using id_type left_cart_proj_cfunc_prod x_def by (typecheck_cfuncs, presburger)
    also have "... =  (eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      by (typecheck_cfuncs, metis assms cfunc_type_def comp_associative)
    also have "... = eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      by (typecheck_cfuncs, metis assms cfunc_type_def comp_associative)
    also have "... = eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>x ,g\<rangle>"
      by (typecheck_cfuncs, metis assms(2) cart_prod_extract_left)
    also have "... = eval_func Z Y \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c \<langle>x ,g\<rangle> ,f\<rangle>"
      by (typecheck_cfuncs, metis assms cart_prod_extract_left)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y) \<circ>\<^sub>c \<langle>f , eval_func Y X \<circ>\<^sub>c  \<langle>x, g\<rangle>\<rangle>"
      by (typecheck_cfuncs, metis assms comp_associative2 swap_ap)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y) \<circ>\<^sub>c \<langle>id\<^sub>c (Z\<^bsup>Y\<^esup>)  \<circ>\<^sub>c  f , (eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X)  \<circ>\<^sub>c \<langle>g, x\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt (z3) assms comp_associative2 id_left_unit2 swap_ap)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y) \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X)) \<circ>\<^sub>c   \<langle>f,\<langle>g, x\<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X)) \<circ>\<^sub>c   \<langle>f,\<langle>g, x\<rangle>\<rangle>"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X)) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c   \<langle>\<langle>f,g\<rangle>, x \<rangle>"
      using assms by (typecheck_cfuncs, simp add: associate_right_ap)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c   \<langle>\<langle>f,g\<rangle>, x \<rangle>"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>) \<circ>\<^sub>c   \<langle>x,  \<langle>f,g\<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, simp add: swap_ap)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c   \<langle>x,  \<langle>f,g\<rangle>\<rangle>"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    also have "... = (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c   ((id\<^sub>c X \<times>\<^sub>f \<langle>f,g\<rangle>) \<circ>\<^sub>c  x1)"
      using assms by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type x_def)
    also have "... = ((eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f \<langle>f,g\<rangle>) \<circ>\<^sub>c x1"
      by (typecheck_cfuncs, meson assms comp_associative2)
    then show "(((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj X one) \<circ>\<^sub>c x1 =
         ((eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f \<langle>f,g\<rangle>) \<circ>\<^sub>c x1"
      using calculation by presburger
  qed
  then have "(((eval_func Z Y \<circ>\<^sub>c \<langle>id\<^sub>c Y,f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func Y X \<circ>\<^sub>c \<langle>id\<^sub>c X,g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c
     left_cart_proj X one)\<^sup>\<sharp> =  (eval_func Z Y \<circ>\<^sub>c  swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X))
         \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c \<langle>f,g\<rangle>"
    using assms by (typecheck_cfuncs, simp add: sharp_comp)  
  then show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj X one\<rangle>)\<^sup>\<sharp> =
    (eval_func Z Y \<circ>\<^sub>c swap (Z\<^bsup>Y\<^esup>) Y \<circ>\<^sub>c (id\<^sub>c (Z\<^bsup>Y\<^esup>) \<times>\<^sub>f eval_func Y X \<circ>\<^sub>c swap (Y\<^bsup>X\<^esup>) X) \<circ>\<^sub>c associate_right (Z\<^bsup>Y\<^esup>) (Y\<^bsup>X\<^esup>) X \<circ>\<^sub>c swap X (Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c \<langle>f,g\<rangle>"
    using assms cfunc_type_def cnufatem_def2 cnufatem_type domain_comp meta_comp2_def2 meta_comp2_def3 metafunc_def by force
qed


lemma meta_comp_on_els:
  assumes "f : W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g : W \<rightarrow> Y\<^bsup>X\<^esup>"
  assumes "w \<in>\<^sub>c W"
  shows "(f \<box> g) \<circ>\<^sub>c w    = (f\<circ>\<^sub>c w) \<box> (g \<circ>\<^sub>c w)"
proof - 
  have "(f \<box> g) \<circ>\<^sub>c w = (f\<^sup>\<flat>  \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  also have "... = (eval_func Z Y \<circ>\<^sub>c (id Y \<times>\<^sub>f f)  \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f g) , right_cart_proj X W\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w"
    using assms comp_associative2 inv_transpose_func_def2 by (typecheck_cfuncs, force)
  also have "... = (eval_func Z Y \<circ>\<^sub>c  \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f g) , f \<circ>\<^sub>c right_cart_proj X W\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = (eval_func Z Y  \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (g\<circ>\<^sub>c w)) , (f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj X one\<rangle>)\<^sup>\<sharp>"
  proof - 
    have "(eval_func Z Y \<circ>\<^sub>c  \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f g) , f \<circ>\<^sub>c right_cart_proj X W\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c (id X \<times>\<^sub>f w) = 
          eval_func Z Y \<circ>\<^sub>c  \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (g\<circ>\<^sub>c w)) , f \<circ>\<^sub>c right_cart_proj X W \<circ>\<^sub>c (id X \<times>\<^sub>f w)\<rangle>"
    proof - 
      have "eval_func Z Y \<circ>\<^sub>c  \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f g) , f \<circ>\<^sub>c right_cart_proj X W\<rangle> \<circ>\<^sub>c (id X \<times>\<^sub>f w) 
          =  eval_func Z Y \<circ>\<^sub>c  \<langle>(eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f g)) \<circ>\<^sub>c (id X \<times>\<^sub>f w) , (f \<circ>\<^sub>c right_cart_proj X W) \<circ>\<^sub>c (id X \<times>\<^sub>f w)\<rangle>"
         using assms cfunc_prod_comp by (typecheck_cfuncs, force)
       also have "... = eval_func Z Y \<circ>\<^sub>c  \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f g) \<circ>\<^sub>c (id X \<times>\<^sub>f w) , f \<circ>\<^sub>c right_cart_proj X W \<circ>\<^sub>c (id X \<times>\<^sub>f w)\<rangle>"
         using assms comp_associative2 by (typecheck_cfuncs, auto)
       also have "... = eval_func Z Y \<circ>\<^sub>c  \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (g\<circ>\<^sub>c w)) , f \<circ>\<^sub>c right_cart_proj X W \<circ>\<^sub>c (id X \<times>\<^sub>f w)\<rangle>"
         using assms by (typecheck_cfuncs, metis identity_distributes_across_composition)
       then show ?thesis
         using assms calculation comp_associative2 flat_cancels_sharp by (typecheck_cfuncs, auto)
     qed
     then show ?thesis
       using assms by (typecheck_cfuncs, smt (z3) comp_associative2 inv_transpose_func_def2 
       inv_transpose_of_composition right_cart_proj_cfunc_cross_prod transpose_func_unique)
  qed
  also have "... = (eval_func Z Y \<circ>\<^sub>c (id\<^sub>c Y  \<times>\<^sub>f ((f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj X one)) \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (g\<circ>\<^sub>c w)) , id (X\<times>\<^sub>c one)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
  also have "... = (eval_func Z Y \<circ>\<^sub>c (id\<^sub>c Y \<times>\<^sub>f (f \<circ>\<^sub>c w)) \<circ>\<^sub>c (id (Y) \<times>\<^sub>f right_cart_proj X one) \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (g\<circ>\<^sub>c w)) , id (X\<times>\<^sub>c one)\<rangle>)\<^sup>\<sharp>"
    using assms comp_associative2 identity_distributes_across_composition by (typecheck_cfuncs, force)
  also have "... = ((f\<circ>\<^sub>cw)\<^sup>\<flat> \<circ>\<^sub>c (id (Y) \<times>\<^sub>f right_cart_proj X one) \<circ>\<^sub>c \<langle>eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f (g\<circ>\<^sub>c w)) , id (X\<times>\<^sub>c one)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, smt (z3) comp_associative2 inv_transpose_func_def2)
  also have "... = ((f\<circ>\<^sub>cw)\<^sup>\<flat> \<circ>\<^sub>c (id (Y) \<times>\<^sub>f right_cart_proj X one) \<circ>\<^sub>c \<langle>(g\<circ>\<^sub>c w)\<^sup>\<flat> , id (X\<times>\<^sub>c one)\<rangle>)\<^sup>\<sharp>"
    using assms inv_transpose_func_def2 by (typecheck_cfuncs, force)
  also have "... = ((f\<circ>\<^sub>c w)\<^sup>\<flat>  \<circ>\<^sub>c \<langle>(g\<circ>\<^sub>c w)\<^sup>\<flat>, right_cart_proj X one\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
  also have "... = (f\<circ>\<^sub>c w) \<box> (g \<circ>\<^sub>c w)"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  then show ?thesis
    by (simp add: calculation)
qed





lemma meta_comp2_def5:
  assumes "f : W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g : W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "f \<box> g   = meta_comp X Y Z \<circ>\<^sub>c \<langle>f,g\<rangle>"
proof(rule one_separator[where X = W, where Y = "Z\<^bsup>X\<^esup>"])
  show "f \<box> g : W \<rightarrow> Z\<^bsup>X\<^esup>"
    using assms by typecheck_cfuncs
  show "meta_comp X Y Z \<circ>\<^sub>c \<langle>f,g\<rangle> : W \<rightarrow> Z\<^bsup>X\<^esup>"
    using assms by typecheck_cfuncs
next
  fix w 
  assume w_type[type_rule]: "w \<in>\<^sub>c W"
  have "(meta_comp X Y Z \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c w = meta_comp X Y Z \<circ>\<^sub>c \<langle>f,g\<rangle> \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = meta_comp X Y Z \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c w, g \<circ>\<^sub>c w\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... = ((f\<circ>\<^sub>c w) \<box> (g \<circ>\<^sub>c w))"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def4)
  also have "... = (f \<box> g) \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: meta_comp_on_els)
  then show "(f \<box> g) \<circ>\<^sub>c w = (meta_comp X Y Z \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c w"
    by (simp add: calculation)
qed

  

lemma meta_left_identity:
  assumes "g \<in>\<^sub>c X\<^bsup>X\<^esup>"
  shows "g \<box> metafunc (id X) = g"
  using assms by (typecheck_cfuncs, metis cfunc_type_def cnufatem_metafunc cnufatem_type id_right_unit meta_comp2_def3 metafunc_cnufatem)
  

lemma meta_right_identity:
  assumes "g \<in>\<^sub>c X\<^bsup>X\<^esup>"
  shows "metafunc(id X) \<box> g = g"
  using assms by (typecheck_cfuncs, smt (z3) cnufatem_metafunc cnufatem_type id_left_unit2 meta_comp2_def3 metafunc_cnufatem)



lemma comp_as_metacomp:
  assumes "g : X \<rightarrow> Y"
  assumes "f : Y \<rightarrow> Z"
  shows "f \<circ>\<^sub>c g = cnufatem(metafunc f \<box> metafunc g)"
  using assms by (typecheck_cfuncs, simp add: cnufatem_metafunc meta_comp2_def3)

lemma comp_as_metacomp2:
  assumes "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  assumes "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>"
  shows "cnufatem f \<circ>\<^sub>c cnufatem g = cnufatem(f \<box> g)"
  using assms by (typecheck_cfuncs, simp add: comp_as_metacomp metafunc_cnufatem)





lemma meta_comp_assoc:
  assumes "e : W \<rightarrow> A\<^bsup>Z\<^esup>"
  assumes "f : W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g : W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "(e \<box> f) \<box>  g  = e \<box> (f \<box> g)"
proof -
  have "(e \<box> f) \<box>  g = (e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat>, right_cart_proj Y W\<rangle>)\<^sup>\<sharp> \<box> g"
    using assms by (simp add: meta_comp2_def2)
  also have "... = ((e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat>, right_cart_proj Y W\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  also have "... = ((e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat>, right_cart_proj Y W\<rangle>) \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: flat_cancels_sharp)    
  also have "... = (e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle> ,right_cart_proj X W\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 right_cart_proj_cfunc_prod)
  also have "... = (e\<^sup>\<flat> \<circ>\<^sub>c \<langle>(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> ,right_cart_proj X W\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: flat_cancels_sharp)
  also have "... = e \<box> (f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj X W\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  also have "... = e \<box> (f \<box> g)"
    using assms by (simp add: meta_comp2_def2)
  then show ?thesis
    by (simp add: calculation)
qed



section \<open>Parameterized Functions\<close>


(*Parameterized Functions*)

definition left_param :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("_\<^bsub>[_,-]\<^esub>" [100,0]100) where
  "left_param k p \<equiv> (THE f.  \<exists> P Q R. k : P \<times>\<^sub>c Q \<rightarrow> R \<and> f = k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id Q\<rangle>)"

  

lemma left_param_def2:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  shows "k\<^bsub>[p,-]\<^esub> \<equiv> k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id Q\<rangle>"
proof - 
  have "\<exists> P Q R. k : P \<times>\<^sub>c Q \<rightarrow> R \<and> left_param k p = k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id Q\<rangle>"
    unfolding left_param_def by (smt (z3) cfunc_type_def the1I2 transpose_func_type assms) 
  then show "k\<^bsub>[p,-]\<^esub> \<equiv> k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id Q\<rangle>"
    by (smt (z3) assms cfunc_type_def transpose_func_type)
qed


lemma left_param_type[type_rule]:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  assumes "p \<in>\<^sub>c P"
  shows "k\<^bsub>[p,-]\<^esub> : Q \<rightarrow> R"
  using assms by (unfold left_param_def2, typecheck_cfuncs)

lemma left_param_on_el:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  assumes "p \<in>\<^sub>c P"
  assumes "q \<in>\<^sub>c Q"
  shows  "k\<^bsub>[p,-]\<^esub> \<circ>\<^sub>c q = k \<circ>\<^sub>c \<langle>p, q\<rangle>"
proof - 
  have "k\<^bsub>[p,-]\<^esub> \<circ>\<^sub>c q = k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id Q\<rangle>  \<circ>\<^sub>c q"
    using assms cfunc_type_def comp_associative left_param_def2 by (typecheck_cfuncs, force)
  also have "... = k \<circ>\<^sub>c \<langle>p, q\<rangle>"
    using  assms(2) assms(3) cart_prod_extract_right by force
  then show ?thesis
    by (simp add: calculation)
qed



definition right_param :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("_\<^bsub>[-,_]\<^esub>" [100,0]100) where
  "right_param k q \<equiv> (THE f.  \<exists> P Q R. k : P \<times>\<^sub>c Q \<rightarrow> R \<and> f = k \<circ>\<^sub>c \<langle>id P, q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>)"


lemma right_param_def2:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  shows "k\<^bsub>[-,q]\<^esub> \<equiv> k \<circ>\<^sub>c \<langle>id P, q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>"
proof - 
  have "\<exists> P Q R. k : P \<times>\<^sub>c Q \<rightarrow> R \<and> right_param k q = k \<circ>\<^sub>c \<langle>id P, q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>"
    unfolding right_param_def by (rule theI', insert assms, auto, metis cfunc_type_def exp_set_inj transpose_func_type) 
  then show "k\<^bsub>[-,q]\<^esub> \<equiv> k \<circ>\<^sub>c \<langle>id\<^sub>c P,q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>"
    by (smt (z3) assms cfunc_type_def exp_set_inj transpose_func_type)
qed

lemma right_param_type[type_rule]:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  assumes "q \<in>\<^sub>c Q"
  shows "k\<^bsub>[-,q]\<^esub> : P \<rightarrow> R"
  using assms by (unfold right_param_def2, typecheck_cfuncs)
  

lemma right_param_on_el:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  assumes "p \<in>\<^sub>c P"
  assumes "q \<in>\<^sub>c Q"
  shows  "k\<^bsub>[-,q]\<^esub> \<circ>\<^sub>c p = k \<circ>\<^sub>c \<langle>p, q\<rangle>"
proof - 
  have "k\<^bsub>[-,q]\<^esub> \<circ>\<^sub>c p = k \<circ>\<^sub>c  \<langle>id P, q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>  \<circ>\<^sub>c p"
    using assms cfunc_type_def comp_associative right_param_def2 by (typecheck_cfuncs, force)
  also have "... = k \<circ>\<^sub>c \<langle>p, q\<rangle>"
    using assms(2) assms(3) cart_prod_extract_left by force
  then show ?thesis
    by (simp add: calculation)
qed




section \<open>Exponential Set Facts\<close>



(* Proposition 2.5.7 *)
lemma set_to_power_one:
  "X\<^bsup>one\<^esup> \<cong> X"
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
  obtain f where f_type: "f = \<alpha>\<^bsub>X\<^esub>\<circ>\<^sub>c (left_cart_proj \<emptyset> one)" and fsharp_type[type_rule]: "f\<^sup>\<sharp> \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
    using transpose_func_type by (typecheck_cfuncs, force)
  have uniqueness: "\<forall>z. z \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup> \<longrightarrow> z=f\<^sup>\<sharp>"
  proof auto
    fix z
    assume z_type[type_rule]: "z \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
    obtain j where j_iso:"j:\<emptyset> \<rightarrow> \<emptyset> \<times>\<^sub>c one \<and> isomorphism(j)"
      using is_isomorphic_def isomorphic_is_symmetric zero_times_X by presburger
    obtain \<psi> where psi_type: "\<psi> : \<emptyset> \<times>\<^sub>c one \<rightarrow> \<emptyset> \<and>
                     j \<circ>\<^sub>c \<psi> = id(\<emptyset> \<times>\<^sub>c one) \<and> \<psi> \<circ>\<^sub>c j = id(\<emptyset>)"
      using cfunc_type_def isomorphism_def j_iso by fastforce 
    then have f_sharp : "id(\<emptyset>)\<times>\<^sub>f z = id(\<emptyset>)\<times>\<^sub>f f\<^sup>\<sharp>"
      by (typecheck_cfuncs, meson comp_type emptyset_is_empty one_separator)
    then show "z = f\<^sup>\<sharp>"
      using  fsharp_type same_evals_equal z_type by force
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
  "(X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<cong> X\<^bsup>A\<^esup> \<times>\<^sub>c Y\<^bsup>A\<^esup>"
proof - 
  have "is_cart_prod ((X \<times>\<^sub>c Y)\<^bsup>A\<^esup>) ((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) (right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f) (X\<^bsup>A\<^esup>) (Y\<^bsup>A\<^esup>)"
    unfolding is_cart_prod_def
  proof auto
    show "(left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f : (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>A\<^esup>"
      by typecheck_cfuncs
  next
    show "(right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f : (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
      by typecheck_cfuncs
  next
    fix f g Z 
    assume f_type[type_rule]: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
    assume g_type[type_rule]: "g : Z \<rightarrow> Y\<^bsup>A\<^esup>"

    show "\<exists>h. h : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<and>
           left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h = f \<and>
           right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h = g \<and>
           (\<forall>h2. h2 : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<and> left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 = f \<and> right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 = g \<longrightarrow>
                 h2 = h)"
    proof (rule_tac x="\<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp>" in exI, auto)
      show sharp_prod_fflat_gflat_type: "\<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup>"
        by typecheck_cfuncs
      have "((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = ((left_cart_proj X Y) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>)\<^sup>\<sharp>"
        by (typecheck_cfuncs, metis transpose_of_comp)
      also have "... = f\<^sup>\<flat>\<^sup>\<sharp>"
        by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
      also have "... = f"
        by (typecheck_cfuncs, simp add: sharp_cancels_flat)
      then show projection_property1: "((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = f"
        by (simp add: calculation)
      show projection_property2: "((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = g"
        by (typecheck_cfuncs, metis right_cart_proj_cfunc_prod sharp_cancels_flat transpose_of_comp)
      show "\<And>h2. h2 : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<Longrightarrow>
          f = left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 \<Longrightarrow>
          g = right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 \<Longrightarrow>
          h2 = \<langle>(left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2)\<^sup>\<flat>,(right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2)\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
      proof -
        fix h
        assume h_type[type_rule]: "h : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup>"
        assume h_property1:  "f = ((left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c h"
        assume h_property2:  "g = ((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c h"
    
        have "f = (left_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp>"
          by (metis  h_property1 h_type sharp_cancels_flat)
        also have "... = ((left_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (typecheck_cfuncs, simp add: transpose_of_comp)
        have computation1: "f = ((left_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (simp add: \<open>left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp> = (left_cart_proj X Y \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>\<close> calculation)
        then have unqiueness1: "(left_cart_proj X Y) \<circ>\<^sub>c  h\<^sup>\<flat> =  f\<^sup>\<flat>"
          using h_type f_type by (typecheck_cfuncs, simp add: computation1 flat_cancels_sharp)
        have   "g = ((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (metis  h_property2 h_type sharp_cancels_flat)
        have "... = ((right_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (typecheck_cfuncs, metis transpose_of_comp)
        have computation2: "g = ((right_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
           by (simp add: \<open>g = right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp>\<close> \<open>right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp> = (right_cart_proj X Y \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>\<close>)
        then have unqiueness2: "(right_cart_proj X Y) \<circ>\<^sub>c  h\<^sup>\<flat> =  g\<^sup>\<flat>"
          using h_type g_type by (typecheck_cfuncs, simp add: computation2 flat_cancels_sharp)
        then have h_flat: "h\<^sup>\<flat> = \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_prod_unique unqiueness1 unqiueness2)
        then have h_is_sharp_prod_fflat_gflat: "h = \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
          by (metis  h_type sharp_cancels_flat)
        then show "h = \<langle>(left_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h)\<^sup>\<flat>,(right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h)\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
          using h_property1 h_property2 by force
      qed
    qed
  qed
  then show "(X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<cong> X\<^bsup>A\<^esup> \<times>\<^sub>c Y\<^bsup>A\<^esup>"
    using canonical_cart_prod_is_cart_prod cart_prods_isomorphic fst_conv is_isomorphic_def by fastforce
qed
  











(*Consider renaming this lemma*)
lemma exponential_distribution:
  "(Z\<^bsup>(X \<Coprod> Y)\<^esup>) \<cong> (Z\<^bsup>X\<^esup>) \<times>\<^sub>c (Z\<^bsup>Y\<^esup>)"
proof - 
  have "is_cart_prod (Z\<^bsup>(X \<Coprod> Y)\<^esup>) ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c (left_coproj X Y) \<times>\<^sub>f (id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) )\<^sup>\<sharp>) ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c (right_coproj X Y) \<times>\<^sub>f (id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) )\<^sup>\<sharp>) (Z\<^bsup>X\<^esup>) (Z\<^bsup>Y\<^esup>)"
    unfolding is_cart_prod_def
  proof auto
    show "(eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> : Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    show "(eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> : Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z\<^bsup>Y\<^esup>"
      by typecheck_cfuncs
  next
    fix f g H
    assume f_type[type_rule]: "f : H \<rightarrow> Z\<^bsup>X\<^esup>"
    assume g_type[type_rule]: "g : H \<rightarrow> Z\<^bsup>Y\<^esup>"
    show "\<exists>h. h : H \<rightarrow> Z\<^bsup>(X \<Coprod> Y)\<^esup> \<and>
           (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h = f \<and>
           (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h = g \<and>
           (\<forall>h2. h2 : H \<rightarrow> Z\<^bsup>(X \<Coprod> Y)\<^esup> \<and>
                 (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h2 = f \<and>
                 (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h2 = g \<longrightarrow>
                 h2 = h)"
    proof (rule_tac x="(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>" in exI, auto)
      show "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp> : H \<rightarrow> Z\<^bsup>(X \<Coprod> Y)\<^esup>"
        by typecheck_cfuncs
    next
      have "(eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp> = 
            ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c (id X \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>))\<^sup>\<sharp>"
        using sharp_comp by (typecheck_cfuncs, blast)
      also have "... = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  (left_coproj X Y \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>))\<^sup>\<sharp>"
        by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_cross_prod comp_associative2 id_left_unit2 id_right_unit2)
      also have "... = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  (id (X \<Coprod> Y) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>) \<circ>\<^sub>c (left_coproj X Y \<times>\<^sub>f id H))\<^sup>\<sharp>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c (dist_prod_coprod_inv2 X Y H \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id H))\<^sup>\<sharp>"
        using comp_associative2 transpose_func_def by (typecheck_cfuncs, force)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c left_coproj (X \<times>\<^sub>c H) (Y \<times>\<^sub>c H))\<^sup>\<sharp>"
        by (simp add: dist_prod_coprod_inv2_left_coproj)
      also have "... = f"
        by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod sharp_cancels_flat)
      then show "(eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp> = f"
        by (simp add: calculation)
    next
      have "(eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp> = 
            ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c (id Y \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>))\<^sup>\<sharp>"
        using sharp_comp by (typecheck_cfuncs, blast)
      also have "... = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  (right_coproj X Y \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>))\<^sup>\<sharp>"
        by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_cross_prod comp_associative2 id_left_unit2 id_right_unit2)
      also have "... = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  (id (X \<Coprod> Y) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>) \<circ>\<^sub>c (right_coproj X Y \<times>\<^sub>f id H))\<^sup>\<sharp>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c (dist_prod_coprod_inv2 X Y H \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id H))\<^sup>\<sharp>"
        using comp_associative2 transpose_func_def by (typecheck_cfuncs, force)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c right_coproj (X \<times>\<^sub>c H) (Y \<times>\<^sub>c H))\<^sup>\<sharp>"
        by (simp add: dist_prod_coprod_inv2_right_coproj)
      also have "... = g"
        by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod sharp_cancels_flat)
      then show "(eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp> = g"
        by (simp add: calculation)
    next
      fix h 
      assume h_type[type_rule]: "h : H \<rightarrow> Z\<^bsup>(X \<Coprod> Y)\<^esup>"
      assume f_eqs: "f = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c  h"
      assume g_eqs: "g = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h"
      have "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H) =  h\<^sup>\<flat>"
      proof(rule one_separator[where X = "(X \<Coprod> Y)\<times>\<^sub>cH", where Y = Z])
        show "f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H : (X \<Coprod> Y) \<times>\<^sub>c H \<rightarrow> Z"
          by typecheck_cfuncs
        show "h\<^sup>\<flat> : (X \<Coprod> Y) \<times>\<^sub>c H \<rightarrow> Z"
          by typecheck_cfuncs
        show "\<And>xyh. xyh \<in>\<^sub>c (X \<Coprod> Y) \<times>\<^sub>c H \<Longrightarrow> (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H) \<circ>\<^sub>c xyh = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
        proof-
          fix xyh
          assume l_type[type_rule]: "xyh \<in>\<^sub>c (X \<Coprod> Y) \<times>\<^sub>c H"
          then obtain xy and z where xy_type[type_rule]: "xy \<in>\<^sub>c X \<Coprod> Y" and z_type[type_rule]: "z \<in>\<^sub>c H"
            and xyh_def: "xyh = \<langle>xy,z\<rangle>"
            using cart_prod_decomp by blast
          show "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H) \<circ>\<^sub>c xyh = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
          proof(cases "\<exists>x. x \<in>\<^sub>c X \<and> xy =  left_coproj X Y \<circ>\<^sub>c x")
            assume "\<exists>x. x \<in>\<^sub>c X \<and> xy = left_coproj X Y \<circ>\<^sub>c x"
            then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and xy_def: "xy =  left_coproj X Y \<circ>\<^sub>c x"
              by blast
            have "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H) \<circ>\<^sub>c xyh = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (dist_prod_coprod_inv2 X Y H  \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c x,z\<rangle>)"
              by (typecheck_cfuncs, simp add: comp_associative2 xy_def xyh_def)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c ((dist_prod_coprod_inv2 X Y H  \<circ>\<^sub>c (left_coproj X Y \<times>\<^sub>f id H)) \<circ>\<^sub>c \<langle>x,z\<rangle>)"
              using dist_prod_coprod_inv2_left_ap dist_prod_coprod_inv2_left_coproj by (typecheck_cfuncs, presburger)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (left_coproj (X \<times>\<^sub>c H) (Y \<times>\<^sub>c H)  \<circ>\<^sub>c \<langle>x,z\<rangle>)"
              using dist_prod_coprod_inv2_left_coproj by presburger
            also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>x,z\<rangle>"
              by (typecheck_cfuncs,  simp add: comp_associative2 left_coproj_cfunc_coprod)
            also have "... = ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c  h)\<^sup>\<flat>  \<circ>\<^sub>c \<langle>x,z\<rangle>"
              using f_eqs by fastforce
            also have "... = (((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp>\<^sup>\<flat>) \<circ>\<^sub>c  (id X \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>x,z\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, presburger)
            also have "... = ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c  (id X \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>x,z\<rangle>"
              by (typecheck_cfuncs, simp add: flat_cancels_sharp)
            also have "... = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>x,z\<rangle>"
              by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_cross_prod comp_associative2 id_left_unit2 id_right_unit2)
            also have "... = eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  \<langle>left_coproj X Y \<circ>\<^sub>c x, h \<circ>\<^sub>c z\<rangle>"
              by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2)
            also have "... = eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  ((id(X \<Coprod> Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>xy,z\<rangle>)"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 xy_def)
            also have "... = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
              by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2 xyh_def)
            then show ?thesis
              by (simp add: calculation)
          next
            assume "\<nexists>x. x \<in>\<^sub>c X \<and> xy = left_coproj X Y \<circ>\<^sub>c x"
            then obtain y where y_type[type_rule]: "y \<in>\<^sub>c Y" and xy_def: "xy =  right_coproj X Y \<circ>\<^sub>c y"
              using  coprojs_jointly_surj by (typecheck_cfuncs, blast)
            have "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_inv2 X Y H) \<circ>\<^sub>c xyh = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (dist_prod_coprod_inv2 X Y H  \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c y,z\<rangle>)"
              by (typecheck_cfuncs, simp add: comp_associative2 xy_def xyh_def)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c ((dist_prod_coprod_inv2 X Y H  \<circ>\<^sub>c (right_coproj X Y \<times>\<^sub>f id H)) \<circ>\<^sub>c \<langle>y,z\<rangle>)"
              using dist_prod_coprod_inv2_right_ap dist_prod_coprod_inv2_right_coproj by (typecheck_cfuncs, presburger)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (right_coproj (X \<times>\<^sub>c H) (Y \<times>\<^sub>c H)  \<circ>\<^sub>c \<langle>y,z\<rangle>)"
              using dist_prod_coprod_inv2_right_coproj by presburger
            also have "... = g\<^sup>\<flat> \<circ>\<^sub>c \<langle>y,z\<rangle>"
              by (typecheck_cfuncs,  simp add: comp_associative2 right_coproj_cfunc_coprod)
            also have "... = ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c  h)\<^sup>\<flat>  \<circ>\<^sub>c \<langle>y,z\<rangle>"
              using g_eqs by fastforce
            also have "... = (((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp>\<^sup>\<flat>) \<circ>\<^sub>c  (id Y \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>y,z\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, presburger)
            also have "... = ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c  (id Y \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>y,z\<rangle>"
              by (typecheck_cfuncs, simp add: flat_cancels_sharp)
            also have "... = (eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>y,z\<rangle>"
              by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_cross_prod comp_associative2 id_left_unit2 id_right_unit2)
            also have "... = eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  \<langle>right_coproj X Y \<circ>\<^sub>c y, h \<circ>\<^sub>c z\<rangle>"
              by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2)
            also have "... = eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c  ((id(X \<Coprod> Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>xy,z\<rangle>)"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 xy_def)
            also have "... = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
              by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2 xyh_def)
            then show ?thesis
              by (simp add: calculation)
          qed
        qed
      qed
      then show "h = (((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c left_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat> \<amalg>
                     ((eval_func Z (X \<Coprod> Y) \<circ>\<^sub>c right_coproj X Y \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat> \<circ>\<^sub>c
                                                                      dist_prod_coprod_inv2 X Y H)\<^sup>\<sharp>"
              using f_eqs g_eqs h_type sharp_cancels_flat by force
    qed
  qed
  then show ?thesis
    by (metis canonical_cart_prod_is_cart_prod cart_prods_isomorphic is_isomorphic_def prod.sel(1,2))
qed











lemma zero_to_X:
  assumes "nonempty X"
  shows "\<emptyset>\<^bsup>X\<^esup> \<cong> \<emptyset>"
proof-
  obtain j where j_type[type_rule]: "j: \<emptyset>\<^bsup>X\<^esup> \<rightarrow> one\<times>\<^sub>c \<emptyset>\<^bsup>X\<^esup>" and j_def: "isomorphism(j)"
    using is_isomorphic_def isomorphic_is_symmetric one_x_A_iso_A by blast
  obtain y where y_type[type_rule]: "y \<in>\<^sub>c X"
    using assms nonempty_def by blast
  obtain e where e_type[type_rule]: "e: X\<times>\<^sub>c \<emptyset>\<^bsup>X\<^esup> \<rightarrow> \<emptyset>"
    using eval_func_type by blast
  have iso_type[type_rule]: "(e \<circ>\<^sub>c y \<times>\<^sub>f id(\<emptyset>\<^bsup>X\<^esup>)) \<circ>\<^sub>c j :  \<emptyset>\<^bsup>X\<^esup> \<rightarrow> \<emptyset>"
    by typecheck_cfuncs
  show "\<emptyset>\<^bsup>X\<^esup> \<cong> \<emptyset>"
    using function_to_empty_is_iso is_isomorphic_def iso_type by blast
qed


(*This is an unnecessarily long proof...... We have a 1 line proof in Coproduct.thy*)
(*In the coproduct theory, we call it "product_distribute_over_coproduct_left"*)
(* Proposition 2.5.10 *)
lemma prod_distribute_coprod:
  "A \<times>\<^sub>c (X \<Coprod> Y) \<cong> (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y)"
proof - 
  obtain \<phi> where phi_def: "\<phi> = (id(A) \<times>\<^sub>f left_coproj X Y) \<amalg> (id(A) \<times>\<^sub>f right_coproj X Y)" and 
       \<phi>_type[type_rule]: "\<phi> : (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y) \<rightarrow> A \<times>\<^sub>c (X \<Coprod> Y)"
    by typecheck_cfuncs
  obtain \<psi> where psi_def: "\<psi> = ((left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> \<amalg> (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>)\<^sup>\<flat>" and
       \<psi>_type[type_rule]: "\<psi> : A \<times>\<^sub>c (X \<Coprod> Y) \<rightarrow> (A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y)"
    by typecheck_cfuncs


   (*Below is first centered eqn on page 52*)
  have FirstCenteredEqn1: "(id(A \<times>\<^sub>c (X \<Coprod> Y))\<^sup>\<sharp> \<circ>\<^sub>c left_coproj X Y)\<^sup>\<flat> =  id A \<times>\<^sub>f left_coproj X Y"
    by (typecheck_cfuncs, simp add: flat_cancels_sharp id_left_unit2 inv_transpose_of_composition)
  have FirstCenteredEqn2: "(id(A \<times>\<^sub>c (X \<Coprod> Y))\<^sup>\<sharp> \<circ>\<^sub>c right_coproj X Y)\<^sup>\<flat> = id A \<times>\<^sub>f right_coproj X Y"
    by (typecheck_cfuncs, simp add: flat_cancels_sharp id_left_unit2 inv_transpose_of_composition)
  have SecondCenteredEqn: "id(A \<times>\<^sub>c X \<Coprod> Y)\<^sup>\<sharp> = ((id A \<times>\<^sub>f left_coproj X Y)\<^sup>\<sharp>) \<amalg> (id A \<times>\<^sub>f right_coproj X Y)\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt (z3) cfunc_coprod_comp id_coprod id_left_unit2 id_right_unit2 sharp_comp)
  have AlsoHaveEquation1: "(id(A) \<times>\<^sub>f (left_coproj X Y))\<^sup>\<sharp> = (\<phi>\<^bsup>A\<^esup>\<^sub>f)  \<circ>\<^sub>c  (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis cfunc_cross_prod_type left_coproj_cfunc_coprod phi_def right_proj_type transpose_of_comp)
  have AlsoHaveEquation2: "(id(A) \<times>\<^sub>f (right_coproj X Y))\<^sup>\<sharp> = (\<phi>\<^bsup>A\<^esup>\<^sub>f)  \<circ>\<^sub>c  (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis cfunc_cross_prod_type left_proj_type phi_def right_coproj_cfunc_coprod transpose_of_comp)
  then have ThirdCenteredEqn: "(id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> =
      (\<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>) 
       \<amalg>
      (\<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>) "
    by (simp add: AlsoHaveEquation1 SecondCenteredEqn)
  also have ThirdCenteredEqnb: " ... =  \<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c ((left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> \<amalg> (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>)"
    using cfunc_coprod_comp by (typecheck_cfuncs, blast)
  have computation1:
    "(\<phi> \<circ>\<^sub>c \<psi>)\<^sup>\<sharp> 
      = \<phi>\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> \<amalg> (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis psi_def sharp_cancels_flat transpose_of_comp)
  have computation2:  "... = (id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp>"
    by (simp add:  ThirdCenteredEqnb calculation)
  have HalfInverse: 
      "\<phi> \<circ>\<^sub>c \<psi> =  id(A \<times>\<^sub>c (X \<Coprod> Y))"
    by (typecheck_cfuncs, metis computation1 computation2 flat_cancels_sharp)
  have FifthCenteredEquation: 
    "(\<psi> \<circ>\<^sub>c \<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)))\<^sup>\<sharp>  = (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp>"
    by (typecheck_cfuncs, smt (z3) HalfInverse comp_associative2 dist_prod_coprod_def 
        dist_prod_coprod_inv_left dist_prod_coprod_inv_type id_left_unit2 phi_def)
  have PsiPhiJ0EqsJ0 :
    "\<psi> \<circ>\<^sub>c \<phi> \<circ>\<^sub>c (left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)) = left_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)"
    by (typecheck_cfuncs, metis FifthCenteredEquation flat_cancels_sharp)
  have PsiPhiJ1EqsJ1: "\<psi> \<circ>\<^sub>c \<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)) = right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)"
    by (typecheck_cfuncs, smt (z3) HalfInverse comp_associative2 dist_prod_coprod_def dist_prod_coprod_inv_def2 id_left_unit2 phi_def)

  have fullinverse: "\<psi> \<circ>\<^sub>c \<phi> = id((A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y)"
    by (typecheck_cfuncs, smt (z3) PsiPhiJ0EqsJ0 PsiPhiJ1EqsJ1 cfunc_coprod_comp comp_associative2 id_coprod id_right_unit2 left_proj_type right_proj_type)
      
  show "A \<times>\<^sub>c X \<Coprod> Y \<cong> (A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y"
    unfolding is_isomorphic_def isomorphism_def 
    using HalfInverse  \<psi>_type cfunc_type_def fullinverse phi_def
    by (rule_tac x="\<psi>" in exI, auto, simp add: \<psi>_type, typecheck_cfuncs, fastforce)
qed




lemma exp_pres_iso_left:
  assumes "A \<cong> X" 
  shows "A\<^bsup>Y\<^esup> \<cong>  X\<^bsup>Y\<^esup>"
proof - 
  obtain \<phi> where \<phi>_def: "\<phi>: X \<rightarrow> A \<and> isomorphism(\<phi>)"
    using assms is_isomorphic_def isomorphic_is_symmetric by blast
  obtain \<psi> where \<psi>_def: "\<psi>: A \<rightarrow> X \<and> isomorphism(\<psi>) \<and> (\<psi> \<circ>\<^sub>c \<phi> = id(X))"
    using \<phi>_def cfunc_type_def isomorphism_def by fastforce
  have idA: "\<phi> \<circ>\<^sub>c \<psi> = id(A)"
    by (metis \<phi>_def \<psi>_def cfunc_type_def comp_associative id_left_unit2 isomorphism_def)
  have phi_eval_type: "(\<phi> \<circ>\<^sub>c eval_func X Y)\<^sup>\<sharp>: X\<^bsup>Y\<^esup> \<rightarrow> A\<^bsup>Y\<^esup>"
    using \<phi>_def by (typecheck_cfuncs, blast)
  have psi_eval_type: "(\<psi> \<circ>\<^sub>c eval_func A Y)\<^sup>\<sharp>: A\<^bsup>Y\<^esup> \<rightarrow> X\<^bsup>Y\<^esup>"
    using \<psi>_def by (typecheck_cfuncs, blast)


  have idXY: "(\<psi> \<circ>\<^sub>c eval_func A Y)\<^sup>\<sharp> \<circ>\<^sub>c  (\<phi> \<circ>\<^sub>c eval_func X Y)\<^sup>\<sharp> = id(X\<^bsup>Y\<^esup>)"
  proof - 
    have "(\<psi> \<circ>\<^sub>c eval_func A Y)\<^sup>\<sharp> \<circ>\<^sub>c  (\<phi> \<circ>\<^sub>c eval_func X Y)\<^sup>\<sharp> = 
          (\<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (eval_func A Y)\<^sup>\<sharp>)\<circ>\<^sub>c  (\<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (eval_func X Y)\<^sup>\<sharp>)"
      using \<phi>_def \<psi>_def exp_func_def2 exponential_object_identity id_right_unit2 phi_eval_type psi_eval_type by auto
    also have "... = (\<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c id(A\<^bsup>Y\<^esup>))\<circ>\<^sub>c  (\<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c id(X\<^bsup>Y\<^esup>))"
      by (simp add: exponential_object_identity)
    also have "... = \<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (id(A\<^bsup>Y\<^esup>)\<circ>\<^sub>c  (\<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c id(X\<^bsup>Y\<^esup>)))" 
      by (typecheck_cfuncs, metis \<phi>_def \<psi>_def comp_associative2)
    also have "... = \<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (id(A\<^bsup>Y\<^esup>)\<circ>\<^sub>c  \<phi>\<^bsup>Y\<^esup>\<^sub>f )"
      using \<phi>_def exp_func_def2 id_right_unit2 phi_eval_type by auto
    also have "... = \<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c \<phi>\<^bsup>Y\<^esup>\<^sub>f"
      using \<phi>_def \<psi>_def calculation exp_func_def2 by auto
    also have "... = (\<psi> \<circ>\<^sub>c \<phi>)\<^bsup>Y\<^esup>\<^sub>f"
      by (metis \<phi>_def \<psi>_def transpose_factors)
    also have "... = (id X)\<^bsup>Y\<^esup>\<^sub>f"
      by (simp add: \<psi>_def)
    also have "...  = id(X\<^bsup>Y\<^esup>)"
      by (simp add: exponential_object_identity2)
    then show "(\<psi> \<circ>\<^sub>c eval_func A Y)\<^sup>\<sharp> \<circ>\<^sub>c  (\<phi> \<circ>\<^sub>c eval_func X Y)\<^sup>\<sharp> = id(X\<^bsup>Y\<^esup>)"
      by (simp add: calculation)
  qed
  have idAY: "(\<phi> \<circ>\<^sub>c eval_func X Y)\<^sup>\<sharp> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c eval_func A Y)\<^sup>\<sharp>  = id(A\<^bsup>Y\<^esup>)"
  proof - 
    have "(\<phi> \<circ>\<^sub>c eval_func X Y)\<^sup>\<sharp> \<circ>\<^sub>c  (\<psi> \<circ>\<^sub>c eval_func A Y)\<^sup>\<sharp> = 
          (\<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (eval_func X Y)\<^sup>\<sharp>)\<circ>\<^sub>c  (\<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (eval_func A Y)\<^sup>\<sharp>)"
      using \<phi>_def \<psi>_def exp_func_def2 exponential_object_identity id_right_unit2 phi_eval_type psi_eval_type by auto
    also have "... = (\<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c id(X\<^bsup>Y\<^esup>))\<circ>\<^sub>c  (\<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c id(A\<^bsup>Y\<^esup>))"
      by (simp add: exponential_object_identity)
    also have "... = \<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (id(X\<^bsup>Y\<^esup>)\<circ>\<^sub>c  (\<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c id(A\<^bsup>Y\<^esup>)))" 
      by (typecheck_cfuncs, metis \<phi>_def \<psi>_def comp_associative2)
    also have "... = \<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c (id(X\<^bsup>Y\<^esup>)\<circ>\<^sub>c  \<psi>\<^bsup>Y\<^esup>\<^sub>f )"
      using \<psi>_def exp_func_def2 id_right_unit2 psi_eval_type by auto
    also have "... = \<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c \<psi>\<^bsup>Y\<^esup>\<^sub>f"
      using \<phi>_def \<psi>_def calculation exp_func_def2 by auto
    also have "... = (\<phi> \<circ>\<^sub>c \<psi>)\<^bsup>Y\<^esup>\<^sub>f"
      by (metis \<phi>_def \<psi>_def transpose_factors)
    also have "... = (id A)\<^bsup>Y\<^esup>\<^sub>f"
      by (simp add: idA)
    also have "...  = id(A\<^bsup>Y\<^esup>)"
      by (simp add: exponential_object_identity2)
    then show "(\<phi> \<circ>\<^sub>c eval_func X Y)\<^sup>\<sharp> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c eval_func A Y)\<^sup>\<sharp>  = id(A\<^bsup>Y\<^esup>)"
      by (simp add: calculation)
qed

  show  "A\<^bsup>Y\<^esup> \<cong>  X\<^bsup>Y\<^esup>"
    by (metis cfunc_type_def comp_epi_imp_epi comp_monic_imp_monic epi_mon_is_iso idAY idXY id_isomorphism is_isomorphic_def iso_imp_epi_and_monic phi_eval_type psi_eval_type)
qed


 
lemma expset_power_tower:
  "((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>) \<cong> (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)"
proof - 
  obtain \<phi> where \<phi>_def: "\<phi> = ((eval_func A (B\<times>\<^sub>c C)) \<circ>\<^sub>c (associate_left B C (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)))" and
                 \<phi>_type[type_rule]: "\<phi>: B \<times>\<^sub>c (C\<times>\<^sub>c (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)) \<rightarrow> A" and 
                 \<phi>dbsharp_type[type_rule]: "(\<phi>\<^sup>\<sharp>)\<^sup>\<sharp> : (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>) \<rightarrow> ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
    using transpose_func_type by (typecheck_cfuncs, blast)


  obtain \<psi> where \<psi>_def: "\<psi> = (eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C) \<circ>\<^sub>c (associate_right B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))" and
                 \<psi>_type[type_rule]: "\<psi> :  (B \<times>\<^sub>c C) \<times>\<^sub>c ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>) \<rightarrow> A" and
                 \<psi>sharp_type[type_rule]: "\<psi>\<^sup>\<sharp>: (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup> \<rightarrow> (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)"
    using transpose_func_type by (typecheck_cfuncs, blast)


  have "(\<phi>\<^sup>\<sharp>)\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp> = id((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
  proof(rule same_evals_equal[where Z= "((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)", where X = "(A\<^bsup>B\<^esup>)", where A = "C"])
    show "\<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp> : A\<^bsup>B\<^esup>\<^bsup>C\<^esup> \<rightarrow> A\<^bsup>B\<^esup>\<^bsup>C\<^esup>"
      by typecheck_cfuncs
    show "id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>) : A\<^bsup>B\<^esup>\<^bsup>C\<^esup> \<rightarrow> A\<^bsup>B\<^esup>\<^bsup>C\<^esup>"
      by typecheck_cfuncs
    show "eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp> =
    eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>)"
    proof(rule same_evals_equal[where Z= "C \<times>\<^sub>c ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)", where X = "A", where A = "B"])
      show "eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp> : C \<times>\<^sub>c A\<^bsup>B\<^esup>\<^bsup>C\<^esup> \<rightarrow> A\<^bsup>B\<^esup>"
        by typecheck_cfuncs
      show "eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>) : C \<times>\<^sub>c A\<^bsup>B\<^esup>\<^bsup>C\<^esup> \<rightarrow> A\<^bsup>B\<^esup>"
        by typecheck_cfuncs
      show "eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f (eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp>)) =
    eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>)"
      proof - 
        have "eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f (eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp>)) =
             eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f (eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (typecheck_cfuncs, metis identity_distributes_across_composition)
        also have "... = eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f ((eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f (\<phi>\<^sup>\<sharp> \<circ>\<^sub>c (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (typecheck_cfuncs, simp add: transpose_func_def)        
        also have "... = eval_func A B \<circ>\<^sub>c ((id\<^sub>c B \<times>\<^sub>f \<phi>\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c B \<times>\<^sub>f (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>)))"
          using identity_distributes_across_composition by (typecheck_cfuncs, auto)
        also have "... = (eval_func A B \<circ>\<^sub>c ((id\<^sub>c B \<times>\<^sub>f \<phi>\<^sup>\<sharp>)))  \<circ>\<^sub>c (id\<^sub>c B \<times>\<^sub>f (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          using comp_associative2 by (typecheck_cfuncs,blast)
        also have "... = \<phi>  \<circ>\<^sub>c (id\<^sub>c B \<times>\<^sub>f (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (typecheck_cfuncs, simp add: transpose_func_def)
        also have "... = ((eval_func A (B\<times>\<^sub>c C)) \<circ>\<^sub>c (associate_left B C (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>))) \<circ>\<^sub>c (id\<^sub>c B \<times>\<^sub>f (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (simp add: \<phi>_def)
        also have "... = (eval_func A (B\<times>\<^sub>c C)) \<circ>\<^sub>c (associate_left B C (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)) \<circ>\<^sub>c (id\<^sub>c B \<times>\<^sub>f (id\<^sub>c C \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          using comp_associative2 by (typecheck_cfuncs, auto)
        also have "... = (eval_func A (B\<times>\<^sub>c C)) \<circ>\<^sub>c ((id\<^sub>c B \<times>\<^sub>f id\<^sub>c C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>) \<circ>\<^sub>c  associate_left B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
          by (typecheck_cfuncs, simp add: associate_left_crossprod_ap)
        also have "... = (eval_func A (B\<times>\<^sub>c C)) \<circ>\<^sub>c ((id\<^sub>c (B \<times>\<^sub>c C)) \<times>\<^sub>f \<psi>\<^sup>\<sharp>) \<circ>\<^sub>c  associate_left B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
          by (simp add: id_cross_prod)
        also have "... = \<psi>  \<circ>\<^sub>c  associate_left B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
          by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
        also have "... = ((eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C)) \<circ>\<^sub>c ((associate_right B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))\<circ>\<^sub>c  associate_left B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))"
          by (typecheck_cfuncs, simp add: \<psi>_def cfunc_type_def comp_associative)
        also have "... = ((eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C)) \<circ>\<^sub>c id(B \<times>\<^sub>c (C \<times>\<^sub>c ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)))"
          by (simp add: right_left)
        also have "... = (eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C)"
          by (typecheck_cfuncs, meson id_right_unit2)
        also have "... = eval_func A B \<circ>\<^sub>c id\<^sub>c B \<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C \<circ>\<^sub>c id\<^sub>c C \<times>\<^sub>f id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>)"
          by (typecheck_cfuncs, simp add: id_cross_prod id_right_unit2)
        then show ?thesis using calculation by auto
      qed
    qed
  qed
  have "  \<psi>\<^sup>\<sharp> \<circ>\<^sub>c (\<phi>\<^sup>\<sharp>)\<^sup>\<sharp>=  id(A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)"
  proof(rule same_evals_equal[where Z= "A\<^bsup>(B\<times>\<^sub>c C)\<^esup>", where X = "A", where A = "(B\<times>\<^sub>c C)"])
    show "\<psi>\<^sup>\<sharp> \<circ>\<^sub>c \<phi>\<^sup>\<sharp>\<^sup>\<sharp> : A\<^bsup>(B \<times>\<^sub>c C)\<^esup> \<rightarrow> A\<^bsup>(B \<times>\<^sub>c C)\<^esup>"
      by typecheck_cfuncs
    show "id\<^sub>c (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>) : A\<^bsup>(B \<times>\<^sub>c C)\<^esup> \<rightarrow> A\<^bsup>(B \<times>\<^sub>c C)\<^esup>"
      by typecheck_cfuncs
    show "eval_func A (B \<times>\<^sub>c C) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp> \<circ>\<^sub>c \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) = 
          eval_func A (B \<times>\<^sub>c C) \<circ>\<^sub>c id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f id\<^sub>c (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)"
    proof -
      have "eval_func A (B \<times>\<^sub>c C) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp> \<circ>\<^sub>c \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) =
              eval_func A (B \<times>\<^sub>c C) \<circ>\<^sub>c ((id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f\<phi>\<^sup>\<sharp>\<^sup>\<sharp>))"
        by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
      also have "... = ( eval_func A (B \<times>\<^sub>c C) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp>))) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f\<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = \<psi> \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
        by (typecheck_cfuncs, simp add: transpose_func_def)
      also have "... =(eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C) \<circ>\<^sub>c (associate_right B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))  \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
        by (typecheck_cfuncs, smt \<psi>_def cfunc_type_def comp_associative domain_comp)
      also have "... =(eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C) \<circ>\<^sub>c (associate_right B C ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))  \<circ>\<^sub>c ((id\<^sub>c (B) \<times>\<^sub>f id( C)) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
        by (typecheck_cfuncs, simp add: id_cross_prod)
      also have "... =(eval_func A B) \<circ>\<^sub>c ((id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C) \<circ>\<^sub>c    ((id\<^sub>c (B) \<times>\<^sub>f (id(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) \<circ>\<^sub>c (associate_right B C (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))))"
        using associate_right_crossprod_ap by (typecheck_cfuncs, auto)
      also have "... =(eval_func A B) \<circ>\<^sub>c ((id(B)\<times>\<^sub>f eval_func (A\<^bsup>B\<^esup>) C) \<circ>\<^sub>c    (id\<^sub>c (B) \<times>\<^sub>f (id(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))) \<circ>\<^sub>c (associate_right B C (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... =(eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f ((eval_func (A\<^bsup>B\<^esup>) C)\<circ>\<^sub>c (id(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))) \<circ>\<^sub>c (associate_right B C (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        using identity_distributes_across_composition by (typecheck_cfuncs, auto)
      also have "... =(eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f \<phi>\<^sup>\<sharp>) \<circ>\<^sub>c (associate_right B C (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: transpose_func_def)
      also have "... =((eval_func A B) \<circ>\<^sub>c (id(B)\<times>\<^sub>f \<phi>\<^sup>\<sharp>)) \<circ>\<^sub>c (associate_right B C (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = \<phi> \<circ>\<^sub>c (associate_right B C (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: transpose_func_def)
      also have "... = (eval_func A (B\<times>\<^sub>c C)) \<circ>\<^sub>c ((associate_left B C (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)) \<circ>\<^sub>c (associate_right B C (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)))"
        by (typecheck_cfuncs, simp add: \<phi>_def comp_associative2)  
      also have "... = eval_func A (B\<times>\<^sub>c C) \<circ>\<^sub>c id ((B \<times>\<^sub>c C) \<times>\<^sub>c  (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: left_right)
      also have "... = eval_func A (B \<times>\<^sub>c C) \<circ>\<^sub>c id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f id\<^sub>c (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)"
        by (typecheck_cfuncs, simp add: id_cross_prod)
      then show ?thesis using calculation by auto
    qed
  qed
  show ?thesis
    by (metis \<open>\<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp> = id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>)\<close> \<open>\<psi>\<^sup>\<sharp> \<circ>\<^sub>c \<phi>\<^sup>\<sharp>\<^sup>\<sharp> = id\<^sub>c (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)\<close> \<phi>dbsharp_type \<psi>sharp_type cfunc_type_def is_isomorphic_def isomorphism_def)
qed




lemma exp_pres_iso_right:
  assumes "A \<cong> X" 
  shows "Y\<^bsup>A\<^esup> \<cong>  Y\<^bsup>X\<^esup>"
proof - 
  obtain \<phi> where \<phi>_def: "\<phi>: X \<rightarrow> A \<and> isomorphism(\<phi>)"
    using assms is_isomorphic_def isomorphic_is_symmetric by blast
  obtain \<psi> where \<psi>_def: "\<psi>: A \<rightarrow> X \<and> isomorphism(\<psi>) \<and> (\<psi> \<circ>\<^sub>c \<phi> = id(X))"
    using \<phi>_def cfunc_type_def isomorphism_def by fastforce
  have idA: "\<phi> \<circ>\<^sub>c \<psi> = id(A)"
    by (metis \<phi>_def \<psi>_def cfunc_type_def comp_associative id_left_unit2 isomorphism_def)
  obtain f where f_def: "f = (eval_func Y X) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>))" and f_type[type_rule]: "f: A\<times>\<^sub>c (Y\<^bsup>X\<^esup>) \<rightarrow> Y" and fsharp_type[type_rule]: "f\<^sup>\<sharp> : Y\<^bsup>X\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
    using \<psi>_def transpose_func_type by (typecheck_cfuncs, presburger)
  obtain g where g_def: "g = (eval_func Y A) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))" and  g_type[type_rule]: "g: X\<times>\<^sub>c (Y\<^bsup>A\<^esup>) \<rightarrow> Y" and gsharp_type[type_rule]: "g\<^sup>\<sharp> : Y\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>"
    using \<phi>_def transpose_func_type by (typecheck_cfuncs, presburger)




  have fsharp_gsharp_id: "(f\<^sup>\<sharp>) \<circ>\<^sub>c (g\<^sup>\<sharp>) = id(Y\<^bsup>A\<^esup>)"
  proof(rule same_evals_equal[where Z = "Y\<^bsup>A\<^esup>", where X = Y, where A = A])
    show "f\<^sup>\<sharp> \<circ>\<^sub>c g\<^sup>\<sharp> : Y\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
      by typecheck_cfuncs
    show idYA_type: "id\<^sub>c (Y\<^bsup>A\<^esup>) : Y\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
      by typecheck_cfuncs
    show "eval_func Y A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f\<^sup>\<sharp> \<circ>\<^sub>c g\<^sup>\<sharp> = eval_func Y A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f id\<^sub>c (Y\<^bsup>A\<^esup>)"
    proof - 
      have "eval_func Y A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f\<^sup>\<sharp> \<circ>\<^sub>c g\<^sup>\<sharp> = eval_func Y A \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f g\<^sup>\<sharp>)"
        using fsharp_type gsharp_type identity_distributes_across_composition by auto
      also have "... = eval_func Y X \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (id\<^sub>c A \<times>\<^sub>f g\<^sup>\<sharp>)"
        using \<psi>_def cfunc_type_def comp_associative f_def f_type gsharp_type transpose_func_def by (typecheck_cfuncs, smt)
      also have "... = eval_func Y X \<circ>\<^sub>c (\<psi> \<times>\<^sub>f g\<^sup>\<sharp>)"
        by (smt \<psi>_def cfunc_cross_prod_comp_cfunc_cross_prod gsharp_type id_left_unit2 id_right_unit2 id_type)
      also have "... = eval_func Y X \<circ>\<^sub>c (id X \<times>\<^sub>f g\<^sup>\<sharp>) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))"
        by (smt \<psi>_def cfunc_cross_prod_comp_cfunc_cross_prod gsharp_type id_left_unit2 id_right_unit2 id_type)
      also have "... = eval_func Y A \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))"
        by (typecheck_cfuncs, smt \<phi>_def \<psi>_def comp_associative2 flat_cancels_sharp g_def g_type inv_transpose_func_def2)
      also have "... = eval_func Y A \<circ>\<^sub>c ((\<phi> \<circ>\<^sub>c \<psi>) \<times>\<^sub>f (id(Y\<^bsup>A\<^esup>) \<circ>\<^sub>c id(Y\<^bsup>A\<^esup>)))"
        using \<phi>_def \<psi>_def idYA_type cfunc_cross_prod_comp_cfunc_cross_prod by auto        
      also have "... = eval_func Y A \<circ>\<^sub>c id(A) \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)"
        using idA idYA_type id_right_unit2 by auto
      then show "eval_func Y A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f\<^sup>\<sharp> \<circ>\<^sub>c g\<^sup>\<sharp> = eval_func Y A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f id\<^sub>c (Y\<^bsup>A\<^esup>)"
        by (simp add: calculation)
    qed
  qed


  have gsharp_fsharp_id: "(g\<^sup>\<sharp>) \<circ>\<^sub>c (f\<^sup>\<sharp>) = id(Y\<^bsup>X\<^esup>)"
  proof(rule same_evals_equal[where Z = "Y\<^bsup>X\<^esup>", where X = Y, where A = X])
    show "g\<^sup>\<sharp> \<circ>\<^sub>c f\<^sup>\<sharp> : Y\<^bsup>X\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    show idYX_type: "id\<^sub>c (Y\<^bsup>X\<^esup>) : Y\<^bsup>X\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f g\<^sup>\<sharp> \<circ>\<^sub>c f\<^sup>\<sharp> = eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>)"
    proof - 
      have "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f g\<^sup>\<sharp> \<circ>\<^sub>c f\<^sup>\<sharp> = eval_func Y X \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f\<^sup>\<sharp>)"
        using fsharp_type gsharp_type identity_distributes_across_composition by auto
      also have "... = eval_func Y A \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f\<^sup>\<sharp>)"
        using \<phi>_def cfunc_type_def comp_associative fsharp_type g_def g_type transpose_func_def by (typecheck_cfuncs, smt)
      also have "... = eval_func Y A \<circ>\<^sub>c (\<phi> \<times>\<^sub>f f\<^sup>\<sharp>)"
        by (smt \<phi>_def cfunc_cross_prod_comp_cfunc_cross_prod fsharp_type id_left_unit2 id_right_unit2 id_type)
      also have "... = eval_func Y A \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>))"
        by (smt \<phi>_def cfunc_cross_prod_comp_cfunc_cross_prod fsharp_type id_left_unit2 id_right_unit2 id_type)
      also have "... = eval_func Y X \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>))"
        by (typecheck_cfuncs, smt \<phi>_def \<psi>_def comp_associative2 f_def f_type flat_cancels_sharp inv_transpose_func_def2)
      also have "... = eval_func Y X \<circ>\<^sub>c ((\<psi> \<circ>\<^sub>c \<phi>) \<times>\<^sub>f (id(Y\<^bsup>X\<^esup>) \<circ>\<^sub>c id(Y\<^bsup>X\<^esup>)))"
        using \<phi>_def \<psi>_def cfunc_cross_prod_comp_cfunc_cross_prod idYX_type by auto
      also have "... = eval_func Y X \<circ>\<^sub>c id(X) \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)"
        using \<psi>_def idYX_type id_left_unit2 by auto
      then show "eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f g\<^sup>\<sharp> \<circ>\<^sub>c f\<^sup>\<sharp> = eval_func Y X \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>)"
        by (simp add: calculation)
    qed
  qed
  show ?thesis
    by (metis cfunc_type_def comp_epi_imp_epi comp_monic_imp_monic epi_mon_is_iso fsharp_gsharp_id fsharp_type gsharp_fsharp_id gsharp_type id_isomorphism is_isomorphic_def iso_imp_epi_and_monic)
qed


lemma exp_pres_iso:
  assumes "A \<cong> X" "B \<cong> Y" 
  shows "A\<^bsup>B\<^esup> \<cong>  X\<^bsup>Y\<^esup>"
  by (meson assms exp_pres_iso_left exp_pres_iso_right isomorphic_is_transitive)






lemma empty_to_nonempty:
  assumes "nonempty X" "is_empty Y" 
  shows "Y\<^bsup>X\<^esup> \<cong> \<emptyset>"
  by (meson assms exp_pres_iso_left isomorphic_is_transitive no_el_iff_iso_0 zero_to_X)



lemma Y_to_empty:
  assumes "is_empty X" 
  shows "Y\<^bsup>X\<^esup> \<cong> one"
  using assms exp_pres_iso_right isomorphic_is_transitive no_el_iff_iso_0 set_to_power_zero by blast

lemma nonempty_to_nonempty:
  assumes "nonempty X" "nonempty Y"
  shows "nonempty(Y\<^bsup>X\<^esup>)"
  by (meson assms(2) comp_type nonempty_def terminal_func_type transpose_func_type)

lemma empty_to_nonempty_converse:
  assumes "Y\<^bsup>X\<^esup> \<cong> \<emptyset>"
  shows "is_empty Y \<and> nonempty X"
  by (metis is_empty_def Y_to_empty assms no_el_iff_iso_0 nonempty_def nonempty_to_nonempty single_elem_iso_one)









section \<open>Fininte and Infinite Sets and Subsets\<close>



(* Definition 2.5.11 *)
definition powerset :: "cset \<Rightarrow> cset" ("\<P>_" [101]100) where
  "\<P> X = \<Omega>\<^bsup>X\<^esup>"

(* Definition 2.6.1: Finite and Infinite Sets *)
definition is_finite :: "cset \<Rightarrow> bool"  where
   "is_finite(X) \<longleftrightarrow> (\<forall>m. (m : X \<rightarrow> X \<and> monomorphism(m)) \<longrightarrow>  isomorphism(m))"

definition is_infinite :: "cset \<Rightarrow> bool"  where
   "is_infinite(X) \<longleftrightarrow> (\<exists> m. (m : X \<rightarrow> X \<and> monomorphism(m) \<and> \<not>surjective(m)))"

lemma either_finite_or_infinite:
  "is_finite(X) \<or> is_infinite(X)"
  using epi_mon_is_iso is_finite_def is_infinite_def surjective_is_epimorphism by blast






(* Definition 2.6.2 *)
definition is_smaller_than :: "cset \<Rightarrow> cset \<Rightarrow> bool" (infix "\<le>\<^sub>c" 50) where
   "X \<le>\<^sub>c Y \<longleftrightarrow> (\<exists> m. m : X \<rightarrow> Y \<and> monomorphism(m))"



(*The point of the following lemma is simply to unify the two notations used in the book.*)
lemma subobject_iff_smaller_than:
  "(X \<le>\<^sub>c Y) = (\<exists>m. (X,m) \<subseteq>\<^sub>c Y)"
  using is_smaller_than_def subobject_of_def2 by auto



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
  assumes "is_empty X"
  shows "is_finite(X)"
  by (metis assms epi_mon_is_iso epimorphism_def3 is_finite_def is_empty_def one_separator)





lemma emptyset_is_smallest_set:
  "\<emptyset> \<le>\<^sub>c X"
  using empty_subset is_smaller_than_def subobject_of_def2 by auto

lemma Y_nonempty_then_X_le_XtoY:
  assumes "nonempty(Y)"
  shows "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
proof - 
  obtain f where f_def: "f = (right_cart_proj Y X)\<^sup>\<sharp>"
    by blast
  then have f_type: "f : X \<rightarrow> X\<^bsup>Y\<^esup>"
    by (simp add: right_cart_proj_type transpose_func_type)
  have mono_f: "injective(f)"
    unfolding injective_def
  proof(auto)
    fix x y 
    assume x_type: "x \<in>\<^sub>c domain f"
    assume y_type: "y \<in>\<^sub>c domain f"
    assume equals: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    have x_type2 : "x \<in>\<^sub>c X"
      using cfunc_type_def f_type x_type by auto
    have y_type2 : "y \<in>\<^sub>c X"
      using cfunc_type_def f_type y_type by auto
    have "x \<circ>\<^sub>c (right_cart_proj Y one) = (right_cart_proj Y X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      using right_cart_proj_cfunc_cross_prod x_type2 by (typecheck_cfuncs, auto)
    also have "... = ((eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    also have "... = (eval_func X Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x))"
      using comp_associative2 f_type x_type2 by (typecheck_cfuncs, fastforce)
    also have "... = (eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c x))"
      using f_type identity_distributes_across_composition x_type2 by auto
    also have "... = (eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c y))"
      by (simp add: equals)
    also have "... = (eval_func X Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y))"
      using f_type identity_distributes_across_composition y_type2 by auto
    also have "... = ((eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      using comp_associative2 f_type y_type2 by (typecheck_cfuncs, fastforce)
    also have "... = (right_cart_proj Y X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    also have "... = y \<circ>\<^sub>c (right_cart_proj Y one)"
      using right_cart_proj_cfunc_cross_prod y_type2 by (typecheck_cfuncs, auto)
    then show "x = y"
      using  assms calculation epimorphism_def3 nonempty_left_imp_right_proj_epimorphism right_cart_proj_type x_type2 y_type2 by fastforce
  qed
  then show "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
    using f_type injective_imp_monomorphism is_smaller_than_def by blast
qed



(* Proved elsewhere.....
lemma setprod_le_setexp:
  assumes "nonempty(Y)"
  assumes "Y \<cong> one"
  shows "(X \<times>\<^sub>c Y) \<le>\<^sub>cY\<^bsup>X\<^esup>"
  sorry
*)



lemma truth_set_is_finite:
  "is_finite(\<Omega>)"
  unfolding is_finite_def
proof(auto)
  fix m 
  assume m_type[type_rule]: "m : \<Omega> \<rightarrow> \<Omega>"
  assume m_mono: "monomorphism(m)"
  have "surjective(m)"
    unfolding surjective_def
  proof(auto)
    fix y
    assume "y \<in>\<^sub>c codomain m" 
    then have "y \<in>\<^sub>c \<Omega>"
      using cfunc_type_def m_type by force
    show "\<exists>x. x \<in>\<^sub>c domain m \<and> m \<circ>\<^sub>c x = y"
      by (smt (verit, del_insts) \<open>y \<in>\<^sub>c \<Omega>\<close> cfunc_type_def codomain_comp domain_comp injective_def m_mono m_type monomorphism_imp_injective true_false_only_truth_values)
  qed
  then show "isomorphism m"
    by (simp add: epi_mon_is_iso m_mono surjective_is_epimorphism)
qed



lemma smaller_than_finite_is_finite:
  assumes "X \<le>\<^sub>c Y" "is_finite(Y)" 
  shows "is_finite(X)"
  unfolding is_finite_def
proof(auto)
  fix x
  assume x_type: "x : X \<rightarrow> X"
  assume x_mono: "monomorphism x"

  obtain m where m_def: "m: X \<rightarrow> Y \<and> monomorphism(m)"
    using assms(1) is_smaller_than_def by blast

  obtain \<phi> where \<phi>_def: "\<phi> = into_super m \<circ>\<^sub>c (x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c try_cast m" 
    by auto

  have \<phi>_type: "\<phi> : Y \<rightarrow> Y"
    unfolding \<phi>_def
    using x_type m_def by (typecheck_cfuncs, blast)

  have "injective(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using cfunc_bowtieprod_inj id_isomorphism id_type iso_imp_epi_and_monic monomorphism_imp_injective x_mono x_type by blast
  then have mono1: "monomorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using injective_imp_monomorphism by auto
  have mono2: "monomorphism(try_cast m)"
    using m_def try_cast_mono by blast
  have mono3: "monomorphism((x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c try_cast m)"
    using cfunc_type_def composition_of_monic_pair_is_monic m_def mono1 mono2 x_type by (typecheck_cfuncs, auto)
  then have \<phi>_mono: "monomorphism(\<phi>)" 
    unfolding \<phi>_def
    using cfunc_type_def composition_of_monic_pair_is_monic 
          into_super_mono m_def mono3 x_type by (typecheck_cfuncs,auto)
  then have "isomorphism(\<phi>)" 
    using \<phi>_def \<phi>_type assms(2) is_finite_def by blast
  have iso_x_bowtie_id: "isomorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    by (typecheck_cfuncs, smt \<open>isomorphism \<phi>\<close> \<phi>_def comp_associative2 id_left_unit2 into_super_iso into_super_try_cast into_super_type isomorphism_sandwich m_def try_cast_type x_type)
  have "left_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x = (x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c left_coproj X (Y \<setminus> (X,m))"
    using x_type  
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_bowtie_prod)
  have "epimorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using iso_imp_epi_and_monic iso_x_bowtie_id by blast
  then have "surjective(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using  epi_is_surj x_type by (typecheck_cfuncs, blast)
  then have "epimorphism(x)"
    using x_type cfunc_bowtieprod_surj_converse id_type surjective_is_epimorphism by blast
  then show "isomorphism(x)"
    by (simp add: epi_mon_is_iso x_mono)
qed



lemma larger_than_infinite_is_infinite:
  assumes "X \<le>\<^sub>c Y" "is_infinite(X)" 
  shows "is_infinite(Y)"
  using assms either_finite_or_infinite epi_is_surj is_finite_def is_infinite_def
    iso_imp_epi_and_monic smaller_than_finite_is_finite by blast



end