section \<open>Exponential Objects, Transposes and Evaluation\<close>

theory Exponential_Objects
  imports Initial
begin

text \<open>The axiomatization below corresponds to Axiom 9 (Exponential Objects) in Halvorson.\<close>
axiomatization
  exp_set :: "cset \<Rightarrow> cset \<Rightarrow> cset" ("_\<^bsup>_\<^esup>" [100,100]100) and
  eval_func  :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  transpose_func :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>\<sharp>" [100]100)
where
  exp_set_inj: "exp_set(X, A) = exp_set(Y, B) \<Longrightarrow> X = Y \<and> A = B" and
  eval_func_type[type_rule]: "eval_func(X, A) : A \<times>\<^sub>c exp_set(X, A) \<rightarrow> X" and
  transpose_func_type[type_rule]: "f : A \<times>\<^sub>c Z \<rightarrow> X \<Longrightarrow> f\<^sup>\<sharp> : Z \<rightarrow> exp_set(X, A)" and
  transpose_func_def: "f : A \<times>\<^sub>c Z \<rightarrow> X \<Longrightarrow> eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) = f" and
  transpose_func_unique: 
    "f : A \<times>\<^sub>c Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> exp_set(X, A) \<Longrightarrow>
      eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) = f \<Longrightarrow> g = f\<^sup>\<sharp>"

lemma eval_func_surj:
  assumes A_nonempty: "nonempty(A)"
  shows "surjective(eval_func(X, A))"
  unfolding surjective_def
proof (intro allI impI)
  fix x
  assume x_cod: "x \<in>\<^sub>c codomain(eval_func(X, A))"
  have eval_type: "eval_func(X, A) : A \<times>\<^sub>c (X\<^bsup>A\<^esup>) \<rightarrow> X"
    by (rule eval_func_type)
  have eval_cod: "codomain(eval_func(X, A)) = X"
    using eval_type unfolding cfunc_type_def by auto
  have eval_dom: "domain(eval_func(X, A)) = A \<times>\<^sub>c (X\<^bsup>A\<^esup>)"
    using eval_type unfolding cfunc_type_def by auto
  have x_type: "x \<in>\<^sub>c X" using x_cod eval_cod by simp
  have exists_a: "\<exists>a. a \<in>\<^sub>c A" by (rule iffD1[OF nonempty_def A_nonempty])
  obtain a where a_type: "a \<in>\<^sub>c A" by (rule exE[OF exists_a])

  define k where k_def: "k = x \<circ>\<^sub>c right_cart_proj(A, \<one>)"
  have rp_type: "right_cart_proj(A, \<one>) : A \<times>\<^sub>c \<one> \<rightarrow> \<one>"
    by (rule right_cart_proj_type)
  have k_type: "k : A \<times>\<^sub>c \<one> \<rightarrow> X"
    unfolding k_def using rp_type x_type comp_type by blast
  have ksharp_type: "k\<^sup>\<sharp> : \<one> \<rightarrow> (X\<^bsup>A\<^esup>)"
    by (rule transpose_func_type[OF k_type])
  have idA_type: "id(A) : A \<rightarrow> A" by (rule id_type)
  have id1_type: "id(\<one>) : \<one> \<rightarrow> \<one>" by (rule id_type)
  have pair_type: "\<langle>a, k\<^sup>\<sharp>\<rangle> : \<one> \<rightarrow> A \<times>\<^sub>c (X\<^bsup>A\<^esup>)"
    by (rule cfunc_prod_type[OF a_type ksharp_type])
  have seed_type: "\<langle>a, id(\<one>)\<rangle> : \<one> \<rightarrow> A \<times>\<^sub>c \<one>"
    by (rule cfunc_prod_type[OF a_type id1_type])
  have cross_type: "id(A) \<times>\<^sub>f k\<^sup>\<sharp> : A \<times>\<^sub>c \<one> \<rightarrow> A \<times>\<^sub>c (X\<^bsup>A\<^esup>)"
    by (rule cfunc_cross_prod_type[OF idA_type ksharp_type])
  have cross_seed: "(id(A) \<times>\<^sub>f k\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a, id(\<one>)\<rangle> = \<langle>a, k\<^sup>\<sharp>\<rangle>"
  proof -
    have s1: "(id(A) \<times>\<^sub>f k\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a, id(\<one>)\<rangle> =
        \<langle>id(A) \<circ>\<^sub>c a, k\<^sup>\<sharp> \<circ>\<^sub>c id(\<one>)\<rangle>"
      by (rule cfunc_cross_prod_comp_cfunc_prod[OF a_type id1_type idA_type ksharp_type])
    have s2: "id(A) \<circ>\<^sub>c a = a" by (rule id_left_unit2[OF a_type])
    have s3: "k\<^sup>\<sharp> \<circ>\<^sub>c id(\<one>) = k\<^sup>\<sharp>" by (rule id_right_unit2[OF ksharp_type])
    show ?thesis using s1 s2 s3 by simp
  qed
  have eval_transpose: "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f k\<^sup>\<sharp>) = k"
    by (rule transpose_func_def[OF k_type])
  have assoc1: "eval_func(X, A) \<circ>\<^sub>c
      ((id(A) \<times>\<^sub>f k\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a, id(\<one>)\<rangle>) =
      (eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f k\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>a, id(\<one>)\<rangle>"
    using comp_associative2[OF seed_type cross_type eval_type] by simp
  have assoc2: "k \<circ>\<^sub>c \<langle>a, id(\<one>)\<rangle> =
      x \<circ>\<^sub>c (right_cart_proj(A, \<one>) \<circ>\<^sub>c \<langle>a, id(\<one>)\<rangle>)"
    unfolding k_def using comp_associative2[OF seed_type rp_type x_type] by simp
  have rp_seed: "right_cart_proj(A, \<one>) \<circ>\<^sub>c \<langle>a, id(\<one>)\<rangle> = id(\<one>)"
    by (rule right_cart_proj_cfunc_prod[OF a_type id1_type])
  have x_id: "x \<circ>\<^sub>c id(\<one>) = x" by (rule id_right_unit2[OF x_type])
  have eval_pair: "eval_func(X, A) \<circ>\<^sub>c \<langle>a, k\<^sup>\<sharp>\<rangle> = x"
    using cross_seed assoc1 eval_transpose assoc2 rp_seed x_id by simp
  have member_dom: "\<langle>a, k\<^sup>\<sharp>\<rangle> \<in>\<^sub>c domain(eval_func(X, A))"
    using pair_type eval_dom by simp
  show "\<exists>y. y \<in>\<^sub>c domain(eval_func(X, A)) \<and> eval_func(X, A) \<circ>\<^sub>c y = x"
    by (rule exI[where x="\<langle>a, k\<^sup>\<sharp>\<rangle>"], intro conjI, rule member_dom, rule eval_pair)
qed

text \<open>The lemma below corresponds to a note above Definition 2.5.1 in Halvorson.\<close>
lemma exponential_object_identity:
  "eval_func(X, A)\<^sup>\<sharp> = id(X\<^bsup>A\<^esup>)"
proof -
  have eval_type: "eval_func(X, A) : A \<times>\<^sub>c (X\<^bsup>A\<^esup>) \<rightarrow> X"
    by (rule eval_func_type)
  have id_exp_type: "id(X\<^bsup>A\<^esup>) : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>A\<^esup>" by (rule id_type)
  have cross_id: "id(A) \<times>\<^sub>f id(X\<^bsup>A\<^esup>) = id(A \<times>\<^sub>c (X\<^bsup>A\<^esup>))"
    by (rule id_cross_prod)
  have eval_id: "eval_func(X, A) \<circ>\<^sub>c id(A \<times>\<^sub>c (X\<^bsup>A\<^esup>)) = eval_func(X, A)"
    by (rule id_right_unit2[OF eval_type])
  have eval_cross: "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f id(X\<^bsup>A\<^esup>)) =
      eval_func(X, A)" using cross_id eval_id by simp
  have id_eq: "id(X\<^bsup>A\<^esup>) = eval_func(X, A)\<^sup>\<sharp>"
    by (rule transpose_func_unique[OF eval_type id_exp_type eval_cross])
  show ?thesis by (rule sym[OF id_eq])
qed

lemma eval_func_X_empty_injective:
  assumes Y_empty: "is_empty(Y)"
  shows "injective(eval_func(X, Y))"
  unfolding injective_def
proof (intro allI impI)
  fix x y
  assume facts: "x \<in>\<^sub>c domain(eval_func(X, Y)) \<and>
      y \<in>\<^sub>c domain(eval_func(X, Y)) \<and>
      eval_func(X, Y) \<circ>\<^sub>c x = eval_func(X, Y) \<circ>\<^sub>c y"
  have eval_type: "eval_func(X, Y) : Y \<times>\<^sub>c (X\<^bsup>Y\<^esup>) \<rightarrow> X"
    by (rule eval_func_type)
  have eval_dom: "domain(eval_func(X, Y)) = Y \<times>\<^sub>c (X\<^bsup>Y\<^esup>)"
    using eval_type unfolding cfunc_type_def by auto
  have x_type: "x \<in>\<^sub>c Y \<times>\<^sub>c (X\<^bsup>Y\<^esup>)"
    using conjunct1[OF facts] eval_dom by simp
  have lp_type: "left_cart_proj(Y, X\<^bsup>Y\<^esup>) : Y \<times>\<^sub>c (X\<^bsup>Y\<^esup>) \<rightarrow> Y"
    by (rule left_cart_proj_type)
  have projected: "left_cart_proj(Y, X\<^bsup>Y\<^esup>) \<circ>\<^sub>c x \<in>\<^sub>c Y"
    using x_type lp_type comp_type by blast
  have exists_y: "\<exists>z. z \<in>\<^sub>c Y" by (rule exI[where x="left_cart_proj(Y, X\<^bsup>Y\<^esup>) \<circ>\<^sub>c x"], rule projected)
  have no_y: "\<not>(\<exists>z. z \<in>\<^sub>c Y)" by (rule iffD1[OF is_empty_def Y_empty])
  have False by (rule notE[OF no_y exists_y])
  then show "x = y" by (rule FalseE)
qed

subsection \<open>Lifting Functions\<close>

text \<open>The definition below corresponds to Definition 2.5.1 in Halvorson.\<close>
definition exp_func :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc" ("(_)\<^bsup>_\<^esup>\<^sub>f" [100,100]100) where
  "exp_func(g, A) = (g \<circ>\<^sub>c eval_func(domain(g), A))\<^sup>\<sharp>"

lemma exp_func_def2:
  assumes "g : X \<rightarrow> Y"
  shows "exp_func(g, A) = (g \<circ>\<^sub>c eval_func(X, A))\<^sup>\<sharp>"
  using assms cfunc_type_def exp_func_def by auto

lemma exp_func_type[type_rule]:
  assumes "g : X \<rightarrow> Y"
  shows "g\<^bsup>A\<^esup>\<^sub>f : X\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
  using assms by (unfold exp_func_def2, typecheck_cfuncs)

lemma exp_of_id_is_id_of_exp:
  "id(X\<^bsup>A\<^esup>) = (id(X))\<^bsup>A\<^esup>\<^sub>f"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have lifted: "(id(X))\<^bsup>A\<^esup>\<^sub>f = (id(X) \<circ>\<^sub>c eval_func(X, A))\<^sup>\<sharp>"
    by (rule exp_func_def2[OF idX_type])
  have eval_type: "eval_func(X, A) : A \<times>\<^sub>c (X\<^bsup>A\<^esup>) \<rightarrow> X"
    by (rule eval_func_type)
  have id_eval: "id(X) \<circ>\<^sub>c eval_func(X, A) = eval_func(X, A)"
    by (rule id_left_unit2[OF eval_type])
  have lifted_id: "(id(X))\<^bsup>A\<^esup>\<^sub>f = id(X\<^bsup>A\<^esup>)"
    using lifted id_eval exponential_object_identity by simp
  show ?thesis by (rule sym[OF lifted_id])
qed

text \<open>The lemma below corresponds to a note below Definition 2.5.1 in Halvorson.\<close>
lemma exponential_square_diagram:
  assumes "g : Y \<rightarrow> Z"
  shows "(eval_func(Z, A)) \<circ>\<^sub>c (id\<^sub>c(A)\<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f)  = g \<circ>\<^sub>c (eval_func(Y, A))"
  using assms by (typecheck_cfuncs, simp add: exp_func_def2 transpose_func_def)

text \<open>The lemma below corresponds to Proposition 2.5.2 in Halvorson.\<close>
lemma transpose_of_comp:
  assumes f_type: "f: A \<times>\<^sub>c X \<rightarrow> Y" and g_type: "g: Y \<rightarrow> Z"
  shows "f: A \<times>\<^sub>c X \<rightarrow> Y \<and> g: Y \<rightarrow> Z  \<Longrightarrow>  (g \<circ>\<^sub>c f)\<^sup>\<sharp> = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>"
proof -
  assume "f: A \<times>\<^sub>c X \<rightarrow> Y \<and> g: Y \<rightarrow> Z"
  have gf_type: "g \<circ>\<^sub>c f : A \<times>\<^sub>c X \<rightarrow> Z"
    using f_type g_type comp_type by blast
  have fsharp_type: "f\<^sup>\<sharp> : X \<rightarrow> Y\<^bsup>A\<^esup>"
    by (rule transpose_func_type[OF f_type])
  have glift_type: "g\<^bsup>A\<^esup>\<^sub>f : Y\<^bsup>A\<^esup> \<rightarrow> Z\<^bsup>A\<^esup>"
    by (rule exp_func_type[OF g_type])
  have composite_type: "g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp> : X \<rightarrow> Z\<^bsup>A\<^esup>"
    using fsharp_type glift_type comp_type by blast
  have idA_type: "id(A) : A \<rightarrow> A" by (rule id_type)
  have cross_f_type: "id(A) \<times>\<^sub>f f\<^sup>\<sharp> : A \<times>\<^sub>c X \<rightarrow> A \<times>\<^sub>c (Y\<^bsup>A\<^esup>)"
    by (rule cfunc_cross_prod_type[OF idA_type fsharp_type])
  have cross_g_type: "id(A) \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f :
      A \<times>\<^sub>c (Y\<^bsup>A\<^esup>) \<rightarrow> A \<times>\<^sub>c (Z\<^bsup>A\<^esup>)"
    by (rule cfunc_cross_prod_type[OF idA_type glift_type])
  have evalZ_type: "eval_func(Z, A) : A \<times>\<^sub>c (Z\<^bsup>A\<^esup>) \<rightarrow> Z"
    by (rule eval_func_type)
  have evalY_type: "eval_func(Y, A) : A \<times>\<^sub>c (Y\<^bsup>A\<^esup>) \<rightarrow> Y"
    by (rule eval_func_type)
  have cross_comp: "id(A) \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>) =
      (id(A) \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>)"
    by (rule identity_distributes_across_composition[OF fsharp_type glift_type])
  have square: "eval_func(Z, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) =
      g \<circ>\<^sub>c eval_func(Y, A)"
    by (rule exponential_square_diagram[OF g_type])
  have f_eval: "eval_func(Y, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) = f"
    by (rule transpose_func_def[OF f_type])
  have right_eq: "(eval_func(Z, A)) \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>)) = g \<circ>\<^sub>c f"
  proof -
    have s1: "eval_func(Z, A) \<circ>\<^sub>c
        ((id(A) \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>)) =
        (eval_func(Z, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f)) \<circ>\<^sub>c
          (id(A) \<times>\<^sub>f f\<^sup>\<sharp>)"
      using comp_associative2[OF cross_f_type cross_g_type evalZ_type] by simp
    have s2: "(g \<circ>\<^sub>c eval_func(Y, A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) =
        g \<circ>\<^sub>c (eval_func(Y, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>))"
      using comp_associative2[OF cross_f_type evalY_type g_type] by simp
    show ?thesis using cross_comp s1 square s2 f_eval by simp
  qed
  have unique: "g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp> = (g \<circ>\<^sub>c f)\<^sup>\<sharp>"
    by (rule transpose_func_unique[OF gf_type composite_type right_eq])
  show "(g \<circ>\<^sub>c f)\<^sup>\<sharp> = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>"
    by (rule sym[OF unique])
qed

lemma exponential_object_identity2: 
  "id(X)\<^bsup>A\<^esup>\<^sub>f = id\<^sub>c(X\<^bsup>A\<^esup>)"
  by (rule sym[OF exp_of_id_is_id_of_exp])

text \<open>The lemma below corresponds to comments below Proposition 2.5.2 and above Definition 2.5.3 in Halvorson.\<close>
lemma eval_of_id_cross_id_sharp1:
  "eval_func(A \<times>\<^sub>c X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (id(A \<times>\<^sub>c X))\<^sup>\<sharp>) =
    id(A \<times>\<^sub>c X)"
  by (rule transpose_func_def[OF id_type])
lemma eval_of_id_cross_id_sharp2:
  assumes "a : Z \<rightarrow> A" "x : Z \<rightarrow> X"
  shows "(eval_func(A \<times>\<^sub>c X, A) \<circ>\<^sub>c
      (id(A) \<times>\<^sub>f (id(A \<times>\<^sub>c X))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>a,x\<rangle> = \<langle>a,x\<rangle>"
proof -
  have pair_type: "\<langle>a,x\<rangle> : Z \<rightarrow> A \<times>\<^sub>c X"
    by (rule cfunc_prod_type[OF assms])
  have id_pair: "id(A \<times>\<^sub>c X) \<circ>\<^sub>c \<langle>a,x\<rangle> = \<langle>a,x\<rangle>"
    by (rule id_left_unit2[OF pair_type])
  show ?thesis using eval_of_id_cross_id_sharp1 id_pair by simp
qed

lemma transpose_factors: 
  assumes f_type: "f: X \<rightarrow> Y"
  assumes g_type: "g: Y \<rightarrow> Z"
  shows "(g \<circ>\<^sub>c f)\<^bsup>A\<^esup>\<^sub>f = (g\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (f\<^bsup>A\<^esup>\<^sub>f)"
proof -
  have eval_type: "eval_func(X, A) : A \<times>\<^sub>c (X\<^bsup>A\<^esup>) \<rightarrow> X"
    by (rule eval_func_type)
  have f_eval_type: "f \<circ>\<^sub>c eval_func(X, A) : A \<times>\<^sub>c (X\<^bsup>A\<^esup>) \<rightarrow> Y"
    using eval_type f_type comp_type by blast
  have gf_type: "g \<circ>\<^sub>c f : X \<rightarrow> Z" using f_type g_type comp_type by blast
  have lhs: "(g \<circ>\<^sub>c f)\<^bsup>A\<^esup>\<^sub>f =
      ((g \<circ>\<^sub>c f) \<circ>\<^sub>c eval_func(X, A))\<^sup>\<sharp>"
    by (rule exp_func_def2[OF gf_type])
  have assoc: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c eval_func(X, A) =
      g \<circ>\<^sub>c (f \<circ>\<^sub>c eval_func(X, A))"
    using comp_associative2[OF eval_type f_type g_type] by simp
  have combined: "f \<circ>\<^sub>c eval_func(X, A) : A \<times>\<^sub>c (X\<^bsup>A\<^esup>) \<rightarrow> Y \<and>
      g : Y \<rightarrow> Z"
    by (intro conjI, rule f_eval_type, rule g_type)
  have transposed: "(g \<circ>\<^sub>c (f \<circ>\<^sub>c eval_func(X, A)))\<^sup>\<sharp> =
      g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c (f \<circ>\<^sub>c eval_func(X, A))\<^sup>\<sharp>"
    by (rule transpose_of_comp[OF f_eval_type g_type combined])
  have f_lift: "f\<^bsup>A\<^esup>\<^sub>f = (f \<circ>\<^sub>c eval_func(X, A))\<^sup>\<sharp>"
    by (rule exp_func_def2[OF f_type])
  show ?thesis using lhs assoc transposed f_lift by simp
qed

subsection \<open>Inverse Transpose Function (flat)\<close>

text \<open>The definition below corresponds to Definition 2.5.3 in Halvorson.\<close>
text \<open>HOL defines inverse transpose with Hilbert's @{text THE}. Plain FOL has no choice
operator, so we conservatively Skolemize the uniquely determined composite.\<close>
axiomatization inv_transpose_func :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>\<flat>" [100]100)
where inv_transpose_func_spec:
  "f : Z \<rightarrow> X\<^bsup>A\<^esup> \<Longrightarrow>
    f\<^sup>\<flat> = (eval_func(X, A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"

lemma inv_transpose_func_def2:
  assumes f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "\<exists> Z X A. domain(f) = Z \<and> codomain(f) = X\<^bsup>A\<^esup> \<and> f\<^sup>\<flat> = (eval_func(X, A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
proof -
  have dom_f: "domain(f) = Z" and cod_f: "codomain(f) = X\<^bsup>A\<^esup>"
    using f_type unfolding cfunc_type_def by auto
  have spec: "f\<^sup>\<flat> = (eval_func(X, A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
    by (rule inv_transpose_func_spec[OF f_type])
  show ?thesis
    by (rule exI[where x=Z], rule exI[where x=X], rule exI[where x=A],
        intro conjI, rule dom_f, rule cod_f, rule spec)
qed

lemma inv_transpose_func_def3:
  assumes f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> = (eval_func(X, A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
  by (rule inv_transpose_func_spec[OF f_type])

lemma flat_type[type_rule]:
  assumes f_type[type_rule]: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X"
  by (etcs_subst inv_transpose_func_def3, typecheck_cfuncs)

text \<open>The lemma below corresponds to Proposition 2.5.4 in Halvorson.\<close>
lemma inv_transpose_of_composition:
  assumes "f: X \<rightarrow> Y" "g: Y \<rightarrow> Z\<^bsup>A\<^esup>"
  shows "(g \<circ>\<^sub>c f)\<^sup>\<flat> = g\<^sup>\<flat> \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
  using assms comp_associative2 identity_distributes_across_composition
  by ((etcs_subst inv_transpose_func_def3)+, typecheck_cfuncs, auto)

text \<open>The lemma below corresponds to Proposition 2.5.5 in Halvorson.\<close>
lemma flat_cancels_sharp:
  "f : A \<times>\<^sub>c Z \<rightarrow> X  \<Longrightarrow> (f\<^sup>\<sharp>)\<^sup>\<flat> = f"
  using inv_transpose_func_def3 transpose_func_def transpose_func_type by fastforce

text \<open>The lemma below corresponds to Proposition 2.5.6 in Halvorson.\<close>
lemma sharp_cancels_flat:
 "f: Z \<rightarrow> X\<^bsup>A\<^esup>  \<Longrightarrow> (f\<^sup>\<flat>)\<^sup>\<sharp> = f"
proof - 
  assume f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  have flat_type': "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X" by (rule flat_type[OF f_type])
  have flat_eq: "f\<^sup>\<flat> = eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
    by (rule inv_transpose_func_def3[OF f_type])
  have eval_eq: "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f) = f\<^sup>\<flat>"
    by (rule sym[OF flat_eq])
  have unique: "f = (f\<^sup>\<flat>)\<^sup>\<sharp>"
    by (rule transpose_func_unique[OF flat_type' f_type eval_eq])
  show ?thesis by (rule sym[OF unique])
qed

lemma same_evals_equal:
  assumes f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>" and g_type: "g: Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f) = eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) \<Longrightarrow> f = g"
proof -
  assume evals_equal: "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f) =
      eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g)"
  have f_flat: "f\<^sup>\<flat> = eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
    by (rule inv_transpose_func_def3[OF f_type])
  have g_flat: "g\<^sup>\<flat> = eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g)"
    by (rule inv_transpose_func_def3[OF g_type])
  have flats_equal: "f\<^sup>\<flat> = g\<^sup>\<flat>" using f_flat g_flat evals_equal by simp
  have sharps_equal: "(f\<^sup>\<flat>)\<^sup>\<sharp> = (g\<^sup>\<flat>)\<^sup>\<sharp>"
    using flats_equal by simp
  have f_cancel: "(f\<^sup>\<flat>)\<^sup>\<sharp> = f" by (rule sharp_cancels_flat[OF f_type])
  have g_cancel: "(g\<^sup>\<flat>)\<^sup>\<sharp> = g" by (rule sharp_cancels_flat[OF g_type])
  show "f = g" using sharps_equal f_cancel g_cancel by simp
qed

lemma sharp_comp:
  assumes f_type[type_rule]: "f : A \<times>\<^sub>c Z \<rightarrow> X" and g_type[type_rule]: "g : W \<rightarrow> Z"
  shows "f\<^sup>\<sharp> \<circ>\<^sub>c g = (f \<circ>\<^sub>c (id(A) \<times>\<^sub>f g))\<^sup>\<sharp>"
proof (etcs_rule same_evals_equal[where X=X, where A=A])

  have "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c g)) = eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g)"
    using assms by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
  also have "... = f \<circ>\<^sub>c (id(A) \<times>\<^sub>f g)"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = eval_func(X, A) \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f (f \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f g))\<^sup>\<sharp>)"
    using assms by (typecheck_cfuncs, simp add: transpose_func_def)
  finally show "eval_func(X, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (f\<^sup>\<sharp> \<circ>\<^sub>c g)) = eval_func(X, A) \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f (f \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f g))\<^sup>\<sharp>)".
qed

lemma flat_pres_epi:
  assumes "nonempty(A)"
  assumes "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  assumes "epimorphism(f)"
  shows "epimorphism(f\<^sup>\<flat>)"
proof - 
  have equals: "f\<^sup>\<flat> = (eval_func(X, A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
    using assms(2) inv_transpose_func_def3 by auto
  have idA_f_epi: "epimorphism((id(A) \<times>\<^sub>f f))"
    using assms(2) assms(3) cfunc_cross_prod_surj epi_is_surj id_isomorphism id_type iso_imp_epi_and_monic surjective_is_epimorphism by blast
  have eval_epi: "epimorphism((eval_func(X, A)))"
    by (simp add: assms(1) eval_func_surj surjective_is_epimorphism)
  have "codomain ((id(A) \<times>\<^sub>f f)) = domain ((eval_func(X, A)))"
    using assms(2) cfunc_type_def by (typecheck_cfuncs, auto)
  then show ?thesis
    by (simp add: composition_of_epi_pair_is_epi equals eval_epi idA_f_epi)
qed

lemma transpose_inj_is_inj:
  assumes "g: X \<rightarrow> Y"
  assumes "injective(g)"
  shows "injective(g\<^bsup>A\<^esup>\<^sub>f)"
  unfolding injective_def
proof(clarify)
  fix x y 
  assume x_type[type_rule]: "x \<in>\<^sub>c domain (g\<^bsup>A\<^esup>\<^sub>f)" 
  assume y_type[type_rule]:"y \<in>\<^sub>c domain (g\<^bsup>A\<^esup>\<^sub>f)"
  assume eqs: "g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c x = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c y"
  have mono_g: "monomorphism(g)"
    by (rule injective_imp_monomorphism[OF assms(2)])
  have x_type'[type_rule]: "x \<in>\<^sub>c  X\<^bsup>A\<^esup>"
    using assms(1) cfunc_type_def exp_func_type by (typecheck_cfuncs, force)
  have lift_dom: "domain(g\<^bsup>A\<^esup>\<^sub>f) = X\<^bsup>A\<^esup>"
    using assms(1) cfunc_type_def exp_func_type by blast
  have y_type'[type_rule]: "y \<in>\<^sub>c  X\<^bsup>A\<^esup>"
    using lift_dom y_type by simp
  have eval_type': "eval_func(X,A) : A \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X"
    by (rule eval_func_type)
  have base_type: "g \<circ>\<^sub>c eval_func(X,A) : A \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> Y"
    using assms(1) eval_type' comp_type by blast
  have dom_g: "domain(g) = X"
    using assms(1) unfolding cfunc_type_def by auto
  have lifted_eq:
    "(g \<circ>\<^sub>c eval_func(X,A))\<^sup>\<sharp> \<circ>\<^sub>c x =
     (g \<circ>\<^sub>c eval_func(X,A))\<^sup>\<sharp> \<circ>\<^sub>c y"
    using eqs dom_g unfolding exp_func_def by simp
  have sx:
    "(g \<circ>\<^sub>c eval_func(X,A))\<^sup>\<sharp> \<circ>\<^sub>c x =
     ((g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x))\<^sup>\<sharp>"
    using sharp_comp[OF base_type x_type'] .
  have sy:
    "(g \<circ>\<^sub>c eval_func(X,A))\<^sup>\<sharp> \<circ>\<^sub>c y =
     ((g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y))\<^sup>\<sharp>"
    using sharp_comp[OF base_type y_type'] .
  have sharp_eq:
    "((g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x))\<^sup>\<sharp> =
     ((g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y))\<^sup>\<sharp>"
    using lifted_eq sx sy by simp
  have left_type:
    "(g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x) :
      A \<times>\<^sub>c \<one> \<rightarrow> Y"
    using base_type x_type' by (typecheck_cfuncs)
  have right_type:
    "(g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y) :
      A \<times>\<^sub>c \<one> \<rightarrow> Y"
    using base_type y_type' by (typecheck_cfuncs)
  have comp_eq:
    "(g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x) =
     (g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y)"
  proof -
    have
      "(((g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x))\<^sup>\<sharp>)\<^sup>\<flat> =
       (((g \<circ>\<^sub>c eval_func(X,A)) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y))\<^sup>\<sharp>)\<^sup>\<flat>"
      using sharp_eq by simp
    then show ?thesis
      using flat_cancels_sharp[OF left_type] flat_cancels_sharp[OF right_type] by simp
  qed
  have gx_eq_gy:
    "g \<circ>\<^sub>c (eval_func(X,A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x)) =
     g \<circ>\<^sub>c (eval_func(X,A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y))"
    using comp_eq assms(1) eval_type' x_type' y_type'
    by (typecheck_cfuncs, simp add: comp_associative2)
  have qx_type:
    "eval_func(X,A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x) :
      A \<times>\<^sub>c \<one> \<rightarrow> X"
    using eval_type' x_type' by (typecheck_cfuncs)
  have qy_type:
    "eval_func(X,A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y) :
      A \<times>\<^sub>c \<one> \<rightarrow> X"
    using eval_type' y_type' by (typecheck_cfuncs)
  have evals_eq:
    "eval_func(X,A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f x) =
     eval_func(X,A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f y)"
    using mono_g monomorphism_def3[OF assms(1)] qx_type qy_type gx_eq_gy by auto
  show "x = y"
    by (rule same_evals_equal[OF x_type' y_type' evals_eq])
qed

lemma eval_func_X_one_injective:
  "injective(eval_func(X,\<one>))"
proof (cases "\<exists> x. x \<in>\<^sub>c X")
  assume "\<exists>x. x \<in>\<^sub>c X"
  show "injective(eval_func(X,\<one>))"
    unfolding injective_def
  proof clarify
    fix a b
    assume a_type: "a \<in>\<^sub>c domain(eval_func(X,\<one>))"
    assume b_type: "b \<in>\<^sub>c domain(eval_func(X,\<one>))"
    assume evals_equal: "eval_func(X,\<one>) \<circ>\<^sub>c a = eval_func(X,\<one>) \<circ>\<^sub>c b"

    have eval_dom: "domain(eval_func(X,\<one>)) = \<one> \<times>\<^sub>c (X\<^bsup>\<one>\<^esup>)"
      using cfunc_type_def eval_func_type by auto

    have a_prod_type: "a : \<one> \<rightarrow> \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using a_type eval_dom unfolding cfunc_type_def by auto
    obtain a1 A where
      a_pair: "a = \<langle>a1,A\<rangle>" and
      a1_type: "a1 : \<one> \<rightarrow> \<one>" and
      A_type: "A \<in>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using cart_prod_decomp[OF a_prod_type] by auto
    have a1_eq: "a1 = id(\<one>)"
      using a1_type element_of_1 by auto
    have a_def: "a = \<langle>id(\<one>),A\<rangle>"
      using a_pair a1_eq by simp

    have b_prod_type: "b : \<one> \<rightarrow> \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using b_type eval_dom unfolding cfunc_type_def by auto
    obtain b1 B where
      b_pair: "b = \<langle>b1,B\<rangle>" and
      b1_type: "b1 : \<one> \<rightarrow> \<one>" and
      B_type: "B \<in>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using cart_prod_decomp[OF b_prod_type] by auto
    have b1_eq: "b1 = id(\<one>)"
      using b1_type element_of_1 by auto
    have b_def: "b = \<langle>id(\<one>),B\<rangle>"
      using b_pair b1_eq by simp

    have Aflat_type: "A\<^sup>\<flat> : \<one> \<times>\<^sub>c \<one> \<rightarrow> X"
      by (rule flat_type[OF A_type])
    have Bflat_type: "B\<^sup>\<flat> : \<one> \<times>\<^sub>c \<one> \<rightarrow> X"
      by (rule flat_type[OF B_type])
    have Aflat_def:
      "A\<^sup>\<flat> = eval_func(X,\<one>) \<circ>\<^sub>c (id(\<one>) \<times>\<^sub>f A)"
      by (rule inv_transpose_func_def3[OF A_type])
    have Bflat_def:
      "B\<^sup>\<flat> = eval_func(X,\<one>) \<circ>\<^sub>c (id(\<one>) \<times>\<^sub>f B)"
      by (rule inv_transpose_func_def3[OF B_type])
    have flat_eq: "A\<^sup>\<flat> = B\<^sup>\<flat>"
    proof (rule one_separator[OF Aflat_type Bflat_type])
      fix z
      assume z_type: "z : \<one> \<rightarrow> \<one> \<times>\<^sub>c \<one>"
      obtain u v where z_pair: "z = \<langle>u,v\<rangle>"
        and u_type: "u : \<one> \<rightarrow> \<one>" and v_type: "v : \<one> \<rightarrow> \<one>"
        using cart_prod_decomp[OF z_type] by auto
      have z_eq: "z = \<langle>id(\<one>),id(\<one>)\<rangle>"
        using z_pair element_of_1[OF u_type] element_of_1[OF v_type] by simp
      have cross_A:
        "(id(\<one>) \<times>\<^sub>f A) \<circ>\<^sub>c \<langle>id(\<one>),id(\<one>)\<rangle> =
         \<langle>id(\<one>),A\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod[OF id_type id_type id_type A_type]
              id_left_unit2[OF id_type] id_right_unit2[OF A_type] by simp
      have cross_B:
        "(id(\<one>) \<times>\<^sub>f B) \<circ>\<^sub>c \<langle>id(\<one>),id(\<one>)\<rangle> =
         \<langle>id(\<one>),B\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod[OF id_type id_type id_type B_type]
              id_left_unit2[OF id_type] id_right_unit2[OF B_type] by simp
      have diag_type:
        "\<langle>id(\<one>),id(\<one>)\<rangle> : \<one> \<rightarrow> \<one> \<times>\<^sub>c \<one>"
        by (typecheck_cfuncs)
      have cross_A_type:
        "id(\<one>) \<times>\<^sub>f A :
          \<one> \<times>\<^sub>c \<one> \<rightarrow> \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
        using A_type by (typecheck_cfuncs)
      have cross_B_type:
        "id(\<one>) \<times>\<^sub>f B :
          \<one> \<times>\<^sub>c \<one> \<rightarrow> \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
        using B_type by (typecheck_cfuncs)
      have eval_type':
        "eval_func(X,\<one>) : \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup> \<rightarrow> X"
        by (rule eval_func_type)
      have eval_pair_eq:
        "eval_func(X,\<one>) \<circ>\<^sub>c \<langle>id(\<one>),A\<rangle> =
         eval_func(X,\<one>) \<circ>\<^sub>c \<langle>id(\<one>),B\<rangle>"
        using evals_equal a_def b_def by simp
      have left_assoc:
        "(eval_func(X,\<one>) \<circ>\<^sub>c (id(\<one>) \<times>\<^sub>f A)) \<circ>\<^sub>c
           \<langle>id(\<one>),id(\<one>)\<rangle> =
         eval_func(X,\<one>) \<circ>\<^sub>c
           ((id(\<one>) \<times>\<^sub>f A) \<circ>\<^sub>c \<langle>id(\<one>),id(\<one>)\<rangle>)"
        using comp_associative2[OF diag_type cross_A_type eval_type'] by simp
      have right_assoc:
        "(eval_func(X,\<one>) \<circ>\<^sub>c (id(\<one>) \<times>\<^sub>f B)) \<circ>\<^sub>c
           \<langle>id(\<one>),id(\<one>)\<rangle> =
         eval_func(X,\<one>) \<circ>\<^sub>c
           ((id(\<one>) \<times>\<^sub>f B) \<circ>\<^sub>c \<langle>id(\<one>),id(\<one>)\<rangle>)"
        using comp_associative2[OF diag_type cross_B_type eval_type'] by simp
      show "A\<^sup>\<flat> \<circ>\<^sub>c z = B\<^sup>\<flat> \<circ>\<^sub>c z"
        using Aflat_def Bflat_def z_eq left_assoc right_assoc cross_A cross_B eval_pair_eq
        by simp
    qed
    have "A = B"
    proof -
      have "A\<^sup>\<flat>\<^sup>\<sharp> = B\<^sup>\<flat>\<^sup>\<sharp>"
        using flat_eq by simp
      then show ?thesis
        using sharp_cancels_flat[OF A_type] sharp_cancels_flat[OF B_type] by simp
    qed
    then show "a = b"
      by (simp add: a_def b_def)
  qed
next
  assume no_x: "\<not>(\<exists>x. x \<in>\<^sub>c X)"
  then show "injective(eval_func(X,\<one>))"
    unfolding injective_def
  proof clarify
    fix a b
    assume a_type: "a \<in>\<^sub>c domain(eval_func(X,\<one>))"
    have eval_type': "eval_func(X,\<one>) : \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup> \<rightarrow> X"
      by (rule eval_func_type)
    have eval_dom: "domain(eval_func(X,\<one>)) = \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using eval_type' unfolding cfunc_type_def by auto
    have a_type': "a : \<one> \<rightarrow> \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using a_type eval_dom unfolding cfunc_type_def by auto
    have "eval_func(X,\<one>) \<circ>\<^sub>c a \<in>\<^sub>c X"
      using comp_type[OF a_type' eval_type'] .
    then show "a = b"
      using no_x by auto
  qed
qed

text \<open>In the lemma below, the nonempty(assumption) is required.
      Consider, for example, @{term "X = \<Omega>"} and @{term "A = \<emptyset>"}\<close>
lemma sharp_pres_mono:
  assumes "f : A \<times>\<^sub>c Z \<rightarrow> X"
  assumes "monomorphism(f)"
  assumes "nonempty(A)"
  shows   "monomorphism(f\<^sup>\<sharp>)"
  unfolding monomorphism_def2
proof(clarify)
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

   then have epic: "epimorphism(right_cart_proj(A, U))"
     using assms(3) nonempty_left_imp_right_proj_epimorphism by blast

   have fIdg_is_fIdh: "f \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) = f \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)"
   proof -
    have fg_type: "f\<^sup>\<sharp> \<circ>\<^sub>c g : U \<rightarrow> X\<^bsup>A\<^esup>"
      using g_type2 f_sharp_type2 comp_type by blast
    have fh_type: "f\<^sup>\<sharp> \<circ>\<^sub>c h : U \<rightarrow> X\<^bsup>A\<^esup>"
      using h_type2 f_sharp_type2 comp_type by blast
    have fflat: "f\<^sup>\<sharp>\<^sup>\<flat> = f"
      by (rule flat_cancels_sharp[OF assms(1)])
    have fg_flat:
      "(f\<^sup>\<sharp> \<circ>\<^sub>c g)\<^sup>\<flat> =
       f\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c (id(A) \<times>\<^sub>f g)"
      by (rule inv_transpose_of_composition[OF g_type2 f_sharp_type2])
    have fh_flat:
      "(f\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat> =
       f\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)"
      by (rule inv_transpose_of_composition[OF h_type2 f_sharp_type2])
    have flat_composites_equal:
      "(f\<^sup>\<sharp> \<circ>\<^sub>c g)\<^sup>\<flat> =
       (f\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat>"
      using equals by simp
    show ?thesis
      using fflat fg_flat fh_flat flat_composites_equal by simp
   qed
   then have idg_is_idh: "(id(A) \<times>\<^sub>f g) = (id(A) \<times>\<^sub>f h)"
    using assms fIdg_is_fIdh idg_type idh_type monomorphism_def3 by blast
   then have "g \<circ>\<^sub>c (right_cart_proj(A, U)) = h \<circ>\<^sub>c (right_cart_proj(A, U))"
   proof -
     have projected:
       "right_cart_proj(A,Z) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) =
        right_cart_proj(A,Z) \<circ>\<^sub>c (id(A) \<times>\<^sub>f h)"
       using idg_is_idh by simp
     have project_g:
       "right_cart_proj(A,Z) \<circ>\<^sub>c (id(A) \<times>\<^sub>f g) =
        g \<circ>\<^sub>c right_cart_proj(A,U)"
       by (rule right_cart_proj_cfunc_cross_prod[OF id_type g_type2])
     have project_h:
       "right_cart_proj(A,Z) \<circ>\<^sub>c (id(A) \<times>\<^sub>f h) =
        h \<circ>\<^sub>c right_cart_proj(A,U)"
       by (rule right_cart_proj_cfunc_cross_prod[OF id_type h_type2])
     show ?thesis
       using projected project_g project_h by simp
   qed
   then show "g = h"
    using epic epimorphism_def2 g_type2 h_type2 right_cart_proj_type by blast
qed

subsection \<open>Metafunctions and their Inverses (Cnufatems)\<close>

subsubsection \<open>Metafunctions\<close>

definition metafunc :: "cfunc \<Rightarrow> cfunc" where
  "metafunc(f) \<equiv> (f \<circ>\<^sub>c left_cart_proj(domain(f),\<one>))\<^sup>\<sharp>"

lemma metafunc_def2:
  assumes "f : X \<rightarrow> Y"
  shows "metafunc(f) = (f \<circ>\<^sub>c (left_cart_proj(X, \<one>)))\<^sup>\<sharp>"
  using assms unfolding metafunc_def cfunc_type_def by auto

lemma metafunc_type[type_rule]:
  assumes "f : X \<rightarrow> Y"
  shows "metafunc(f) \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  using assms by (unfold metafunc_def2, typecheck_cfuncs)

lemma eval_lemma:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes x_type[type_rule]: "x  \<in>\<^sub>c X"
  shows "eval_func(Y, X) \<circ>\<^sub>c \<langle>x, metafunc(f)\<rangle> = f \<circ>\<^sub>c x"
proof - 
  have "eval_func(Y, X) \<circ>\<^sub>c \<langle>x, metafunc(f)\<rangle> = eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (f \<circ>\<^sub>c (left_cart_proj(X, \<one>)))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 metafunc_def2)
  also have "... = (eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (f \<circ>\<^sub>c (left_cart_proj(X, \<one>)))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
    using comp_associative2 by (typecheck_cfuncs, blast)
  also have "... = (f \<circ>\<^sub>c (left_cart_proj(X, \<one>))) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle>"
  proof -
    have base_type:
      "f \<circ>\<^sub>c left_cart_proj(X,\<one>) : X \<times>\<^sub>c \<one> \<rightarrow> Y"
      using f_type by (typecheck_cfuncs)
    have eval_transpose:
      "eval_func(Y,X) \<circ>\<^sub>c
        (id(X) \<times>\<^sub>f (f \<circ>\<^sub>c left_cart_proj(X,\<one>))\<^sup>\<sharp>) =
       f \<circ>\<^sub>c left_cart_proj(X,\<one>)"
      by (rule transpose_func_def[OF base_type])
    show ?thesis
      using eval_transpose by simp
  qed
  also have "... = f \<circ>\<^sub>c x"
  proof -
    have lp_type:
      "left_cart_proj(X,\<one>) : X \<times>\<^sub>c \<one> \<rightarrow> X"
      by (rule left_cart_proj_type)
    have pair_type: "\<langle>x,id(\<one>)\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c \<one>"
      using x_type by (typecheck_cfuncs)
    have projected:
      "left_cart_proj(X,\<one>) \<circ>\<^sub>c \<langle>x,id(\<one>)\<rangle> = x"
      by (rule left_cart_proj_cfunc_prod[OF x_type id_type])
    have associated:
      "(f \<circ>\<^sub>c left_cart_proj(X,\<one>)) \<circ>\<^sub>c \<langle>x,id(\<one>)\<rangle> =
       f \<circ>\<^sub>c (left_cart_proj(X,\<one>) \<circ>\<^sub>c \<langle>x,id(\<one>)\<rangle>)"
      using comp_associative2[OF pair_type lp_type f_type] by simp
    show ?thesis
      using associated projected by simp
  qed
  finally show "eval_func(Y, X) \<circ>\<^sub>c \<langle>x, metafunc(f)\<rangle> = f \<circ>\<^sub>c x".
qed

subsubsection \<open>Inverse Metafunctions (Cnufatems)\<close>

text \<open>As for inverse transpose, HOL's @{text THE}-definition is replaced by its uniquely
determined Skolem specification.\<close>
axiomatization cnufatem :: "cfunc \<Rightarrow> cfunc"
where cnufatem_spec:
  "f \<in>\<^sub>c Y\<^bsup>X\<^esup> \<Longrightarrow>
    cnufatem(f) = eval_func(Y, X) \<circ>\<^sub>c \<langle>id(X), f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"

lemma cnufatem_def2:
  assumes "f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "cnufatem(f) = eval_func(Y, X) \<circ>\<^sub>c \<langle>id(X), f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
  by (rule cnufatem_spec[OF assms])

lemma cnufatem_type[type_rule]:
  assumes "f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "cnufatem(f) : X  \<rightarrow> Y"
  using assms cnufatem_def2 
  by (auto, typecheck_cfuncs)

lemma cnufatem_metafunc:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  shows "cnufatem (metafunc(f)) = f"
proof -
  have mf_type: "metafunc(f) \<in>\<^sub>c Y\<^bsup>X\<^esup>"
    by (rule metafunc_type[OF f_type])
  have cmf_type: "cnufatem(metafunc(f)) : X \<rightarrow> Y"
    by (rule cnufatem_type[OF mf_type])
  show ?thesis
  proof (rule one_separator[OF cmf_type f_type])
  fix x
  assume x_type[type_rule]: "x \<in>\<^sub>c X"
    have cnufatem_eq:
      "cnufatem(metafunc(f)) =
       eval_func(Y,X) \<circ>\<^sub>c
         \<langle>id(X),metafunc(f) \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>"
      by (rule cnufatem_def2[OF mf_type])
    have mf_pair:
      "\<langle>id(X),metafunc(f) \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x =
       \<langle>x,metafunc(f)\<rangle>"
      using cart_prod_extract_left[OF x_type mf_type] by simp
    have pair_map_type:
      "\<langle>id(X),metafunc(f) \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> :
        X \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>"
      using mf_type by (typecheck_cfuncs)
    have eval_type': "eval_func(Y,X) : X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Y"
      by (rule eval_func_type)
    have associated:
      "(eval_func(Y,X) \<circ>\<^sub>c
        \<langle>id(X),metafunc(f) \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x =
       eval_func(Y,X) \<circ>\<^sub>c
        (\<langle>id(X),metafunc(f) \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x)"
      using comp_associative2[OF x_type pair_map_type eval_type'] by simp
    have evaluated:
      "eval_func(Y,X) \<circ>\<^sub>c \<langle>x,metafunc(f)\<rangle> = f \<circ>\<^sub>c x"
      by (rule eval_lemma[OF f_type x_type])
    show "cnufatem(metafunc(f)) \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
      using cnufatem_eq associated mf_pair evaluated by simp
  qed
qed

lemma metafunc_cnufatem:
  assumes f_type[type_rule]: "f \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "metafunc (cnufatem(f)) = f"
proof -
  have cf_type: "cnufatem(f) : X \<rightarrow> Y"
    by (rule cnufatem_type[OF f_type])
  have mcf_type: "metafunc(cnufatem(f)) \<in>\<^sub>c Y\<^bsup>X\<^esup>"
    by (rule metafunc_type[OF cf_type])
  have left_type:
    "eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f metafunc(cnufatem(f))) :
      X \<times>\<^sub>c \<one> \<rightarrow> Y"
    using mcf_type by (typecheck_cfuncs)
  have right_type:
    "eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) :
      X \<times>\<^sub>c \<one> \<rightarrow> Y"
    using f_type by (typecheck_cfuncs)
  have evals_eq:
    "eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f metafunc(cnufatem(f))) =
     eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)"
  proof (rule one_separator[OF left_type right_type])
  fix x1
  assume x1_type[type_rule]: "x1 \<in>\<^sub>c X \<times>\<^sub>c \<one>"
  then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and x_def: " x1 = \<langle>x, id(\<one>)\<rangle>"
    using cart_prod_decomp one_unique_element by (typecheck_cfuncs, blast)
  have "(eval_func(Y, X) \<circ>\<^sub>c id\<^sub>c(X) \<times>\<^sub>f metafunc (cnufatem(f))) \<circ>\<^sub>c \<langle>x, id(\<one>)\<rangle> =
         eval_func(Y, X) \<circ>\<^sub>c \<langle>x , metafunc (cnufatem(f))\<rangle>"
  proof -
    have pair_type: "\<langle>x,id(\<one>)\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c \<one>"
      using x_type by (typecheck_cfuncs)
    have cross_type:
      "id(X) \<times>\<^sub>f metafunc(cnufatem(f)) :
        X \<times>\<^sub>c \<one> \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>"
      using mcf_type by (typecheck_cfuncs)
    have eval_type': "eval_func(Y,X) : X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Y"
      by (rule eval_func_type)
    have cross_pair:
      "(id(X) \<times>\<^sub>f metafunc(cnufatem(f))) \<circ>\<^sub>c
        \<langle>x,id(\<one>)\<rangle> = \<langle>x,metafunc(cnufatem(f))\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF x_type id_type id_type mcf_type]
        id_left_unit2[OF x_type] id_right_unit2[OF mcf_type] by simp
    have associated:
      "(eval_func(Y,X) \<circ>\<^sub>c
        (id(X) \<times>\<^sub>f metafunc(cnufatem(f)))) \<circ>\<^sub>c
        \<langle>x,id(\<one>)\<rangle> =
       eval_func(Y,X) \<circ>\<^sub>c
        ((id(X) \<times>\<^sub>f metafunc(cnufatem(f))) \<circ>\<^sub>c
          \<langle>x,id(\<one>)\<rangle>)"
      using comp_associative2[OF pair_type cross_type eval_type'] by simp
    show ?thesis
      using associated cross_pair by simp
  qed
  also have "... = (cnufatem(f)) \<circ>\<^sub>c x"
    using eval_lemma by (typecheck_cfuncs, blast)
  also have "... = (eval_func(Y, X) \<circ>\<^sub>c \<langle>id(X), f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x"
    using cnufatem_def2[OF f_type] by simp
  also have "... = eval_func(Y,X) \<circ>\<^sub>c \<langle>x,f\<rangle>"
  proof -
    have pair_map_type:
      "\<langle>id(X),f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> :
        X \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>"
      using f_type by (typecheck_cfuncs)
    have eval_type': "eval_func(Y,X) : X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Y"
      by (rule eval_func_type)
    have pair_eq:
      "\<langle>id(X),f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x =
       \<langle>x,f\<rangle>"
      using cart_prod_extract_left[OF x_type f_type] by simp
    have associated:
      "(eval_func(Y,X) \<circ>\<^sub>c
        \<langle>id(X),f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x =
       eval_func(Y,X) \<circ>\<^sub>c
        (\<langle>id(X),f \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x)"
      using comp_associative2[OF x_type pair_map_type eval_type'] by simp
    show ?thesis
      using associated pair_eq by simp
  qed
  also have "... = (eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)) \<circ>\<^sub>c
      \<langle>x,id(\<one>)\<rangle>"
  proof -
    have pair_type: "\<langle>x,id(\<one>)\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c \<one>"
      using x_type by (typecheck_cfuncs)
    have cross_type:
      "id(X) \<times>\<^sub>f f : X \<times>\<^sub>c \<one> \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>"
      using f_type by (typecheck_cfuncs)
    have eval_type': "eval_func(Y,X) : X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Y"
      by (rule eval_func_type)
    have cross_pair:
      "(id(X) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>x,id(\<one>)\<rangle> = \<langle>x,f\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod[OF x_type id_type id_type f_type]
        id_left_unit2[OF x_type] id_right_unit2[OF f_type] by simp
    have associated:
      "(eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)) \<circ>\<^sub>c
        \<langle>x,id(\<one>)\<rangle> =
       eval_func(Y,X) \<circ>\<^sub>c
        ((id(X) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>x,id(\<one>)\<rangle>)"
      using comp_associative2[OF pair_type cross_type eval_type'] by simp
    show ?thesis
      using associated cross_pair by simp
  qed
  finally have pair_result:
    "(eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f metafunc(cnufatem(f)))) \<circ>\<^sub>c
       \<langle>x,id(\<one>)\<rangle> =
     (eval_func(Y,X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)) \<circ>\<^sub>c
       \<langle>x,id(\<one>)\<rangle>" .
  show "(eval_func(Y, X) \<circ>\<^sub>c id\<^sub>c(X) \<times>\<^sub>f metafunc (cnufatem(f))) \<circ>\<^sub>c x1 =
        (eval_func(Y, X) \<circ>\<^sub>c id\<^sub>c(X) \<times>\<^sub>f f) \<circ>\<^sub>c x1"
    by (rule subst[OF sym[OF x_def]], rule pair_result)
  qed
  show ?thesis
    by (rule same_evals_equal[OF mcf_type f_type evals_eq])
qed

subsubsection \<open>Metafunction Composition\<close>

definition meta_comp :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc"  where 
  "meta_comp(X,Y,Z) =
    (eval_func(Z,Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>,Y) \<circ>\<^sub>c
      (id(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y,X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>,X))) \<circ>\<^sub>c
      associate_right(Z\<^bsup>Y\<^esup>,Y\<^bsup>X\<^esup>,X) \<circ>\<^sub>c
      swap(X,Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>))\<^sup>\<sharp>"

lemma meta_comp_type[type_rule]:
  "meta_comp(X, Y, Z) : Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Z\<^bsup>X\<^esup>"
  unfolding meta_comp_def by typecheck_cfuncs

axiomatization meta_comp2 :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<box>" 55)
where meta_comp2_spec:
  "g : W \<rightarrow> Y\<^bsup>X\<^esup> \<Longrightarrow>
    f \<box> g = (f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>"

lemma meta_comp2_def2: 
  assumes "f: W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g: W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "f \<box> g  = (f\<^sup>\<flat>  \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>"
  by (rule meta_comp2_spec[OF assms(2)])

lemma meta_comp2_type[type_rule]: 
  assumes "f: W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g: W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "f \<box> g : W \<rightarrow> Z\<^bsup>X\<^esup>"
proof - 
  have "(f\<^sup>\<flat>  \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> : W \<rightarrow> Z\<^bsup>X\<^esup>"
    using assms by typecheck_cfuncs
  then show ?thesis 
    using assms by (simp add: meta_comp2_def2)
qed

lemma meta_comp2_elements_aux: 
  assumes "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>"
  assumes "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  assumes "x \<in>\<^sub>c X"
  shows "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>)  \<circ>\<^sub>c \<langle>x, id\<^sub>c(\<one>)\<rangle> = eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>,f\<rangle>"
proof-
    have "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>)  \<circ>\<^sub>c \<langle>x, id\<^sub>c(\<one>)\<rangle>=  f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>  \<circ>\<^sub>c \<langle>x, id\<^sub>c(\<one>)\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat> \<circ>\<^sub>c \<langle>x, id\<^sub>c(\<one>)\<rangle>,right_cart_proj(X, \<one>) \<circ>\<^sub>c \<langle>x, id\<^sub>c(\<one>)\<rangle> \<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat> \<circ>\<^sub>c \<langle>x, id\<^sub>c(\<one>)\<rangle>,id\<^sub>c(\<one>)\<rangle>"
      using assms one_unique_element by (typecheck_cfuncs, fastforce)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>(eval_func(Y, X)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x, id\<^sub>c(\<one>)\<rangle>,id\<^sub>c(\<one>)\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def3)
    also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>(eval_func(Y, X)) \<circ>\<^sub>c  \<langle>x, g\<rangle>,id\<^sub>c(\<one>)\<rangle>"
      using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs,force)
    also have "... = (eval_func(Z, Y)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>(eval_func(Y, X)) \<circ>\<^sub>c  \<langle>x, g\<rangle>,id\<^sub>c(\<one>)\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def3)
    also have "... = (eval_func(Z, Y)) \<circ>\<^sub>c  \<langle>(eval_func(Y, X)) \<circ>\<^sub>c  \<langle>x, g\<rangle>,f\<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
    finally show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>) \<circ>\<^sub>c \<langle>x,id\<^sub>c(\<one>)\<rangle> = eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>,f\<rangle>".
qed

lemma meta_comp2_def3: 
  assumes "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>"
  assumes "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "f \<box> g = metafunc ((cnufatem(f)) \<circ>\<^sub>c (cnufatem(g)))"
  using assms
proof(unfold meta_comp2_def2 cnufatem_def2 metafunc_def meta_comp_def)          
  have "f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle> = ((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c  left_cart_proj(X, \<one>)"
  proof(rule one_separator[where X = "X \<times>\<^sub>c \<one>", where Y = Z])
    show "f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle> : X \<times>\<^sub>c \<one> \<rightarrow> Z"
      using assms by typecheck_cfuncs
    show "((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>) : X \<times>\<^sub>c \<one> \<rightarrow> Z"
      using assms by typecheck_cfuncs
  next
    fix x1 
    assume x1_type[type_rule]: "x1  \<in>\<^sub>c (X \<times>\<^sub>c \<one>)"
    then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and x_def: "x1 = \<langle>x, id\<^sub>c(\<one>)\<rangle>"
      using cart_prod_decomp one_unique_element
      by (typecheck_cfuncs, force)
    then have "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>) \<circ>\<^sub>c x1 = eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>,f\<rangle>"
      using assms meta_comp2_elements_aux x_def by blast
    also have "... = eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      using assms cart_prod_extract_left comp_associative2
      by (typecheck_cfuncs, force)
    also have "... =  (eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    also have "... = ((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>) \<circ>\<^sub>c x1"
      using assms id_type left_cart_proj_cfunc_prod x_def by (typecheck_cfuncs, auto)
    also have "... = (((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c x1"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    finally show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>) \<circ>\<^sub>c x1 = (((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c x1".      
  qed
  moreover have "domain ((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) = X"
    using assms by (typecheck_cfuncs, unfold cfunc_type_def, fastforce)
  ultimately show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>)\<^sup>\<sharp> = (((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(domain ((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>), \<one>))\<^sup>\<sharp>"
    by simp
qed

lemma meta_comp2_def4:
  assumes f_type[type_rule]: "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>" and g_type[type_rule]: "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  shows "f \<box> g   = meta_comp(X, Y, Z) \<circ>\<^sub>c \<langle>f,g\<rangle>"
  using assms 
proof(unfold meta_comp2_def2 cnufatem_def2 metafunc_def meta_comp_def)          
  have "(((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>)) =  
          (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>f,g\<rangle>)"
  proof(etcs_rule one_separator)
    fix x1 
    assume x1_type[type_rule]: "x1  \<in>\<^sub>c X \<times>\<^sub>c \<one>"
    then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and x_def: "x1 = \<langle>x, id\<^sub>c(\<one>)\<rangle>"
      using cart_prod_decomp one_unique_element
      by (typecheck_cfuncs, force)
    have "(((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c x1 = 
           ((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>) \<circ>\<^sub>c x1"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c x"
      using id_type left_cart_proj_cfunc_prod x_def by (typecheck_cfuncs, force)
    also have "... =  (eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x"
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle> \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>x ,g\<rangle>"
      using assms cart_prod_extract_left by (typecheck_cfuncs, fastforce)
    also have "... = eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c \<langle>x ,g\<rangle> ,f\<rangle>"
      using assms cart_prod_extract_left by (typecheck_cfuncs, fastforce)
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y)) \<circ>\<^sub>c \<langle>f, eval_func(Y, X) \<circ>\<^sub>c \<langle>x, g\<rangle>\<rangle>"
    proof -
      have h_type[type_rule]: "eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle> \<in>\<^sub>c Y"
        using assms by typecheck_cfuncs
      have swap_pair:
        "swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c
          \<langle>f, eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>\<rangle> =
          \<langle>eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>, f\<rangle>"
        by (rule swap_ap[OF f_type h_type])
      have pair_type[type_rule]:
        "\<langle>f, eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>\<rangle> \<in>\<^sub>c
          Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y"
        using assms by typecheck_cfuncs
      have swap_type'[type_rule]:
        "swap(Z\<^bsup>Y\<^esup>, Y) :
          Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c Z\<^bsup>Y\<^esup>"
        by typecheck_cfuncs
      have eval_type'[type_rule]:
        "eval_func(Z, Y) : Y \<times>\<^sub>c Z\<^bsup>Y\<^esup> \<rightarrow> Z"
        by typecheck_cfuncs
      show ?thesis
      proof -
        have "eval_func(Z, Y) \<circ>\<^sub>c
            \<langle>eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>, f\<rangle> =
            eval_func(Z, Y) \<circ>\<^sub>c
              (swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c
                \<langle>f, eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>\<rangle>)"
          using swap_pair by simp
        also have "... =
            (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y)) \<circ>\<^sub>c
              \<langle>f, eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>\<rangle>"
          by (rule comp_associative2[OF pair_type swap_type' eval_type'])
        finally show ?thesis .
      qed
    qed
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y)) \<circ>\<^sub>c \<langle>id\<^sub>c(Z\<^bsup>Y\<^esup>) \<circ>\<^sub>c f, (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X)) \<circ>\<^sub>c \<langle>g, x\<rangle>\<rangle>"
    proof -
      have id_f: "id\<^sub>c(Z\<^bsup>Y\<^esup>) \<circ>\<^sub>c f = f"
        by (rule id_left_unit2[OF f_type])
      have gx_type[type_rule]: "\<langle>g,x\<rangle> \<in>\<^sub>c Y\<^bsup>X\<^esup> \<times>\<^sub>c X"
        using assms by typecheck_cfuncs
      have swap_gx: "swap(Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c \<langle>g,x\<rangle> = \<langle>x,g\<rangle>"
        by (rule swap_ap[OF g_type x_type])
      have swap_type'[type_rule]:
        "swap(Y\<^bsup>X\<^esup>, X) :
          Y\<^bsup>X\<^esup> \<times>\<^sub>c X \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>"
        by typecheck_cfuncs
      have eval_type'[type_rule]:
        "eval_func(Y, X) : X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Y"
        by typecheck_cfuncs
      have eval_swap:
        "(eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X)) \<circ>\<^sub>c
          \<langle>g,x\<rangle> = eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>"
      proof -
        have "(eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X)) \<circ>\<^sub>c
            \<langle>g,x\<rangle> =
            eval_func(Y, X) \<circ>\<^sub>c
              (swap(Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c \<langle>g,x\<rangle>)"
          using comp_associative2[OF gx_type swap_type' eval_type'] by simp
        also have "... = eval_func(Y, X) \<circ>\<^sub>c \<langle>x,g\<rangle>"
          using swap_gx by simp
        finally show ?thesis .
      qed
      show ?thesis using id_f eval_swap by simp
    qed
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y)) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c \<langle>f,\<langle>g, x\<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X)))) \<circ>\<^sub>c \<langle>f,\<langle>g, x\<rangle>\<rangle>"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X)))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c \<langle>\<langle>f,g\<rangle>, x\<rangle>"
      using assms by (typecheck_cfuncs, simp add: associate_right_ap)
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X)) \<circ>\<^sub>c \<langle>\<langle>f,g\<rangle>, x\<rangle>"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X)) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>) \<circ>\<^sub>c \<langle>x, \<langle>f,g\<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, simp add: swap_ap)
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c \<langle>x, \<langle>f,g\<rangle>\<rangle>"
      using assms comp_associative2 by (typecheck_cfuncs, force)
    also have "... = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c ((id\<^sub>c(X) \<times>\<^sub>f \<langle>f,g\<rangle>) \<circ>\<^sub>c x1)"
    proof -
      have idX_type[type_rule]: "id\<^sub>c(X) : X \<rightarrow> X"
        by typecheck_cfuncs
      have id1_type[type_rule]: "id\<^sub>c(\<one>) \<in>\<^sub>c \<one>"
        by typecheck_cfuncs
      have fg_type[type_rule]: "\<langle>f,g\<rangle> \<in>\<^sub>c Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>"
        using assms by typecheck_cfuncs
      have cross_seed:
        "(id\<^sub>c(X) \<times>\<^sub>f \<langle>f,g\<rangle>) \<circ>\<^sub>c
          \<langle>x,id\<^sub>c(\<one>)\<rangle> = \<langle>x,\<langle>f,g\<rangle>\<rangle>"
      proof -
        have "(id\<^sub>c(X) \<times>\<^sub>f \<langle>f,g\<rangle>) \<circ>\<^sub>c
            \<langle>x,id\<^sub>c(\<one>)\<rangle> =
            \<langle>id\<^sub>c(X) \<circ>\<^sub>c x,
              \<langle>f,g\<rangle> \<circ>\<^sub>c id\<^sub>c(\<one>)\<rangle>"
          by (rule cfunc_cross_prod_comp_cfunc_prod[
                OF x_type id1_type idX_type fg_type])
        also have "... = \<langle>x,\<langle>f,g\<rangle>\<rangle>"
          using id_left_unit2[OF x_type] id_right_unit2[OF fg_type] by simp
        finally show ?thesis .
      qed
      show ?thesis using x_def cross_seed by simp
    qed
    also have "... = ((eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (id\<^sub>c(X) \<times>\<^sub>f \<langle>f,g\<rangle>)) \<circ>\<^sub>c x1"
      using comp_associative2 by (typecheck_cfuncs, force)
    finally show "(((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(X, \<one>)) \<circ>\<^sub>c x1 =
         ((eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (id\<^sub>c(X) \<times>\<^sub>f \<langle>f,g\<rangle>)) \<circ>\<^sub>c x1".
  qed
  then have "(((eval_func(Z, Y) \<circ>\<^sub>c \<langle>id\<^sub>c(Y),f \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>) \<circ>\<^sub>c eval_func(Y, X) \<circ>\<^sub>c \<langle>id\<^sub>c(X),g \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<circ>\<^sub>c
     left_cart_proj(X, \<one>))\<^sup>\<sharp> = (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X)))
         \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c \<langle>f,g\<rangle>"
    using assms by (typecheck_cfuncs, simp add: sharp_comp)  
  then show "(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>,right_cart_proj(X, \<one>)\<rangle>)\<^sup>\<sharp> =
    (eval_func(Z, Y) \<circ>\<^sub>c swap(Z\<^bsup>Y\<^esup>, Y) \<circ>\<^sub>c (id\<^sub>c(Z\<^bsup>Y\<^esup>) \<times>\<^sub>f (eval_func(Y, X) \<circ>\<^sub>c swap(Y\<^bsup>X\<^esup>, X))) \<circ>\<^sub>c associate_right(Z\<^bsup>Y\<^esup>, Y\<^bsup>X\<^esup>, X) \<circ>\<^sub>c swap(X, Z\<^bsup>Y\<^esup> \<times>\<^sub>c Y\<^bsup>X\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c \<langle>f,g\<rangle>"
    using assms cfunc_type_def cnufatem_def2 cnufatem_type domain_comp meta_comp2_def2 meta_comp2_def3 metafunc_def by force
qed

lemma meta_comp_on_els:
  assumes "f : W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g : W \<rightarrow> Y\<^bsup>X\<^esup>"
  assumes "w \<in>\<^sub>c W"
  shows "(f \<box> g) \<circ>\<^sub>c w = (f \<circ>\<^sub>c w) \<box> (g \<circ>\<^sub>c w)"
proof - 
  have "(f \<box> g) \<circ>\<^sub>c w = (f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  also have "... = (eval_func(Z, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g), right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w"
    using assms comp_associative2 inv_transpose_func_def3 by (typecheck_cfuncs, force)
  also have "... = (eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g), f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = (eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g\<circ>\<^sub>c w)), (f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj(X, \<one>)\<rangle>)\<^sup>\<sharp>"
  proof - 
    have inner_eq: "(eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g), f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f w) = 
          eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g\<circ>\<^sub>c w)), f \<circ>\<^sub>c right_cart_proj(X, W) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w)\<rangle>"
    proof - 
      have "eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g), f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle> \<circ>\<^sub>c (id(X) \<times>\<^sub>f w) 
          =  eval_func(Z, Y) \<circ>\<^sub>c \<langle>(eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w), (f \<circ>\<^sub>c right_cart_proj(X, W)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w)\<rangle>"
         using assms cfunc_prod_comp by (typecheck_cfuncs, force)
       also have "... = eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w), f \<circ>\<^sub>c right_cart_proj(X, W) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w)\<rangle>"
         using assms comp_associative2 by (typecheck_cfuncs, auto)
       also have "... = eval_func(Z, Y) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g\<circ>\<^sub>c w)), f \<circ>\<^sub>c right_cart_proj(X, W) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w)\<rangle>"
       proof -
         have cross_comp:
           "(id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w) =
             id(X) \<times>\<^sub>f (g \<circ>\<^sub>c w)"
           using identity_distributes_across_composition[OF assms(3) assms(2)]
           by simp
         show ?thesis using cross_comp by simp
       qed
       ultimately show ?thesis
         using assms comp_associative2 flat_cancels_sharp by (typecheck_cfuncs, auto)
     qed
     have source_type:
       "eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g),
           f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle> :
          X \<times>\<^sub>c W \<rightarrow> Z"
       using assms by typecheck_cfuncs
     have source_sharp_type:
       "(eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g),
           f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> :
          W \<rightarrow> Z\<^bsup>X\<^esup>"
       by (rule transpose_func_type[OF source_type])
     have lhs_type:
       "(eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g),
           f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w :
          \<one> \<rightarrow> Z\<^bsup>X\<^esup>"
       using assms source_sharp_type by typecheck_cfuncs
     have target_type:
       "eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g \<circ>\<^sub>c w)),
           (f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj(X, \<one>)\<rangle> :
          X \<times>\<^sub>c \<one> \<rightarrow> Z"
       using assms by typecheck_cfuncs
     have projection:
       "right_cart_proj(X, W) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w) =
          w \<circ>\<^sub>c right_cart_proj(X, \<one>)"
       by (rule right_cart_proj_cfunc_cross_prod[OF id_type assms(3)])
     have right_component:
       "f \<circ>\<^sub>c right_cart_proj(X, W) \<circ>\<^sub>c (id(X) \<times>\<^sub>f w) =
          (f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj(X, \<one>)"
       using assms projection comp_associative2 by (typecheck_cfuncs, force)
     have flattened:
       "(eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g),
           f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c
          (id(X) \<times>\<^sub>f w) =
        eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g \<circ>\<^sub>c w)),
           (f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj(X, \<one>)\<rangle>"
       using inner_eq right_component by simp
     have composite_flat:
       "((eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g),
           f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w)\<^sup>\<flat> =
        (eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g),
           f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c
          (id(X) \<times>\<^sub>f w)"
       by (rule inv_transpose_of_composition[OF assms(3) source_sharp_type])
     have eval_lhs:
       "eval_func(Z, X) \<circ>\<^sub>c
          (id(X) \<times>\<^sub>f
            ((eval_func(Z, Y) \<circ>\<^sub>c
              \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g),
               f \<circ>\<^sub>c right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c w)) =
        eval_func(Z, Y) \<circ>\<^sub>c
          \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g \<circ>\<^sub>c w)),
           (f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj(X, \<one>)\<rangle>"
       using inv_transpose_func_def3[OF lhs_type] composite_flat flattened by simp
     show ?thesis
       by (rule transpose_func_unique[OF target_type lhs_type eval_lhs])
  qed
  also have "... = (eval_func(Z, Y) \<circ>\<^sub>c (id\<^sub>c(Y) \<times>\<^sub>f ((f \<circ>\<^sub>c w) \<circ>\<^sub>c right_cart_proj(X, \<one>))) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g\<circ>\<^sub>c w)), id (X\<times>\<^sub>c \<one>)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
  also have "... = (eval_func(Z, Y) \<circ>\<^sub>c (id\<^sub>c(Y) \<times>\<^sub>f (f \<circ>\<^sub>c w)) \<circ>\<^sub>c (id (Y) \<times>\<^sub>f right_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g\<circ>\<^sub>c w)), id (X\<times>\<^sub>c \<one>)\<rangle>)\<^sup>\<sharp>"
    using assms comp_associative2 identity_distributes_across_composition by (typecheck_cfuncs, force)
  also have "... = ((f\<circ>\<^sub>cw)\<^sup>\<flat> \<circ>\<^sub>c (id (Y) \<times>\<^sub>f right_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (g\<circ>\<^sub>c w)), id (X\<times>\<^sub>c \<one>)\<rangle>)\<^sup>\<sharp>"
  proof -
    have fw_type: "f \<circ>\<^sub>c w : \<one> \<rightarrow> Z\<^bsup>Y\<^esup>"
      using assms by typecheck_cfuncs
    have fw_flat:
      "(f \<circ>\<^sub>c w)\<^sup>\<flat> =
        eval_func(Z, Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c w))"
      by (rule inv_transpose_func_def3[OF fw_type])
    show ?thesis
      using assms fw_flat comp_associative2
      by (typecheck_cfuncs, fastforce)
  qed
  also have "... = ((f\<circ>\<^sub>cw)\<^sup>\<flat> \<circ>\<^sub>c (id (Y) \<times>\<^sub>f right_cart_proj(X, \<one>)) \<circ>\<^sub>c \<langle>(g\<circ>\<^sub>c w)\<^sup>\<flat>, id (X\<times>\<^sub>c \<one>)\<rangle>)\<^sup>\<sharp>"
    using assms inv_transpose_func_def3 by (typecheck_cfuncs, force)
  also have "... = ((f\<circ>\<^sub>c w)\<^sup>\<flat> \<circ>\<^sub>c \<langle>(g\<circ>\<^sub>c w)\<^sup>\<flat>, right_cart_proj(X, \<one>)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
  also have "... = (f\<circ>\<^sub>c w) \<box> (g \<circ>\<^sub>c w)"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  finally show ?thesis.
qed

lemma meta_comp2_def5:
  assumes "f : W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g : W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "f \<box> g   = meta_comp(X, Y, Z) \<circ>\<^sub>c \<langle>f,g\<rangle>"
proof(rule one_separator[where X = W, where Y = "Z\<^bsup>X\<^esup>"])
  show "f \<box> g : W \<rightarrow> Z\<^bsup>X\<^esup>"
    using assms by typecheck_cfuncs
  show "meta_comp(X, Y, Z) \<circ>\<^sub>c \<langle>f,g\<rangle> : W \<rightarrow> Z\<^bsup>X\<^esup>"
    using assms by typecheck_cfuncs
next
  fix w 
  assume w_type[type_rule]: "w \<in>\<^sub>c W"
  have "(meta_comp(X, Y, Z) \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c w = meta_comp(X, Y, Z) \<circ>\<^sub>c \<langle>f,g\<rangle> \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = meta_comp(X, Y, Z) \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c w, g \<circ>\<^sub>c w\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... = (f\<circ>\<^sub>c w) \<box> (g \<circ>\<^sub>c w)"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def4)
  also have "... = (f \<box> g) \<circ>\<^sub>c w"
    using assms by (typecheck_cfuncs, simp add: meta_comp_on_els)
  ultimately show "(f \<box> g) \<circ>\<^sub>c w = (meta_comp(X, Y, Z) \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c w"
    by simp
qed

lemma meta_left_identity:
  assumes "g \<in>\<^sub>c X\<^bsup>X\<^esup>"
  shows "g \<box> metafunc (id(X)) = g"
proof -
  have idX_type: "id(X) : X \<rightarrow> X"
    by (rule id_type)
  have metafunc_id_type: "metafunc(id(X)) \<in>\<^sub>c X\<^bsup>X\<^esup>"
    using idX_type by typecheck_cfuncs
  have cnufatem_g_type: "cnufatem(g) : X \<rightarrow> X"
    by (rule cnufatem_type[OF assms])
  have "g \<box> metafunc(id(X)) =
      metafunc(cnufatem(g) \<circ>\<^sub>c cnufatem(metafunc(id(X))))"
    by (rule meta_comp2_def3[OF assms metafunc_id_type])
  also have "... = metafunc(cnufatem(g) \<circ>\<^sub>c id(X))"
    using cnufatem_metafunc[OF idX_type] by simp
  also have "... = metafunc(cnufatem(g))"
    using id_right_unit2[OF cnufatem_g_type] by simp
  also have "... = g"
    by (rule metafunc_cnufatem[OF assms])
  finally show ?thesis.
qed
  
lemma meta_right_identity:
  assumes "g \<in>\<^sub>c X\<^bsup>X\<^esup>"
  shows "metafunc(id(X)) \<box> g = g"
proof -
  have idX_type: "id(X) : X \<rightarrow> X"
    by (rule id_type)
  have metafunc_id_type: "metafunc(id(X)) \<in>\<^sub>c X\<^bsup>X\<^esup>"
    using idX_type by typecheck_cfuncs
  have cnufatem_g_type: "cnufatem(g) : X \<rightarrow> X"
    by (rule cnufatem_type[OF assms])
  have "metafunc(id(X)) \<box> g =
      metafunc(cnufatem(metafunc(id(X))) \<circ>\<^sub>c cnufatem(g))"
    by (rule meta_comp2_def3[OF metafunc_id_type assms])
  also have "... = metafunc(id(X) \<circ>\<^sub>c cnufatem(g))"
    using cnufatem_metafunc[OF idX_type] by simp
  also have "... = metafunc(cnufatem(g))"
    using id_left_unit2[OF cnufatem_g_type] by simp
  also have "... = g"
    by (rule metafunc_cnufatem[OF assms])
  finally show ?thesis.
qed

lemma comp_as_metacomp:
  assumes "g : X \<rightarrow> Y"
  assumes "f : Y \<rightarrow> Z"
  shows "f \<circ>\<^sub>c g = cnufatem(metafunc(f) \<box> metafunc(g))"
  using assms by (typecheck_cfuncs, simp add: cnufatem_metafunc meta_comp2_def3)

lemma metacomp_as_comp:
  assumes "g \<in>\<^sub>c Y\<^bsup>X\<^esup>"
  assumes "f \<in>\<^sub>c Z\<^bsup>Y\<^esup>"
  shows "cnufatem(f) \<circ>\<^sub>c cnufatem(g) = cnufatem(f \<box> g)"
  using assms by (typecheck_cfuncs, simp add: comp_as_metacomp metafunc_cnufatem)

lemma meta_comp_assoc:
  assumes "e : W \<rightarrow> A\<^bsup>Z\<^esup>"
  assumes "f : W \<rightarrow> Z\<^bsup>Y\<^esup>"
  assumes "g : W \<rightarrow> Y\<^bsup>X\<^esup>"
  shows "(e \<box> f) \<box>  g  = e \<box> (f \<box> g)"
proof -
  have "(e \<box> f) \<box>  g = (e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat>, right_cart_proj(Y, W)\<rangle>)\<^sup>\<sharp> \<box> g"
    using assms by (simp add: meta_comp2_def2)
  also have "... = ((e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat>, right_cart_proj(Y, W)\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  also have "... = ((e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat>, right_cart_proj(Y, W)\<rangle>) \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: flat_cancels_sharp)    
  also have "... = (e\<^sup>\<flat> \<circ>\<^sub>c \<langle>f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle> ,right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>"
  proof -
    have inner_pair_type:
      "\<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle> :
        X \<times>\<^sub>c W \<rightarrow> Y \<times>\<^sub>c W"
      using assms by typecheck_cfuncs
    have outer_pair_type:
      "\<langle>f\<^sup>\<flat>, right_cart_proj(Y, W)\<rangle> :
        Y \<times>\<^sub>c W \<rightarrow> Z \<times>\<^sub>c W"
      using assms by typecheck_cfuncs
    have f_flat_type: "f\<^sup>\<flat> : Y \<times>\<^sub>c W \<rightarrow> Z"
      using assms by typecheck_cfuncs
    have outer_projection_type:
      "right_cart_proj(Y, W) : Y \<times>\<^sub>c W \<rightarrow> W"
      by (rule right_cart_proj_type)
    have e_flat_type: "e\<^sup>\<flat> : Z \<times>\<^sub>c W \<rightarrow> A"
      using assms by typecheck_cfuncs
    have pair_comp:
      "\<langle>f\<^sup>\<flat>, right_cart_proj(Y, W)\<rangle> \<circ>\<^sub>c
          \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle> =
        \<langle>f\<^sup>\<flat> \<circ>\<^sub>c
            \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>,
          right_cart_proj(Y, W) \<circ>\<^sub>c
            \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>\<rangle>"
      by (rule cfunc_prod_comp[
            OF inner_pair_type f_flat_type outer_projection_type])
    have projection:
      "right_cart_proj(Y, W) \<circ>\<^sub>c
          \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle> =
        right_cart_proj(X, W)"
      using assms by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_prod)
    have reassociate:
      "e\<^sup>\<flat> \<circ>\<^sub>c
          \<langle>f\<^sup>\<flat>, right_cart_proj(Y, W)\<rangle> \<circ>\<^sub>c
          \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle> =
        (e\<^sup>\<flat> \<circ>\<^sub>c
          \<langle>f\<^sup>\<flat>, right_cart_proj(Y, W)\<rangle>) \<circ>\<^sub>c
          \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>"
      by (rule comp_associative2[OF inner_pair_type outer_pair_type e_flat_type])
    show ?thesis
      using pair_comp projection reassociate by simp
  qed
  also have "... = (e\<^sup>\<flat> \<circ>\<^sub>c \<langle>(f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>\<^sup>\<flat> ,right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: flat_cancels_sharp)
  also have "... = e \<box> (f\<^sup>\<flat> \<circ>\<^sub>c \<langle>g\<^sup>\<flat>, right_cart_proj(X, W)\<rangle>)\<^sup>\<sharp>"
    using assms by (typecheck_cfuncs, simp add: meta_comp2_def2)
  also have "... = e \<box> (f \<box> g)"
    using assms by (simp add: meta_comp2_def2)
  finally show ?thesis.
qed

subsection \<open>Partially Parameterized Functions on Pairs\<close>

axiomatization left_param :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc"
  ("_\<^bsub>[_,-]\<^esub>" [100,0]100)
where left_param_spec:
  "k : P \<times>\<^sub>c Q \<rightarrow> R \<Longrightarrow>
    k\<^bsub>[p,-]\<^esub> = k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id(Q)\<rangle>"

lemma left_param_def2:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  shows "k\<^bsub>[p,-]\<^esub> = k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id(Q)\<rangle>"
  by (rule left_param_spec[OF assms])

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
  have pair_map_type:
    "\<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id(Q)\<rangle> :
      Q \<rightarrow> P \<times>\<^sub>c Q"
    using assms by typecheck_cfuncs
  have param_eq:
    "k\<^bsub>[p,-]\<^esub> =
      k \<circ>\<^sub>c \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id(Q)\<rangle>"
    by (rule left_param_def2[OF assms(1)])
  have associated:
    "k \<circ>\<^sub>c
        \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id(Q)\<rangle> \<circ>\<^sub>c q =
      (k \<circ>\<^sub>c
        \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id(Q)\<rangle>) \<circ>\<^sub>c q"
    by (rule comp_associative2[OF assms(3) pair_map_type assms(1)])
  have extracted:
    "\<langle>p, q\<rangle> =
      \<langle>p \<circ>\<^sub>c \<beta>\<^bsub>Q\<^esub>, id(Q)\<rangle> \<circ>\<^sub>c q"
    by (rule cart_prod_extract_right[OF assms(2) assms(3)])
  show ?thesis using param_eq associated extracted by simp
qed

axiomatization right_param :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc"
  ("_\<^bsub>[-,_]\<^esub>" [100,0]100)
where right_param_spec:
  "k : P \<times>\<^sub>c Q \<rightarrow> R \<Longrightarrow>
    k\<^bsub>[-,q]\<^esub> = k \<circ>\<^sub>c \<langle>id(P), q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>"

lemma right_param_def2:
  assumes "k : P \<times>\<^sub>c Q \<rightarrow> R"
  shows "k\<^bsub>[-,q]\<^esub> = k \<circ>\<^sub>c \<langle>id(P), q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>"
  by (rule right_param_spec[OF assms])

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
  have pair_map_type:
    "\<langle>id(P), q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle> :
      P \<rightarrow> P \<times>\<^sub>c Q"
    using assms by typecheck_cfuncs
  have param_eq:
    "k\<^bsub>[-,q]\<^esub> =
      k \<circ>\<^sub>c \<langle>id(P), q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>"
    by (rule right_param_def2[OF assms(1)])
  have associated:
    "k \<circ>\<^sub>c
        \<langle>id(P), q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle> \<circ>\<^sub>c p =
      (k \<circ>\<^sub>c
        \<langle>id(P), q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle>) \<circ>\<^sub>c p"
    by (rule comp_associative2[OF assms(2) pair_map_type assms(1)])
  have extracted:
    "\<langle>p, q\<rangle> =
      \<langle>id(P), q \<circ>\<^sub>c \<beta>\<^bsub>P\<^esub>\<rangle> \<circ>\<^sub>c p"
    by (rule cart_prod_extract_left[OF assms(2) assms(3)])
  show ?thesis using param_eq associated extracted by simp
qed

subsection \<open>Exponential Set Facts\<close>

text \<open>The lemma below corresponds to Proposition 2.5.7 in Halvorson.\<close>
lemma exp_one:
  "X\<^bsup>\<one>\<^esup> \<cong> X"
proof -
  obtain e where e_defn: "e = eval_func(X, \<one>)" and e_type: "e : \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup> \<rightarrow> X"
    using eval_func_type by auto
  define i where "i = left_cart_proj(\<one>, \<one>)"
  have i_type: "i : \<one> \<times>\<^sub>c \<one> \<rightarrow> \<one>"
    unfolding i_def by (rule left_cart_proj_type)
  define i_inv where "i_inv = \<langle>id(\<one>), \<beta>\<^bsub>\<one>\<^esub>\<rangle>"
  have i_inv_type: "i_inv : \<one> \<rightarrow> \<one> \<times>\<^sub>c \<one>"
    unfolding i_inv_def by typecheck_cfuncs
  have i_i_inv: "i \<circ>\<^sub>c i_inv = id(\<one>)"
    unfolding i_def i_inv_def
    by (rule left_cart_proj_one_right_inverse)
  have i_inv_i: "i_inv \<circ>\<^sub>c i = id(\<one> \<times>\<^sub>c \<one>)"
    unfolding i_def i_inv_def
    by (rule left_cart_proj_one_left_inverse)
  have i_iso: "i_inv: \<one>\<rightarrow> \<one> \<times>\<^sub>c \<one> \<and>
      i \<circ>\<^sub>c i_inv = id(\<one>) \<and>
      i_inv \<circ>\<^sub>c i = id(\<one> \<times>\<^sub>c \<one>)"
    using i_inv_type i_i_inv i_inv_i by auto

  have inj: "injective(e)"
    by (simp add: e_defn eval_func_X_one_injective)

  have surj: "surjective(e)"
     unfolding surjective_def
   proof clarify
    fix y 
    assume "y \<in>\<^sub>c codomain(e)"
    then have y_type: "y \<in>\<^sub>c X"
      using cfunc_type_def e_type by auto

    have ysharp_type: "(y \<circ>\<^sub>c i)\<^sup>\<sharp> : \<one> \<rightarrow> X\<^bsup>\<one>\<^esup>"
      using y_type i_type by typecheck_cfuncs
    have cross_type: "id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp> : \<one> \<times>\<^sub>c \<one> \<rightarrow> \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using ysharp_type by typecheck_cfuncs
    have witness_type: "(id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>) \<circ>\<^sub>c i_inv \<in>\<^sub>c \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using cross_type i_inv_type by typecheck_cfuncs

    have square: "e \<circ>\<^sub>c (id(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>) = y \<circ>\<^sub>c i"
      using comp_type e_defn i_type transpose_func_def y_type by blast

    have assoc: "e \<circ>\<^sub>c ((id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>) \<circ>\<^sub>c i_inv) =
        (e \<circ>\<^sub>c (id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>)) \<circ>\<^sub>c i_inv"
      by (rule comp_associative2[OF i_inv_type cross_type e_type])

    have eval_witness: "e \<circ>\<^sub>c ((id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>) \<circ>\<^sub>c i_inv) = y"
    proof -
      have s1: "(e \<circ>\<^sub>c (id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>)) \<circ>\<^sub>c i_inv = (y \<circ>\<^sub>c i) \<circ>\<^sub>c i_inv"
        using square by simp
      have s2: "(y \<circ>\<^sub>c i) \<circ>\<^sub>c i_inv = y \<circ>\<^sub>c (i \<circ>\<^sub>c i_inv)"
        by (rule sym[OF comp_associative2[OF i_inv_type i_type y_type]])
      have s3: "y \<circ>\<^sub>c (i \<circ>\<^sub>c i_inv) = y \<circ>\<^sub>c id(\<one>)"
        by (simp add: i_i_inv)
      have s4: "y \<circ>\<^sub>c id(\<one>) = y"
        by (rule id_right_unit2[OF y_type])
      show ?thesis using assoc s1 s2 s3 s4 by simp
    qed

    have dom_e: "domain(e) = \<one> \<times>\<^sub>c X\<^bsup>\<one>\<^esup>"
      using e_type cfunc_type_def by auto
    have witness_dom: "(id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>) \<circ>\<^sub>c i_inv \<in>\<^sub>c domain(e)"
      using witness_type dom_e by simp
    show "\<exists>x. x \<in>\<^sub>c domain(e) \<and> e \<circ>\<^sub>c x = y"
      by (rule exI[where x="(id\<^sub>c(\<one>) \<times>\<^sub>f (y \<circ>\<^sub>c i)\<^sup>\<sharp>) \<circ>\<^sub>c i_inv"],
          intro conjI, rule witness_dom, rule eval_witness)
  qed

  have "isomorphism(e)"
    using epi_mon_is_iso inj injective_imp_monomorphism surj surjective_is_epimorphism by fastforce
  then show "X\<^bsup>\<one>\<^esup> \<cong> X"
    using e_type is_isomorphic_def isomorphic_is_symmetric isomorphic_is_transitive one_x_A_iso_A by blast
qed

text \<open>The lemma below corresponds to Proposition 2.5.8 in Halvorson.\<close>
lemma exp_empty:
  "X\<^bsup>\<emptyset>\<^esup> \<cong> \<one>"
proof - 
  obtain f where f_type: "f = \<alpha>\<^bsub>X\<^esub>\<circ>\<^sub>c (left_cart_proj(\<emptyset>, \<one>))" and fsharp_type[type_rule]: "f\<^sup>\<sharp> \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
    using transpose_func_type by (typecheck_cfuncs, force)
  have uniqueness: "\<forall>z. z \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup> \<longrightarrow> z=f\<^sup>\<sharp>"
  proof clarify
    fix z
    assume z_type[type_rule]: "z \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
    have lhs_type: "id(\<emptyset>) \<times>\<^sub>f z :
        \<emptyset> \<times>\<^sub>c \<one> \<rightarrow> \<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
      using z_type by typecheck_cfuncs
    have rhs_type: "id(\<emptyset>) \<times>\<^sub>f f\<^sup>\<sharp> :
        \<emptyset> \<times>\<^sub>c \<one> \<rightarrow> \<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
      using fsharp_type by typecheck_cfuncs
    have f_sharp: "id(\<emptyset>) \<times>\<^sub>f z = id(\<emptyset>) \<times>\<^sub>f f\<^sup>\<sharp>"
    proof (rule one_separator[OF lhs_type rhs_type])
      fix x
      assume x_type: "x \<in>\<^sub>c \<emptyset> \<times>\<^sub>c \<one>"
      have empty_element: "left_cart_proj(\<emptyset>, \<one>) \<circ>\<^sub>c x \<in>\<^sub>c \<emptyset>"
        using x_type by typecheck_cfuncs
      have False by (rule notE[OF emptyset_is_empty empty_element])
      then show "(id(\<emptyset>) \<times>\<^sub>f z) \<circ>\<^sub>c x =
          (id(\<emptyset>) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c x"
        by (rule FalseE)
    qed
    then show "z = f\<^sup>\<sharp>"
      using  fsharp_type same_evals_equal z_type by force
  qed
  then have "\<exists>! x. x \<in>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
    by (intro ex1I[where a="f\<^sup>\<sharp>"], simp_all add: fsharp_type)
  then show "X\<^bsup>\<emptyset>\<^esup> \<cong> \<one>"
    using single_elem_iso_one by auto
qed

lemma one_exp:
  "\<one>\<^bsup>X\<^esup> \<cong> \<one>"
proof - 
  have nonempty: "nonempty(\<one>\<^bsup>X\<^esup>)"
    using nonempty_def right_cart_proj_type transpose_func_type by blast
  obtain e where e_defn: "e = eval_func(\<one>, X)" and e_type: "e : X \<times>\<^sub>c \<one>\<^bsup>X\<^esup> \<rightarrow> \<one>"
    by (simp add: eval_func_type)
  have uniqueness: "\<forall>y. (y\<in>\<^sub>c \<one>\<^bsup>X\<^esup> \<longrightarrow> e \<circ>\<^sub>c (id(X) \<times>\<^sub>f y) : X \<times>\<^sub>c \<one>  \<rightarrow> \<one>)"
    using cfunc_cross_prod_type comp_type e_type id_type by blast
  have uniquess_form: "\<forall>y. (y\<in>\<^sub>c \<one>\<^bsup>X\<^esup> \<longrightarrow> e \<circ>\<^sub>c (id(X) \<times>\<^sub>f y) = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)"
    using terminal_func_unique uniqueness by blast
  have terminal_type: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> : X \<times>\<^sub>c \<one> \<rightarrow> \<one>"
    by (rule terminal_func_type)
  have all_transposes:
      "\<forall>y. y \<in>\<^sub>c \<one>\<^bsup>X\<^esup> \<longrightarrow>
        y = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>\<^sup>\<sharp>"
  proof (intro allI impI)
    fix y
    assume y_type: "y \<in>\<^sub>c \<one>\<^bsup>X\<^esup>"
    have eval_y_e:
        "e \<circ>\<^sub>c (id(X) \<times>\<^sub>f y) = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>"
      by (rule mp[OF spec[OF uniquess_form] y_type])
    have eval_y:
        "eval_func(\<one>, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f y) =
          \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>"
      using eval_y_e e_defn by simp
    show "y = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>\<^sup>\<sharp>"
      by (rule transpose_func_unique[OF terminal_type y_type eval_y])
  qed
  have exists_element: "\<exists>x. x \<in>\<^sub>c \<one>\<^bsup>X\<^esup>"
    by (rule iffD1[OF nonempty_def nonempty])
  obtain x where x_type: "x \<in>\<^sub>c \<one>\<^bsup>X\<^esup>"
    by (rule exE[OF exists_element])
  have ex1: "\<exists>!y. y \<in>\<^sub>c \<one>\<^bsup>X\<^esup>"
  proof (rule ex1I[where a=x])
    show "x \<in>\<^sub>c \<one>\<^bsup>X\<^esup>" by (rule x_type)
  next
    fix y
    assume y_type: "y \<in>\<^sub>c \<one>\<^bsup>X\<^esup>"
    have x_eq: "x = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>\<^sup>\<sharp>"
      by (rule mp[OF spec[OF all_transposes] x_type])
    have y_eq: "y = \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>\<^sup>\<sharp>"
      by (rule mp[OF spec[OF all_transposes] y_type])
    show "y = x" using y_eq x_eq by simp
  qed
  show "\<one>\<^bsup>X\<^esup> \<cong> \<one>"
    using ex1 single_elem_iso_one by auto
qed

text \<open>The lemma below corresponds to Proposition 2.5.9 in Halvorson.\<close>
lemma power_rule:
  "(X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<cong> X\<^bsup>A\<^esup> \<times>\<^sub>c Y\<^bsup>A\<^esup>"
proof - 
  have left_exp_type:
      "left_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f :
        (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>A\<^esup>"
    by typecheck_cfuncs
  have right_exp_type:
      "right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f :
        (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
    by typecheck_cfuncs
  have "is_cart_prod ((X \<times>\<^sub>c Y)\<^bsup>A\<^esup>) ((left_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) (right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f) (X\<^bsup>A\<^esup>) (Y\<^bsup>A\<^esup>)"
  proof (rule iffD2[OF is_cart_prod_def2[OF left_exp_type right_exp_type]], clarify)
    fix f g Z 
    assume f_type[type_rule]: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
    assume g_type[type_rule]: "g : Z \<rightarrow> Y\<^bsup>A\<^esup>"

    show "\<exists>h. h : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<and>
           left_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h = f \<and>
           right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h = g \<and>
           (\<forall>h2. h2 : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<and> left_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 = f \<and> right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 = g \<longrightarrow>
                 h2 = h)"
    proof (intro exI[where x="\<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"], safe, typecheck_cfuncs)
      have "((left_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = ((left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>)\<^sup>\<sharp>"
        using transpose_of_comp by (typecheck_cfuncs, fastforce)
      also have "... = f\<^sup>\<flat>\<^sup>\<sharp>"
        by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
      also have "... = f"
        by (typecheck_cfuncs, simp add: sharp_cancels_flat)
      finally show projection_property1: "((left_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = f".
      show projection_property2: "((right_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>f\<^sup>\<flat> ,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> = g"
      proof -
        have "((right_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c
            \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>\<^sup>\<sharp> =
            (right_cart_proj(X, Y) \<circ>\<^sub>c
              \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>)\<^sup>\<sharp>"
          using transpose_of_comp by (typecheck_cfuncs, fastforce)
        also have "... = g\<^sup>\<flat>\<^sup>\<sharp>"
          by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_prod)
        also have "... = g"
          by (typecheck_cfuncs, simp add: sharp_cancels_flat)
        finally show ?thesis.
      qed
      show "\<And>h2. h2 : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<Longrightarrow>
          f = left_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 \<Longrightarrow>
          g = right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2 \<Longrightarrow>
          h2 = \<langle>(left_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2)\<^sup>\<flat>,(right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h2)\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
      proof -
        fix h
        assume h_type[type_rule]: "h : Z \<rightarrow> (X \<times>\<^sub>c Y)\<^bsup>A\<^esup>"
        assume h_property1:  "f = ((left_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c h"
        assume h_property2:  "g = ((right_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c h"
    
        have "f = (left_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp>"
          using h_property1 h_type sharp_cancels_flat by fastforce
        also have "... = ((left_cart_proj(X, Y)) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (typecheck_cfuncs, simp add: transpose_of_comp)
        ultimately have computation1: "f = ((left_cart_proj(X, Y)) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          by simp
        then have unqiueness1: "(left_cart_proj(X, Y)) \<circ>\<^sub>c  h\<^sup>\<flat> =  f\<^sup>\<flat>"
          by (typecheck_cfuncs, simp add: flat_cancels_sharp)
        have "g = ((right_cart_proj(X, Y))\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (h\<^sup>\<flat>)\<^sup>\<sharp>"
          using h_property2 h_type sharp_cancels_flat by fastforce
        have "... = ((right_cart_proj(X, Y)) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
          using transpose_of_comp by (typecheck_cfuncs, fastforce)
        have computation2: "g = ((right_cart_proj(X, Y)) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
           by (simp add: \<open>g = right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp>\<close> \<open>right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp> = (right_cart_proj(X, Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>\<close>)
        then have unqiueness2: "(right_cart_proj(X, Y)) \<circ>\<^sub>c  h\<^sup>\<flat> =  g\<^sup>\<flat>"
          using h_type g_type by (typecheck_cfuncs, simp add: computation2 flat_cancels_sharp)
        have h_flat_type: "h\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y"
          using h_type by typecheck_cfuncs
        have f_flat_type: "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X"
          using f_type by typecheck_cfuncs
        have g_flat_type: "g\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> Y"
          using g_type by typecheck_cfuncs
        have h_flat: "h\<^sup>\<flat> = \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>"
          by (rule cfunc_prod_unique[
                OF f_flat_type g_flat_type h_flat_type unqiueness1 unqiueness2])
        then have h_is_sharp_prod_fflat_gflat: "h = \<langle>f\<^sup>\<flat>, g\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
          using h_type sharp_cancels_flat by fastforce
        then show "h = \<langle>(left_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h)\<^sup>\<flat>,(right_cart_proj(X, Y)\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h)\<^sup>\<flat>\<rangle>\<^sup>\<sharp>"
          using h_property1 h_property2 by force
      qed
    qed
  qed
  then show "(X \<times>\<^sub>c Y)\<^bsup>A\<^esup> \<cong> X\<^bsup>A\<^esup> \<times>\<^sub>c Y\<^bsup>A\<^esup>"
    using canonical_cart_prod_is_cart_prod cart_prods_isomorphic is_isomorphic_def by fastforce
qed

lemma exponential_coprod_distribution:
  "Z\<^bsup>(X \<Coprod> Y)\<^esup> \<cong> (Z\<^bsup>X\<^esup>) \<times>\<^sub>c (Z\<^bsup>Y\<^esup>)"
proof - 
  have left_eval_type:
      "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
        (left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)))\<^sup>\<sharp> :
        Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z\<^bsup>X\<^esup>"
    by typecheck_cfuncs
  have right_eval_type:
      "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
        (right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)))\<^sup>\<sharp> :
        Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z\<^bsup>Y\<^esup>"
    by typecheck_cfuncs
  have "is_cart_prod(
      Z\<^bsup>(X \<Coprod> Y)\<^esup>,
      (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
        (left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)))\<^sup>\<sharp>,
      (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
        (right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)))\<^sup>\<sharp>,
      Z\<^bsup>X\<^esup>,
      Z\<^bsup>Y\<^esup>)"
  proof (rule iffD2[OF is_cart_prod_def2[OF left_eval_type right_eval_type]], clarify)
    fix f g H
    assume f_type[type_rule]: "f : H \<rightarrow> Z\<^bsup>X\<^esup>"
    assume g_type[type_rule]: "g : H \<rightarrow> Z\<^bsup>Y\<^esup>"
    show "\<exists>h. h : H \<rightarrow> Z\<^bsup>(X \<Coprod> Y)\<^esup> \<and>
           (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h = f \<and>
           (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h = g \<and>
           (\<forall>h2. h2 : H \<rightarrow> Z\<^bsup>(X \<Coprod> Y)\<^esup> \<and>
                 (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h2 = f \<and>
                 (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h2 = g \<longrightarrow>
                 h2 = h)"
    proof (intro exI[where x="(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>"], safe, typecheck_cfuncs)
      have left_cross_mediator:
          "(left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
             (id(X) \<times>\<^sub>f
               (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) =
           left_coproj(X, Y) \<times>\<^sub>f
             (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>"
        by (typecheck_cfuncs,
            simp add: cfunc_cross_prod_comp_cfunc_cross_prod
              id_left_unit2 id_right_unit2)
      have left_mediator_cross_type:
          "id(X) \<times>\<^sub>f
             (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp> :
           X \<times>\<^sub>c H \<rightarrow> X \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
        by typecheck_cfuncs
      have left_coproj_cross_type:
          "left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>) :
           X \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow>
           (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
        by typecheck_cfuncs
      have coproduct_eval_type:
          "eval_func(Z, X \<Coprod> Y) :
           (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z"
        by typecheck_cfuncs
      have eval_left_mediator:
          "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
             (left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
             (id(X) \<times>\<^sub>f
               (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) =
           eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
             (left_coproj(X, Y) \<times>\<^sub>f
               (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>)"
      proof -
        have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
              (left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
              (id(X) \<times>\<^sub>f
                (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) =
            eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
              ((left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
               (id(X) \<times>\<^sub>f
                 (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>))"
          by (rule sym,
              rule comp_associative2[
                OF left_mediator_cross_type left_coproj_cross_type coproduct_eval_type])
        also have "... =
            eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
              (left_coproj(X, Y) \<times>\<^sub>f
                (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>)"
          using left_cross_mediator by simp
        finally show ?thesis.
      qed
      have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp> = 
            ((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>))\<^sup>\<sharp>"
        using sharp_comp by (typecheck_cfuncs, blast)
      also have "... = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  (left_coproj(X, Y) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>))\<^sup>\<sharp>"
        using eval_left_mediator by simp
      also have "... = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  (id (X \<Coprod> Y) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) \<circ>\<^sub>c (left_coproj(X, Y) \<times>\<^sub>f id(H)))\<^sup>\<sharp>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c (dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id(H)))\<^sup>\<sharp>"
        using comp_associative2 transpose_func_def by (typecheck_cfuncs, force)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H))\<^sup>\<sharp>"
        by (simp add: dist_prod_coprod_right_left_coproj)
      also have "... = f"
        by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod sharp_cancels_flat)
      finally show "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp> = f".
    next
      have right_cross_mediator:
          "(right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
             (id(Y) \<times>\<^sub>f
               (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) =
           right_coproj(X, Y) \<times>\<^sub>f
             (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>"
        by (typecheck_cfuncs,
            simp add: cfunc_cross_prod_comp_cfunc_cross_prod
              id_left_unit2 id_right_unit2)
      have right_mediator_cross_type:
          "id(Y) \<times>\<^sub>f
             (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp> :
           Y \<times>\<^sub>c H \<rightarrow> Y \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
        by typecheck_cfuncs
      have right_coproj_cross_type:
          "right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>) :
           Y \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow>
           (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
        by typecheck_cfuncs
      have coproduct_eval_type:
          "eval_func(Z, X \<Coprod> Y) :
           (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z"
        by typecheck_cfuncs
      have eval_right_mediator:
          "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
             (right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
             (id(Y) \<times>\<^sub>f
               (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) =
           eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
             (right_coproj(X, Y) \<times>\<^sub>f
               (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>)"
      proof -
        have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
              (right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
              (id(Y) \<times>\<^sub>f
                (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) =
            eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
              ((right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
               (id(Y) \<times>\<^sub>f
                 (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>))"
          by (rule sym,
              rule comp_associative2[
                OF right_mediator_cross_type right_coproj_cross_type coproduct_eval_type])
        also have "... =
            eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
              (right_coproj(X, Y) \<times>\<^sub>f
                (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>)"
          using right_cross_mediator by simp
        finally show ?thesis.
      qed
      have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp> = 
            ((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>))\<^sup>\<sharp>"
        using sharp_comp by (typecheck_cfuncs, blast)
      also have "... = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  (right_coproj(X, Y) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>))\<^sup>\<sharp>"
        using eval_right_mediator by simp
      also have "... = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  (id (X \<Coprod> Y) \<times>\<^sub>f (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>) \<circ>\<^sub>c (right_coproj(X, Y) \<times>\<^sub>f id(H)))\<^sup>\<sharp>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c (dist_prod_coprod_right(X, Y, H) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id(H)))\<^sup>\<sharp>"
        using comp_associative2 transpose_func_def by (typecheck_cfuncs, force)
      also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H))\<^sup>\<sharp>"
        by (simp add: dist_prod_coprod_right_right_coproj)
      also have "... = g"
        by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod sharp_cancels_flat)
      finally show "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp> = g".
    next
      fix h 
      assume h_type[type_rule]: "h : H \<rightarrow> Z\<^bsup>(X \<Coprod> Y)\<^esup>"
      assume f_eqs: "f = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c  h"
      assume g_eqs: "g = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h"
      have "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H)) = h\<^sup>\<flat>"
      proof(etcs_rule one_separator[where X = "(X \<Coprod> Y) \<times>\<^sub>c H", where Y = Z])
        show "\<And>xyh. xyh \<in>\<^sub>c (X \<Coprod> Y) \<times>\<^sub>c H \<Longrightarrow> (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H)) \<circ>\<^sub>c xyh = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
        proof-
          fix xyh
          assume l_type[type_rule]: "xyh \<in>\<^sub>c (X \<Coprod> Y) \<times>\<^sub>c H"
          then obtain xy and z where xy_type[type_rule]: "xy \<in>\<^sub>c X \<Coprod> Y" and z_type[type_rule]: "z \<in>\<^sub>c H"
            and xyh_def: "xyh = \<langle>xy,z\<rangle>"
            using cart_prod_decomp by blast
          show "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H)) \<circ>\<^sub>c xyh = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
          proof(cases "\<exists>x. x \<in>\<^sub>c X \<and> xy =  left_coproj(X, Y) \<circ>\<^sub>c x")
            assume "\<exists>x. x \<in>\<^sub>c X \<and> xy = left_coproj(X, Y) \<circ>\<^sub>c x"
            then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and xy_def: "xy =  left_coproj(X, Y) \<circ>\<^sub>c x"
              by blast
            have left_cross:
                "(left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
                   (id(X) \<times>\<^sub>f h) =
                 left_coproj(X, Y) \<times>\<^sub>f h"
              by (typecheck_cfuncs,
                  simp add: cfunc_cross_prod_comp_cfunc_cross_prod
                    id_left_unit2 id_right_unit2)
            have idX_h_type:
                "id(X) \<times>\<^sub>f h :
                 X \<times>\<^sub>c H \<rightarrow> X \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
              by typecheck_cfuncs
            have left_cross_id_type:
                "left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>) :
                 X \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow>
                 (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
              by typecheck_cfuncs
            have coproduct_eval_type:
                "eval_func(Z, X \<Coprod> Y) :
                 (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z"
              by typecheck_cfuncs
            have eval_left_cross:
                "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   (left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
                   (id(X) \<times>\<^sub>f h) =
                 eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   (left_coproj(X, Y) \<times>\<^sub>f h)"
            proof -
              have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    (left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
                    (id(X) \<times>\<^sub>f h) =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    ((left_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
                     (id(X) \<times>\<^sub>f h))"
                by (rule sym,
                    rule comp_associative2[
                      OF idX_h_type left_cross_id_type coproduct_eval_type])
              also have "... =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    (left_coproj(X, Y) \<times>\<^sub>f h)"
                using left_cross by simp
              finally show ?thesis.
            qed
            have left_cross_pair:
                "(left_coproj(X, Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>x,z\<rangle> =
                 \<langle>left_coproj(X, Y) \<circ>\<^sub>c x, h \<circ>\<^sub>c z\<rangle>"
              using cfunc_cross_prod_comp_cfunc_prod
              by (typecheck_cfuncs, fastforce)
            have xz_type:
                "\<langle>x,z\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c H"
              by typecheck_cfuncs
            have left_h_type:
                "left_coproj(X, Y) \<times>\<^sub>f h :
                 X \<times>\<^sub>c H \<rightarrow>
                 (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
              by typecheck_cfuncs
            have eval_left_pair:
                "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   (left_coproj(X, Y) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>x,z\<rangle> =
                 eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   \<langle>left_coproj(X, Y) \<circ>\<^sub>c x, h \<circ>\<^sub>c z\<rangle>"
            proof -
              have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    (left_coproj(X, Y) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>x,z\<rangle> =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    ((left_coproj(X, Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>x,z\<rangle>)"
                by (rule sym,
                    rule comp_associative2[
                      OF xz_type left_h_type coproduct_eval_type])
              also have "... =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    \<langle>left_coproj(X, Y) \<circ>\<^sub>c x, h \<circ>\<^sub>c z\<rangle>"
                using left_cross_pair by simp
              finally show ?thesis.
            qed
            have "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H)) \<circ>\<^sub>c xyh = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (dist_prod_coprod_right(X, Y, H)  \<circ>\<^sub>c \<langle>left_coproj(X, Y) \<circ>\<^sub>c x,z\<rangle>)"
              by (typecheck_cfuncs, simp add: comp_associative2 xy_def xyh_def)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c ((dist_prod_coprod_right(X, Y, H)  \<circ>\<^sub>c (left_coproj(X, Y) \<times>\<^sub>f id(H))) \<circ>\<^sub>c \<langle>x,z\<rangle>)"
              using dist_prod_coprod_right_ap_left dist_prod_coprod_right_left_coproj by (typecheck_cfuncs, fastforce)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (left_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H)  \<circ>\<^sub>c \<langle>x,z\<rangle>)"
              using dist_prod_coprod_right_left_coproj by fastforce
            also have "... = f\<^sup>\<flat> \<circ>\<^sub>c \<langle>x,z\<rangle>"
              by (typecheck_cfuncs,  simp add: comp_associative2 left_coproj_cfunc_coprod)
            also have "... = ((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c  h)\<^sup>\<flat>  \<circ>\<^sub>c \<langle>x,z\<rangle>"
              using f_eqs by fastforce
            also have "... = (((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp>\<^sup>\<flat>) \<circ>\<^sub>c  (id(X) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>x,z\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, fastforce)
            also have "... = ((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c  (id(X) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>x,z\<rangle>"
              by (typecheck_cfuncs, simp add: flat_cancels_sharp)
            also have "... = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>x,z\<rangle>"
              using eval_left_cross by simp
            also have "... = eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  \<langle>left_coproj(X, Y) \<circ>\<^sub>c x, h \<circ>\<^sub>c z\<rangle>"
              using eval_left_pair by simp
            also have "... = eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  ((id(X \<Coprod> Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>xy,z\<rangle>)"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 xy_def)
            also have "... = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
              by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def3 xyh_def)
            finally show ?thesis.
          next
            assume "\<not> (\<exists>x. x \<in>\<^sub>c X \<and> xy = left_coproj(X, Y) \<circ>\<^sub>c x)"
            then obtain y where y_type[type_rule]: "y \<in>\<^sub>c Y" and xy_def: "xy =  right_coproj(X, Y) \<circ>\<^sub>c y"
              using  coprojs_jointly_surj by (typecheck_cfuncs, blast)
            have right_cross:
                "(right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
                   (id(Y) \<times>\<^sub>f h) =
                 right_coproj(X, Y) \<times>\<^sub>f h"
              by (typecheck_cfuncs,
                  simp add: cfunc_cross_prod_comp_cfunc_cross_prod
                    id_left_unit2 id_right_unit2)
            have idY_h_type:
                "id(Y) \<times>\<^sub>f h :
                 Y \<times>\<^sub>c H \<rightarrow> Y \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
              by typecheck_cfuncs
            have right_cross_id_type:
                "right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>) :
                 Y \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow>
                 (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
              by typecheck_cfuncs
            have coproduct_eval_type:
                "eval_func(Z, X \<Coprod> Y) :
                 (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup> \<rightarrow> Z"
              by typecheck_cfuncs
            have eval_right_cross:
                "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   (right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
                   (id(Y) \<times>\<^sub>f h) =
                 eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   (right_coproj(X, Y) \<times>\<^sub>f h)"
            proof -
              have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    (right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>))) \<circ>\<^sub>c
                    (id(Y) \<times>\<^sub>f h) =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    ((right_coproj(X, Y) \<times>\<^sub>f id(Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c
                     (id(Y) \<times>\<^sub>f h))"
                by (rule sym,
                    rule comp_associative2[
                      OF idY_h_type right_cross_id_type coproduct_eval_type])
              also have "... =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    (right_coproj(X, Y) \<times>\<^sub>f h)"
                using right_cross by simp
              finally show ?thesis.
            qed
            have right_cross_pair:
                "(right_coproj(X, Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>y,z\<rangle> =
                 \<langle>right_coproj(X, Y) \<circ>\<^sub>c y, h \<circ>\<^sub>c z\<rangle>"
              using cfunc_cross_prod_comp_cfunc_prod
              by (typecheck_cfuncs, fastforce)
            have yz_type:
                "\<langle>y,z\<rangle> : \<one> \<rightarrow> Y \<times>\<^sub>c H"
              by typecheck_cfuncs
            have right_h_type:
                "right_coproj(X, Y) \<times>\<^sub>f h :
                 Y \<times>\<^sub>c H \<rightarrow>
                 (X \<Coprod> Y) \<times>\<^sub>c Z\<^bsup>(X \<Coprod> Y)\<^esup>"
              by typecheck_cfuncs
            have eval_right_pair:
                "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   (right_coproj(X, Y) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>y,z\<rangle> =
                 eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                   \<langle>right_coproj(X, Y) \<circ>\<^sub>c y, h \<circ>\<^sub>c z\<rangle>"
            proof -
              have "(eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    (right_coproj(X, Y) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>y,z\<rangle> =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    ((right_coproj(X, Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>y,z\<rangle>)"
                by (rule sym,
                    rule comp_associative2[
                      OF yz_type right_h_type coproduct_eval_type])
              also have "... =
                  eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c
                    \<langle>right_coproj(X, Y) \<circ>\<^sub>c y, h \<circ>\<^sub>c z\<rangle>"
                using right_cross_pair by simp
              finally show ?thesis.
            qed
            have "(f\<^sup>\<flat> \<amalg> g\<^sup>\<flat> \<circ>\<^sub>c dist_prod_coprod_right(X, Y, H)) \<circ>\<^sub>c xyh = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (dist_prod_coprod_right(X, Y, H)  \<circ>\<^sub>c \<langle>right_coproj(X, Y) \<circ>\<^sub>c y,z\<rangle>)"
              by (typecheck_cfuncs, simp add: comp_associative2 xy_def xyh_def)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c ((dist_prod_coprod_right(X, Y, H)  \<circ>\<^sub>c (right_coproj(X, Y) \<times>\<^sub>f id(H))) \<circ>\<^sub>c \<langle>y,z\<rangle>)"
              using dist_prod_coprod_right_ap_right dist_prod_coprod_right_right_coproj by (typecheck_cfuncs, fastforce)
            also have "... = (f\<^sup>\<flat> \<amalg> g\<^sup>\<flat>) \<circ>\<^sub>c (right_coproj(X \<times>\<^sub>c H, Y \<times>\<^sub>c H)  \<circ>\<^sub>c \<langle>y,z\<rangle>)"
              using dist_prod_coprod_right_right_coproj by fastforce
            also have "... = g\<^sup>\<flat> \<circ>\<^sub>c \<langle>y,z\<rangle>"
              by (typecheck_cfuncs,  simp add: comp_associative2 right_coproj_cfunc_coprod)
            also have "... = ((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c  h)\<^sup>\<flat>  \<circ>\<^sub>c \<langle>y,z\<rangle>"
              using g_eqs by fastforce
            also have "... = (((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp>\<^sup>\<flat>) \<circ>\<^sub>c  (id(Y) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>y,z\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, fastforce)
            also have "... = ((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>)) \<circ>\<^sub>c  (id(Y) \<times>\<^sub>f h)) \<circ>\<^sub>c \<langle>y,z\<rangle>"
              by (typecheck_cfuncs, simp add: flat_cancels_sharp)
            also have "... = (eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>y,z\<rangle>"
              using eval_right_cross by simp
            also have "... = eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  \<langle>right_coproj(X, Y) \<circ>\<^sub>c y, h \<circ>\<^sub>c z\<rangle>"
              using eval_right_pair by simp
            also have "... = eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c  ((id(X \<Coprod> Y) \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>xy,z\<rangle>)"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 xy_def)
            also have "... = h\<^sup>\<flat> \<circ>\<^sub>c xyh"
              by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def3 xyh_def)
            finally show ?thesis.
          qed
        qed
      qed
      then show "h = (((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c left_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat> \<amalg>
                     ((eval_func(Z, X \<Coprod> Y) \<circ>\<^sub>c right_coproj(X, Y) \<times>\<^sub>f id\<^sub>c (Z\<^bsup>(X \<Coprod> Y)\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h)\<^sup>\<flat> \<circ>\<^sub>c
                                                                      dist_prod_coprod_right(X, Y, H))\<^sup>\<sharp>"
        using f_eqs g_eqs h_type sharp_cancels_flat by force
    qed
  qed
  then show ?thesis
    using canonical_cart_prod_is_cart_prod cart_prods_isomorphic is_isomorphic_def
    by fastforce
qed

lemma empty_exp_nonempty:
  assumes "nonempty(X)"
  shows "\<emptyset>\<^bsup>X\<^esup> \<cong> \<emptyset>"
proof-
  obtain j where j_type[type_rule]: "j: \<emptyset>\<^bsup>X\<^esup> \<rightarrow> \<one>\<times>\<^sub>c \<emptyset>\<^bsup>X\<^esup>" and j_def: "isomorphism(j)"
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

lemma exp_pres_iso_left:
  assumes "A \<cong> X" 
  shows "A\<^bsup>Y\<^esup> \<cong>  X\<^bsup>Y\<^esup>"
proof - 
  obtain \<phi> where \<phi>_def: "\<phi>: X \<rightarrow> A \<and> isomorphism(\<phi>)"
    using assms is_isomorphic_def isomorphic_is_symmetric by blast
  obtain \<psi> where \<psi>_def: "\<psi>: A \<rightarrow> X \<and> isomorphism(\<psi>) \<and> (\<psi> \<circ>\<^sub>c \<phi> = id(X))"
    using \<phi>_def cfunc_type_def isomorphism_def by fastforce
  have phi_type: "\<phi> : X \<rightarrow> A"
    using \<phi>_def by blast
  have phi_iso: "isomorphism(\<phi>)"
    using \<phi>_def by blast
  have psi_type: "\<psi> : A \<rightarrow> X"
    using \<psi>_def by blast
  have psi_phi: "\<psi> \<circ>\<^sub>c \<phi> = id(X)"
    using \<psi>_def by blast
  obtain \<chi> where chi_type: "\<chi> : A \<rightarrow> X"
      and chi_phi: "\<chi> \<circ>\<^sub>c \<phi> = id(X)"
      and phi_chi: "\<phi> \<circ>\<^sub>c \<chi> = id(A)"
    using iffD1[OF isomorphism_def3[OF phi_type] phi_iso] by blast
  have psi_eq_chi: "\<psi> = \<chi>"
  proof -
    have "\<psi> = \<psi> \<circ>\<^sub>c id(A)"
      by (rule sym, rule id_right_unit2[OF psi_type])
    also have "... = \<psi> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c \<chi>)"
      using phi_chi by simp
    also have "... = (\<psi> \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c \<chi>"
      by (rule comp_associative2[OF chi_type phi_type psi_type])
    also have "... = id(X) \<circ>\<^sub>c \<chi>"
      using psi_phi by simp
    also have "... = \<chi>"
      by (rule id_left_unit2[OF chi_type])
    finally show ?thesis.
  qed
  have idA: "\<phi> \<circ>\<^sub>c \<psi> = id(A)"
    using psi_eq_chi phi_chi by simp
  have phi_eval_type: "(\<phi> \<circ>\<^sub>c eval_func(X, Y))\<^sup>\<sharp>: X\<^bsup>Y\<^esup> \<rightarrow> A\<^bsup>Y\<^esup>"
    using \<phi>_def by (typecheck_cfuncs, blast)
  have psi_eval_type: "(\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp>: A\<^bsup>Y\<^esup> \<rightarrow> X\<^bsup>Y\<^esup>"
    using \<psi>_def by (typecheck_cfuncs, blast)

  have idXY: "(\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp> \<circ>\<^sub>c  (\<phi> \<circ>\<^sub>c eval_func(X, Y))\<^sup>\<sharp> = id(X\<^bsup>Y\<^esup>)"
  proof - 
    have "(\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c eval_func(X, Y))\<^sup>\<sharp> = \<psi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c \<phi>\<^bsup>Y\<^esup>\<^sub>f"
      using \<phi>_def \<psi>_def exp_func_def2 by auto
    also have "... = (\<psi> \<circ>\<^sub>c \<phi>)\<^bsup>Y\<^esup>\<^sub>f"
      by (rule sym, rule transpose_factors[OF phi_type psi_type])
    also have "... = (id(X))\<^bsup>Y\<^esup>\<^sub>f"
      by (simp add: \<psi>_def)
    also have "...  = id(X\<^bsup>Y\<^esup>)"
      by (simp add: exponential_object_identity2)
    finally show "(\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp> \<circ>\<^sub>c  (\<phi> \<circ>\<^sub>c eval_func(X, Y))\<^sup>\<sharp> = id(X\<^bsup>Y\<^esup>)".
  qed
  have idAY: "(\<phi> \<circ>\<^sub>c eval_func(X, Y))\<^sup>\<sharp> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp>  = id(A\<^bsup>Y\<^esup>)"
  proof - 
    have "(\<phi> \<circ>\<^sub>c eval_func(X, Y))\<^sup>\<sharp> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp> = \<phi>\<^bsup>Y\<^esup>\<^sub>f \<circ>\<^sub>c \<psi>\<^bsup>Y\<^esup>\<^sub>f"
      using \<phi>_def \<psi>_def exp_func_def2 by auto
    also have "... = (\<phi> \<circ>\<^sub>c \<psi>)\<^bsup>Y\<^esup>\<^sub>f"
      by (rule sym, rule transpose_factors[OF psi_type phi_type])
    also have "... = (id(A))\<^bsup>Y\<^esup>\<^sub>f"
      by (simp add: idA)
    also have "...  = id(A\<^bsup>Y\<^esup>)"
      by (simp add: exponential_object_identity2)
    finally show "(\<phi> \<circ>\<^sub>c eval_func(X, Y))\<^sup>\<sharp> \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp>  = id(A\<^bsup>Y\<^esup>)".
  qed
  have psi_eval_iso:
      "isomorphism((\<psi> \<circ>\<^sub>c eval_func(A, Y))\<^sup>\<sharp>)"
    unfolding isomorphism_def3[OF psi_eval_type]
    using phi_eval_type idAY idXY by auto
  show  "A\<^bsup>Y\<^esup> \<cong>  X\<^bsup>Y\<^esup>"
    unfolding is_isomorphic_def
    using psi_eval_type psi_eval_iso by auto
qed

lemma expset_power_tower:
  "(A\<^bsup>B\<^esup>)\<^bsup>C\<^esup> \<cong> A\<^bsup>(B\<times>\<^sub>c C)\<^esup>"
proof - 
  obtain \<phi> where \<phi>_def: "\<phi> = ((eval_func(A, B\<times>\<^sub>c C)) \<circ>\<^sub>c (associate_left(B, C, A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)))" and
                 \<phi>_type[type_rule]: "\<phi>: B \<times>\<^sub>c (C\<times>\<^sub>c (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)) \<rightarrow> A" and 
                 \<phi>dbsharp_type[type_rule]: "(\<phi>\<^sup>\<sharp>)\<^sup>\<sharp> : (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>) \<rightarrow> ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
    using transpose_func_type by (typecheck_cfuncs, fastforce)

  obtain \<psi> where \<psi>_def: "\<psi> = (eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c (associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))" and
                 \<psi>_type[type_rule]: "\<psi> :  (B \<times>\<^sub>c C) \<times>\<^sub>c ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>) \<rightarrow> A" and
                 \<psi>sharp_type[type_rule]: "\<psi>\<^sup>\<sharp>: (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup> \<rightarrow> (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)"
    using transpose_func_type by (typecheck_cfuncs, blast)

  have dbsharp_sharp_id: "\<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp> = id((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
  proof(etcs_rule same_evals_equal[where X = "(A\<^bsup>B\<^esup>)", where A = "C"])
    show "eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c id\<^sub>c(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp> =
          eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c id\<^sub>c(C) \<times>\<^sub>f id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>)"
    proof(etcs_rule same_evals_equal[where X = "A", where A = "B"])
      show "eval_func(A, B) \<circ>\<^sub>c id\<^sub>c(B) \<times>\<^sub>f (eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c (id\<^sub>c(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp>)) =
            eval_func(A, B) \<circ>\<^sub>c id\<^sub>c(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c id\<^sub>c(C) \<times>\<^sub>f id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>)"
      proof - 
        have inner_cross:
            "id(C) \<times>\<^sub>f (\<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp>) =
             (id(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>) \<circ>\<^sub>c
             (id(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>)"
          by (rule identity_distributes_across_composition[
                OF \<psi>sharp_type \<phi>dbsharp_type])
        have "eval_func(A, B) \<circ>\<^sub>c id\<^sub>c(B) \<times>\<^sub>f (eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c (id\<^sub>c(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> \<circ>\<^sub>c \<psi>\<^sup>\<sharp>)) =
              eval_func(A, B) \<circ>\<^sub>c id\<^sub>c(B) \<times>\<^sub>f (eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c (id\<^sub>c(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          using inner_cross by simp
        also have "... = eval_func(A, B) \<circ>\<^sub>c id\<^sub>c(B) \<times>\<^sub>f ((eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c (id\<^sub>c(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = eval_func(A, B) \<circ>\<^sub>c id\<^sub>c(B) \<times>\<^sub>f (\<phi>\<^sup>\<sharp> \<circ>\<^sub>c (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (typecheck_cfuncs, simp add: transpose_func_def)        
        also have "... = eval_func(A, B) \<circ>\<^sub>c ((id\<^sub>c(B) \<times>\<^sub>f \<phi>\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c(B) \<times>\<^sub>f (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>)))"
          using identity_distributes_across_composition by (typecheck_cfuncs, auto)
        also have "... = (eval_func(A, B) \<circ>\<^sub>c ((id\<^sub>c(B) \<times>\<^sub>f \<phi>\<^sup>\<sharp>)))  \<circ>\<^sub>c (id\<^sub>c(B) \<times>\<^sub>f (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          using comp_associative2 by (typecheck_cfuncs,blast)
        also have "... = \<phi>  \<circ>\<^sub>c (id\<^sub>c(B) \<times>\<^sub>f (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (typecheck_cfuncs, simp add: transpose_func_def)
        also have "... = ((eval_func(A, B\<times>\<^sub>c C)) \<circ>\<^sub>c (associate_left(B, C, A\<^bsup>(B\<times>\<^sub>c C)\<^esup>))) \<circ>\<^sub>c (id\<^sub>c(B) \<times>\<^sub>f (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          by (simp add: \<phi>_def)
        also have "... = (eval_func(A, B\<times>\<^sub>c C)) \<circ>\<^sub>c (associate_left(B, C, A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)) \<circ>\<^sub>c (id\<^sub>c(B) \<times>\<^sub>f (id\<^sub>c(C) \<times>\<^sub>f \<psi>\<^sup>\<sharp>))"
          using comp_associative2 by (typecheck_cfuncs, auto)
        also have "... = (eval_func(A, B\<times>\<^sub>c C)) \<circ>\<^sub>c ((id\<^sub>c(B) \<times>\<^sub>f id\<^sub>c(C)) \<times>\<^sub>f \<psi>\<^sup>\<sharp>) \<circ>\<^sub>c associate_left(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
          by (typecheck_cfuncs, simp add: associate_left_crossprod_ap)
        also have "... = (eval_func(A, B\<times>\<^sub>c C)) \<circ>\<^sub>c ((id\<^sub>c (B \<times>\<^sub>c C)) \<times>\<^sub>f \<psi>\<^sup>\<sharp>) \<circ>\<^sub>c associate_left(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
          by (simp add: id_cross_prod)
        also have "... = \<psi> \<circ>\<^sub>c associate_left(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
          by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
        also have "... = ((eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C))) \<circ>\<^sub>c ((associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))\<circ>\<^sub>c  associate_left(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))"
          by (typecheck_cfuncs, simp add: \<psi>_def cfunc_type_def comp_associative)
        also have "... = ((eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C))) \<circ>\<^sub>c id(B \<times>\<^sub>c (C \<times>\<^sub>c ((A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)))"
          by (simp add: right_left)
        also have "... = (eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C))"
          using id_right_unit2 by (typecheck_cfuncs, blast)
        also have "... = eval_func(A, B) \<circ>\<^sub>c id\<^sub>c(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C) \<circ>\<^sub>c id\<^sub>c(C) \<times>\<^sub>f id\<^sub>c (A\<^bsup>B\<^esup>\<^bsup>C\<^esup>)"
          by (typecheck_cfuncs, simp add: id_cross_prod id_right_unit2)
        finally show ?thesis.
      qed
    qed
  qed
  have sharp_dbsharp_id: "\<psi>\<^sup>\<sharp> \<circ>\<^sub>c \<phi>\<^sup>\<sharp>\<^sup>\<sharp> = id(A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)"
  proof(etcs_rule same_evals_equal[where X = "A", where A = "(B \<times>\<^sub>c C)"])
    show "eval_func(A, B \<times>\<^sub>c C) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp> \<circ>\<^sub>c \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) = 
          eval_func(A, B \<times>\<^sub>c C) \<circ>\<^sub>c id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f id\<^sub>c (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)"
    proof -
      have evalB_type:
          "eval_func(A, B) : B \<times>\<^sub>c A\<^bsup>B\<^esup> \<rightarrow> A"
        by typecheck_cfuncs
      have cross_eval_type:
          "id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C) :
           B \<times>\<^sub>c (C \<times>\<^sub>c (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>) \<rightarrow>
           B \<times>\<^sub>c A\<^bsup>B\<^esup>"
        by typecheck_cfuncs
      have assoc_right_type:
          "associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>) :
           (B \<times>\<^sub>c C) \<times>\<^sub>c (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup> \<rightarrow>
           B \<times>\<^sub>c (C \<times>\<^sub>c (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)"
        by typecheck_cfuncs
      have cross_phi_type:
          "id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp> :
           (B \<times>\<^sub>c C) \<times>\<^sub>c A\<^bsup>(B \<times>\<^sub>c C)\<^esup> \<rightarrow>
           (B \<times>\<^sub>c C) \<times>\<^sub>c (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>"
        by typecheck_cfuncs
      have eval_after_assoc_type:
          "(id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c
             associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>) :
           (B \<times>\<^sub>c C) \<times>\<^sub>c (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup> \<rightarrow>
           B \<times>\<^sub>c A\<^bsup>B\<^esup>"
        by (rule comp_type[OF assoc_right_type cross_eval_type])
      have psi_reassoc:
          "((eval_func(A, B) \<circ>\<^sub>c
               (id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C))) \<circ>\<^sub>c
              associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)) \<circ>\<^sub>c
             (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>) =
           eval_func(A, B) \<circ>\<^sub>c
             (((id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c
                associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)) \<circ>\<^sub>c
              (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))"
      proof -
        have "((eval_func(A, B) \<circ>\<^sub>c
                 (id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C))) \<circ>\<^sub>c
                associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)) \<circ>\<^sub>c
               (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>) =
              (eval_func(A, B) \<circ>\<^sub>c
                ((id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c
                 associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))) \<circ>\<^sub>c
               (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
          using comp_associative2[OF assoc_right_type cross_eval_type evalB_type]
          by simp
        also have "... =
            eval_func(A, B) \<circ>\<^sub>c
              (((id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c
                 associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)) \<circ>\<^sub>c
               (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))"
          by (rule sym,
              rule comp_associative2[
                OF cross_phi_type eval_after_assoc_type evalB_type])
        finally show ?thesis.
      qed
      have "eval_func(A, B \<times>\<^sub>c C) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp> \<circ>\<^sub>c \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) =
            eval_func(A, B \<times>\<^sub>c C) \<circ>\<^sub>c ((id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))"
        by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
      also have "... = ( eval_func(A, B \<times>\<^sub>c C) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f (\<psi>\<^sup>\<sharp>))) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = \<psi> \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
        by (typecheck_cfuncs, simp add: transpose_func_def)
      also have "... =(eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c (associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)) \<circ>\<^sub>c (id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
      proof -
        have "\<psi> \<circ>\<^sub>c
                (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>) =
              (eval_func(A, B) \<circ>\<^sub>c
                ((id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c
                 associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>))) \<circ>\<^sub>c
                (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
          using \<psi>_def by simp
        also have "... =
            eval_func(A, B) \<circ>\<^sub>c
              (((id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c
                 associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)) \<circ>\<^sub>c
               (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))"
          by (rule sym,
              rule comp_associative2[
                OF cross_phi_type eval_after_assoc_type evalB_type])
        also have "... =
            eval_func(A, B) \<circ>\<^sub>c
              ((id(B) \<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c
               (associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>) \<circ>\<^sub>c
                (id(B \<times>\<^sub>c C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)))"
          using comp_associative2[
            OF cross_phi_type assoc_right_type cross_eval_type] by simp
        finally show ?thesis.
      qed
      also have "... =(eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c (associate_right(B, C, (A\<^bsup>B\<^esup>)\<^bsup>C\<^esup>)) \<circ>\<^sub>c ((id\<^sub>c (B) \<times>\<^sub>f id( C)) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)"
        by (typecheck_cfuncs, simp add: id_cross_prod)
      also have "... =(eval_func(A, B)) \<circ>\<^sub>c ((id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c ((id\<^sub>c (B) \<times>\<^sub>f (id(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>)) \<circ>\<^sub>c (associate_right(B, C, A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))))"
        using associate_right_crossprod_ap by (typecheck_cfuncs, auto)
      also have "... =(eval_func(A, B)) \<circ>\<^sub>c ((id(B)\<times>\<^sub>f eval_func(A\<^bsup>B\<^esup>, C)) \<circ>\<^sub>c (id\<^sub>c (B) \<times>\<^sub>f (id(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))) \<circ>\<^sub>c (associate_right(B, C, A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... =(eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f ((eval_func(A\<^bsup>B\<^esup>, C))\<circ>\<^sub>c (id(C) \<times>\<^sub>f \<phi>\<^sup>\<sharp>\<^sup>\<sharp>))) \<circ>\<^sub>c (associate_right(B, C, A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        using identity_distributes_across_composition by (typecheck_cfuncs, auto)
      also have "... =(eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f \<phi>\<^sup>\<sharp>) \<circ>\<^sub>c (associate_right(B, C, A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: transpose_func_def)
      also have "... =((eval_func(A, B)) \<circ>\<^sub>c (id(B)\<times>\<^sub>f \<phi>\<^sup>\<sharp>)) \<circ>\<^sub>c (associate_right(B, C, A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = \<phi> \<circ>\<^sub>c (associate_right(B, C, A\<^bsup>(B \<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: transpose_func_def)
      also have "... = (eval_func(A, B\<times>\<^sub>c C)) \<circ>\<^sub>c ((associate_left(B, C, A\<^bsup>(B\<times>\<^sub>c C)\<^esup>)) \<circ>\<^sub>c (associate_right(B, C, A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)))"
        by (typecheck_cfuncs, simp add: \<phi>_def comp_associative2)  
      also have "... = eval_func(A, B\<times>\<^sub>c C) \<circ>\<^sub>c id ((B \<times>\<^sub>c C) \<times>\<^sub>c (A\<^bsup>(B\<times>\<^sub>c C)\<^esup>))"
        by (typecheck_cfuncs, simp add: left_right)
      also have "... = eval_func(A, B \<times>\<^sub>c C) \<circ>\<^sub>c id\<^sub>c (B \<times>\<^sub>c C) \<times>\<^sub>f id\<^sub>c (A\<^bsup>(B \<times>\<^sub>c C)\<^esup>)"
        by (typecheck_cfuncs, simp add: id_cross_prod)
      finally show ?thesis.
    qed
  qed
  have psi_sharp_iso: "isomorphism(\<psi>\<^sup>\<sharp>)"
    unfolding isomorphism_def3[OF \<psi>sharp_type]
    using \<phi>dbsharp_type dbsharp_sharp_id sharp_dbsharp_id by auto
  show ?thesis
    unfolding is_isomorphic_def
    using \<psi>sharp_type psi_sharp_iso by auto
qed

lemma exp_pres_iso_right:
  assumes "A \<cong> X" 
  shows "Y\<^bsup>A\<^esup> \<cong>  Y\<^bsup>X\<^esup>"
proof - 
  obtain \<phi> where \<phi>_def: "\<phi>: X \<rightarrow> A \<and> isomorphism(\<phi>)"
    using assms is_isomorphic_def isomorphic_is_symmetric by blast
  obtain \<psi> where \<psi>_def: "\<psi>: A \<rightarrow> X \<and> isomorphism(\<psi>) \<and> (\<psi> \<circ>\<^sub>c \<phi> = id(X))"
    using \<phi>_def cfunc_type_def isomorphism_def by fastforce
  have phi_type[type_rule]: "\<phi> : X \<rightarrow> A"
    using \<phi>_def by blast
  have phi_iso: "isomorphism(\<phi>)"
    using \<phi>_def by blast
  have psi_type[type_rule]: "\<psi> : A \<rightarrow> X"
    using \<psi>_def by blast
  have psi_phi: "\<psi> \<circ>\<^sub>c \<phi> = id(X)"
    using \<psi>_def by blast
  obtain \<chi> where chi_type: "\<chi> : A \<rightarrow> X"
      and chi_phi: "\<chi> \<circ>\<^sub>c \<phi> = id(X)"
      and phi_chi: "\<phi> \<circ>\<^sub>c \<chi> = id(A)"
    using iffD1[OF isomorphism_def3[OF phi_type] phi_iso] by blast
  have psi_eq_chi: "\<psi> = \<chi>"
  proof -
    have "\<psi> = \<psi> \<circ>\<^sub>c id(A)"
      by (rule sym, rule id_right_unit2[OF psi_type])
    also have "... = \<psi> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c \<chi>)"
      using phi_chi by simp
    also have "... = (\<psi> \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c \<chi>"
      by (rule comp_associative2[OF chi_type phi_type psi_type])
    also have "... = id(X) \<circ>\<^sub>c \<chi>"
      using psi_phi by simp
    also have "... = \<chi>"
      by (rule id_left_unit2[OF chi_type])
    finally show ?thesis.
  qed
  have idA: "\<phi> \<circ>\<^sub>c \<psi> = id(A)"
    using psi_eq_chi phi_chi by simp
  obtain f where f_def: "f = (eval_func(Y, X)) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>))" and f_type[type_rule]: "f: A\<times>\<^sub>c (Y\<^bsup>X\<^esup>) \<rightarrow> Y" and fsharp_type[type_rule]: "f\<^sup>\<sharp> : Y\<^bsup>X\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
    using \<psi>_def transpose_func_type by (typecheck_cfuncs, blast)
  obtain g where g_def: "g = (eval_func(Y, A)) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))" and  g_type[type_rule]: "g: X\<times>\<^sub>c (Y\<^bsup>A\<^esup>) \<rightarrow> Y" and gsharp_type[type_rule]: "g\<^sup>\<sharp> : Y\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>X\<^esup>"
    using \<phi>_def transpose_func_type by (typecheck_cfuncs, blast)
  have eval_YX_type:
      "eval_func(Y, X) : X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> Y"
    by typecheck_cfuncs
  have eval_YA_type:
      "eval_func(Y, A) : A \<times>\<^sub>c Y\<^bsup>A\<^esup> \<rightarrow> Y"
    by typecheck_cfuncs
  have psi_id_YA_type:
      "\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>) :
       A \<times>\<^sub>c Y\<^bsup>A\<^esup> \<rightarrow> X \<times>\<^sub>c Y\<^bsup>A\<^esup>"
    by typecheck_cfuncs
  have id_X_gsharp_type:
      "id(X) \<times>\<^sub>f g\<^sup>\<sharp> :
       X \<times>\<^sub>c Y\<^bsup>A\<^esup> \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>"
    by typecheck_cfuncs
  have phi_id_YX_type:
      "\<phi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>) :
       X \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> A \<times>\<^sub>c Y\<^bsup>X\<^esup>"
    by typecheck_cfuncs
  have id_A_fsharp_type:
      "id(A) \<times>\<^sub>f f\<^sup>\<sharp> :
       A \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> A \<times>\<^sub>c Y\<^bsup>A\<^esup>"
    by typecheck_cfuncs
  have psi_cross_gsharp:
      "(\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c
         (id(A) \<times>\<^sub>f g\<^sup>\<sharp>) =
       \<psi> \<times>\<^sub>f g\<^sup>\<sharp>"
    using cfunc_cross_prod_comp_cfunc_cross_prod[
        OF id_type gsharp_type psi_type id_type]
      id_right_unit2[OF psi_type] id_left_unit2[OF gsharp_type]
    by (simp only:)
  have psi_gsharp_factor:
      "(id(X) \<times>\<^sub>f g\<^sup>\<sharp>) \<circ>\<^sub>c
         (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)) =
       \<psi> \<times>\<^sub>f g\<^sup>\<sharp>"
    using cfunc_cross_prod_comp_cfunc_cross_prod[
        OF psi_type id_type id_type gsharp_type]
      id_left_unit2[OF psi_type] id_right_unit2[OF gsharp_type]
    by (simp only:)
  have phi_cross_fsharp:
      "(\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)) \<circ>\<^sub>c
         (id(X) \<times>\<^sub>f f\<^sup>\<sharp>) =
       \<phi> \<times>\<^sub>f f\<^sup>\<sharp>"
    using cfunc_cross_prod_comp_cfunc_cross_prod[
        OF id_type fsharp_type phi_type id_type]
      id_right_unit2[OF phi_type] id_left_unit2[OF fsharp_type]
    by (simp only:)
  have phi_fsharp_factor:
      "(id(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c
         (\<phi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)) =
       \<phi> \<times>\<^sub>f f\<^sup>\<sharp>"
    using cfunc_cross_prod_comp_cfunc_cross_prod[
        OF phi_type id_type id_type fsharp_type]
      id_left_unit2[OF phi_type] id_right_unit2[OF fsharp_type]
    by (simp only:)

  have fsharp_gsharp_id: "f\<^sup>\<sharp> \<circ>\<^sub>c g\<^sup>\<sharp> = id(Y\<^bsup>A\<^esup>)"
  proof(etcs_rule same_evals_equal[where X = Y, where A = A])
    have "eval_func(Y, A) \<circ>\<^sub>c id\<^sub>c(A) \<times>\<^sub>f f\<^sup>\<sharp> \<circ>\<^sub>c g\<^sup>\<sharp> = eval_func(Y, A) \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f g\<^sup>\<sharp>)"
      using fsharp_type gsharp_type identity_distributes_across_composition by auto
    also have "... = eval_func(Y, X) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (id\<^sub>c(A) \<times>\<^sub>f g\<^sup>\<sharp>)"
      using \<psi>_def cfunc_type_def comp_associative f_def f_type gsharp_type transpose_func_def by (typecheck_cfuncs, force)
    also have "... = eval_func(Y, X) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f g\<^sup>\<sharp>)"
      by (simp only: psi_cross_gsharp)
    also have "... = eval_func(Y, X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g\<^sup>\<sharp>) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))"
      by (simp only: psi_gsharp_factor)
    also have "... = eval_func(Y, A) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))"
    proof -
      have "eval_func(Y, X) \<circ>\<^sub>c
              ((id(X) \<times>\<^sub>f g\<^sup>\<sharp>) \<circ>\<^sub>c
               (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))) =
            (eval_func(Y, X) \<circ>\<^sub>c
              (id(X) \<times>\<^sub>f g\<^sup>\<sharp>)) \<circ>\<^sub>c
             (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))"
        by (rule comp_associative2[
              OF psi_id_YA_type id_X_gsharp_type eval_YX_type])
      also have "... = g \<circ>\<^sub>c
             (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))"
        by (simp only: transpose_func_def[OF g_type])
      also have "... =
            (eval_func(Y, A) \<circ>\<^sub>c
              (\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))) \<circ>\<^sub>c
             (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>))"
        by (simp only: g_def)
      also have "... =
            eval_func(Y, A) \<circ>\<^sub>c
              ((\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)) \<circ>\<^sub>c
               (\<psi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)))"
      proof -
        have phi_id_YA_type: "\<phi> \<times>\<^sub>f id(Y\<^bsup>A\<^esup>) : X \<times>\<^sub>c Y\<^bsup>A\<^esup> \<rightarrow> A \<times>\<^sub>c Y\<^bsup>A\<^esup>"
          by (rule cfunc_cross_prod_type[OF phi_type id_type])
        show ?thesis
          by (rule sym,
              rule comp_associative2[
                OF psi_id_YA_type phi_id_YA_type eval_YA_type])
      qed
      finally show ?thesis.
    qed
    also have "... = eval_func(Y, A) \<circ>\<^sub>c ((\<phi> \<circ>\<^sub>c \<psi>) \<times>\<^sub>f (id(Y\<^bsup>A\<^esup>) \<circ>\<^sub>c id(Y\<^bsup>A\<^esup>)))"
      using \<phi>_def \<psi>_def cfunc_cross_prod_comp_cfunc_cross_prod by (typecheck_cfuncs, auto)
    also have "... = eval_func(Y, A) \<circ>\<^sub>c id(A) \<times>\<^sub>f id(Y\<^bsup>A\<^esup>)"
      using idA id_right_unit2 by (typecheck_cfuncs, auto)
    finally show "eval_func(Y, A) \<circ>\<^sub>c id\<^sub>c(A) \<times>\<^sub>f f\<^sup>\<sharp> \<circ>\<^sub>c g\<^sup>\<sharp> = eval_func(Y, A) \<circ>\<^sub>c id\<^sub>c(A) \<times>\<^sub>f id\<^sub>c (Y\<^bsup>A\<^esup>)".
  qed

  have gsharp_fsharp_id: "g\<^sup>\<sharp> \<circ>\<^sub>c f\<^sup>\<sharp> = id(Y\<^bsup>X\<^esup>)"
  proof(etcs_rule same_evals_equal[where X = Y, where A = X])
    have "eval_func(Y, X) \<circ>\<^sub>c id\<^sub>c(X) \<times>\<^sub>f g\<^sup>\<sharp> \<circ>\<^sub>c f\<^sup>\<sharp> = eval_func(Y, X) \<circ>\<^sub>c (id\<^sub>c(X) \<times>\<^sub>f g\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c(X) \<times>\<^sub>f f\<^sup>\<sharp>)"
      using fsharp_type gsharp_type identity_distributes_across_composition by auto
    also have "... = eval_func(Y, A) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id\<^sub>c(X) \<times>\<^sub>f f\<^sup>\<sharp>)"
      using \<phi>_def cfunc_type_def comp_associative fsharp_type g_def g_type transpose_func_def by (typecheck_cfuncs, force)
    also have "... = eval_func(Y, A) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f f\<^sup>\<sharp>)"
      by (simp only: phi_cross_fsharp)
    also have "... = eval_func(Y, A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>))"
      by (simp only: phi_fsharp_factor)
    also have "... = eval_func(Y, X) \<circ>\<^sub>c (\<psi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c (\<phi> \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>))"
    proof -
      have "eval_func(Y, A) \<circ>\<^sub>c
              ((id(A) \<times>\<^sub>f f\<^sup>\<sharp>) \<circ>\<^sub>c
               (\<phi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>))) =
            (eval_func(Y, A) \<circ>\<^sub>c
              (id(A) \<times>\<^sub>f f\<^sup>\<sharp>)) \<circ>\<^sub>c
             (\<phi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>))"
        by (rule comp_associative2[
              OF phi_id_YX_type id_A_fsharp_type eval_YA_type])
      also have "... = f \<circ>\<^sub>c
             (\<phi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>))"
        by (simp only: transpose_func_def[OF f_type])
      also have "... =
            (eval_func(Y, X) \<circ>\<^sub>c
              (\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>))) \<circ>\<^sub>c
             (\<phi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>))"
        by (simp only: f_def)
      also have "... =
            eval_func(Y, X) \<circ>\<^sub>c
              ((\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)) \<circ>\<^sub>c
               (\<phi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)))"
      proof -
        have psi_id_YX_type: "\<psi> \<times>\<^sub>f id(Y\<^bsup>X\<^esup>) : A \<times>\<^sub>c Y\<^bsup>X\<^esup> \<rightarrow> X \<times>\<^sub>c Y\<^bsup>X\<^esup>"
          by (rule cfunc_cross_prod_type[OF psi_type id_type])
        show ?thesis
          by (rule sym,
              rule comp_associative2[
                OF phi_id_YX_type psi_id_YX_type eval_YX_type])
      qed
      finally show ?thesis.
    qed
    also have "... = eval_func(Y, X) \<circ>\<^sub>c ((\<psi> \<circ>\<^sub>c \<phi>) \<times>\<^sub>f (id(Y\<^bsup>X\<^esup>) \<circ>\<^sub>c id(Y\<^bsup>X\<^esup>)))"
      using \<phi>_def \<psi>_def cfunc_cross_prod_comp_cfunc_cross_prod by (typecheck_cfuncs, auto)
    also have "... = eval_func(Y, X) \<circ>\<^sub>c id(X) \<times>\<^sub>f id(Y\<^bsup>X\<^esup>)"
      using \<psi>_def id_left_unit2 by (typecheck_cfuncs, auto)
    finally show "eval_func(Y, X) \<circ>\<^sub>c id\<^sub>c(X) \<times>\<^sub>f g\<^sup>\<sharp> \<circ>\<^sub>c f\<^sup>\<sharp> = eval_func(Y, X) \<circ>\<^sub>c id\<^sub>c(X) \<times>\<^sub>f id\<^sub>c (Y\<^bsup>X\<^esup>)".
  qed
  have gsharp_iso: "isomorphism(g\<^sup>\<sharp>)"
    unfolding isomorphism_def3[OF gsharp_type]
    using fsharp_type fsharp_gsharp_id gsharp_fsharp_id by auto
  show ?thesis
    unfolding is_isomorphic_def
    using gsharp_type gsharp_iso by auto
qed

lemma exp_pres_iso:
  assumes "A \<cong> X" "B \<cong> Y" 
  shows "A\<^bsup>B\<^esup> \<cong>  X\<^bsup>Y\<^esup>"
  using assms exp_pres_iso_left exp_pres_iso_right isomorphic_is_transitive by blast

lemma empty_to_nonempty:
  assumes "nonempty(X)" "is_empty(Y)" 
  shows "Y\<^bsup>X\<^esup> \<cong> \<emptyset>"
  using assms exp_pres_iso_left isomorphic_is_transitive no_el_iff_iso_empty
    empty_exp_nonempty by blast

lemma exp_is_empty:
  assumes "is_empty(X)" 
  shows "Y\<^bsup>X\<^esup> \<cong> \<one>"
  using assms exp_pres_iso_right isomorphic_is_transitive no_el_iff_iso_empty exp_empty by blast

lemma nonempty_to_nonempty:
  assumes "nonempty(X)" "nonempty(Y)"
  shows "nonempty(Y\<^bsup>X\<^esup>)"
proof -
  obtain y where y_type: "y \<in>\<^sub>c Y"
    using assms(2) nonempty_def by auto
  have beta_type: "\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> : X \<times>\<^sub>c \<one> \<rightarrow> \<one>"
    by (rule terminal_func_type)
  have f_type: "y \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub> : X \<times>\<^sub>c \<one> \<rightarrow> Y"
    by (rule comp_type[OF beta_type y_type])
  have fsharp_type: "(y \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp> \<in>\<^sub>c Y\<^bsup>X\<^esup>"
    by (rule transpose_func_type[OF f_type])
  show ?thesis
    unfolding nonempty_def
    by (rule exI[where x="(y \<circ>\<^sub>c \<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>)\<^sup>\<sharp>"], rule fsharp_type)
qed

lemma empty_to_nonempty_converse:
  assumes "Y\<^bsup>X\<^esup> \<cong> \<emptyset>"
  shows "is_empty(Y) \<and> nonempty(X)"
proof -
  have X_nonempty: "nonempty(X)"
  proof (rule ccontr)
    assume "\<not> nonempty(X)"
    then have X_empty: "is_empty(X)"
      using nonempty_def is_empty_def by auto
    have YX_one: "Y\<^bsup>X\<^esup> \<cong> \<one>"
      using X_empty exp_is_empty by auto
    have one_empty: "\<one> \<cong> \<emptyset>"
      using assms YX_one isomorphic_is_symmetric isomorphic_is_transitive by blast
    have "is_empty(\<one>)"
      using one_empty no_el_iff_iso_empty by auto
    then show False
      using is_empty_def id_type by auto
  qed
  have Y_empty: "is_empty(Y)"
  proof (rule ccontr)
    assume "\<not> is_empty(Y)"
    then have Y_nonempty: "nonempty(Y)"
      using nonempty_def is_empty_def by auto
    have YX_nonempty: "nonempty(Y\<^bsup>X\<^esup>)"
      using X_nonempty Y_nonempty nonempty_to_nonempty by auto
    then have "\<not> is_empty(Y\<^bsup>X\<^esup>)"
      using nonempty_def is_empty_def by auto
    then show False
      using assms no_el_iff_iso_empty by auto
  qed
  show ?thesis using Y_empty X_nonempty by auto
qed

text \<open>The definition below corresponds to Definition 2.5.11 in Halvorson.\<close>
definition powerset :: "cset \<Rightarrow> cset" ("\<P>_" [101]100) where
  "\<P> X = \<Omega>\<^bsup>X\<^esup>"

lemma sets_squared:
  "A\<^bsup>\<Omega>\<^esup> \<cong> A \<times>\<^sub>c A"
proof - 
  obtain \<phi> where \<phi>_def: "\<phi> = \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                              eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle>" and
                 \<phi>_type[type_rule]: "\<phi> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A \<times>\<^sub>c A"
                  by (typecheck_cfuncs, simp)
  have "injective(\<phi>)"
    unfolding injective_def
  proof(clarify)
    fix f g 
    assume "f \<in>\<^sub>c domain(\<phi>)" then have f_type[type_rule]: "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
      using \<phi>_type cfunc_type_def by (typecheck_cfuncs, auto)
    assume "g \<in>\<^sub>c domain(\<phi>)" then have g_type[type_rule]: "g \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
      using \<phi>_type cfunc_type_def by (typecheck_cfuncs, auto)
    assume eqs: "\<phi> \<circ>\<^sub>c f = \<phi> \<circ>\<^sub>c g"
    show "f = g"
    proof(etcs_rule one_separator)
      show "\<And>id_1. id_1 \<in>\<^sub>c \<one> \<Longrightarrow> f \<circ>\<^sub>c id_1 = g \<circ>\<^sub>c id_1"
      proof(etcs_rule same_evals_equal[where X = A, where A = \<Omega>])
        fix id_1
        assume id1_is: "id_1 \<in>\<^sub>c \<one>"
        then have id1_eq: "id_1 = id(\<one>)"
          using id_type one_unique_element by auto

        obtain a1 a2 where phi_f_def: "\<phi> \<circ>\<^sub>c f = \<langle>a1,a2\<rangle> \<and> a1 \<in>\<^sub>c A \<and> a2 \<in>\<^sub>c A"
          using \<phi>_type cart_prod_decomp comp_type f_type by blast
        have equation1: "\<langle>a1,a2\<rangle> =  \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, f\<rangle>,
                            eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, f\<rangle>\<rangle>"
        proof - 
          have beta_type: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<one>"
            by (rule terminal_func_type)
          have t_beta_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega>"
            by (rule comp_type[OF beta_type true_func_type])
          have f_beta_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega>"
            by (rule comp_type[OF beta_type false_func_type])
          have idAO_type: "id(A\<^bsup>\<Omega>\<^esup>) : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A\<^bsup>\<Omega>\<^esup>"
            by (rule id_type)
          have pair1_type: "\<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
            by (rule cfunc_prod_type[OF t_beta_type idAO_type])
          have pair2_type: "\<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
            by (rule cfunc_prod_type[OF f_beta_type idAO_type])
          have eval_type: "eval_func(A, \<Omega>) : \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup> \<rightarrow> A"
            by (rule eval_func_type)
          have a_type: "eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A"
            by (rule comp_type[OF pair1_type eval_type])
          have b_type: "eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A"
            by (rule comp_type[OF pair2_type eval_type])
          have step1: "\<langle>a1,a2\<rangle> = \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                              eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c f"
            using \<phi>_def phi_f_def by auto
          have step2: "\<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                        eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c f =
                      \<langle>(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f,
                       (eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f\<rangle>"
            by (rule cfunc_prod_comp[OF f_type a_type b_type])
          have step3: "\<langle>(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f,
                        (eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f\<rangle> =
                      \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f,
                       eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f\<rangle>"
            using comp_associative2[OF f_type pair1_type eval_type]
              comp_associative2[OF f_type pair2_type eval_type]
            by simp
          have step4: "\<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f,
                       eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f\<rangle> =
                      \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>,
                       eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>\<rangle>"
            using cfunc_prod_comp[OF f_type t_beta_type idAO_type]
              cfunc_prod_comp[OF f_type f_beta_type idAO_type]
              comp_associative2[OF f_type beta_type true_func_type]
              comp_associative2[OF f_type beta_type false_func_type]
            by simp
          have beta_f_type: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f : \<one> \<rightarrow> \<one>"
            by (rule comp_type[OF f_type beta_type])
          have beta_f_eq: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = id(\<one>)"
          proof -
            have "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<beta>\<^bsub>\<one>\<^esub>"
              by (rule terminal_func_unique[OF beta_f_type])
            also have "... = id(\<one>)"
              by (rule sym[OF terminal_func_unique[OF id_type]])
            finally show ?thesis.
          qed
          have t_beta_f_eq: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<t>"
          proof -
            have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<t> \<circ>\<^sub>c id(\<one>)"
              using beta_f_eq by simp
            also have "... = \<t>"
              by (rule id_right_unit2[OF true_func_type])
            finally show ?thesis.
          qed
          have f_beta_f_eq: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<f>"
          proof -
            have "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<f> \<circ>\<^sub>c id(\<one>)"
              using beta_f_eq by simp
            also have "... = \<f>"
              by (rule id_right_unit2[OF false_func_type])
            finally show ?thesis.
          qed
          have idAO_f_eq: "id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f = f"
            by (rule id_left_unit2[OF f_type])
          show ?thesis
            using step1 step2 step3 step4 t_beta_f_eq f_beta_f_eq idAO_f_eq by simp
        qed
        have equation2: "\<langle>a1,a2\<rangle> =  \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, g\<rangle>,
                                    eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, g\<rangle>\<rangle>"
        proof -
          have beta_type: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<one>"
            by (rule terminal_func_type)
          have t_beta_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega>"
            by (rule comp_type[OF beta_type true_func_type])
          have f_beta_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega>"
            by (rule comp_type[OF beta_type false_func_type])
          have idAO_type: "id(A\<^bsup>\<Omega>\<^esup>) : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A\<^bsup>\<Omega>\<^esup>"
            by (rule id_type)
          have pair1_type: "\<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
            by (rule cfunc_prod_type[OF t_beta_type idAO_type])
          have pair2_type: "\<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
            by (rule cfunc_prod_type[OF f_beta_type idAO_type])
          have eval_type: "eval_func(A, \<Omega>) : \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup> \<rightarrow> A"
            by (rule eval_func_type)
          have a_type: "eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A"
            by (rule comp_type[OF pair1_type eval_type])
          have b_type: "eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A"
            by (rule comp_type[OF pair2_type eval_type])
          have step1: "\<langle>a1,a2\<rangle> = \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                          eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c g"
            using \<phi>_def eqs phi_f_def by auto
          have step2: "\<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                      eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c g =
                    \<langle>(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c g,
                     (eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c g\<rangle>"
            by (rule cfunc_prod_comp[OF g_type a_type b_type])
          have step3: "\<langle>(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c g,
                      (eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c g\<rangle> =
                    \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g,
                     eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g\<rangle>"
            using comp_associative2[OF g_type pair1_type eval_type]
              comp_associative2[OF g_type pair2_type eval_type]
            by simp
          have step4: "\<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g,
                     eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g\<rangle> =
                    \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c g\<rangle>,
                     eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c g\<rangle>\<rangle>"
            using cfunc_prod_comp[OF g_type t_beta_type idAO_type]
              cfunc_prod_comp[OF g_type f_beta_type idAO_type]
              comp_associative2[OF g_type beta_type true_func_type]
              comp_associative2[OF g_type beta_type false_func_type]
            by simp
          have beta_g_type: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g : \<one> \<rightarrow> \<one>"
            by (rule comp_type[OF g_type beta_type])
          have beta_g_eq: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g = id(\<one>)"
          proof -
            have "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g = \<beta>\<^bsub>\<one>\<^esub>"
              by (rule terminal_func_unique[OF beta_g_type])
            also have "... = id(\<one>)"
              by (rule sym[OF terminal_func_unique[OF id_type]])
            finally show ?thesis.
          qed
          have t_beta_g_eq: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g = \<t>"
          proof -
            have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g = \<t> \<circ>\<^sub>c id(\<one>)"
              using beta_g_eq by simp
            also have "... = \<t>"
              by (rule id_right_unit2[OF true_func_type])
            finally show ?thesis.
          qed
          have f_beta_g_eq: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g = \<f>"
          proof -
            have "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g = \<f> \<circ>\<^sub>c id(\<one>)"
              using beta_g_eq by simp
            also have "... = \<f>"
              by (rule id_right_unit2[OF false_func_type])
            finally show ?thesis.
          qed
          have idAO_g_eq: "id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c g = g"
            by (rule id_left_unit2[OF g_type])
          show ?thesis
            using step1 step2 step3 step4 t_beta_g_eq f_beta_g_eq idAO_g_eq by simp
        qed
        have "\<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, f\<rangle>, eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, f\<rangle>\<rangle> = 
              \<langle>eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, g\<rangle>, eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, g\<rangle>\<rangle>"
          using equation1 equation2 by auto
        then have equation3: "(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, f\<rangle> = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, g\<rangle>) \<and> 
                              (eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, f\<rangle> = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, g\<rangle>)"
          using  cart_prod_eq2 by (typecheck_cfuncs, auto)
        have "eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f f  = eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f g"
        proof(etcs_rule one_separator)
          fix x
          assume x_type[type_rule]: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<one>"
          then obtain w i where  x_def: "(w \<in>\<^sub>c \<Omega>) \<and> (i \<in>\<^sub>c \<one>) \<and> (x = \<langle>w,i\<rangle>)"
            using cart_prod_decomp by blast
          then have i_def: "i = id(\<one>)"
            using id1_eq id1_is one_unique_element by auto
          have w_def: "(w = \<f>) \<or> (w = \<t>)"
            by (simp add: true_false_only_truth_values x_def)
          then have x_def2: "(x = \<langle>\<f>,i\<rangle>) \<or> (x = \<langle>\<t>,i\<rangle>)"
            using x_def by auto
          show "(eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f g) \<circ>\<^sub>c x"
          proof(cases "(x = \<langle>\<f>,i\<rangle>)", clarify)
            assume case1: "x = \<langle>\<f>,i\<rangle>"
            have "(eval_func(A, \<Omega>) \<circ>\<^sub>c (id\<^sub>c(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<f>,i\<rangle> = eval_func(A, \<Omega>) \<circ>\<^sub>c ((id\<^sub>c(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>)"
              using case1 comp_associative2 x_type by (typecheck_cfuncs, auto)
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>id\<^sub>c(\<Omega>) \<circ>\<^sub>c  \<f>,f \<circ>\<^sub>c i\<rangle>"
              using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, f \<rangle>"
              using f_type false_func_type i_def id_left_unit2 id_right_unit2 by auto
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f>, g\<rangle>"
              using equation3 by blast
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>id\<^sub>c(\<Omega>) \<circ>\<^sub>c  \<f>,g \<circ>\<^sub>c i\<rangle>"
              by (typecheck_cfuncs, simp add: i_def id_left_unit2 id_right_unit2)
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c ((id\<^sub>c(\<Omega>) \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>)"
              using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
            also have "... = (eval_func(A, \<Omega>) \<circ>\<^sub>c (id\<^sub>c(\<Omega>) \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>"
              using case1 comp_associative2 x_type by (typecheck_cfuncs, auto)
            finally show "(eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>,i\<rangle> = (eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>".
          next
            assume case2: "x \<noteq> \<langle>\<f>,i\<rangle>"
            then have x_eq: "x = \<langle>\<t>,i\<rangle>"
              using x_def2 by blast
            have "(eval_func(A, \<Omega>) \<circ>\<^sub>c (id\<^sub>c(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<t>,i\<rangle> = eval_func(A, \<Omega>) \<circ>\<^sub>c ((id\<^sub>c(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>)"
                using case2 x_eq comp_associative2 x_type by (typecheck_cfuncs, auto)
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>id\<^sub>c(\<Omega>) \<circ>\<^sub>c  \<t>,f \<circ>\<^sub>c i\<rangle>"
                using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, f \<rangle>"
              using f_type i_def id_left_unit2 id_right_unit2 true_func_type by auto
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t>, g\<rangle>"
              using equation3 by blast
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>id\<^sub>c(\<Omega>) \<circ>\<^sub>c  \<t>,g \<circ>\<^sub>c i\<rangle>"
                by (typecheck_cfuncs, simp add: i_def id_left_unit2 id_right_unit2)
            also have "... = eval_func(A, \<Omega>) \<circ>\<^sub>c ((id\<^sub>c(\<Omega>) \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>)"
                using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
            also have "... = (eval_func(A, \<Omega>) \<circ>\<^sub>c (id\<^sub>c(\<Omega>) \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>"
              using comp_associative2 x_eq x_type by (typecheck_cfuncs, blast)
            ultimately show "(eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f g) \<circ>\<^sub>c x"
              by (simp add: x_eq)
          qed
        qed
        then show "eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f f \<circ>\<^sub>c id_1 = eval_func(A, \<Omega>) \<circ>\<^sub>c id\<^sub>c(\<Omega>) \<times>\<^sub>f g \<circ>\<^sub>c id_1"
          using  f_type g_type same_evals_equal by blast
        qed
      qed
    qed
    then have "monomorphism(\<phi>)"
      using injective_imp_monomorphism by auto
    have "surjective(\<phi>)"
      unfolding surjective_def
    proof(clarify)
      fix y 
      assume "y \<in>\<^sub>c codomain(\<phi>)" then have y_type[type_rule]: "y \<in>\<^sub>c A \<times>\<^sub>c A"
        using \<phi>_type cfunc_type_def by auto
      then obtain a1 a2 where y_def[type_rule]: "y = \<langle>a1,a2\<rangle> \<and> a1 \<in>\<^sub>c A \<and> a2 \<in>\<^sub>c A"
        using cart_prod_decomp by blast
      then have aua: "(a1 \<amalg> a2): \<one> \<Coprod> \<one> \<rightarrow> A"
        by (typecheck_cfuncs, simp add: y_def)     
    
      define f where f_def: "f = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>))\<^sup>\<sharp>"
      have lcp_type: "left_cart_proj(\<Omega>, \<one>) : \<Omega> \<times>\<^sub>c \<one> \<rightarrow> \<Omega>"
        by (rule left_cart_proj_type)
      have cb_lcp_type: "case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>) : \<Omega> \<times>\<^sub>c \<one> \<rightarrow> \<one> \<Coprod> \<one>"
        by (rule comp_type[OF lcp_type case_bool_type])
      have inner_type: "(a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>) : \<Omega> \<times>\<^sub>c \<one> \<rightarrow> A"
        by (rule comp_type[OF cb_lcp_type aua])
      have f_type[type_rule]: "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
        unfolding f_def by (rule transpose_func_type[OF inner_type])
      have beta_type: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<one>"
        by (rule terminal_func_type)
      have t_beta_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega>"
        by (rule comp_type[OF beta_type true_func_type])
      have f_beta_type: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega>"
        by (rule comp_type[OF beta_type false_func_type])
      have idAO_type: "id(A\<^bsup>\<Omega>\<^esup>) : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A\<^bsup>\<Omega>\<^esup>"
        by (rule id_type)
      have pair1_type: "\<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
        by (rule cfunc_prod_type[OF t_beta_type idAO_type])
      have pair2_type: "\<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
        by (rule cfunc_prod_type[OF f_beta_type idAO_type])
      have eval_type: "eval_func(A, \<Omega>) : \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup> \<rightarrow> A"
        by (rule eval_func_type)
      have beta_f_type: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f : \<one> \<rightarrow> \<one>"
        by (rule comp_type[OF f_type beta_type])
      have beta_f_eq: "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = id(\<one>)"
      proof -
        have "\<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<beta>\<^bsub>\<one>\<^esub>"
          by (rule terminal_func_unique[OF beta_f_type])
        also have "... = id(\<one>)"
          by (rule sym[OF terminal_func_unique[OF id_type]])
        finally show ?thesis.
      qed
      have t_beta_f_eq: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<t>"
      proof -
        have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<t> \<circ>\<^sub>c id(\<one>)"
          using beta_f_eq by simp
        also have "... = \<t>"
          by (rule id_right_unit2[OF true_func_type])
        finally show ?thesis.
      qed
      have f_beta_f_eq: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<f>"
      proof -
        have "\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f = \<f> \<circ>\<^sub>c id(\<one>)"
          using beta_f_eq by simp
        also have "... = \<f>"
          by (rule id_right_unit2[OF false_func_type])
        finally show ?thesis.
      qed
      have idAO_f_eq: "id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f = f"
        by (rule id_left_unit2[OF f_type])
      have a1_type: "a1 \<in>\<^sub>c A"
        using y_def by blast
      have a2_type: "a2 \<in>\<^sub>c A"
        using y_def by blast
      have t_id1_type: "\<langle>\<t>, id(\<one>)\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<one>"
        by (rule cfunc_prod_type[OF true_func_type id_type])
      have f_id1_type: "\<langle>\<f>, id(\<one>)\<rangle> : \<one> \<rightarrow> \<Omega> \<times>\<^sub>c \<one>"
        by (rule cfunc_prod_type[OF false_func_type id_type])
      have lcp_t_id1_eq: "left_cart_proj(\<Omega>, \<one>) \<circ>\<^sub>c \<langle>\<t>, id(\<one>)\<rangle> = \<t>"
        by (rule left_cart_proj_cfunc_prod[OF true_func_type id_type])
      have lcp_f_id1_eq: "left_cart_proj(\<Omega>, \<one>) \<circ>\<^sub>c \<langle>\<f>, id(\<one>)\<rangle> = \<f>"
        by (rule left_cart_proj_cfunc_prod[OF false_func_type id_type])
      have f_flat_eq: "f\<^sup>\<flat> = (a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>)"
      proof -
        have "f\<^sup>\<flat> = (((a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>))\<^sup>\<sharp>)\<^sup>\<flat>"
          by (simp add: f_def)
        also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>)"
          by (rule flat_cancels_sharp[OF inner_type])
        finally show ?thesis.
      qed
      have f_flat_eq2: "f\<^sup>\<flat> = eval_func(A, \<Omega>) \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f)"
        by (rule inv_transpose_func_def3[OF f_type])
      have eval_cross_f_eq: "eval_func(A, \<Omega>) \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f) = (a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>)"
        using f_flat_eq f_flat_eq2 by simp
      have cross_type: "id(\<Omega>) \<times>\<^sub>f f : \<Omega> \<times>\<^sub>c \<one> \<rightarrow> \<Omega> \<times>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
        by (rule cfunc_cross_prod_type[OF id_type f_type])
     have a1_is: "(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = a1"
     proof-
       have assoc1: "(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f =
                    eval_func(A, \<Omega>) \<circ>\<^sub>c (\<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f)"
         by (rule sym[OF comp_associative2[OF f_type pair1_type eval_type]])
       have prod_comp1: "\<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f = \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>"
         using cfunc_prod_comp[OF f_type t_beta_type idAO_type]
           comp_associative2[OF f_type beta_type true_func_type]
         by simp
       have cross_prod_eq: "\<langle>\<t>, f\<rangle> = (id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>, id(\<one>)\<rangle>"
       proof -
         have "(id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>, id(\<one>)\<rangle> = \<langle>id(\<Omega>) \<circ>\<^sub>c \<t>, f \<circ>\<^sub>c id(\<one>)\<rangle>"
           by (rule cfunc_cross_prod_comp_cfunc_prod[OF true_func_type id_type id_type f_type])
         also have "... = \<langle>\<t>, f\<rangle>"
           using id_left_unit2[OF true_func_type] id_right_unit2[OF f_type] by simp
         finally show ?thesis by (rule sym)
       qed
       have assoc2: "eval_func(A, \<Omega>) \<circ>\<^sub>c ((id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>, id(\<one>)\<rangle>) =
                     (eval_func(A, \<Omega>) \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<t>, id(\<one>)\<rangle>"
         by (rule comp_associative2[OF t_id1_type cross_type eval_type])
       have assoc3: "((a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>)) \<circ>\<^sub>c \<langle>\<t>, id(\<one>)\<rangle> =
                     (a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>) \<circ>\<^sub>c \<langle>\<t>, id(\<one>)\<rangle>"
         using comp_associative2[OF t_id1_type cb_lcp_type aua]
           comp_associative2[OF t_id1_type lcp_type case_bool_type]
         by simp
       have assoc4: "(a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<t> = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<t>"
         by (rule comp_associative2[OF true_func_type case_bool_type aua])
       have final_eq: "((a1 \<amalg> a2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<t> = a1"
         by (rule coprod_case_bool_true[OF a1_type a2_type])
       show ?thesis
         using assoc1 prod_comp1 t_beta_f_eq idAO_f_eq cross_prod_eq assoc2
           eval_cross_f_eq assoc3 lcp_t_id1_eq assoc4 final_eq
         by simp
     qed
     have a2_is: "(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = a2"
     proof-
       have assoc1: "(eval_func(A, \<Omega>) \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f =
                    eval_func(A, \<Omega>) \<circ>\<^sub>c (\<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f)"
         by (rule sym[OF comp_associative2[OF f_type pair2_type eval_type]])
       have prod_comp1: "\<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f = \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>"
         using cfunc_prod_comp[OF f_type f_beta_type idAO_type]
           comp_associative2[OF f_type beta_type false_func_type]
         by simp
       have cross_prod_eq: "\<langle>\<f>, f\<rangle> = (id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>, id(\<one>)\<rangle>"
       proof -
         have "(id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>, id(\<one>)\<rangle> = \<langle>id(\<Omega>) \<circ>\<^sub>c \<f>, f \<circ>\<^sub>c id(\<one>)\<rangle>"
           by (rule cfunc_cross_prod_comp_cfunc_prod[OF false_func_type id_type id_type f_type])
         also have "... = \<langle>\<f>, f\<rangle>"
           using id_left_unit2[OF false_func_type] id_right_unit2[OF f_type] by simp
         finally show ?thesis by (rule sym)
       qed
       have assoc2: "eval_func(A, \<Omega>) \<circ>\<^sub>c ((id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>, id(\<one>)\<rangle>) =
                     (eval_func(A, \<Omega>) \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<f>, id(\<one>)\<rangle>"
         by (rule comp_associative2[OF f_id1_type cross_type eval_type])
       have assoc3: "((a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>)) \<circ>\<^sub>c \<langle>\<f>, id(\<one>)\<rangle> =
                     (a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c left_cart_proj(\<Omega>, \<one>) \<circ>\<^sub>c \<langle>\<f>, id(\<one>)\<rangle>"
         using comp_associative2[OF f_id1_type cb_lcp_type aua]
           comp_associative2[OF f_id1_type lcp_type case_bool_type]
         by simp
       have assoc4: "(a1 \<amalg> a2) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<f> = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<f>"
         by (rule comp_associative2[OF false_func_type case_bool_type aua])
       have final_eq: "((a1 \<amalg> a2) \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<f> = a2"
         by (rule coprod_case_bool_false[OF a1_type a2_type])
       show ?thesis
         using assoc1 prod_comp1 f_beta_f_eq idAO_f_eq cross_prod_eq assoc2
           eval_cross_f_eq assoc3 lcp_f_id1_eq assoc4 final_eq
         by simp
     qed
     have "\<phi> \<circ>\<^sub>c f  = \<langle>a1,a2\<rangle>"
       unfolding \<phi>_def by (typecheck_cfuncs, simp add: a1_is a2_is cfunc_prod_comp)
     then show "\<exists>x. x \<in>\<^sub>c domain(\<phi>) \<and> \<phi> \<circ>\<^sub>c x = y"
       using \<phi>_type cfunc_type_def f_type y_def by auto
   qed
   then have "epimorphism(\<phi>)"
     by (simp add: surjective_is_epimorphism)
   then have "isomorphism(\<phi>)"
     by (simp add: \<open>monomorphism(\<phi>)\<close> epi_mon_is_iso)
   then show ?thesis
     using \<phi>_type is_isomorphic_def by blast
qed

end
