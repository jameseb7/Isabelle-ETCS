theory ETCS_Cartesian
  imports ETCS_Base
begin

section \<open>Axiom 2: Cartesian Products\<close>

axiomatization
  cart_prod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<times>\<^sub>c" 65) and
  left_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("\<langle>_,_\<rangle>")
where
  left_cart_proj_type[type_rule]: "left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> X" and
  right_cart_proj_type[type_rule]: "right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y" and
  cfunc_prod_type[type_rule]: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> \<langle>f,g\<rangle> : Z \<rightarrow> X \<times>\<^sub>c Y" and
  left_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> left_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = f" and
  right_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> right_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = g" and
  cfunc_prod_unique: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> h : Z \<rightarrow> X \<times>\<^sub>c Y \<Longrightarrow> 
    left_cart_proj X Y \<circ>\<^sub>c h = f \<Longrightarrow> right_cart_proj X Y \<circ>\<^sub>c h = g \<Longrightarrow> h = \<langle>f,g\<rangle>"
  

definition is_cart_prod :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" where
  "is_cart_prod W \<pi>\<^sub>0 \<pi>\<^sub>1 X Y \<longleftrightarrow> 
    (\<pi>\<^sub>0 : W \<rightarrow> X \<and> \<pi>\<^sub>1 : W \<rightarrow> Y \<and>
    (\<forall> f g Z. (f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y) \<longrightarrow> 
      (\<exists> h. h : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h = g \<and>
        (\<forall> h2. (h2 : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h))))"

abbreviation is_cart_prod_triple :: "cset \<times> cfunc \<times> cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" where
  "is_cart_prod_triple W\<pi> X Y \<equiv> is_cart_prod (fst W\<pi>) (fst (snd W\<pi>)) (snd (snd W\<pi>)) X Y"

lemma canonical_cart_prod_is_cart_prod:
 "is_cart_prod (X \<times>\<^sub>c Y) (left_cart_proj X Y) (right_cart_proj X Y) X Y"
  unfolding is_cart_prod_def
proof auto
  show "left_cart_proj X Y: X \<times>\<^sub>c Y \<rightarrow> X"
    using left_cart_proj_type by blast
  show "right_cart_proj X Y: X \<times>\<^sub>c Y \<rightarrow> Y"
    using right_cart_proj_type by blast
next 
  fix f g Z
  assume f_type: "f: Z \<rightarrow> X"
  assume g_type: "g: Z \<rightarrow> Y"
  show "\<exists>h. h : Z \<rightarrow> X \<times>\<^sub>c Y \<and>
           left_cart_proj X Y \<circ>\<^sub>c h = f \<and>
           right_cart_proj X Y \<circ>\<^sub>c h = g \<and>
           (\<forall>h2. h2 : Z \<rightarrow> X \<times>\<^sub>c Y \<and>
                 left_cart_proj X Y \<circ>\<^sub>c h2 = f \<and> right_cart_proj X Y \<circ>\<^sub>c h2 = g \<longrightarrow>
                 h2 = h)"
    apply (rule_tac x="\<langle>f,g\<rangle>" in exI)
    apply auto
       apply (simp add: cfunc_prod_type f_type g_type)
       using f_type g_type left_cart_proj_cfunc_prod apply blast
       using f_type g_type right_cart_proj_cfunc_prod apply blast
       using cfunc_prod_unique f_type g_type by blast
qed

(*Proposition 2.1.8*: Suppose that both (W,\<pi>_0,\<pi>_1) and (W',\<pi>'_0,\<pi>'_1) are 
Cartesian products of X and Y.  Then there is an isomorphism f:W\<rightarrow>W' such that 
\<pi>'_0f = \<pi>_0 and \<pi>'_1f = \<pi>_1.*)
lemma cart_prods_isomorphic:
  assumes W_cart_prod:  "is_cart_prod_triple (W, \<pi>\<^sub>0, \<pi>\<^sub>1) X Y"
  assumes W'_cart_prod: "is_cart_prod_triple (W', \<pi>'\<^sub>0, \<pi>'\<^sub>1) X Y"
  shows "\<exists> f. f : W \<rightarrow> W' \<and> isomorphism f \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
proof -
  obtain f where f_def: "f : W \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
    using W'_cart_prod W_cart_prod unfolding is_cart_prod_def by (metis fstI sndI)

  obtain g where g_def: "g : W' \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c g = \<pi>'\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c g = \<pi>'\<^sub>1"
      using W'_cart_prod W_cart_prod unfolding is_cart_prod_def by (metis fstI sndI)

  have fg0: "\<pi>'\<^sub>0 \<circ>\<^sub>c (f \<circ>\<^sub>c g) = \<pi>'\<^sub>0"
    using W'_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto
  have fg1: "\<pi>'\<^sub>1 \<circ>\<^sub>c (f \<circ>\<^sub>c g) = \<pi>'\<^sub>1"
    using W'_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto

  obtain idW' where "idW' : W' \<rightarrow> W' \<and> (\<forall> h2. (h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1) \<longrightarrow> h2 = idW')"
    using W'_cart_prod unfolding is_cart_prod_def by (metis fst_conv snd_conv)
  then have fg: "f \<circ>\<^sub>c g = id W'"
  proof auto
    assume idW'_unique: "\<forall>h2. h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1 \<longrightarrow> h2 = idW'"
    have 1: "f \<circ>\<^sub>c g = idW'"
      using idW'_unique apply (erule_tac x="f \<circ>\<^sub>c g" in allE, auto)
      using cfunc_type_def codomain_comp domain_comp f_def fg0 fg1 g_def by auto
    have 2: "id W' = idW'"
      using idW'_unique apply (erule_tac x="f \<circ>\<^sub>c g" in allE, auto)
      using W'_cart_prod id_right_unit2 id_type is_cart_prod_def by auto
    from 1 2 show "f \<circ>\<^sub>c g = id W'"
      by auto
  qed

  have gf0: "\<pi>\<^sub>0 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>0"
    using W_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto
  have gf1: "\<pi>\<^sub>1 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>1"
    using W_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto

  obtain idW where "idW : W \<rightarrow> W \<and> (\<forall> h2. (h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1) \<longrightarrow> h2 = idW)"
    using W_cart_prod unfolding is_cart_prod_def by (metis fst_conv snd_conv)
  then have gf: "g \<circ>\<^sub>c f = id W"
  proof auto
    assume idW_unique: "\<forall>h2. h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1 \<longrightarrow> h2 = idW"
    have 1: "g \<circ>\<^sub>c f = idW"
      using idW_unique apply (erule_tac x="g \<circ>\<^sub>c f" in allE, auto)
      using cfunc_type_def codomain_comp domain_comp f_def gf0 gf1 g_def by auto
    have 2: "id W = idW"
      using idW_unique apply (erule_tac x="id W" in allE, auto)
      using W_cart_prod id_right_unit2 id_type is_cart_prod_def by auto
    from 1 2 show "g \<circ>\<^sub>c f = id W"
      by auto
  qed

  have f_iso: "isomorphism f"
    unfolding isomorphism_def apply (rule_tac x=g in exI, auto)
    using cfunc_type_def f_def g_def fg gf by auto

  from f_iso f_def show "\<exists>f. f : W \<rightarrow> W' \<and> isomorphism f \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
    by auto
qed



(*Product commutes*)

lemma product_commutes:
  "A \<times>\<^sub>c B \<cong> B \<times>\<^sub>c A"
proof -
  have qprod_type: "\<langle>right_cart_proj B A, left_cart_proj B A\<rangle> : B \<times>\<^sub>c A \<rightarrow> A \<times>\<^sub>c B"
    by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)
  have pprod_type: "\<langle>right_cart_proj A B, left_cart_proj A B\<rangle> : A \<times>\<^sub>c B \<rightarrow> B \<times>\<^sub>c A"
    by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)
  have id_AB: "\<langle>right_cart_proj B A, left_cart_proj B A\<rangle> \<circ>\<^sub>c \<langle>right_cart_proj A B, left_cart_proj A B\<rangle> = id(A \<times>\<^sub>c B)"
    by (smt cfunc_prod_unique cfunc_type_def comp_associative comp_type id_right_unit id_type left_cart_proj_cfunc_prod left_cart_proj_type pprod_type qprod_type right_cart_proj_cfunc_prod right_cart_proj_type)
  have fact1: "\<langle>right_cart_proj A B, left_cart_proj A B\<rangle> \<circ>\<^sub>c \<langle>right_cart_proj B A, left_cart_proj B A\<rangle>: B \<times>\<^sub>c A \<rightarrow>  B \<times>\<^sub>c A"
    by (meson comp_type pprod_type qprod_type)
  have id_BA: "\<langle>right_cart_proj A B, left_cart_proj A B\<rangle> \<circ>\<^sub>c \<langle>right_cart_proj B A, left_cart_proj B A\<rangle> = id(B \<times>\<^sub>c A)"
    by (smt cfunc_prod_unique comp_associative2 comp_type id_right_unit2 id_type left_cart_proj_cfunc_prod left_cart_proj_type pprod_type qprod_type right_cart_proj_cfunc_prod right_cart_proj_type)
    
  show "A \<times>\<^sub>c B \<cong> B \<times>\<^sub>c A"
    by (metis cfunc_type_def id_AB id_BA is_isomorphic_def isomorphism_def pprod_type qprod_type)
  qed 




(*Definition 2.1.9*)
definition diagonal :: "cset \<Rightarrow> cfunc" where
  "diagonal(X) = \<langle>id(X),id(X)\<rangle>"

lemma diagonal_type[type_rule]:
  "diagonal X : X \<rightarrow> X \<times>\<^sub>c X"
  unfolding diagonal_def by (simp add: cfunc_prod_type id_type)

(*Note at the end of Definition 2.1.9*)
lemma diag_mono:
"monomorphism(diagonal(X))"
proof - 
  have f1: "left_cart_proj X X \<circ>\<^sub>c diagonal X = id(X)"
    by (metis diagonal_def id_type left_cart_proj_cfunc_prod)
  show "monomorphism(diagonal(X))"
    by (metis cfunc_type_def comp_monic_imp_monic diagonal_type f1 id_isomorphism iso_imp_epi_and_monic left_cart_proj_type)
qed



(*Definition 2.1.10*)
definition cfunc_cross_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<times>\<^sub>f" 55) where
  "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj (domain f) (domain g), g \<circ>\<^sub>c right_cart_proj (domain f) (domain g)\<rangle>"

lemma cfunc_cross_prod_type[type_rule]:
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> f \<times>\<^sub>f g : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z"
  unfolding cfunc_cross_prod_def
  using cfunc_prod_type cfunc_type_def comp_type left_cart_proj_type right_cart_proj_type by auto

lemma left_cart_proj_cfunc_cross_prod:
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> left_cart_proj Y Z \<circ>\<^sub>c f \<times>\<^sub>f g = f \<circ>\<^sub>c left_cart_proj W X"
  unfolding cfunc_cross_prod_def
  using cfunc_type_def comp_type left_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_type by auto

lemma right_cart_proj_cfunc_cross_prod:
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> right_cart_proj Y Z \<circ>\<^sub>c f \<times>\<^sub>f g = g \<circ>\<^sub>c right_cart_proj W X"
  unfolding cfunc_cross_prod_def
  using cfunc_type_def comp_type right_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_type by auto

lemma cfunc_cross_prod_unique: "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> h : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z \<Longrightarrow>
    left_cart_proj Y Z \<circ>\<^sub>c h = f \<circ>\<^sub>c left_cart_proj W X \<Longrightarrow>
    right_cart_proj Y Z \<circ>\<^sub>c h = g \<circ>\<^sub>c right_cart_proj W X \<Longrightarrow> h = f \<times>\<^sub>f g"
  unfolding cfunc_cross_prod_def
  using cfunc_prod_unique cfunc_type_def comp_type left_cart_proj_type right_cart_proj_type by auto

(*Proposition 2.1.11*)
lemma identity_distributes_across_composition:
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C"
  shows "id(X) \<times>\<^sub>f (g  \<circ>\<^sub>c f) = (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)"
proof -
  from cfunc_cross_prod_unique
  have uniqueness: "\<forall>h. h : X \<times>\<^sub>c A \<rightarrow> X \<times>\<^sub>c C \<and>
    left_cart_proj X C \<circ>\<^sub>c h = id\<^sub>c X \<circ>\<^sub>c left_cart_proj X A \<and>
    right_cart_proj X C \<circ>\<^sub>c h = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj X A \<longrightarrow>
    h = id\<^sub>c X \<times>\<^sub>f (g \<circ>\<^sub>c f)"
    by (meson comp_type f_type g_type id_type)

  have left_eq: "left_cart_proj X C \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) = id\<^sub>c X \<circ>\<^sub>c left_cart_proj X A"
    using assms apply (typecheck_cfuncs)
    thm type_rule
    by (smt comp_associative2 id_left_unit2 left_cart_proj_cfunc_cross_prod left_cart_proj_type)
  have right_eq: "right_cart_proj X C \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj X A"
    using assms apply (typecheck_cfuncs)
    by (smt comp_associative2 right_cart_proj_cfunc_cross_prod right_cart_proj_type)

  show "id\<^sub>c X \<times>\<^sub>f g \<circ>\<^sub>c f = (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f"
    using assms left_eq right_eq uniqueness by (typecheck_cfuncs, auto)
qed

lemma cfunc_cross_prod_comp_cfunc_prod:
  assumes a_type: "a : A \<rightarrow> W" and b_type: "b : A \<rightarrow> X"
  assumes f_type: "f : W \<rightarrow> Y" and g_type: "g : X \<rightarrow> Z"
  shows "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = \<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle>"
proof -
  from cfunc_prod_unique have uniqueness:
    "\<forall>h. h : A \<rightarrow> Y \<times>\<^sub>c Z \<and> left_cart_proj Y Z \<circ>\<^sub>c h = f \<circ>\<^sub>c a \<and> right_cart_proj Y Z \<circ>\<^sub>c h = g \<circ>\<^sub>c b \<longrightarrow> 
      h = \<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle>"
    using assms comp_type by blast

  have "left_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c left_cart_proj W X \<circ>\<^sub>c \<langle>a, b\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
  then have left_eq: "left_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c a"
    using a_type b_type left_cart_proj_cfunc_prod by auto
  
  have "right_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c right_cart_proj W X \<circ>\<^sub>c \<langle>a, b\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
  then have right_eq: "right_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c b"
    using a_type b_type right_cart_proj_cfunc_prod by auto

  show "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a,b\<rangle> = \<langle>f \<circ>\<^sub>c a,g \<circ>\<^sub>c b\<rangle>"
    using uniqueness left_eq right_eq assms apply (erule_tac x="f \<times>\<^sub>f g \<circ>\<^sub>c \<langle>a,b\<rangle>" in allE)
    by (meson cfunc_cross_prod_type cfunc_prod_type comp_type uniqueness)
qed

lemma cfunc_prod_comp:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes a_type: "a : Y \<rightarrow> A" and b_type: "b : Y \<rightarrow> B"
  shows "\<langle>a, b\<rangle> \<circ>\<^sub>c f = \<langle>a \<circ>\<^sub>c f, b \<circ>\<^sub>c f\<rangle>"
proof -
  
  have same_type: "\<langle>a, b\<rangle> \<circ>\<^sub>c f : X \<rightarrow> A \<times>\<^sub>c B"
    using a_type b_type cfunc_prod_type comp_type f_type by auto
  have same_left_proj: "left_cart_proj A B \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = a \<circ>\<^sub>c f"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_prod)
  have same_right_proj: "right_cart_proj A B \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = b \<circ>\<^sub>c f"
    using assms comp_associative2 right_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)

  show "\<langle>a,b\<rangle> \<circ>\<^sub>c f = \<langle>a \<circ>\<^sub>c f, b \<circ>\<^sub>c f\<rangle>"
    using a_type b_type cfunc_prod_unique comp_type f_type same_left_proj same_right_proj same_type by blast
qed

(*Exercise 2.1.12: Product of identities is identity of product*)
lemma id_cross_prod: "id(X) \<times>\<^sub>f id(Y) = id(X \<times>\<^sub>c Y)"
  unfolding cfunc_cross_prod_def 
  by (metis cfunc_prod_unique cfunc_type_def id_left_unit id_right_unit id_type left_cart_proj_type right_cart_proj_type)

(*Exercise 2.1.14: diagonal_commutes_cross_product*) 
lemma cfunc_cross_prod_comp_diagonal:
  assumes "f: X \<rightarrow> Y" 
  shows "(f \<times>\<^sub>f f) \<circ>\<^sub>c diagonal(X) = diagonal(Y) \<circ>\<^sub>c f"
  unfolding diagonal_def
proof -
  have "(f \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>id\<^sub>c X, id\<^sub>c X\<rangle> = \<langle>f \<circ>\<^sub>c id\<^sub>c X, f \<circ>\<^sub>c id\<^sub>c X\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_type by blast
  also have "... = \<langle>f, f\<rangle>"
    using assms cfunc_type_def id_right_unit by auto
  also have "... = \<langle>id\<^sub>c Y \<circ>\<^sub>c f, id\<^sub>c Y \<circ>\<^sub>c f\<rangle>"
    using assms cfunc_type_def id_left_unit by auto
  also have "... = \<langle>id\<^sub>c Y, id\<^sub>c Y\<rangle> \<circ>\<^sub>c f"
    using assms cfunc_prod_comp id_type by fastforce
  then show "(f \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>id\<^sub>c X,id\<^sub>c X\<rangle> = \<langle>id\<^sub>c Y,id\<^sub>c Y\<rangle> \<circ>\<^sub>c f"
    using calculation by auto
qed

lemma cfunc_cross_prod_comp_cfunc_cross_prod:
  assumes "a : A \<rightarrow> X" "b : B \<rightarrow> Y" "x : X \<rightarrow> Z" "y : Y \<rightarrow> W"
  shows "(x \<times>\<^sub>f y) \<circ>\<^sub>c (a \<times>\<^sub>f b) = (x \<circ>\<^sub>c a) \<times>\<^sub>f (y \<circ>\<^sub>c b)"
proof -
  have "(x \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c left_cart_proj A B , b \<circ>\<^sub>c right_cart_proj A B\<rangle>
      = \<langle>x \<circ>\<^sub>c a \<circ>\<^sub>c left_cart_proj A B, y \<circ>\<^sub>c b \<circ>\<^sub>c right_cart_proj A B\<rangle>"
    by (meson assms cfunc_cross_prod_comp_cfunc_prod comp_type left_cart_proj_type right_cart_proj_type)
  then show "(x \<times>\<^sub>f y) \<circ>\<^sub>c a \<times>\<^sub>f b = (x \<circ>\<^sub>c a) \<times>\<^sub>f y \<circ>\<^sub>c b"
    using assms cfunc_type_def cfunc_cross_prod_def comp_associative2 left_cart_proj_type right_cart_proj_type
    by (typecheck_cfuncs, auto)
qed

lemma cart_prod_eq:
  assumes "a : Z \<rightarrow> X \<times>\<^sub>c Y" "b : Z \<rightarrow>  X \<times>\<^sub>c Y"
  shows "a = b \<longleftrightarrow> 
    (left_cart_proj X Y \<circ>\<^sub>c a = left_cart_proj X Y \<circ>\<^sub>c b 
      \<and> right_cart_proj X Y \<circ>\<^sub>c a = right_cart_proj X Y \<circ>\<^sub>c b)"
  by (metis (full_types) assms cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type)

lemma cart_prod_eq2:
  assumes "a : Z \<rightarrow> X" "b : Z \<rightarrow> Y" "c : Z \<rightarrow>  X" "d : Z \<rightarrow>  Y"
  shows "\<langle>a, b\<rangle> = \<langle>c,d\<rangle> \<longleftrightarrow> (a = c \<and> b = d)"
  by (metis assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)

lemma cart_prod_decomp:
  assumes "a : A \<rightarrow> X \<times>\<^sub>c Y"
  shows "\<exists> x y. a = \<langle>x, y\<rangle> \<and> x : A \<rightarrow> X \<and> y : A \<rightarrow> Y"
proof (rule_tac x="left_cart_proj X Y \<circ>\<^sub>c a" in exI, rule_tac x="right_cart_proj X Y \<circ>\<^sub>c a" in exI, auto)
  show "a = \<langle>left_cart_proj X Y \<circ>\<^sub>c a,right_cart_proj X Y \<circ>\<^sub>c a\<rangle>"
    using assms cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type by blast
  show "left_cart_proj X Y \<circ>\<^sub>c a : A \<rightarrow>  X"
    using assms left_cart_proj_type comp_type by auto
  show "right_cart_proj X Y \<circ>\<^sub>c a : A \<rightarrow> Y"
    using assms right_cart_proj_type comp_type by auto
qed

lemma cfunc_cross_prod_mono:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes f_mono: "monomorphism f" and g_mono: "monomorphism g"
  shows "monomorphism (f \<times>\<^sub>f g)"
  using type_assms
proof (typecheck_cfuncs, unfold monomorphism_def3, auto)
  fix x y A
  assume x_type: "x : A \<rightarrow> X \<times>\<^sub>c Z"
  assume y_type: "y : A \<rightarrow> X \<times>\<^sub>c Z"

  obtain x1 x2 where x_expand: "x = \<langle>x1, x2\<rangle>" and x1_x2_type: "x1 : A \<rightarrow> X" "x2 : A \<rightarrow> Z"
    using cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type x_type by blast
  obtain y1 y2 where y_expand: "y = \<langle>y1, y2\<rangle>" and y1_y2_type: "y1 : A \<rightarrow> X" "y2 : A \<rightarrow> Z"
    using cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type y_type by blast

  assume "(f \<times>\<^sub>f g) \<circ>\<^sub>c x = (f \<times>\<^sub>f g) \<circ>\<^sub>c y"
  then have "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x1, x2\<rangle> = (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>y1, y2\<rangle>"
    using x_expand y_expand by blast
  then have "\<langle>f \<circ>\<^sub>c x1, g \<circ>\<^sub>c x2\<rangle> = \<langle>f \<circ>\<^sub>c y1, g \<circ>\<^sub>c y2\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod type_assms x1_x2_type y1_y2_type by auto
  then have "f \<circ>\<^sub>c x1 = f \<circ>\<^sub>c y1 \<and> g \<circ>\<^sub>c x2 = g \<circ>\<^sub>c y2"
    by (meson cart_prod_eq2 comp_type type_assms x1_x2_type y1_y2_type)
  then have "x1 = y1 \<and> x2 = y2"
    using cfunc_type_def f_mono g_mono monomorphism_def type_assms x1_x2_type y1_y2_type by auto
  then have "\<langle>x1, x2\<rangle> = \<langle>y1, y2\<rangle>"
    by blast
  then show "x = y"
    by (simp add: x_expand y_expand)
qed




  



subsection \<open>Useful Cartesian product permuting functions\<close>

subsubsection \<open>Swapping a Cartesian product\<close>

definition swap :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "swap X Y = \<langle>right_cart_proj X Y, left_cart_proj X Y\<rangle>"

lemma swap_type[type_rule]: "swap X Y : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c X"
  unfolding swap_def by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)

lemma swap_ap:
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y"
  shows "swap X Y \<circ>\<^sub>c \<langle>x, y\<rangle> = \<langle>y, x\<rangle>"
proof -
  have "swap X Y \<circ>\<^sub>c \<langle>x, y\<rangle> = \<langle>right_cart_proj X Y,left_cart_proj X Y\<rangle> \<circ>\<^sub>c \<langle>x,y\<rangle>"
    unfolding swap_def by auto
  also have "... = \<langle>right_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>, left_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
    by (meson assms cfunc_prod_comp cfunc_prod_type left_cart_proj_type right_cart_proj_type)
  also have "... = \<langle>y, x\<rangle>"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

lemma swap_cross_prod:
  assumes "x : A \<rightarrow> X" "y : B \<rightarrow> Y"
  shows "swap X Y \<circ>\<^sub>c (x \<times>\<^sub>f y) = (y \<times>\<^sub>f x) \<circ>\<^sub>c swap A B"
proof -
  have "swap X Y \<circ>\<^sub>c (x \<times>\<^sub>f y) = swap X Y \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj A B, y \<circ>\<^sub>c right_cart_proj A B\<rangle>"
    using assms unfolding cfunc_cross_prod_def cfunc_type_def by auto
  also have "... = \<langle>y \<circ>\<^sub>c right_cart_proj A B, x \<circ>\<^sub>c left_cart_proj A B\<rangle>"
    by (meson assms comp_type left_cart_proj_type right_cart_proj_type swap_ap)
  also have "... = (y \<times>\<^sub>f x) \<circ>\<^sub>c \<langle>right_cart_proj A B, left_cart_proj A B\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = (y \<times>\<^sub>f x) \<circ>\<^sub>c swap A B"
    unfolding swap_def by auto
  then show ?thesis
    using calculation by auto
qed

lemma swap_idempotent:
  "swap Y X \<circ>\<^sub>c swap X Y = id (X \<times>\<^sub>c Y)"
  by (metis swap_def cfunc_prod_unique id_right_unit2 id_type left_cart_proj_type
      right_cart_proj_type swap_ap)

subsubsection \<open>Permuting a Cartesian product to associate to the right\<close>

definition associate_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_right X Y Z =
    \<langle>
      left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, 
      \<langle>
        right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z,
        right_cart_proj (X \<times>\<^sub>c Y) Z
      \<rangle>
    \<rangle>"

lemma associate_right_type[type_rule]: "associate_right X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  unfolding associate_right_def by (meson cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type)

lemma associate_right_ap:
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "associate_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>x, \<langle>y, z\<rangle>\<rangle>"
  (is "?lhs = ?rhs")
proof -
  have xy_z_type: "\<langle>\<langle>x,y\<rangle>,z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
    by (simp add: assms cfunc_prod_type)
  have ll_type: "left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X"
    using comp_type left_cart_proj_type by blast
  have rl_r_type:
    "\<langle>right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z,right_cart_proj (X \<times>\<^sub>c Y) Z\<rangle>
      : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c Z"
    using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast
  

  have "?lhs = \<langle>
    left_cart_proj X Y \<circ>\<^sub>c  left_cart_proj (X \<times>\<^sub>c Y) Z,
      \<langle>
        right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z,
        right_cart_proj (X \<times>\<^sub>c Y) Z
      \<rangle>
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>"
    unfolding associate_right_def by auto
  also have "... = \<langle>
    (left_cart_proj X Y \<circ>\<^sub>c  left_cart_proj (X \<times>\<^sub>c Y) Z) \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>,
      \<langle>
        (right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z),
        right_cart_proj (X \<times>\<^sub>c Y) Z
      \<rangle> \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>
    \<rangle>"
    using cfunc_prod_comp ll_type rl_r_type xy_z_type by blast
  also have "... = \<langle>
    (left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z) \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>,
      \<langle>
        (right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z) \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>,
        right_cart_proj (X \<times>\<^sub>c Y) Z \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>
      \<rangle>
    \<rangle>"
    by (smt cfunc_prod_comp comp_type left_cart_proj_type right_cart_proj_type xy_z_type)
  also have "... = \<langle>left_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>, \<langle>right_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>, z\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = ?rhs"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

subsubsection \<open>Permuting a Cartesian product to associate to the left\<close>

definition associate_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_left X Y Z =
    \<langle>
      \<langle>
        left_cart_proj X (Y \<times>\<^sub>c Z),
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
      \<rangle>,
      right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
    \<rangle>"

lemma associate_left_type[type_rule]: "associate_left X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
  unfolding associate_left_def
  by (meson cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type)

lemma associate_left_ap:
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "associate_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>\<langle>x, y\<rangle>, z\<rangle>"
  (is "?lhs = ?rhs")
proof -
  have x_yz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
    by (simp add: assms cfunc_prod_type)
  have yz_type: "\<langle>y, z\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z"
    by (simp add: assms cfunc_prod_type)
  have rr_type: "right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Z"
    using comp_type right_cart_proj_type by blast
  have lr_type: "left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y"
    using comp_type left_cart_proj_type right_cart_proj_type by blast
  have l_ll_type:
    "\<langle>left_cart_proj X (Y \<times>\<^sub>c Z), left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle>
      : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Y"
    using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

  have "?lhs = \<langle>
      \<langle>
        left_cart_proj X (Y \<times>\<^sub>c Z),
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
      \<rangle>,
      right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
    \<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding associate_left_def by auto
  also have "... = \<langle>
      \<langle>
        left_cart_proj X (Y \<times>\<^sub>c Z),
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
      \<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
      right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)  \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>
      \<langle>
        left_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
      \<rangle> ,
      right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)  \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>\<langle>x, left_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>, right_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>"
    using assms(1) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod yz_type by auto
  also have "... = ?rhs"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

lemma product_associates:
  "A \<times>\<^sub>c (B \<times>\<^sub>c C)  \<cong> (A \<times>\<^sub>c B) \<times>\<^sub>c C"
proof-
  have right_left: "(associate_right A B C) \<circ>\<^sub>c (associate_left A B C) = id (A \<times>\<^sub>c (B \<times>\<^sub>c C))"
    by (smt associate_left_def associate_right_ap cfunc_cross_prod_def cfunc_prod_unique comp_type id_cross_prod id_domain id_left_unit2 left_cart_proj_type right_cart_proj_type)
  have left_right: "(associate_left A B C) \<circ>\<^sub>c (associate_right A B C) = id ((A \<times>\<^sub>c B) \<times>\<^sub>c C)"
    by (smt associate_left_ap associate_right_def cfunc_cross_prod_def cfunc_prod_unique comp_type id_cross_prod id_domain id_left_unit2 left_cart_proj_type right_cart_proj_type)
  show ?thesis
    by (metis associate_left_type associate_right_type cfunc_type_def is_isomorphic_def isomorphism_def left_right right_left) 
qed






subsubsection \<open>Distributing over a Cartesian product from the right\<close>

definition distribute_right_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right_left X Y Z = 
    \<langle>left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, right_cart_proj (X \<times>\<^sub>c Y) Z\<rangle>"

lemma distribute_right_left_type[type_rule]:
  "distribute_right_left X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Z"
  unfolding distribute_right_left_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_right_left_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_right_left X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>x, z\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have xyz_type: "\<langle>\<langle>x, y\<rangle>, z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
    by (simp add: assms cfunc_prod_type)
  have ll_type: "left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X"
    using comp_type left_cart_proj_type by blast
  have "?lhs = 
    \<langle>left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, right_cart_proj (X \<times>\<^sub>c Y) Z\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    unfolding distribute_right_left_def by simp
  also have "... = \<langle>left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>, 
      right_cart_proj (X \<times>\<^sub>c Y) Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>"
    using assms cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = \<langle>left_cart_proj X Y \<circ>\<^sub>c \<langle>x, y\<rangle>, z\<rangle>"
    by (metis assms cfunc_prod_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = ?rhs"
    using assms(1) assms(2) left_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

definition distribute_right_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right_right X Y Z = 
    \<langle>right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, right_cart_proj (X \<times>\<^sub>c Y) Z\<rangle>"

lemma distribute_right_right_type[type_rule]:
  "distribute_right_right X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c Z"
  unfolding distribute_right_right_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_right_right_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_right_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>y, z\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have xyz_type: "\<langle>\<langle>x, y\<rangle>, z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
    by (simp add: assms cfunc_prod_type)
  have rl_type: "right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y"
    using comp_type right_cart_proj_type left_cart_proj_type by blast
  have "?lhs = 
    \<langle>right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, right_cart_proj (X \<times>\<^sub>c Y) Z\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    unfolding distribute_right_right_def by simp
  also have "... = \<langle>right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>, 
      right_cart_proj (X \<times>\<^sub>c Y) Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>right_cart_proj X Y \<circ>\<^sub>c \<langle>x, y\<rangle>, z\<rangle>"
    by (metis assms cfunc_prod_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = ?rhs"
    using assms(1) assms(2) right_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

definition distribute_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right X Y Z = \<langle>distribute_right_left X Y Z, distribute_right_right X Y Z\<rangle>"

lemma distribute_right_type[type_rule]:
  "distribute_right X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  unfolding distribute_right_def
  by (simp add: cfunc_prod_type distribute_right_left_type distribute_right_right_type)

lemma distribute_right_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>\<langle>x, z\<rangle>, \<langle>y, z\<rangle>\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have xyz_type: "\<langle>\<langle>x, y\<rangle>, z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
    by (simp add: assms cfunc_prod_type)
  have "?lhs = \<langle>distribute_right_left X Y Z, distribute_right_right X Y Z\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    unfolding distribute_right_def by simp
  also have "... = \<langle>distribute_right_left X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>, distribute_right_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>"
    using cfunc_prod_comp distribute_right_left_type distribute_right_right_type xyz_type by blast
  also have "... = ?rhs"
    using assms distribute_right_left_ap distribute_right_right_ap by auto
  then show ?thesis
    using calculation by auto
qed

lemma distribute_right_mono:
  "monomorphism (distribute_right X Y Z)"
proof (typecheck_cfuncs, unfold monomorphism_def3, auto)
  fix g h A
  assume g_type: "g : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
  then obtain g1 g2 g3 where g_expand: "g = \<langle>\<langle>g1, g2\<rangle>, g3\<rangle>"
      and g1_g2_g3_types: "g1 : A \<rightarrow> X" "g2 : A \<rightarrow> Y" "g3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 
  assume h_type: "h : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
  then obtain h1 h2 h3 where h_expand: "h = \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>"
      and h1_h2_h3_types: "h1 : A \<rightarrow> X" "h2 : A \<rightarrow> Y" "h3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 

  assume "distribute_right X Y Z \<circ>\<^sub>c g = distribute_right X Y Z \<circ>\<^sub>c h"
  then have "distribute_right X Y Z \<circ>\<^sub>c \<langle>\<langle>g1, g2\<rangle>, g3\<rangle> = distribute_right X Y Z \<circ>\<^sub>c \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>"
    using g_expand h_expand by auto
  then have "\<langle>\<langle>g1, g3\<rangle>, \<langle>g2, g3\<rangle>\<rangle> = \<langle>\<langle>h1, h3\<rangle>, \<langle>h2, h3\<rangle>\<rangle>"
    using distribute_right_ap g1_g2_g3_types h1_h2_h3_types by auto
  then have "\<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle> \<and> \<langle>g2, g3\<rangle> = \<langle>h2, h3\<rangle>"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by (typecheck_cfuncs, auto)
  then have "g1 = h1 \<and> g2 = h2 \<and> g3 = h3"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by auto
  then have "\<langle>\<langle>g1, g2\<rangle>, g3\<rangle> = \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>"
    by simp
  then show "g = h"
    by (simp add: g_expand h_expand)
qed


subsubsection \<open>Distributing over a Cartesian product from the left\<close>

definition distribute_left_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left_left X Y Z = 
    \<langle>left_cart_proj X (Y \<times>\<^sub>c Z), left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle>"

lemma distribute_left_left_type[type_rule]:
  "distribute_left_left X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Y"
  unfolding distribute_left_left_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_left_left_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_left_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>x, y\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have xyz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
    by (simp add: assms cfunc_prod_type)
  have ll_type: "left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y"
    using comp_type left_cart_proj_type right_cart_proj_type by blast
  have "?lhs = 
    \<langle>left_cart_proj X (Y \<times>\<^sub>c Z), left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding distribute_left_left_def by simp
  also have "... = \<langle>left_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
    left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>x, left_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>"
    by (metis assms cfunc_prod_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = ?rhs"
    using assms(2) assms(3) left_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

definition distribute_left_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left_right X Y Z = 
    \<langle>left_cart_proj X (Y \<times>\<^sub>c Z), right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle>"

lemma distribute_left_right_type[type_rule]:
  "distribute_left_right X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Z"
  unfolding distribute_left_right_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_left_right_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_left_right X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>x, z\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have xyz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
    by (simp add: assms cfunc_prod_type)
  have rl_type: "right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Z"
    using comp_type left_cart_proj_type right_cart_proj_type by blast
  have "?lhs = 
    \<langle>left_cart_proj X (Y \<times>\<^sub>c Z), right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding distribute_left_right_def by simp
  also have "... = \<langle>left_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
    right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>x, right_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>"
    by (metis assms cfunc_prod_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = ?rhs"
    using assms(2) assms(3) right_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

definition distribute_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left X Y Z = \<langle>distribute_left_left X Y Z, distribute_left_right X Y Z\<rangle>"

lemma distribute_left_type[type_rule]:
  "distribute_left X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
  unfolding distribute_left_def
  by (simp add: cfunc_prod_type distribute_left_left_type distribute_left_right_type)

lemma distribute_left_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>\<langle>x, y\<rangle>, \<langle>x, z\<rangle>\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have xyz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
    by (simp add: assms cfunc_prod_type)
  have "?lhs = \<langle>distribute_left_left X Y Z, distribute_left_right X Y Z\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding distribute_left_def by simp
  also have "... = \<langle>distribute_left_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>, distribute_left_right X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp distribute_left_left_type distribute_left_right_type xyz_type by blast
  also have "... = ?rhs"
    using assms distribute_left_left_ap distribute_left_right_ap by auto
  then show ?thesis
    using calculation by auto
qed

lemma distribute_left_mono:
  "monomorphism (distribute_left X Y Z)"
proof (typecheck_cfuncs, unfold monomorphism_def3, auto)
  fix g h A
  assume g_type: "g : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  then obtain g1 g2 g3 where g_expand: "g = \<langle>g1, \<langle>g2, g3\<rangle>\<rangle>"
      and g1_g2_g3_types: "g1 : A \<rightarrow> X" "g2 : A \<rightarrow> Y" "g3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 
  assume h_type: "h : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  then obtain h1 h2 h3 where h_expand: "h = \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>"
      and h1_h2_h3_types: "h1 : A \<rightarrow> X" "h2 : A \<rightarrow> Y" "h3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 

  assume "distribute_left X Y Z \<circ>\<^sub>c g = distribute_left X Y Z \<circ>\<^sub>c h"
  then have "distribute_left X Y Z \<circ>\<^sub>c \<langle>g1, \<langle>g2, g3\<rangle>\<rangle> = distribute_left X Y Z \<circ>\<^sub>c \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>"
    using g_expand h_expand by auto
  then have "\<langle>\<langle>g1, g2\<rangle>, \<langle>g1, g3\<rangle>\<rangle> = \<langle>\<langle>h1, h2\<rangle>, \<langle>h1, h3\<rangle>\<rangle>"
    using distribute_left_ap g1_g2_g3_types h1_h2_h3_types by auto
  then have "\<langle>g1, g2\<rangle> = \<langle>h1, h2\<rangle> \<and> \<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle>"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by (typecheck_cfuncs, auto)
  then have "g1 = h1 \<and> g2 = h2 \<and> g3 = h3"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by auto
  then have "\<langle>g1, \<langle>g2, g3\<rangle>\<rangle> = \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>"
    by simp
  then show "g = h"
    by (simp add: g_expand h_expand)
qed

subsubsection \<open>Selecting pairs from a pair of pairs\<close>

definition outers :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "outers A B C D = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma outers_type[type_rule]: "outers A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (A \<times>\<^sub>c D)"
  unfolding outers_def by typecheck_cfuncs

lemma outers_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "outers A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> = \<langle>a,d\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle>"
    unfolding outers_def by auto
  also have "... = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>left_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, right_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>a, d\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed

definition inners :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "inners A B C D = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma inners_type[type_rule]: "inners A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (B \<times>\<^sub>c C)"
  unfolding inners_def by typecheck_cfuncs
    
lemma inners_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "inners A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>b,c\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding inners_def by auto
  also have "... = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>right_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, left_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>b, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed

definition lefts :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "lefts A B C D = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma lefts_type[type_rule]: "lefts A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (A \<times>\<^sub>c C)"
  unfolding lefts_def by typecheck_cfuncs

lemma lefts_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "lefts A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>a,c\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding lefts_def by (auto)
  also have "... = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>left_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, left_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>a, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed

definition rights :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "rights A B C D = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma rights_type[type_rule]: "rights A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (B \<times>\<^sub>c D)"
  unfolding rights_def by typecheck_cfuncs

lemma rights_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "rights A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>b,d\<rangle>"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding rights_def using assms comp_associative2 by auto
  also have "... = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>right_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, right_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>b, d\<rangle>"
    using assms by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_prod)
  then show ?thesis
    using calculation by auto
qed



end