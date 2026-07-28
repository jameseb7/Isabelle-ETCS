section \<open>Cartesian Products of Sets\<close>

theory Product
  imports Cfunc
begin

text \<open>The axiomatization below corresponds to Axiom 2 (Cartesian Products) in Halvorson.\<close>
axiomatization
  cart_prod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<times>\<^sub>c" 65) and
  left_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("\<langle>_,_\<rangle>")
where
  left_cart_proj_type[type_rule]: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" and
  right_cart_proj_type[type_rule]: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" and
  cfunc_prod_type[type_rule]: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> \<langle>f,g\<rangle> : Z \<rightarrow> X \<times>\<^sub>c Y" and
  left_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>f,g\<rangle> = f" and
  right_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>f,g\<rangle> = g" and
  cfunc_prod_unique: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> h : Z \<rightarrow> X \<times>\<^sub>c Y \<Longrightarrow>
    left_cart_proj(X, Y) \<circ>\<^sub>c h = f \<Longrightarrow> right_cart_proj(X, Y) \<circ>\<^sub>c h = g \<Longrightarrow> h = \<langle>f,g\<rangle>"

definition is_cart_prod :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> o" where
  "is_cart_prod(W, \<pi>\<^sub>0, \<pi>\<^sub>1, X, Y) \<longleftrightarrow>
    (\<pi>\<^sub>0 : W \<rightarrow> X \<and> \<pi>\<^sub>1 : W \<rightarrow> Y \<and>
    (\<forall> f g Z. (f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y) \<longrightarrow>
      (\<exists> h. h : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h = g \<and>
        (\<forall> h2. (h2 : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h))))"

lemma is_cart_prod_def2:
  assumes "\<pi>\<^sub>0 : W \<rightarrow> X" "\<pi>\<^sub>1 : W \<rightarrow> Y"
  shows "is_cart_prod(W, \<pi>\<^sub>0, \<pi>\<^sub>1, X, Y) \<longleftrightarrow>
    (\<forall> f g Z. (f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y) \<longrightarrow>
      (\<exists> h. h : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h = g \<and>
        (\<forall> h2. (h2 : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h)))"
  unfolding is_cart_prod_def using assms by auto

text \<open>Note: HOL's @{text is_cart_prod_triple} abbreviation (bundling @{text "W \<pi>\<^sub>0 \<pi>\<^sub>1"} into a
  single HOL tuple via @{text fst}/@{text snd}) has no plain-FOL equivalent -- FOL, unlike HOL, has
  no built-in product/tuple type. We simply take the three components as separate arguments
  wherever the HOL original used the triple form; this is a pure notational difference, not a
  change in content.\<close>

lemma canonical_cart_prod_is_cart_prod:
 "is_cart_prod(X \<times>\<^sub>c Y, left_cart_proj(X, Y), right_cart_proj(X, Y), X, Y)"
  unfolding is_cart_prod_def
proof (intro conjI)
  show "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by typecheck_cfuncs
  show "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by typecheck_cfuncs
  show "\<forall>f g Z. f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y \<longrightarrow>
    (\<exists>h. h : Z \<rightarrow> X \<times>\<^sub>c Y \<and> left_cart_proj(X, Y) \<circ>\<^sub>c h = f \<and> right_cart_proj(X, Y) \<circ>\<^sub>c h = g \<and>
      (\<forall>h2. h2 : Z \<rightarrow> X \<times>\<^sub>c Y \<and> left_cart_proj(X, Y) \<circ>\<^sub>c h2 = f \<and> right_cart_proj(X, Y) \<circ>\<^sub>c h2 = g \<longrightarrow> h2 = h))"
  proof (intro allI impI)
    fix f g Z
    assume "f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y"
    then have f_type: "f : Z \<rightarrow> X" and g_type: "g : Z \<rightarrow> Y" by auto
    show "\<exists>h. h : Z \<rightarrow> X \<times>\<^sub>c Y \<and> left_cart_proj(X, Y) \<circ>\<^sub>c h = f \<and> right_cart_proj(X, Y) \<circ>\<^sub>c h = g \<and>
      (\<forall>h2. h2 : Z \<rightarrow> X \<times>\<^sub>c Y \<and> left_cart_proj(X, Y) \<circ>\<^sub>c h2 = f \<and> right_cart_proj(X, Y) \<circ>\<^sub>c h2 = g \<longrightarrow> h2 = h)"
    proof (intro exI[where x="\<langle>f,g\<rangle>"] conjI)
      show "\<langle>f,g\<rangle> : Z \<rightarrow> X \<times>\<^sub>c Y" using f_type g_type cfunc_prod_type by auto
      show "left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>f,g\<rangle> = f" using f_type g_type left_cart_proj_cfunc_prod by auto
      show "right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>f,g\<rangle> = g" using f_type g_type right_cart_proj_cfunc_prod by auto
      show "\<forall>h2. h2 : Z \<rightarrow> X \<times>\<^sub>c Y \<and> left_cart_proj(X, Y) \<circ>\<^sub>c h2 = f \<and> right_cart_proj(X, Y) \<circ>\<^sub>c h2 = g \<longrightarrow> h2 = \<langle>f,g\<rangle>"
      proof (intro allI impI)
        fix h2
        assume "h2 : Z \<rightarrow> X \<times>\<^sub>c Y \<and> left_cart_proj(X, Y) \<circ>\<^sub>c h2 = f \<and> right_cart_proj(X, Y) \<circ>\<^sub>c h2 = g"
        then show "h2 = \<langle>f,g\<rangle>"
          using f_type g_type cfunc_prod_unique by auto
      qed
    qed
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.1.8 in Halvorson.\<close>
lemma cart_prods_isomorphic:
  assumes W_cart_prod:  "is_cart_prod(W, \<pi>\<^sub>0, \<pi>\<^sub>1, X, Y)"
  assumes W'_cart_prod: "is_cart_prod(W', \<pi>'\<^sub>0, \<pi>'\<^sub>1, X, Y)"
  shows "\<exists> f. f : W \<rightarrow> W' \<and> isomorphism(f) \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
proof -
  obtain f where f_def: "f : W \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
    using W'_cart_prod W_cart_prod unfolding is_cart_prod_def by blast

  obtain g where g_def: "g : W' \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c g = \<pi>'\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c g = \<pi>'\<^sub>1"
      using W'_cart_prod W_cart_prod unfolding is_cart_prod_def by blast

  have fg0: "\<pi>'\<^sub>0 \<circ>\<^sub>c (f \<circ>\<^sub>c g) = \<pi>'\<^sub>0"
    using W'_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto
  have fg1: "\<pi>'\<^sub>1 \<circ>\<^sub>c (f \<circ>\<^sub>c g) = \<pi>'\<^sub>1"
    using W'_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto

  obtain idW' where idW'_props: "idW' : W' \<rightarrow> W' \<and> (\<forall> h2. (h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1) \<longrightarrow> h2 = idW')"
    using W'_cart_prod unfolding is_cart_prod_def by blast
  have fg: "f \<circ>\<^sub>c g = id(W')"
  proof -
    have idW'_unique: "\<forall>h2. h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1 \<longrightarrow> h2 = idW'"
      using idW'_props by auto
    have 1: "f \<circ>\<^sub>c g = idW'"
      using comp_type f_def fg0 fg1 g_def idW'_unique by blast
    have pi0'_type: "\<pi>'\<^sub>0 : W' \<rightarrow> X" and pi1'_type: "\<pi>'\<^sub>1 : W' \<rightarrow> Y"
      using W'_cart_prod unfolding is_cart_prod_def by auto
    have 2: "id(W') = idW'"
    proof -
      have "id(W') : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c id(W') = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c id(W') = \<pi>'\<^sub>1"
        using pi0'_type pi1'_type id_type id_right_unit2 by auto
      then show "id(W') = idW'" using idW'_unique by auto
    qed
    from 1 2 show "f \<circ>\<^sub>c g = id(W')"
      by auto
  qed

  have gf0: "\<pi>\<^sub>0 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>0"
    using W_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto
  have gf1: "\<pi>\<^sub>1 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>1"
    using W_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto

  obtain idW where idW_props: "idW : W \<rightarrow> W \<and> (\<forall> h2. (h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1) \<longrightarrow> h2 = idW)"
    using W_cart_prod unfolding is_cart_prod_def by blast
  have gf: "g \<circ>\<^sub>c f = id(W)"
  proof -
    have idW_unique: "\<forall>h2. h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1 \<longrightarrow> h2 = idW"
      using idW_props by auto
    have 1: "g \<circ>\<^sub>c f = idW"
      using comp_type g_def f_def gf0 gf1 idW_unique by blast
    have pi0_type: "\<pi>\<^sub>0 : W \<rightarrow> X" and pi1_type: "\<pi>\<^sub>1 : W \<rightarrow> Y"
      using W_cart_prod unfolding is_cart_prod_def by auto
    have 2: "id(W) = idW"
    proof -
      have "id(W) : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c id(W) = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c id(W) = \<pi>\<^sub>1"
        using pi0_type pi1_type id_type id_right_unit2 by auto
      then show "id(W) = idW" using idW_unique by auto
    qed
    from 1 2 show "g \<circ>\<^sub>c f = id(W)"
      by auto
  qed

  have f_iso: "isomorphism(f)"
    using f_def fg g_def gf isomorphism_def3 by blast
  from f_iso f_def show "\<exists>f. f : W \<rightarrow> W' \<and> isomorphism(f) \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
    by auto
qed

lemma product_commutes:
  "A \<times>\<^sub>c B \<cong> B \<times>\<^sub>c A"
proof -
  define swapAB where "swapAB = \<langle>right_cart_proj(A, B), left_cart_proj(A, B)\<rangle>"
  define swapBA where "swapBA = \<langle>right_cart_proj(B, A), left_cart_proj(B, A)\<rangle>"
  have swapAB_type: "swapAB : A \<times>\<^sub>c B \<rightarrow> B \<times>\<^sub>c A"
    unfolding swapAB_def by typecheck_cfuncs
  have swapBA_type: "swapBA : B \<times>\<^sub>c A \<rightarrow> A \<times>\<^sub>c B"
    unfolding swapBA_def by typecheck_cfuncs
  have left_swapAB: "left_cart_proj(B, A) \<circ>\<^sub>c swapAB = right_cart_proj(A, B)"
    unfolding swapAB_def by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
  have right_swapAB: "right_cart_proj(B, A) \<circ>\<^sub>c swapAB = left_cart_proj(A, B)"
    unfolding swapAB_def by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_prod)
  have left_swapBA: "left_cart_proj(A, B) \<circ>\<^sub>c swapBA = right_cart_proj(B, A)"
    unfolding swapBA_def by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
  have right_swapBA: "right_cart_proj(A, B) \<circ>\<^sub>c swapBA = left_cart_proj(B, A)"
    unfolding swapBA_def by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_prod)

  have id_AB: "swapBA \<circ>\<^sub>c swapAB = id(A \<times>\<^sub>c B)"
  proof -
    have l: "left_cart_proj(A, B) \<circ>\<^sub>c (swapBA \<circ>\<^sub>c swapAB) = left_cart_proj(A, B)"
      using swapAB_type swapBA_type left_swapBA right_swapAB
      by (typecheck_cfuncs, simp add: comp_associative2)
    have r: "right_cart_proj(A, B) \<circ>\<^sub>c (swapBA \<circ>\<^sub>c swapAB) = right_cart_proj(A, B)"
      using swapAB_type swapBA_type right_swapBA left_swapAB
      by (typecheck_cfuncs, simp add: comp_associative2)
    have eq1: "swapBA \<circ>\<^sub>c swapAB = \<langle>left_cart_proj(A, B), right_cart_proj(A, B)\<rangle>"
    proof (rule cfunc_prod_unique)
      show "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by typecheck_cfuncs
      show "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by typecheck_cfuncs
      show "swapBA \<circ>\<^sub>c swapAB : A \<times>\<^sub>c B \<rightarrow> A \<times>\<^sub>c B" using swapAB_type swapBA_type comp_type by auto
      show "left_cart_proj(A, B) \<circ>\<^sub>c (swapBA \<circ>\<^sub>c swapAB) = left_cart_proj(A, B)" using l by simp
      show "right_cart_proj(A, B) \<circ>\<^sub>c (swapBA \<circ>\<^sub>c swapAB) = right_cart_proj(A, B)" using r by simp
    qed
    have eq2: "id(A \<times>\<^sub>c B) = \<langle>left_cart_proj(A, B), right_cart_proj(A, B)\<rangle>"
    proof (rule cfunc_prod_unique)
      show "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by typecheck_cfuncs
      show "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by typecheck_cfuncs
      show "id(A \<times>\<^sub>c B) : A \<times>\<^sub>c B \<rightarrow> A \<times>\<^sub>c B" by typecheck_cfuncs
      show "left_cart_proj(A, B) \<circ>\<^sub>c id(A \<times>\<^sub>c B) = left_cart_proj(A, B)" by (typecheck_cfuncs, simp add: id_right_unit2)
      show "right_cart_proj(A, B) \<circ>\<^sub>c id(A \<times>\<^sub>c B) = right_cart_proj(A, B)" by (typecheck_cfuncs, simp add: id_right_unit2)
    qed
    show ?thesis using eq1 eq2 by simp
  qed
  have id_BA: "swapAB \<circ>\<^sub>c swapBA = id(B \<times>\<^sub>c A)"
  proof -
    have l: "left_cart_proj(B, A) \<circ>\<^sub>c (swapAB \<circ>\<^sub>c swapBA) = left_cart_proj(B, A)"
      using swapAB_type swapBA_type left_swapAB right_swapBA
      by (typecheck_cfuncs, simp add: comp_associative2)
    have r: "right_cart_proj(B, A) \<circ>\<^sub>c (swapAB \<circ>\<^sub>c swapBA) = right_cart_proj(B, A)"
      using swapAB_type swapBA_type right_swapAB left_swapBA
      by (typecheck_cfuncs, simp add: comp_associative2)
    have eq1: "swapAB \<circ>\<^sub>c swapBA = \<langle>left_cart_proj(B, A), right_cart_proj(B, A)\<rangle>"
    proof (rule cfunc_prod_unique)
      show "left_cart_proj(B, A) : B \<times>\<^sub>c A \<rightarrow> B" by typecheck_cfuncs
      show "right_cart_proj(B, A) : B \<times>\<^sub>c A \<rightarrow> A" by typecheck_cfuncs
      show "swapAB \<circ>\<^sub>c swapBA : B \<times>\<^sub>c A \<rightarrow> B \<times>\<^sub>c A" using swapAB_type swapBA_type comp_type by auto
      show "left_cart_proj(B, A) \<circ>\<^sub>c (swapAB \<circ>\<^sub>c swapBA) = left_cart_proj(B, A)" using l by simp
      show "right_cart_proj(B, A) \<circ>\<^sub>c (swapAB \<circ>\<^sub>c swapBA) = right_cart_proj(B, A)" using r by simp
    qed
    have eq2: "id(B \<times>\<^sub>c A) = \<langle>left_cart_proj(B, A), right_cart_proj(B, A)\<rangle>"
    proof (rule cfunc_prod_unique)
      show "left_cart_proj(B, A) : B \<times>\<^sub>c A \<rightarrow> B" by typecheck_cfuncs
      show "right_cart_proj(B, A) : B \<times>\<^sub>c A \<rightarrow> A" by typecheck_cfuncs
      show "id(B \<times>\<^sub>c A) : B \<times>\<^sub>c A \<rightarrow> B \<times>\<^sub>c A" by typecheck_cfuncs
      show "left_cart_proj(B, A) \<circ>\<^sub>c id(B \<times>\<^sub>c A) = left_cart_proj(B, A)" by (typecheck_cfuncs, simp add: id_right_unit2)
      show "right_cart_proj(B, A) \<circ>\<^sub>c id(B \<times>\<^sub>c A) = right_cart_proj(B, A)" by (typecheck_cfuncs, simp add: id_right_unit2)
    qed
    show ?thesis using eq1 eq2 by simp
  qed
  show "A \<times>\<^sub>c B \<cong> B \<times>\<^sub>c A"
    unfolding is_isomorphic_def
  proof (intro exI[where x=swapAB])
    show "swapAB : A \<times>\<^sub>c B \<rightarrow> B \<times>\<^sub>c A \<and> isomorphism(swapAB)"
    proof
      show "swapAB : A \<times>\<^sub>c B \<rightarrow> B \<times>\<^sub>c A"
        using swapAB_type by simp
    next
      show "isomorphism(swapAB)"
        unfolding isomorphism_def
      proof (intro exI[where x=swapBA])
        show "domain(swapBA) = codomain(swapAB) \<and>
              codomain(swapBA) = domain(swapAB) \<and>
              swapBA \<circ>\<^sub>c swapAB = id(domain(swapAB)) \<and>
              swapAB \<circ>\<^sub>c swapBA = id(domain(swapBA))"
          using swapAB_type swapBA_type id_BA id_AB unfolding cfunc_type_def by auto
      qed
    qed
  qed
qed

lemma cart_prod_eq:
  assumes a_type: "a : Z \<rightarrow> X \<times>\<^sub>c Y" and b_type: "b : Z \<rightarrow> X \<times>\<^sub>c Y"
  shows "a = b \<longleftrightarrow>
    (left_cart_proj(X, Y) \<circ>\<^sub>c a = left_cart_proj(X, Y) \<circ>\<^sub>c b
      \<and> right_cart_proj(X, Y) \<circ>\<^sub>c a = right_cart_proj(X, Y) \<circ>\<^sub>c b)"
proof
  assume "a = b"
  then show "left_cart_proj(X, Y) \<circ>\<^sub>c a = left_cart_proj(X, Y) \<circ>\<^sub>c b \<and> right_cart_proj(X, Y) \<circ>\<^sub>c a = right_cart_proj(X, Y) \<circ>\<^sub>c b"
    by auto
next
  assume eqs: "left_cart_proj(X, Y) \<circ>\<^sub>c a = left_cart_proj(X, Y) \<circ>\<^sub>c b \<and> right_cart_proj(X, Y) \<circ>\<^sub>c a = right_cart_proj(X, Y) \<circ>\<^sub>c b"
  have a_eq: "a = \<langle>left_cart_proj(X, Y) \<circ>\<^sub>c a, right_cart_proj(X, Y) \<circ>\<^sub>c a\<rangle>"
  proof (rule cfunc_prod_unique)
    show "left_cart_proj(X, Y) \<circ>\<^sub>c a : Z \<rightarrow> X" using a_type by typecheck_cfuncs
    show "right_cart_proj(X, Y) \<circ>\<^sub>c a : Z \<rightarrow> Y" using a_type by typecheck_cfuncs
    show "a : Z \<rightarrow> X \<times>\<^sub>c Y" using a_type by simp
    show "left_cart_proj(X, Y) \<circ>\<^sub>c a = left_cart_proj(X, Y) \<circ>\<^sub>c a" by simp
    show "right_cart_proj(X, Y) \<circ>\<^sub>c a = right_cart_proj(X, Y) \<circ>\<^sub>c a" by simp
  qed
  have b_eq: "b = \<langle>left_cart_proj(X, Y) \<circ>\<^sub>c b, right_cart_proj(X, Y) \<circ>\<^sub>c b\<rangle>"
  proof (rule cfunc_prod_unique)
    show "left_cart_proj(X, Y) \<circ>\<^sub>c b : Z \<rightarrow> X" using b_type by typecheck_cfuncs
    show "right_cart_proj(X, Y) \<circ>\<^sub>c b : Z \<rightarrow> Y" using b_type by typecheck_cfuncs
    show "b : Z \<rightarrow> X \<times>\<^sub>c Y" using b_type by simp
    show "left_cart_proj(X, Y) \<circ>\<^sub>c b = left_cart_proj(X, Y) \<circ>\<^sub>c b" by simp
    show "right_cart_proj(X, Y) \<circ>\<^sub>c b = right_cart_proj(X, Y) \<circ>\<^sub>c b" by simp
  qed
  show "a = b" using a_eq b_eq eqs by simp
qed

lemma cart_prod_eqI:
  assumes "a : Z \<rightarrow> X \<times>\<^sub>c Y" "b : Z \<rightarrow> X \<times>\<^sub>c Y"
  assumes "(left_cart_proj(X, Y) \<circ>\<^sub>c a = left_cart_proj(X, Y) \<circ>\<^sub>c b
      \<and> right_cart_proj(X, Y) \<circ>\<^sub>c a = right_cart_proj(X, Y) \<circ>\<^sub>c b)"
  shows "a = b"
  using assms cart_prod_eq by auto

lemma cart_prod_eq2:
  assumes a_type: "a : Z \<rightarrow> X" and b_type: "b : Z \<rightarrow> Y" and c_type: "c : Z \<rightarrow> X" and d_type: "d : Z \<rightarrow> Y"
  shows "\<langle>a, b\<rangle> = \<langle>c,d\<rangle> \<longleftrightarrow> (a = c \<and> b = d)"
proof
  assume eq: "\<langle>a, b\<rangle> = \<langle>c,d\<rangle>"
  have left_a: "left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>a,b\<rangle> = a" using a_type b_type left_cart_proj_cfunc_prod by auto
  have left_c: "left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>c,d\<rangle> = c" using c_type d_type left_cart_proj_cfunc_prod by auto
  have right_a: "right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>a,b\<rangle> = b" using a_type b_type right_cart_proj_cfunc_prod by auto
  have right_c: "right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>c,d\<rangle> = d" using c_type d_type right_cart_proj_cfunc_prod by auto
  have "a = c" using eq left_a left_c by simp
  moreover have "b = d" using eq right_a right_c by simp
  ultimately show "a = c \<and> b = d" by simp
next
  assume "a = c \<and> b = d"
  then show "\<langle>a, b\<rangle> = \<langle>c,d\<rangle>" by auto
qed

lemma cart_prod_decomp:
  assumes a_type: "a : A \<rightarrow> X \<times>\<^sub>c Y"
  shows "\<exists> x y. a = \<langle>x, y\<rangle> \<and> x : A \<rightarrow> X \<and> y : A \<rightarrow> Y"
proof -
  have lp_type: "left_cart_proj(X, Y) \<circ>\<^sub>c a : A \<rightarrow> X"
    using a_type left_cart_proj_type comp_type by blast
  have rp_type: "right_cart_proj(X, Y) \<circ>\<^sub>c a : A \<rightarrow> Y"
    using a_type right_cart_proj_type comp_type by blast
  have a_eq: "a = \<langle>left_cart_proj(X, Y) \<circ>\<^sub>c a, right_cart_proj(X, Y) \<circ>\<^sub>c a\<rangle>"
  proof (rule cfunc_prod_unique)
    show "left_cart_proj(X, Y) \<circ>\<^sub>c a : A \<rightarrow> X" using lp_type by simp
    show "right_cart_proj(X, Y) \<circ>\<^sub>c a : A \<rightarrow> Y" using rp_type by simp
    show "a : A \<rightarrow> X \<times>\<^sub>c Y" using a_type by simp
    show "left_cart_proj(X, Y) \<circ>\<^sub>c a = left_cart_proj(X, Y) \<circ>\<^sub>c a" by simp
    show "right_cart_proj(X, Y) \<circ>\<^sub>c a = right_cart_proj(X, Y) \<circ>\<^sub>c a" by simp
  qed
  show "\<exists> x y. a = \<langle>x, y\<rangle> \<and> x : A \<rightarrow> X \<and> y : A \<rightarrow> Y"
    using a_eq lp_type rp_type by auto
qed

subsection \<open>Diagonal Functions\<close>

text \<open>The definition below corresponds to Definition 2.1.9 in Halvorson.\<close>
definition diagonal :: "cset \<Rightarrow> cfunc" where
  "diagonal(X) = \<langle>id(X),id(X)\<rangle>"

lemma diagonal_type[type_rule]:
  "diagonal(X) : X \<rightarrow> X \<times>\<^sub>c X"
  unfolding diagonal_def by (simp add: cfunc_prod_type id_type)

lemma diag_mono:
  "monomorphism(diagonal(X))"
proof -
  have diag_type: "diagonal(X) : X \<rightarrow> X \<times>\<^sub>c X" by (rule diagonal_type)
  have lp_type: "left_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by typecheck_cfuncs
  have comp_eq: "left_cart_proj(X, X) \<circ>\<^sub>c diagonal(X) = id(X)"
    unfolding diagonal_def using left_cart_proj_cfunc_prod[OF id_type id_type] by simp
  have dom_eq: "domain(left_cart_proj(X, X)) = codomain(diagonal(X))"
    using diag_type lp_type unfolding cfunc_type_def by auto
  have id_mono: "monomorphism(id(X))"
    using id_isomorphism iso_imp_epi_and_monic by auto
  have "monomorphism(left_cart_proj(X, X) \<circ>\<^sub>c diagonal(X))"
    using comp_eq id_mono by simp
  then show "monomorphism(diagonal(X))"
    using dom_eq comp_monic_imp_monic by auto
qed

subsection \<open>Products of Functions\<close>

text \<open>The definition below corresponds to Definition 2.1.10 in Halvorson.\<close>
definition cfunc_cross_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<times>\<^sub>f" 55) where
  "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj(domain(f), domain(g)), g \<circ>\<^sub>c right_cart_proj(domain(f), domain(g))\<rangle>"

lemma cfunc_cross_prod_def2:
  assumes "f : X \<rightarrow> Y" "g : V \<rightarrow> W"
  shows "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj(X, V), g \<circ>\<^sub>c right_cart_proj(X, V)\<rangle>"
  using assms cfunc_cross_prod_def unfolding cfunc_type_def by auto

lemma cfunc_cross_prod_type[type_rule]:
  assumes f_type: "f : W \<rightarrow> Y" and g_type: "g : X \<rightarrow> Z"
  shows "f \<times>\<^sub>f g : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z"
proof -
  have eq: "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj(W, X), g \<circ>\<^sub>c right_cart_proj(W, X)\<rangle>"
    using f_type g_type cfunc_cross_prod_def2 by auto
  have lp_type: "left_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> W" by typecheck_cfuncs
  have rp_type: "right_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> X" by typecheck_cfuncs
  have "f \<circ>\<^sub>c left_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Y" using f_type lp_type comp_type by blast
  moreover have "g \<circ>\<^sub>c right_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Z" using g_type rp_type comp_type by blast
  ultimately show ?thesis using eq cfunc_prod_type by auto
qed

lemma left_cart_proj_cfunc_cross_prod:
  assumes f_type: "f : W \<rightarrow> Y" and g_type: "g : X \<rightarrow> Z"
  shows "left_cart_proj(Y, Z) \<circ>\<^sub>c f \<times>\<^sub>f g = f \<circ>\<^sub>c left_cart_proj(W, X)"
proof -
  have eq: "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj(W, X), g \<circ>\<^sub>c right_cart_proj(W, X)\<rangle>"
    using f_type g_type cfunc_cross_prod_def2 by auto
  have fW: "f \<circ>\<^sub>c left_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Y"
    using f_type comp_type left_cart_proj_type by blast
  have gX: "g \<circ>\<^sub>c right_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Z"
    using g_type comp_type right_cart_proj_type by blast
  show ?thesis
    using eq fW gX left_cart_proj_cfunc_prod by auto
qed

lemma right_cart_proj_cfunc_cross_prod:
  assumes f_type: "f : W \<rightarrow> Y" and g_type: "g : X \<rightarrow> Z"
  shows "right_cart_proj(Y, Z) \<circ>\<^sub>c f \<times>\<^sub>f g = g \<circ>\<^sub>c right_cart_proj(W, X)"
proof -
  have eq: "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj(W, X), g \<circ>\<^sub>c right_cart_proj(W, X)\<rangle>"
    using f_type g_type cfunc_cross_prod_def2 by auto
  have fW: "f \<circ>\<^sub>c left_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Y"
    using f_type comp_type left_cart_proj_type by blast
  have gX: "g \<circ>\<^sub>c right_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Z"
    using g_type comp_type right_cart_proj_type by blast
  show ?thesis
    using eq fW gX right_cart_proj_cfunc_prod by auto
qed

lemma cfunc_cross_prod_unique:
  assumes f_type: "f : W \<rightarrow> Y" and g_type: "g : X \<rightarrow> Z" and h_type: "h : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z"
  assumes left_eq: "left_cart_proj(Y, Z) \<circ>\<^sub>c h = f \<circ>\<^sub>c left_cart_proj(W, X)"
  assumes right_eq: "right_cart_proj(Y, Z) \<circ>\<^sub>c h = g \<circ>\<^sub>c right_cart_proj(W, X)"
  shows "h = f \<times>\<^sub>f g"
proof -
  have eq: "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj(W, X), g \<circ>\<^sub>c right_cart_proj(W, X)\<rangle>"
    using f_type g_type cfunc_cross_prod_def2 by auto
  have fW: "f \<circ>\<^sub>c left_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Y"
    using f_type comp_type left_cart_proj_type by blast
  have gX: "g \<circ>\<^sub>c right_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Z"
    using g_type comp_type right_cart_proj_type by blast
  have "h = \<langle>f \<circ>\<^sub>c left_cart_proj(W, X), g \<circ>\<^sub>c right_cart_proj(W, X)\<rangle>"
  proof (rule cfunc_prod_unique)
    show "f \<circ>\<^sub>c left_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Y" using fW by simp
    show "g \<circ>\<^sub>c right_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> Z" using gX by simp
    show "h : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z" using h_type by simp
    show "left_cart_proj(Y, Z) \<circ>\<^sub>c h = f \<circ>\<^sub>c left_cart_proj(W, X)" using left_eq by simp
    show "right_cart_proj(Y, Z) \<circ>\<^sub>c h = g \<circ>\<^sub>c right_cart_proj(W, X)" using right_eq by simp
  qed
  then show ?thesis using eq by simp
qed

text \<open>The lemma below corresponds to Proposition 2.1.11 in Halvorson.\<close>
lemma identity_distributes_across_composition:
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C"
  shows "id(X) \<times>\<^sub>f (g \<circ>\<^sub>c f) = (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have gf_type: "g \<circ>\<^sub>c f : A \<rightarrow> C" using f_type g_type comp_type by blast
  have h1_type: "id(X) \<times>\<^sub>f f : X \<times>\<^sub>c A \<rightarrow> X \<times>\<^sub>c B" using idX_type f_type cfunc_cross_prod_type by auto
  have h2_type: "id(X) \<times>\<^sub>f g : X \<times>\<^sub>c B \<rightarrow> X \<times>\<^sub>c C" using idX_type g_type cfunc_cross_prod_type by auto
  have h_type: "(id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) : X \<times>\<^sub>c A \<rightarrow> X \<times>\<^sub>c C"
    using h1_type h2_type comp_type by blast
  have lpXC_type: "left_cart_proj(X, C) : X \<times>\<^sub>c C \<rightarrow> X" by typecheck_cfuncs
  have lpXB_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by typecheck_cfuncs
  have rpXC_type: "right_cart_proj(X, C) : X \<times>\<^sub>c C \<rightarrow> C" by typecheck_cfuncs
  have rpXB_type: "right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> B" by typecheck_cfuncs
  have lpXA_type: "left_cart_proj(X, A) : X \<times>\<^sub>c A \<rightarrow> X" by typecheck_cfuncs
  have idlp_type: "id(X) \<circ>\<^sub>c left_cart_proj(X, A) : X \<times>\<^sub>c A \<rightarrow> X" using idX_type lpXA_type comp_type by blast
  have left_eq: "left_cart_proj(X, C) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) = id(X) \<circ>\<^sub>c left_cart_proj(X, A)"
  proof -
    have "left_cart_proj(X, C) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)) = (left_cart_proj(X, C) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)"
      using comp_associative2[OF h1_type h2_type lpXC_type] by simp
    also have "... = (id(X) \<circ>\<^sub>c left_cart_proj(X, B)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)"
      using idX_type g_type left_cart_proj_cfunc_cross_prod by simp
    also have "... = id(X) \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f))"
      using comp_associative2[OF h1_type lpXB_type idX_type] by simp
    also have "... = id(X) \<circ>\<^sub>c (id(X) \<circ>\<^sub>c left_cart_proj(X, A))"
      using idX_type f_type left_cart_proj_cfunc_cross_prod by simp
    also have "... = id(X) \<circ>\<^sub>c left_cart_proj(X, A)"
      using id_left_unit2[OF idlp_type] by simp
    finally show ?thesis by simp
  qed
  have right_eq: "right_cart_proj(X, C) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj(X, A)"
  proof -
    have "right_cart_proj(X, C) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)) = (right_cart_proj(X, C) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)"
      using comp_associative2[OF h1_type h2_type rpXC_type] by simp
    also have "... = (g \<circ>\<^sub>c right_cart_proj(X, B)) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f)"
      using idX_type g_type right_cart_proj_cfunc_cross_prod by simp
    also have "... = g \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f))"
      using comp_associative2[OF h1_type rpXB_type g_type] by simp
    also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c right_cart_proj(X, A))"
      using idX_type f_type right_cart_proj_cfunc_cross_prod by simp
    also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj(X, A)"
      using comp_associative2[OF right_cart_proj_type f_type g_type] by simp
    finally show ?thesis by simp
  qed
  have result: "(id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) = id(X) \<times>\<^sub>f (g \<circ>\<^sub>c f)"
  proof (rule cfunc_cross_prod_unique)
    show "id(X) : X \<rightarrow> X" by (rule idX_type)
    show "g \<circ>\<^sub>c f : A \<rightarrow> C" by (rule gf_type)
    show "(id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) : X \<times>\<^sub>c A \<rightarrow> X \<times>\<^sub>c C" by (rule h_type)
    show "left_cart_proj(X, C) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) = id(X) \<circ>\<^sub>c left_cart_proj(X, A)" by (rule left_eq)
    show "right_cart_proj(X, C) \<circ>\<^sub>c (id(X) \<times>\<^sub>f g) \<circ>\<^sub>c (id(X) \<times>\<^sub>f f) = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj(X, A)" by (rule right_eq)
  qed
  show ?thesis using result by simp
qed

lemma cfunc_cross_prod_comp_cfunc_prod:
  assumes a_type: "a : A \<rightarrow> W" and b_type: "b : A \<rightarrow> X"
  assumes f_type: "f : W \<rightarrow> Y" and g_type: "g : X \<rightarrow> Z"
  shows "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = \<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle>"
proof -
  have ab_type: "\<langle>a, b\<rangle> : A \<rightarrow> W \<times>\<^sub>c X" using a_type b_type cfunc_prod_type by auto
  have fg_type: "f \<times>\<^sub>f g : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z" using f_type g_type cfunc_cross_prod_type by auto
  have h_type: "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z"
    using ab_type fg_type comp_type by blast
  have lpYZ_type: "left_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Y" by typecheck_cfuncs
  have rpYZ_type: "right_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Z" by typecheck_cfuncs
  have lpWX_type: "left_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> W" by typecheck_cfuncs
  have rpWX_type: "right_cart_proj(W, X) : W \<times>\<^sub>c X \<rightarrow> X" by typecheck_cfuncs
  have left_eq: "left_cart_proj(Y, Z) \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c a"
  proof -
    have "left_cart_proj(Y, Z) \<circ>\<^sub>c ((f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle>) = (left_cart_proj(Y, Z) \<circ>\<^sub>c (f \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using comp_associative2[OF ab_type fg_type lpYZ_type] by simp
    also have "... = (f \<circ>\<^sub>c left_cart_proj(W, X)) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using f_type g_type left_cart_proj_cfunc_cross_prod by simp
    also have "... = f \<circ>\<^sub>c (left_cart_proj(W, X) \<circ>\<^sub>c \<langle>a, b\<rangle>)"
      using comp_associative2[OF ab_type lpWX_type f_type] by simp
    also have "... = f \<circ>\<^sub>c a"
      using a_type b_type left_cart_proj_cfunc_prod by simp
    finally show ?thesis by simp
  qed
  have right_eq: "right_cart_proj(Y, Z) \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c b"
  proof -
    have "right_cart_proj(Y, Z) \<circ>\<^sub>c ((f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle>) = (right_cart_proj(Y, Z) \<circ>\<^sub>c (f \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using comp_associative2[OF ab_type fg_type rpYZ_type] by simp
    also have "... = (g \<circ>\<^sub>c right_cart_proj(W, X)) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using f_type g_type right_cart_proj_cfunc_cross_prod by simp
    also have "... = g \<circ>\<^sub>c (right_cart_proj(W, X) \<circ>\<^sub>c \<langle>a, b\<rangle>)"
      using comp_associative2[OF ab_type rpWX_type g_type] by simp
    also have "... = g \<circ>\<^sub>c b"
      using a_type b_type right_cart_proj_cfunc_prod by simp
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (rule cfunc_prod_unique)
    show "f \<circ>\<^sub>c a : A \<rightarrow> Y" using f_type a_type comp_type by blast
    show "g \<circ>\<^sub>c b : A \<rightarrow> Z" using g_type b_type comp_type by blast
    show "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z" using h_type by simp
    show "left_cart_proj(Y, Z) \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c a" using left_eq by simp
    show "right_cart_proj(Y, Z) \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c b" using right_eq by simp
  qed
qed

lemma cfunc_prod_comp:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes a_type: "a : Y \<rightarrow> A" and b_type: "b : Y \<rightarrow> B"
  shows "\<langle>a, b\<rangle> \<circ>\<^sub>c f = \<langle>a \<circ>\<^sub>c f, b \<circ>\<^sub>c f\<rangle>"
proof -
  have ab_type: "\<langle>a, b\<rangle> : Y \<rightarrow> A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
  have h_type: "\<langle>a, b\<rangle> \<circ>\<^sub>c f : X \<rightarrow> A \<times>\<^sub>c B" using ab_type f_type comp_type by blast
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by typecheck_cfuncs
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by typecheck_cfuncs
  have same_left_proj: "left_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = a \<circ>\<^sub>c f"
  proof -
    have "left_cart_proj(A, B) \<circ>\<^sub>c (\<langle>a, b\<rangle> \<circ>\<^sub>c f) = (left_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle>) \<circ>\<^sub>c f"
      using comp_associative2[OF f_type ab_type lpAB_type] by simp
    also have "... = a \<circ>\<^sub>c f"
      using a_type b_type left_cart_proj_cfunc_prod by simp
    finally show ?thesis by simp
  qed
  have same_right_proj: "right_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = b \<circ>\<^sub>c f"
  proof -
    have "right_cart_proj(A, B) \<circ>\<^sub>c (\<langle>a, b\<rangle> \<circ>\<^sub>c f) = (right_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle>) \<circ>\<^sub>c f"
      using comp_associative2[OF f_type ab_type rpAB_type] by simp
    also have "... = b \<circ>\<^sub>c f"
      using a_type b_type right_cart_proj_cfunc_prod by simp
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (rule cfunc_prod_unique)
    show "a \<circ>\<^sub>c f : X \<rightarrow> A" using a_type f_type comp_type by blast
    show "b \<circ>\<^sub>c f : X \<rightarrow> B" using b_type f_type comp_type by blast
    show "\<langle>a, b\<rangle> \<circ>\<^sub>c f : X \<rightarrow> A \<times>\<^sub>c B" using h_type by simp
    show "left_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = a \<circ>\<^sub>c f" using same_left_proj by simp
    show "right_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = b \<circ>\<^sub>c f" using same_right_proj by simp
  qed
qed

text \<open>The lemma below corresponds to Exercise 2.1.12 in Halvorson.\<close>
lemma id_cross_prod: "id(X) \<times>\<^sub>f id(Y) = id(X \<times>\<^sub>c Y)"
proof -
  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have idY_type: "id(Y) : Y \<rightarrow> Y" by (rule id_type)
  have h_type: "id(X \<times>\<^sub>c Y) : X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c Y" by (rule id_type)
  have lpXY_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXY_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have left_eq: "left_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = id(X) \<circ>\<^sub>c left_cart_proj(X, Y)"
  proof -
    have "left_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = left_cart_proj(X, Y)"
      using id_right_unit2[OF lpXY_type] by simp
    also have "... = id(X) \<circ>\<^sub>c left_cart_proj(X, Y)"
      using id_left_unit2[OF lpXY_type] by simp
    finally show ?thesis by simp
  qed
  have right_eq: "right_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = id(Y) \<circ>\<^sub>c right_cart_proj(X, Y)"
  proof -
    have "right_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = right_cart_proj(X, Y)"
      using id_right_unit2[OF rpXY_type] by simp
    also have "... = id(Y) \<circ>\<^sub>c right_cart_proj(X, Y)"
      using id_left_unit2[OF rpXY_type] by simp
    finally show ?thesis by simp
  qed
  have result: "id(X \<times>\<^sub>c Y) = id(X) \<times>\<^sub>f id(Y)"
  proof (rule cfunc_cross_prod_unique)
    show "id(X) : X \<rightarrow> X" by (rule idX_type)
    show "id(Y) : Y \<rightarrow> Y" by (rule idY_type)
    show "id(X \<times>\<^sub>c Y) : X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c Y" by (rule h_type)
    show "left_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = id(X) \<circ>\<^sub>c left_cart_proj(X, Y)" by (rule left_eq)
    show "right_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = id(Y) \<circ>\<^sub>c right_cart_proj(X, Y)" by (rule right_eq)
  qed
  show ?thesis using result by simp
qed

text \<open>The lemma below corresponds to Exercise 2.1.14 in Halvorson.\<close>
lemma cfunc_cross_prod_comp_diagonal:
  assumes f_type: "f: X \<rightarrow> Y"
  shows "(f \<times>\<^sub>f f) \<circ>\<^sub>c diagonal(X) = diagonal(Y) \<circ>\<^sub>c f"
  unfolding diagonal_def
proof -
  have f_dom: "domain(f) = X" and f_cod: "codomain(f) = Y"
    using f_type unfolding cfunc_type_def by auto
  have "(f \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>id(X), id(X)\<rangle> = \<langle>f \<circ>\<^sub>c id(X), f \<circ>\<^sub>c id(X)\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF id_type id_type f_type f_type] by simp
  also have "... = \<langle>f, f\<rangle>"
    using f_dom[symmetric] by (simp add: id_right_unit)
  also have "... = \<langle>id(Y) \<circ>\<^sub>c f, id(Y) \<circ>\<^sub>c f\<rangle>"
    using f_cod[symmetric] by (simp add: id_left_unit)
  also have "... = \<langle>id(Y), id(Y)\<rangle> \<circ>\<^sub>c f"
    using cfunc_prod_comp[OF f_type id_type id_type] by simp
  finally show "(f \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>id(X), id(X)\<rangle> = \<langle>id(Y), id(Y)\<rangle> \<circ>\<^sub>c f" by simp
qed

lemma cfunc_cross_prod_comp_cfunc_cross_prod:
  assumes a_type: "a : A \<rightarrow> X" and b_type: "b : B \<rightarrow> Y" and x_type: "x : X \<rightarrow> Z" and y_type: "y : Y \<rightarrow> W"
  shows "(x \<times>\<^sub>f y) \<circ>\<^sub>c (a \<times>\<^sub>f b) = (x \<circ>\<^sub>c a) \<times>\<^sub>f (y \<circ>\<^sub>c b)"
proof -
  have ab_eq: "a \<times>\<^sub>f b = \<langle>a \<circ>\<^sub>c left_cart_proj(A, B), b \<circ>\<^sub>c right_cart_proj(A, B)\<rangle>"
    using a_type b_type cfunc_cross_prod_def2 by auto
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by typecheck_cfuncs
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by typecheck_cfuncs
  have aLP_type: "a \<circ>\<^sub>c left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> X" using a_type lpAB_type comp_type by blast
  have bRP_type: "b \<circ>\<^sub>c right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> Y" using b_type rpAB_type comp_type by blast
  have step: "(x \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c left_cart_proj(A, B), b \<circ>\<^sub>c right_cart_proj(A, B)\<rangle>
      = \<langle>x \<circ>\<^sub>c (a \<circ>\<^sub>c left_cart_proj(A, B)), y \<circ>\<^sub>c (b \<circ>\<^sub>c right_cart_proj(A, B))\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF aLP_type bRP_type x_type y_type] by simp
  have assoc1: "x \<circ>\<^sub>c (a \<circ>\<^sub>c left_cart_proj(A, B)) = (x \<circ>\<^sub>c a) \<circ>\<^sub>c left_cart_proj(A, B)"
    using comp_associative2[OF lpAB_type a_type x_type] by simp
  have assoc2: "y \<circ>\<^sub>c (b \<circ>\<^sub>c right_cart_proj(A, B)) = (y \<circ>\<^sub>c b) \<circ>\<^sub>c right_cart_proj(A, B)"
    using comp_associative2[OF rpAB_type b_type y_type] by simp
  have xa_type: "x \<circ>\<^sub>c a : A \<rightarrow> Z" using x_type a_type comp_type by blast
  have yb_type: "y \<circ>\<^sub>c b : B \<rightarrow> W" using y_type b_type comp_type by blast
  have final_eq: "(x \<circ>\<^sub>c a) \<times>\<^sub>f (y \<circ>\<^sub>c b) = \<langle>(x \<circ>\<^sub>c a) \<circ>\<^sub>c left_cart_proj(A, B), (y \<circ>\<^sub>c b) \<circ>\<^sub>c right_cart_proj(A, B)\<rangle>"
    using xa_type yb_type cfunc_cross_prod_def2 by auto
  show ?thesis
    using ab_eq step assoc1 assoc2 final_eq by simp
qed

lemma cfunc_cross_prod_mono:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes f_mono: "monomorphism(f)" and g_mono: "monomorphism(g)"
  shows "monomorphism(f \<times>\<^sub>f g)"
proof -
  have fg_type: "f \<times>\<^sub>f g : X \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c W"
    using type_assms cfunc_cross_prod_type by auto
  show ?thesis
    unfolding monomorphism_def3[OF fg_type]
  proof (intro allI impI)
    fix x y A
    assume "x : A \<rightarrow> X \<times>\<^sub>c Z \<and> y : A \<rightarrow> X \<times>\<^sub>c Z"
    then have x_type: "x : A \<rightarrow> X \<times>\<^sub>c Z" and y_type: "y : A \<rightarrow> X \<times>\<^sub>c Z" by auto

    obtain x1 x2 where x_expand: "x = \<langle>x1, x2\<rangle>" and x1_type: "x1 : A \<rightarrow> X" and x2_type: "x2 : A \<rightarrow> Z"
      using cart_prod_decomp x_type by blast
    obtain y1 y2 where y_expand: "y = \<langle>y1, y2\<rangle>" and y1_type: "y1 : A \<rightarrow> X" and y2_type: "y2 : A \<rightarrow> Z"
      using cart_prod_decomp y_type by blast

    assume eq: "(f \<times>\<^sub>f g) \<circ>\<^sub>c x = (f \<times>\<^sub>f g) \<circ>\<^sub>c y"
    then have "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x1, x2\<rangle> = (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>y1, y2\<rangle>"
      using x_expand y_expand by simp
    then have prod_eq: "\<langle>f \<circ>\<^sub>c x1, g \<circ>\<^sub>c x2\<rangle> = \<langle>f \<circ>\<^sub>c y1, g \<circ>\<^sub>c y2\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod type_assms x1_type x2_type y1_type y2_type by auto
    have fx1_type: "f \<circ>\<^sub>c x1 : A \<rightarrow> Y" using type_assms x1_type comp_type by blast
    have gx2_type: "g \<circ>\<^sub>c x2 : A \<rightarrow> W" using type_assms x2_type comp_type by blast
    have fy1_type: "f \<circ>\<^sub>c y1 : A \<rightarrow> Y" using type_assms y1_type comp_type by blast
    have gy2_type: "g \<circ>\<^sub>c y2 : A \<rightarrow> W" using type_assms y2_type comp_type by blast
    have proj_eq: "f \<circ>\<^sub>c x1 = f \<circ>\<^sub>c y1 \<and> g \<circ>\<^sub>c x2 = g \<circ>\<^sub>c y2"
      using prod_eq fx1_type gx2_type fy1_type gy2_type cart_prod_eq2 by auto
    have x1_eq: "x1 = y1"
      using proj_eq f_mono x1_type y1_type type_assms(1) monomorphism_def3[OF type_assms(1), THEN iffD1, rule_format, where g=x1 and h=y1 and A=A]
      by auto
    have x2_eq: "x2 = y2"
      using proj_eq g_mono x2_type y2_type type_assms(2) monomorphism_def3[OF type_assms(2), THEN iffD1, rule_format, where g=x2 and h=y2 and A=A]
      by auto
    show "x = y" using x_expand y_expand x1_eq x2_eq by simp
  qed
qed

subsection \<open>Useful Cartesian Product Permuting Functions\<close>

subsubsection \<open>Swapping a Cartesian Product\<close>

definition swap :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "swap(X, Y) = \<langle>right_cart_proj(X, Y), left_cart_proj(X, Y)\<rangle>"

lemma swap_type[type_rule]: "swap(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c X"
  unfolding swap_def by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)

lemma swap_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y"
  shows "swap(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle> = \<langle>y, x\<rangle>"
proof -
  have xy_type: "\<langle>x, y\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
  have "swap(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle> = \<langle>right_cart_proj(X, Y), left_cart_proj(X, Y)\<rangle> \<circ>\<^sub>c \<langle>x, y\<rangle>"
    unfolding swap_def by simp
  also have "... = \<langle>right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle>, left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xy_type right_cart_proj_type left_cart_proj_type] by simp
  also have "... = \<langle>y, x\<rangle>"
    using right_cart_proj_cfunc_prod[OF x_type y_type] left_cart_proj_cfunc_prod[OF x_type y_type] by simp
  finally show ?thesis by simp
qed

lemma swap_cross_prod:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : B \<rightarrow> Y"
  shows "swap(X, Y) \<circ>\<^sub>c (x \<times>\<^sub>f y) = (y \<times>\<^sub>f x) \<circ>\<^sub>c swap(A, B)"
proof -
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by (rule left_cart_proj_type)
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have xLP_type: "x \<circ>\<^sub>c left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> X"
    using x_type lpAB_type comp_type by blast
  have yRP_type: "y \<circ>\<^sub>c right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> Y"
    using y_type rpAB_type comp_type by blast
  have "swap(X, Y) \<circ>\<^sub>c (x \<times>\<^sub>f y) = swap(X, Y) \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj(A, B), y \<circ>\<^sub>c right_cart_proj(A, B)\<rangle>"
    using cfunc_cross_prod_def2[OF x_type y_type] by simp
  also have "... = \<langle>y \<circ>\<^sub>c right_cart_proj(A, B), x \<circ>\<^sub>c left_cart_proj(A, B)\<rangle>"
    using swap_ap[OF xLP_type yRP_type] by simp
  also have "... = (y \<times>\<^sub>f x) \<circ>\<^sub>c \<langle>right_cart_proj(A, B), left_cart_proj(A, B)\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF rpAB_type lpAB_type y_type x_type] by simp
  also have "... = (y \<times>\<^sub>f x) \<circ>\<^sub>c swap(A, B)"
    unfolding swap_def by simp
  finally show ?thesis by simp
qed

lemma swap_idempotent:
  "swap(Y, X) \<circ>\<^sub>c swap(X, Y) = id(X \<times>\<^sub>c Y)"
proof -
  have lpXY_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXY_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have id_XY_eq: "id(X \<times>\<^sub>c Y) = \<langle>left_cart_proj(X, Y), right_cart_proj(X, Y)\<rangle>"
  proof (rule cfunc_prod_unique)
    show "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule lpXY_type)
    show "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule rpXY_type)
    show "id(X \<times>\<^sub>c Y) : X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c Y" by (rule id_type)
    show "left_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = left_cart_proj(X, Y)"
      using id_right_unit2[OF lpXY_type] by simp
    show "right_cart_proj(X, Y) \<circ>\<^sub>c id(X \<times>\<^sub>c Y) = right_cart_proj(X, Y)"
      using id_right_unit2[OF rpXY_type] by simp
  qed
  have "swap(Y, X) \<circ>\<^sub>c swap(X, Y) = swap(Y, X) \<circ>\<^sub>c \<langle>right_cart_proj(X, Y), left_cart_proj(X, Y)\<rangle>"
    unfolding swap_def by simp
  also have "... = \<langle>left_cart_proj(X, Y), right_cart_proj(X, Y)\<rangle>"
    using swap_ap[OF rpXY_type lpXY_type] by simp
  also have "... = id(X \<times>\<^sub>c Y)"
    using id_XY_eq by simp
  finally show ?thesis by simp
qed

lemma swap_mono:
  "monomorphism(swap(X, Y))"
proof -
  have sxy_type: "swap(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c X" by (rule swap_type)
  have syx_type: "swap(Y, X) : Y \<times>\<^sub>c X \<rightarrow> X \<times>\<^sub>c Y" by (rule swap_type)
  have dir1: "swap(Y, X) \<circ>\<^sub>c swap(X, Y) = id(X \<times>\<^sub>c Y)" by (rule swap_idempotent)
  have dir2: "swap(X, Y) \<circ>\<^sub>c swap(Y, X) = id(Y \<times>\<^sub>c X)" by (rule swap_idempotent)
  have iso: "isomorphism(swap(X, Y))"
    unfolding isomorphism_def3[OF sxy_type]
    using syx_type dir1 dir2 by auto
  show ?thesis using iso sxy_type iso_imp_epi_and_monic by auto
qed

subsubsection \<open>Permuting a Cartesian Product to Associate to the Right\<close>

definition associate_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_right(X, Y, Z) =
    \<langle>
      left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z),
      \<langle>
        right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z),
        right_cart_proj(X \<times>\<^sub>c Y, Z)
      \<rangle>
    \<rangle>"

lemma associate_right_type[type_rule]: "associate_right(X, Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
proof -
  have lpXY_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXY_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have lpXYZ_type: "left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have t1: "left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X"
    using lpXY_type lpXYZ_type comp_type by blast
  have t2: "right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y"
    using rpXY_type lpXYZ_type comp_type by blast
  have t3: "\<langle>right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle> : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c Z"
    using t2 rpXYZ_type cfunc_prod_type by auto
  show ?thesis unfolding associate_right_def using t1 t3 cfunc_prod_type by auto
qed

lemma associate_right_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "associate_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>x, \<langle>y, z\<rangle>\<rangle>"
proof -
  have lpXY_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXY_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have lpXYZ_type: "left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have p_type: "left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X"
    using lpXY_type lpXYZ_type comp_type by blast
  have q_type: "right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y"
    using rpXY_type lpXYZ_type comp_type by blast
  have qr_type: "\<langle>right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle> : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c Z"
    using q_type rpXYZ_type cfunc_prod_type by auto
  have xy_type: "\<langle>x, y\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
  have xyz_type: "\<langle>\<langle>x, y\<rangle>, z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z" using xy_type z_type cfunc_prod_type by auto
  have "associate_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
    = \<langle>left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z),
       \<langle>right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    unfolding associate_right_def by simp
  also have "... = \<langle>(left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>,
       \<langle>right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type p_type qr_type] by simp
  also have "... = \<langle>(left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>,
       \<langle>(right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>, right_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type q_type rpXYZ_type] by simp
  also have "... = \<langle>x, \<langle>y, z\<rangle>\<rangle>"
  proof -
    have lpz: "left_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>x, y\<rangle>"
      using left_cart_proj_cfunc_prod[OF xy_type z_type] by simp
    have rpz: "right_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = z"
      using right_cart_proj_cfunc_prod[OF xy_type z_type] by simp
    have p_eq: "(left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = x"
    proof -
      have "(left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
        = left_cart_proj(X, Y) \<circ>\<^sub>c (left_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>)"
        using comp_associative2[OF xyz_type lpXYZ_type lpXY_type] by simp
      also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using lpz by simp
      also have "... = x"
        using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
      finally show ?thesis by simp
    qed
    have q_eq: "(right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = y"
    proof -
      have "(right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
        = right_cart_proj(X, Y) \<circ>\<^sub>c (left_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>)"
        using comp_associative2[OF xyz_type lpXYZ_type rpXY_type] by simp
      also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using lpz by simp
      also have "... = y"
        using right_cart_proj_cfunc_prod[OF x_type y_type] by simp
      finally show ?thesis by simp
    qed
    show ?thesis using p_eq q_eq rpz by simp
  qed
  finally show ?thesis by simp
qed

lemma associate_right_crossprod_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : B \<rightarrow> Y" and z_type: "z : C \<rightarrow> Z"
  shows "associate_right(X, Y, Z) \<circ>\<^sub>c ((x \<times>\<^sub>f y) \<times>\<^sub>f z) = (x \<times>\<^sub>f (y \<times>\<^sub>f z)) \<circ>\<^sub>c associate_right(A, B, C)"
proof -
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by (rule left_cart_proj_type)
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have lpABC_type: "left_cart_proj(A \<times>\<^sub>c B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABC_type: "right_cart_proj(A \<times>\<^sub>c B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> C" by (rule right_cart_proj_type)
  have xy_type: "x \<times>\<^sub>f y : A \<times>\<^sub>c B \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_cross_prod_type by auto
  have yz_type: "y \<times>\<^sub>f z : B \<times>\<^sub>c C \<rightarrow> Y \<times>\<^sub>c Z" using y_type z_type cfunc_cross_prod_type by auto
  have xLPAB_type: "x \<circ>\<^sub>c left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> X" using x_type lpAB_type comp_type by blast
  have yRPAB_type: "y \<circ>\<^sub>c right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> Y" using y_type rpAB_type comp_type by blast
  have lpABLPABC_type: "left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> A"
    using lpAB_type lpABC_type comp_type by blast
  have rpABLPABC_type: "right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> B"
    using rpAB_type lpABC_type comp_type by blast
  have xLPABLPABC_type: "x \<circ>\<^sub>c left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> X"
    using x_type lpABLPABC_type comp_type by blast
  have yRPABLPABC_type: "y \<circ>\<^sub>c right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> Y"
    using y_type rpABLPABC_type comp_type by blast
  have zRPABC_type: "z \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> Z"
    using z_type rpABC_type comp_type by blast
  have inner_type: "\<langle>right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), right_cart_proj(A \<times>\<^sub>c B, C)\<rangle> : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> B \<times>\<^sub>c C"
    using rpABLPABC_type rpABC_type cfunc_prod_type by auto
  have "associate_right(X, Y, Z) \<circ>\<^sub>c ((x \<times>\<^sub>f y) \<times>\<^sub>f z)
    = associate_right(X, Y, Z) \<circ>\<^sub>c \<langle>(x \<times>\<^sub>f y) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), z \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C)\<rangle>"
    using cfunc_cross_prod_def2[OF xy_type z_type] by simp
  also have "... = associate_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x \<circ>\<^sub>c left_cart_proj(A, B), y \<circ>\<^sub>c right_cart_proj(A, B)\<rangle> \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), z \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C)\<rangle>"
    using cfunc_cross_prod_def2[OF x_type y_type] by simp
  also have "... = associate_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x \<circ>\<^sub>c left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), y \<circ>\<^sub>c right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C)\<rangle>, z \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C)\<rangle>"
  proof -
    have "\<langle>x \<circ>\<^sub>c left_cart_proj(A, B), y \<circ>\<^sub>c right_cart_proj(A, B)\<rangle> \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C)
      = \<langle>(x \<circ>\<^sub>c left_cart_proj(A, B)) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), (y \<circ>\<^sub>c right_cart_proj(A, B)) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C)\<rangle>"
      using cfunc_prod_comp[OF lpABC_type xLPAB_type yRPAB_type] by simp
    then show ?thesis
      using comp_associative2[OF lpABC_type lpAB_type x_type] comp_associative2[OF lpABC_type rpAB_type y_type] by simp
  qed
  also have "... = \<langle>x \<circ>\<^sub>c left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), \<langle>y \<circ>\<^sub>c right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), z \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C)\<rangle>\<rangle>"
    using associate_right_ap[OF xLPABLPABC_type yRPABLPABC_type zRPABC_type] by simp
  also have "... = \<langle>x \<circ>\<^sub>c left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), (y \<times>\<^sub>f z) \<circ>\<^sub>c \<langle>right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), right_cart_proj(A \<times>\<^sub>c B, C)\<rangle>\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF rpABLPABC_type rpABC_type y_type z_type] by simp
  also have "... = (x \<times>\<^sub>f (y \<times>\<^sub>f z)) \<circ>\<^sub>c \<langle>left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), \<langle>right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C), right_cart_proj(A \<times>\<^sub>c B, C)\<rangle>\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF lpABLPABC_type inner_type x_type yz_type] by simp
  also have "... = (x \<times>\<^sub>f (y \<times>\<^sub>f z)) \<circ>\<^sub>c associate_right(A, B, C)"
    unfolding associate_right_def by simp
  finally show ?thesis by simp
qed

subsubsection \<open>Permuting a Cartesian Product to Associate to the Left\<close>

definition associate_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_left(X, Y, Z) =
    \<langle>
      \<langle>
        left_cart_proj(X, Y \<times>\<^sub>c Z),
        left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)
      \<rangle>,
      right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)
    \<rangle>"

lemma associate_left_type[type_rule]: "associate_left(X, Y, Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
proof -
  have lpXYZ_type: "left_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y \<times>\<^sub>c Z" by (rule right_cart_proj_type)
  have lpYZ_type: "left_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Y" by (rule left_cart_proj_type)
  have rpYZ_type: "right_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have t1: "left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y"
    using lpYZ_type rpXYZ_type comp_type by blast
  have t2: "right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Z"
    using rpYZ_type rpXYZ_type comp_type by blast
  have t3: "\<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle> : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Y"
    using lpXYZ_type t1 cfunc_prod_type by auto
  show ?thesis unfolding associate_left_def using t3 t2 cfunc_prod_type by auto
qed

lemma associate_left_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "associate_left(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>\<langle>x, y\<rangle>, z\<rangle>"
proof -
  have lpXYZ_type: "left_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y \<times>\<^sub>c Z" by (rule right_cart_proj_type)
  have lpYZ_type: "left_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Y" by (rule left_cart_proj_type)
  have rpYZ_type: "right_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have p_type: "left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y"
    using lpYZ_type rpXYZ_type comp_type by blast
  have q_type: "right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Z"
    using rpYZ_type rpXYZ_type comp_type by blast
  have lp_p_type: "\<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle> : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Y"
    using lpXYZ_type p_type cfunc_prod_type by auto
  have yz_type: "\<langle>y, z\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z" using y_type z_type cfunc_prod_type by auto
  have xyz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)" using x_type yz_type cfunc_prod_type by auto
  have "associate_left(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
    = \<langle>\<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle>,
       right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding associate_left_def by simp
  also have "... = \<langle>\<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
       (right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type lp_p_type q_type] by simp
  also have "... = \<langle>\<langle>left_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>, (left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>,
       (right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type lpXYZ_type p_type] by simp
  also have "... = \<langle>\<langle>x, y\<rangle>, z\<rangle>"
  proof -
    have rpz: "right_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>y, z\<rangle>"
      using right_cart_proj_cfunc_prod[OF x_type yz_type] by simp
    have lp_eq: "left_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = x"
      using left_cart_proj_cfunc_prod[OF x_type yz_type] by simp
    have p_eq: "(left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = y"
    proof -
      have "(left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
        = left_cart_proj(Y, Z) \<circ>\<^sub>c (right_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>)"
        using comp_associative2[OF xyz_type rpXYZ_type lpYZ_type] by simp
      also have "... = left_cart_proj(Y, Z) \<circ>\<^sub>c \<langle>y, z\<rangle>"
        using rpz by simp
      also have "... = y"
        using left_cart_proj_cfunc_prod[OF y_type z_type] by simp
      finally show ?thesis by simp
    qed
    have q_eq: "(right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = z"
    proof -
      have "(right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
        = right_cart_proj(Y, Z) \<circ>\<^sub>c (right_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>)"
        using comp_associative2[OF xyz_type rpXYZ_type rpYZ_type] by simp
      also have "... = right_cart_proj(Y, Z) \<circ>\<^sub>c \<langle>y, z\<rangle>"
        using rpz by simp
      also have "... = z"
        using right_cart_proj_cfunc_prod[OF y_type z_type] by simp
      finally show ?thesis by simp
    qed
    show ?thesis using lp_eq p_eq q_eq by simp
  qed
  finally show ?thesis by simp
qed

lemma right_left:
  "associate_right(A, B, C) \<circ>\<^sub>c associate_left(A, B, C) = id(A \<times>\<^sub>c (B \<times>\<^sub>c C))"
proof -
  have id_type': "id(A \<times>\<^sub>c (B \<times>\<^sub>c C)) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c (B \<times>\<^sub>c C)" by (rule id_type)
  obtain x1 w where id_decomp: "id(A \<times>\<^sub>c (B \<times>\<^sub>c C)) = \<langle>x1, w\<rangle>"
      and x1_type: "x1 : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> A" and w_type: "w : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> B \<times>\<^sub>c C"
    using cart_prod_decomp[OF id_type'] by blast
  obtain y z where w_decomp: "w = \<langle>y, z\<rangle>"
      and y_type: "y : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> B" and z_type: "z : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> C"
    using cart_prod_decomp[OF w_type] by blast
  have id_eq: "id(A \<times>\<^sub>c (B \<times>\<^sub>c C)) = \<langle>x1, \<langle>y, z\<rangle>\<rangle>" using id_decomp w_decomp by simp
  have alr_type: "associate_left(A, B, C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> (A \<times>\<^sub>c B) \<times>\<^sub>c C" by (rule associate_left_type)
  have "associate_right(A, B, C) \<circ>\<^sub>c associate_left(A, B, C)
    = associate_right(A, B, C) \<circ>\<^sub>c associate_left(A, B, C) \<circ>\<^sub>c id(A \<times>\<^sub>c (B \<times>\<^sub>c C))"
    using id_right_unit2[OF alr_type] by simp
  also have "... = associate_right(A, B, C) \<circ>\<^sub>c associate_left(A, B, C) \<circ>\<^sub>c \<langle>x1, \<langle>y, z\<rangle>\<rangle>"
    using id_eq by simp
  also have "... = associate_right(A, B, C) \<circ>\<^sub>c \<langle>\<langle>x1, y\<rangle>, z\<rangle>"
    using associate_left_ap[OF x1_type y_type z_type] by simp
  also have "... = \<langle>x1, \<langle>y, z\<rangle>\<rangle>"
    using associate_right_ap[OF x1_type y_type z_type] by simp
  also have "... = id(A \<times>\<^sub>c (B \<times>\<^sub>c C))"
    using id_eq by simp
  finally show ?thesis by simp
qed

lemma left_right:
  "associate_left(A, B, C) \<circ>\<^sub>c associate_right(A, B, C) = id((A \<times>\<^sub>c B) \<times>\<^sub>c C)"
proof -
  have id_type': "id((A \<times>\<^sub>c B) \<times>\<^sub>c C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> (A \<times>\<^sub>c B) \<times>\<^sub>c C" by (rule id_type)
  obtain w z where id_decomp: "id((A \<times>\<^sub>c B) \<times>\<^sub>c C) = \<langle>w, z\<rangle>"
      and w_type: "w : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> A \<times>\<^sub>c B" and z_type: "z : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> C"
    using cart_prod_decomp[OF id_type'] by blast
  obtain x y where w_decomp: "w = \<langle>x, y\<rangle>"
      and x_type: "x : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> A" and y_type: "y : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> B"
    using cart_prod_decomp[OF w_type] by blast
  have id_eq: "id((A \<times>\<^sub>c B) \<times>\<^sub>c C) = \<langle>\<langle>x, y\<rangle>, z\<rangle>" using id_decomp w_decomp by simp
  have arr_type: "associate_right(A, B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> A \<times>\<^sub>c (B \<times>\<^sub>c C)" by (rule associate_right_type)
  have "associate_left(A, B, C) \<circ>\<^sub>c associate_right(A, B, C)
    = associate_left(A, B, C) \<circ>\<^sub>c associate_right(A, B, C) \<circ>\<^sub>c id((A \<times>\<^sub>c B) \<times>\<^sub>c C)"
    using id_right_unit2[OF arr_type] by simp
  also have "... = associate_left(A, B, C) \<circ>\<^sub>c associate_right(A, B, C) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    using id_eq by simp
  also have "... = associate_left(A, B, C) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    using associate_right_ap[OF x_type y_type z_type] by simp
  also have "... = \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    using associate_left_ap[OF x_type y_type z_type] by simp
  also have "... = id((A \<times>\<^sub>c B) \<times>\<^sub>c C)"
    using id_eq by simp
  finally show ?thesis by simp
qed

lemma product_associates:
  "A \<times>\<^sub>c (B \<times>\<^sub>c C) \<cong> (A \<times>\<^sub>c B) \<times>\<^sub>c C"
proof -
  have arr_type: "associate_right(A, B, C) : (A \<times>\<^sub>c B) \<times>\<^sub>c C \<rightarrow> A \<times>\<^sub>c (B \<times>\<^sub>c C)" by (rule associate_right_type)
  have alr_type: "associate_left(A, B, C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> (A \<times>\<^sub>c B) \<times>\<^sub>c C" by (rule associate_left_type)
  have iso: "isomorphism(associate_left(A, B, C))"
    unfolding isomorphism_def3[OF alr_type]
    using arr_type right_left left_right by auto
  show ?thesis unfolding is_isomorphic_def using alr_type iso by auto
qed

lemma associate_left_crossprod_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : B \<rightarrow> Y" and z_type: "z : C \<rightarrow> Z"
  shows "associate_left(X, Y, Z) \<circ>\<^sub>c (x \<times>\<^sub>f (y \<times>\<^sub>f z)) = ((x \<times>\<^sub>f y) \<times>\<^sub>f z) \<circ>\<^sub>c associate_left(A, B, C)"
proof -
  have lpBC_type: "left_cart_proj(B, C) : B \<times>\<^sub>c C \<rightarrow> B" by (rule left_cart_proj_type)
  have rpBC_type: "right_cart_proj(B, C) : B \<times>\<^sub>c C \<rightarrow> C" by (rule right_cart_proj_type)
  have lpABC_type: "left_cart_proj(A, B \<times>\<^sub>c C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> A" by (rule left_cart_proj_type)
  have rpABC_type: "right_cart_proj(A, B \<times>\<^sub>c C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> B \<times>\<^sub>c C" by (rule right_cart_proj_type)
  have xy_type: "x \<times>\<^sub>f y : A \<times>\<^sub>c B \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_cross_prod_type by auto
  have yz_type: "y \<times>\<^sub>f z : B \<times>\<^sub>c C \<rightarrow> Y \<times>\<^sub>c Z" using y_type z_type cfunc_cross_prod_type by auto
  have yLPBC_type: "y \<circ>\<^sub>c left_cart_proj(B, C) : B \<times>\<^sub>c C \<rightarrow> Y" using y_type lpBC_type comp_type by blast
  have zRPBC_type: "z \<circ>\<^sub>c right_cart_proj(B, C) : B \<times>\<^sub>c C \<rightarrow> Z" using z_type rpBC_type comp_type by blast
  have lpBCRPABC_type: "left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> B"
    using lpBC_type rpABC_type comp_type by blast
  have rpBCRPABC_type: "right_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> C"
    using rpBC_type rpABC_type comp_type by blast
  have xLPABC_type: "x \<circ>\<^sub>c left_cart_proj(A, B \<times>\<^sub>c C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> X"
    using x_type lpABC_type comp_type by blast
  have yLPBCRPABC_type: "y \<circ>\<^sub>c left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> Y"
    using y_type lpBCRPABC_type comp_type by blast
  have zRPBCRPABC_type: "z \<circ>\<^sub>c right_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C) : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> Z"
    using z_type rpBCRPABC_type comp_type by blast
  have inner_type: "\<langle>left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C), right_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle> : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> B \<times>\<^sub>c C"
    using lpBCRPABC_type rpBCRPABC_type cfunc_prod_type by auto
  have "associate_left(X, Y, Z) \<circ>\<^sub>c (x \<times>\<^sub>f (y \<times>\<^sub>f z))
    = associate_left(X, Y, Z) \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj(A, B \<times>\<^sub>c C), (y \<times>\<^sub>f z) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>"
    using cfunc_cross_prod_def2[OF x_type yz_type] by simp
  also have "... = associate_left(X, Y, Z) \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj(A, B \<times>\<^sub>c C), \<langle>y \<circ>\<^sub>c left_cart_proj(B, C), z \<circ>\<^sub>c right_cart_proj(B, C)\<rangle> \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>"
    using cfunc_cross_prod_def2[OF y_type z_type] by simp
  also have "... = associate_left(X, Y, Z) \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj(A, B \<times>\<^sub>c C), \<langle>y \<circ>\<^sub>c left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C), z \<circ>\<^sub>c right_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>\<rangle>"
  proof -
    have "\<langle>y \<circ>\<^sub>c left_cart_proj(B, C), z \<circ>\<^sub>c right_cart_proj(B, C)\<rangle> \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)
      = \<langle>(y \<circ>\<^sub>c left_cart_proj(B, C)) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C), (z \<circ>\<^sub>c right_cart_proj(B, C)) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>"
      using cfunc_prod_comp[OF rpABC_type yLPBC_type zRPBC_type] by simp
    then show ?thesis
      using comp_associative2[OF rpABC_type lpBC_type y_type] comp_associative2[OF rpABC_type rpBC_type z_type] by simp
  qed
  also have "... = \<langle>\<langle>x \<circ>\<^sub>c left_cart_proj(A, B \<times>\<^sub>c C), y \<circ>\<^sub>c left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>, z \<circ>\<^sub>c right_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>"
    using associate_left_ap[OF xLPABC_type yLPBCRPABC_type zRPBCRPABC_type] by simp
  also have "... = \<langle>(x \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>left_cart_proj(A, B \<times>\<^sub>c C), left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>, z \<circ>\<^sub>c right_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod[OF lpABC_type lpBCRPABC_type x_type y_type] by simp
  also have "... = ((x \<times>\<^sub>f y) \<times>\<^sub>f z) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj(A, B \<times>\<^sub>c C), left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>, right_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle>"
  proof -
    have lp_p_type: "\<langle>left_cart_proj(A, B \<times>\<^sub>c C), left_cart_proj(B, C) \<circ>\<^sub>c right_cart_proj(A, B \<times>\<^sub>c C)\<rangle> : A \<times>\<^sub>c (B \<times>\<^sub>c C) \<rightarrow> A \<times>\<^sub>c B"
      using lpABC_type lpBCRPABC_type cfunc_prod_type by auto
    show ?thesis
      using cfunc_cross_prod_comp_cfunc_prod[OF lp_p_type rpBCRPABC_type xy_type z_type] by simp
  qed
  also have "... = ((x \<times>\<^sub>f y) \<times>\<^sub>f z) \<circ>\<^sub>c associate_left(A, B, C)"
    unfolding associate_left_def by simp
  finally show ?thesis by simp
qed

subsubsection \<open>Distributing over a Cartesian Product from the Right\<close>

definition distribute_right_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right_left(X, Y, Z) =
    \<langle>left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle>"

lemma distribute_right_left_type[type_rule]:
  "distribute_right_left(X, Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Z"
proof -
  have lpXY_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have lpXYZ_type: "left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have p_type: "left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X"
    using lpXY_type lpXYZ_type comp_type by blast
  show ?thesis unfolding distribute_right_left_def using p_type rpXYZ_type cfunc_prod_type by auto
qed

lemma distribute_right_left_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "distribute_right_left(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>x, z\<rangle>"
proof -
  have lpXY_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have lpXYZ_type: "left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have p_type: "left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X"
    using lpXY_type lpXYZ_type comp_type by blast
  have xy_type: "\<langle>x, y\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
  have xyz_type: "\<langle>\<langle>x, y\<rangle>, z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z" using xy_type z_type cfunc_prod_type by auto
  have "distribute_right_left(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
    = \<langle>left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    unfolding distribute_right_left_def by simp
  also have "... = \<langle>(left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>, right_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type p_type rpXYZ_type] by simp
  also have "... = \<langle>x, z\<rangle>"
  proof -
    have "(left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
      = left_cart_proj(X, Y) \<circ>\<^sub>c (left_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>)"
      using comp_associative2[OF xyz_type lpXYZ_type lpXY_type] by simp
    also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle>"
      using left_cart_proj_cfunc_prod[OF xy_type z_type] by simp
    also have "... = x"
      using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
    finally have p_eq: "(left_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = x" by simp
    have rp_eq: "right_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = z"
      using right_cart_proj_cfunc_prod[OF xy_type z_type] by simp
    show ?thesis using p_eq rp_eq by simp
  qed
  finally show ?thesis by simp
qed

definition distribute_right_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right_right(X, Y, Z) =
    \<langle>right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle>"

lemma distribute_right_right_type[type_rule]:
  "distribute_right_right(X, Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c Z"
proof -
  have rpXY_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have lpXYZ_type: "left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have q_type: "right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y"
    using rpXY_type lpXYZ_type comp_type by blast
  show ?thesis unfolding distribute_right_right_def using q_type rpXYZ_type cfunc_prod_type by auto
qed

lemma distribute_right_right_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "distribute_right_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>y, z\<rangle>"
proof -
  have rpXY_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have lpXYZ_type: "left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Y" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have q_type: "right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y"
    using rpXY_type lpXYZ_type comp_type by blast
  have xy_type: "\<langle>x, y\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
  have xyz_type: "\<langle>\<langle>x, y\<rangle>, z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z" using xy_type z_type cfunc_prod_type by auto
  have "distribute_right_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
    = \<langle>right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z), right_cart_proj(X \<times>\<^sub>c Y, Z)\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    unfolding distribute_right_right_def by simp
  also have "... = \<langle>(right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>, right_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type q_type rpXYZ_type] by simp
  also have "... = \<langle>y, z\<rangle>"
  proof -
    have "(right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
      = right_cart_proj(X, Y) \<circ>\<^sub>c (left_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>)"
      using comp_associative2[OF xyz_type lpXYZ_type rpXY_type] by simp
    also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x, y\<rangle>"
      using left_cart_proj_cfunc_prod[OF xy_type z_type] by simp
    also have "... = y"
      using right_cart_proj_cfunc_prod[OF x_type y_type] by simp
    finally have q_eq: "(right_cart_proj(X, Y) \<circ>\<^sub>c left_cart_proj(X \<times>\<^sub>c Y, Z)) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = y" by simp
    have rp_eq: "right_cart_proj(X \<times>\<^sub>c Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = z"
      using right_cart_proj_cfunc_prod[OF xy_type z_type] by simp
    show ?thesis using q_eq rp_eq by simp
  qed
  finally show ?thesis by simp
qed

definition distribute_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right(X, Y, Z) = \<langle>distribute_right_left(X, Y, Z), distribute_right_right(X, Y, Z)\<rangle>"

lemma distribute_right_type[type_rule]:
  "distribute_right(X, Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  unfolding distribute_right_def
  using distribute_right_left_type distribute_right_right_type cfunc_prod_type by auto

lemma distribute_right_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "distribute_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>\<langle>x, z\<rangle>, \<langle>y, z\<rangle>\<rangle>"
proof -
  have xy_type: "\<langle>x, y\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
  have xyz_type: "\<langle>\<langle>x, y\<rangle>, z\<rangle> : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z" using xy_type z_type cfunc_prod_type by auto
  have drl_type: "distribute_right_left(X, Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Z" by (rule distribute_right_left_type)
  have drr_type: "distribute_right_right(X, Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c Z" by (rule distribute_right_right_type)
  have "distribute_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>
    = \<langle>distribute_right_left(X, Y, Z), distribute_right_right(X, Y, Z)\<rangle> \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    unfolding distribute_right_def by simp
  also have "... = \<langle>distribute_right_left(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>, distribute_right_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type drl_type drr_type] by simp
  also have "... = \<langle>\<langle>x, z\<rangle>, \<langle>y, z\<rangle>\<rangle>"
    using distribute_right_left_ap[OF x_type y_type z_type] distribute_right_right_ap[OF x_type y_type z_type] by simp
  finally show ?thesis by simp
qed

lemma distribute_right_mono:
  "monomorphism(distribute_right(X, Y, Z))"
proof -
  have dr_type: "distribute_right(X, Y, Z) : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (Y \<times>\<^sub>c Z)" by (rule distribute_right_type)
  show ?thesis
    unfolding monomorphism_def3[OF dr_type]
  proof (intro allI impI)
    fix g h A
    assume "g : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<and> h : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
    then have g_type: "g : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z" and h_type: "h : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z" by auto
    obtain g12 g3 where g_decomp1: "g = \<langle>g12, g3\<rangle>" and g12_type: "g12 : A \<rightarrow> X \<times>\<^sub>c Y" and g3_type: "g3 : A \<rightarrow> Z"
      using cart_prod_decomp[OF g_type] by blast
    obtain g1 g2 where g_decomp2: "g12 = \<langle>g1, g2\<rangle>" and g1_type: "g1 : A \<rightarrow> X" and g2_type: "g2 : A \<rightarrow> Y"
      using cart_prod_decomp[OF g12_type] by blast
    obtain h12 h3 where h_decomp1: "h = \<langle>h12, h3\<rangle>" and h12_type: "h12 : A \<rightarrow> X \<times>\<^sub>c Y" and h3_type: "h3 : A \<rightarrow> Z"
      using cart_prod_decomp[OF h_type] by blast
    obtain h1 h2 where h_decomp2: "h12 = \<langle>h1, h2\<rangle>" and h1_type: "h1 : A \<rightarrow> X" and h2_type: "h2 : A \<rightarrow> Y"
      using cart_prod_decomp[OF h12_type] by blast
    have g_eq: "g = \<langle>\<langle>g1, g2\<rangle>, g3\<rangle>" using g_decomp1 g_decomp2 by simp
    have h_eq: "h = \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>" using h_decomp1 h_decomp2 by simp
    assume dr_eq: "distribute_right(X, Y, Z) \<circ>\<^sub>c g = distribute_right(X, Y, Z) \<circ>\<^sub>c h"
    then have "distribute_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>g1, g2\<rangle>, g3\<rangle> = distribute_right(X, Y, Z) \<circ>\<^sub>c \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>"
      using g_eq h_eq by simp
    then have pairs_eq: "\<langle>\<langle>g1, g3\<rangle>, \<langle>g2, g3\<rangle>\<rangle> = \<langle>\<langle>h1, h3\<rangle>, \<langle>h2, h3\<rangle>\<rangle>"
      using distribute_right_ap[OF g1_type g2_type g3_type] distribute_right_ap[OF h1_type h2_type h3_type] by simp
    have g13_type: "\<langle>g1, g3\<rangle> : A \<rightarrow> X \<times>\<^sub>c Z" using g1_type g3_type cfunc_prod_type by auto
    have g23_type: "\<langle>g2, g3\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z" using g2_type g3_type cfunc_prod_type by auto
    have h13_type: "\<langle>h1, h3\<rangle> : A \<rightarrow> X \<times>\<^sub>c Z" using h1_type h3_type cfunc_prod_type by auto
    have h23_type: "\<langle>h2, h3\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z" using h2_type h3_type cfunc_prod_type by auto
    have split_eq: "\<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle> \<and> \<langle>g2, g3\<rangle> = \<langle>h2, h3\<rangle>"
      using pairs_eq cart_prod_eq2[OF g13_type g23_type h13_type h23_type] by auto
    have g13_eq: "\<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle>" using split_eq by simp
    have g23_eq: "\<langle>g2, g3\<rangle> = \<langle>h2, h3\<rangle>" using split_eq by simp
    have g1_eq: "g1 = h1" using g13_eq cart_prod_eq2[OF g1_type g3_type h1_type h3_type] by auto
    have g3_eq: "g3 = h3" using g13_eq cart_prod_eq2[OF g1_type g3_type h1_type h3_type] by auto
    have g2_eq: "g2 = h2" using g23_eq cart_prod_eq2[OF g2_type g3_type h2_type h3_type] by auto
    show "g = h" using g_eq h_eq g1_eq g2_eq g3_eq by simp
  qed
qed

subsubsection \<open>Distributing over a Cartesian Product from the Left\<close>

definition distribute_left_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left_left(X, Y, Z) =
    \<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle>"

lemma distribute_left_left_type[type_rule]:
  "distribute_left_left(X, Y, Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Y"
proof -
  have lpXYZ_type: "left_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y \<times>\<^sub>c Z" by (rule right_cart_proj_type)
  have lpYZ_type: "left_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Y" by (rule left_cart_proj_type)
  have p_type: "left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y"
    using lpYZ_type rpXYZ_type comp_type by blast
  show ?thesis unfolding distribute_left_left_def using lpXYZ_type p_type cfunc_prod_type by auto
qed

lemma distribute_left_left_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "distribute_left_left(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>x, y\<rangle>"
proof -
  have lpXYZ_type: "left_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y \<times>\<^sub>c Z" by (rule right_cart_proj_type)
  have lpYZ_type: "left_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Y" by (rule left_cart_proj_type)
  have p_type: "left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y"
    using lpYZ_type rpXYZ_type comp_type by blast
  have yz_type: "\<langle>y, z\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z" using y_type z_type cfunc_prod_type by auto
  have xyz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)" using x_type yz_type cfunc_prod_type by auto
  have "distribute_left_left(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
    = \<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding distribute_left_left_def by simp
  also have "... = \<langle>left_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>, (left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type lpXYZ_type p_type] by simp
  also have "... = \<langle>x, y\<rangle>"
  proof -
    have lp_eq: "left_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = x"
      using left_cart_proj_cfunc_prod[OF x_type yz_type] by simp
    have "(left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
      = left_cart_proj(Y, Z) \<circ>\<^sub>c (right_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>)"
      using comp_associative2[OF xyz_type rpXYZ_type lpYZ_type] by simp
    also have "... = left_cart_proj(Y, Z) \<circ>\<^sub>c \<langle>y, z\<rangle>"
      using right_cart_proj_cfunc_prod[OF x_type yz_type] by simp
    also have "... = y"
      using left_cart_proj_cfunc_prod[OF y_type z_type] by simp
    finally have p_eq: "(left_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = y" by simp
    show ?thesis using lp_eq p_eq by simp
  qed
  finally show ?thesis by simp
qed

definition distribute_left_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left_right(X, Y, Z) =
    \<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle>"

lemma distribute_left_right_type[type_rule]:
  "distribute_left_right(X, Y, Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Z"
proof -
  have lpXYZ_type: "left_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y \<times>\<^sub>c Z" by (rule right_cart_proj_type)
  have rpYZ_type: "right_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have q_type: "right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Z"
    using rpYZ_type rpXYZ_type comp_type by blast
  show ?thesis unfolding distribute_left_right_def using lpXYZ_type q_type cfunc_prod_type by auto
qed

lemma distribute_left_right_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "distribute_left_right(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>x, z\<rangle>"
proof -
  have lpXYZ_type: "left_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X" by (rule left_cart_proj_type)
  have rpXYZ_type: "right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Y \<times>\<^sub>c Z" by (rule right_cart_proj_type)
  have rpYZ_type: "right_cart_proj(Y, Z) : Y \<times>\<^sub>c Z \<rightarrow> Z" by (rule right_cart_proj_type)
  have q_type: "right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> Z"
    using rpYZ_type rpXYZ_type comp_type by blast
  have yz_type: "\<langle>y, z\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z" using y_type z_type cfunc_prod_type by auto
  have xyz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)" using x_type yz_type cfunc_prod_type by auto
  have "distribute_left_right(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
    = \<langle>left_cart_proj(X, Y \<times>\<^sub>c Z), right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding distribute_left_right_def by simp
  also have "... = \<langle>left_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>, (right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type lpXYZ_type q_type] by simp
  also have "... = \<langle>x, z\<rangle>"
  proof -
    have lp_eq: "left_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = x"
      using left_cart_proj_cfunc_prod[OF x_type yz_type] by simp
    have "(right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
      = right_cart_proj(Y, Z) \<circ>\<^sub>c (right_cart_proj(X, Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>)"
      using comp_associative2[OF xyz_type rpXYZ_type rpYZ_type] by simp
    also have "... = right_cart_proj(Y, Z) \<circ>\<^sub>c \<langle>y, z\<rangle>"
      using right_cart_proj_cfunc_prod[OF x_type yz_type] by simp
    also have "... = z"
      using right_cart_proj_cfunc_prod[OF y_type z_type] by simp
    finally have q_eq: "(right_cart_proj(Y, Z) \<circ>\<^sub>c right_cart_proj(X, Y \<times>\<^sub>c Z)) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = z" by simp
    show ?thesis using lp_eq q_eq by simp
  qed
  finally show ?thesis by simp
qed

definition distribute_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left(X, Y, Z) = \<langle>distribute_left_left(X, Y, Z), distribute_left_right(X, Y, Z)\<rangle>"

lemma distribute_left_type[type_rule]:
  "distribute_left(X, Y, Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
  unfolding distribute_left_def
  using distribute_left_left_type distribute_left_right_type cfunc_prod_type by auto

lemma distribute_left_ap:
  assumes x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y" and z_type: "z : A \<rightarrow> Z"
  shows "distribute_left(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>\<langle>x, y\<rangle>, \<langle>x, z\<rangle>\<rangle>"
proof -
  have yz_type: "\<langle>y, z\<rangle> : A \<rightarrow> Y \<times>\<^sub>c Z" using y_type z_type cfunc_prod_type by auto
  have xyz_type: "\<langle>x, \<langle>y, z\<rangle>\<rangle> : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)" using x_type yz_type cfunc_prod_type by auto
  have dll_type: "distribute_left_left(X, Y, Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Y" by (rule distribute_left_left_type)
  have dlr_type: "distribute_left_right(X, Y, Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Z" by (rule distribute_left_right_type)
  have "distribute_left(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
    = \<langle>distribute_left_left(X, Y, Z), distribute_left_right(X, Y, Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>"
    unfolding distribute_left_def by simp
  also have "... = \<langle>distribute_left_left(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>, distribute_left_right(X, Y, Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF xyz_type dll_type dlr_type] by simp
  also have "... = \<langle>\<langle>x, y\<rangle>, \<langle>x, z\<rangle>\<rangle>"
    using distribute_left_left_ap[OF x_type y_type z_type] distribute_left_right_ap[OF x_type y_type z_type] by simp
  finally show ?thesis by simp
qed

lemma distribute_left_mono:
  "monomorphism(distribute_left(X, Y, Z))"
proof -
  have dl_type: "distribute_left(X, Y, Z) : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c (X \<times>\<^sub>c Z)" by (rule distribute_left_type)
  show ?thesis
    unfolding monomorphism_def3[OF dl_type]
  proof (intro allI impI)
    fix g h A
    assume "g : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<and> h : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
    then have g_type: "g : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)" and h_type: "h : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)" by auto
    obtain g1 g23 where g_decomp1: "g = \<langle>g1, g23\<rangle>" and g1_type: "g1 : A \<rightarrow> X" and g23_type: "g23 : A \<rightarrow> Y \<times>\<^sub>c Z"
      using cart_prod_decomp[OF g_type] by blast
    obtain g2 g3 where g_decomp2: "g23 = \<langle>g2, g3\<rangle>" and g2_type: "g2 : A \<rightarrow> Y" and g3_type: "g3 : A \<rightarrow> Z"
      using cart_prod_decomp[OF g23_type] by blast
    obtain h1 h23 where h_decomp1: "h = \<langle>h1, h23\<rangle>" and h1_type: "h1 : A \<rightarrow> X" and h23_type: "h23 : A \<rightarrow> Y \<times>\<^sub>c Z"
      using cart_prod_decomp[OF h_type] by blast
    obtain h2 h3 where h_decomp2: "h23 = \<langle>h2, h3\<rangle>" and h2_type: "h2 : A \<rightarrow> Y" and h3_type: "h3 : A \<rightarrow> Z"
      using cart_prod_decomp[OF h23_type] by blast
    have g_eq: "g = \<langle>g1, \<langle>g2, g3\<rangle>\<rangle>" using g_decomp1 g_decomp2 by simp
    have h_eq: "h = \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>" using h_decomp1 h_decomp2 by simp
    assume dl_eq: "distribute_left(X, Y, Z) \<circ>\<^sub>c g = distribute_left(X, Y, Z) \<circ>\<^sub>c h"
    then have "distribute_left(X, Y, Z) \<circ>\<^sub>c \<langle>g1, \<langle>g2, g3\<rangle>\<rangle> = distribute_left(X, Y, Z) \<circ>\<^sub>c \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>"
      using g_eq h_eq by simp
    then have pairs_eq: "\<langle>\<langle>g1, g2\<rangle>, \<langle>g1, g3\<rangle>\<rangle> = \<langle>\<langle>h1, h2\<rangle>, \<langle>h1, h3\<rangle>\<rangle>"
      using distribute_left_ap[OF g1_type g2_type g3_type] distribute_left_ap[OF h1_type h2_type h3_type] by simp
    have g12_type: "\<langle>g1, g2\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using g1_type g2_type cfunc_prod_type by auto
    have g13_type: "\<langle>g1, g3\<rangle> : A \<rightarrow> X \<times>\<^sub>c Z" using g1_type g3_type cfunc_prod_type by auto
    have h12_type: "\<langle>h1, h2\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using h1_type h2_type cfunc_prod_type by auto
    have h13_type: "\<langle>h1, h3\<rangle> : A \<rightarrow> X \<times>\<^sub>c Z" using h1_type h3_type cfunc_prod_type by auto
    have split_eq: "\<langle>g1, g2\<rangle> = \<langle>h1, h2\<rangle> \<and> \<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle>"
      using pairs_eq cart_prod_eq2[OF g12_type g13_type h12_type h13_type] by auto
    have g12_eq: "\<langle>g1, g2\<rangle> = \<langle>h1, h2\<rangle>" using split_eq by simp
    have g13_eq: "\<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle>" using split_eq by simp
    have g1_eq: "g1 = h1" using g12_eq cart_prod_eq2[OF g1_type g2_type h1_type h2_type] by auto
    have g2_eq: "g2 = h2" using g12_eq cart_prod_eq2[OF g1_type g2_type h1_type h2_type] by auto
    have g3_eq: "g3 = h3" using g13_eq cart_prod_eq2[OF g1_type g3_type h1_type h3_type] by auto
    show "g = h" using g_eq h_eq g1_eq g2_eq g3_eq by simp
  qed
qed

subsubsection \<open>Selecting Pairs from a Pair of Pairs\<close>

definition outers :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "outers(A, B, C, D) = \<langle>
      left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D),
      right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)
    \<rangle>"

lemma outers_type[type_rule]: "outers(A, B, C, D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (A \<times>\<^sub>c D)"
proof -
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by (rule left_cart_proj_type)
  have rpCD_type: "right_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> D" by (rule right_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A"
    using lpAB_type lpABCD_type comp_type by blast
  have t2: "right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> D"
    using rpCD_type rpABCD_type comp_type by blast
  show ?thesis unfolding outers_def using t1 t2 cfunc_prod_type by auto
qed

lemma outers_apply:
  assumes a_type: "a : Z \<rightarrow> A" and b_type: "b : Z \<rightarrow> B" and c_type: "c : Z \<rightarrow> C" and d_type: "d : Z \<rightarrow> D"
  shows "outers(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>a, d\<rangle>"
proof -
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by (rule left_cart_proj_type)
  have rpCD_type: "right_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> D" by (rule right_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A"
    using lpAB_type lpABCD_type comp_type by blast
  have t2: "right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> D"
    using rpCD_type rpABCD_type comp_type by blast
  have ab_type: "\<langle>a, b\<rangle> : Z \<rightarrow> A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
  have cd_type: "\<langle>c, d\<rangle> : Z \<rightarrow> C \<times>\<^sub>c D" using c_type d_type cfunc_prod_type by auto
  have abcd_type: "\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> : Z \<rightarrow> (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D)" using ab_type cd_type cfunc_prod_type by auto
  have "outers(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    = \<langle>left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D), right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding outers_def by simp
  also have "... = \<langle>(left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>, (right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF abcd_type t1 t2] by simp
  also have "... = \<langle>a, d\<rangle>"
  proof -
    have "(left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = left_cart_proj(A, B) \<circ>\<^sub>c (left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type lpABCD_type lpAB_type] by simp
    also have "... = left_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using left_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = a"
      using left_cart_proj_cfunc_prod[OF a_type b_type] by simp
    finally have e1: "(left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = a" by simp
    have "(right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = right_cart_proj(C, D) \<circ>\<^sub>c (right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type rpABCD_type rpCD_type] by simp
    also have "... = right_cart_proj(C, D) \<circ>\<^sub>c \<langle>c, d\<rangle>"
      using right_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = d"
      using right_cart_proj_cfunc_prod[OF c_type d_type] by simp
    finally have e2: "(right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = d" by simp
    show ?thesis using e1 e2 by simp
  qed
  finally show ?thesis by simp
qed

definition inners :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "inners(A, B, C, D) = \<langle>
      right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D),
      left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)
    \<rangle>"

lemma inners_type[type_rule]: "inners(A, B, C, D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (B \<times>\<^sub>c C)"
proof -
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have lpCD_type: "left_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> C" by (rule left_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> B"
    using rpAB_type lpABCD_type comp_type by blast
  have t2: "left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C"
    using lpCD_type rpABCD_type comp_type by blast
  show ?thesis unfolding inners_def using t1 t2 cfunc_prod_type by auto
qed

lemma inners_apply:
  assumes a_type: "a : Z \<rightarrow> A" and b_type: "b : Z \<rightarrow> B" and c_type: "c : Z \<rightarrow> C" and d_type: "d : Z \<rightarrow> D"
  shows "inners(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>b, c\<rangle>"
proof -
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have lpCD_type: "left_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> C" by (rule left_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> B"
    using rpAB_type lpABCD_type comp_type by blast
  have t2: "left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C"
    using lpCD_type rpABCD_type comp_type by blast
  have ab_type: "\<langle>a, b\<rangle> : Z \<rightarrow> A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
  have cd_type: "\<langle>c, d\<rangle> : Z \<rightarrow> C \<times>\<^sub>c D" using c_type d_type cfunc_prod_type by auto
  have abcd_type: "\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> : Z \<rightarrow> (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D)" using ab_type cd_type cfunc_prod_type by auto
  have "inners(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    = \<langle>right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D), left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding inners_def by simp
  also have "... = \<langle>(right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>, (left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF abcd_type t1 t2] by simp
  also have "... = \<langle>b, c\<rangle>"
  proof -
    have "(right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = right_cart_proj(A, B) \<circ>\<^sub>c (left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type lpABCD_type rpAB_type] by simp
    also have "... = right_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using left_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = b"
      using right_cart_proj_cfunc_prod[OF a_type b_type] by simp
    finally have e1: "(right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = b" by simp
    have "(left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = left_cart_proj(C, D) \<circ>\<^sub>c (right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type rpABCD_type lpCD_type] by simp
    also have "... = left_cart_proj(C, D) \<circ>\<^sub>c \<langle>c, d\<rangle>"
      using right_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = c"
      using left_cart_proj_cfunc_prod[OF c_type d_type] by simp
    finally have e2: "(left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = c" by simp
    show ?thesis using e1 e2 by simp
  qed
  finally show ?thesis by simp
qed

definition lefts :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "lefts(A, B, C, D) = \<langle>
      left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D),
      left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)
    \<rangle>"

lemma lefts_type[type_rule]: "lefts(A, B, C, D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (A \<times>\<^sub>c C)"
proof -
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by (rule left_cart_proj_type)
  have lpCD_type: "left_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> C" by (rule left_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A"
    using lpAB_type lpABCD_type comp_type by blast
  have t2: "left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C"
    using lpCD_type rpABCD_type comp_type by blast
  show ?thesis unfolding lefts_def using t1 t2 cfunc_prod_type by auto
qed

lemma lefts_apply:
  assumes a_type: "a : Z \<rightarrow> A" and b_type: "b : Z \<rightarrow> B" and c_type: "c : Z \<rightarrow> C" and d_type: "d : Z \<rightarrow> D"
  shows "lefts(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>a, c\<rangle>"
proof -
  have lpAB_type: "left_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> A" by (rule left_cart_proj_type)
  have lpCD_type: "left_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> C" by (rule left_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A"
    using lpAB_type lpABCD_type comp_type by blast
  have t2: "left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C"
    using lpCD_type rpABCD_type comp_type by blast
  have ab_type: "\<langle>a, b\<rangle> : Z \<rightarrow> A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
  have cd_type: "\<langle>c, d\<rangle> : Z \<rightarrow> C \<times>\<^sub>c D" using c_type d_type cfunc_prod_type by auto
  have abcd_type: "\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> : Z \<rightarrow> (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D)" using ab_type cd_type cfunc_prod_type by auto
  have "lefts(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    = \<langle>left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D), left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding lefts_def by simp
  also have "... = \<langle>(left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>, (left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF abcd_type t1 t2] by simp
  also have "... = \<langle>a, c\<rangle>"
  proof -
    have "(left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = left_cart_proj(A, B) \<circ>\<^sub>c (left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type lpABCD_type lpAB_type] by simp
    also have "... = left_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using left_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = a"
      using left_cart_proj_cfunc_prod[OF a_type b_type] by simp
    finally have e1: "(left_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = a" by simp
    have "(left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = left_cart_proj(C, D) \<circ>\<^sub>c (right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type rpABCD_type lpCD_type] by simp
    also have "... = left_cart_proj(C, D) \<circ>\<^sub>c \<langle>c, d\<rangle>"
      using right_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = c"
      using left_cart_proj_cfunc_prod[OF c_type d_type] by simp
    finally have e2: "(left_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = c" by simp
    show ?thesis using e1 e2 by simp
  qed
  finally show ?thesis by simp
qed

definition rights :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "rights(A, B, C, D) = \<langle>
      right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D),
      right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)
    \<rangle>"

lemma rights_type[type_rule]: "rights(A, B, C, D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (B \<times>\<^sub>c D)"
proof -
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have rpCD_type: "right_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> D" by (rule right_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> B"
    using rpAB_type lpABCD_type comp_type by blast
  have t2: "right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> D"
    using rpCD_type rpABCD_type comp_type by blast
  show ?thesis unfolding rights_def using t1 t2 cfunc_prod_type by auto
qed

lemma rights_apply:
  assumes a_type: "a : Z \<rightarrow> A" and b_type: "b : Z \<rightarrow> B" and c_type: "c : Z \<rightarrow> C" and d_type: "d : Z \<rightarrow> D"
  shows "rights(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>b, d\<rangle>"
proof -
  have rpAB_type: "right_cart_proj(A, B) : A \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have rpCD_type: "right_cart_proj(C, D) : C \<times>\<^sub>c D \<rightarrow> D" by (rule right_cart_proj_type)
  have lpABCD_type: "left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> A \<times>\<^sub>c B" by (rule left_cart_proj_type)
  have rpABCD_type: "right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> C \<times>\<^sub>c D" by (rule right_cart_proj_type)
  have t1: "right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> B"
    using rpAB_type lpABCD_type comp_type by blast
  have t2: "right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> D"
    using rpCD_type rpABCD_type comp_type by blast
  have ab_type: "\<langle>a, b\<rangle> : Z \<rightarrow> A \<times>\<^sub>c B" using a_type b_type cfunc_prod_type by auto
  have cd_type: "\<langle>c, d\<rangle> : Z \<rightarrow> C \<times>\<^sub>c D" using c_type d_type cfunc_prod_type by auto
  have abcd_type: "\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> : Z \<rightarrow> (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D)" using ab_type cd_type cfunc_prod_type by auto
  have "rights(A, B, C, D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    = \<langle>right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D), right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    unfolding rights_def by simp
  also have "... = \<langle>(right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>, (right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>\<rangle>"
    using cfunc_prod_comp[OF abcd_type t1 t2] by simp
  also have "... = \<langle>b, d\<rangle>"
  proof -
    have "(right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = right_cart_proj(A, B) \<circ>\<^sub>c (left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type lpABCD_type rpAB_type] by simp
    also have "... = right_cart_proj(A, B) \<circ>\<^sub>c \<langle>a, b\<rangle>"
      using left_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = b"
      using right_cart_proj_cfunc_prod[OF a_type b_type] by simp
    finally have e1: "(right_cart_proj(A, B) \<circ>\<^sub>c left_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = b" by simp
    have "(right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>
      = right_cart_proj(C, D) \<circ>\<^sub>c (right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>)"
      using comp_associative2[OF abcd_type rpABCD_type rpCD_type] by simp
    also have "... = right_cart_proj(C, D) \<circ>\<^sub>c \<langle>c, d\<rangle>"
      using right_cart_proj_cfunc_prod[OF ab_type cd_type] by simp
    also have "... = d"
      using right_cart_proj_cfunc_prod[OF c_type d_type] by simp
    finally have e2: "(right_cart_proj(C, D) \<circ>\<^sub>c right_cart_proj(A \<times>\<^sub>c B, C \<times>\<^sub>c D)) \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> = d" by simp
    show ?thesis using e1 e2 by simp
  qed
  finally show ?thesis by simp
qed

end
