theory ETCS_Base_FOL
  imports FOL
begin

typedecl cset
typedecl cfunc

axiomatization
  d0   :: "cfunc => cset" and
  d1   :: "cfunc => cset" and
  comp :: "cfunc => cfunc => cfunc"  (infixr "o" 55) and
  id   :: "cset => cfunc"
where
  d0_comp:
    "d1 (f) = d0 g --> d0 (g o f) = d0 f" and
  d1_comp:
    "d1 f = d0 g --> d1 (g o f) = d1 g" and
  comp_associative:
    "d1 f = d0 g --> d1 g = d0 h --> h o (g o f) = (h o g) o f" and
  id_d0:
    "d0 (id X) = X" and
  id_d1:
    "d1 (id X) = X" and
  id_right_unit:
    "f o id (d0 f) = f" and
  id_left_unit:
    "id (d1 f) o f = f"

definition cfunc_type :: "[cfunc, cset, cset] \<Rightarrow> o" ("_ : _ \<rightarrow> _" [50, 50, 50] 50) where
  "f : X \<rightarrow> Y \<equiv> (d0(f) = X \<and> d1(f) = Y)"

lemma comp_type:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> g \<circ> f : X \<rightarrow> Z"
  by (simp add: cfunc_type_def d0_comp d1_comp)

lemma comp_associative2:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> h : Z \<rightarrow> W \<Longrightarrow> h \<circ> (g \<circ> f) = (h \<circ> g) \<circ> f"
  by (simp add: cfunc_type_def comp_associative)

lemma id_type:
  "id(X) : X \<rightarrow> X"
  by (simp add: cfunc_type_def id_d0 id_d1)

lemma id_right_unit2:
  "f : X \<rightarrow> Y \<Longrightarrow> f \<circ> id(X) = f"
  by (simp add: cfunc_type_def id_right_unit)

lemma id_left_unit2:
  "f : X \<rightarrow> Y \<Longrightarrow> id(Y) \<circ> f = f"
  by (simp add: cfunc_type_def id_left_unit)

subsection \<open>Basic category-theoretic predicates\<close>

definition triangle_commutes ::
  "[cset, cset, cset, cfunc, cfunc, cfunc] \<Rightarrow> o"
where
  "triangle_commutes(A, B, C, ab, bc, ac) \<equiv>
     (ab : A \<rightarrow> B \<and> bc : B \<rightarrow> C \<and> ac : A \<rightarrow> C \<and> bc \<circ> ab = ac)"

definition square_commutes ::
  "[cset, cset, cset, cset, cfunc, cfunc, cfunc, cfunc] \<Rightarrow> o"
where
  "square_commutes(A, B, C, D, ab, bd, ac, cd) \<equiv>
     (ab : A \<rightarrow> B \<and> bd : B \<rightarrow> D \<and> ac : A \<rightarrow> C \<and> cd : C \<rightarrow> D \<and> bd \<circ> ab = cd \<circ> ac)"

definition is_pullback ::
  "[cset, cset, cset, cset, cfunc, cfunc, cfunc, cfunc] \<Rightarrow> o"
where
  "is_pullback(A, B, C, D, ab, bd, ac, cd) \<equiv>
     (square_commutes(A, B, C, D, ab, bd, ac, cd) \<and>
      (\<forall> Z k h.
         (k : Z \<rightarrow> B \<and> h : Z \<rightarrow> C \<and> bd \<circ> k = cd \<circ> h) \<longrightarrow>
         (\<exists>! j. j : Z \<rightarrow> A \<and> ab \<circ> j = k \<and> ac \<circ> j = h)))"

definition monomorphism :: "cfunc \<Rightarrow> o" where
  "monomorphism(f) \<equiv>
     (\<forall> g h.
        (d1(g) = d0(f) \<and> d1(h) = d0(f)) \<longrightarrow>
        (f \<circ> g = f \<circ> h \<longrightarrow> g = h))"

lemma monomorphism_def2:
  "monomorphism(f) \<longleftrightarrow>
     (\<forall> g h A X Y.
        g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<and> f : X \<rightarrow> Y \<longrightarrow>
        (f \<circ> g = f \<circ> h \<longrightarrow> g = h))"
  unfolding monomorphism_def cfunc_type_def
  by blast

lemma monomorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "monomorphism(f) \<longleftrightarrow>
           (\<forall> g h A.
              g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<longrightarrow>
              (f \<circ> g = f \<circ> h \<longrightarrow> g = h))"
  using assms
  unfolding monomorphism_def2 cfunc_type_def
  by blast

definition epimorphism :: "cfunc \<Rightarrow> o" where
  "epimorphism(f) \<equiv>
     (\<forall> g h.
        (d0(g) = d1(f) \<and> d0(h) = d1(f)) \<longrightarrow>
        (g \<circ> f = h \<circ> f \<longrightarrow> g = h))"

lemma epimorphism_def2:
  "epimorphism(f) \<longleftrightarrow>
     (\<forall> g h A X Y.
        f : X \<rightarrow> Y \<and> g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow>
        (g \<circ> f = h \<circ> f \<longrightarrow> g = h))"
  unfolding epimorphism_def cfunc_type_def
  by blast

lemma epimorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "epimorphism(f) \<longleftrightarrow>
           (\<forall> g h A.
              g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow>
              (g \<circ> f = h \<circ> f \<longrightarrow> g = h))"
  using assms
  unfolding epimorphism_def2 cfunc_type_def
  by blast

subsection \<open>Isomorphisms (relational inverse, not THE)\<close>

definition inverse_of :: "[cfunc, cfunc] \<Rightarrow> o" where
  "inverse_of(g, f) \<equiv>
     (g : d1(f) \<rightarrow> d0(f) \<and>
      g \<circ> f = id(d0(f)) \<and>
      f \<circ> g = id(d1(f)))"

definition isomorphism :: "cfunc \<Rightarrow> o" where
  "isomorphism(f) \<equiv> (\<exists> g. inverse_of(g, f))"

lemma inverse_of_type:
  "inverse_of(g, f) \<Longrightarrow> g : d1(f) \<rightarrow> d0(f)"
  by (simp add: inverse_of_def)

lemma inverse_of_sym:
  assumes "inverse_of(g, f)"
  shows "inverse_of(f, g)"
proof -
  from assms have g_ty: "g : d1(f) \<rightarrow> d0(f)"
    and gf: "g \<circ> f = id(d0(f))"
    and fg: "f \<circ> g = id(d1(f))"
    unfolding inverse_of_def by blast+
  have f_ty: "f : d0(f) \<rightarrow> d1(f)"
    by (simp add: cfunc_type_def)
  from g_ty have "d0(g) = d1(f)" and "d1(g) = d0(f)"
    by (simp_all add: cfunc_type_def)
  with f_ty gf fg show ?thesis
    unfolding inverse_of_def cfunc_type_def
    by simp
qed

lemma inverse_of_unique:
  assumes gf: "inverse_of(g, f)"
    and hf: "inverse_of(h, f)"
  shows "g = h"
proof -
  from gf have g_ty: "g : d1(f) \<rightarrow> d0(f)"
    and gf1: "g \<circ> f = id(d0(f))"
    and gf2: "f \<circ> g = id(d1(f))"
    unfolding inverse_of_def by blast+
  from hf have h_ty: "h : d1(f) \<rightarrow> d0(f)"
    and hf1: "h \<circ> f = id(d0(f))"
    and hf2: "f \<circ> h = id(d1(f))"
    unfolding inverse_of_def by blast+
  have f_ty: "f : d0(f) \<rightarrow> d1(f)"
    by (simp add: cfunc_type_def)

  have "g = id(d0(f)) \<circ> g"
    using g_ty by (simp add: id_left_unit2)
  also have "... = (h \<circ> f) \<circ> g"
    by (simp add: hf1)
  also have "... = h \<circ> (f \<circ> g)"
    by (rule sym, rule comp_associative2[OF g_ty f_ty h_ty])
  also have "... = h \<circ> id(d1(f))"
    by (simp add: gf2)
  also have "... = h"
    using h_ty by (simp add: id_right_unit2)
  finally show "g = h" .
qed

lemma isomorphism_def2:
  "isomorphism(f) \<longleftrightarrow>
     (\<exists> g X Y.
        f : X \<rightarrow> Y \<and> g : Y \<rightarrow> X \<and>
        g \<circ> f = id(X) \<and> f \<circ> g = id(Y))"
  unfolding isomorphism_def inverse_of_def
  by (blast simp add: cfunc_type_def)

lemma isomorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "isomorphism(f) \<longleftrightarrow>
           (\<exists> g.
              g : Y \<rightarrow> X \<and>
              g \<circ> f = id(X) \<and>
              f \<circ> g = id(Y))"
  using assms
  unfolding isomorphism_def2 cfunc_type_def
  by blast

definition is_isomorphic :: "[cset, cset] \<Rightarrow> o" (infix "\<cong>" 50) where
  "X \<cong> Y \<equiv> (\<exists> f. f : X \<rightarrow> Y \<and> isomorphism(f))"

lemma id_isomorphism:
  "isomorphism(id(X))"
proof -
  have "inverse_of(id(X), id(X))"
    unfolding inverse_of_def
    by (simp add: id_type id_left_unit2 id_right_unit2)
  thus ?thesis
    unfolding isomorphism_def
    by blast
qed

lemma isomorphic_is_reflexive:
  "X \<cong> X"
  unfolding is_isomorphic_def
  by (blast intro: id_type id_isomorphism)

lemma isomorphic_is_symmetric:
  "X \<cong> Y \<Longrightarrow> Y \<cong> X"
  unfolding is_isomorphic_def isomorphism_def
  by (blast intro: inverse_of_sym)

subsection \<open>Representative transported lemmas\<close>

lemma comp_monic_imp_monic:
  assumes "d1(f) = d0(g)"
  shows "monomorphism(g \<circ> f) \<Longrightarrow> monomorphism(f)"
  unfolding monomorphism_def
proof clarify
  fix s t
  assume gf_monic:
    "\<forall> s t.
       (d1(s) = d0(g \<circ> f) \<and> d1(t) = d0(g \<circ> f)) \<longrightarrow>
       ((g \<circ> f) \<circ> s = (g \<circ> f) \<circ> t \<longrightarrow> s = t)"
  assume s_ty: "d1(s) = d0(f)"
  assume t_ty: "d1(t) = d0(f)"
  assume fst_eq: "f \<circ> s = f \<circ> t"

  have "(g \<circ> f) \<circ> s = (g \<circ> f) \<circ> t"
    using fst_eq assms s_ty t_ty
    by (blast intro: comp_associative)
  thus "s = t"
    using gf_monic s_ty t_ty assms d0_comp
    by simp
qed

lemma comp_epi_imp_epi:
  assumes "d1(f) = d0(g)"
  shows "epimorphism(g \<circ> f) \<Longrightarrow> epimorphism(g)"
  unfolding epimorphism_def
proof clarify
  fix s t
  assume gf_epi:
    "\<forall> s t.
       (d0(s) = d1(g \<circ> f) \<and> d0(t) = d1(g \<circ> f)) \<longrightarrow>
       (s \<circ> (g \<circ> f) = t \<circ> (g \<circ> f) \<longrightarrow> s = t)"
  assume s_ty: "d0(s) = d1(g)"
  assume t_ty: "d0(t) = d1(g)"
  assume sg_tg: "s \<circ> g = t \<circ> g"

  have "s \<circ> (g \<circ> f) = t \<circ> (g \<circ> f)"
    using sg_tg assms s_ty t_ty
    by (simp add: comp_associative)
  thus "s = t"
    using gf_epi s_ty t_ty assms d1_comp
    by simp
qed

lemma iso_imp_epi_and_monic:
  "isomorphism(f) \<Longrightarrow> epimorphism(f) \<and> monomorphism(f)"
  unfolding isomorphism_def
proof
  assume "\<exists> g. inverse_of(g, f)"
  then obtain g where inv: "inverse_of(g, f)"
    by blast

  from inv have g_ty: "g : d1(f) \<rightarrow> d0(f)"
    and gf_id: "g \<circ> f = id(d0(f))"
    and fg_id: "f \<circ> g = id(d1(f))"
    unfolding inverse_of_def by blast+

  have f_ty: "f : d0(f) \<rightarrow> d1(f)"
    by (simp add: cfunc_type_def)

  show "epimorphism(f) \<and> monomorphism(f)"
  proof (rule conjI)
    show "epimorphism(f)"
      unfolding epimorphism_def
    proof clarify
      fix s t
      assume s_ty: "d0(s) = d1(f)"
      assume t_ty: "d0(t) = d1(f)"
      assume sf_tf: "s \<circ> f = t \<circ> f"

      have s_type: "s : d1(f) \<rightarrow> d1(s)"
        using s_ty by (simp add: cfunc_type_def)
      have t_type: "t : d1(f) \<rightarrow> d1(t)"
        using t_ty by (simp add: cfunc_type_def)

      have "s = s \<circ> id(d1(f))"
        using s_type by (simp add: id_right_unit2)
      also have "... = s \<circ> (f \<circ> g)"
        by (simp add: fg_id)
      also have "... = (s \<circ> f) \<circ> g"
        by (rule comp_associative2[OF g_ty f_ty s_type])
      also have "... = (t \<circ> f) \<circ> g"
        by (simp add: sf_tf)
      also have "... = t \<circ> (f \<circ> g)"
        by (rule sym, rule comp_associative2[OF g_ty f_ty t_type])
      also have "... = t \<circ> id(d1(f))"
        by (simp add: fg_id)
      also have "... = t"
        using t_type by (simp add: id_right_unit2)
      finally show "s = t" .
    qed

    show "monomorphism(f)"
      unfolding monomorphism_def
    proof clarify
      fix h k
      assume h_ty: "d1(h) = d0(f)"
      assume k_ty: "d1(k) = d0(f)"
      assume fh_fk: "f \<circ> h = f \<circ> k"

      have h_type: "h : d0(h) \<rightarrow> d0(f)"
        using h_ty by (simp add: cfunc_type_def)
      have k_type: "k : d0(k) \<rightarrow> d0(f)"
        using k_ty by (simp add: cfunc_type_def)

      have "h = id(d0(f)) \<circ> h"
        using h_type by (simp add: id_left_unit2)
      also have "... = (g \<circ> f) \<circ> h"
        by (simp add: gf_id)
      also have "... = g \<circ> (f \<circ> h)"
        by (rule comp_associative2[OF h_type f_ty g_ty])
      also have "... = g \<circ> (f \<circ> k)"
        by (simp add: fh_fk)
      also have "... = (g \<circ> f) \<circ> k"
        by (rule sym, rule comp_associative2[OF k_type f_ty g_ty])
      also have "... = id(d0(f)) \<circ> k"
        by (simp add: gf_id)
      also have "... = k"
        using k_type by (simp add: id_left_unit2)
      finally show "h = k" .
    qed
  qed
qed

end