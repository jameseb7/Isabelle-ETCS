theory ETCS_Base
  imports Main
begin

typedecl cset
typedecl cfunc


section \<open>Axiom 1: Sets is a Category\<close>

axiomatization
  domain :: \<open>cfunc \<Rightarrow> cset\<close> and
  codomain :: "cfunc \<Rightarrow> cset" and
  id :: "cset \<Rightarrow> cfunc" ("id\<^sub>c") and
  comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<circ>\<^sub>c" 55) and
  ETCS_func :: "cfunc set"
where
  compatible_comp_ETCS_func:
    "g \<circ>\<^sub>c f \<in> ETCS_func \<longleftrightarrow> (domain(g) = codomain(f) \<and> g \<in> ETCS_func \<and> f \<in> ETCS_func)" and
  domain_comp: "domain(g \<circ>\<^sub>c f) = domain(f)" and
  codomain_comp: "codomain(g \<circ>\<^sub>c f) = codomain(g)" and
  comp_associative: "h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f" and
  id_ETCS_func: "id X \<in> ETCS_func" and
  id_domain: "domain(id(X)) = X" and
  id_codomain: "codomain(id(X)) = X" and
  id_right_unit: "f \<circ>\<^sub>c id(domain(f)) = f" and
  id_left_unit: "id(codomain(f)) \<circ>\<^sub>c f = f"

definition cfunc_type :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" ("_ : _ \<rightarrow> _" [50, 50, 50]50) where
  "(f : X \<rightarrow> Y) \<longleftrightarrow> (domain(f) = X \<and> codomain(f) = Y \<and> f \<in> ETCS_func)"

lemma comp_type[simp]:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> g \<circ>\<^sub>c f : X \<rightarrow> Z"
  by (simp add: cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp)

lemma id_type: "id(X) : X \<rightarrow> X"
  unfolding cfunc_type_def using id_domain id_codomain id_ETCS_func by auto

lemma id_right_unit2: "f : X \<rightarrow> Y \<Longrightarrow> f \<circ>\<^sub>c id X = f"
  unfolding cfunc_type_def using id_right_unit by auto

lemma id_left_unit2: "f : X \<rightarrow> Y \<Longrightarrow> id Y \<circ>\<^sub>c f = f"
  unfolding cfunc_type_def using id_left_unit by auto

subsection \<open>Basic Category Theory Definitions\<close>

(*
  A
  |\c
 av \
  B\<rightarrow>C
   b
*)

definition triangle_commutes :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "triangle_commutes A B C ab bc ac \<longleftrightarrow> 
    ((ab : A \<rightarrow> B) \<and> (bc : B \<rightarrow> C) \<and> (ac : A \<rightarrow> C) \<and> (bc \<circ>\<^sub>c ab = ac))"

(*
      ab
 A -------> B
 |          |
 | ac       | bd
 |          |
 \<or>   cd     \<or>
 C -------> D
*)

definition square_commutes :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "square_commutes A B C D ab bd ac cd \<longleftrightarrow>
    ((ab : A \<rightarrow> B) \<and> (bd : B \<rightarrow> D) \<and> (ac : A \<rightarrow> C) \<and> (cd : C \<rightarrow> D) \<and> (bd \<circ>\<^sub>c ab = cd \<circ>\<^sub>c ac))"

definition is_pullback :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "is_pullback A B C D ab bd ac cd \<longleftrightarrow> 
    (square_commutes A B C D ab bd ac cd \<and> 
    (\<forall> Z k h. (k : Z \<rightarrow> B \<and> h : Z \<rightarrow> C \<and> bd \<circ>\<^sub>c k = cd \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> A \<and> ab \<circ>\<^sub>c j = k \<and> ac \<circ>\<^sub>c j = h)))"

definition monomorphism :: "cfunc \<Rightarrow> bool" where
  "monomorphism(f) \<longleftrightarrow> (\<forall> g\<in>ETCS_func. \<forall>h\<in>ETCS_func. 
    (codomain(g) = domain(f) \<and> codomain(h) = domain(f)) \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"

definition epimorphism :: "cfunc \<Rightarrow> bool" where
  "epimorphism(f) \<longleftrightarrow> (\<forall> g\<in>ETCS_func. \<forall>h\<in>ETCS_func. 
    (domain(g) = codomain(f) \<and> domain(h) = codomain(f)) \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"

definition isomorphism :: "cfunc \<Rightarrow> bool" where
  "isomorphism(f) \<longleftrightarrow> (\<exists> g. domain(g) = codomain(f) \<and> codomain(g) = domain(f) \<and> 
    (g \<circ>\<^sub>c f = id(domain(f))) \<and> (f \<circ>\<^sub>c g = id(domain(g))))"

definition is_isomorphic :: "cset \<Rightarrow> cset \<Rightarrow> bool" (infix "\<cong>" 50)  where
  "X \<cong> Y \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> Y \<and> isomorphism(f))"

lemma id_isomorphism: "isomorphism (id X)"
  unfolding isomorphism_def
  by (rule_tac x="id X" in exI, auto simp add: id_codomain id_domain, metis id_domain id_right_unit)

(*facts about isomorphisms*)
lemma isomorphic_is_reflexive: "X \<cong> X"
  unfolding is_isomorphic_def
  by (rule_tac x="id X" in exI, auto simp add: id_domain id_codomain id_isomorphism id_type)

lemma isomorphic_is_symmetric: "X \<cong> Y \<longrightarrow> Y \<cong> X"
  unfolding is_isomorphic_def isomorphism_def apply (auto, rule_tac x="g" in exI, auto)
  by (metis cfunc_type_def compatible_comp_ETCS_func id_right_unit)

lemma isomorphism_comp: 
  "domain f = codomain g \<Longrightarrow> isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  unfolding isomorphism_def
proof (auto, rule_tac x="gaa \<circ>\<^sub>c ga" in exI, auto)
  fix ga gaa
  assume domain_ga: "domain ga = codomain f"
  assume codomain_gaa: "codomain gaa = domain g"

  show "domain (gaa \<circ>\<^sub>c ga) = codomain (f \<circ>\<^sub>c g)"
    by (simp add: codomain_comp domain_comp domain_ga)
  show "codomain (gaa \<circ>\<^sub>c ga) = domain (f \<circ>\<^sub>c g)"
    by (simp add: codomain_comp codomain_gaa domain_comp)
next
  fix ga gaa
  assume domain_f: "domain f = codomain g"
  assume domain_ga: "domain ga = codomain f"
  assume domain_gaa: "domain gaa = codomain g"
  assume codomain_ga: "codomain ga = codomain g"
  assume codomain_gaa: "codomain gaa = domain g"
  assume ga_comp_f: "ga \<circ>\<^sub>c f = id (codomain g)"
  assume gaa_comp_g: "gaa \<circ>\<^sub>c g = id (domain g)"

  have "(gaa \<circ>\<^sub>c ga) \<circ>\<^sub>c f \<circ>\<^sub>c g =  gaa \<circ>\<^sub>c id (domain f) \<circ>\<^sub>c g"
    by (metis comp_associative domain_f ga_comp_f)
  also have "... = gaa \<circ>\<^sub>c g"
    by (simp add: domain_f id_left_unit)
  also have "... = id (domain (f \<circ>\<^sub>c g))"
    by (simp add: domain_comp gaa_comp_g)
  then show "(gaa \<circ>\<^sub>c ga) \<circ>\<^sub>c f \<circ>\<^sub>c g = id (domain (f \<circ>\<^sub>c g))"
    using calculation by auto
next
  fix ga gaa
  assume domain_f: "domain f = codomain g"
  assume domain_ga: "domain ga = codomain f"
  assume domain_gaa: "domain gaa = codomain g"
  assume codomain_ga: "codomain ga = codomain g"
  assume codomain_gaa: "codomain gaa = domain g"
  assume f_comp_ga: "f \<circ>\<^sub>c ga = id (codomain f)"
  assume g_comp_gaa: "g \<circ>\<^sub>c gaa = id (codomain g)"

  have "(f \<circ>\<^sub>c g) \<circ>\<^sub>c gaa \<circ>\<^sub>c ga = f \<circ>\<^sub>c id (codomain g) \<circ>\<^sub>c ga"
    by (metis comp_associative g_comp_gaa)
  also have "... = f \<circ>\<^sub>c ga"
    by (metis codomain_ga id_left_unit)
  also have "... = id (domain (gaa \<circ>\<^sub>c ga))"
    by (metis domain_comp f_comp_ga id_domain)
  then show "(f \<circ>\<^sub>c g) \<circ>\<^sub>c gaa \<circ>\<^sub>c ga = id (domain (gaa \<circ>\<^sub>c ga))"
    using calculation by auto
qed

lemma isomorphism_comp': 
  assumes "f : Y \<rightarrow> Z" "g : X \<rightarrow> Y"
  shows "isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  using assms(1) assms(2) cfunc_type_def isomorphism_comp by auto

lemma isomorphic_is_transitive: "(X \<cong> Y \<and> Y \<cong> Z) \<longrightarrow> X \<cong> Z"
  unfolding is_isomorphic_def 
  by (auto, rule_tac x="fa \<circ>\<^sub>c f" in exI, auto simp add: isomorphism_comp')

lemma is_isomorphic_equiv:
  "equiv UNIV {(X, Y). X \<cong> Y}"
  unfolding equiv_def
proof auto
  show "refl {(x, y). x \<cong> y}"
    unfolding refl_on_def using isomorphic_is_reflexive by auto
next
  show "sym {(x, y). x \<cong> y}"
    unfolding sym_def using isomorphic_is_symmetric by blast
next
  show "trans {(x, y). x \<cong> y}"
    unfolding trans_def using isomorphic_is_transitive by blast
qed

(*Exercise 2.1.7a*)
lemma comp_monic_imp_monic:
  "monomorphism (g \<circ>\<^sub>c f) \<longrightarrow> monomorphism f"
  unfolding monomorphism_def
proof auto
  fix s t
  assume gf_monic: "\<forall>s\<in>ETCS_func. \<forall>t\<in>ETCS_func. 
    codomain s = domain (g \<circ>\<^sub>c f) \<and> codomain t = domain (g \<circ>\<^sub>c f) \<longrightarrow>
          (g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_s: "codomain s = domain f"
  assume codomain_t: "codomain t = domain f"
  assume fs_eq_ft: "f \<circ>\<^sub>c s = f \<circ>\<^sub>c t"
  assume s_ETCS: "s \<in> ETCS_func"
  assume t_ETCS: "t \<in> ETCS_func"

  from fs_eq_ft have "(g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t"
    by (metis comp_associative)
  then show "s = t"
    using gf_monic codomain_s codomain_t s_ETCS t_ETCS domain_comp by auto
qed      

(*Exercise 2.1.7b*)
lemma comp_epi_imp_epi:
  "epimorphism (g \<circ>\<^sub>c f) \<longrightarrow> epimorphism g"
  unfolding epimorphism_def
proof auto
  fix s t
  assume gf_epi: "\<forall>s\<in>ETCS_func. \<forall>t\<in>ETCS_func.
    domain s = codomain (g \<circ>\<^sub>c f) \<and> domain t = codomain (g \<circ>\<^sub>c f) \<longrightarrow>
          s \<circ>\<^sub>c g \<circ>\<^sub>c f = t \<circ>\<^sub>c g \<circ>\<^sub>c f \<longrightarrow> s = t"
  assume domain_s: "domain s = codomain g"
  assume domain_t: "domain t = codomain g"
  assume sf_eq_tf: "s \<circ>\<^sub>c g = t \<circ>\<^sub>c g"
  assume s_ETCS: "s \<in> ETCS_func"
  assume t_ETCS: "t \<in> ETCS_func"

  from sf_eq_tf have "s \<circ>\<^sub>c (g \<circ>\<^sub>c f) = t \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (metis comp_associative)
  then show "s = t"
    using gf_epi codomain_comp domain_s domain_t s_ETCS t_ETCS by auto
qed

(*Exercise 2.1.7c*)
lemma composition_of_monic_pair_is_monic:
  assumes "codomain(f) = domain(g)" "f \<in> ETCS_func" "g \<in> ETCS_func"
  shows "monomorphism(f) \<and> monomorphism(g) \<longrightarrow> monomorphism(g \<circ>\<^sub>c f)"
  unfolding monomorphism_def
proof auto
  fix h k
  assume f_mono: "\<forall>s\<in>ETCS_func. \<forall>t\<in>ETCS_func. 
    codomain s = domain f \<and> codomain t = domain f \<longrightarrow> f \<circ>\<^sub>c s = f \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume g_mono: "\<forall>s\<in>ETCS_func. \<forall>t\<in>ETCS_func. 
    codomain s = domain g \<and> codomain t = domain g \<longrightarrow> g \<circ>\<^sub>c s = g \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_k: "codomain k = domain (g \<circ>\<^sub>c f)"
  assume codomain_h: "codomain h = domain (g \<circ>\<^sub>c f)"
  assume gfh_eq_gfk: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c k = (g \<circ>\<^sub>c f) \<circ>\<^sub>c h"
  assume h_ETCS: "h \<in> ETCS_func"
  assume k_ETCS: "k \<in> ETCS_func"
 
  have "g \<circ>\<^sub>c (f \<circ>\<^sub>c h) = (g  \<circ>\<^sub>c f)  \<circ>\<^sub>c h"
    by (simp add: comp_associative)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: gfh_eq_gfk)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: comp_associative)
  
  then have "f \<circ>\<^sub>c h = f \<circ>\<^sub>c k"
    using assms calculation cfunc_type_def codomain_h codomain_k comp_type domain_comp g_mono h_ETCS k_ETCS by auto
  then show "k = h"
    by (simp add: codomain_h codomain_k domain_comp f_mono h_ETCS k_ETCS)
qed

(*Exercise 2.1.7d*)
lemma composition_of_epi_pair_is_epi:
assumes "codomain(f) = domain(g)" "f \<in> ETCS_func" "g \<in> ETCS_func"
  shows "epimorphism(f) \<and> epimorphism(g) \<longrightarrow> epimorphism(g \<circ>\<^sub>c f)"
  unfolding epimorphism_def
proof auto
  fix h k
  assume f_epi :"\<forall> s\<in>ETCS_func. \<forall>h\<in>ETCS_func.
    (domain(s) = codomain(f) \<and> domain(h) = codomain(f)) \<longrightarrow> (s \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> s = h)"
  assume g_epi :"\<forall> s\<in>ETCS_func. \<forall>h\<in>ETCS_func.
    (domain(s) = codomain(g) \<and> domain(h) = codomain(g)) \<longrightarrow> (s \<circ>\<^sub>c g = h \<circ>\<^sub>c g \<longrightarrow> s = h)"
  assume domain_k: "domain k = codomain (g \<circ>\<^sub>c f)"
  assume domain_h: "domain h = codomain (g \<circ>\<^sub>c f)"
  assume hgf_eq_kgf: "h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
  assume h_ETCS: "h \<in> ETCS_func"
  assume k_ETCS: "k \<in> ETCS_func"
  
  have "(h \<circ>\<^sub>c g) \<circ>\<^sub>c f = h \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: comp_associative)
  also have "... = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: hgf_eq_kgf)
  also have "... =(k \<circ>\<^sub>c g) \<circ>\<^sub>c f "
    by (simp add: comp_associative)
 
  then have "h \<circ>\<^sub>c g = k \<circ>\<^sub>c g"
    by (simp add: assms calculation codomain_comp compatible_comp_ETCS_func domain_comp domain_h domain_k f_epi h_ETCS k_ETCS)
  then show "h = k"
    by (simp add: codomain_comp domain_h domain_k g_epi h_ETCS k_ETCS)
qed


(*Exercise 2.1.7e*)
lemma iso_imp_epi_and_monic:
  "isomorphism f \<longrightarrow> (epimorphism f \<and> monomorphism f)"
  unfolding isomorphism_def epimorphism_def monomorphism_def
proof auto
  fix g s t
  assume domain_g: "domain g = codomain f"
  assume codomain_g: "codomain g = domain f"
  assume gf_id: "g \<circ>\<^sub>c f = id (domain f)"
  assume fg_id: "f \<circ>\<^sub>c g = id (codomain f)"
  assume domain_s: "domain s = codomain f"
  assume domain_t: "domain t = codomain f"
  assume sf_eq_tf: "s \<circ>\<^sub>c f = t \<circ>\<^sub>c f"

  have "s = s \<circ>\<^sub>c id(codomain(f))"
    by (metis domain_s id_right_unit)
  also have "... = s \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    by (metis fg_id)
  also have "... = (s \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    by (simp add: comp_associative)
  also have "... = (t \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    by (simp add: sf_eq_tf)
  also have "... = t \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    by (simp add: comp_associative)
  also have "... = t \<circ>\<^sub>c id(codomain(f))"
    by (metis fg_id)
  also have "... = t"
    by (metis domain_t id_right_unit)
    
  then show "s = t"
    using calculation by auto
next
  fix g h k

  assume domain_g: "domain g = codomain f"
  assume codomain_g: "codomain g = domain f"
  assume gf_id: "g \<circ>\<^sub>c f = id (domain f)"
  assume fg_id: "f \<circ>\<^sub>c g = id (codomain f)"
  assume codomain_k: "codomain k = domain f"
  assume codomain_h: "codomain h = domain f"
  assume fk_eq_fh: "f \<circ>\<^sub>c k = f \<circ>\<^sub>c h"

  have "h = id(domain(f)) \<circ>\<^sub>c h"
    by (metis codomain_h id_left_unit)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c h"
    using gf_id by auto
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c h)"
    by (simp add: comp_associative)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: fk_eq_fh)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: comp_associative)
  also have "... = id(domain(f)) \<circ>\<^sub>c k"
    by (simp add: gf_id)
  also have "... = k"
    by (metis codomain_k id_left_unit)

  then show "k = h"
    using calculation by auto
qed

end