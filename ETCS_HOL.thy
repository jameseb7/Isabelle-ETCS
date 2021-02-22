theory ETCS_HOL
  imports Main
begin

typedecl cset
typedecl cfunc

(********* USEFUL LITERATURE
https://mathoverflow.net/questions/116701/how-would-set-theory-research-be-affected-by-using-etcs-instead-of-zfc
https://golem.ph.utexas.edu/category/2014/01/an_elementary_theory_of_the_ca.html
https://arxiv.org/abs/1212.6543    (Friendly paper, Leinster)
https://www.pnas.org/content/pnas/52/6/1506.full.pdf  (Original paper, Lawvere)
http://www.tac.mta.ca/tac/reprints/articles/11/tr11.pdf (Long and modern version, Lawvere)
***********************************
***********************************)

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
  then show "(f \<circ>\<^sub>c g) \<circ>\<^sub>c gaa \<circ>\<^sub>c ga = ETCS_HOL.id (domain (gaa \<circ>\<^sub>c ga))"
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
  

section \<open>Axiom 2: Cartesian Products\<close>

axiomatization
  cart_prod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<times>\<^sub>c" 65) and
  left_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("\<langle>_,_\<rangle>")
where
  left_cart_proj_type: "left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> X" and
  right_cart_proj_type: "right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y" and
  cfunc_prod_type: "f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y \<longrightarrow> \<langle>f,g\<rangle> : Z \<rightarrow> X \<times>\<^sub>c Y" and
  left_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y \<longrightarrow> left_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = f" and
  right_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y \<longrightarrow> right_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = g" and
  cfunc_prod_unique: "f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y \<longrightarrow>
    (\<forall> h. ((h : Z \<rightarrow> (X \<times>\<^sub>c Y)) \<and> (left_cart_proj X Y \<circ>\<^sub>c h = f) \<and> (right_cart_proj X Y \<circ>\<^sub>c h = g))
        \<longrightarrow> h = \<langle>f,g\<rangle>)"

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
    by (simp add: comp_associative f_def g_def)
  have fg1: "\<pi>'\<^sub>1 \<circ>\<^sub>c (f \<circ>\<^sub>c g) = \<pi>'\<^sub>1"
    by (simp add: comp_associative f_def g_def)

  obtain idW' where "idW' : W' \<rightarrow> W' \<and> (\<forall> h2. (h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1) \<longrightarrow> h2 = idW')"
    using W'_cart_prod unfolding is_cart_prod_def by (metis fst_conv snd_conv)
  then have fg: "f \<circ>\<^sub>c g = id W'"
  proof auto
    assume idW'_unique: "\<forall>h2. h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1 \<longrightarrow> h2 = idW'"
    have 1: "f \<circ>\<^sub>c g = idW'"
      using idW'_unique apply (erule_tac x="f \<circ>\<^sub>c g" in allE, auto)
      using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp f_def fg0 fg1 g_def by auto
    have 2: "id W' = idW'"
      using idW'_unique apply (erule_tac x="f \<circ>\<^sub>c g" in allE, auto)
      by (metis cfunc_type_def domain_comp g_def id_right_unit id_type)
    from 1 2 show "f \<circ>\<^sub>c g = id W'"
      by auto
  qed

  have gf0: "\<pi>\<^sub>0 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>0"
    by (simp add: comp_associative f_def g_def)
  have gf1: "\<pi>\<^sub>1 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>1"
    by (simp add: comp_associative f_def g_def)

  obtain idW where "idW : W \<rightarrow> W \<and> (\<forall> h2. (h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1) \<longrightarrow> h2 = idW)"
    using W_cart_prod unfolding is_cart_prod_def by (metis fst_conv snd_conv)
  then have gf: "g \<circ>\<^sub>c f = id W"
  proof auto
    assume idW_unique: "\<forall>h2. h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1 \<longrightarrow> h2 = idW"
    have 1: "g \<circ>\<^sub>c f = idW"
      using idW_unique apply (erule_tac x="g \<circ>\<^sub>c f" in allE, auto)
      using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp f_def gf0 gf1 g_def by auto
    have 2: "id W = idW"
      using idW_unique apply (erule_tac x="id W" in allE, auto)
      by (metis cfunc_type_def domain_comp f_def id_right_unit id_type)
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
    by (smt cfunc_prod_unique cfunc_type_def comp_associative fact1 id_right_unit id_type left_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_cfunc_prod right_cart_proj_type)
  show "A \<times>\<^sub>c B \<cong> B \<times>\<^sub>c A"
    by (metis cfunc_type_def id_AB id_BA is_isomorphic_def isomorphism_def pprod_type qprod_type)
  qed 




(*Definition 2.1.9*)
definition diagonal :: "cset \<Rightarrow> cfunc" where
  "diagonal(X) = \<langle>id(X),id(X)\<rangle>"


(*Definition 2.1.10*)
definition cfunc_cross_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<times>\<^sub>f" 65) where
  "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj (domain f) (domain g), g \<circ>\<^sub>c right_cart_proj (domain f) (domain g)\<rangle>"

lemma cfunc_cross_prod_type:
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

lemma cfunc_cross_prod_unique: "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow>
    \<forall> h. ((h : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z)
      \<and> (left_cart_proj Y Z \<circ>\<^sub>c h = f \<circ>\<^sub>c left_cart_proj W X)
      \<and> (right_cart_proj Y Z \<circ>\<^sub>c h = g \<circ>\<^sub>c right_cart_proj W X)) 
        \<longrightarrow> h = f \<times>\<^sub>f g"
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

  have step1: "(id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) : X \<times>\<^sub>c A \<rightarrow> X \<times>\<^sub>c C"
    by (meson cfunc_cross_prod_type comp_type f_type g_type id_type)
  have step2: "left_cart_proj X C \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) = id\<^sub>c X \<circ>\<^sub>c left_cart_proj X A"
    by (smt comp_associative f_type g_type id_domain id_right_unit id_type left_cart_proj_cfunc_cross_prod)
  have step3: "right_cart_proj X C \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj X A"
    by (smt comp_associative f_type g_type id_type right_cart_proj_cfunc_cross_prod)

  show "id\<^sub>c X \<times>\<^sub>f (g \<circ>\<^sub>c f) = id\<^sub>c X \<times>\<^sub>f g \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f"
    using uniqueness step1 step2 step3 by force
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
    using cfunc_cross_prod_def cfunc_type_def comp_associative comp_type f_type g_type
      left_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_type by auto
  then have left_eq: "left_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c a"
    using a_type b_type left_cart_proj_cfunc_prod by auto
  
  have "right_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c right_cart_proj W X \<circ>\<^sub>c \<langle>a, b\<rangle>"
    using cfunc_cross_prod_def cfunc_type_def comp_associative comp_type f_type g_type
      left_cart_proj_type right_cart_proj_cfunc_prod right_cart_proj_type by auto
  then have right_eq: "right_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c b"
    using a_type b_type right_cart_proj_cfunc_prod by auto

  show "f \<times>\<^sub>f g \<circ>\<^sub>c \<langle>a,b\<rangle> = \<langle>f \<circ>\<^sub>c a,g \<circ>\<^sub>c b\<rangle>"
    using uniqueness left_eq right_eq assms apply (erule_tac x="f \<times>\<^sub>f g \<circ>\<^sub>c \<langle>a,b\<rangle>" in allE, auto)
    by (metis cfunc_type_def compatible_comp_ETCS_func domain_comp right_cart_proj_type)
qed

lemma cfunc_prod_comp:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes a_type: "a : Y \<rightarrow> A" and b_type: "b : Y \<rightarrow> B"
  shows "\<langle>a, b\<rangle> \<circ>\<^sub>c f = \<langle>a \<circ>\<^sub>c f, b \<circ>\<^sub>c f\<rangle>"
proof -
  
  have same_type: "\<langle>a, b\<rangle> \<circ>\<^sub>c f : X \<rightarrow> A \<times>\<^sub>c B"
    using a_type b_type cfunc_prod_type f_type by auto
  have same_left_proj: "left_cart_proj A B \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = a \<circ>\<^sub>c f"
    using a_type b_type comp_associative left_cart_proj_cfunc_prod by auto
  have same_right_proj: "right_cart_proj A B \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = b \<circ>\<^sub>c f"
    using a_type b_type comp_associative right_cart_proj_cfunc_prod by auto

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
  have "f \<times>\<^sub>f f \<circ>\<^sub>c \<langle>id\<^sub>c X, id\<^sub>c X\<rangle> = \<langle>f \<circ>\<^sub>c id\<^sub>c X, f \<circ>\<^sub>c id\<^sub>c X\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_type by blast
  also have "... = \<langle>f, f\<rangle>"
    using assms cfunc_type_def id_right_unit by auto
  also have "... = \<langle>id\<^sub>c Y \<circ>\<^sub>c f, id\<^sub>c Y \<circ>\<^sub>c f\<rangle>"
    using assms cfunc_type_def id_left_unit by auto
  also have "... = \<langle>id\<^sub>c Y, id\<^sub>c Y\<rangle> \<circ>\<^sub>c f"
    using assms cfunc_prod_comp id_type by fastforce
  then show "f \<times>\<^sub>f f \<circ>\<^sub>c \<langle>id\<^sub>c X,id\<^sub>c X\<rangle> = \<langle>id\<^sub>c Y,id\<^sub>c Y\<rangle> \<circ>\<^sub>c f"
    using calculation by auto
qed

lemma cfunc_cross_prod_comp_cfunc_cross_prod:
  assumes "a : A \<rightarrow> X" "b : B \<rightarrow> Y" "x : X \<rightarrow> Z" "y : Y \<rightarrow> W"
  shows "(x \<times>\<^sub>f y) \<circ>\<^sub>c (a \<times>\<^sub>f b) = (x \<circ>\<^sub>c a) \<times>\<^sub>f (y \<circ>\<^sub>c b)"
proof -
  have "(x \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c left_cart_proj A B , b \<circ>\<^sub>c right_cart_proj A B\<rangle>
      = \<langle>x \<circ>\<^sub>c a \<circ>\<^sub>c left_cart_proj A B, y \<circ>\<^sub>c b \<circ>\<^sub>c right_cart_proj A B\<rangle>"
    by (meson assms cfunc_cross_prod_comp_cfunc_prod comp_type left_cart_proj_type right_cart_proj_type)
  then show "x \<times>\<^sub>f y \<circ>\<^sub>c a \<times>\<^sub>f b = (x \<circ>\<^sub>c a) \<times>\<^sub>f (y \<circ>\<^sub>c b)"
    unfolding cfunc_cross_prod_def
    using assms cfunc_type_def comp_associative domain_comp 
    by auto
qed

subsection \<open>Useful Cartesian product permuting functions\<close>

definition swap :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "swap X Y = \<langle>right_cart_proj X Y, left_cart_proj X Y\<rangle>"

lemma swap_type: "swap X Y : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c X"
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

definition associate_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_right X Y Z =
    \<langle>
      left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, 
      \<langle>
        right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z,
        right_cart_proj (X \<times>\<^sub>c Y) Z
      \<rangle>
    \<rangle>"

lemma associate_right_type: "associate_right X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
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
    by (smt assms cfunc_prod_type comp_associative left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = ?rhs"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

definition associate_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_left X Y Z =
    \<langle>
      \<langle>
        left_cart_proj X (Y \<times>\<^sub>c Z),
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
      \<rangle>,
      right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
    \<rangle>"

lemma associate_left_type: "associate_left X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
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
    using cfunc_prod_comp comp_associative l_ll_type rr_type x_yz_type by auto
  also have "... = \<langle>
      \<langle>
        left_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
      \<rangle> ,
      right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)  \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>
    \<rangle>"
    using cfunc_prod_comp comp_associative left_cart_proj_type lr_type x_yz_type by fastforce
  also have "... = \<langle>\<langle>x, left_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>, right_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>"
    using assms(1) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod yz_type by auto
  also have "... = ?rhs"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  then show ?thesis
    using calculation by auto
qed

section \<open>Axiom 3: Terminal Objects\<close>

axiomatization
  terminal_func :: "cset \<Rightarrow> cfunc" ("\<beta>\<^bsub>_\<^esub>" 100) and
  one :: "cset"
where
  terminal_func_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> one" and
  terminal_func_unique: "\<forall> h. (h :  X \<rightarrow> one)  \<longrightarrow> (h =\<beta>\<^bsub>X\<^esub>)" and
  one_separator: "f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> (\<And> x. x : one \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x) \<Longrightarrow> f = g"

abbreviation member :: "cfunc \<Rightarrow> cset \<Rightarrow> bool" (infix "\<in>\<^sub>c" 50) where
  "x \<in>\<^sub>c X \<equiv> (x : one \<rightarrow> X)"

definition nonempty :: "cset \<Rightarrow> bool" where
  "nonempty X \<equiv> (\<exists>x. x \<in>\<^sub>c X)"
  
definition terminal_object :: "cset \<Rightarrow> bool" where
  "terminal_object(X) \<longleftrightarrow> (\<forall> Y. \<exists>! f. f : Y \<rightarrow> X)"

lemma diag_on_elements:
  assumes "x \<in>\<^sub>c X"
  shows "diagonal(X) \<circ>\<^sub>c x = \<langle>x,x\<rangle>"
using assms cfunc_prod_comp cfunc_type_def diagonal_def id_left_unit id_type by auto

lemma one_separator_contrapos:
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> Y"
  shows "f \<noteq> g \<Longrightarrow> \<exists> x. x : one \<rightarrow> X \<and> f \<circ>\<^sub>c x \<noteq> g \<circ>\<^sub>c x"
proof -
  have "(\<forall> x. x : one \<rightarrow> X \<longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x) \<longrightarrow> f = g"
    using assms(1) assms(2) one_separator by blast
  then show "f \<noteq> g \<Longrightarrow> \<exists>x. x \<in>\<^sub>c X \<and> f \<circ>\<^sub>c x \<noteq> g \<circ>\<^sub>c x"
    by blast
qed
    

lemma one_terminal_object: "terminal_object(one)"
  unfolding terminal_object_def
proof auto
  fix Y
  have "\<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> one"
    using terminal_func_type by simp
  then show "\<exists>f. (f : Y \<rightarrow> one)"
    by auto
next
  fix Y f y
  assume "f : Y \<rightarrow> one" "y : Y \<rightarrow> one"
  then have "f = \<beta>\<^bsub>Y\<^esub> \<and> y = \<beta>\<^bsub>Y\<^esub>"
    using terminal_func_unique by auto
  then show "f = y"
    by simp
qed

(* Exercise 2.1.15 *)
lemma terminal_objects_isomorphic:
  assumes "terminal_object X" "terminal_object Y"
  shows "X \<cong> Y"
  unfolding is_isomorphic_def
proof -

  obtain f where f_type: "f : X \<rightarrow> Y" and f_unique: "\<forall>g. g : X \<rightarrow> Y \<longrightarrow> f = g"
    using assms(2) terminal_object_def by force

  obtain g where g_type: "g : Y \<rightarrow> X" and g_unique: "\<forall>f. f : Y \<rightarrow> X \<longrightarrow> g = f"
    using assms(1) terminal_object_def by force

  have g_f_is_id: "g \<circ>\<^sub>c f = id X"
    using assms(1) comp_type f_type g_type id_type terminal_object_def by blast

  have f_g_is_id: "f \<circ>\<^sub>c g = id Y"
    using assms(2) comp_type f_type g_type id_type terminal_object_def by blast

  have f_isomorphism: "isomorphism f"
    unfolding isomorphism_def
    using cfunc_type_def f_type g_type g_f_is_id f_g_is_id
    by (rule_tac x=g in exI, auto)

  show "\<exists>f. f : X \<rightarrow> Y \<and> isomorphism f"
    using f_isomorphism f_type by auto
qed

(* Exercise 2.1.18 *)
lemma element_monomorphism:
  "x \<in>\<^sub>c X \<Longrightarrow> monomorphism x"
  unfolding monomorphism_def
  by (metis comp_monic_imp_monic comp_type id_isomorphism id_type iso_imp_epi_and_monic
      monomorphism_def terminal_func_type terminal_func_unique)

lemma one_unique_element:
  "\<exists>! x. x \<in>\<^sub>c one"
proof (rule_tac a="id one" in ex1I)
  show "id\<^sub>c one \<in>\<^sub>c one"
    by (simp add: id_type)
next
  fix x
  assume "x \<in>\<^sub>c one"
  then show "x = id\<^sub>c one"
    by (metis id_type terminal_func_unique)
qed

lemma one_cross_one_unique_element:
  "\<exists>! x. x \<in>\<^sub>c one \<times>\<^sub>c one"
proof (rule_tac a="diagonal one" in ex1I)
  show "diagonal one \<in>\<^sub>c one \<times>\<^sub>c one"
    by (simp add: cfunc_prod_type diagonal_def id_type)
next
  fix x
  assume "x \<in>\<^sub>c one \<times>\<^sub>c one"
  then show "x = diagonal one"
    by (smt cfunc_prod_unique comp_type diagonal_def id_type left_cart_proj_type right_cart_proj_type terminal_func_unique)
qed

(* Proposition 2.1.19 *)
lemma single_elem_iso_one:
  "(\<exists>! x. x \<in>\<^sub>c X) \<longleftrightarrow> X \<cong> one"
proof
  assume X_iso_one: "X \<cong> one"
  then have "one \<cong> X"
    by (simp add: isomorphic_is_symmetric)
  then obtain f where f_type: "f : one \<rightarrow> X" and f_iso: "isomorphism f"
    using is_isomorphic_def by blast

  show "\<exists>!x. x \<in>\<^sub>c X"
  proof (rule_tac a=f in ex1I, auto simp add: f_type)
    fix x
    assume x_type: "x \<in>\<^sub>c X"
    then have \<beta>x_eq_\<beta>f: "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x = \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f"
      using f_type one_unique_element terminal_func_type by auto
    have "isomorphism (\<beta>\<^bsub>X\<^esub>)"
      using X_iso_one is_isomorphic_def terminal_func_unique by blast
    then have "monomorphism (\<beta>\<^bsub>X\<^esub>)"
      by (simp add: iso_imp_epi_and_monic)
    then show "x = f"
      unfolding monomorphism_def using \<beta>x_eq_\<beta>f x_type cfunc_type_def f_type terminal_func_type by auto 
  qed
next
  assume "\<exists>!x. x \<in>\<^sub>c X"
  then obtain x where x_type: "x : one \<rightarrow> X" and x_unique: "\<forall> y. y : one \<rightarrow> X \<longrightarrow> x = y"
    by blast

  have "terminal_object X"
    unfolding terminal_object_def
  proof 
    fix Y
    show "\<exists>!f. f : Y \<rightarrow> X"
    proof (rule_tac a="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" in ex1I)
      show "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X"
        using comp_type terminal_func_type x_type by blast
    next
      fix xa
      assume xa_type: "xa : Y \<rightarrow> X"
      show "xa = x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
      proof (rule ccontr)
        assume "xa \<noteq> x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
        then obtain y where elems_neq: "xa \<circ>\<^sub>c y \<noteq> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y" and y_type: "y : one \<rightarrow> Y"
          using one_separator_contrapos[where f=xa, where g="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>", where X=Y, where Y=X]
          using comp_type terminal_func_type x_type xa_type by blast
        have elem1: "xa \<circ>\<^sub>c y \<in>\<^sub>c X"
          using xa_type y_type by auto
        have elem2: "(x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y \<in>\<^sub>c X"
          using comp_type terminal_func_type x_type y_type by blast
        show False
          using elem1 elem2 elems_neq x_unique by blast
      qed
    qed
  qed
  then show "X \<cong> one"
    by (simp add: one_terminal_object terminal_objects_isomorphic)
qed

(* Converse to Exercise 2.1.15: Part 1 *)
lemma iso_to1_is_term:
  assumes "X \<cong> one"
  shows "terminal_object X"
  unfolding terminal_object_def
proof 
   fix Y
   obtain x where x_type: "x : one \<rightarrow> X" and x_unique: "\<forall> y. y : one \<rightarrow> X \<longrightarrow> x = y"
      using assms single_elem_iso_one by fastforce 
   show  "\<exists>!f. f : Y \<rightarrow> X"
      proof (rule_tac a="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>" in ex1I)
         show "x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub> : Y \<rightarrow> X"
           using comp_type terminal_func_type x_type by blast
      next
         fix xa
         assume xa_type: "xa : Y \<rightarrow> X"
         show "xa = x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
         proof (rule ccontr)
           assume "xa \<noteq> x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>"
           then obtain y where elems_neq: "xa \<circ>\<^sub>c y \<noteq> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y" and y_type: "y : one \<rightarrow> Y"
             using one_separator_contrapos[where f=xa, where g="x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>", where X=Y, where Y=X]
             using comp_type terminal_func_type x_type xa_type by blast
           have elem1: "xa \<circ>\<^sub>c y \<in>\<^sub>c X"
             using xa_type y_type by auto
           have elem2: "(x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>) \<circ>\<^sub>c y \<in>\<^sub>c X"
             using comp_type terminal_func_type x_type y_type by blast
           show False
             using elem1 elem2 elems_neq x_unique by blast
         qed
      qed
qed 

(* Converse to Exercise 2.1.15: Part 2 *)

lemma iso_to_term_is_term:
  assumes "X \<cong> Y" and "terminal_object Y"
  shows "terminal_object X"
  by (meson assms(1) assms(2) iso_to1_is_term isomorphic_is_transitive one_terminal_object terminal_objects_isomorphic)

(* Proposition 2.1.20 *)
lemma X_is_cart_prod1:
  "is_cart_prod X (id X) (\<beta>\<^bsub>X\<^esub>) X one"
  unfolding is_cart_prod_def
proof auto
  show "id\<^sub>c X : X \<rightarrow> X"
    by (simp add: id_type)
next
  show "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> one"
    by (simp add: terminal_func_type)
next
  fix f g Y
  assume f_type: "f : Y \<rightarrow> X" and g_type: "g : Y \<rightarrow> one"
  then show "\<exists>h. h : Y \<rightarrow> X \<and>
           id\<^sub>c X \<circ>\<^sub>c h = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = g \<and> (\<forall>h2. h2 : Y \<rightarrow> X \<and> id\<^sub>c X \<circ>\<^sub>c h2 = f \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = g \<longrightarrow> h2 = h)"
  proof (rule_tac x=f in exI, auto)
    show "id X \<circ>\<^sub>c f = f"
      using cfunc_type_def f_type id_left_unit by auto
    show "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c f = g"
      by (metis comp_type f_type g_type terminal_func_type terminal_func_unique)
    show "\<And>h2. h2 : Y \<rightarrow> X \<Longrightarrow> h2 = id\<^sub>c X \<circ>\<^sub>c h2"
      using cfunc_type_def id_left_unit by auto
  qed
qed

lemma X_is_cart_prod2:
  "is_cart_prod X (\<beta>\<^bsub>X\<^esub>) (id X) one X"
  unfolding is_cart_prod_def
proof auto
  show "id\<^sub>c X : X \<rightarrow> X"
    by (simp add: id_type)
next
  show "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> one"
    by (simp add: terminal_func_type)
next
  fix f g Z
  assume f_type: "f : Z \<rightarrow> one" and g_type: "g : Z \<rightarrow> X"
  then show "\<exists>h. h : Z \<rightarrow> X \<and>
           \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h = f \<and> id\<^sub>c X \<circ>\<^sub>c h = g \<and> (\<forall>h2. h2 : Z \<rightarrow> X \<and> \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h2 = f \<and> id\<^sub>c X \<circ>\<^sub>c h2 = g \<longrightarrow> h2 = h)"
  proof (rule_tac x=g in exI, auto)
    show "id\<^sub>c X \<circ>\<^sub>c g = g"
      using cfunc_type_def g_type id_left_unit by auto
    show "\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g = f"
      by (metis comp_type f_type g_type terminal_func_type terminal_func_unique)
    show "\<And>h2. h2 : Z \<rightarrow> X \<Longrightarrow> h2 = id\<^sub>c X \<circ>\<^sub>c h2"
      using cfunc_type_def id_left_unit by auto
  qed
qed

lemma A_x_one_iso_A:
  "X \<times>\<^sub>c one \<cong> X"
  by (metis X_is_cart_prod1 canonical_cart_prod_is_cart_prod cart_prods_isomorphic fst_conv is_isomorphic_def snd_conv)

lemma one_x_A_iso_A:
  "one \<times>\<^sub>c X \<cong> X"
  by (meson A_x_one_iso_A isomorphic_is_transitive product_commutes)

(* Proposition 2.1.21 *)
lemma cart_prod_elem_eq:
  assumes "a \<in>\<^sub>c X \<times>\<^sub>c Y" "b \<in>\<^sub>c X \<times>\<^sub>c Y"
  shows "a = b \<longleftrightarrow> 
    (left_cart_proj X Y \<circ>\<^sub>c a = left_cart_proj X Y \<circ>\<^sub>c b 
      \<and> right_cart_proj X Y \<circ>\<^sub>c a = right_cart_proj X Y \<circ>\<^sub>c b)"
  by (metis (full_types) assms cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type)

lemma cart_prod_eq:
  assumes "a : Z \<rightarrow> X \<times>\<^sub>c Y" "b : Z \<rightarrow>  X \<times>\<^sub>c Y"
  shows "a = b \<longleftrightarrow> 
    (left_cart_proj X Y \<circ>\<^sub>c a = left_cart_proj X Y \<circ>\<^sub>c b 
      \<and> right_cart_proj X Y \<circ>\<^sub>c a = right_cart_proj X Y \<circ>\<^sub>c b)"
  by (metis (full_types) assms cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type)

lemma cart_prod_decomp:
  assumes "a \<in>\<^sub>c X \<times>\<^sub>c Y"
  shows "\<exists> x y. a = \<langle>x, y\<rangle> \<and> x \<in>\<^sub>c X \<and> y \<in>\<^sub>c Y"
proof (rule_tac x="left_cart_proj X Y \<circ>\<^sub>c a" in exI, rule_tac x="right_cart_proj X Y \<circ>\<^sub>c a" in exI, auto)
  show "a = \<langle>left_cart_proj X Y \<circ>\<^sub>c a,right_cart_proj X Y \<circ>\<^sub>c a\<rangle>"
    using assms cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type by blast
  show "left_cart_proj X Y \<circ>\<^sub>c a \<in>\<^sub>c X"
    using assms left_cart_proj_type by auto
  show "right_cart_proj X Y \<circ>\<^sub>c a \<in>\<^sub>c Y"
    using assms right_cart_proj_type by auto
qed

(* Note 2.1.22 *)
lemma  element_pair_eq:
  assumes "x \<in>\<^sub>c X" "x' \<in>\<^sub>c X" "y \<in>\<^sub>c Y" "y' \<in>\<^sub>c Y"
  shows "\<langle>x, y\<rangle> = \<langle>x', y'\<rangle> \<longleftrightarrow> x = x' \<and> y = y'"
  by (metis assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)

(* Proposition 2.1.23 *)
lemma nonempty_right_imp_left_proj_epimorphism:
  "nonempty Y \<Longrightarrow> epimorphism (left_cart_proj X Y)"
proof -
  assume "nonempty Y"
  then obtain y where "y : one \<rightarrow> Y"
    using nonempty_def by blast
  then have "(left_cart_proj X Y) \<circ>\<^sub>c \<langle>id X, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> = id X"
    using comp_type id_type left_cart_proj_cfunc_prod terminal_func_type by blast
  then have "epimorphism ((left_cart_proj X Y) \<circ>\<^sub>c \<langle>id X, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"
    by (simp add: id_isomorphism iso_imp_epi_and_monic)
  then show "epimorphism (left_cart_proj X Y)"
    using comp_epi_imp_epi by blast
qed

(*Dual to Proposition 2.1.23 *)
lemma nonempty_left_imp_right_proj_epimorphism:
  "nonempty X \<Longrightarrow> epimorphism (right_cart_proj X Y)"
proof - 
  assume "nonempty X"
  then obtain y where "y: one \<rightarrow> X"
    using nonempty_def by blast
   then have "(right_cart_proj X Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>, id Y\<rangle> = id Y"
     using comp_type id_type right_cart_proj_cfunc_prod terminal_func_type by blast
    then have "epimorphism ((right_cart_proj X Y) \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>,id Y\<rangle>)"
      by (simp add: id_isomorphism iso_imp_epi_and_monic)
    then show "epimorphism (right_cart_proj X Y)"
    using comp_epi_imp_epi by blast
qed

(* Definition 2.1.24 *)
definition injective :: "cfunc \<Rightarrow> bool" where
 "injective f  \<longleftrightarrow> (\<forall> x y. (x \<in>\<^sub>c domain f \<and> y \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y) \<longrightarrow> x = y)"

(* Exercise 2.1.26 *)
lemma monomorphism_imp_injective:
  "monomorphism f \<Longrightarrow> injective f"
  by (simp add: cfunc_type_def injective_def monomorphism_def)

(* Proposition 2.1.27 *)
lemma injective_imp_monomorphism:
  assumes "f \<in> ETCS_func"
  shows "injective f \<Longrightarrow> monomorphism f"
  unfolding monomorphism_def injective_def
proof safe
  fix g h
  assume f_inj: "\<forall>x y. x \<in>\<^sub>c domain f \<and> y \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y \<longrightarrow> x = y"
  assume cd_g_eq_d_f: "codomain g = domain f"
  assume cd_h_eq_d_f: "codomain h = domain f"
  assume fg_eq_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
  assume g_ETCS: "g \<in> ETCS_func"
  assume h_ETCS: "h \<in> ETCS_func"

  obtain X Y where f_type: "f : X \<rightarrow> Y"
    using assms cfunc_type_def by blast
  obtain A where g_type: "g : A \<rightarrow> X" and h_type: "h : A \<rightarrow> X"
    by (metis cd_g_eq_d_f cd_h_eq_d_f cfunc_type_def domain_comp f_type fg_eq_fh g_ETCS h_ETCS)

  have "(\<forall>x. x \<in>\<^sub>c A \<longrightarrow> g \<circ>\<^sub>c x = h \<circ>\<^sub>c x)"
  proof auto
    fix x
    assume x_in_A: "x \<in>\<^sub>c A"

    have "f \<circ>\<^sub>c (g \<circ>\<^sub>c x) = f \<circ>\<^sub>c (h \<circ>\<^sub>c x)"
      by (simp add: comp_associative fg_eq_fh)
    then show "g \<circ>\<^sub>c x = h \<circ>\<^sub>c x"
      using cd_h_eq_d_f cfunc_type_def comp_type f_inj g_type h_type x_in_A by presburger
  qed
  then show "g = h"
    using g_type h_type one_separator by auto
qed

(* Definition 2.1.28 *)
definition surjective :: "cfunc \<Rightarrow> bool" where
 "surjective f  \<longleftrightarrow> (\<forall>y. y \<in>\<^sub>c codomain f \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = y))"

(* Exercise 2.1.30 *)
lemma surjective_is_epimorphism:
  "surjective f \<Longrightarrow> epimorphism f"
  unfolding surjective_def epimorphism_def
proof (cases "nonempty (codomain f)", auto)
  fix g h
  assume f_surj: "\<forall>y. y \<in>\<^sub>c codomain f \<longrightarrow> (\<exists>x. x \<in>\<^sub>c domain f \<and> f \<circ>\<^sub>c x = y)"
  assume d_g_eq_cd_f: "domain g = codomain f"
  assume d_h_eq_cd_f: "domain h = codomain f"
  assume gf_eq_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
  assume g_ETCS: "g \<in> ETCS_func" 
  assume h_ETCS: "h \<in> ETCS_func"
  assume nonempty: "nonempty (codomain f)"

  obtain X Y where f_type: "f : X \<rightarrow> Y"
    using nonempty cfunc_type_def compatible_comp_ETCS_func f_surj nonempty_def by auto
  obtain A where g_type: "g : Y \<rightarrow> A" and h_type: "h : Y \<rightarrow> A"
    by (metis cfunc_type_def codomain_comp d_g_eq_cd_f d_h_eq_cd_f f_type g_ETCS gf_eq_hf h_ETCS)

  show "g = h"
  proof (rule ccontr)
    assume "g \<noteq> h"
    then obtain y where y_in_X: "y \<in>\<^sub>c Y" and gy_neq_hy: "g \<circ>\<^sub>c y \<noteq> h \<circ>\<^sub>c y"
      using g_type h_type one_separator by blast
    then obtain x where "x \<in>\<^sub>c X" and "f \<circ>\<^sub>c x = y"
      using cfunc_type_def f_surj f_type by auto
    then have "g \<circ>\<^sub>c f \<circ>\<^sub>c x \<noteq> h \<circ>\<^sub>c f \<circ>\<^sub>c x"
      by (simp add: gy_neq_hy)
    then have "g \<circ>\<^sub>c f \<noteq> h \<circ>\<^sub>c f"
      using comp_associative by auto
    then show False
      using gf_eq_hf by auto
  qed
next
  fix g h
  assume empty: "\<not> nonempty (codomain f)"
  assume "g \<in> ETCS_func" "h \<in> ETCS_func" "domain g = codomain f" "domain h = codomain f"
  then show "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<Longrightarrow> g = h"
    by (metis empty cfunc_type_def codomain_comp nonempty_def one_separator)
qed

section \<open>Axiom 4: Equalizers\<close>

definition equalizer :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "equalizer E m f g \<longleftrightarrow> (\<exists> X Y. (f : X \<rightarrow> Y) \<and> (g : X \<rightarrow> Y) \<and> (m : E \<rightarrow> X)
    \<and> (f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)
    \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)))"

axiomatization where
  equalizer_exists: "((f : X \<rightarrow> Y) \<and> (g : X \<rightarrow> Y)) \<longrightarrow> (\<exists> E m. equalizer E m f g)"

(*Exercise 2.1.31*)
lemma
  assumes "equalizer E m f g" "equalizer E' m' f g"
  shows "\<exists> k. k : E \<rightarrow> E' \<and> isomorphism k"
proof -
  have fm_eq_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
    using assms(1) equalizer_def by blast
  have fm'_eq_gm': "f \<circ>\<^sub>c m' = g \<circ>\<^sub>c m'"
    using assms(2) equalizer_def by blast

  obtain k where k_type: "k : E' \<rightarrow> E" and mk_eq_m': "m \<circ>\<^sub>c k = m'"
    by (metis assms(1) assms(2) cfunc_type_def equalizer_def)
  obtain k' where k_type: "k' : E \<rightarrow> E'" and m'k_eq_m: "m' \<circ>\<^sub>c k' = m"
    by (metis assms(1) assms(2) cfunc_type_def equalizer_def)

  have "f \<circ>\<^sub>c m \<circ>\<^sub>c k \<circ>\<^sub>c k' = g \<circ>\<^sub>c m \<circ>\<^sub>c k \<circ>\<^sub>c k'"
    by (simp add: comp_associative fm_eq_gm)

  have "k \<circ>\<^sub>c k' : E \<rightarrow> E \<and> m \<circ>\<^sub>c k \<circ>\<^sub>c k' = m"
    by (metis assms(1) cfunc_type_def comp_associative compatible_comp_ETCS_func equalizer_def m'k_eq_m mk_eq_m')
  then have kk'_eq_id: "k \<circ>\<^sub>c k' = id E"
    by (metis assms(1) cfunc_type_def equalizer_def id_right_unit id_type)

  have "k' \<circ>\<^sub>c k : E' \<rightarrow> E' \<and> m' \<circ>\<^sub>c k' \<circ>\<^sub>c k = m'"
    by (metis assms(2) cfunc_type_def comp_associative compatible_comp_ETCS_func equalizer_def mk_eq_m' m'k_eq_m)
  then have k'k_eq_id: "k' \<circ>\<^sub>c k = id E'"
    by (metis assms(2) cfunc_type_def equalizer_def id_right_unit id_type)

  show "\<exists>k. k : E \<rightarrow> E' \<and> isomorphism k"
    apply (rule_tac x="k'" in exI)
    by (metis codomain_comp domain_comp id_codomain id_domain isomorphism_def k'k_eq_id k_type kk'_eq_id)
qed

(*What do we name this lemma?*)
lemma 
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> Y"
  shows "\<exists> E m. (m : E \<rightarrow> X) \<and> (f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)"
proof -
  obtain E m where "equalizer E m f g"
    using assms equalizer_exists by blast
  then show "\<exists> E m. (m : E \<rightarrow> X) \<and> (f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)"
    using assms unfolding equalizer_def cfunc_type_def by auto
qed


(*Definition 2.1.32*)
definition factors_through :: "cfunc  \<Rightarrow> cfunc \<Rightarrow> bool" (infix "factorsthru" 90)
  where "g factorsthru f \<longleftrightarrow> (\<exists> h. (h: domain(g)\<rightarrow> domain(f)) \<and> f \<circ>\<^sub>c h = g)"


(*Exercise 2.1.33*)
lemma xfactorthru_equalizer_iff_fx_eq_gx:
  assumes "f: X\<rightarrow> Y" "g:X \<rightarrow> Y" "equalizer E m f g" "x\<in>\<^sub>c X"
  shows "x factorsthru m \<longleftrightarrow> f \<circ>\<^sub>c x = g  \<circ>\<^sub>c x"
proof auto
  assume LHS: "x factorsthru m"
  show "f \<circ>\<^sub>c x = g  \<circ>\<^sub>c x"
    using LHS assms(3) comp_associative equalizer_def factors_through_def by fastforce
next
  assume RHS: "f \<circ>\<^sub>c x = g  \<circ>\<^sub>c x"
  show "x factorsthru m"
    unfolding equalizer_def cfunc_type_def factors_through_def
    by (metis RHS assms(1) assms(3) assms(4) cfunc_type_def equalizer_def)
qed

(*Proposition 2.1.34*)
lemma equalizer_is_monomorphism:
"equalizer E m f g \<Longrightarrow>  monomorphism(m)"
  unfolding equalizer_def monomorphism_def
proof auto
  fix ga h X Y
  assume ga_ETCS: "ga \<in> ETCS_func"
  assume h_ETCS: "h \<in> ETCS_func"
  assume f_type: "f : X \<rightarrow> Y"
  assume g_type: "g : X \<rightarrow> Y"
  assume m_type: "m : E \<rightarrow> X"
  assume fm_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
  assume uniqueness: "\<forall>h F. h : F \<rightarrow> X \<and> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h \<longrightarrow> (\<exists>!k. k : F \<rightarrow> E \<and> m \<circ>\<^sub>c k = h)"
  assume relation_ga: "codomain ga = domain m"
  assume relation_h: "codomain h = domain m" 
  assume m_ga_mh: "m \<circ>\<^sub>c ga = m \<circ>\<^sub>c h" 
  
  have  "f \<circ>\<^sub>c m \<circ>\<^sub>c ga =  g \<circ>\<^sub>c m \<circ>\<^sub>c h"
    by (simp add: comp_associative fm_gm m_ga_mh)
  then obtain z where "z: domain(ga) \<rightarrow> E \<and> m \<circ>\<^sub>c z = m \<circ>\<^sub>c ga \<and> 
    (\<forall> j. j:domain(ga) \<rightarrow> E \<and>  m \<circ>\<^sub>c j = m \<circ>\<^sub>c ga \<longrightarrow> j = z)"
    using uniqueness apply (erule_tac x="m \<circ>\<^sub>c ga" in allE, erule_tac x="domain(ga)" in allE)
    by (metis (mono_tags, lifting) cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp ga_ETCS m_ga_mh m_type relation_ga)
  then show "ga = h"
    by (metis cfunc_type_def domain_comp ga_ETCS h_ETCS m_ga_mh m_type relation_ga relation_h)
qed


(* Definition 2.1.35 *)
definition regular_monomorphism :: "cfunc \<Rightarrow> bool"
  where "regular_monomorphism f  \<longleftrightarrow>  
          (\<exists> g h. (domain(g) = codomain(f) \<and> domain(h) = codomain(f) \<and> equalizer (domain f) f g h))"

(*Exercise 2.1.36*)
lemma epi_regmon_is_iso:
  assumes "epimorphism(f)" "regular_monomorphism(f)"
  shows "isomorphism(f)"
proof -
  obtain g h where g_type: "domain(g) = codomain(f)" and
                   h_type: "domain(h) = codomain(f)" and
                   f_equalizer: "equalizer (domain f) f g h"
    using assms(2) regular_monomorphism_def by auto
  then have "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
    using equalizer_def by blast
  then have "g = h"
    using assms(1) cfunc_type_def epimorphism_def equalizer_def f_equalizer by auto
  then have "g \<circ>\<^sub>c id(codomain(f)) = h \<circ>\<^sub>c id(codomain(f))"
    by simp
  then obtain k where k_type: "f \<circ>\<^sub>c k = id(codomain(f))"
    by (metis cfunc_type_def equalizer_def f_equalizer id_type)
  then have "f \<circ>\<^sub>c id(domain(f)) = f \<circ>\<^sub>c (k \<circ>\<^sub>c f)"
    using comp_associative id_left_unit id_right_unit by auto
  then have "k \<circ>\<^sub>c f = id(domain(f))"
    by (metis k_type compatible_comp_ETCS_func equalizer_is_monomorphism f_equalizer id_ETCS_func id_codomain monomorphism_def)
  then show "isomorphism(f)"
    by (metis (mono_tags, lifting) codomain_comp domain_comp id_codomain id_domain isomorphism_def k_type)
qed

(*Definition 2.1.37*)
definition subobject_of :: "cset \<times> cfunc \<Rightarrow> cset \<Rightarrow> bool" (infix "\<subseteq>\<^sub>c" 50)
  where "B \<subseteq>\<^sub>c X \<longleftrightarrow> (snd B : fst B \<rightarrow> X \<and> monomorphism (snd B))"

lemma subobject_of_def2:
  "(B,m) \<subseteq>\<^sub>c X = (m : B \<rightarrow> X \<and> monomorphism m)"
  by (simp add: subobject_of_def)

definition relative_subset :: "cset \<times> cfunc \<Rightarrow> cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" ("_\<subseteq>\<^bsub>_\<^esub>_" [51,50,51]50)
  where "B \<subseteq>\<^bsub>X\<^esub> A  \<longleftrightarrow> 
    (snd B : fst B \<rightarrow> X \<and> monomorphism (snd B) \<and> snd A : fst A \<rightarrow> X \<and> monomorphism (snd A)
          \<and> (\<exists> k. k: fst B \<rightarrow> fst A \<and> snd A \<circ>\<^sub>c k = snd B))"

lemma relative_subset_def2: 
  "(B,m) \<subseteq>\<^bsub>X\<^esub> (A,n) = (m : B \<rightarrow> X \<and> monomorphism m \<and> n : A \<rightarrow> X \<and> monomorphism n
          \<and> (\<exists> k. k: B \<rightarrow> A \<and> n \<circ>\<^sub>c k = m))"
  unfolding relative_subset_def by auto

lemma subobject_is_relative_subset: "(B,m) \<subseteq>\<^sub>c A \<longleftrightarrow> (B,m) \<subseteq>\<^bsub>A\<^esub> (A, id(A))"
  unfolding relative_subset_def2 subobject_of_def2
  using cfunc_type_def id_isomorphism id_left_unit id_type iso_imp_epi_and_monic by auto

definition inverse_image :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1[_]\<^bsub>_\<^esub>" 100) where
  "inverse_image f B m = (SOME A. \<exists> X Y k. f : X \<rightarrow> Y \<and> m : B \<rightarrow> Y \<and> monomorphism m \<and>
    equalizer A k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B))"

lemma inverse_image_is_equalizer:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "\<exists>k. equalizer (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
proof -
  obtain A k where "equalizer A k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    by (meson assms(1) assms(2) comp_type equalizer_exists left_cart_proj_type right_cart_proj_type)
  then have "\<exists> X Y k. f : X \<rightarrow> Y \<and> m : B \<rightarrow> Y \<and> monomorphism m \<and>
    equalizer (inverse_image f B m) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    unfolding inverse_image_def apply (rule_tac someI_ex, auto)
    by (rule_tac x="A" in exI, rule_tac x="X" in exI, rule_tac x="Y" in exI, auto simp add: assms)
  then show "\<exists>k. equalizer (inverse_image f B m) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    using assms(2) cfunc_type_def by auto
qed

definition inverse_image_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "inverse_image_mapping f B m = (SOME k. \<exists> X Y. f : X \<rightarrow> Y \<and> m : B \<rightarrow> Y \<and> monomorphism m \<and>
    equalizer (inverse_image f B m) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B))"

lemma inverse_image_is_equalizer2:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "equalizer (inverse_image f B m) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
proof -
  obtain k where "equalizer (inverse_image f B m) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    using assms(1) assms(2) assms(3) inverse_image_is_equalizer by blast
  then have "\<exists> X Y. f : X \<rightarrow> Y \<and> m : B \<rightarrow> Y \<and> monomorphism m \<and>
    equalizer (inverse_image f B m) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    unfolding inverse_image_mapping_def using assms by (rule_tac someI_ex, auto)
  then show "equalizer (inverse_image f B m) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    using assms(2) cfunc_type_def by auto
qed

lemma inverse_image_mapping_type:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "inverse_image_mapping f B m : (inverse_image f B m) \<rightarrow> X \<times>\<^sub>c B"
  using assms cfunc_type_def domain_comp equalizer_def inverse_image_is_equalizer2 left_cart_proj_type by auto

lemma inverse_image_mapping_eq:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "f \<circ>\<^sub>c left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m
    = m \<circ>\<^sub>c right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m"
  by (metis assms comp_associative equalizer_def inverse_image_is_equalizer2)

lemma inverse_image_mapping_monomorphism:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "monomorphism (inverse_image_mapping f B m)"
  using assms equalizer_is_monomorphism inverse_image_is_equalizer2 by blast

(* Proposition 2.1.38 *)
lemma inverse_image_monomorphism:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "monomorphism (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)"
  unfolding monomorphism_def
proof auto
  fix g h
  assume g_ETCS: "g \<in> ETCS_func"
  assume h_ETCS: "h \<in> ETCS_func"
  assume codomain_g: "codomain g = domain (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)"
  assume codomain_h: "codomain h = domain (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)"

  have g_comp1_ETCS: "inverse_image_mapping f B m \<circ>\<^sub>c g \<in> ETCS_func"
    using assms cfunc_type_def codomain_g compatible_comp_ETCS_func domain_comp g_ETCS inverse_image_mapping_type by auto
  have h_comp1_ETCS: "inverse_image_mapping f B m \<circ>\<^sub>c h \<in> ETCS_func"
    using assms cfunc_type_def codomain_h compatible_comp_ETCS_func domain_comp h_ETCS inverse_image_mapping_type by auto
  have g_comp2_ETCS: "(right_cart_proj X (domain m) \<circ>\<^sub>c inverse_image_mapping f (domain m) m) \<circ>\<^sub>c g \<in> ETCS_func"
    using assms cfunc_type_def compatible_comp_ETCS_func domain_comp g_comp1_ETCS inverse_image_mapping_type right_cart_proj_type by auto
  have h_comp2_ETCS: "(right_cart_proj X (domain m) \<circ>\<^sub>c inverse_image_mapping f (domain m) m) \<circ>\<^sub>c h \<in> ETCS_func"
    using assms cfunc_type_def compatible_comp_ETCS_func domain_comp h_comp1_ETCS inverse_image_mapping_type right_cart_proj_type by auto

  assume eq_assm: "(left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
  then have "f \<circ>\<^sub>c (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = f \<circ>\<^sub>c (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    by auto
  then have "m \<circ>\<^sub>c (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = m \<circ>\<^sub>c (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    using assms comp_associative inverse_image_mapping_eq by auto
  then have "(right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    using assms cfunc_type_def codomain_comp g_comp2_ETCS h_comp2_ETCS monomorphism_def right_cart_proj_type by auto
  then have "inverse_image_mapping f B m \<circ>\<^sub>c g = inverse_image_mapping f B m \<circ>\<^sub>c h"
    using cart_prod_eq[where a="inverse_image_mapping f B m \<circ>\<^sub>c g", where b="inverse_image_mapping f B m \<circ>\<^sub>c g"]
    by (metis assms(1) cart_prod_eq cfunc_type_def comp_associative compatible_comp_ETCS_func eq_assm h_comp2_ETCS right_cart_proj_type)
  then show "g = h"
    by (metis assms compatible_comp_ETCS_func g_comp1_ETCS inverse_image_mapping_monomorphism monomorphism_def)
qed

lemma inverse_image_subobject:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "(inverse_image f B m, left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<subseteq>\<^sub>c X"
  using assms cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp
        inverse_image_mapping_type inverse_image_monomorphism left_cart_proj_type subobject_of_def2 
  by auto

lemma inverse_image_pullback:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "is_pullback (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>) B X Y 
    (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) m
    (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) f"
  unfolding is_pullback_def square_commutes_def using assms
proof auto
  show right_type: "right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m : f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<rightarrow> B"
    using assms cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp
      inverse_image_mapping_type right_cart_proj_type by auto
  show left_type: "left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m : f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<rightarrow> X"
    using assms fst_conv inverse_image_subobject subobject_of_def by auto

  show "m \<circ>\<^sub>c right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m =
      f \<circ>\<^sub>c left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m"
    using assms inverse_image_mapping_eq by auto

  show "\<And>Z k h.  k : Z \<rightarrow> B \<Longrightarrow> h : Z \<rightarrow> X \<Longrightarrow> m \<circ>\<^sub>c k = f \<circ>\<^sub>c h \<Longrightarrow>
       \<exists>j. j : Z \<rightarrow> (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>) \<and>
           (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = k \<and>
           (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = h"
  proof -
    fix Z k h
    assume k_type: "k : Z \<rightarrow> B" and h_type: "h : Z \<rightarrow> X"
    assume mk_eq_fh: "m \<circ>\<^sub>c k = f \<circ>\<^sub>c h"

    have "equalizer (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B )"
      using assms inverse_image_is_equalizer2 by blast
    then have "\<forall>h F. h : F \<rightarrow> (X \<times>\<^sub>c B) 
              \<and> (f \<circ>\<^sub>c left_cart_proj X B) \<circ>\<^sub>c h = (m \<circ>\<^sub>c right_cart_proj X B) \<circ>\<^sub>c h \<longrightarrow>
            (\<exists>!k. k : F \<rightarrow> (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>) \<and> inverse_image_mapping f B m \<circ>\<^sub>c k = h)"
      unfolding equalizer_def using cfunc_type_def domain_comp left_cart_proj_type by auto 

      thm inverse_image_is_equalizer2

(* Definition 2.1.39 *)
definition relative_member :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" ("_ \<in>\<^bsub>_\<^esub> _" [51,50,51]50) where
  "x \<in>\<^bsub>X\<^esub> B \<longleftrightarrow> (x \<in>\<^sub>c X \<and> monomorphism (snd B) \<and> snd B : fst B \<rightarrow> X \<and> x factorsthru (snd B))"

lemma relative_member_def2:
  "x \<in>\<^bsub>X\<^esub> (B, m) = (x \<in>\<^sub>c X \<and> monomorphism m \<and> m : B \<rightarrow> X \<and> x factorsthru m)"
  unfolding relative_member_def by auto

(* Proposition 2.1.40 *)
lemma 
  assumes "(A,n) \<subseteq>\<^bsub>X\<^esub> (B,m)" "x \<in>\<^sub>c X"
  shows "x \<in>\<^bsub>X\<^esub> (A,n) \<Longrightarrow> x \<in>\<^bsub>X\<^esub> (B,m)"
  using assms unfolding relative_member_def2 relative_subset_def2
proof auto
  fix k
  assume m_type: "m : B \<rightarrow> X"
  assume k_type: "k : A \<rightarrow> B"

  assume m_monomorphism: "monomorphism m"
  assume mk_monomorphism: "monomorphism (m \<circ>\<^sub>c k)"

  assume n_eq_mk: "n = m \<circ>\<^sub>c k"

  assume factorsthru_mk: "x factorsthru (m \<circ>\<^sub>c k)"
  
  obtain a where a_assms: "a \<in>\<^sub>c A \<and> (m \<circ>\<^sub>c k) \<circ>\<^sub>c a = x"
    using assms(2) cfunc_type_def domain_comp factors_through_def factorsthru_mk k_type by auto
  then show "x factorsthru m "
    unfolding factors_through_def 
    using cfunc_type_def comp_type k_type m_type comp_associative
    by (rule_tac x="k \<circ>\<^sub>c a" in exI, auto)
qed

thm equalizer_def

(* Definition 2.1.42 *)
definition fibered_product :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset" ("_ \<^bsub>_\<^esub>\<times>\<^sub>c\<^bsub>_\<^esub> _" [66,66,65,65]65) where
  "X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y = (SOME E. \<exists> Z m. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
    equalizer E m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y))"

lemma fibered_product_equalizer:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "\<exists> m. equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
proof -
  have type1: "f \<circ>\<^sub>c left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Z"
    using assms(1) comp_type left_cart_proj_type by blast
  have type2: "g \<circ>\<^sub>c right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Z"
    using assms(2) comp_type right_cart_proj_type by blast

  obtain E m where "equalizer E m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    using equalizer_exists type1 type2 by blast
  then have "\<exists>x Z m. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
      equalizer x m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    using assms(1) assms(2) by blast
  then have "\<exists> Z m. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and> 
      equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    unfolding fibered_product_def by (rule someI_ex)
  then show "\<exists>m. equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    by auto
qed

definition fibered_product_morphism :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_morphism X f g Y = (SOME m. \<exists> Z. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
    equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y))"

lemma fibered_product_morphism_equalizer:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) (fibered_product_morphism X f g Y) (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
proof -

  have "\<exists>x Z. f : X \<rightarrow> Z \<and>
      g : Y \<rightarrow> Z \<and> equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) x (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    using assms fibered_product_equalizer by blast
  then have "\<exists>Z. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
    equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) (fibered_product_morphism X f g Y) (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    unfolding fibered_product_morphism_def apply - by (rule someI_ex, auto)
  then show "equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) (fibered_product_morphism X f g Y) (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    by auto
qed

lemma fibered_product_morphism_type:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "fibered_product_morphism X f g Y : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<rightarrow> X \<times>\<^sub>c Y"
  using assms cfunc_type_def domain_comp equalizer_def fibered_product_morphism_equalizer left_cart_proj_type by auto

lemma fibered_product_morphism_monomorphism:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "monomorphism (fibered_product_morphism X f g Y)"
  using assms equalizer_is_monomorphism fibered_product_morphism_equalizer by blast

definition fibered_product_left_proj :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_left_proj X f g Y = (left_cart_proj X Y) \<circ>\<^sub>c (fibered_product_morphism X f g Y)"

lemma fibered_product_left_proj_type:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "fibered_product_left_proj X f g Y : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<rightarrow> X"
  by (metis assms comp_type fibered_product_left_proj_def fibered_product_morphism_type left_cart_proj_type)

definition fibered_product_right_proj :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_right_proj X f g Y = (right_cart_proj X Y) \<circ>\<^sub>c (fibered_product_morphism X f g Y)"

lemma fibered_product_right_proj_type:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "fibered_product_right_proj X f g Y : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<rightarrow> Y"
  by (metis assms comp_type fibered_product_right_proj_def fibered_product_morphism_type right_cart_proj_type)

lemma pair_factorsthru_fibered_product_morphism:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z" "x : A \<rightarrow> X" "y : A \<rightarrow> Y"
  shows "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y \<Longrightarrow> \<langle>x,y\<rangle> factorsthru fibered_product_morphism X f g Y"
  unfolding factors_through_def
proof -
  assume "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
  then have "(f \<circ>\<^sub>c left_cart_proj X Y) \<circ>\<^sub>c \<langle>x,y\<rangle> = (g \<circ>\<^sub>c right_cart_proj X Y) \<circ>\<^sub>c \<langle>x,y\<rangle>"
    by (metis assms(3) assms(4) comp_associative left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then have "\<exists>h. h : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<and> fibered_product_morphism X f g Y \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    using fibered_product_morphism_equalizer[where f=f, where g=g, where X=X, where Y=Y, where Z=Z] assms
    unfolding equalizer_def apply (auto, erule_tac x="\<langle>x,y\<rangle>" in allE, erule_tac x="A" in allE, auto)
    using cfunc_prod_type cfunc_type_def domain_comp left_cart_proj_type by auto
  then show "\<exists>h. h : domain \<langle>x,y\<rangle> \<rightarrow> domain (fibered_product_morphism X f g Y) \<and>
        fibered_product_morphism X f g Y \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    by (metis assms(1) assms(2) cfunc_type_def domain_comp fibered_product_morphism_type)
qed

lemma fibered_product_is_pullback:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) Y X Z  (fibered_product_right_proj X f g Y) g (fibered_product_left_proj X f g Y) f"
  unfolding is_pullback_def square_commutes_def
  using assms fibered_product_left_proj_type fibered_product_right_proj_type
proof auto
  show "g \<circ>\<^sub>c fibered_product_right_proj X f g Y = f \<circ>\<^sub>c fibered_product_left_proj X f g Y"
    by (metis assms comp_associative equalizer_def fibered_product_left_proj_def fibered_product_morphism_equalizer fibered_product_right_proj_def)
next
  fix Za k h
  assume k_type: "k : Za \<rightarrow> Y" and h_type: "h : Za \<rightarrow> X"
  assume k_h_commutes: "g \<circ>\<^sub>c k = f \<circ>\<^sub>c h"

  have "\<langle>h,k\<rangle> factorsthru fibered_product_morphism X f g Y"
    using assms h_type k_h_commutes k_type pair_factorsthru_fibered_product_morphism by auto
  then have "(\<exists>j. j : Za \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<and> fibered_product_morphism X f g Y \<circ>\<^sub>c j = \<langle>h,k\<rangle>)"
    unfolding factors_through_def apply auto
    by (smt assms cfunc_prod_comp cfunc_type_def domain_comp fibered_product_morphism_type h_type id_right_unit id_type k_type)
  then show "\<exists>j. j : Za \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<and>
           fibered_product_right_proj X f g Y \<circ>\<^sub>c j = k \<and> fibered_product_left_proj X f g Y \<circ>\<^sub>c j = h"
    by (metis comp_associative fibered_product_left_proj_def fibered_product_right_proj_def h_type k_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
next
  fix Za j y
  assume j_type: "j : Za \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y" and y_type: "y : Za \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y"
  assume "fibered_product_right_proj X f g Y \<circ>\<^sub>c y = fibered_product_right_proj X f g Y \<circ>\<^sub>c j"
  then have right_eq: "right_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c y) =
      right_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c j)"
    unfolding fibered_product_right_proj_def by (simp add: comp_associative)
  assume "fibered_product_left_proj X f g Y \<circ>\<^sub>c y = fibered_product_left_proj X f g Y \<circ>\<^sub>c j"
  then have left_eq: "left_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c y) =
      left_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c j)"
    unfolding fibered_product_left_proj_def by (simp add: comp_associative)

  have mono: "monomorphism (fibered_product_morphism X f g Y)"
    using assms fibered_product_morphism_monomorphism by auto

  have "fibered_product_morphism X f g Y \<circ>\<^sub>c y = fibered_product_morphism X f g Y \<circ>\<^sub>c j"
    using right_eq left_eq cart_prod_eq fibered_product_morphism_type y_type j_type assms
    by (subst cart_prod_eq[where Z=Za, where X=X, where Y=Y], auto)
  then show "j = y"
    using mono assms cfunc_type_def fibered_product_morphism_type j_type y_type
    unfolding monomorphism_def
    by auto 
qed

(* Exercise 2.1.44 Part 1 *)
lemma kern_pair_proj_iso_TFAE1:
  assumes "f: X \<rightarrow> Y \<and> monomorphism(f)"
  shows "(fibered_product_left_proj X f f X) = (fibered_product_right_proj X f f X)"
proof (cases "\<exists>x. x\<in>\<^sub>c X\<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub>X", auto)
  fix x
  assume x_type: "x\<in>\<^sub>c X\<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub>X"
  then have "(f\<circ>\<^sub>c (fibered_product_left_proj X f f X))\<circ>\<^sub>c x = (f\<circ>\<^sub>c (fibered_product_right_proj X f f X))\<circ>\<^sub>c x"
    by (metis assms comp_associative equalizer_def fibered_product_left_proj_def fibered_product_morphism_equalizer fibered_product_right_proj_def)
  then have "f\<circ>\<^sub>c (fibered_product_left_proj X f f X) = f\<circ>\<^sub>c (fibered_product_right_proj X f f X)"
    using assms fibered_product_is_pullback is_pullback_def square_commutes_def by auto
  then show "(fibered_product_left_proj X f f X) = (fibered_product_right_proj X f f X)"
    using assms cfunc_type_def fibered_product_left_proj_type fibered_product_right_proj_type monomorphism_def by auto
next
  assume "\<forall>x. \<not> x \<in>\<^sub>c X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
  then show "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
    using assms fibered_product_left_proj_type fibered_product_right_proj_type one_separator by blast
qed

(* Exercise 2.1.44 Part 2 *)
lemma kern_pair_proj_iso_TFAE2:
  assumes "f: X \<rightarrow> Y" "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
  shows "monomorphism f \<and> isomorphism (fibered_product_left_proj X f f X) \<and> isomorphism (fibered_product_right_proj X f f X)"
  using assms
proof auto
  have "injective f"
    unfolding injective_def
  proof auto
    fix x y
    assume x_type: "x \<in>\<^sub>c domain f" and y_type: "y \<in>\<^sub>c domain f"
    then have x_type2: "x \<in>\<^sub>c X" and y_type2: "y \<in>\<^sub>c X"
      using assms(1) cfunc_type_def by auto
    assume "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    then have factorsthru: "\<langle>x,y\<rangle> factorsthru fibered_product_morphism X f f X"
      using assms(1) pair_factorsthru_fibered_product_morphism x_type2 y_type2 by auto
    then obtain xy where xy_assms: "xy : one \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and> \<langle>x,y\<rangle> = fibered_product_morphism X f f X \<circ>\<^sub>c xy"
      unfolding factors_through_def apply auto
      by (smt assms(1) cfunc_type_def domain_comp fibered_product_morphism_type right_cart_proj_cfunc_prod x_type y_type)

    have left_proj: "fibered_product_left_proj X f f X \<circ>\<^sub>c xy = x"
      by (metis comp_associative fibered_product_left_proj_def left_cart_proj_cfunc_prod x_type2 xy_assms y_type2)
    have right_proj: "fibered_product_right_proj X f f X \<circ>\<^sub>c xy = y"
      by (metis comp_associative fibered_product_right_proj_def right_cart_proj_cfunc_prod x_type2 xy_assms y_type2)

    show "x = y"
      using assms(2) left_proj right_proj by auto
  qed
  then show "monomorphism f"
    using assms(1) cfunc_type_def injective_imp_monomorphism by auto
next
  have "diagonal X factorsthru fibered_product_morphism X f f X"
    using assms(1) diagonal_def id_type pair_factorsthru_fibered_product_morphism by fastforce
  then obtain xx where xx_assms: "xx : X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and> diagonal X = fibered_product_morphism X f f X \<circ>\<^sub>c xx"
    by (smt assms(1) cfunc_cross_prod_comp_diagonal cfunc_type_def domain_comp factors_through_def fibered_product_morphism_type)
  have eq1: "fibered_product_right_proj X f f X \<circ>\<^sub>c xx = id X"
    by (metis xx_assms comp_associative diagonal_def fibered_product_right_proj_def id_type right_cart_proj_cfunc_prod)

  have eq2: "xx \<circ>\<^sub>c fibered_product_right_proj X f f X = id (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
  proof (rule one_separator[where X="X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X", where Y="X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"])
    show "xx \<circ>\<^sub>c fibered_product_right_proj X f f X : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
      using assms(1) comp_type fibered_product_right_proj_type xx_assms by blast
    show "id\<^sub>c (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
      by (simp add: id_type)
  next
    fix x
    assume x_type: "x \<in>\<^sub>c X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
    then obtain a where a_assms: "\<langle>a,a\<rangle> = fibered_product_morphism X f f X \<circ>\<^sub>c x \<and> a \<in>\<^sub>c X"
      by (smt assms cfunc_prod_comp cfunc_prod_unique comp_type fibered_product_left_proj_def
          fibered_product_morphism_type fibered_product_right_proj_def fibered_product_right_proj_type)

    have "(xx \<circ>\<^sub>c fibered_product_right_proj X f f X) \<circ>\<^sub>c x = xx \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c \<langle>a,a\<rangle>"
      by (simp add: a_assms comp_associative fibered_product_right_proj_def)
    also have "... = xx \<circ>\<^sub>c a"
      by (metis a_assms right_cart_proj_cfunc_prod)
    also have "... = x"
    proof -
      have f1: "diagonal X \<in> ETCS_func"
        by (metis comp_associative compatible_comp_ETCS_func eq1 fibered_product_right_proj_def id_ETCS_func xx_assms)
      have f2: "\<forall>c. fibered_product_morphism X f f X \<circ>\<^sub>c xx \<circ>\<^sub>c c = diagonal X \<circ>\<^sub>c c"
        by (simp add: comp_associative xx_assms)
      have f3: "domain (fibered_product_morphism X f f X) = codomain xx"
        using f1 by (simp add: compatible_comp_ETCS_func xx_assms)
      have f4: "xx : X \<rightarrow> codomain xx"
        using cfunc_type_def xx_assms by presburger
      have f5: "diagonal X \<circ>\<^sub>c a = \<langle>a,a\<rangle>"
        using a_assms diag_on_elements by blast
      have f6: "codomain (xx \<circ>\<^sub>c a) = codomain xx"
        using f4 by (meson a_assms cfunc_type_def comp_type)
      have f7: "xx \<circ>\<^sub>c a \<in> ETCS_func"
        using f4 by (meson a_assms cfunc_type_def comp_type)
      then have f8: "\<langle>a,a\<rangle> \<in> ETCS_func"
        using f6 f5 f2 f1 by (metis (full_types) compatible_comp_ETCS_func xx_assms)
      then have f9: "x : domain x \<rightarrow> codomain xx"
        using f3 by (simp add: a_assms cfunc_type_def compatible_comp_ETCS_func)
      have f10: "\<forall>c ca. domain (ca \<circ>\<^sub>c a) = one \<or> \<not> ca : X \<rightarrow> c"
        by (meson a_assms cfunc_type_def comp_type)
      then have "domain \<langle>a,a\<rangle> = one"
        using f8 f5 by (metis (no_types) cfunc_type_def comp_associative compatible_comp_ETCS_func xx_assms)
      then have f11: "domain x = one"
        using f9 f1 a_assms cfunc_type_def comp_type compatible_comp_ETCS_func xx_assms by auto
      have "xx \<circ>\<^sub>c a \<in>\<^sub>c codomain xx"
        using f10 f7 f6 f4 cfunc_type_def by blast
      then show ?thesis
        using f11 f9 f5 f3 f2 by (metis (no_types) a_assms assms(1) fibered_product_morphism_monomorphism injective_def monomorphism_imp_injective)
    qed
    also have "... = id\<^sub>c (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c x"
      by (metis cfunc_type_def id_left_unit x_type)
    then show "(xx \<circ>\<^sub>c fibered_product_right_proj X f f X) \<circ>\<^sub>c x = id\<^sub>c (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c x"
      using calculation by auto
  qed
 
  show "isomorphism (fibered_product_right_proj X f f X)"
    unfolding isomorphism_def
    by (rule_tac x=xx in exI, metis codomain_comp domain_comp eq1 eq2 id_codomain id_domain)
qed

(* Exercise 2.1.44 Part 3 *)
lemma kern_pair_proj_iso_TFAE3:
  assumes "f: X \<rightarrow> Y"
  assumes "isomorphism (fibered_product_left_proj X f f X)" "isomorphism (fibered_product_right_proj X f f X)"
  shows "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
proof -
  obtain q0 where 
    q0_assms: "q0 : X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X 
      \<and> fibered_product_left_proj X f f X \<circ>\<^sub>c q0 = id X
      \<and> q0 \<circ>\<^sub>c fibered_product_left_proj X f f X = id (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using assms(2) unfolding isomorphism_def
    by (metis assms(1) cfunc_type_def compatible_comp_ETCS_func fibered_product_left_proj_type id_ETCS_func)

  obtain q1 where 
    q1_assms: "q1 : X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X 
      \<and> fibered_product_right_proj X f f X \<circ>\<^sub>c q1 = id X
      \<and> q1 \<circ>\<^sub>c fibered_product_right_proj X f f X = id (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using assms(3) unfolding isomorphism_def
    by (metis assms(1) cfunc_type_def compatible_comp_ETCS_func fibered_product_right_proj_type id_ETCS_func)

  have "\<And>x. x \<in>\<^sub>c domain f \<Longrightarrow> q0 \<circ>\<^sub>c x = q1 \<circ>\<^sub>c x"
  proof -
    fix x 
    have fxfx:  "f\<circ>\<^sub>c x = f\<circ>\<^sub>c x"
       by simp
    assume x_type: "x \<in>\<^sub>c domain f"
    have factorsthru: "\<langle>x,x\<rangle> factorsthru fibered_product_morphism X f f X"
      using assms(1) cfunc_type_def fxfx pair_factorsthru_fibered_product_morphism x_type  by auto
    then obtain xx where xx_assms: "xx : one \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and> \<langle>x,x\<rangle> = fibered_product_morphism X f f X \<circ>\<^sub>c xx"
      by (smt assms(1) cfunc_type_def diag_on_elements domain_comp factors_through_def fibered_product_morphism_type x_type)
    have projection_prop: "q0 \<circ>\<^sub>c ((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx) = 
                               q1 \<circ>\<^sub>c ((fibered_product_right_proj X f f X)\<circ>\<^sub>c xx)"
      by (simp add: comp_associative q0_assms q1_assms)
    then have fun_fact: "x = ((fibered_product_left_proj X f f X) \<circ>\<^sub>c q1)\<circ>\<^sub>c (((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx))"
      by (metis assms(1) cfunc_type_def comp_associative fibered_product_left_proj_def fibered_product_right_proj_def id_left_unit left_cart_proj_cfunc_prod q0_assms right_cart_proj_cfunc_prod x_type xx_assms)
    then have "q1  \<circ>\<^sub>c ((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx) = 
             q0  \<circ>\<^sub>c ((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx)"
      by (metis cfunc_type_def codomain_comp comp_associative fibered_product_left_proj_def fibered_product_right_proj_def id_codomain left_cart_proj_cfunc_prod projection_prop q0_assms right_cart_proj_cfunc_prod x_type xx_assms)
    then show "q0 \<circ>\<^sub>c x = q1 \<circ>\<^sub>c x"
      by (metis cfunc_type_def comp_associative fun_fact id_left_unit q0_assms xx_assms)
  qed
  then have "q0 = q1"
    by (metis assms(1) cfunc_type_def one_separator_contrapos q0_assms q1_assms)
  then show "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
    by (metis comp_associative domain_comp id_domain id_right_unit q0_assms q1_assms)
qed

section  \<open>Axiom 5: Truth-Value Object\<close>

axiomatization
  true_func :: "cfunc" ("\<t>") and
  false_func  :: "cfunc" ("\<f>") and
  truth_value_set :: "cset" ("\<Omega>")
where
  true_func_type: "\<t> \<in>\<^sub>c \<Omega>" and
  false_func_type: "\<f> \<in>\<^sub>c \<Omega>" and
  true_false_distinct: "\<t> \<noteq> \<f>" and
  true_false_only_truth_values: "\<forall> x. (x \<in>\<^sub>c \<Omega>) \<longrightarrow> (x = \<f> \<or> x = \<t>)" and
  characteristic_function_exists:
    "\<forall> X m. ((m : B \<rightarrow> X) \<and> monomorphism(m)) \<longrightarrow> (\<exists>! \<chi>. is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi> )"

thm subobject_of_def

(* Proposition 2.2.1: see under Axiom 8 *)

(* Proposition 2.2.2 *)
lemma "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
proof -
  have "{x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = {\<langle>\<t>,\<t>\<rangle>, \<langle>\<t>,\<f>\<rangle>, \<langle>\<f>,\<t>\<rangle>, \<langle>\<f>,\<f>\<rangle>}"
    apply (auto simp add: cfunc_prod_type true_func_type false_func_type)
    by (smt cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type true_false_only_truth_values)
  then show "card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4"
    using element_pair_eq false_func_type true_false_distinct true_func_type by auto
qed

(* Exercise 2.2.3 *)
lemma regmono_is_mono: "regular_monomorphism(m) \<Longrightarrow> monomorphism(m)"
  using equalizer_is_monomorphism regular_monomorphism_def by blast

(* Proposition 2.2.4 *)
lemma mono_is_regmono:
  assumes "m \<in> ETCS_func"
  shows "monomorphism(m) \<Longrightarrow> regular_monomorphism(m)"
  unfolding regular_monomorphism_def
proof - 
  assume m_mono: "monomorphism(m)"
  then obtain \<chi> where chi_pullback: "is_pullback (domain(m)) one  (codomain(m)) \<Omega> (\<beta>\<^bsub>domain(m)\<^esub>) \<t> m \<chi> "
    using assms cfunc_type_def characteristic_function_exists by blast

  have pullback: "\<And>k h Z. k : Z \<rightarrow> one \<and> h : Z \<rightarrow> codomain m \<and> \<t> \<circ>\<^sub>c k = \<chi> \<circ>\<^sub>c h \<longrightarrow>
     (\<exists>!j. j : Z \<rightarrow> domain m \<and> \<beta>\<^bsub>domain m\<^esub> \<circ>\<^sub>c j = k \<and> m \<circ>\<^sub>c j = h)"
    using chi_pullback unfolding is_pullback_def by auto

  have "equalizer (domain(m)) m (\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub>) \<chi>"
    unfolding equalizer_def
  proof (rule_tac x="codomain(m)" in exI, rule_tac x="\<Omega>" in exI, auto)
    show tbeta_type: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain(m)\<^esub> : codomain(m) \<rightarrow>  \<Omega>"
      using comp_type terminal_func_type true_func_type by blast
    show chi_type: "\<chi> : codomain(m) \<rightarrow>  \<Omega>"
      using chi_pullback is_pullback_def square_commutes_def by auto
    show m_type: "m : domain m \<rightarrow> codomain m"
      by (simp add: assms cfunc_type_def)

    have comm: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>domain m\<^esub> = \<chi> \<circ>\<^sub>c m"
      using chi_pullback unfolding is_pullback_def square_commutes_def by auto
    then have "\<beta>\<^bsub>domain m\<^esub> = \<beta>\<^bsub>codomain m\<^esub> \<circ>\<^sub>c m"
      by (metis (mono_tags, hide_lams) cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp terminal_func_type terminal_func_unique true_func_type)
    then show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>) \<circ>\<^sub>c m = \<chi> \<circ>\<^sub>c m"
      using comm comp_associative by auto
  next
    fix h F
    assume  "h : F \<rightarrow> codomain m" "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>codomain m\<^esub>) \<circ>\<^sub>c h = \<chi> \<circ>\<^sub>c h"
    then show "\<exists>k. k : F \<rightarrow> domain m \<and> m \<circ>\<^sub>c k = h"
      by (metis comp_associative comp_type pullback terminal_func_type)
  next
    fix F k y
    assume "k : F \<rightarrow> domain m" "y : F \<rightarrow> domain m"
    then show "m \<circ>\<^sub>c y = m \<circ>\<^sub>c k \<Longrightarrow> k = y"
      using m_mono unfolding monomorphism_def by (simp add: cfunc_type_def)
  qed
  then show "\<exists>g h. domain g = codomain m \<and> domain h = codomain m \<and> equalizer (domain m) m g h"
    by (metis cfunc_type_def equalizer_def)
qed

(*Proposition 2.2.5*)
lemma epi_mon_is_iso:
  assumes "f \<in> ETCS_func"
  assumes "epimorphism(f)" "monomorphism(f)"
  shows "isomorphism(f)"
  by (simp add: assms epi_regmon_is_iso mono_is_regmono)

(* Definition 2.2.6 *)
definition fiber :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1{_}" [100,100]100) where
  "f\<^sup>-\<^sup>1{y} = (f\<^sup>-\<^sup>1[one]\<^bsub>y\<^esub>)"

definition fiber_morphism :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "fiber_morphism f y = left_cart_proj (domain f) one \<circ>\<^sub>c inverse_image_mapping f one y"

lemma fiber_morphism_type:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "fiber_morphism f y : f\<^sup>-\<^sup>1{y} \<rightarrow> X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject subobject_of_def2
  by auto

lemma fiber_subset: 
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "(f\<^sup>-\<^sup>1{y}, fiber_morphism f y) \<subseteq>\<^sub>c X"
  unfolding fiber_def fiber_morphism_def
  using assms cfunc_type_def element_monomorphism inverse_image_subobject
  by auto

lemma fiber_morphism_monomorphism:
  assumes "f : X \<rightarrow> Y" "y \<in>\<^sub>c Y"
  shows "monomorphism (fiber_morphism f y)"
  using assms cfunc_type_def element_monomorphism fiber_morphism_def inverse_image_monomorphism by auto

(* Proposition 2.2.7 *)
lemma not_surjective_has_some_empty_preimage:
  assumes "p: X \<rightarrow> Y" "\<not>surjective(p)"
  shows "\<exists> y. (y\<in>\<^sub>c Y \<and>  \<not>nonempty(p\<^sup>-\<^sup>1{y}))"
proof -
  have nonempty: "nonempty(Y)"
    using assms(1) assms(2) cfunc_type_def nonempty_def surjective_def by auto
  obtain y0 where y0_type: "(y0\<in>\<^sub>c Y)\<and>(\<forall> x. (x\<in>\<^sub>c X \<longrightarrow> p\<circ>\<^sub>c x \<noteq> y0))"
    using assms(1) assms(2) cfunc_type_def surjective_def by auto
  (* then have "is_pullback (p\<^sup>-\<^sup>1{y0}) one X Y (\<beta>\<^bsub>p\<^sup>-\<^sup>1{y0}\<^esub>) (y0) m p" *)
  have "\<not>nonempty(p\<^sup>-\<^sup>1{y0})"
  proof (rule ccontr,auto)
    assume a1: "nonempty(p\<^sup>-\<^sup>1{y0})"
    obtain z where z_type: "z\<in>\<^sub>c p\<^sup>-\<^sup>1{y0}"
      using a1 nonempty_def by blast
    then have contradiction: "p \<circ>\<^sub>c (m \<circ>\<^sub>c z) = y0"
      oops

section  \<open>Axiom 6: Equivalence Classes\<close>

definition reflexive :: "cset \<times> cfunc \<Rightarrow> bool" where
  "reflexive R = (\<exists> X. R \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and> 
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<langle>x,x\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R)))"

definition symmetric :: "cset \<times> cfunc \<Rightarrow> bool" where
  "symmetric R = (\<exists> X. R  \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and>
    (\<forall>x y. x \<in>\<^sub>c X \<and>  y \<in>\<^sub>c X \<longrightarrow> 
      (\<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longrightarrow> \<langle>y,x\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R)))" 

definition transitive :: "cset \<times> cfunc \<Rightarrow> bool" where
  "transitive R = (\<exists> X. R  \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and>
    (\<forall>x y z. x \<in>\<^sub>c X \<and>  y \<in>\<^sub>c X \<and> z \<in>\<^sub>c X  \<longrightarrow>
      (\<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<and> \<langle>y,z\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longrightarrow> \<langle>x,z\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R)))"

definition reflexive_on :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" where
  "reflexive_on X R = (R \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and> 
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<langle>x,x\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R)))"

definition symmetric_on :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" where
  "symmetric_on X R = (R  \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and>
    (\<forall>x y. x \<in>\<^sub>c X \<and>  y \<in>\<^sub>c X \<longrightarrow> 
      (\<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longrightarrow> \<langle>y,x\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R)))" 

definition transitive_on :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" where
  "transitive_on X R = (R  \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and>
    (\<forall>x y z. x \<in>\<^sub>c X \<and>  y \<in>\<^sub>c X \<and> z \<in>\<^sub>c X  \<longrightarrow>
      (\<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<and> \<langle>y,z\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longrightarrow> \<langle>x,z\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R)))"

definition equiv_rel :: "cset \<times> cfunc \<Rightarrow> bool" where
  "equiv_rel R  \<longleftrightarrow> (reflexive R \<and> symmetric R \<and> transitive R)"

definition equiv_rel_on :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" where
  "equiv_rel_on X R  \<longleftrightarrow> (reflexive_on X R \<and> symmetric_on X R \<and> transitive_on X R)"

axiomatization 
  quotient_set :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> cset" and
  equiv_class :: "cset \<times> cfunc \<Rightarrow> cfunc" and
  quotient_func :: "cfunc \<Rightarrow> cset \<times> cfunc \<Rightarrow> cfunc"
where
  equiv_class_type: "equiv_rel_on X R \<Longrightarrow> equiv_class R : X \<rightarrow> quotient_set X R" and
  equiv_class_eq: "equiv_rel_on X R \<Longrightarrow> \<langle>x, y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longleftrightarrow> q \<circ>\<^sub>c x = q \<circ>\<^sub>c y" and
  quotient_func_type: "equiv_rel_on X R \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> \<langle>x, y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longleftrightarrow> q \<circ>\<^sub>c x = q \<circ>\<^sub>c y \<Longrightarrow>
    quotient_func f R : quotient_set X R \<rightarrow> Y" and 
  quotient_func_eq: "equiv_rel_on X R \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> \<langle>x, y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longleftrightarrow> q \<circ>\<^sub>c x = q \<circ>\<^sub>c y \<Longrightarrow>
    equiv_class R \<circ>\<^sub>c quotient_func f R = f" and  
  quotient_func_unique: "equiv_rel_on X R \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> \<langle>x, y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longleftrightarrow> q \<circ>\<^sub>c x = q \<circ>\<^sub>c y \<Longrightarrow>
    h : quotient_set X R \<rightarrow> Y \<Longrightarrow> equiv_class R \<circ>\<^sub>c quotient_func h R = f \<Longrightarrow> 
      h = quotient_func f R"


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


section  \<open>Axiom 8: Empty Set\<close>

axiomatization
  initial_func :: "cset \<Rightarrow> cfunc" ("\<alpha>\<^bsub>_\<^esub>" 100) and
  emptyset :: "cset" ("\<emptyset>")
where
  initial_func_type: "initial_func(X) :  \<emptyset> \<rightarrow> X" and
  initial_func_unique: "((\<forall> h. h : \<emptyset> \<rightarrow> X) \<longrightarrow> (h = initial_func(X)))" and
  emptyset_is_empty: "\<not>(x \<in>\<^sub>c \<emptyset>)"

(*characteristic_function_exists:
    "\<forall> X m. ((m : B \<rightarrow> X) \<and> monomorphism(m)) \<longrightarrow> (\<exists>! \<chi>. is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi> )"*)


(* Exercise 2.4.6 *)
(* This lemma is a pre-requiste to the real version of the theorem. *)
lemma coproduct_with_zero_does_nothing:
  shows "X \<Coprod> \<emptyset> \<cong> X"
proof -
  have i0_type: "(left_coproj X \<emptyset>) : X \<rightarrow> X\<Coprod>\<emptyset>"
    by (simp add: left_proj_type)
  have i1_type: "(right_coproj X \<emptyset>) : \<emptyset> \<rightarrow> X\<Coprod>\<emptyset>"
    by (simp add: right_proj_type)  
  have i0Ui1_type:"(left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>):  X\<Coprod>\<emptyset> \<rightarrow> X\<Coprod>\<emptyset>"
    by (simp add: cfunc_coprod_type i0_type i1_type)
  have idX_U_alpha_X_type: "(id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) : X\<Coprod>\<emptyset> \<rightarrow> X"
    by (simp add: cfunc_coprod_type id_type initial_func_type)
  then have "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = 
          (left_coproj X \<emptyset>) \<circ>\<^sub>c ((id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c (left_coproj X \<emptyset>))"
    by (simp add: comp_associative) 
  also have "... = (left_coproj X \<emptyset>) \<circ>\<^sub>c id(X)"
    by (metis id_type initial_func_type left_coproj_cfunc_coprod)
  also have "... = left_coproj X \<emptyset>"
    by (metis cfunc_type_def i0_type id_right_unit)
  then have comp1: "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = left_coproj X \<emptyset>"
    by (simp add: calculation)
  have "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = 
             (left_coproj X \<emptyset>) \<circ>\<^sub>c ((id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c (right_coproj X \<emptyset>))"
    by (simp add: comp_associative)
  have "... = (left_coproj X \<emptyset>) \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>"
    by (metis id_type initial_func_type right_coproj_cfunc_coprod)
  have "... = right_coproj X \<emptyset>"
    by (meson comp_type emptyset_is_empty initial_func_type left_proj_type one_separator right_proj_type)
  then have comp2: "((left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) =right_coproj X \<emptyset>"
    by (simp add: \<open>(left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>\<close>)
  then have fact1: "((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>)) \<circ>\<^sub>c (left_coproj X \<emptyset>) = (left_coproj X \<emptyset>)"
    using i0_type i1_type left_coproj_cfunc_coprod by blast
  then have fact2: "((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>)) \<circ>\<^sub>c (right_coproj X \<emptyset>) = (right_coproj X \<emptyset>)"
    using i0_type i1_type right_coproj_cfunc_coprod by blast
  then have concl: "(left_coproj X \<emptyset>) \<circ>\<^sub>c (id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>) = ((left_coproj X \<emptyset>)\<amalg>(right_coproj X \<emptyset>))"
    using \<open>(left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub>) \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub> = right_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X = left_coproj X \<emptyset>\<close> \<open>left_coproj X \<emptyset> \<circ>\<^sub>c id\<^sub>c X \<amalg> \<alpha>\<^bsub>X\<^esub> \<circ>\<^sub>c right_coproj X \<emptyset> = left_coproj X \<emptyset> \<circ>\<^sub>c \<alpha>\<^bsub>X\<^esub>\<close> calculation cfunc_coprod_unique i0_type i1_type idX_U_alpha_X_type by auto
  also have "... = id(X\<Coprod>\<emptyset>)"
    by (metis cfunc_coprod_unique cfunc_type_def i0_type i1_type id_left_unit id_type)
  then have "isomorphism(id(X) \<amalg> \<alpha>\<^bsub>X\<^esub>)"
    using cfunc_type_def concl i0_type idX_U_alpha_X_type id_type initial_func_type isomorphism_def left_coproj_cfunc_coprod by auto
  then show "X\<Coprod>\<emptyset> \<cong> X"
    using idX_U_alpha_X_type is_isomorphic_def by blast
qed

(* Proposition 2.4.7 *)
lemma function_to_empty_is_iso:
  assumes "codomain(f) = \<emptyset>" "f \<in> ETCS_func"
  shows "isomorphism(f)"
proof -
  have "surjective(f)"
    by (simp add: assms emptyset_is_empty surjective_def)
  have "epimorphism(f)"
    by (simp add: \<open>surjective f\<close> surjective_is_epimorphism) 
 
  have dom_f_is_empty: "\<not>nonempty(domain(f))"
  proof (rule ccontr, auto)
    assume BWOC:  "nonempty(domain(f))"
    obtain x where x_type: "x \<in>\<^sub>c domain(f)"
    using BWOC nonempty_def by blast
    have contradiction: "f \<circ>\<^sub>c x \<in>\<^sub>c \<emptyset>"
       using assms(1) assms(2) cfunc_type_def comp_type x_type by blast
     show False
       using contradiction emptyset_is_empty by auto
   qed
   have f_inj: "injective(f)"
     using dom_f_is_empty injective_def nonempty_def by blast
   have f_mono: "monomorphism(f)"
     by (simp add: assms(2) f_inj injective_imp_monomorphism)
   show "isomorphism(f)"    (*Modify this proof after you've shown that mono + epi = iso*)
      proof -
          have f1: "f : domain f \<rightarrow> \<emptyset>"
              using assms(1) assms(2) cfunc_type_def by blast
              have f2: "\<forall>c. domain (\<alpha>\<^bsub>c\<^esub>) = \<emptyset>"
              using cfunc_type_def initial_func_type by presburger
              have f3: "f \<circ>\<^sub>c \<alpha>\<^bsub>domain f\<^esub> = id\<^sub>c \<emptyset>"
              using f1 by (meson comp_type emptyset_is_empty id_type initial_func_type one_separator)
              have "\<alpha>\<^bsub>domain f\<^esub> \<circ>\<^sub>c f = id\<^sub>c (domain f)"
              using f1 by (meson comp_type emptyset_is_empty id_type initial_func_type one_separator)
              then show ?thesis
              using f3 f2 assms(1) cfunc_type_def initial_func_type isomorphism_def by auto
      qed
qed

lemma zero_times_X:
  "\<emptyset> \<times>\<^sub>c X \<cong> \<emptyset>"
  using cfunc_type_def function_to_empty_is_iso is_isomorphic_def left_cart_proj_type by blast

lemma X_times_zero: 
  "X \<times>\<^sub>c \<emptyset> \<cong> \<emptyset>"
  using cfunc_type_def function_to_empty_is_iso is_isomorphic_def right_cart_proj_type by blast

(* Proposition  2.4.8 *)
lemma no_el_iff_iso_0:
  "\<not>(nonempty(X)) \<longleftrightarrow> X \<cong> \<emptyset>"
proof auto
  assume "X \<cong> \<emptyset>"
  then show "nonempty X \<Longrightarrow> False "
    using comp_type emptyset_is_empty is_isomorphic_def nonempty_def by blast
  have "\<not>(nonempty(X))"
    using \<open>nonempty X \<Longrightarrow> False\<close> by blast
next 
  assume "\<not>(nonempty(X))"
  obtain f where f_type: "f: \<emptyset> \<rightarrow> X"
    using initial_func_type by blast  (* f = \<alpha>_X *)
 
  have  f_inj: "injective(f)"
    using cfunc_type_def emptyset_is_empty f_type injective_def by auto
  then have f_mono: "monomorphism(f)"
    using  cfunc_type_def f_type injective_imp_monomorphism by blast
  have f_surj: "surjective(f)"
    using \<open>\<not> nonempty X\<close> cfunc_type_def f_type nonempty_def surjective_def by auto
  then have epi_f: "epimorphism(f)"
    using surjective_is_epimorphism by blast
  then have iso_f: "isomorphism(f)"
    using cfunc_type_def epi_mon_is_iso f_mono f_type by blast
  then show "X \<cong> \<emptyset>"
    using f_type is_isomorphic_def isomorphic_is_symmetric by blast
qed

lemma empty_subset: "(\<emptyset>, \<alpha>\<^bsub>X\<^esub>) \<subseteq>\<^sub>c X"
  by (metis cfunc_type_def emptyset_is_empty initial_func_type injective_def
      injective_imp_monomorphism subobject_of_def2)

(* Proposition 2.2.1 *)
lemma "card ({(X,m). (X,m) \<subseteq>\<^sub>c one}//{((X,m1),(Y,m2)). X \<cong> Y}) = 2"
proof -
  have one_subobject: "(one, id one) \<subseteq>\<^sub>c one"
    using element_monomorphism id_type subobject_of_def2 by blast
  have empty_subobject: "(\<emptyset>, \<alpha>\<^bsub>one\<^esub>) \<subseteq>\<^sub>c one"
    by (simp add: empty_subset)

  have subobject_one_or_empty: "\<And>X m. (X,m) \<subseteq>\<^sub>c one \<Longrightarrow> X \<cong> one \<or> X \<cong> \<emptyset>"
  proof -
    fix X m
    assume X_m_subobject: "(X, m) \<subseteq>\<^sub>c one"

    obtain \<chi> where \<chi>_pullback: "is_pullback X one one \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> m \<chi>"
      using X_m_subobject characteristic_function_exists subobject_of_def2 by blast
    then have \<chi>_true_or_false: "\<chi> = \<t> \<or> \<chi> = \<f>"
      using is_pullback_def square_commutes_def true_false_only_truth_values by auto

    have true_iso_one: "\<chi> = \<t> \<Longrightarrow> X \<cong> one"
    proof -
      assume \<chi>_true: "\<chi> = \<t>"
      then have "\<exists>! x. x \<in>\<^sub>c X"
        using \<chi>_pullback unfolding is_pullback_def apply clarsimp
        apply (erule_tac x=one in allE, erule_tac x="id one" in allE, erule_tac x="id one" in allE)
        by (metis comp_type id_type square_commutes_def terminal_func_unique)
      then show "X \<cong> one"
        using single_elem_iso_one by auto
    qed

    have false_iso_one: "\<chi> = \<f> \<Longrightarrow> X \<cong> \<emptyset>"
    proof -
      assume \<chi>_false: "\<chi> = \<f>"
      have "\<nexists> x. x \<in>\<^sub>c X"
      proof auto
        fix x
        assume x_in_X: "x \<in>\<^sub>c X"
        have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> = \<f> \<circ>\<^sub>c m"
          using \<chi>_false \<chi>_pullback is_pullback_def square_commutes_def by auto
        then have "\<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c x) = \<f> \<circ>\<^sub>c (m \<circ>\<^sub>c x)"
          by (simp add: comp_associative)
        then have "\<t> = \<f>"
          by (smt X_m_subobject cfunc_type_def comp_type false_func_type id_right_unit id_type
              subobject_of_def2 terminal_func_unique true_func_type x_in_X)
        then show False
          using true_false_distinct by auto
      qed
      then show "X \<cong> \<emptyset>"
        using no_el_iff_iso_0 nonempty_def by blast
    qed

    show "X \<cong> one \<or> X \<cong> \<emptyset>"
      using \<chi>_true_or_false false_iso_one true_iso_one by blast
  qed

  have classes_distinct: "{(X, m). X \<cong> \<emptyset>} \<noteq> {(X, m). X \<cong> one}"
    by (metis case_prod_eta curry_case_prod emptyset_is_empty id_isomorphism id_type is_isomorphic_def mem_Collect_eq)

  have "{(X, m). (X, m) \<subseteq>\<^sub>c one} // {((X, m1), Y, m2). X \<cong> Y} = {{(X, m). X \<cong> \<emptyset>}, {(X, m). X \<cong> one}}"
    unfolding quotient_def apply auto
    using isomorphic_is_symmetric isomorphic_is_transitive subobject_one_or_empty apply blast+
    using empty_subobject apply (rule_tac x=\<emptyset> in exI, auto simp add: isomorphic_is_symmetric)
    using one_subobject apply (rule_tac x=one in exI, auto simp add: isomorphic_is_symmetric)
    done
  then show "card ({(X, m). (X, m) \<subseteq>\<^sub>c one} // {((X, m1), Y, m2). X \<cong> Y}) = 2"
    by (simp add: classes_distinct)
qed

section \<open>Axiom 9: Exponential Objects\<close>

axiomatization
  exp_set :: "cset \<Rightarrow> cset \<Rightarrow> cset" ("_\<^bsup>_\<^esup>" [100,100]100) and
  eval_func  :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  transpose_func :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>\<sharp>" [100]100)
where
  exp_set_inj: "X\<^bsup>A\<^esup> = Y\<^bsup>B\<^esup> \<Longrightarrow> X = Y \<and> A = B" and
  eval_func_type:  "eval_func X A : A\<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X" and
  transpose_func_def: "f : A \<times>\<^sub>c Z \<rightarrow> X \<longrightarrow> (f\<^sup>\<sharp> : Z \<rightarrow> X\<^bsup>A\<^esup> \<and> (eval_func X A) \<circ>\<^sub>c (id A)\<times>\<^sub>f(f\<^sup>\<sharp>) = f)" and
  transpose_func_unique: "(g: Z \<rightarrow> X\<^bsup>A\<^esup> \<and> ((eval_func X A) \<circ>\<^sub>c (id A)\<times>\<^sub>fg = f) \<and> f : A\<times>\<^sub>cZ \<rightarrow> X) \<longrightarrow> g = f\<^sup>\<sharp>"

(* Definition 2.5.1 *)
definition exp_func :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc" ("(_)\<^bsup>_\<^esup>\<^sub>f" [100,100]100) where
  "exp_func g A = (g \<circ>\<^sub>c eval_func (domain g) A)\<^sup>\<sharp>"
lemma exp_func_type:
  assumes "g : X \<rightarrow> Y"
  shows "g\<^bsup>A\<^esup>\<^sub>f : X\<^bsup>A\<^esup> \<rightarrow> Y\<^bsup>A\<^esup>"
  using assms cfunc_type_def comp_type eval_func_type exp_func_def transpose_func_def by auto

(* Note above Definition 2.5.1 *)
lemma exponential_object_identity:
  "(eval_func X A)\<^sup>\<sharp> = id\<^sub>c(X\<^bsup>A\<^esup>)"
  by (metis cfunc_type_def eval_func_type id_cross_prod id_right_unit id_type transpose_func_unique)

(* Note below Definition 2.5.1 *)
lemma exponential_square_diagram:
  assumes "g : Y \<rightarrow> Z"
  shows "square_commutes (A \<times>\<^sub>c Y\<^bsup>A\<^esup>) Y (A \<times>\<^sub>c Z\<^bsup>A\<^esup>) Z (eval_func Y A)  g (id\<^sub>c(A)\<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) (eval_func Z A)"
  using assms cfunc_cross_prod_type cfunc_type_def comp_type eval_func_type exp_func_def id_type square_commutes_def transpose_func_def by auto

(* Proposition 2.5.2 *)
lemma transpose_of_comp:
  "f: A \<times>\<^sub>c X \<rightarrow> Y \<and> g: Y \<rightarrow> Z  \<Longrightarrow>  (g \<circ>\<^sub>c f)\<^sup>\<sharp> = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>"
proof auto
  assume f_type: "f : A \<times>\<^sub>c X \<rightarrow> Y"
  assume g_type: "g : Y \<rightarrow> Z"
  have "square_commutes (A \<times>\<^sub>c Y\<^bsup>A\<^esup>) Y (A \<times>\<^sub>c Z\<^bsup>A\<^esup>) Z (eval_func Y A)  g (id(A)\<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) (eval_func Z A)"
    using exponential_square_diagram g_type by blast
  have "triangle_commutes (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y\<^bsup>A\<^esup>) Y (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) (eval_func Y A) f"
    using cfunc_cross_prod_type eval_func_type f_type id_type transpose_func_def triangle_commutes_def by auto
  have "(eval_func Z A) \<circ>\<^sub>c(id(A) \<times>\<^sub>f (g \<circ>\<^sub>c f)\<^sup>\<sharp>) = (g \<circ>\<^sub>c f)"
    using comp_type f_type g_type transpose_func_def by blast
  have "g\<^bsup>A\<^esup>\<^sub>f : Y\<^bsup>A\<^esup> \<rightarrow> Z\<^bsup>A\<^esup>"
    by (simp add: exp_func_type g_type)
  have "f\<^sup>\<sharp> : X \<rightarrow> Y\<^bsup>A\<^esup>"
    by (simp add: f_type transpose_func_def)
  have "(id(A) \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>) = id(A) \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>)"
    using \<open>f\<^sup>\<sharp> : X \<rightarrow> Y\<^bsup>A\<^esup>\<close> \<open>g\<^bsup>A\<^esup>\<^sub>f : Y\<^bsup>A\<^esup> \<rightarrow> Z\<^bsup>A\<^esup>\<close> identity_distributes_across_composition by auto (*by Prop 2.1.11 plus previous two lines *)
  have "(eval_func Z A) \<circ>\<^sub>c ((id(A) \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (id(A) \<times>\<^sub>f f\<^sup>\<sharp>)) = (eval_func Z A) \<circ>\<^sub>c  (id(A) \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>))"
    by (simp add: \<open>id\<^sub>c A \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f\<^sup>\<sharp> = id\<^sub>c A \<times>\<^sub>f (g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>)\<close>)
  also have "... = g  \<circ>\<^sub>c f"
    by (metis \<open>square_commutes (A \<times>\<^sub>c Y\<^bsup>A\<^esup>) Y (A \<times>\<^sub>c Z\<^bsup>A\<^esup>) Z (eval_func Y A) g (id\<^sub>c A \<times>\<^sub>f g\<^bsup>A\<^esup>\<^sub>f) (eval_func Z A)\<close> calculation comp_associative f_type square_commutes_def transpose_func_def)
  then show "(g \<circ>\<^sub>c f)\<^sup>\<sharp> = g\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c f\<^sup>\<sharp>"
    using \<open>f\<^sup>\<sharp> : X \<rightarrow> Y\<^bsup>A\<^esup>\<close> \<open>g\<^bsup>A\<^esup>\<^sub>f : Y\<^bsup>A\<^esup> \<rightarrow> Z\<^bsup>A\<^esup>\<close> comp_type f_type g_type transpose_func_unique by fastforce
qed

(*Comments below Proposition 2.5.2 and above Definition 2.5.3*)
lemma eval_of_id_cross_id_sharp1:
  "(eval_func (A \<times>\<^sub>c X) A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (id(A \<times>\<^sub>c X))\<^sup>\<sharp>)  = id(A \<times>\<^sub>c X)"
  using id_type transpose_func_def by blast
lemma eval_of_id_cross_id_sharp2:
  assumes "a : Z \<rightarrow> A" "x : Z \<rightarrow> X"
  shows "((eval_func (A \<times>\<^sub>c X) A) \<circ>\<^sub>c (id(A) \<times>\<^sub>f (id(A \<times>\<^sub>c X))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>a,x\<rangle> = \<langle>a,x\<rangle>"
  by (metis assms cfunc_type_def compatible_comp_ETCS_func eval_of_id_cross_id_sharp1 id_left_unit
      left_cart_proj_cfunc_prod left_cart_proj_type)

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

lemma flat_type:
  assumes f_type: "f : Z \<rightarrow> X\<^bsup>A\<^esup>"
  shows "f\<^sup>\<flat> : A \<times>\<^sub>c Z \<rightarrow> X"
proof (subst inv_transpose_func_def2[where Z=Z, where X=X, where A=A], simp add: assms)
  have cross_type: "id\<^sub>c A \<times>\<^sub>f f : A \<times>\<^sub>c Z \<rightarrow> A \<times>\<^sub>c X\<^bsup>A\<^esup>"
    by (simp add: cfunc_cross_prod_type f_type id_type)
  have "eval_func X A : A \<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X"
    by (simp add: eval_func_type)
  then show "eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f f : A \<times>\<^sub>c Z \<rightarrow> X"
    using cross_type by auto
qed

(* Proposition 2.5.4 *)
lemma inv_transpose_of_composition:
  shows "f: X \<rightarrow> Y \<and> g: Y \<rightarrow> Z\<^bsup>A\<^esup> \<Longrightarrow> (g \<circ>\<^sub>c f)\<^sup>\<flat> = g\<^sup>\<flat> \<circ>\<^sub>c (id(A) \<times>\<^sub>f f)"
  by (smt comp_associative comp_type identity_distributes_across_composition inv_transpose_func_def2)

(* Proposition 2.5.5 *)
lemma flat_cancels_sharp:
  "f : A \<times>\<^sub>c Z \<rightarrow> X  \<Longrightarrow> (f\<^sup>\<sharp>)\<^sup>\<flat> = f"
  by (metis inv_transpose_func_def2 transpose_func_def)

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
    assume "a \<in>\<^sub>c domain (eval_func X one)"
    assume "b \<in>\<^sub>c domain (eval_func X one)"
    assume "eval_func X one \<circ>\<^sub>c a = eval_func X one \<circ>\<^sub>c b"

    have "a = (eval_func X one \<circ>\<^sub>c a)\<^sup>\<sharp>"
    

  thm transpose_func_unique[where f="eval_func X one \<circ>\<^sub>c a", where A=one, where X=X, where Z=one, where g=a]
    oops




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
  have inj: "injective(e)"
  unfolding injective_def
  proof auto
    fix x y 
    assume a1: "x \<in>\<^sub>c domain e"
    assume a2: "y \<in>\<^sub>c domain e"
    assume a3: "e \<circ>\<^sub>c x = e \<circ>\<^sub>c y"

    have "\<langle>id(one),((right_cart_proj one  (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c x)\<rangle> : one \<rightarrow> domain e"
      using a1 cfunc_prod_type cfunc_type_def comp_type e_defn eval_func_type id_type right_cart_proj_type by auto
    then have x_eq: "x = \<langle>id(one),(right_cart_proj one  (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c x\<rangle>"
      using a1 cfunc_prod_unique[where f="id(one)", where g="(right_cart_proj one  (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c x"]
      using cfunc_type_def comp_type e_defn eval_func_type id_type left_cart_proj_type one_unique_element right_cart_proj_type by force

    have "\<langle>id(one),((right_cart_proj one  (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c y)\<rangle> : one \<rightarrow> domain e"
      using a2 cfunc_prod_type cfunc_type_def comp_type e_defn eval_func_type id_type right_cart_proj_type by auto
    then have y_eq: "y = \<langle>id(one),(right_cart_proj one  (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c y\<rangle>"
      using a2 cfunc_prod_unique[where f="id(one)", where g="(right_cart_proj one  (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c y"]
      using cfunc_type_def comp_type e_defn eval_func_type id_type left_cart_proj_type one_unique_element right_cart_proj_type by force

    have "e \<circ>\<^sub>c (id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)) = (e\<circ>\<^sub>c x) \<circ>\<^sub>c i"
    proof -
      have "e \<circ>\<^sub>c (id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)) = 
            e \<circ>\<^sub>c ((id(one) \<circ>\<^sub>c id(one)) \<times>\<^sub>f (((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x) \<circ>\<^sub>c id(one)))"
        by (metis a1 cfunc_type_def domain_comp id_right_unit)
      also have "... = e\<circ>\<^sub>c ((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)) \<circ>\<^sub>c (id(one)\<times>\<^sub>f id(one)))"
        by (smt a1 cfunc_type_def domain_comp e_defn eval_func_type id_cross_prod id_right_unit id_type identity_distributes_across_composition right_cart_proj_type)
      also have "... = e\<circ>\<^sub>c ((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)) \<circ>\<^sub>c (diagonal(one)\<circ>\<^sub>c i))"
        by (metis cfunc_prod_unique comp_type diagonal_def i_iso i_type id_cross_prod left_cart_proj_type right_cart_proj_type terminal_func_unique)
      also have "... = e\<circ>\<^sub>c (((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)) \<circ>\<^sub>c diagonal(one))\<circ>\<^sub>c i)"
        by (simp add: comp_associative)
      also have "... = e\<circ>\<^sub>c (((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)) \<circ>\<^sub>c \<langle>id(one),id(one)\<rangle>)\<circ>\<^sub>c i)"
        by (simp add: diagonal_def)
      also have "... = e\<circ>\<^sub>c (\<langle>id(one) \<circ>\<^sub>c id(one),((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)\<circ>\<^sub>c id(one)\<rangle>\<circ>\<^sub>c i)"
        using a1 cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_type e_defn eval_func_type id_type right_cart_proj_type by auto
      also have "... = e\<circ>\<^sub>c (\<langle>id(one),((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c x)\<rangle>\<circ>\<^sub>c i)"
        by (metis a1 cfunc_type_def domain_comp id_right_unit)
      also have "... = (e\<circ>\<^sub>c x) \<circ>\<^sub>c i"
        using comp_associative x_eq by auto
      then show ?thesis
        using calculation by auto
    qed
    then have x_property: "right_cart_proj one (X\<^bsup>one\<^esup>) \<circ>\<^sub>c x = ((e \<circ>\<^sub>c x) \<circ>\<^sub>c i)\<^sup>\<sharp>"
    proof -
      have 1: "right_cart_proj one (X\<^bsup>one\<^esup>) \<circ>\<^sub>c x \<in>\<^sub>c X\<^bsup>one\<^esup>"
        using a1 cfunc_type_def comp_type e_defn eval_func_type right_cart_proj_type by auto
      have 2: "(e \<circ>\<^sub>c y) \<circ>\<^sub>c i : one \<times>\<^sub>c one \<rightarrow> X"
        by (metis (mono_tags, hide_lams) a1 a3 cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp e_defn eval_func_type i_type)
      assume "e \<circ>\<^sub>c id\<^sub>c one \<times>\<^sub>f (right_cart_proj one (X\<^bsup>one\<^esup>) \<circ>\<^sub>c x) = (e \<circ>\<^sub>c x) \<circ>\<^sub>c i"
      then show ?thesis
        using "1" "2" a3 e_defn transpose_func_unique by auto
    qed

    have "e \<circ>\<^sub>c (id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)) = (e\<circ>\<^sub>c y) \<circ>\<^sub>c i"
    proof -
      have "e \<circ>\<^sub>c (id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)) = 
            e \<circ>\<^sub>c ((id(one) \<circ>\<^sub>c id(one)) \<times>\<^sub>f (((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y) \<circ>\<^sub>c id(one)))"
        by (metis a2 cfunc_type_def domain_comp id_right_unit)
      also have "... = e\<circ>\<^sub>c ((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)) \<circ>\<^sub>c (id(one)\<times>\<^sub>f id(one)))"
        by (smt a2 cfunc_type_def domain_comp e_defn eval_func_type id_cross_prod id_right_unit id_type identity_distributes_across_composition right_cart_proj_type)
      also have "... = e\<circ>\<^sub>c ((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)) \<circ>\<^sub>c (diagonal(one)\<circ>\<^sub>c i))"
        by (metis cfunc_prod_unique comp_type diagonal_def i_iso i_type id_cross_prod left_cart_proj_type right_cart_proj_type terminal_func_unique)
      also have "... = e\<circ>\<^sub>c (((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)) \<circ>\<^sub>c diagonal(one))\<circ>\<^sub>c i)"
        by (simp add: comp_associative)
      also have "... = e\<circ>\<^sub>c (((id(one) \<times>\<^sub>f ((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)) \<circ>\<^sub>c \<langle>id(one),id(one)\<rangle>)\<circ>\<^sub>c i)"
        by (simp add: diagonal_def)
      also have "... = e\<circ>\<^sub>c (\<langle>id(one) \<circ>\<^sub>c id(one),((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)\<circ>\<^sub>c id(one)\<rangle>\<circ>\<^sub>c i)"
        using a2 cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_type e_defn eval_func_type id_type right_cart_proj_type by auto
      also have "... = e\<circ>\<^sub>c (\<langle>id(one),((right_cart_proj one  (X\<^bsup>one\<^esup>))\<circ>\<^sub>c y)\<rangle>\<circ>\<^sub>c i)"
        by (metis a2 cfunc_type_def domain_comp id_right_unit)
      also have "... = (e\<circ>\<^sub>c y) \<circ>\<^sub>c i"
        using comp_associative y_eq by auto
      then show ?thesis
        using calculation by auto
    qed
    then have y_property: "right_cart_proj one (X\<^bsup>one\<^esup>) \<circ>\<^sub>c y = ((e \<circ>\<^sub>c y) \<circ>\<^sub>c i)\<^sup>\<sharp>"
    proof -
      have 1: "right_cart_proj one (X\<^bsup>one\<^esup>) \<circ>\<^sub>c y \<in>\<^sub>c X\<^bsup>one\<^esup>"
        using a2 cfunc_type_def comp_type e_defn eval_func_type right_cart_proj_type by auto
      have 2: "(e \<circ>\<^sub>c y) \<circ>\<^sub>c i : one \<times>\<^sub>c one \<rightarrow> X"
        by (metis (mono_tags, hide_lams) a2 a3 cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp e_defn eval_func_type i_type)
      assume "e \<circ>\<^sub>c id\<^sub>c one \<times>\<^sub>f (right_cart_proj one (X\<^bsup>one\<^esup>) \<circ>\<^sub>c y) = (e \<circ>\<^sub>c y) \<circ>\<^sub>c i"
      then show ?thesis
        using "1" "2" a3 e_defn transpose_func_unique x_property by auto
    qed

    have "(right_cart_proj one (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c x = (right_cart_proj one (X\<^bsup>one\<^esup>)) \<circ>\<^sub>c y"
      by (simp add: a3 x_property y_property)
    then show "x = y"
      using x_eq y_eq by auto
  qed

  have surj: "surjective(e)"
     unfolding surjective_def
   proof auto
    fix y 
    assume assumption1: "y \<in>\<^sub>c codomain e"
    then have square: "e \<circ>\<^sub>c (id(one) \<times>\<^sub>f (y\<circ>\<^sub>c i)\<^sup>\<sharp>) = y\<circ>\<^sub>c i"
      using cfunc_type_def comp_type e_defn e_type i_type transpose_func_def by auto 
    then show "\<exists>x. x \<in>\<^sub>c domain e \<and> e \<circ>\<^sub>c x = y" 
      using e_type unfolding cfunc_type_def
      apply (rule_tac x="(id(one) \<times>\<^sub>f (y\<circ>\<^sub>c i)\<^sup>\<sharp>)\<circ>\<^sub>c i_inv" in exI, auto)
      apply (metis domain_comp i_iso id_domain)
      apply (metis assumption1 cfunc_type_def codomain_comp compatible_comp_ETCS_func i_type)
      apply (metis assumption1 cfunc_type_def compatible_comp_ETCS_func domain_comp i_iso i_type)
      by (metis assumption1 cfunc_type_def comp_associative i_iso id_right_unit)
  qed

  have "isomorphism e"
    using cfunc_type_def e_type epi_mon_is_iso inj injective_imp_monomorphism surj surjective_is_epimorphism by auto
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
    using comp_type f_type initial_func_type left_cart_proj_type transpose_func_def by blast
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
      using cfunc_type_def compatible_comp_ETCS_func id_ETCS_func isomorphism_def j_iso by fastforce
    then have \<psi>_type_uniqe: "\<forall>g. (g: \<emptyset> \<times>\<^sub>c one \<rightarrow> \<emptyset>) \<longrightarrow> g=\<psi>"
      using comp_type emptyset_is_empty one_separator by blast
    have "\<emptyset>\<cong> \<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
      by (simp add: isomorphic_is_symmetric zero_times_X)
    then obtain \<phi> where phi_iso: "\<phi>:\<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup> \<rightarrow> \<emptyset> \<and> isomorphism(\<phi>)"
      using is_isomorphic_def zero_times_X by blast
    then have Id0xz_type: "(id(\<emptyset>)\<times>\<^sub>f z):\<emptyset> \<times>\<^sub>c one \<rightarrow> \<emptyset> \<times>\<^sub>c X\<^bsup>\<emptyset>\<^esup>"
      by (simp add: cfunc_cross_prod_type id_type z_type)
    then have phiId0xz_typ: "\<phi> \<circ>\<^sub>c (id(\<emptyset>)\<times>\<^sub>f z):\<emptyset> \<times>\<^sub>c one  \<rightarrow>  \<emptyset>"
      using phi_iso by auto
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
    using nonempty_def terminal_func_type transpose_func_def by blast
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
        using transpose_func_def by blast
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
          by (smt assms comp_type flat_type h_type inv_transpose_func_def2 proj_type transpose_func_def)
        have   "g = ((right_cart_proj X Y)\<^bsup>A\<^esup>\<^sub>f) \<circ>\<^sub>c (h\<^sup>\<flat>)\<^sup>\<sharp>"
          by (metis assms h_property2 h_type sharp_cancels_flat)
        have "... = ((right_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
           by (metis assms flat_type h_type proj2_type transpose_of_comp)
        have computation2: "g = ((right_cart_proj X Y) \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>"
           by (simp add: \<open>g = right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp>\<close> \<open>right_cart_proj X Y\<^bsup>A\<^esup>\<^sub>f \<circ>\<^sub>c h\<^sup>\<flat>\<^sup>\<sharp> = (right_cart_proj X Y \<circ>\<^sub>c h\<^sup>\<flat>)\<^sup>\<sharp>\<close>)
        then have unqiueness2: "(right_cart_proj X Y) \<circ>\<^sub>c  h\<^sup>\<flat> =  g\<^sup>\<flat>"
          by (smt assms cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp fflat_type g_type inv_transpose_func_def2 proj2_type proj_type transpose_func_def unqiueness1)
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
    using e_type j_type y_id_type by auto
  show "\<emptyset>\<^bsup>X\<^esup> \<cong> \<emptyset>"
    using cfunc_type_def function_to_empty_is_iso is_isomorphic_def iso_type by blast
qed

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
    by (simp add: left_proj_type transpose_func_def)
  have j1sharp_type:  "(right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y))\<^sup>\<sharp> : Y  \<rightarrow>  ((A \<times>\<^sub>c X) \<Coprod> (A \<times>\<^sub>c Y))\<^bsup>A\<^esup>"
    by (simp add: right_proj_type transpose_func_def)
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
    by (simp add: id_type transpose_func_def)
   (*Below is first centered eqn on page 52*)
  have FirstCenteredEqn1: "((id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> \<circ>\<^sub>c (left_coproj X Y))\<^sup>\<flat> =  id(A) \<times>\<^sub>f (left_coproj X Y)"
    by (smt assms cfunc_type_def flat_cancels_sharp gsharp_type idAxi0_type id_left_unit id_type inv_transpose_of_composition left_proj_type)
  have FirstCenteredEqn2: "((id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> \<circ>\<^sub>c (right_coproj X Y))\<^sup>\<flat> = id(A) \<times>\<^sub>f (right_coproj X Y)"
    by (metis assms cfunc_type_def eval_of_id_cross_id_sharp1 gsharp_type idAxi1_type id_left_unit inv_transpose_func_def2 inv_transpose_of_composition right_proj_type)
  then have SecondCenteredEqn: "(id(A \<times>\<^sub>c (X \<Coprod> Y)))\<^sup>\<sharp> = ((id(A) \<times>\<^sub>f left_coproj X Y)\<^sup>\<sharp>) \<amalg> ((id(A) \<times>\<^sub>f right_coproj X Y)\<^sup>\<sharp>)"
    by (smt assms cfunc_coprod_unique cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp FirstCenteredEqn1 gsharp_type left_proj_type right_proj_type sharp_cancels_flat)
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
    by (smt assms inv_transpose_func_def2 inv_transpose_of_composition j0sharpUj1sharp_type j1sharp_type left_coproj_cfunc_coprod left_proj_type phi_j0_Eqs_idAxi0 psi_def transpose_func_def)
  then have PsiPhiJ1EqsJ1: 
    "\<psi> \<circ>\<^sub>c \<phi> \<circ>\<^sub>c (right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)) = right_coproj (A \<times>\<^sub>c X) (A \<times>\<^sub>c Y)"
    by (smt assms inv_transpose_func_def2 inv_transpose_of_composition j0sharpUj1sharp_type j0sharp_type phi_j1_Eqs_idAxi1 psi_def right_coproj_cfunc_coprod right_proj_type transpose_func_def)
  have psiphi_type: "\<psi> \<circ>\<^sub>c \<phi> : (A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y \<rightarrow> (A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y"
    using phi_type psi_type by auto
    thm phi_type psi_type
  then have fullinverse: "\<psi> \<circ>\<^sub>c \<phi> = id((A \<times>\<^sub>c X) \<Coprod> A \<times>\<^sub>c Y)"
    by (metis PsiPhiJ0EqsJ0 PsiPhiJ1EqsJ1 cfunc_coprod_unique cfunc_type_def comp_associative id_left_unit id_type left_proj_type right_proj_type)
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
  unfolding is_smaller_than_def nonempty_def monomorphism_def
proof 
   obtain y where "y \<in>\<^sub>c Y"
    using assms nonempty_def by blast
   have map_type: "\<langle>id(X),y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> (X \<times>\<^sub>c Y)"
     using \<open>y \<in>\<^sub>c Y\<close> cfunc_prod_type cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp id_type terminal_func_type by auto
   have "monomorphism(\<langle> id(X),y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"
     by (metis \<open>y \<in>\<^sub>c Y\<close> comp_monic_imp_monic comp_type id_isomorphism id_type iso_imp_epi_and_monic left_cart_proj_cfunc_prod terminal_func_type)
   have "X \<le>\<^sub>c (X \<times>\<^sub>c Y)"
     using \<open>monomorphism \<langle>id\<^sub>c X,y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>\<close> is_smaller_than_def map_type by blast
   oops

lemma emptyset_is_finite:
  "is_finite(\<emptyset>)"
  using emptyset_is_empty id_isomorphism id_type is_finite_def one_separator_contrapos by blast

lemma emptyset_is_smallest_set:
  "\<emptyset> \<le>\<^sub>c X"
  by (metis cfunc_type_def emptyset_is_empty initial_func_type injective_def injective_imp_monomorphism is_smaller_than_def)

lemma smaller_than_finite_is_finite:
  assumes "X \<le>\<^sub>c Y \<and> is_finite(Y)"
  shows "is_finite(X)"
  oops

section \<open>Axiom 10: Natural Number Object\<close>

axiomatization
  natural_numbers :: "cset" ("\<nat>\<^sub>c") and
  zero :: "cfunc" and
  successor :: "cfunc"
  where
  zero_type: "zero \<in>\<^sub>c \<nat>\<^sub>c" and 
  successor_type: "successor: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and 
  natural_number_object_property: 
  "((q : one \<rightarrow> X) \<and> (f: X \<rightarrow> X))\<longrightarrow>
   (\<exists>!u. u: \<nat>\<^sub>c \<rightarrow> X \<and>
   triangle_commutes one \<nat>\<^sub>c X zero u q \<and>
   square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X u f successor u)"

lemma natural_number_object_func_unique:
  assumes u_type: "u : \<nat>\<^sub>c \<rightarrow> X" and v_type: "v : \<nat>\<^sub>c \<rightarrow> X" and f_type: "f: X \<rightarrow> X"
  assumes zeros_eq: "u \<circ>\<^sub>c zero = v \<circ>\<^sub>c zero"
  assumes u_successor_eq: "u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u"
  assumes v_successor_eq: "v \<circ>\<^sub>c successor = f \<circ>\<^sub>c v"
  shows "u = v"
proof -
  have u_zero_type: "u \<circ>\<^sub>c zero : one \<rightarrow> X"
    using u_type zero_type by auto
  have triangle_commutes_u: "triangle_commutes one \<nat>\<^sub>c X zero u (u \<circ>\<^sub>c zero)"
    by (simp add: triangle_commutes_def u_type u_zero_type zero_type)
  have square_commutes_u: "square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X u f successor u"
    by (simp add: f_type square_commutes_def successor_type u_successor_eq u_type)
  have uniqueness: "\<And> w. w: \<nat>\<^sub>c \<rightarrow> X \<and>
   triangle_commutes one \<nat>\<^sub>c X zero w (u \<circ>\<^sub>c zero) \<and>
   square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X w f successor w \<Longrightarrow> w = u"
    using u_zero_type triangle_commutes_u square_commutes_u
    using natural_number_object_property square_commutes_def by blast

  have v_zero_type: "v \<circ>\<^sub>c zero : one \<rightarrow> X"
    using v_type zero_type by auto
  have triangle_commutes_v: "triangle_commutes one \<nat>\<^sub>c X zero v (u \<circ>\<^sub>c zero)"
    by (simp add: triangle_commutes_def v_type v_zero_type zero_type zeros_eq)
  have square_commutes_v: "square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X v f successor v"
    by (simp add: f_type square_commutes_def successor_type v_successor_eq v_type)

  from uniqueness show "u = v"
    using square_commutes_v triangle_commutes_v v_type by blast
qed


definition is_NNO :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool"  where
   "is_NNO Y z s \<longleftrightarrow>(\<forall> X f q. ((q : one \<rightarrow> X) \<and> (f: X \<rightarrow> X))\<longrightarrow>
   (\<exists>!u. u: Y \<rightarrow> X \<and>
   triangle_commutes one Y X z u q \<and>
   square_commutes Y X Y X u f s u))"

lemma N_is_a_NNO:
    "is_NNO \<nat>\<^sub>c zero successor"
  by (simp add: is_NNO_def natural_number_object_property)

(* Exercise 2.6.5 *)
lemma NNOs_are_iso_N:
  assumes "is_NNO N z s"
  shows "N \<cong> \<nat>\<^sub>c"
proof-
  have z_and_s_type: "(z : one \<rightarrow>  N) \<and> (s:  N \<rightarrow>  N)"
    using assms is_NNO_def square_commutes_def successor_type triangle_commutes_def zero_type by auto
  then obtain u where u_type: "(u: \<nat>\<^sub>c \<rightarrow> N \<and>
   triangle_commutes one \<nat>\<^sub>c N zero u z \<and>
   square_commutes \<nat>\<^sub>c N \<nat>\<^sub>c N u s successor u)"
      proof -
         assume "\<And>u. u : \<nat>\<^sub>c \<rightarrow> N \<and> triangle_commutes one \<nat>\<^sub>c N zero u z \<and> square_commutes \<nat>\<^sub>c N \<nat>\<^sub>c N u s successor u \<Longrightarrow> thesis"
         then show ?thesis
           using z_and_s_type natural_number_object_property by blast
      qed
  then obtain v where v_type: "(v: N \<rightarrow> \<nat>\<^sub>c \<and>
   triangle_commutes one N  \<nat>\<^sub>c z v zero \<and>
   square_commutes N  \<nat>\<^sub>c N  \<nat>\<^sub>c v successor s v)"
     using assms is_NNO_def successor_type zero_type by blast
  then have vuzeroEqzero: "v \<circ>\<^sub>c (u \<circ>\<^sub>c zero) = zero"
     using  u_type triangle_commutes_def by auto
  have id_facts1: "(id(\<nat>\<^sub>c): \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c)\<and>
          (triangle_commutes one \<nat>\<^sub>c \<nat>\<^sub>c zero (id(\<nat>\<^sub>c)) zero)\<and>
          (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c (id(\<nat>\<^sub>c)) successor successor (id(\<nat>\<^sub>c)))"
     by (metis cfunc_type_def id_left_unit id_right_unit id_type square_commutes_def successor_type triangle_commutes_def zero_type)
  then have vu_facts: "((v \<circ>\<^sub>c u): \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c)\<and>
          (triangle_commutes one \<nat>\<^sub>c \<nat>\<^sub>c zero (v \<circ>\<^sub>c u) zero)\<and>
          (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c (v \<circ>\<^sub>c u) successor successor (v \<circ>\<^sub>c u))"
    proof -
      have "triangle_commutes one \<nat>\<^sub>c \<nat>\<^sub>c zero (v \<circ>\<^sub>c u) zero"
        using u_type v_type comp_associative triangle_commutes_def by auto
      then show ?thesis
        by (metis (no_types) u_type v_type comp_associative square_commutes_def triangle_commutes_def)
    qed
  then have half_isomorphism: "(v \<circ>\<^sub>c u) = id(\<nat>\<^sub>c)"
      using id_facts1 natural_number_object_property successor_type zero_type by blast
  have uvzEqz: "u \<circ>\<^sub>c (v \<circ>\<^sub>c z) = z"
    using triangle_commutes_def u_type v_type by auto
  have id_facts2: "(id(N): N \<rightarrow> N)\<and>
          (triangle_commutes one N N z (id(N)) z)\<and>
          (square_commutes N N N N (id(N)) s s (id(N)))"
    by (metis cfunc_type_def id_left_unit id_right_unit id_type square_commutes_def triangle_commutes_def z_and_s_type)
  then have uv_facts: "((u \<circ>\<^sub>c v): N \<rightarrow> N)\<and>
          (triangle_commutes one N N z (u \<circ>\<^sub>c v) z)\<and>
          (square_commutes N N N N (u \<circ>\<^sub>c v) s s (u \<circ>\<^sub>c v))"
    proof -
      have "u \<circ>\<^sub>c v \<in> ETCS_func"
        using cfunc_type_def compatible_comp_ETCS_func u_type v_type by presburger
      then have "u \<circ>\<^sub>c v : N \<rightarrow> N"
        using cfunc_type_def codomain_comp domain_comp u_type v_type by presburger
      then show ?thesis
        by (metis comp_associative square_commutes_def triangle_commutes_def u_type v_type)
    qed
  then have half_isomorphism2: "(u \<circ>\<^sub>c v) = id(N)"
    using assms id_facts2 is_NNO_def z_and_s_type by blast
  then show "N \<cong> \<nat>\<^sub>c"
    by (metis codomain_comp domain_comp half_isomorphism id_codomain id_domain is_isomorphic_def isomorphic_is_symmetric isomorphism_def u_type)
qed

(* Converse to Exercise 2.6.5 *)
lemma Iso_to_N_is_NNO:
  assumes "N \<cong> \<nat>\<^sub>c"
  shows "\<exists> z s. is_NNO N z s"
proof - 
  obtain i where i_type: "i: N \<rightarrow> \<nat>\<^sub>c \<and> isomorphism(i)"
    using assms is_isomorphic_def by auto 
  obtain j where j_type: "j: \<nat>\<^sub>c \<rightarrow> N \<and> isomorphism(j) \<and> i \<circ>\<^sub>c j = id(\<nat>\<^sub>c) \<and> j \<circ>\<^sub>c i = id(N)"
    using cfunc_type_def compatible_comp_ETCS_func i_type id_ETCS_func isomorphism_def by fastforce
  obtain z where z_form: "z = j \<circ>\<^sub>c zero"
    by simp
  obtain s where s_form: "s = (j \<circ>\<^sub>c successor)  \<circ>\<^sub>c i"
    by simp
  have z_type: "z: one \<rightarrow> N"
    using j_type z_form zero_type by auto
  have s_type: "s: N \<rightarrow> N"
    using i_type j_type s_form successor_type by auto
  have "is_NNO N z s"
    unfolding is_NNO_def
  proof auto
    fix X q f 
    assume q_type: "q: one \<rightarrow> X"
    assume f_type: "f:   X \<rightarrow> X"

    obtain u where u_properties: "
     (u: \<nat>\<^sub>c \<rightarrow> X \<and>
   triangle_commutes one \<nat>\<^sub>c X zero u q \<and>
   square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X u f successor u)"
      using f_type natural_number_object_property q_type by blast
    obtain v where v_Eqs_ui: "v = u \<circ>\<^sub>c i"
      by simp
    then have v_type: "v: N \<rightarrow> X"
      using comp_type i_type u_properties by blast
    then have D2_triangle: "v \<circ>\<^sub>c z = q"
      by (metis cfunc_type_def comp_associative id_left_unit j_type triangle_commutes_def u_properties v_Eqs_ui z_form)
    have D2_square: "v \<circ>\<^sub>c s = f \<circ>\<^sub>c v"
      by (metis cfunc_type_def comp_associative id_left_unit j_type s_form square_commutes_def u_properties v_Eqs_ui)
    show unique_v: "\<And> w y. w : N \<rightarrow> X \<Longrightarrow> y : N \<rightarrow> X \<Longrightarrow>
       triangle_commutes one N X z w q \<Longrightarrow> square_commutes N X N X w f s w \<Longrightarrow>
       triangle_commutes one N X z y q \<Longrightarrow> square_commutes N X N X y f s y \<Longrightarrow> w = y"
    proof -
      fix w y
      assume w_type: "w: N \<rightarrow> X"
      assume "square_commutes N X N X w f s w"
      then have w_square:"w \<circ>\<^sub>c s = f \<circ>\<^sub>c w"
        by (simp add: square_commutes_def)
      assume "triangle_commutes one N X z w q"
      then have w_triangle: "q = w \<circ>\<^sub>c z"
        by (simp add: triangle_commutes_def)

      assume y_type: "y: N \<rightarrow> X"
      assume "square_commutes N X N X y f s y"
      then have y_square:"y \<circ>\<^sub>c s = f \<circ>\<^sub>c y"
        by (simp add: square_commutes_def)
      assume "triangle_commutes one N X z y q"
      then have y_triangle: "q = y \<circ>\<^sub>c z"
        by (simp add: triangle_commutes_def)

      have "\<And> w. w: N \<rightarrow> X \<Longrightarrow> w \<circ>\<^sub>c s = f \<circ>\<^sub>c w \<Longrightarrow> q = w \<circ>\<^sub>c z \<Longrightarrow> w = v"
      proof -
        fix w 
        assume w_type: "w: N \<rightarrow> X"
        assume w_square:"w \<circ>\<^sub>c s = f \<circ>\<^sub>c w"
        assume w_triangle: "q = w \<circ>\<^sub>c z"

        have fact1: "(w \<circ>\<^sub>c j): \<nat>\<^sub>c \<rightarrow> X"
          by (meson comp_type j_type w_type)
        then have fact2: "triangle_commutes one \<nat>\<^sub>c X zero (w \<circ>\<^sub>c j) q"
          using comp_associative  triangle_commutes_def w_triangle z_form zero_type by force
        then have fact3: "square_commutes \<nat>\<^sub>c X \<nat>\<^sub>c X (w \<circ>\<^sub>c j) f successor (w \<circ>\<^sub>c j)"
        proof -
          have "successor = successor \<circ>\<^sub>c i \<circ>\<^sub>c j"
            by (metis (no_types) cfunc_type_def id_right_unit j_type successor_type)
          then show ?thesis
            by (metis comp_associative f_type fact1 s_form square_commutes_def successor_type w_square)
        qed
        then have fact4: "(w \<circ>\<^sub>c j)\<circ>\<^sub>c successor = (f \<circ>\<^sub>c w) \<circ>\<^sub>c j"
          by (simp add: comp_associative square_commutes_def)
        then have wj_Eqs_u: "w \<circ>\<^sub>c j = u"
          using f_type fact1 fact2 fact3 natural_number_object_property q_type u_properties by blast
        then show "w = v"
          by (metis cfunc_type_def comp_associative id_right_unit j_type v_Eqs_ui w_type)
      qed
      then show "w = y"
        using w_square w_triangle w_type y_square y_triangle y_type by blast
    qed
    show "\<exists>u. u : N \<rightarrow> X \<and> triangle_commutes one N X z u q \<and> square_commutes N X N X u f s u"
      using D2_square D2_triangle f_type s_type square_commutes_def triangle_commutes_def v_type z_type by auto
  qed
  then show "\<exists>z s. is_NNO N z s"
    by auto
qed

lemma zero_is_not_successor:
  "\<not>(\<exists> x. (x \<in>\<^sub>c \<nat>\<^sub>c \<and> zero = successor \<circ>\<^sub>c x))"
  oops

(* Proposition 2.6.6 *)
lemma  oneUN_iso_N_isomorphism:
 "isomorphism(zero \<amalg> successor)" 
proof - 
 have iso_type: "zero \<amalg> successor : one \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
   by (simp add: cfunc_coprod_type successor_type zero_type)
  obtain i0 where coproj0:  "i0 = left_coproj one \<nat>\<^sub>c"
    by simp
  obtain i1 where coproj1:  "i1 = right_coproj one \<nat>\<^sub>c"
    by simp 
  have i1zUi1s_type: "(i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor) : one \<Coprod> \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c"
    using cfunc_coprod_type coproj1 right_proj_type successor_type zero_type by auto
  have i1z_type: "i1 \<circ>\<^sub>c zero : one \<rightarrow>  one \<Coprod> \<nat>\<^sub>c"
    using coproj1 right_proj_type zero_type by auto
  obtain g where "(g: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)) \<and>
   (triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0) \<and>
   (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)))"
    by (metis coproj0 i1zUi1s_type left_proj_type natural_number_object_property square_commutes_def)
  then have second_diagram1: "g\<circ>\<^sub>c zero = i0"
    by (simp add: triangle_commutes_def)
  have second_diagram2: "g \<circ>\<^sub>c successor =   ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c g"
    using \<open>g : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0 \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> square_commutes_def by auto
  then have second_diagram3: "g \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)  = (i1 \<circ>\<^sub>c zero)"
    by (smt cfunc_coprod_comp comp_associative coproj0 coproj1 left_coproj_cfunc_coprod right_proj_type second_diagram1 successor_type zero_type)
  then have g_s_s_Eqs_i1zUi1s_g_s:
    "(g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor = ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (g \<circ>\<^sub>c successor)"
    by (metis comp_associative second_diagram2)
  then have g_s_s_zEqs_i1zUi1s_i1z: "((g \<circ>\<^sub>c successor) \<circ>\<^sub>c successor)\<circ>\<^sub>c zero =
    ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (i1 \<circ>\<^sub>c zero)"
    by (metis comp_associative second_diagram3)
  then have i1_sEqs_i1zUi1s_i1: "i1 \<circ>\<^sub>c successor =
    ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c i1"
    by (metis comp_type coproj1 i1z_type right_coproj_cfunc_coprod right_proj_type successor_type)
  then obtain u where "(u: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)) \<and>
      (triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero u (i1 \<circ>\<^sub>c zero)) \<and>
      (square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor u u ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor)))"
    using coproj1 i1zUi1s_type right_proj_type square_commutes_def successor_type triangle_commutes_def zero_type by auto
  then have u_Eqs_i1: "u=i1"
    by (metis coproj1 i1_sEqs_i1zUi1s_i1 natural_number_object_property right_proj_type square_commutes_def triangle_commutes_def)
  then have g_s_type: "g\<circ>\<^sub>c successor: \<nat>\<^sub>c \<rightarrow> (one \<Coprod> \<nat>\<^sub>c)"
    using \<open>g : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0 \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> comp_type successor_type by blast
  then have g_s_triangle: 
  "triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero (g\<circ>\<^sub>c successor) ( (i1 \<circ>\<^sub>c zero))"
    using comp_associative i1z_type second_diagram3 triangle_commutes_def zero_type by auto
  then have g_s_square: 
"square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c)  (one \<Coprod> \<nat>\<^sub>c) successor  (g\<circ>\<^sub>c successor)  (g\<circ>\<^sub>c successor) ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))"
    by (simp add: g_s_s_Eqs_i1zUi1s_g_s g_s_type i1zUi1s_type square_commutes_def successor_type)
  then have u_Eqs_g_s: "u=(g\<circ>\<^sub>c successor)"
    by (metis \<open>u : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero u (i1 \<circ>\<^sub>c zero) \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor u u ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> g_s_triangle i1z_type natural_number_object_property square_commutes_def)
  then have g_sEqs_i1: "(g\<circ>\<^sub>c successor) = i1"
    using u_Eqs_i1 by blast
  then have "(zero \<amalg> successor) \<circ>\<^sub>c g = id(\<nat>\<^sub>c)"
  proof - 
    have firstCenteredEqn1: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c zero) = 
                            (zero \<amalg> successor) \<circ>\<^sub>c i0"
      using second_diagram1 by auto
    also have firstCenteredEqn2:  "... = zero"
      using coproj0 left_coproj_cfunc_coprod successor_type zero_type by auto
    then have firstCenteredEqn: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c zero) = zero"
      by (simp add: firstCenteredEqn1)
    have secondCenteredEqn1: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c successor) = 
                            (zero \<amalg> successor) \<circ>\<^sub>c i1"
      using g_sEqs_i1 by blast
    have secondCenteredEqn: "(zero \<amalg> successor) \<circ>\<^sub>c (g \<circ>\<^sub>c successor) = successor"
      using coproj1 right_coproj_cfunc_coprod secondCenteredEqn1 successor_type zero_type by auto
    then show "(zero \<amalg> successor) \<circ>\<^sub>c g = id(\<nat>\<^sub>c)"
    proof -
        have f1: "\<forall>c ca cb. (c : ca \<rightarrow> cb) = (domain c = ca \<and> codomain c = cb \<and> c \<in> ETCS_func)"
           using cfunc_type_def by blast
        then have f2: "domain successor = \<nat>\<^sub>c \<and> codomain successor = \<nat>\<^sub>c \<and> successor \<in> ETCS_func"
           using successor_type by presburger
        have f3: "domain successor = \<nat>\<^sub>c \<and> codomain successor = \<nat>\<^sub>c \<and> successor \<in> ETCS_func"
           using f1 successor_type by presburger
        have f4: "\<forall>c ca. (c \<circ>\<^sub>c ca \<in> ETCS_func) = (domain c = codomain ca \<and> c \<in> ETCS_func \<and> ca \<in> ETCS_func)"
           using compatible_comp_ETCS_func by presburger
        have f5: "domain i1 = \<nat>\<^sub>c \<and> codomain i1 = one \<Coprod> \<nat>\<^sub>c \<and> i1 \<in> ETCS_func"
           using f1 g_sEqs_i1 g_s_type by presburger
        have "i1 \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c g = (i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor) \<circ>\<^sub>c g"
           using cfunc_coprod_comp comp_associative g_sEqs_i1 g_s_type successor_type zero_type by force
        then have "i1 \<circ>\<^sub>c zero \<amalg> successor \<circ>\<^sub>c g = i1 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
           using f3 by (metis comp_associative g_sEqs_i1 id_right_unit second_diagram2)
        then show ?thesis
           using f5 f4 f2 by (metis comp_associative coproj1 monomorphism_def right_coproj_are_monomorphisms secondCenteredEqn)
    qed
  qed
  then have "g \<circ>\<^sub>c (zero \<amalg> successor) = id(one \<Coprod> \<nat>\<^sub>c)"
  proof - 
    have ThirdCenteredEqn1: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i0) = g \<circ>\<^sub>c zero"
      using coproj0 left_coproj_cfunc_coprod successor_type zero_type by auto
    also have ThirdCenteredEqn2: "... = i0"
      by (simp add: second_diagram1)
    then have ThirdCenteredEqn: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i0) = i0"
      by (simp add: calculation)
    have ForthCenteredEqn1: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i1) = g \<circ>\<^sub>c successor"
      using coproj1 right_coproj_cfunc_coprod successor_type zero_type by auto
    have ForthCenteredEqn2: "... = i1"
      using g_sEqs_i1 by blast
    then have ForthCenteredEqn: "g \<circ>\<^sub>c ((zero \<amalg> successor)  \<circ>\<^sub>c i1) = i1"
      using ForthCenteredEqn1 by blast
    then show "g \<circ>\<^sub>c (zero \<amalg> successor) = id(one \<Coprod> \<nat>\<^sub>c)"
      by (metis \<open>g : \<nat>\<^sub>c \<rightarrow> one \<Coprod> \<nat>\<^sub>c \<and> triangle_commutes one \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) zero g i0 \<and> square_commutes \<nat>\<^sub>c \<nat>\<^sub>c (one \<Coprod> \<nat>\<^sub>c) (one \<Coprod> \<nat>\<^sub>c) successor g g ((i1 \<circ>\<^sub>c zero) \<amalg> (i1 \<circ>\<^sub>c successor))\<close> cfunc_coprod_comp cfunc_coprod_unique cfunc_type_def coproj0 coproj1 g_sEqs_i1 g_s_type id_left_unit id_type left_proj_type second_diagram1 successor_type zero_type)
  qed
  then show "isomorphism(zero \<amalg> successor)"
    by (metis \<open>g \<circ>\<^sub>c zero \<amalg> successor = id\<^sub>c (one \<Coprod> \<nat>\<^sub>c)\<close> \<open>zero \<amalg> successor \<circ>\<^sub>c g = id\<^sub>c \<nat>\<^sub>c\<close> codomain_comp domain_comp id_codomain id_domain isomorphism_def)
qed

(* Corollary *)
lemma oneUN_iso_N:
  "one \<Coprod> \<nat>\<^sub>c \<cong> \<nat>\<^sub>c"
  using cfunc_coprod_type is_isomorphic_def oneUN_iso_N_isomorphism successor_type zero_type by blast

lemma NUone_iso_N:
  "\<nat>\<^sub>c \<Coprod> one \<cong> \<nat>\<^sub>c"
  using coproduct_commutes isomorphic_is_transitive oneUN_iso_N by blast

(* Proposition 2.6.7 *)
lemma Peano's_Axioms:
 "injective(successor) \<and> \<not>surjective(successor)"
proof - 
  have i1_mono: "monomorphism(right_coproj one \<nat>\<^sub>c)"
    by (simp add: right_coproj_are_monomorphisms)
  have zUs_iso: "isomorphism(zero \<amalg> successor)"
    using oneUN_iso_N_isomorphism by blast
  have zUsi1EqsS: "(zero \<amalg> successor) \<circ>\<^sub>c (right_coproj one \<nat>\<^sub>c) = successor"
    using right_coproj_cfunc_coprod successor_type zero_type by auto
  then have succ_mono: "monomorphism(successor)"
    by (metis  cfunc_type_def compatible_comp_ETCS_func composition_of_monic_pair_is_monic i1_mono iso_imp_epi_and_monic oneUN_iso_N_isomorphism successor_type)
  have f_fact: "(\<f>\<circ>\<^sub>c\<beta>\<^bsub>\<Omega>\<^esub>): \<Omega> \<rightarrow> \<Omega>"
    using comp_type false_func_type terminal_func_type by blast
  then obtain u where u_form: "(u:  \<nat>\<^sub>c  \<rightarrow> \<Omega>) \<and>
   (triangle_commutes one  \<nat>\<^sub>c \<Omega> zero u \<t>) \<and>
   (square_commutes \<nat>\<^sub>c \<Omega> \<nat>\<^sub>c \<Omega> u (\<f>\<circ>\<^sub>c\<beta>\<^bsub>\<Omega>\<^esub>) successor u)"
    using natural_number_object_property true_func_type by blast
  have s_not_surj: "\<not>(surjective(successor))"
    proof (rule ccontr, auto)
      assume BWOC : "surjective(successor)"
      obtain n where snEqz: "successor \<circ>\<^sub>c n = zero"
        using BWOC cfunc_type_def successor_type surjective_def zero_type by auto
      have map_type: "\<beta>\<^bsub>\<Omega>\<^esub>\<circ>\<^sub>c (u\<circ>\<^sub>c n): one \<rightarrow> one"
       by (metis (mono_tags, lifting) cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp f_fact false_func_type snEqz successor_type u_form zero_type)
      then have uniqueness: "\<beta>\<^bsub>\<Omega>\<^esub>\<circ>\<^sub>c (u\<circ>\<^sub>c n) = id(one)"
       using id_type one_unique_element by blast
      have "\<t> = u \<circ>\<^sub>c zero"
       using triangle_commutes_def u_form by auto
      also have "... = u \<circ>\<^sub>c (successor \<circ>\<^sub>c n)"
       by (simp add: snEqz)
      also have "... = \<f> \<circ>\<^sub>c (\<beta>\<^bsub>\<Omega>\<^esub>\<circ>\<^sub>c (u\<circ>\<^sub>c n))"
       using comp_associative square_commutes_def u_form by auto
      also have "... =\<f>"
        by (metis cfunc_type_def false_func_type id_right_unit uniqueness)
      then  have Contradiction: "\<t> = \<f>"
        by (simp add: calculation)
      then show False
        using true_false_distinct by auto
    qed
  then show "injective successor \<and> \<not> surjective successor"
    using monomorphism_imp_injective succ_mono by blast
qed

(* Definition 2.6.9 *)
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

(* Definition 2.6.12 *)
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "fixed_point a g \<longleftrightarrow> (\<exists> A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = g)"
definition has_fixed_point :: "cfunc \<Rightarrow> bool" where
  "has_fixed_point g \<longleftrightarrow> (\<exists> a. fixed_point a g)"
definition fixed_point_property :: "cset \<Rightarrow> bool" where
  "fixed_point_property A \<longleftrightarrow> (\<forall> g. g : A \<rightarrow> A \<longrightarrow> has_fixed_point g)"

(* Exercise 2.6.15 *)
lemma inject_into_powerset: 
  "(\<exists> f.((f : X \<rightarrow> \<P> X) \<and> injective(f)))"
proof -
  obtain \<delta> where delta_def: "\<delta> = diagonal(X)"
    by simp
  have \<delta>_type: "\<delta> : X \<rightarrow> X \<times>\<^sub>c X"
    by (simp add: cfunc_prod_type delta_def diagonal_def id_type)
  have \<delta>_mono: "monomorphism(\<delta>)"
    by (metis comp_monic_imp_monic delta_def diagonal_def id_isomorphism id_type iso_imp_epi_and_monic left_cart_proj_cfunc_prod)
  obtain \<chi>\<^sub>\<delta> where chi_delta_def: "is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> \<delta> \<chi>\<^sub>\<delta>"
    using \<delta>_mono \<delta>_type characteristic_function_exists by blast 
  have helpful_fact: "\<forall> x y. (x\<in>\<^sub>c X \<and> y\<in>\<^sub>c X \<longrightarrow> (x=y \<longleftrightarrow> \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>))"
  proof (auto)
    fix y 
    assume y_type: "y \<in>\<^sub>c X"
    have "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>y,y\<rangle> = \<chi>\<^sub>\<delta> \<circ>\<^sub>c (\<delta> \<circ>\<^sub>c y)"
      by (simp add: delta_def diag_on_elements y_type)
    also have "... =  \<t> \<circ>\<^sub>c (\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c y)"
      using chi_delta_def comp_associative is_pullback_def square_commutes_def by auto
    also have "... = \<t>"
      by (metis cfunc_type_def comp_type id_right_unit id_type one_unique_element terminal_func_type true_func_type y_type)
    then show "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>y,y\<rangle> = \<t>"
      by (simp add: calculation)
  next
    fix x y
    assume x_type: "x\<in>\<^sub>c X" 
    assume y_type: "y\<in>\<^sub>c X" 
    assume chi_xxEq_t: "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>"
     
    have xy_prod_type: "\<langle>x,y\<rangle> : one \<rightarrow> X \<times>\<^sub>c X"
          by (simp add: cfunc_prod_type x_type y_type)
    have pullbackProp: "is_pullback X one (X \<times>\<^sub>c X) \<Omega> (\<beta>\<^bsub>X\<^esub>) \<t> \<delta> \<chi>\<^sub>\<delta>"
          using chi_delta_def by blast
    then obtain k where k_type: "k : one \<rightarrow> X \<and> \<delta> \<circ>\<^sub>c k = \<langle>x,y\<rangle>"
          by (smt cfunc_type_def chi_xxEq_t id_right_unit id_type is_pullback_def true_func_type xy_prod_type)
    then have "x = (left_cart_proj X X) \<circ>\<^sub>c \<langle>x,y\<rangle>"
          using left_cart_proj_cfunc_prod x_type y_type by auto
    also have "... = (left_cart_proj X X) \<circ>\<^sub>c (\<delta> \<circ>\<^sub>c k)"
          using k_type by auto
    also have "... = ((left_cart_proj X X) \<circ>\<^sub>c \<langle>id(X),id(X)\<rangle>) \<circ>\<^sub>c k"
          by (simp add: comp_associative delta_def diagonal_def)
    also have "... = id(X) \<circ>\<^sub>c k"
          by (metis id_type left_cart_proj_cfunc_prod)
    also have "... = y"
          by (metis calculation cfunc_prod_comp cfunc_type_def delta_def diagonal_def id_left_unit id_type k_type right_cart_proj_cfunc_prod y_type)
    then show "x = y"
         using calculation by blast
    qed
  
  have  \<chi>\<^sub>\<delta>sharp_type: "\<chi>\<^sub>\<delta>\<^sup>\<sharp> : X \<rightarrow> \<Omega>\<^bsup>X\<^esup>"
      using chi_delta_def is_pullback_def square_commutes_def transpose_func_def by auto
  have \<chi>\<^sub>\<delta>sharp_injective: "injective(\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      unfolding injective_def
  proof (auto)
      fix x y 
      assume x_type: "x \<in>\<^sub>c domain (\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      assume y_type: "y \<in>\<^sub>c domain (\<chi>\<^sub>\<delta>\<^sup>\<sharp>)"
      assume chixEqschiy: "\<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c x = \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c y"
      
      have "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,x\<rangle> = ((eval_func \<Omega> X) \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x,x\<rangle>"
        using chi_delta_def is_pullback_def square_commutes_def transpose_func_def by auto
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,x\<rangle>)"
        by (simp add: comp_associative)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c x, \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c x\<rangle>"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_type x_type by auto
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c x, \<chi>\<^sub>\<delta>\<^sup>\<sharp> \<circ>\<^sub>c y\<rangle>"
        using chixEqschiy by auto
      also have "... =  (eval_func \<Omega> X) \<circ>\<^sub>c ((id(X) \<times>\<^sub>f \<chi>\<^sub>\<delta>\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>x,y\<rangle>)"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_type x_type y_type by auto
      also have "... = \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle>"
        using chi_delta_def comp_associative is_pullback_def square_commutes_def transpose_func_def by auto
      then have computation: "\<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,x\<rangle> = \<chi>\<^sub>\<delta> \<circ>\<^sub>c \<langle>x,y\<rangle>"
        by (simp add: calculation)
      then show "x=y"
        using \<chi>\<^sub>\<delta>sharp_type cfunc_type_def helpful_fact x_type y_type by fastforce
    qed
  then show "(\<exists> f.((f : X \<rightarrow> \<P> X) \<and> injective(f)))"
    using \<chi>\<^sub>\<delta>sharp_type powerset_def by auto
qed

(*Defining addition on N*)

definition add_curried :: "cfunc" where
   "add_curried = (THE u. u: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero u ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) u (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) successor u)"

lemma add_curried_property: "(add_curried: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero add_curried ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) add_curried (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) successor add_curried)"
  unfolding add_curried_def
proof (rule theI')
  have q_type: "((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (simp add: left_cart_proj_type transpose_func_def)
  have f_type: "(successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) : (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: exp_func_type successor_type)
  show "\<exists>!x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
         triangle_commutes one \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero x ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
         square_commutes \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) x (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)
          successor x"
    using q_type f_type natural_number_object_property by auto
qed

lemma add_curried_type: "add_curried:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: add_curried_property)
 
lemma add_curried_0_eq: "add_curried \<circ>\<^sub>c zero = (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
  using add_curried_property triangle_commutes_def by blast

lemma add_curried_comp_succ_eq: "add_curried \<circ>\<^sub>c successor = (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c add_curried"
  using add_curried_property square_commutes_def by auto

definition add_uncurried :: "cfunc"
  where "add_uncurried = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add_curried)"

lemma add_uncurried_type: "add_uncurried:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding add_uncurried_def
proof - 
  have "id \<nat>\<^sub>c \<times>\<^sub>f add_curried : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: add_curried_property cfunc_cross_prod_type id_type)
  then show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type eval_func_type by blast
qed


definition add :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "+\<^sub>\<nat>" 65)
  where "m +\<^sub>\<nat> n = add_uncurried\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma add_def2:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add_curried \<circ>\<^sub>c n\<rangle>"
  unfolding add_def add_uncurried_def
  by (smt add_curried_type assms cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit id_type)



lemma add_respects_zero_on_right:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> zero = m"
proof -
  have projsharp_type: "(left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>: one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (simp add: left_cart_proj_type transpose_func_def)
  
  have "m +\<^sub>\<nat> zero =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add_curried \<circ>\<^sub>c zero\<rangle>"
    by (simp add: add_def2 assms zero_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<rangle>"
    by (simp add: add_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<circ>\<^sub>c id one \<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit projsharp_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<circ>\<^sub>c  \<langle>m, id one \<rangle>)"
    by (smt assms cfunc_cross_prod_comp_cfunc_prod id_type projsharp_type)
  also have "... =  (left_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c \<langle>m,id one\<rangle>"
    by (metis comp_associative left_cart_proj_type transpose_func_def)
  also have "... = m"
    using assms id_type left_cart_proj_cfunc_prod by blast
  then show "m +\<^sub>\<nat> zero = m"
    by (simp add: calculation)
qed

lemma zero_betaN_type: 
  shows "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>): \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using comp_type terminal_func_type zero_type by blast

lemma add_apply1:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
  unfolding add_def 
proof - 
  have fact1: "m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(1) comp_type terminal_func_type by blast
  have "add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c id one  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms(2) comp_type id_type one_unique_element terminal_func_type)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>(m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using comp_associative by auto
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
    using assms(2) cfunc_prod_comp fact1 id_type by fastforce
  then show "add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n"  using calculation by auto
qed

(*We make this unusual result its own lemma since it will be used in the commutativity proof*)
lemma id_N_def2:
  shows  "add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> = id \<nat>\<^sub>c"
  proof (rule natural_number_object_func_unique[where f= successor,  where X= "\<nat>\<^sub>c"])
    show "add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (meson add_uncurried_type cfunc_prod_type comp_type id_type terminal_func_type zero_type)
    show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (simp add: id_type)
    show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (simp add: successor_type)
    show "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    proof - 
      have "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = 
             add_uncurried \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<circ>\<^sub>c zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
        by (smt cfunc_prod_comp comp_associative comp_type id_type terminal_func_type zero_type)
      also have "... =add_uncurried \<circ>\<^sub>c \<langle>zero,zero \<rangle>"
        by (metis cfunc_type_def comp_associative comp_type id_left_unit id_right_unit id_type one_unique_element terminal_func_type zero_type)
      also have "... = zero"
        using add_def add_respects_zero_on_right zero_type by auto
      also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
        by (metis cfunc_type_def id_left_unit zero_type)
      then show ?thesis  using calculation by auto
    qed
    show "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof - 
      have "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
           add_uncurried \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor) "
        by (simp add: comp_associative)
      also have "... =  add_uncurried \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
        using cfunc_prod_comp id_type comp_type  successor_type zero_betaN_type by fastforce
      also have "... =  add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,  successor\<rangle>"
        by (metis cfunc_type_def comp_associative comp_type id_left_unit successor_type terminal_func_type terminal_func_unique)
      also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
        unfolding add_uncurried_def
        by auto
      also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  add_curried \<circ>\<^sub>c successor\<rangle>"
        by (smt \<open>id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> add_curried_property cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit successor_type zero_betaN_type)
      also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried\<rangle>"
        by (simp add: add_curried_comp_succ_eq)
      also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add_curried\<rangle>"
        by (smt \<open>id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> add_curried_property cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit square_commutes_def zero_betaN_type)
      also have "... = (successor  \<circ>\<^sub>c  eval_func \<nat>\<^sub>c \<nat>\<^sub>c ) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add_curried\<rangle>"
        unfolding exp_func_def
        using \<open>successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp eval_func_type transpose_func_def by auto
      also have "... = successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c \<langle>zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
        by (smt \<open>id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> add_curried_property cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit id_right_unit zero_betaN_type)
      also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        by (simp add: add_uncurried_def comp_associative)
      then show ?thesis using calculation by auto
    qed
    show " id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
      by (metis cfunc_type_def id_left_unit id_right_unit successor_type)
  qed


lemma add_respects_zero_on_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "zero +\<^sub>\<nat> m = m"
    by (metis add_apply1 assms cfunc_type_def comp_associative id_left_unit zero_type id_N_def2)



lemma add_respects_succ1:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n)  =  successor\<circ>\<^sub>c (m +\<^sub>\<nat> n)"
proof - 
  have fact1: "add_curried \<circ>\<^sub>c n: one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using add_curried_type assms(2) comp_type by blast
  have "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n) =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add_curried \<circ>\<^sub>c (successor  \<circ>\<^sub>c n)\<rangle>"
    using add_def2 assms successor_type by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried \<circ>\<^sub>c n\<rangle>"
    by (simp add: add_curried_comp_succ_eq comp_associative)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried \<circ>\<^sub>c n\<rangle>"
    by (metis assms(1) cfunc_type_def id_left_unit)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>m,add_curried \<circ>\<^sub>c n\<rangle>)"
    using  cfunc_cross_prod_comp_cfunc_prod
    by (smt add_curried_property assms(1) fact1 id_type square_commutes_def)
  also have "... = successor \<circ>\<^sub>c (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>m,add_curried \<circ>\<^sub>c n\<rangle>)"
    using cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp eval_func_type exp_func_def successor_type transpose_func_def by auto
  also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle>)"
    using add_def add_def2 assms by presburger
  also have "... = successor\<circ>\<^sub>c (m +\<^sub>\<nat> n)"
    by (simp add: add_def)
  then show ?thesis 
    using calculation by auto
qed

 

lemma add_respects_succ2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n)  =  (successor\<circ>\<^sub>c m) +\<^sub>\<nat> n"
proof -
  have fact00: "(successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c):  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type successor_type)
  then have fact01: "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using add_uncurried_type transpose_func_def by auto
  then have fact02: "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using comp_type zero_type by blast
  have fact03: "(successor  \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp> :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using comp_type left_cart_proj_type successor_type transpose_func_def by blast
  have fact0: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor): \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type successor_type)
  then have fact1: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using add_uncurried_type transpose_func_def by auto
  have fact04: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)): \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    using add_curried_property cfunc_cross_prod_type id_type square_commutes_def by auto
  have fact05: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) : \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: add_curried_type cfunc_cross_prod_type id_type)
  have fact2: "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>: one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (meson add_curried_property comp_type square_commutes_def triangle_commutes_def)
  have fact21: "(successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)) :\<nat>\<^sub>c\<times>\<^sub>c  one \<rightarrow>  \<nat>\<^sub>c"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp left_cart_proj_type successor_type by auto
  then have fact22: "(successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>: one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using transpose_func_def by blast
  have fact23: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero: one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using fact1 zero_type by auto
  have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
    using fact1 identity_distributes_across_composition zero_type by auto
  also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
    by (metis add_uncurried_type comp_associative comp_type fact0 transpose_func_def)
  also have "... = add_uncurried  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c zero))"
    using identity_distributes_across_composition successor_type zero_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor \<circ>\<^sub>c zero))"
    by (simp add: add_uncurried_def comp_associative)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)))"
    by (metis add_curried_property comp_type identity_distributes_across_composition successor_type zero_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_curried\<circ>\<^sub>c zero)))"
    by (simp add: add_curried_comp_succ_eq comp_associative)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>))"
    by (simp add: add_curried_0_eq)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
    using add_curried_property identity_distributes_across_composition square_commutes_def triangle_commutes_def by auto
  also have "... = (successor \<circ>\<^sub>c eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
    using cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp eval_func_type exp_func_def successor_type transpose_func_def by auto
  also have "... = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    by (metis comp_associative left_cart_proj_type transpose_func_def)
  then have fact2: " eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
   successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    using calculation by auto
  have fact3: "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp left_cart_proj_type successor_type transpose_func_def by auto 
  then have fact4: "(successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp> =
(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero"
    using transpose_func_unique fact2 fact21 fact23 by auto
  have fact5: "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero)) =
              successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)" (*page 13 big aligned equation*)
  proof -
    have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero))
     = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)"
      using fact01 identity_distributes_across_composition zero_type by auto
    also have "... = (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)"
      by (metis add_uncurried_type comp_associative comp_type fact00 transpose_func_def)
    also have "... =  add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f zero)"
      by (smt cfunc_cross_prod_comp_cfunc_cross_prod cfunc_type_def comp_associative id_left_unit id_right_unit id_type successor_type zero_type)
    also have "... = add_uncurried \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c successor)  \<times>\<^sub>f (zero \<circ>\<^sub>c id\<^sub>c one))"
      by (metis cfunc_type_def id_left_unit id_right_unit successor_type zero_type)
    also have "... =  add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)  \<circ>\<^sub>c(successor \<times>\<^sub>f id\<^sub>c one)"
      by (smt cfunc_cross_prod_comp_cfunc_cross_prod id_type successor_type zero_type)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c
        (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)  \<circ>\<^sub>c(successor \<times>\<^sub>f id\<^sub>c one)"
      by (simp add: add_uncurried_def comp_associative)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c  (successor \<times>\<^sub>f id\<^sub>c one)"
      by (metis add_curried_0_eq add_curried_property comp_associative identity_distributes_across_composition zero_type)
    also have "... = (left_cart_proj \<nat>\<^sub>c one)  \<circ>\<^sub>c  (successor \<times>\<^sub>f id\<^sub>c one)"
      by (metis comp_associative left_cart_proj_type transpose_func_def)
    also have "... = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
      by (simp add: id_type left_cart_proj_cfunc_cross_prod successor_type)
    then show ?thesis using calculation by auto
  qed

  have fact6: "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))
              = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
  proof - 
    have "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)) = 
        (successor \<circ>\<^sub>c  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried))  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (simp add: add_uncurried_def comp_associative)
    also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f))) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried))  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      unfolding exp_func_def using exponential_square_diagram square_commutes_def successor_type cfunc_type_def comp_type transpose_func_def by auto 
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (smt add_curried_property cfunc_cross_prod_comp_cfunc_cross_prod comp_associative id_domain id_right_unit id_type square_commutes_def)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (  add_curried \<circ>\<^sub>c successor)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (simp add: add_curried_comp_succ_eq)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f   add_curried)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor)"
      using add_curried_property comp_associative identity_distributes_across_composition successor_type by auto
    also have "... =  add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor)"
      by (simp add: add_uncurried_def comp_associative)
    then show ?thesis using calculation by auto
  qed

  

  have fact6b: "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))
    = (( add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
    by (smt add_curried_comp_succ_eq add_curried_type add_uncurried_def comp_associative comp_type flat_type inv_transpose_of_composition sharp_cancels_flat successor_type transpose_func_def transpose_of_comp)



  have fact6c: "(add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor
= successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f  \<circ>\<^sub>c (add_uncurried  \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
  proof -
    have "(add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor
= (successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
      by (smt comp_type fact1 fact6b sharp_cancels_flat successor_type)
    also have "... = successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f  \<circ>\<^sub>c (add_uncurried  \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
      using add_uncurried_type comp_type fact0 successor_type transpose_of_comp by blast
    then show ?thesis using calculation by auto
  qed

  have fact6d: "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))
              = add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
  proof - 
    have "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))
              = successor  \<circ>\<^sub>c eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
      by (simp add: add_uncurried_def comp_associative)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
proof -
    have f1: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried\<^sup>\<sharp> = add_uncurried"
        using add_uncurried_type transpose_func_def by blast
      have f2: "domain successor = \<nat>\<^sub>c"
        using cfunc_type_def successor_type by blast
      have f3: "codomain (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried\<^sup>\<sharp>) = domain (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)"
        using f1 by (metis (no_types) add_uncurried_type cfunc_type_def compatible_comp_ETCS_func)
      have f4: "successor \<circ>\<^sub>c add_uncurried \<in> ETCS_func"
        using add_uncurried_type cfunc_type_def compatible_comp_ETCS_func successor_type by fastforce
      have f5: "\<forall>c ca. codomain (eval_func ca c) = ca"
        by (meson cfunc_type_def eval_func_type)
      have f6: "\<forall>c ca. eval_func ca c \<in> ETCS_func"
        using cfunc_type_def eval_func_type by presburger
      have f7: "successor \<circ>\<^sub>c successor \<in> ETCS_func"
        using cfunc_type_def compatible_comp_ETCS_func successor_type by presburger
      then have f8: "domain (successor \<circ>\<^sub>c successor) = \<nat>\<^sub>c"
        using f6 f5 f2 by (metis comp_associative compatible_comp_ETCS_func)
      have "eval_func (codomain (successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c)) \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> = successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c"
        using f4 f3 f1 by (metis cfunc_type_def comp_associative compatible_comp_ETCS_func eval_func_type transpose_func_def)
     then show ?thesis
      using f8 f7 f6 f5 by (metis (no_types) add_uncurried_def comp_associative compatible_comp_ETCS_func exp_func_def)
  qed
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    by (smt add_curried_property cfunc_cross_prod_comp_cfunc_cross_prod comp_associative id_domain id_right_unit id_type square_commutes_def)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  ( add_curried \<circ>\<^sub>c successor)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    by (simp add: add_curried_comp_succ_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    using add_curried_type comp_associative identity_distributes_across_composition successor_type by auto
  also have "... = add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    by (simp add: add_uncurried_def comp_associative)
  also have "... = add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
  proof -
    have "successor \<times>\<^sub>f successor = (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<times>\<^sub>f (successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c)"
      by (metis (no_types) cfunc_type_def id_left_unit id_right_unit successor_type)
    then show ?thesis
      by (metis (no_types) cfunc_cross_prod_comp_cfunc_cross_prod id_type successor_type)
  qed
 then show ?thesis using calculation by auto
qed

  have fact6d: "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) = 
               ((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
  proof - 
    have "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) =  
        add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
      by (simp add: fact6d)
    also have "... = (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))"
      by (metis (mono_tags, lifting) cfunc_cross_prod_comp_cfunc_cross_prod cfunc_type_def id_left_unit id_right_unit id_type successor_type)
    also have "... = ((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
      by (smt add_uncurried_type comp_associative comp_type fact00 inv_transpose_func_def2 inv_transpose_of_composition successor_type transpose_func_def)
    then show ?thesis using calculation by auto
  qed


  have fact6e: "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor = 
                successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>" 
  proof - 
    have "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor = 
          (successor  \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
    proof -
      have "\<forall>c ca. ca \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> c \<or> \<not> ca : \<nat>\<^sub>c \<rightarrow> c"
        by (meson comp_type successor_type)
      then show ?thesis
        by (metis (no_types) fact01 fact6d sharp_cancels_flat)
    qed
    also have "... = successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
      by (meson add_uncurried_type comp_type fact00 successor_type transpose_of_comp)
then show ?thesis using calculation by auto
  qed
  

  
  have fact8: " (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor)))\<^sup>\<sharp> = 
                (add_uncurried \<circ>\<^sub>c ((successor) \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ))\<^sup>\<sharp>" 
   proof (rule natural_number_object_func_unique[where f= "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f",  where X= "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"])
     show sg1: "(add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
       by (simp add: fact1)
     show sg2: "(add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
       by (simp add: fact01)
     show sg3: "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f : \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
       by (simp add: exp_func_type successor_type)
     show sg4: " (add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> \<circ>\<^sub>c zero =
              (add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
       using fact02 fact21 fact4 fact5 transpose_func_unique by auto
     show sg5: "(add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> \<circ>\<^sub>c successor =
                successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp>"
       using fact6c by auto
     show sg6: "(add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
                 successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
       by (simp add: fact6e)
   qed
    
   have fact9: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor))) = 
                (add_uncurried \<circ>\<^sub>c ((successor) \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ))"
     by (smt add_uncurried_type comp_type fact0 fact00 fact8 transpose_func_def)

   show "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n)  =  (successor\<circ>\<^sub>c m) +\<^sub>\<nat> n"
   proof - 
     have "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n) = add_uncurried  \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>"
       by (simp add: add_def)
     also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor)) \<circ>\<^sub>c  \<langle>m,n\<rangle>"
       by (smt assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_type successor_type)
     also have "... = add_uncurried \<circ>\<^sub>c ((successor)\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c  ) \<circ>\<^sub>c  \<langle>m,n\<rangle>"
       by (simp add: comp_associative fact9)
     also have "... = add_uncurried  \<circ>\<^sub>c \<langle>successor  \<circ>\<^sub>c m, n\<rangle>"
       by (smt assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_type successor_type)
     also have "... = (successor\<circ>\<^sub>c m) +\<^sub>\<nat> n"
       by (simp add: add_def)
   then show ?thesis using calculation by auto
 qed
qed

lemma add_pi1_pi0_1xsEqs_s_add_pi1_pi_0:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<circ>\<^sub>c \<langle>m,n\<rangle> = 
successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>\<circ>\<^sub>c \<langle>m,n\<rangle>"
proof - 
  have type1: "\<langle>m,successor \<circ>\<^sub>c n\<rangle>: one \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    using assms(1) assms(2) cfunc_prod_type successor_type by auto
  have type2: "\<langle>m, n\<rangle>: one \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: assms(1) assms(2) cfunc_prod_type)
  have "add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<circ>\<^sub>c \<langle>m,n\<rangle> = 
add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    by (smt assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_type successor_type)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle> ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle> \<rangle>"
    using cfunc_prod_comp left_cart_proj_type right_cart_proj_type type1 by fastforce
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , m\<rangle>"
    by (metis assms(1) assms(2) comp_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod successor_type)
  also have "... = (successor \<circ>\<^sub>c n)  +\<^sub>\<nat> m"
    by (simp add: add_def)
  also have "... = successor  \<circ>\<^sub>c (n  +\<^sub>\<nat> m)"
    using add_respects_succ1 add_respects_succ2 assms(1) assms(2) by auto
  also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>n , m\<rangle>"
    by (simp add: add_def)
  also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c
                 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m , n\<rangle> , 
                  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m , n\<rangle>\<rangle>"
    using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>\<circ>\<^sub>c \<langle>m,n\<rangle>"
    using cfunc_prod_comp  left_cart_proj_type right_cart_proj_type type2 by fastforce 
  then show ?thesis using calculation by auto
qed

lemma pointfree_add_pi1_pi0_1xsEqs_s_add_pi1_pi_0:
  shows "add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)
    = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>"
proof (rule one_separator[where X="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where Y="\<nat>\<^sub>c"])
  have cross_type: "id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type successor_type)
  show "add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor
          : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type cross_type swap_type by blast
  show "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
          : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type successor_type swap_type by blast
next
  fix x
  assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  show "(add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c x
    = (successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
    using add_pi1_pi0_1xsEqs_s_add_pi1_pi_0 cart_prod_decomp comp_associative x_type by fastforce
qed

lemma add_commutes:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> n  = n +\<^sub>\<nat> m"
proof - 
  have type1: " \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>: 
        (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
      by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)
    have type2: "(add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>): (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow>  \<nat>\<^sub>c"
      by (meson add_uncurried_type comp_type type1)
    have type3: "(add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      by (simp add: transpose_func_def type2)
    have type4: "(add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero : one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      using type3 zero_type by auto
    have type5: " \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>:
         (\<nat>\<^sub>c \<times>\<^sub>c one)   \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
      by (meson cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type zero_type)
    have type6: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one):  \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> one"
      by (meson comp_type left_cart_proj_type terminal_func_type)
    then have type7: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one):  \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
      using comp_type zero_type by blast
    then have type8: "\<langle>m,n\<rangle>: one \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c\<nat>\<^sub>c"
      by (simp add: assms(1) assms(2) cfunc_prod_type)
  have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    left_cart_proj \<nat>\<^sub>c one"
  proof-
    have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried  \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
      using identity_distributes_across_composition type3 zero_type by auto 
    also have "... = add_uncurried \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
        using comp_associative transpose_func_def type2 by presburger
    also have "... = add_uncurried \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c
   \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (metis cfunc_cross_prod_def cfunc_type_def id_domain id_left_unit left_cart_proj_type zero_type)
    also have "... = add_uncurried \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>,
    (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>
   \<rangle>"
      using cfunc_prod_comp left_cart_proj_type right_cart_proj_type type5 by fastforce
    also have "... = add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one), (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      using cfunc_prod_comp
      by (smt comp_type left_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_cfunc_prod right_cart_proj_type zero_type)
    also have "... =  add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one), (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (metis right_cart_proj_type terminal_func_unique type6)
    also have "... =  add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one), id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (metis cfunc_type_def compatible_comp_ETCS_func domain_comp id_left_unit type6 zero_betaN_type)
    also have "... =  add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one) "
      using cfunc_prod_comp
      by (smt comp_associative id_type left_cart_proj_type zero_betaN_type)
    also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one) "
    by (simp add: comp_associative id_N_def2)
    also have "... = left_cart_proj \<nat>\<^sub>c one"
    by (metis cfunc_type_def id_left_unit left_cart_proj_type)
   then show ?thesis using calculation by auto
    qed
  
    then have fact0: "((add_uncurried  \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)
   = (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
    using inv_transpose_func_def2 sharp_cancels_flat type4 by fastforce 

  have fact1: "((add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor)\<^sup>\<flat> = 
        successor \<circ>\<^sub>c 
        add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>"
  proof - 
     have "((add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor)\<^sup>\<flat> = 
    (add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>)\<^sup>\<sharp>\<^sup>\<flat>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)"
      by (meson inv_transpose_of_composition successor_type type3)
    also have "... =  (add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>)
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)"
      using flat_cancels_sharp type2 by auto
    also have "... =  successor \<circ>\<^sub>c 
        add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>"
      using comp_associative pointfree_add_pi1_pi0_1xsEqs_s_add_pi1_pi_0 by auto
    then show ?thesis using calculation by auto
 qed

  have fact2: "((add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor) = 
        successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c 
        (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>"
    by (metis comp_type fact1 sharp_cancels_flat successor_type transpose_of_comp type2 type3)

  have add_curried_def2: "(add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> = add_curried"
    using add_curried_0_eq add_curried_property fact0 fact2 natural_number_object_func_unique square_commutes_def type3 by auto

  show "m +\<^sub>\<nat> n  = n +\<^sub>\<nat> m"
  proof - 
    have "m +\<^sub>\<nat> n = add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add_def)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried)\<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add_uncurried_def comp_associative)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add_curried_def2)
    also have "... =  (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle>"
      using \<open>m +\<^sub>\<nat> n = add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle>\<close> add_curried_def2 add_uncurried_def calculation transpose_func_def type2 by force
    also have "... = (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>m,n\<rangle>, (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>m,n\<rangle> \<rangle>) "
      by (metis cfunc_prod_comp comp_associative left_cart_proj_type right_cart_proj_type type8)
    also have "... = add_uncurried \<circ>\<^sub>c \<langle>n,m\<rangle>"
      using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
    also have "...= n +\<^sub>\<nat> m"
      by (simp add: add_def)
 then show ?thesis using calculation by auto
qed
qed

lemma add_associates:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "(a +\<^sub>\<nat> b ) +\<^sub>\<nat> c   = a +\<^sub>\<nat> (b +\<^sub>\<nat> c)"
proof - 
  have typePair: "\<langle>a,b\<rangle> \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c"
    using assms(1) assms(2) cfunc_prod_type by blast
  have typePair1: " \<langle>\<langle>a,b\<rangle>,zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: cfunc_prod_type typePair zero_type)
  have projPairType: "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c): 
    (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
    using comp_type left_cart_proj_type right_cart_proj_type by blast
  have type0: "\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast
  have type1: "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c): (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type left_cart_proj_type by blast
  have type2:  "\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    using cfunc_prod_type type0 type1 by blast
  have type3: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c  \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    using add_uncurried_type cfunc_cross_prod_type id_type type2 by auto

  have type4: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>): (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c  \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type type3 by blast
  have type5: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)"
    using transpose_func_def type4 by blast
  have type6: "add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one\<rightarrow>  \<nat>\<^sub>c"
    using add_uncurried_type comp_type left_cart_proj_type by blast

  have triangle1: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> = (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
  proof - 
    have triangle1_el: "(eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>  = a +\<^sub>\<nat> b"
    proof - (* if e: A \<times> X^A ---> X then below we have X = N and A = N\<times>N. *)
      have "(eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = 
      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) ) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)  \<times>\<^sub>f zero)  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
        using comp_associative identity_distributes_across_composition type5 zero_type by auto
      also have "... = (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
        using comp_associative flat_cancels_sharp inv_transpose_func_def2 type4 type5 by fastforce
      also have "... =  (add_uncurried \<circ>\<^sub>c   \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, add_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
        by (smt add_uncurried_type cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_type type0 type1)
      also have "... =  (add_uncurried \<circ>\<^sub>c   \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, add_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)  \<circ>\<^sub>c  \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>,zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod
        by (smt id_type typePair zero_type)
      also have "... = (add_uncurried \<circ>\<^sub>c   \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, add_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,zero\<rangle>"
        by (metis cfunc_type_def id_left_unit id_right_unit typePair zero_type)
      also have "... = add_uncurried \<circ>\<^sub>c   \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, add_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,zero\<rangle>"
        using comp_associative by auto
      also have "... = add_uncurried \<circ>\<^sub>c   \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,zero\<rangle>,
 add_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<rangle>  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,zero\<rangle> \<rangle> "
        by (smt add_uncurried_type cfunc_prod_comp cfunc_prod_type comp_associative comp_type type0 type1 typePair zero_type)
      also have "... =  add_uncurried \<circ>\<^sub>c   \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,zero\<rangle>,
 add_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,zero\<rangle>,
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,zero\<rangle>  \<rangle>  \<rangle> "
        by (smt cfunc_prod_comp comp_associative projPairType right_cart_proj_type typePair1)
      also have "... = add_uncurried \<circ>\<^sub>c   \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
 \<langle>a,b\<rangle>,
 add_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>a,b\<rangle>,
zero  \<rangle>  \<rangle> "
        using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod typePair zero_type by presburger
      also have "... = add_uncurried \<circ>\<^sub>c   \<langle>a, add_uncurried \<circ>\<^sub>c \<langle>b, zero  \<rangle>  \<rangle> "
        using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by presburger
      also have "... =  a +\<^sub>\<nat> b"
        using add_def add_respects_zero_on_right assms(2) by presburger
     then show ?thesis using calculation by auto
   qed
 
   have triangle1SecondHalf_el: "(eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f   (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one)\<^sup>\<sharp>)
 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>  = a +\<^sub>\<nat> b"
   proof - 
     have "(eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f   (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one)\<^sup>\<sharp>)
 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one) \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
       using comp_associative transpose_func_def type6 by presburger
     also have "... = add_uncurried \<circ>\<^sub>c
              (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>)"
       by (simp add: comp_associative)
     also have "... = a +\<^sub>\<nat> b"
       by (metis add_def id_type left_cart_proj_cfunc_prod typePair)
    then show ?thesis using calculation by auto
  qed

(*Now make the above point free*)
 have triangle1_elFree: "(eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))   = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f   (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one)\<^sup>\<sharp>)" 
 proof (rule one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y="\<nat>\<^sub>c"])
   show LHS_type: " eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
    id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    ((add_uncurried \<circ>\<^sub>c
      id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried \<circ>\<^sub>c
      \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
       left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
        \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
             left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
              \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
     zero) : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
     by (meson cfunc_cross_prod_type comp_type eval_func_type id_type type5 zero_type)
   show RHS_type: "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
    id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (add_uncurried \<circ>\<^sub>c
     left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) one)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
     using transpose_func_def type6 by presburger
   show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          ((add_uncurried \<circ>\<^sub>c
            id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried \<circ>\<^sub>c
            \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
             left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
              \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
                   left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
                    \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
           zero)) \<circ>\<^sub>c
         x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) one)\<^sup>\<sharp>) \<circ>\<^sub>c
         x"
     oops

section \<open>Axiom 11: Axiom of Choice\<close>

definition section_of :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" (infix "sectionof" 90)
  where "s sectionof f \<longleftrightarrow> s : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c s = id (codomain(f))"

definition split_epimorphism :: "cfunc \<Rightarrow> bool"
  where "split_epimorphism(f)\<longleftrightarrow>(\<exists> s. s sectionof f )" 

axiomatization
  where
  axiom_of_choice :"epimorphism(f) \<longrightarrow> (\<exists> g . g sectionof f)"

end