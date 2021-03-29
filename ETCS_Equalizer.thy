theory ETCS_Equalizer
  imports ETCS_Terminal
begin

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
    oops

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

end