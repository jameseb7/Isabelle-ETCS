section \<open>Equalizers and Subobjects\<close>

theory Equalizer
  imports Terminal
begin

subsection \<open>Equalizers\<close>

definition equalizer :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> o" where
  "equalizer(E, m, f, g) \<longleftrightarrow> (\<exists> X Y. (f : X \<rightarrow> Y) \<and> (g : X \<rightarrow> Y) \<and> (m : E \<rightarrow> X)
    \<and> (f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)
    \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)))"

lemma equalizer_def2:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and m_type: "m : E \<rightarrow> X"
  shows "equalizer(E, m, f, g) \<longleftrightarrow> ((f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)
    \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)))"
proof (rule iffI)
  assume "equalizer(E, m, f, g)"
  then obtain X' Y' where f_type': "f : X' \<rightarrow> Y'" and g_type': "g : X' \<rightarrow> Y'" and m_type': "m : E \<rightarrow> X'"
      and fm_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
      and uniq: "\<forall> h F. ((h : F \<rightarrow> X') \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)"
    unfolding equalizer_def by auto
  have XX': "X = X'" using f_type f_type' unfolding cfunc_type_def by auto
  show "(f \<circ>\<^sub>c m = g \<circ>\<^sub>c m) \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h))"
    using fm_gm uniq XX' by simp
next
  assume rhs: "(f \<circ>\<^sub>c m = g \<circ>\<^sub>c m) \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h))"
  show "equalizer(E, m, f, g)"
    unfolding equalizer_def
    using f_type g_type m_type rhs by auto
qed

lemma equalizer_eq:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and m_type: "m : E \<rightarrow> X"
  assumes eq: "equalizer(E, m, f, g)"
  shows "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
  using eq equalizer_def2[OF f_type g_type m_type] by auto

lemma similar_equalizers:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and m_type: "m : E \<rightarrow> X"
  assumes eq: "equalizer(E, m, f, g)"
  assumes h_type: "h : F \<rightarrow> X" and fh_gh: "f \<circ>\<^sub>c h = g \<circ>\<^sub>c h"
  shows "\<exists>! k. k : F \<rightarrow> E \<and> m \<circ>\<^sub>c k = h"
  using eq equalizer_def2[OF f_type g_type m_type] h_type fh_gh by auto

text \<open>The definition above and the axiomatization below correspond to Axiom 4 (Equalizers) in Halvorson.\<close>
axiomatization where
  equalizer_exists: "f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> \<exists> E m. equalizer(E, m, f, g)"

lemma equalizer_exists2:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y"
  shows "\<exists> E m. m : E \<rightarrow> X \<and> f \<circ>\<^sub>c m = g \<circ>\<^sub>c m \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h))"
proof -
  obtain E m where eq: "equalizer(E, m, f, g)" using f_type g_type equalizer_exists by blast
  obtain X' Y' where f_type': "f : X' \<rightarrow> Y'" and g_type': "g : X' \<rightarrow> Y'" and m_type': "m : E \<rightarrow> X'"
      and fm_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
      and uniq: "\<forall> h F. ((h : F \<rightarrow> X') \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)"
    using eq unfolding equalizer_def by auto
  have XX': "X' = X" using f_type f_type' unfolding cfunc_type_def by auto
  have m_type: "m : E \<rightarrow> X" using m_type' XX' by simp
  have uniq2: "\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)"
    using uniq XX' by simp
  show ?thesis using m_type fm_gm uniq2 by auto
qed

text \<open>The lemma below corresponds to Exercise 2.1.31 in Halvorson.\<close>
lemma equalizers_isomorphic:
  assumes eq1: "equalizer(E, m, f, g)" and eq2: "equalizer(E', m', f, g)"
  shows "\<exists> k. k : E \<rightarrow> E' \<and> isomorphism(k) \<and> m = m' \<circ>\<^sub>c k"
proof -
  obtain X Y where f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and m_type: "m : E \<rightarrow> X"
    using eq1 unfolding equalizer_def by auto
  obtain X' Y' where f_type': "f : X' \<rightarrow> Y'" and g_type': "g : X' \<rightarrow> Y'" and m'_type': "m' : E' \<rightarrow> X'"
    using eq2 unfolding equalizer_def by auto
  have XX': "X' = X" using f_type f_type' unfolding cfunc_type_def by auto
  have m'_type: "m' : E' \<rightarrow> X" using m'_type' XX' by simp

  have fm_eq_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m" using equalizer_eq[OF f_type g_type m_type eq1] by simp
  have fm'_eq_gm': "f \<circ>\<^sub>c m' = g \<circ>\<^sub>c m'" using equalizer_eq[OF f_type g_type m'_type eq2] by simp

  have ex1k: "\<exists>! k. k : E' \<rightarrow> E \<and> m \<circ>\<^sub>c k = m'"
    using similar_equalizers[OF f_type g_type m_type eq1 m'_type fm'_eq_gm'] by simp
  then obtain k where k_type: "k : E' \<rightarrow> E" and mk_eq_m': "m \<circ>\<^sub>c k = m'"
    by auto

  have ex1k': "\<exists>! k'. k' : E \<rightarrow> E' \<and> m' \<circ>\<^sub>c k' = m"
    using similar_equalizers[OF f_type g_type m'_type eq2 m_type fm_eq_gm] by simp
  then obtain k' where k'_type: "k' : E \<rightarrow> E'" and m'k_eq_m: "m' \<circ>\<^sub>c k' = m"
    by auto

  have kk'_type: "k \<circ>\<^sub>c k' : E \<rightarrow> E" using k_type k'_type comp_type by blast
  have m_kk'_eq_m: "m \<circ>\<^sub>c (k \<circ>\<^sub>c k') = m"
  proof -
    have "m \<circ>\<^sub>c (k \<circ>\<^sub>c k') = (m \<circ>\<^sub>c k) \<circ>\<^sub>c k'" using comp_associative2[OF k'_type k_type m_type] by simp
    also have "... = m' \<circ>\<^sub>c k'" using mk_eq_m' by simp
    also have "... = m" using m'k_eq_m by simp
    finally show ?thesis by simp
  qed
  have idE_type: "id(E) : E \<rightarrow> E" by (rule id_type)
  have m_idE_eq_m: "m \<circ>\<^sub>c id(E) = m" using id_right_unit2[OF m_type] by simp
  have ex1j: "\<exists>! j. j : E \<rightarrow> E \<and> m \<circ>\<^sub>c j = m"
    using similar_equalizers[OF f_type g_type m_type eq1 m_type fm_eq_gm] by simp
  then obtain j where j_type: "j : E \<rightarrow> E" and j_eq: "m \<circ>\<^sub>c j = m"
    and j_unique: "\<forall>j2. (j2 : E \<rightarrow> E \<and> m \<circ>\<^sub>c j2 = m) \<longrightarrow> j2 = j" by auto
  have kk'_eq_j: "k \<circ>\<^sub>c k' = j" using j_unique kk'_type m_kk'_eq_m by auto
  have idE_eq_j: "id(E) = j" using j_unique idE_type m_idE_eq_m by auto
  have kk'_eq_id: "k \<circ>\<^sub>c k' = id(E)" using kk'_eq_j idE_eq_j by simp

  have k'k_type: "k' \<circ>\<^sub>c k : E' \<rightarrow> E'" using k'_type k_type comp_type by blast
  have m'_k'k_eq_m': "m' \<circ>\<^sub>c (k' \<circ>\<^sub>c k) = m'"
  proof -
    have "m' \<circ>\<^sub>c (k' \<circ>\<^sub>c k) = (m' \<circ>\<^sub>c k') \<circ>\<^sub>c k" using comp_associative2[OF k_type k'_type m'_type] by simp
    also have "... = m \<circ>\<^sub>c k" using m'k_eq_m by simp
    also have "... = m'" using mk_eq_m' by simp
    finally show ?thesis by simp
  qed
  have idE'_type: "id(E') : E' \<rightarrow> E'" by (rule id_type)
  have m'_idE'_eq_m': "m' \<circ>\<^sub>c id(E') = m'" using id_right_unit2[OF m'_type] by simp
  have ex1j': "\<exists>! j'. j' : E' \<rightarrow> E' \<and> m' \<circ>\<^sub>c j' = m'"
    using similar_equalizers[OF f_type g_type m'_type eq2 m'_type fm'_eq_gm'] by simp
  then obtain j' where j'_type: "j' : E' \<rightarrow> E'" and j'_eq: "m' \<circ>\<^sub>c j' = m'"
    and j'_unique: "\<forall>j2. (j2 : E' \<rightarrow> E' \<and> m' \<circ>\<^sub>c j2 = m') \<longrightarrow> j2 = j'" by auto
  have k'k_eq_j': "k' \<circ>\<^sub>c k = j'" using j'_unique k'k_type m'_k'k_eq_m' by auto
  have idE'_eq_j': "id(E') = j'" using j'_unique idE'_type m'_idE'_eq_m' by auto
  have k'k_eq_id: "k' \<circ>\<^sub>c k = id(E')" using k'k_eq_j' idE'_eq_j' by simp

  have k'_iso: "isomorphism(k')"
    unfolding isomorphism_def
  proof (intro exI[where x=k])
    have dk: "domain(k) = E'" using k_type unfolding cfunc_type_def by auto
    have ck: "codomain(k) = E" using k_type unfolding cfunc_type_def by auto
    have dk': "domain(k') = E" using k'_type unfolding cfunc_type_def by auto
    have ck': "codomain(k') = E'" using k'_type unfolding cfunc_type_def by auto
    show "domain(k) = codomain(k') \<and> codomain(k) = domain(k') \<and>
        k \<circ>\<^sub>c k' = id(domain(k')) \<and> k' \<circ>\<^sub>c k = id(domain(k))"
      using dk ck dk' ck' kk'_eq_id k'k_eq_id by simp
  qed
  show ?thesis using k'_type k'_iso m'k_eq_m by auto
qed

lemma isomorphic_to_equalizer_is_equalizer:
  assumes phi_type: "\<phi> : E' \<rightarrow> E"
  assumes phi_iso: "isomorphism(\<phi>)"
  assumes eqlz: "equalizer(E, m, f, g)"
  assumes f_type: "f : X \<rightarrow> Y"
  assumes g_type: "g : X \<rightarrow> Y"
  assumes m_type: "m : E \<rightarrow> X"
  shows "equalizer(E', m \<circ>\<^sub>c \<phi>, f, g)"
proof -
  have phi_inv_type: "\<phi>\<^bold>\<inverse> : E \<rightarrow> E'" using inverse_type[OF phi_iso phi_type] by simp
  have phi_inv_phi: "\<phi>\<^bold>\<inverse> \<circ>\<^sub>c \<phi> = id(E')" using inv_left[OF phi_iso phi_type] by simp
  have phi_phi_inv: "\<phi> \<circ>\<^sub>c \<phi>\<^bold>\<inverse> = id(E)" using inv_right[OF phi_iso phi_type] by simp
  have m_phi_type: "m \<circ>\<^sub>c \<phi> : E' \<rightarrow> X" using phi_type m_type comp_type by blast

  have fm_eq_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m" using equalizer_eq[OF f_type g_type m_type eqlz] by simp
  have equalizes: "f \<circ>\<^sub>c (m \<circ>\<^sub>c \<phi>) = g \<circ>\<^sub>c (m \<circ>\<^sub>c \<phi>)"
  proof -
    have "f \<circ>\<^sub>c (m \<circ>\<^sub>c \<phi>) = (f \<circ>\<^sub>c m) \<circ>\<^sub>c \<phi>" using comp_associative2[OF phi_type m_type f_type] by simp
    also have "... = (g \<circ>\<^sub>c m) \<circ>\<^sub>c \<phi>" using fm_eq_gm by simp
    also have "... = g \<circ>\<^sub>c (m \<circ>\<^sub>c \<phi>)" using comp_associative2[OF phi_type m_type g_type] by simp
    finally show ?thesis by simp
  qed

  have uniq: "\<forall>h F. h : F \<rightarrow> X \<and> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h \<longrightarrow> (\<exists>!k. k : F \<rightarrow> E' \<and> (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k = h)"
  proof (intro allI impI)
    fix h F
    assume "h : F \<rightarrow> X \<and> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h"
    then have h_type: "h : F \<rightarrow> X" and h_eq: "f \<circ>\<^sub>c h = g \<circ>\<^sub>c h" by auto
    have ex1k0: "\<exists>! k0. k0 : F \<rightarrow> E \<and> m \<circ>\<^sub>c k0 = h"
      using similar_equalizers[OF f_type g_type m_type eqlz h_type h_eq] by simp
    then obtain k0 where k0_type: "k0 : F \<rightarrow> E" and k0_eq: "m \<circ>\<^sub>c k0 = h"
      and k0_unique: "\<forall>k2. (k2 : F \<rightarrow> E \<and> m \<circ>\<^sub>c k2 = h) \<longrightarrow> k2 = k0" by auto
    have k_type: "\<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0 : F \<rightarrow> E'" using k0_type phi_inv_type comp_type by blast
    have mphi_k_eq_h: "(m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c (\<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0) = h"
    proof -
      have "(m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c (\<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0) = m \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c (\<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0))"
        using comp_associative2[OF k_type phi_type m_type] by simp
      also have "... = m \<circ>\<^sub>c ((\<phi> \<circ>\<^sub>c \<phi>\<^bold>\<inverse>) \<circ>\<^sub>c k0)"
        using comp_associative2[OF k0_type phi_inv_type phi_type] by simp
      also have "... = m \<circ>\<^sub>c (id(E) \<circ>\<^sub>c k0)"
        using phi_phi_inv by simp
      also have "... = m \<circ>\<^sub>c k0"
        using id_left_unit2[OF k0_type] by simp
      also have "... = h" using k0_eq by simp
      finally show ?thesis by simp
    qed
    show "\<exists>!k. k : F \<rightarrow> E' \<and> (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k = h"
    proof (rule ex1I[where a="\<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0"])
      show "\<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0 : F \<rightarrow> E' \<and> (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c (\<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0) = h" using k_type mphi_k_eq_h by simp
    next
      fix k'
      assume "k' : F \<rightarrow> E' \<and> (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k' = h"
      then have k'_type: "k' : F \<rightarrow> E'" and k'_eq: "(m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k' = h" by auto
      have phik'_type: "\<phi> \<circ>\<^sub>c k' : F \<rightarrow> E" using k'_type phi_type comp_type by blast
      have m_phik'_eq_h: "m \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c k') = h"
      proof -
        have "m \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c k') = (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k'" using comp_associative2[OF k'_type phi_type m_type] by simp
        also have "... = h" using k'_eq by simp
        finally show ?thesis by simp
      qed
      have phik'_eq_k0: "\<phi> \<circ>\<^sub>c k' = k0" using k0_unique phik'_type m_phik'_eq_h by auto
      have k'_eq_phiinv_phik': "k' = \<phi>\<^bold>\<inverse> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c k')"
      proof -
        have "\<phi>\<^bold>\<inverse> \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c k') = (\<phi>\<^bold>\<inverse> \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k'" using comp_associative2[OF k'_type phi_type phi_inv_type] by simp
        also have "... = id(E') \<circ>\<^sub>c k'" using phi_inv_phi by simp
        also have "... = k'" using id_left_unit2[OF k'_type] by simp
        finally show ?thesis by simp
      qed
      then show "k' = \<phi>\<^bold>\<inverse> \<circ>\<^sub>c k0" using phik'_eq_k0 by simp
    qed
  qed
  show ?thesis unfolding equalizer_def2[OF f_type g_type m_phi_type] using equalizes uniq by simp
qed

text \<open>The lemma below corresponds to Exercise 2.1.34 in Halvorson.\<close>
lemma equalizer_is_monomorphism:
  assumes eq: "equalizer(E, m, f, g)"
  shows "monomorphism(m)"
  unfolding monomorphism_def
proof (intro allI impI)
  fix h1 h2
  obtain X Y where f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and m_type: "m : E \<rightarrow> X"
      and fm_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
      and uniqueness: "\<forall>h F. h : F \<rightarrow> X \<and> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h \<longrightarrow> (\<exists>!k. k : F \<rightarrow> E \<and> m \<circ>\<^sub>c k = h)"
    using eq unfolding equalizer_def by auto
  assume "codomain(h1) = domain(m) \<and> codomain(h2) = domain(m)"
  then have relation_h1: "codomain(h1) = domain(m)" and relation_h2: "codomain(h2) = domain(m)" by auto
  assume m_h1_h2: "m \<circ>\<^sub>c h1 = m \<circ>\<^sub>c h2"
  have dom_m: "domain(m) = E" using m_type unfolding cfunc_type_def by auto
  have dh1: "domain(m \<circ>\<^sub>c h1) = domain(h1)" using relation_h1 domain_comp by auto
  have dh2: "domain(m \<circ>\<^sub>c h2) = domain(h2)" using relation_h2 domain_comp by auto
  have dom_h1_h2: "domain(h1) = domain(h2)" using dh1 dh2 m_h1_h2 by simp
  have h1_type: "h1 : domain(h1) \<rightarrow> E" unfolding cfunc_type_def using relation_h1 dom_m by auto
  have h2_type: "h2 : domain(h1) \<rightarrow> E" unfolding cfunc_type_def using relation_h2 dom_m dom_h1_h2 by auto
  have mh1_type: "m \<circ>\<^sub>c h1 : domain(h1) \<rightarrow> X" using h1_type m_type comp_type by blast
  have f_mh1_eq_g_mh1: "f \<circ>\<^sub>c (m \<circ>\<^sub>c h1) = g \<circ>\<^sub>c (m \<circ>\<^sub>c h1)"
  proof -
    have "f \<circ>\<^sub>c (m \<circ>\<^sub>c h1) = (f \<circ>\<^sub>c m) \<circ>\<^sub>c h1" using comp_associative2[OF h1_type m_type f_type] by simp
    also have "... = (g \<circ>\<^sub>c m) \<circ>\<^sub>c h1" using fm_gm by simp
    also have "... = g \<circ>\<^sub>c (m \<circ>\<^sub>c h1)" using comp_associative2[OF h1_type m_type g_type] by simp
    finally show ?thesis by simp
  qed
  have ex1k: "\<exists>!k. k : domain(h1) \<rightarrow> E \<and> m \<circ>\<^sub>c k = m \<circ>\<^sub>c h1"
    using uniqueness[rule_format, where h="m \<circ>\<^sub>c h1" and F="domain(h1)"] mh1_type f_mh1_eq_g_mh1 by auto
  then obtain k where k_type: "k : domain(h1) \<rightarrow> E" and k_eq: "m \<circ>\<^sub>c k = m \<circ>\<^sub>c h1"
    and k_unique: "\<forall>k2. (k2 : domain(h1) \<rightarrow> E \<and> m \<circ>\<^sub>c k2 = m \<circ>\<^sub>c h1) \<longrightarrow> k2 = k" by auto
  have h1_eq_k: "h1 = k" using k_unique h1_type by auto
  have h2_eq_k: "h2 = k" using k_unique h2_type m_h1_h2 by auto
  show "h1 = h2" using h1_eq_k h2_eq_k by simp
qed

text \<open>The definition below corresponds to Definition 2.1.35 in Halvorson.\<close>
definition regular_monomorphism :: "cfunc \<Rightarrow> o"
  where "regular_monomorphism(f) \<longleftrightarrow>
          (\<exists> g h. domain(g) = codomain(f) \<and> domain(h) = codomain(f) \<and> equalizer(domain(f), f, g, h))"

text \<open>The lemma below corresponds to Exercise 2.1.36 in Halvorson.\<close>
lemma epi_regmon_is_iso:
  assumes epi: "epimorphism(f)" and regmon: "regular_monomorphism(f)"
  shows "isomorphism(f)"
proof -
  obtain g h where g_type: "domain(g) = codomain(f)" and h_type: "domain(h) = codomain(f)"
      and f_equalizer: "equalizer(domain(f), f, g, h)"
    using regmon unfolding regular_monomorphism_def by auto
  obtain X Y where g_type2: "g : X \<rightarrow> Y" and h_type2: "h : X \<rightarrow> Y" and f_type2: "f : domain(f) \<rightarrow> X"
      and gf_eq_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
      and f_uniq: "\<forall> k F. k : F \<rightarrow> X \<and> g \<circ>\<^sub>c k = h \<circ>\<^sub>c k \<longrightarrow> (\<exists>! j. j : F \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c j = k)"
    using f_equalizer unfolding equalizer_def by auto
  have Xeq: "X = codomain(f)" using g_type2 g_type unfolding cfunc_type_def by auto

  have epi_prop: "\<forall>g' h'. domain(g') = codomain(f) \<and> domain(h') = codomain(f) \<longrightarrow> (g' \<circ>\<^sub>c f = h' \<circ>\<^sub>c f \<longrightarrow> g' = h')"
    using epi unfolding epimorphism_def by auto
  have g_eq_h: "g = h" using epi_prop[rule_format, where g'=g and h'=h] g_type h_type gf_eq_hf by auto

  have idcf_type: "id(codomain(f)) : codomain(f) \<rightarrow> X" unfolding cfunc_type_def using Xeq id_domain id_codomain by auto
  have g_idcf_eq_h_idcf: "g \<circ>\<^sub>c id(codomain(f)) = h \<circ>\<^sub>c id(codomain(f))" using g_eq_h by simp

  have ex1k: "\<exists>! k. k : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c k = id(codomain(f))"
    using f_uniq[rule_format, where k="id(codomain(f))" and F="codomain(f)"] idcf_type g_idcf_eq_h_idcf by auto
  then obtain k where k_type: "k : codomain(f) \<rightarrow> domain(f)" and fk_eq_id: "f \<circ>\<^sub>c k = id(codomain(f))"
    by auto

  have f_mono: "monomorphism(f)" using equalizer_is_monomorphism[OF f_equalizer] by simp

  have domf_type: "f : domain(f) \<rightarrow> codomain(f)" unfolding cfunc_type_def using id_domain id_codomain by auto
  have kf_type: "k \<circ>\<^sub>c f : domain(f) \<rightarrow> domain(f)" using domf_type k_type comp_type by blast
  have iddomf_type: "id(domain(f)) : domain(f) \<rightarrow> domain(f)" by (rule id_type)

  have f_iddomf_eq_f_kf: "f \<circ>\<^sub>c id(domain(f)) = f \<circ>\<^sub>c (k \<circ>\<^sub>c f)"
  proof -
    have "f \<circ>\<^sub>c id(domain(f)) = f" using id_right_unit2[OF domf_type] by simp
    also have "... = id(codomain(f)) \<circ>\<^sub>c f" using id_left_unit2[OF domf_type] by simp
    also have "... = (f \<circ>\<^sub>c k) \<circ>\<^sub>c f" using fk_eq_id by simp
    also have "... = f \<circ>\<^sub>c (k \<circ>\<^sub>c f)" using comp_associative2[OF domf_type k_type domf_type] by simp
    finally show ?thesis by simp
  qed
  have mono_prop: "\<forall>g' h'. codomain(g') = domain(f) \<and> codomain(h') = domain(f) \<longrightarrow> (f \<circ>\<^sub>c g' = f \<circ>\<^sub>c h' \<longrightarrow> g' = h')"
    using f_mono unfolding monomorphism_def by auto
  have cod_iddomf: "codomain(id(domain(f))) = domain(f)" by (rule id_codomain)
  have cod_kf: "codomain(k \<circ>\<^sub>c f) = domain(f)" using kf_type unfolding cfunc_type_def by auto
  have kf_eq_id: "k \<circ>\<^sub>c f = id(domain(f))"
    using mono_prop[rule_format, where g'="id(domain(f))" and h'="k \<circ>\<^sub>c f"] cod_iddomf cod_kf f_iddomf_eq_f_kf by auto

  show "isomorphism(f)"
    unfolding isomorphism_def
  proof (intro exI[where x=k])
    have dk: "domain(k) = codomain(f)" using k_type unfolding cfunc_type_def by auto
    have ck: "codomain(k) = domain(f)" using k_type unfolding cfunc_type_def by auto
    show "domain(k) = codomain(f) \<and> codomain(k) = domain(f) \<and>
        k \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c k = id(domain(k))"
      using dk ck kf_eq_id fk_eq_id by simp
  qed
qed

subsection \<open>Subobjects\<close>

text \<open>The definition below corresponds to Definition 2.1.32 in Halvorson.\<close>
definition factors_through :: "cfunc \<Rightarrow> cfunc \<Rightarrow> o" (infix "factorsthru" 90)
  where "g factorsthru f \<longleftrightarrow> (\<exists> h. (h : domain(g) \<rightarrow> domain(f)) \<and> f \<circ>\<^sub>c h = g)"

lemma factors_through_def2:
  assumes g_type: "g : X \<rightarrow> Z" and f_type: "f : Y \<rightarrow> Z"
  shows "g factorsthru f \<longleftrightarrow> (\<exists> h. h : X \<rightarrow> Y \<and> f \<circ>\<^sub>c h = g)"
proof -
  have dom_g: "domain(g) = X" using g_type unfolding cfunc_type_def by auto
  have dom_f: "domain(f) = Y" using f_type unfolding cfunc_type_def by auto
  show ?thesis unfolding factors_through_def using dom_g dom_f by simp
qed

text \<open>The lemma below corresponds to Exercise 2.1.33 in Halvorson.\<close>
lemma xfactorthru_equalizer_iff_fx_eq_gx:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and eq: "equalizer(E, m, f, g)" and x_type: "x \<in>\<^sub>c X"
  shows "x factorsthru m \<longleftrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x"
proof -
  obtain X' Y' where f_type': "f : X' \<rightarrow> Y'" and m_type': "m : E \<rightarrow> X'"
    using eq unfolding equalizer_def by auto
  have XX': "X' = X" using f_type f_type' unfolding cfunc_type_def by auto
  have m_type: "m : E \<rightarrow> X" using m_type' XX' by simp
  have fm_eq_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m" using equalizer_eq[OF f_type g_type m_type eq] by simp
  show ?thesis
  proof (rule iffI)
    assume "x factorsthru m"
    then obtain h where h_type: "h : \<one> \<rightarrow> E" and h_eq: "m \<circ>\<^sub>c h = x"
      using factors_through_def2[OF x_type m_type] by auto
    have "f \<circ>\<^sub>c x = f \<circ>\<^sub>c (m \<circ>\<^sub>c h)" using h_eq by simp
    also have "... = (f \<circ>\<^sub>c m) \<circ>\<^sub>c h" using comp_associative2[OF h_type m_type f_type] by simp
    also have "... = (g \<circ>\<^sub>c m) \<circ>\<^sub>c h" using fm_eq_gm by simp
    also have "... = g \<circ>\<^sub>c (m \<circ>\<^sub>c h)" using comp_associative2[OF h_type m_type g_type] by simp
    also have "... = g \<circ>\<^sub>c x" using h_eq by simp
    finally show "f \<circ>\<^sub>c x = g \<circ>\<^sub>c x" by simp
  next
    assume RHS: "f \<circ>\<^sub>c x = g \<circ>\<^sub>c x"
    have ex1k: "\<exists>! k. k : \<one> \<rightarrow> E \<and> m \<circ>\<^sub>c k = x"
      using similar_equalizers[OF f_type g_type m_type eq x_type RHS] by simp
    then obtain k where k_type: "k : \<one> \<rightarrow> E" and k_eq: "m \<circ>\<^sub>c k = x" by auto
    show "x factorsthru m" using factors_through_def2[OF x_type m_type] k_type k_eq by auto
  qed
qed

text \<open>The definition below corresponds to Definition 2.1.37 in Halvorson. HOL's original bundles
  the subobject's underlying set and monomorphism into a single @{text "cset \<times> cfunc"} pair and
  writes this as an infix @{text "(B,m) \<subseteq>\<^sub>c X"}; FOL has no tuple type, so (matching the same
  design choice already made for @{text is_cart_prod}) the two components stay separate arguments
  throughout this whole theory.\<close>
definition subobject_of :: "cset \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> o" where
  "subobject_of(B, m, X) \<longleftrightarrow> (m : B \<rightarrow> X \<and> monomorphism(m))"

definition relative_subset :: "cset \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> o" where
  "relative_subset(B, m, X, A, n) \<longleftrightarrow>
    (m : B \<rightarrow> X \<and> monomorphism(m) \<and> n : A \<rightarrow> X \<and> monomorphism(n)
          \<and> (\<exists> k. k : B \<rightarrow> A \<and> n \<circ>\<^sub>c k = m))"

text \<open>The definition below corresponds to Definition 2.1.39 in Halvorson.\<close>
definition relative_member :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> o" where
  "relative_member(x, X, B, m) \<longleftrightarrow> (x \<in>\<^sub>c X \<and> monomorphism(m) \<and> m : B \<rightarrow> X \<and> x factorsthru m)"

lemma subobject_is_relative_subset: "subobject_of(B, m, A) \<longleftrightarrow> relative_subset(B, m, A, A, id(A))"
proof (rule iffI)
  assume "subobject_of(B, m, A)"
  then have m_type: "m : B \<rightarrow> A" and m_mono: "monomorphism(m)" unfolding subobject_of_def by auto
  have idA_type: "id(A) : A \<rightarrow> A" by (rule id_type)
  have idA_mono: "monomorphism(id(A))"
    using id_isomorphism iso_imp_epi_and_monic by auto
  have "\<exists>k. k : B \<rightarrow> A \<and> id(A) \<circ>\<^sub>c k = m" using m_type id_left_unit2[OF m_type] by auto
  then show "relative_subset(B, m, A, A, id(A))"
    unfolding relative_subset_def using m_type m_mono idA_type idA_mono by auto
next
  assume "relative_subset(B, m, A, A, id(A))"
  then show "subobject_of(B, m, A)" unfolding relative_subset_def subobject_of_def by auto
qed

text \<open>The lemma below corresponds to Proposition 2.1.40 in Halvorson.\<close>
lemma relative_subobject_member:
  assumes rel_sub: "relative_subset(A, n, X, B, m)" and x_type: "x \<in>\<^sub>c X"
  shows "relative_member(x, X, A, n) \<Longrightarrow> relative_member(x, X, B, m)"
proof -
  assume rel_mem: "relative_member(x, X, A, n)"
  have n_type: "n : A \<rightarrow> X" and m_type: "m : B \<rightarrow> X" and m_mono: "monomorphism(m)"
      and ex_k: "\<exists>k. k : A \<rightarrow> B \<and> m \<circ>\<^sub>c k = n"
    using rel_sub unfolding relative_subset_def by auto
  obtain k where k_type: "k : A \<rightarrow> B" and mk_eq_n: "m \<circ>\<^sub>c k = n" using ex_k by auto
  have x_factorsthru_n: "x factorsthru n" using rel_mem unfolding relative_member_def by auto
  obtain h where h_type: "h : \<one> \<rightarrow> A" and nh_eq_x: "n \<circ>\<^sub>c h = x"
    using factors_through_def2[OF x_type n_type] x_factorsthru_n by auto
  have kh_type: "k \<circ>\<^sub>c h : \<one> \<rightarrow> B" using h_type k_type comp_type by blast
  have m_kh_eq_x: "m \<circ>\<^sub>c (k \<circ>\<^sub>c h) = x"
  proof -
    have "m \<circ>\<^sub>c (k \<circ>\<^sub>c h) = (m \<circ>\<^sub>c k) \<circ>\<^sub>c h" using comp_associative2[OF h_type k_type m_type] by simp
    also have "... = n \<circ>\<^sub>c h" using mk_eq_n by simp
    also have "... = x" using nh_eq_x by simp
    finally show ?thesis by simp
  qed
  have x_factorsthru_m: "x factorsthru m"
    using factors_through_def2[OF x_type m_type] kh_type m_kh_eq_x by auto
  show "relative_member(x, X, B, m)"
    unfolding relative_member_def using x_type m_mono m_type x_factorsthru_m by auto
qed

subsection \<open>Inverse Image\<close>

text \<open>The definition below corresponds to a definition given by a diagram between Definition 2.1.37
  and Proposition 2.1.38 in Halvorson. HOL's original picks @{text A} via Hilbert's choice operator
  (@{text SOME}), which has no equivalent in plain FOL; instead we axiomatize @{text inverse_image}
  and @{text inverse_image_mapping} together as the (Skolemized) witness of the existence fact that
  @{text equalizer_exists} already gives for the parallel pair @{text "f \<circ>\<^sub>c left_cart_proj(X,B)"} /
  @{text "m \<circ>\<^sub>c right_cart_proj(X,B)"} -- the same conservative-Skolemization technique used for
  @{text inverse}/@{text "f\<^bold>\<inverse>"} in @{text Cfunc.thy}. This collapses HOL's two-stage
  @{text inverse_image_is_equalizer}/@{text inverse_image_is_equalizer2} into the single fact below.\<close>
axiomatization
  inverse_image :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1\<lparr>_\<rparr>\<^bsub>_\<^esub>" [101,0,0]100) and
  inverse_image_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc"
where
  inverse_image_spec: "m : B \<rightarrow> Y \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> monomorphism(m) \<Longrightarrow>
    equalizer(inverse_image(f, B, m), inverse_image_mapping(f, B, m), f \<circ>\<^sub>c left_cart_proj(X, B), m \<circ>\<^sub>c right_cart_proj(X, B))"

lemma inverse_image_is_equalizer2:
  assumes m_type: "m : B \<rightarrow> Y" and f_type: "f : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "equalizer(inverse_image(f, B, m), inverse_image_mapping(f, B, m), f \<circ>\<^sub>c left_cart_proj(X, B), m \<circ>\<^sub>c right_cart_proj(X, B))"
  using inverse_image_spec[OF m_type f_type m_mono] by simp

lemma inverse_image_mapping_type[type_rule]:
  assumes m_type: "m : B \<rightarrow> Y" and f_type: "f : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X \<times>\<^sub>c B"
proof -
  have eq: "equalizer(inverse_image(f, B, m), inverse_image_mapping(f, B, m), f \<circ>\<^sub>c left_cart_proj(X, B), m \<circ>\<^sub>c right_cart_proj(X, B))"
    using inverse_image_spec[OF m_type f_type m_mono] by simp
  have lp_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by (rule left_cart_proj_type)
  have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> Y" using lp_type f_type comp_type by blast
  obtain X' Y' where flp_type': "f \<circ>\<^sub>c left_cart_proj(X, B) : X' \<rightarrow> Y'"
      and k_type': "inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X'"
    using eq unfolding equalizer_def by auto
  have XX': "X' = X \<times>\<^sub>c B" using flp_type flp_type' unfolding cfunc_type_def by auto
  show ?thesis using k_type' XX' by simp
qed

lemma inverse_image_mapping_eq:
  assumes m_type: "m : B \<rightarrow> Y" and f_type: "f : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "f \<circ>\<^sub>c left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)
      = m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
proof -
  have eq: "equalizer(inverse_image(f, B, m), inverse_image_mapping(f, B, m), f \<circ>\<^sub>c left_cart_proj(X, B), m \<circ>\<^sub>c right_cart_proj(X, B))"
    using inverse_image_spec[OF m_type f_type m_mono] by simp
  have lp_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> Y" using lp_type f_type comp_type by blast
  have mrp_type: "m \<circ>\<^sub>c right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> Y" using rp_type m_type comp_type by blast
  have k_type: "inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X \<times>\<^sub>c B"
    using inverse_image_mapping_type[OF m_type f_type m_mono] by simp
  have bundled_eq: "(f \<circ>\<^sub>c left_cart_proj(X, B)) \<circ>\<^sub>c inverse_image_mapping(f, B, m)
      = (m \<circ>\<^sub>c right_cart_proj(X, B)) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using equalizer_eq[OF flp_type mrp_type k_type eq] by simp
  have left_assoc: "f \<circ>\<^sub>c left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) = (f \<circ>\<^sub>c left_cart_proj(X, B)) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using comp_associative2[OF k_type lp_type f_type] by simp
  have right_assoc: "m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) = (m \<circ>\<^sub>c right_cart_proj(X, B)) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using comp_associative2[OF k_type rp_type m_type] by simp
  show ?thesis using bundled_eq left_assoc right_assoc by simp
qed

lemma inverse_image_mapping_monomorphism:
  assumes m_type: "m : B \<rightarrow> Y" and f_type: "f : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "monomorphism(inverse_image_mapping(f, B, m))"
  using equalizer_is_monomorphism[OF inverse_image_spec[OF m_type f_type m_mono]] by simp

text \<open>The lemma below is the dual of Proposition 2.1.38 in Halvorson.\<close>
lemma inverse_image_monomorphism:
  assumes m_type: "m : B \<rightarrow> Y" and f_type: "f : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "monomorphism(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))"
proof -
  have k_type: "inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X \<times>\<^sub>c B"
    using inverse_image_mapping_type[OF m_type f_type m_mono] by simp
  have lp_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have lpk_type: "left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X"
    using lp_type k_type comp_type by blast
  have rpk_type: "right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> B"
    using rp_type k_type comp_type by blast
  have k_mono: "monomorphism(inverse_image_mapping(f, B, m))"
    using inverse_image_mapping_monomorphism[OF m_type f_type m_mono] by simp

  have key: "\<And>A c. c : A \<rightarrow> (inverse_image(f, B, m)) \<Longrightarrow>
      f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c c))
      = m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c c))"
  proof -
    fix A c
    assume c_type: "c : A \<rightarrow> (inverse_image(f, B, m))"
    have "f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c c))
        = f \<circ>\<^sub>c ((left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c c)"
      using comp_associative2[OF c_type k_type lp_type] by simp
    also have "... = (f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))) \<circ>\<^sub>c c"
      using comp_associative2[OF c_type lpk_type f_type] by simp
    also have "... = (m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))) \<circ>\<^sub>c c"
      using inverse_image_mapping_eq[OF m_type f_type m_mono] by simp
    also have "... = m \<circ>\<^sub>c ((right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c c)"
      using comp_associative2[OF c_type rpk_type m_type] by simp
    also have "... = m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c c))"
      using comp_associative2[OF c_type k_type rp_type] by simp
    finally show "f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c c))
      = m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c c))" by simp
  qed

  show ?thesis
    unfolding monomorphism_def3[OF lpk_type]
  proof (intro allI impI)
    fix g h A
    assume "g : A \<rightarrow> (inverse_image(f, B, m)) \<and> h : A \<rightarrow> (inverse_image(f, B, m))"
    then have g_type: "g : A \<rightarrow> (inverse_image(f, B, m))" and h_type: "h : A \<rightarrow> (inverse_image(f, B, m))" by auto
    assume left_eq: "(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c g
        = (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h"

    have kg_type: "inverse_image_mapping(f, B, m) \<circ>\<^sub>c g : A \<rightarrow> X \<times>\<^sub>c B" using k_type g_type comp_type by blast
    have kh_type: "inverse_image_mapping(f, B, m) \<circ>\<^sub>c h : A \<rightarrow> X \<times>\<^sub>c B" using k_type h_type comp_type by blast

    have left_eq2: "left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g) = left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c h)"
    proof -
      have "left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g) = (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c g"
        using comp_associative2[OF g_type k_type lp_type] by simp
      also have "... = (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h" using left_eq by simp
      also have "... = left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c h)"
        using comp_associative2[OF h_type k_type lp_type] by simp
      finally show ?thesis by simp
    qed

    have key_g: "f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g))
        = m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g))"
      using key[OF g_type] by simp
    have key_h: "f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c h))
        = m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c h))"
      using key[OF h_type] by simp

    have m_rpg_eq_m_rph: "m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g))
        = m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c h))"
      using key_g key_h left_eq2 by simp

    have rpg_type: "right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g) : A \<rightarrow> B"
      using rp_type kg_type comp_type by blast
    have rph_type: "right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c h) : A \<rightarrow> B"
      using rp_type kh_type comp_type by blast

    have mono_prop_m: "\<forall>g' h'. g' : A \<rightarrow> B \<and> h' : A \<rightarrow> B \<longrightarrow> (m \<circ>\<^sub>c g' = m \<circ>\<^sub>c h' \<longrightarrow> g' = h')"
      using m_mono monomorphism_def3[OF m_type] by auto
    have right_eq2: "right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g)
        = right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c h)"
      using mono_prop_m[rule_format] rpg_type rph_type m_rpg_eq_m_rph by auto

    have kg_eq_kh: "inverse_image_mapping(f, B, m) \<circ>\<^sub>c g = inverse_image_mapping(f, B, m) \<circ>\<^sub>c h"
      using cart_prod_eq[OF kg_type kh_type] left_eq2 right_eq2 by auto

    have mono_prop_k: "\<forall>g' h'. g' : A \<rightarrow> (inverse_image(f, B, m)) \<and> h' : A \<rightarrow> (inverse_image(f, B, m)) \<longrightarrow>
        (inverse_image_mapping(f, B, m) \<circ>\<^sub>c g' = inverse_image_mapping(f, B, m) \<circ>\<^sub>c h' \<longrightarrow> g' = h')"
      using k_mono monomorphism_def3[OF k_type] by auto
    show "g = h"
      using mono_prop_k[rule_format] g_type h_type kg_eq_kh by auto
  qed
qed

text \<open>Dropping HOL's fancy @{text "[f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>]map"} mixfix syntax in favor of a plain function call,
  consistent with the rest of this port.\<close>
definition inverse_image_subobject_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "inverse_image_subobject_mapping(f, B, m) = left_cart_proj(domain(f), B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"

lemma inverse_image_subobject_mapping_def2:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "inverse_image_subobject_mapping(f, B, m) = left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
  using f_type unfolding inverse_image_subobject_mapping_def cfunc_type_def by auto

lemma inverse_image_subobject_mapping_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Y" and m_type: "m : B \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "inverse_image_subobject_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X"
proof -
  have eq: "inverse_image_subobject_mapping(f, B, m) = left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using inverse_image_subobject_mapping_def2[OF f_type] by simp
  have "left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : inverse_image(f, B, m) \<rightarrow> X"
    using left_cart_proj_type inverse_image_mapping_type[OF m_type f_type m_mono] comp_type by blast
  then show ?thesis using eq by simp
qed

lemma inverse_image_subobject_mapping_mono:
  assumes f_type: "f : X \<rightarrow> Y" and m_type: "m : B \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "monomorphism(inverse_image_subobject_mapping(f, B, m))"
proof -
  have "inverse_image_subobject_mapping(f, B, m) = left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using inverse_image_subobject_mapping_def2[OF f_type] by simp
  then show ?thesis using inverse_image_monomorphism[OF m_type f_type m_mono] by simp
qed

lemma inverse_image_subobject:
  assumes m_type: "m : B \<rightarrow> Y" and f_type: "f : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "subobject_of(inverse_image(f, B, m), inverse_image_subobject_mapping(f, B, m), X)"
  unfolding subobject_of_def
  using inverse_image_subobject_mapping_type[OF f_type m_type m_mono]
        inverse_image_subobject_mapping_mono[OF f_type m_type m_mono] by simp

lemma inverse_image_pullback:
  assumes m_type: "m : B \<rightarrow> Y" and f_type: "f : X \<rightarrow> Y" and m_mono: "monomorphism(m)"
  shows "is_pullback(inverse_image(f, B, m), B, X, Y,
    right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m), m,
    left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m), f)"
  unfolding is_pullback_def
proof (intro conjI)
  have k_type: "inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X \<times>\<^sub>c B"
    using inverse_image_mapping_type[OF m_type f_type m_mono] by simp
  have lp_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  show right_type: "right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> B"
    using rp_type k_type comp_type by blast
  show "m : B \<rightarrow> Y" by (rule m_type)
  show left_type: "left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X"
    using lp_type k_type comp_type by blast
  show "f : X \<rightarrow> Y" by (rule f_type)
  show "m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) =
      f \<circ>\<^sub>c left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)"
    using inverse_image_mapping_eq[OF m_type f_type m_mono] by simp
  show "\<forall>Z k h. k : Z \<rightarrow> B \<and> h : Z \<rightarrow> X \<and> m \<circ>\<^sub>c k = f \<circ>\<^sub>c h \<longrightarrow>
      (\<exists>!j. j : Z \<rightarrow> (inverse_image(f, B, m)) \<and>
        (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = k \<and>
        (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = h)"
  proof (intro allI impI)
    fix Z k h
    assume "k : Z \<rightarrow> B \<and> h : Z \<rightarrow> X \<and> m \<circ>\<^sub>c k = f \<circ>\<^sub>c h"
    then have k_type2: "k : Z \<rightarrow> B" and h_type2: "h : Z \<rightarrow> X" and mk_eq_fh: "m \<circ>\<^sub>c k = f \<circ>\<^sub>c h" by auto
    have hk_type: "\<langle>h,k\<rangle> : Z \<rightarrow> X \<times>\<^sub>c B" using h_type2 k_type2 cfunc_prod_type by auto
    have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> Y" using lp_type f_type comp_type by blast
    have mrp_type: "m \<circ>\<^sub>c right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> Y" using rp_type m_type comp_type by blast
    have flp_hk_eq: "(f \<circ>\<^sub>c left_cart_proj(X, B)) \<circ>\<^sub>c \<langle>h,k\<rangle> = (m \<circ>\<^sub>c right_cart_proj(X, B)) \<circ>\<^sub>c \<langle>h,k\<rangle>"
    proof -
      have "(f \<circ>\<^sub>c left_cart_proj(X, B)) \<circ>\<^sub>c \<langle>h,k\<rangle> = f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c \<langle>h,k\<rangle>)"
        using comp_associative2[OF hk_type lp_type f_type] by simp
      also have "... = f \<circ>\<^sub>c h" using left_cart_proj_cfunc_prod[OF h_type2 k_type2] by simp
      also have "... = m \<circ>\<^sub>c k" using mk_eq_fh by simp
      also have "... = m \<circ>\<^sub>c (right_cart_proj(X, B) \<circ>\<^sub>c \<langle>h,k\<rangle>)"
        using right_cart_proj_cfunc_prod[OF h_type2 k_type2] by simp
      also have "... = (m \<circ>\<^sub>c right_cart_proj(X, B)) \<circ>\<^sub>c \<langle>h,k\<rangle>"
        using comp_associative2[OF hk_type rp_type m_type] by simp
      finally show ?thesis by simp
    qed
    have eq: "equalizer(inverse_image(f, B, m), inverse_image_mapping(f, B, m), f \<circ>\<^sub>c left_cart_proj(X, B), m \<circ>\<^sub>c right_cart_proj(X, B))"
      using inverse_image_spec[OF m_type f_type m_mono] by simp
    have ex1u: "\<exists>!u. u : Z \<rightarrow> (inverse_image(f, B, m)) \<and> inverse_image_mapping(f, B, m) \<circ>\<^sub>c u = \<langle>h,k\<rangle>"
      using similar_equalizers[OF flp_type mrp_type k_type eq hk_type flp_hk_eq] by simp
    then obtain u where u_type: "u : Z \<rightarrow> (inverse_image(f, B, m))" and u_eq: "inverse_image_mapping(f, B, m) \<circ>\<^sub>c u = \<langle>h,k\<rangle>"
      by auto
    have rpk_u_eq_k: "(right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c u = k"
    proof -
      have "(right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c u = right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c u)"
        using comp_associative2[OF u_type k_type rp_type] by simp
      also have "... = right_cart_proj(X, B) \<circ>\<^sub>c \<langle>h,k\<rangle>" using u_eq by simp
      also have "... = k" using right_cart_proj_cfunc_prod[OF h_type2 k_type2] by simp
      finally show ?thesis by simp
    qed
    have lpk_u_eq_h: "(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c u = h"
    proof -
      have "(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c u = left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c u)"
        using comp_associative2[OF u_type k_type lp_type] by simp
      also have "... = left_cart_proj(X, B) \<circ>\<^sub>c \<langle>h,k\<rangle>" using u_eq by simp
      also have "... = h" using left_cart_proj_cfunc_prod[OF h_type2 k_type2] by simp
      finally show ?thesis by simp
    qed
    show "\<exists>!j. j : Z \<rightarrow> (inverse_image(f, B, m)) \<and>
        (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = k \<and>
        (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = h"
    proof (rule ex1I[where a=u])
      show "u : Z \<rightarrow> (inverse_image(f, B, m)) \<and>
        (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c u = k \<and>
        (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c u = h"
        using u_type rpk_u_eq_k lpk_u_eq_h by simp
    next
      fix y
      assume "y : Z \<rightarrow> (inverse_image(f, B, m)) \<and>
        (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c y = k \<and>
        (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c y = h"
      then have y_type: "y : Z \<rightarrow> (inverse_image(f, B, m))"
          and rpk_y_eq_k: "(right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c y = k"
          and lpk_y_eq_h: "(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c y = h" by auto
      have ky_eq_hk: "inverse_image_mapping(f, B, m) \<circ>\<^sub>c y = \<langle>h,k\<rangle>"
      proof -
        have ky_type: "inverse_image_mapping(f, B, m) \<circ>\<^sub>c y : Z \<rightarrow> X \<times>\<^sub>c B" using k_type y_type comp_type by blast
        have lp_ky: "left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c y) = h"
        proof -
          have "left_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c y) = (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c y"
            using comp_associative2[OF y_type k_type lp_type] by simp
          also have "... = h" using lpk_y_eq_h by simp
          finally show ?thesis by simp
        qed
        have rp_ky: "right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c y) = k"
        proof -
          have "right_cart_proj(X, B) \<circ>\<^sub>c (inverse_image_mapping(f, B, m) \<circ>\<^sub>c y) = (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c y"
            using comp_associative2[OF y_type k_type rp_type] by simp
          also have "... = k" using rpk_y_eq_k by simp
          finally show ?thesis by simp
        qed
        show ?thesis using cfunc_prod_unique[OF h_type2 k_type2 ky_type lp_ky rp_ky] by simp
      qed
      obtain u2 where u2_type: "u2 : Z \<rightarrow> (inverse_image(f, B, m))" and u2_eq: "inverse_image_mapping(f, B, m) \<circ>\<^sub>c u2 = \<langle>h,k\<rangle>"
          and u2_unique: "\<forall>w. (w : Z \<rightarrow> (inverse_image(f, B, m)) \<and> inverse_image_mapping(f, B, m) \<circ>\<^sub>c w = \<langle>h,k\<rangle>) \<longrightarrow> w = u2"
        using ex1u by auto
      have y_eq_u2: "y = u2" using u2_unique y_type ky_eq_hk by auto
      have u_eq_u2: "u = u2" using u2_unique u_type u_eq by auto
      show "y = u" using y_eq_u2 u_eq_u2 by simp
    qed
  qed
qed

text \<open>The lemma below corresponds to Proposition 2.1.41 in Halvorson.\<close>
lemma in_inverse_image:
  assumes f_type: "f : X \<rightarrow> Y" and B_sub: "subobject_of(B, m, Y)" and x_type: "x \<in>\<^sub>c X"
  shows "relative_member(x, X, inverse_image(f, B, m), left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))
       \<longleftrightarrow> relative_member(f \<circ>\<^sub>c x, Y, B, m)"
proof -
  have m_type: "m : B \<rightarrow> Y" and m_mono: "monomorphism(m)" using B_sub unfolding subobject_of_def by auto
  have k_type: "inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X \<times>\<^sub>c B"
    using inverse_image_mapping_type[OF m_type f_type m_mono] by simp
  have lp_type: "left_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, B) : X \<times>\<^sub>c B \<rightarrow> B" by (rule right_cart_proj_type)
  have lpk_type: "left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> X"
    using lp_type k_type comp_type by blast
  have rpk_type: "right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m) : (inverse_image(f, B, m)) \<rightarrow> B"
    using rp_type k_type comp_type by blast
  have fx_type: "f \<circ>\<^sub>c x \<in>\<^sub>c Y" using x_type f_type comp_type by blast

  show ?thesis
  proof (rule iffI)
    assume "relative_member(x, X, inverse_image(f, B, m), left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))"
    then have x_factorsthru_lpk: "x factorsthru (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))"
      unfolding relative_member_def by auto
    then obtain h where h_type: "h : \<one> \<rightarrow> (inverse_image(f, B, m))"
        and h_def: "(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h = x"
      using factors_through_def2[OF x_type lpk_type] by auto

    have fx_eq: "f \<circ>\<^sub>c x = (m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h"
    proof -
      have "f \<circ>\<^sub>c x = f \<circ>\<^sub>c ((left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h)" using h_def by simp
      also have "... = (f \<circ>\<^sub>c (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))) \<circ>\<^sub>c h"
        using comp_associative2[OF h_type lpk_type f_type] by simp
      also have "... = (m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h"
        using inverse_image_mapping_eq[OF m_type f_type m_mono] by simp
      finally show ?thesis by simp
    qed
    have fx_eq2: "f \<circ>\<^sub>c x = m \<circ>\<^sub>c ((right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h)"
    proof -
      have "(m \<circ>\<^sub>c right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h = m \<circ>\<^sub>c ((right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h)"
        using comp_associative2[OF h_type rpk_type m_type] by simp
      then show ?thesis using fx_eq by simp
    qed
    have rpkh_type: "(right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c h : \<one> \<rightarrow> B"
      using rpk_type h_type comp_type by blast
    have fx_factorsthru_m: "(f \<circ>\<^sub>c x) factorsthru m"
      using factors_through_def2[OF fx_type m_type] rpkh_type fx_eq2 by auto
    show "relative_member(f \<circ>\<^sub>c x, Y, B, m)"
      unfolding relative_member_def using fx_type m_mono m_type fx_factorsthru_m by auto
  next
    assume "relative_member(f \<circ>\<^sub>c x, Y, B, m)"
    then have fx_factorsthru_m: "(f \<circ>\<^sub>c x) factorsthru m" unfolding relative_member_def by auto
    then obtain h where h_type: "h : \<one> \<rightarrow> B" and h_def: "m \<circ>\<^sub>c h = f \<circ>\<^sub>c x"
      using factors_through_def2[OF fx_type m_type] by auto

    have pb: "is_pullback(inverse_image(f, B, m), B, X, Y,
      right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m), m,
      left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m), f)"
      using inverse_image_pullback[OF m_type f_type m_mono] by simp
    have pb_uniq: "\<forall>Z k' h'. k' : Z \<rightarrow> B \<and> h' : Z \<rightarrow> X \<and> m \<circ>\<^sub>c k' = f \<circ>\<^sub>c h' \<longrightarrow>
        (\<exists>!j. j : Z \<rightarrow> (inverse_image(f, B, m)) \<and>
          (right_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = k' \<and>
          (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = h')"
      using pb unfolding is_pullback_def by auto
    have h_x_eq: "m \<circ>\<^sub>c h = f \<circ>\<^sub>c x" using h_def by simp
    obtain j where j_type: "j : \<one> \<rightarrow> (inverse_image(f, B, m))"
        and lpk_j_eq_x: "(left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m)) \<circ>\<^sub>c j = x"
      using pb_uniq[rule_format, where Z="\<one>" and k'=h and h'=x] h_type x_type h_x_eq by auto

    have x_factorsthru: "x factorsthru (left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))"
      using factors_through_def2[OF x_type lpk_type] j_type lpk_j_eq_x by auto
    show "relative_member(x, X, inverse_image(f, B, m), left_cart_proj(X, B) \<circ>\<^sub>c inverse_image_mapping(f, B, m))"
      unfolding relative_member_def
      using x_type inverse_image_monomorphism[OF m_type f_type m_mono] lpk_type x_factorsthru by auto
  qed
qed

subsection \<open>Fibered Products\<close>

text \<open>The definition below corresponds to Definition 2.1.42 in Halvorson. As with @{text
  inverse_image}/@{text inverse_image_mapping} above, HOL's @{text SOME}-based two-stage definition
  collapses into a single conservative Skolemization of the existence fact @{text equalizer_exists}
  already gives for the parallel pair @{text "f \<circ>\<^sub>c left_cart_proj(X,Y)"} /
  @{text "g \<circ>\<^sub>c right_cart_proj(X,Y)"}.\<close>
axiomatization
  fibered_product :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset" ("_ \<^bsub>_\<^esub>\<times>\<^sub>c\<^bsub>_\<^esub> _" [66,50,50,65]65) and
  fibered_product_morphism :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc"
where
  fibered_product_spec: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow>
    equalizer(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y), f \<circ>\<^sub>c left_cart_proj(X, Y), g \<circ>\<^sub>c right_cart_proj(X, Y))"

lemma fibered_product_morphism_equalizer:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  shows "equalizer(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y), f \<circ>\<^sub>c left_cart_proj(X, Y), g \<circ>\<^sub>c right_cart_proj(X, Y))"
  using fibered_product_spec[OF f_type g_type] by simp

lemma fibered_product_morphism_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  shows "fibered_product_morphism(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X \<times>\<^sub>c Y"
proof -
  have eq: "equalizer(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y), f \<circ>\<^sub>c left_cart_proj(X, Y), g \<circ>\<^sub>c right_cart_proj(X, Y))"
    using fibered_product_spec[OF f_type g_type] by simp
  have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Z" using lp_type f_type comp_type by blast
  obtain X' Y' where flp_type': "f \<circ>\<^sub>c left_cart_proj(X, Y) : X' \<rightarrow> Y'"
      and k_type': "fibered_product_morphism(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X'"
    using eq unfolding equalizer_def by auto
  have XX': "X' = X \<times>\<^sub>c Y" using flp_type flp_type' unfolding cfunc_type_def by auto
  show ?thesis using k_type' XX' by simp
qed

lemma fibered_product_morphism_monomorphism:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  shows "monomorphism(fibered_product_morphism(X, f, g, Y))"
  using equalizer_is_monomorphism[OF fibered_product_spec[OF f_type g_type]] by simp

definition fibered_product_left_proj :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_left_proj(X, f, g, Y) = left_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)"

lemma fibered_product_left_proj_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  shows "fibered_product_left_proj(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X"
  unfolding fibered_product_left_proj_def
  using left_cart_proj_type fibered_product_morphism_type[OF f_type g_type] comp_type by blast

definition fibered_product_right_proj :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_right_proj(X, f, g, Y) = right_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)"

lemma fibered_product_right_proj_type[type_rule]:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  shows "fibered_product_right_proj(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> Y"
  unfolding fibered_product_right_proj_def
  using right_cart_proj_type fibered_product_morphism_type[OF f_type g_type] comp_type by blast

lemma pair_factorsthru_fibered_product_morphism:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z" and x_type: "x : A \<rightarrow> X" and y_type: "y : A \<rightarrow> Y"
  shows "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y \<Longrightarrow> \<langle>x,y\<rangle> factorsthru fibered_product_morphism(X, f, g, Y)"
proof -
  assume fx_eq_gy: "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
  have eqlz: "equalizer(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y), f \<circ>\<^sub>c left_cart_proj(X, Y), g \<circ>\<^sub>c right_cart_proj(X, Y))"
    using fibered_product_spec[OF f_type g_type] by simp
  have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
  have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Z" using lp_type f_type comp_type by blast
  have grp_type: "g \<circ>\<^sub>c right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Z" using rp_type g_type comp_type by blast
  have xy_type: "\<langle>x,y\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
  have flp_xy_eq: "(f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>x,y\<rangle> = (g \<circ>\<^sub>c right_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>x,y\<rangle>"
  proof -
    have "(f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>x,y\<rangle> = f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>)"
      using comp_associative2[OF xy_type lp_type f_type] by simp
    also have "... = f \<circ>\<^sub>c x" using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
    also have "... = g \<circ>\<^sub>c y" using fx_eq_gy by simp
    also have "... = g \<circ>\<^sub>c (right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>)" using right_cart_proj_cfunc_prod[OF x_type y_type] by simp
    also have "... = (g \<circ>\<^sub>c right_cart_proj(X, Y)) \<circ>\<^sub>c \<langle>x,y\<rangle>" using comp_associative2[OF xy_type rp_type g_type] by simp
    finally show ?thesis by simp
  qed
  have ex1h: "\<exists>! h. h : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<and> fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    using similar_equalizers[OF flp_type grp_type fibered_product_morphism_type[OF f_type g_type] eqlz xy_type flp_xy_eq] by simp
  then obtain h where h_type: "h : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y)" and h_eq: "fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c h = \<langle>x,y\<rangle>" by auto
  show "\<langle>x,y\<rangle> factorsthru fibered_product_morphism(X, f, g, Y)"
    using factors_through_def2[OF xy_type fibered_product_morphism_type[OF f_type g_type]] h_type h_eq by auto
qed

lemma fibered_product_is_pullback:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  shows "is_pullback(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, Y, X, Z, fibered_product_right_proj(X, f, g, Y), g, fibered_product_left_proj(X, f, g, Y), f)"
  unfolding is_pullback_def
proof (intro conjI)
  show "fibered_product_right_proj(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> Y"
    using fibered_product_right_proj_type[OF f_type g_type] by simp
  show "g : Y \<rightarrow> Z" by (rule g_type)
  show "fibered_product_left_proj(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type g_type] by simp
  show "f : X \<rightarrow> Z" by (rule f_type)
  show "g \<circ>\<^sub>c fibered_product_right_proj(X, f, g, Y) = f \<circ>\<^sub>c fibered_product_left_proj(X, f, g, Y)"
  proof -
    have m_type: "fibered_product_morphism(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X \<times>\<^sub>c Y"
      using fibered_product_morphism_type[OF f_type g_type] by simp
    have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
    have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)
    have eqlz_eq: "f \<circ>\<^sub>c left_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)
        = g \<circ>\<^sub>c right_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)"
    proof -
      have eqlz: "equalizer(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y), f \<circ>\<^sub>c left_cart_proj(X, Y), g \<circ>\<^sub>c right_cart_proj(X, Y))"
        using fibered_product_spec[OF f_type g_type] by simp
      have flp_type: "f \<circ>\<^sub>c left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Z" using lp_type f_type comp_type by blast
      have grp_type: "g \<circ>\<^sub>c right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Z" using rp_type g_type comp_type by blast
      have bundled: "(f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)
          = (g \<circ>\<^sub>c right_cart_proj(X, Y)) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)"
        using equalizer_eq[OF flp_type grp_type m_type eqlz] by simp
      have l_assoc: "f \<circ>\<^sub>c left_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y) = (f \<circ>\<^sub>c left_cart_proj(X, Y)) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)"
        using comp_associative2[OF m_type lp_type f_type] by simp
      have r_assoc: "g \<circ>\<^sub>c right_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y) = (g \<circ>\<^sub>c right_cart_proj(X, Y)) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)"
        using comp_associative2[OF m_type rp_type g_type] by simp
      show ?thesis using bundled l_assoc r_assoc by simp
    qed
    have g_rp_eq: "g \<circ>\<^sub>c fibered_product_right_proj(X, f, g, Y) = g \<circ>\<^sub>c (right_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y))"
      unfolding fibered_product_right_proj_def by simp
    have f_lp_eq: "f \<circ>\<^sub>c fibered_product_left_proj(X, f, g, Y) = f \<circ>\<^sub>c (left_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y))"
      unfolding fibered_product_left_proj_def by simp
    show ?thesis using g_rp_eq f_lp_eq eqlz_eq by simp
  qed
  show "\<forall>A k h. k : A \<rightarrow> Y \<and> h : A \<rightarrow> X \<and> g \<circ>\<^sub>c k = f \<circ>\<^sub>c h \<longrightarrow>
      (\<exists>!j. j : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<and>
        fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c j = k \<and>
        fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c j = h)"
  proof (intro allI impI)
    fix A k h
    assume "k : A \<rightarrow> Y \<and> h : A \<rightarrow> X \<and> g \<circ>\<^sub>c k = f \<circ>\<^sub>c h"
    then have k_type: "k : A \<rightarrow> Y" and h_type: "h : A \<rightarrow> X" and gk_eq_fh: "g \<circ>\<^sub>c k = f \<circ>\<^sub>c h" by auto
    have fh_eq_gk: "f \<circ>\<^sub>c h = g \<circ>\<^sub>c k" using gk_eq_fh by simp
    have hk_factorsthru: "\<langle>h,k\<rangle> factorsthru fibered_product_morphism(X, f, g, Y)"
      using pair_factorsthru_fibered_product_morphism[OF f_type g_type h_type k_type fh_eq_gk] by simp
    have hk_type: "\<langle>h,k\<rangle> : A \<rightarrow> X \<times>\<^sub>c Y" using h_type k_type cfunc_prod_type by auto
    have m_type: "fibered_product_morphism(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X \<times>\<^sub>c Y"
      using fibered_product_morphism_type[OF f_type g_type] by simp
    obtain u where u_type: "u : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y)" and u_eq: "fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c u = \<langle>h,k\<rangle>"
      using factors_through_def2[OF hk_type m_type] hk_factorsthru by auto

    have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
    have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)

    have rpm_u_eq_k: "fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c u = k"
    proof -
      have "fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c u = (right_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)) \<circ>\<^sub>c u"
        unfolding fibered_product_right_proj_def by simp
      also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c u)"
        using comp_associative2[OF u_type m_type rp_type] by simp
      also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>h,k\<rangle>" using u_eq by simp
      also have "... = k" using right_cart_proj_cfunc_prod[OF h_type k_type] by simp
      finally show ?thesis by simp
    qed
    have lpm_u_eq_h: "fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c u = h"
    proof -
      have "fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c u = (left_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)) \<circ>\<^sub>c u"
        unfolding fibered_product_left_proj_def by simp
      also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c u)"
        using comp_associative2[OF u_type m_type lp_type] by simp
      also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>h,k\<rangle>" using u_eq by simp
      also have "... = h" using left_cart_proj_cfunc_prod[OF h_type k_type] by simp
      finally show ?thesis by simp
    qed

    show "\<exists>!j. j : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<and>
        fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c j = k \<and>
        fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c j = h"
    proof (rule ex1I[where a=u])
      show "u : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<and>
          fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c u = k \<and>
          fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c u = h"
        using u_type rpm_u_eq_k lpm_u_eq_h by simp
    next
      fix y
      assume "y : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<and>
          fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c y = k \<and>
          fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c y = h"
      then have y_type: "y : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y)"
          and rpm_y_eq_k: "fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c y = k"
          and lpm_y_eq_h: "fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c y = h" by auto
      have my_eq_hk: "fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y = \<langle>h,k\<rangle>"
      proof -
        have my_type: "fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y : A \<rightarrow> X \<times>\<^sub>c Y" using m_type y_type comp_type by blast
        have lp_my: "left_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y) = h"
        proof -
          have "left_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y) = (left_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)) \<circ>\<^sub>c y"
            using comp_associative2[OF y_type m_type lp_type] by simp
          also have "... = fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c y" unfolding fibered_product_left_proj_def by simp
          also have "... = h" using lpm_y_eq_h by simp
          finally show ?thesis by simp
        qed
        have rp_my: "right_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y) = k"
        proof -
          have "right_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y) = (right_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)) \<circ>\<^sub>c y"
            using comp_associative2[OF y_type m_type rp_type] by simp
          also have "... = fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c y" unfolding fibered_product_right_proj_def by simp
          also have "... = k" using rpm_y_eq_k by simp
          finally show ?thesis by simp
        qed
        show ?thesis using cfunc_prod_unique[OF h_type k_type my_type lp_my rp_my] by simp
      qed
      have m_mono: "monomorphism(fibered_product_morphism(X, f, g, Y))"
        using fibered_product_morphism_monomorphism[OF f_type g_type] by simp
      have mono_prop: "\<forall>y' u'. y' : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<and> u' : A \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<longrightarrow>
          (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y' = fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c u' \<longrightarrow> y' = u')"
        using m_mono monomorphism_def3[OF m_type] by auto
      have my_eq_mu: "fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c y = fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c u"
        using my_eq_hk u_eq by simp
      show "y = u" using mono_prop[rule_format] y_type u_type my_eq_mu by auto
    qed
  qed
qed

lemma fibered_product_proj_eq:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z"
  shows "f \<circ>\<^sub>c fibered_product_left_proj(X, f, g, Y) = g \<circ>\<^sub>c fibered_product_right_proj(X, f, g, Y)"
  using fibered_product_is_pullback[OF f_type g_type] unfolding is_pullback_def by auto

lemma fibered_product_pair_member:
  assumes f_type: "f : X \<rightarrow> Z" and g_type: "g : Y \<rightarrow> Z" and x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c Y"
  shows "relative_member(\<langle>x, y\<rangle>, X \<times>\<^sub>c Y, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y)) \<longleftrightarrow> (f \<circ>\<^sub>c x = g \<circ>\<^sub>c y)"
proof -
  have xy_type: "\<langle>x, y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y" using x_type y_type cfunc_prod_type by auto
  have m_type: "fibered_product_morphism(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X \<times>\<^sub>c Y"
    using fibered_product_morphism_type[OF f_type g_type] by simp
  show ?thesis
  proof (rule iffI)
    assume "relative_member(\<langle>x, y\<rangle>, X \<times>\<^sub>c Y, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y))"
    then have xy_factorsthru: "\<langle>x,y\<rangle> factorsthru fibered_product_morphism(X, f, g, Y)" unfolding relative_member_def by auto
    obtain h where h_type: "h : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y)" and h_eq: "fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
      using factors_through_def2[OF xy_type m_type] xy_factorsthru by auto

    have lp_type: "left_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> X" by (rule left_cart_proj_type)
    have rp_type: "right_cart_proj(X, Y) : X \<times>\<^sub>c Y \<rightarrow> Y" by (rule right_cart_proj_type)

    have left_eq: "fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c h = x"
    proof -
      have "fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c h = (left_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)) \<circ>\<^sub>c h"
        unfolding fibered_product_left_proj_def by simp
      also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c h)"
        using comp_associative2[OF h_type m_type lp_type] by simp
      also have "... = left_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>" using h_eq by simp
      also have "... = x" using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
      finally show ?thesis by simp
    qed
    have right_eq: "fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c h = y"
    proof -
      have "fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c h = (right_cart_proj(X, Y) \<circ>\<^sub>c fibered_product_morphism(X, f, g, Y)) \<circ>\<^sub>c h"
        unfolding fibered_product_right_proj_def by simp
      also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c (fibered_product_morphism(X, f, g, Y) \<circ>\<^sub>c h)"
        using comp_associative2[OF h_type m_type rp_type] by simp
      also have "... = right_cart_proj(X, Y) \<circ>\<^sub>c \<langle>x,y\<rangle>" using h_eq by simp
      also have "... = y" using right_cart_proj_cfunc_prod[OF x_type y_type] by simp
      finally show ?thesis by simp
    qed

    have lp_h_type: "fibered_product_left_proj(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> X"
      using fibered_product_left_proj_type[OF f_type g_type] by simp
    have rp_h_type: "fibered_product_right_proj(X, f, g, Y) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) \<rightarrow> Y"
      using fibered_product_right_proj_type[OF f_type g_type] by simp

    have "f \<circ>\<^sub>c (fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c h) = g \<circ>\<^sub>c (fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c h)"
    proof -
      have "f \<circ>\<^sub>c (fibered_product_left_proj(X, f, g, Y) \<circ>\<^sub>c h) = (f \<circ>\<^sub>c fibered_product_left_proj(X, f, g, Y)) \<circ>\<^sub>c h"
        using comp_associative2[OF h_type lp_h_type f_type] by simp
      also have "... = (g \<circ>\<^sub>c fibered_product_right_proj(X, f, g, Y)) \<circ>\<^sub>c h"
        using fibered_product_proj_eq[OF f_type g_type] by simp
      also have "... = g \<circ>\<^sub>c (fibered_product_right_proj(X, f, g, Y) \<circ>\<^sub>c h)"
        using comp_associative2[OF h_type rp_h_type g_type] by simp
      finally show ?thesis by simp
    qed
    then show "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y" using left_eq right_eq by simp
  next
    assume f_g_eq: "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    have xy_factorsthru: "\<langle>x,y\<rangle> factorsthru fibered_product_morphism(X, f, g, Y)"
      using pair_factorsthru_fibered_product_morphism[OF f_type g_type x_type y_type f_g_eq] by simp
    show "relative_member(\<langle>x, y\<rangle>, X \<times>\<^sub>c Y, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism(X, f, g, Y))"
      unfolding relative_member_def
      using xy_type fibered_product_morphism_monomorphism[OF f_type g_type] m_type xy_factorsthru by auto
  qed
qed

lemma fibered_product_pair_member2:
  assumes f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> E"
  assumes eqcond: "g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
  shows "\<forall>x y. x \<in>\<^sub>c X \<longrightarrow> y \<in>\<^sub>c X \<longrightarrow>
    relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X)) \<longrightarrow> g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
proof (intro allI impI)
  fix x y
  assume x_type: "x \<in>\<^sub>c X"
  assume y_type: "y \<in>\<^sub>c X"
  assume a3: "relative_member(\<langle>x,y\<rangle>, X \<times>\<^sub>c X, X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X))"
  have xy_type: "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X" using x_type y_type cfunc_prod_type by auto
  have m_type: "fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<times>\<^sub>c X"
    using fibered_product_morphism_type[OF f_type f_type] by simp
  have "\<langle>x,y\<rangle> factorsthru fibered_product_morphism(X, f, f, X)" using a3 unfolding relative_member_def by auto
  then obtain h where h_type: "h : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)" and h_eq: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    using factors_through_def2[OF xy_type m_type] by auto

  have lp_type: "left_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)

  have left_eq: "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c h = x"
  proof -
    have "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c h = (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c h"
      unfolding fibered_product_left_proj_def by simp
    also have "... = left_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c h)"
      using comp_associative2[OF h_type m_type lp_type] by simp
    also have "... = left_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,y\<rangle>" using h_eq by simp
    also have "... = x" using left_cart_proj_cfunc_prod[OF x_type y_type] by simp
    finally show ?thesis by simp
  qed
  have right_eq: "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c h = y"
  proof -
    have "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c h = (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c h"
      unfolding fibered_product_right_proj_def by simp
    also have "... = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c h)"
      using comp_associative2[OF h_type m_type rp_type] by simp
    also have "... = right_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,y\<rangle>" using h_eq by simp
    also have "... = y" using right_cart_proj_cfunc_prod[OF x_type y_type] by simp
    finally show ?thesis by simp
  qed

  have lp_h_type: "fibered_product_left_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type f_type] by simp
  have rp_h_type: "fibered_product_right_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_right_proj_type[OF f_type f_type] by simp

  have "g \<circ>\<^sub>c (fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c h) = g \<circ>\<^sub>c (fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c h)"
  proof -
    have "g \<circ>\<^sub>c (fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c h) = (g \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)) \<circ>\<^sub>c h"
      using comp_associative2[OF h_type lp_h_type g_type] by simp
    also have "... = (g \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)) \<circ>\<^sub>c h" using eqcond by simp
    also have "... = g \<circ>\<^sub>c (fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c h)"
      using comp_associative2[OF h_type rp_h_type g_type] by simp
    finally show ?thesis by simp
  qed
  then show "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y" using left_eq right_eq by simp
qed

lemma kernel_pair_subset:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "subobject_of(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism(X, f, f, X), X \<times>\<^sub>c X)"
  unfolding subobject_of_def
  using fibered_product_morphism_type[OF f_type f_type] fibered_product_morphism_monomorphism[OF f_type f_type] by simp

text \<open>The three lemmas below correspond to Exercise 2.1.44 in Halvorson.\<close>
lemma kern_pair_proj_iso_TFAE1:
  assumes f_type: "f : X \<rightarrow> Y" and f_mono: "monomorphism(f)"
  shows "fibered_product_left_proj(X, f, f, X) = fibered_product_right_proj(X, f, f, X)"
proof -
  have lp_type: "fibered_product_left_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type f_type] by simp
  have rp_type: "fibered_product_right_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_right_proj_type[OF f_type f_type] by simp
  have f_lp_eq_f_rp: "f \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = f \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
    using fibered_product_proj_eq[OF f_type f_type] by simp
  have mono_prop: "\<forall>a b. a : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<and> b : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c a = f \<circ>\<^sub>c b \<longrightarrow> a = b)"
    using f_mono monomorphism_def3[OF f_type] by auto
  show ?thesis using mono_prop[rule_format] lp_type rp_type f_lp_eq_f_rp by auto
qed

lemma kern_pair_proj_iso_TFAE2:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes eq_projs: "fibered_product_left_proj(X, f, f, X) = fibered_product_right_proj(X, f, f, X)"
  shows "monomorphism(f) \<and> isomorphism(fibered_product_left_proj(X, f, f, X)) \<and> isomorphism(fibered_product_right_proj(X, f, f, X))"
proof -
  have f_inj: "injective(f)"
    unfolding injective_def
  proof (intro allI impI)
    fix x y
    assume "x \<in>\<^sub>c domain(f) \<and> y \<in>\<^sub>c domain(f) \<and> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    then have x_type: "x \<in>\<^sub>c domain(f)" and y_type: "y \<in>\<^sub>c domain(f)" and fx_eq_fy: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y" by auto
    have dom_f: "domain(f) = X" using f_type unfolding cfunc_type_def by auto
    have x_type2: "x \<in>\<^sub>c X" using x_type dom_f by simp
    have y_type2: "y \<in>\<^sub>c X" using y_type dom_f by simp
    have xy_type: "\<langle>x,y\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c X" using x_type2 y_type2 cfunc_prod_type by auto
    have m_type: "fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<times>\<^sub>c X"
      using fibered_product_morphism_type[OF f_type f_type] by simp
    have xy_factorsthru: "\<langle>x,y\<rangle> factorsthru fibered_product_morphism(X, f, f, X)"
      using pair_factorsthru_fibered_product_morphism[OF f_type f_type x_type2 y_type2 fx_eq_fy] by simp
    obtain xy0 where xy0_type: "xy0 : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)" and xy0_eq: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xy0 = \<langle>x,y\<rangle>"
      using factors_through_def2[OF xy_type m_type] xy_factorsthru by auto

    have lp_type: "left_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule left_cart_proj_type)
    have rp_type: "right_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)

    have left_proj: "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c xy0 = x"
    proof -
      have "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c xy0 = (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c xy0"
        unfolding fibered_product_left_proj_def by simp
      also have "... = left_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xy0)"
        using comp_associative2[OF xy0_type m_type lp_type] by simp
      also have "... = left_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,y\<rangle>" using xy0_eq by simp
      also have "... = x" using left_cart_proj_cfunc_prod[OF x_type2 y_type2] by simp
      finally show ?thesis by simp
    qed
    have right_proj: "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xy0 = y"
    proof -
      have "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xy0 = (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c xy0"
        unfolding fibered_product_right_proj_def by simp
      also have "... = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xy0)"
        using comp_associative2[OF xy0_type m_type rp_type] by simp
      also have "... = right_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,y\<rangle>" using xy0_eq by simp
      also have "... = y" using right_cart_proj_cfunc_prod[OF x_type2 y_type2] by simp
      finally show ?thesis by simp
    qed
    show "x = y" using eq_projs left_proj right_proj by simp
  qed
  have f_mono: "monomorphism(f)" using f_inj injective_imp_monomorphism by simp

  have idX_type: "id(X) : X \<rightarrow> X" by (rule id_type)
  have diag_factorsthru: "diagonal(X) factorsthru fibered_product_morphism(X, f, f, X)"
  proof -
    have ffid: "f \<circ>\<^sub>c id(X) = f \<circ>\<^sub>c id(X)" by simp
    have "\<langle>id(X), id(X)\<rangle> factorsthru fibered_product_morphism(X, f, f, X)"
      using pair_factorsthru_fibered_product_morphism[OF f_type f_type idX_type idX_type ffid] by simp
    then show ?thesis unfolding diagonal_def by simp
  qed
  have diagX_type: "diagonal(X) : X \<rightarrow> X \<times>\<^sub>c X" by (rule diagonal_type)
  have m_type: "fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<times>\<^sub>c X"
    using fibered_product_morphism_type[OF f_type f_type] by simp
  obtain xx where xx_type: "xx : X \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)" and xx_eq: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xx = diagonal(X)"
    using factors_through_def2[OF diagX_type m_type] diag_factorsthru by auto

  have lp_type: "left_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule left_cart_proj_type)
  have rp_type: "right_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)
  have lp_h_type: "fibered_product_left_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type f_type] by simp
  have rp_h_type: "fibered_product_right_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_right_proj_type[OF f_type f_type] by simp

  have eq1: "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xx = id(X)"
  proof -
    have "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xx = (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c xx"
      unfolding fibered_product_right_proj_def by simp
    also have "... = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xx)"
      using comp_associative2[OF xx_type m_type rp_type] by simp
    also have "... = right_cart_proj(X, X) \<circ>\<^sub>c diagonal(X)" using xx_eq by simp
    also have "... = right_cart_proj(X, X) \<circ>\<^sub>c \<langle>id(X), id(X)\<rangle>" unfolding diagonal_def by simp
    also have "... = id(X)" using right_cart_proj_cfunc_prod[OF idX_type idX_type] by simp
    finally show ?thesis by simp
  qed

  have eq2: "xx \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) = id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
  proof (rule one_separator)
    show "xx \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
      using xx_type rp_h_type comp_type by blast
    show "id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)" by (rule id_type)
    fix z
    assume z_type: "z : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    have mz_type: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z : \<one> \<rightarrow> X \<times>\<^sub>c X" using m_type z_type comp_type by blast

    have lp_mz_eq_rp_mz: "left_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z) = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z)"
    proof -
      have "left_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z) = (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c z"
        using comp_associative2[OF z_type m_type lp_type] by simp
      also have "... = fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c z" unfolding fibered_product_left_proj_def by simp
      also have "... = fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c z" using eq_projs by simp
      also have "... = (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c z" unfolding fibered_product_right_proj_def by simp
      also have "... = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z)"
        using comp_associative2[OF z_type m_type rp_type] by simp
      finally show ?thesis by simp
    qed

    obtain a b where mz_decomp: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z = \<langle>a,b\<rangle>" and a_type: "a \<in>\<^sub>c X" and b_type: "b \<in>\<^sub>c X"
      using cart_prod_decomp[OF mz_type] by blast
    have a_eq_b: "a = b"
    proof -
      have "left_cart_proj(X, X) \<circ>\<^sub>c \<langle>a,b\<rangle> = right_cart_proj(X, X) \<circ>\<^sub>c \<langle>a,b\<rangle>" using lp_mz_eq_rp_mz mz_decomp by simp
      then show ?thesis using left_cart_proj_cfunc_prod[OF a_type b_type] right_cart_proj_cfunc_prod[OF a_type b_type] by simp
    qed
    have mz_eq_diag_a: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z = diagonal(X) \<circ>\<^sub>c a"
    proof -
      have "diagonal(X) \<circ>\<^sub>c a = \<langle>a,a\<rangle>" using diag_on_elements[OF a_type] by simp
      then show ?thesis using mz_decomp a_eq_b by simp
    qed
    have mz_eq_mxxa: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z = fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c (xx \<circ>\<^sub>c a)"
    proof -
      have "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c (xx \<circ>\<^sub>c a) = (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xx) \<circ>\<^sub>c a"
        using comp_associative2[OF a_type xx_type m_type] by simp
      also have "... = diagonal(X) \<circ>\<^sub>c a" using xx_eq by simp
      finally show ?thesis using mz_eq_diag_a by simp
    qed
    have m_mono: "monomorphism(fibered_product_morphism(X, f, f, X))"
      using fibered_product_morphism_monomorphism[OF f_type f_type] by simp
    have xxa_type: "xx \<circ>\<^sub>c a : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)" using xx_type a_type comp_type by blast
    have mono_prop: "\<forall>p q. p : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<and> q : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<longrightarrow>
        (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c p = fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c q \<longrightarrow> p = q)"
      using m_mono monomorphism_def3[OF m_type] by auto
    have z_eq_xxa: "z = xx \<circ>\<^sub>c a" using mono_prop[rule_format] z_type xxa_type mz_eq_mxxa by auto

    have "(xx \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)) \<circ>\<^sub>c z = xx \<circ>\<^sub>c (fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c z)"
      using comp_associative2[OF z_type rp_h_type xx_type] by simp
    also have "... = xx \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z))"
    proof -
      have "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c z = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z)"
      proof -
        have "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c z = (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c z"
          unfolding fibered_product_right_proj_def by simp
        also have "... = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c z)"
          using comp_associative2[OF z_type m_type rp_type] by simp
        finally show ?thesis by simp
      qed
      then show ?thesis by simp
    qed
    also have "... = xx \<circ>\<^sub>c (right_cart_proj(X, X) \<circ>\<^sub>c \<langle>a,b\<rangle>)" using mz_decomp by simp
    also have "... = xx \<circ>\<^sub>c b" using right_cart_proj_cfunc_prod[OF a_type b_type] by simp
    also have "... = xx \<circ>\<^sub>c a" using a_eq_b by simp
    also have "... = z" using z_eq_xxa by simp
    also have "... = id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c z" using id_left_unit2[OF z_type] by simp
    finally show "(xx \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)) \<circ>\<^sub>c z = id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c z" by simp
  qed

  have iso_right: "isomorphism(fibered_product_right_proj(X, f, f, X))"
    unfolding isomorphism_def
  proof (intro exI[where x=xx])
    have d_rp: "domain(fibered_product_right_proj(X, f, f, X)) = X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" using rp_h_type unfolding cfunc_type_def by auto
    have c_rp: "codomain(fibered_product_right_proj(X, f, f, X)) = X" using rp_h_type unfolding cfunc_type_def by auto
    have d_xx: "domain(xx) = X" using xx_type unfolding cfunc_type_def by auto
    have c_xx: "codomain(xx) = X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" using xx_type unfolding cfunc_type_def by auto
    show "domain(xx) = codomain(fibered_product_right_proj(X, f, f, X)) \<and>
        codomain(xx) = domain(fibered_product_right_proj(X, f, f, X)) \<and>
        xx \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) = id(domain(fibered_product_right_proj(X, f, f, X))) \<and>
        fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xx = id(domain(xx))"
      using d_rp c_rp d_xx c_xx eq1 eq2 by simp
  qed
  have iso_left: "isomorphism(fibered_product_left_proj(X, f, f, X))" using iso_right eq_projs by simp

  show ?thesis using f_mono iso_left iso_right by simp
qed

lemma kern_pair_proj_iso_TFAE3:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes iso_left: "isomorphism(fibered_product_left_proj(X, f, f, X))"
  assumes iso_right: "isomorphism(fibered_product_right_proj(X, f, f, X))"
  shows "fibered_product_left_proj(X, f, f, X) = fibered_product_right_proj(X, f, f, X)"
proof -
  have lp_type: "fibered_product_left_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_left_proj_type[OF f_type f_type] by simp
  have rp_type: "fibered_product_right_proj(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X"
    using fibered_product_right_proj_type[OF f_type f_type] by simp

  have q0_inv_type: "(fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> : X \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using inverse_type[OF iso_left lp_type] by simp
  have q0_left: "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c (fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> = id(X)"
    using inv_right[OF iso_left lp_type] by simp
  have q0_right: "(fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X) = id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using inv_left[OF iso_left lp_type] by simp

  have q1_inv_type: "(fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> : X \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using inverse_type[OF iso_right rp_type] by simp
  have q1_right: "(fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X) = id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using inv_left[OF iso_right rp_type] by simp

  have meta: "\<And>x. x : \<one> \<rightarrow> X \<Longrightarrow>
      (fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x = (fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x"
  proof -
    fix x assume x_type: "x : \<one> \<rightarrow> X"
    have fxfx: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c x" by simp
    have xx_factorsthru: "\<langle>x,x\<rangle> factorsthru fibered_product_morphism(X, f, f, X)"
      using pair_factorsthru_fibered_product_morphism[OF f_type f_type x_type x_type fxfx] by simp
    have xx_type2: "\<langle>x,x\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c X" using x_type cfunc_prod_type by auto
    have m_type: "fibered_product_morphism(X, f, f, X) : (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<rightarrow> X \<times>\<^sub>c X"
      using fibered_product_morphism_type[OF f_type f_type] by simp
    obtain xx0 where xx0_type: "xx0 : \<one> \<rightarrow> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)" and xx0_eq: "fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xx0 = \<langle>x,x\<rangle>"
      using factors_through_def2[OF xx_type2 m_type] xx_factorsthru by auto

    have lpX_type: "left_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule left_cart_proj_type)
    have rpX_type: "right_cart_proj(X, X) : X \<times>\<^sub>c X \<rightarrow> X" by (rule right_cart_proj_type)

    have lp_xx0_eq_x: "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c xx0 = x"
    proof -
      have "fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c xx0 = (left_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c xx0"
        unfolding fibered_product_left_proj_def by simp
      also have "... = left_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xx0)"
        using comp_associative2[OF xx0_type m_type lpX_type] by simp
      also have "... = left_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,x\<rangle>" using xx0_eq by simp
      also have "... = x" using left_cart_proj_cfunc_prod[OF x_type x_type] by simp
      finally show ?thesis by simp
    qed
    have rp_xx0_eq_x: "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xx0 = x"
    proof -
      have "fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xx0 = (right_cart_proj(X, X) \<circ>\<^sub>c fibered_product_morphism(X, f, f, X)) \<circ>\<^sub>c xx0"
        unfolding fibered_product_right_proj_def by simp
      also have "... = right_cart_proj(X, X) \<circ>\<^sub>c (fibered_product_morphism(X, f, f, X) \<circ>\<^sub>c xx0)"
        using comp_associative2[OF xx0_type m_type rpX_type] by simp
      also have "... = right_cart_proj(X, X) \<circ>\<^sub>c \<langle>x,x\<rangle>" using xx0_eq by simp
      also have "... = x" using right_cart_proj_cfunc_prod[OF x_type x_type] by simp
      finally show ?thesis by simp
    qed

    have inv_lp_x_eq_xx0: "(fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x = xx0"
    proof -
      have "(fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x = (fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c (fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c xx0)"
        using lp_xx0_eq_x by simp
      also have "... = ((fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c fibered_product_left_proj(X, f, f, X)) \<circ>\<^sub>c xx0"
        using comp_associative2[OF xx0_type lp_type q0_inv_type] by simp
      also have "... = id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c xx0" using q0_right by simp
      also have "... = xx0" using id_left_unit2[OF xx0_type] by simp
      finally show ?thesis by simp
    qed
    have inv_rp_x_eq_xx0: "(fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x = xx0"
    proof -
      have "(fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x = (fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c (fibered_product_right_proj(X, f, f, X) \<circ>\<^sub>c xx0)"
        using rp_xx0_eq_x by simp
      also have "... = ((fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)) \<circ>\<^sub>c xx0"
        using comp_associative2[OF xx0_type rp_type q1_inv_type] by simp
      also have "... = id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c xx0" using q1_right by simp
      also have "... = xx0" using id_left_unit2[OF xx0_type] by simp
      finally show ?thesis by simp
    qed
    show "(fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x = (fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c x"
      using inv_lp_x_eq_xx0 inv_rp_x_eq_xx0 by simp
  qed

  have q0_eq_q1: "(fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> = (fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse>"
    using q0_inv_type q1_inv_type meta by (rule one_separator)

  show ?thesis
  proof -
    have "fibered_product_left_proj(X, f, f, X) = fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c id(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
      using id_right_unit2[OF lp_type] by simp
    also have "... = fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c ((fibered_product_right_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X))"
      using q1_right by simp
    also have "... = fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c ((fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse> \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X))"
      using q0_eq_q1 by simp
    also have "... = (fibered_product_left_proj(X, f, f, X) \<circ>\<^sub>c (fibered_product_left_proj(X, f, f, X))\<^bold>\<inverse>) \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)"
      using comp_associative2[OF rp_type q0_inv_type lp_type] by simp
    also have "... = id(X) \<circ>\<^sub>c fibered_product_right_proj(X, f, f, X)" using q0_left by simp
    also have "... = fibered_product_right_proj(X, f, f, X)" using id_left_unit2[OF rp_type] by simp
    finally show ?thesis by simp
  qed
qed

lemma terminal_fib_prod_iso:
  assumes term_T: "terminal_object(T)"
  assumes f_type: "f : Y \<rightarrow> T"
  assumes g_type: "g : X \<rightarrow> T"
  shows "(X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) \<cong> X \<times>\<^sub>c Y"
proof -
  have pb: "is_pullback(X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y, Y, X, T, fibered_product_right_proj(X, g, f, Y), f, fibered_product_left_proj(X, g, f, Y), g)"
    using fibered_product_is_pullback[OF g_type f_type] by simp
  have cp: "is_cart_prod(X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y, fibered_product_left_proj(X, g, f, Y), fibered_product_right_proj(X, g, f, Y), X, Y)"
    using pb pullback_iff_product[OF term_T f_type g_type] by auto
  have cp2: "is_cart_prod(X \<times>\<^sub>c Y, left_cart_proj(X, Y), right_cart_proj(X, Y), X, Y)"
    by (rule canonical_cart_prod_is_cart_prod)
  obtain k where k_def: "k : (X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) \<rightarrow> X \<times>\<^sub>c Y \<and> isomorphism(k) \<and> left_cart_proj(X, Y) \<circ>\<^sub>c k = fibered_product_left_proj(X, g, f, Y) \<and> right_cart_proj(X, Y) \<circ>\<^sub>c k = fibered_product_right_proj(X, g, f, Y)"
    using cart_prods_isomorphic[OF cp cp2] by blast
  show ?thesis unfolding is_isomorphic_def using k_def by auto
qed

end
