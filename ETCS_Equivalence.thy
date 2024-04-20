theory ETCS_Equivalence
  imports ETCS_Truth
begin

section  \<open>Axiom 6: Equivalence Classes\<close>

(* discussion at the top of page 42 *)
lemma kernel_pair_connection:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y" and g_type[type_rule]: "g : X \<rightarrow> E"
  assumes g_epi: "epimorphism g"
  assumes h_g_eq_f: "h \<circ>\<^sub>c g = f"
  assumes g_eq: "g \<circ>\<^sub>c fibered_product_left_proj X f f X = g \<circ>\<^sub>c fibered_product_right_proj X f f X "
  assumes h_type[type_rule]: "h : E \<rightarrow> Y"
  shows "\<exists>! b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and>
    fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
    fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
    epimorphism b"
proof -
  have gxg_fpmorph_eq: "(h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X
        = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
  proof -
    have "(h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X
        = h \<circ>\<^sub>c (left_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g)) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c left_cart_proj X X) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
    also have "... = (h \<circ>\<^sub>c g) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... = f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (simp add: h_g_eq_f)
    also have "... = f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      using f_type fibered_product_left_proj_def fibered_product_proj_eq fibered_product_right_proj_def by auto
    also have "... = (h \<circ>\<^sub>c g) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (simp add: h_g_eq_f)
    also have "... = h \<circ>\<^sub>c (g \<circ>\<^sub>c right_cart_proj X X) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, smt comp_associative2)
    also have "... = h \<circ>\<^sub>c right_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
    also have "... = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
      by (typecheck_cfuncs, smt comp_associative2)
    then show ?thesis
      using calculation by auto
  qed
  have h_equalizer: "equalizer (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) (fibered_product_morphism E h h E) (h \<circ>\<^sub>c left_cart_proj E E) (h \<circ>\<^sub>c right_cart_proj E E)"
    using fibered_product_morphism_equalizer h_type by auto
  then have "\<forall>j F. j : F \<rightarrow> E \<times>\<^sub>c E \<and> (h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c j = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c j \<longrightarrow>
               (\<exists>!k. k : F \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and> fibered_product_morphism E h h E \<circ>\<^sub>c k = j)"
    unfolding equalizer_def using cfunc_type_def fibered_product_morphism_type h_type by (smt (verit))
  then have "(g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X  : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<times>\<^sub>c E \<and> (h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X = (h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X \<longrightarrow>
               (\<exists>!k. k : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and> fibered_product_morphism E h h E \<circ>\<^sub>c k = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X)"
    by auto
  then obtain b where b_type[type_rule]: "b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E"
          and b_eq: "fibered_product_morphism E h h E \<circ>\<^sub>c b = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
    by (meson cfunc_cross_prod_type comp_type f_type fibered_product_morphism_type g_type gxg_fpmorph_eq)
      
  have "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) (X \<times>\<^sub>c X) (E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E) (E \<times>\<^sub>c E)
      (fibered_product_morphism X f f X) (g \<times>\<^sub>f g) b (fibered_product_morphism E h h E)"
  proof (insert b_eq, unfold is_pullback_def square_commutes_def, typecheck_cfuncs, clarify)
    fix Z k j

    assume k_type[type_rule]: "k : Z \<rightarrow> X \<times>\<^sub>c X" and h_type[type_rule]: "j : Z \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E"

    assume k_h_eq: "(g \<times>\<^sub>f g) \<circ>\<^sub>c k = fibered_product_morphism E h h E \<circ>\<^sub>c j"

    have left_k_right_k_eq: "f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k = f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k"
    proof -
      have "f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k = h \<circ>\<^sub>c g \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k"
        by (smt (z3) assms(6) comp_associative2 comp_type g_type h_g_eq_f k_type left_cart_proj_type)
      also have "... = h \<circ>\<^sub>c left_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c k"
        by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
      also have "... = h \<circ>\<^sub>c left_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c j"
        by (simp add: k_h_eq)
      also have "... = ((h \<circ>\<^sub>c left_cart_proj E E) \<circ>\<^sub>c fibered_product_morphism E h h E) \<circ>\<^sub>c j"
        by (typecheck_cfuncs, smt comp_associative2)
      also have "... = ((h \<circ>\<^sub>c right_cart_proj E E) \<circ>\<^sub>c fibered_product_morphism E h h E) \<circ>\<^sub>c j"
        using equalizer_def h_equalizer by auto
      also have "... = h \<circ>\<^sub>c right_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c j"
        by (typecheck_cfuncs, smt comp_associative2)
      also have "... = h \<circ>\<^sub>c right_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c k"
        by (simp add: k_h_eq)
      also have "... = h \<circ>\<^sub>c g \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k"
        by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
      also have "... = f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k"
        using assms(6) comp_associative2 comp_type g_type h_g_eq_f k_type right_cart_proj_type by blast
      then show ?thesis
        using calculation by auto
    qed

    have "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) X X Y
        (fibered_product_right_proj X f f X) f (fibered_product_left_proj X f f X) f"
      by (simp add: f_type fibered_product_is_pullback)
    then have "right_cart_proj X X \<circ>\<^sub>c k : Z \<rightarrow> X \<Longrightarrow> left_cart_proj X X \<circ>\<^sub>c k : Z \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c k = f \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c k \<Longrightarrow>
      (\<exists>!j. j : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and>
        fibered_product_right_proj X f f X \<circ>\<^sub>c j = right_cart_proj X X \<circ>\<^sub>c k
        \<and> fibered_product_left_proj X f f X \<circ>\<^sub>c j = left_cart_proj X X \<circ>\<^sub>c k)"
      unfolding is_pullback_def by auto
    then obtain z where z_type[type_rule]: "z : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
        and k_right_eq: "fibered_product_right_proj X f f X \<circ>\<^sub>c z = right_cart_proj X X \<circ>\<^sub>c k" 
        and k_left_eq: "fibered_product_left_proj X f f X \<circ>\<^sub>c z = left_cart_proj X X \<circ>\<^sub>c k"
        and z_unique: "\<And>j. j : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X 
          \<and> fibered_product_right_proj X f f X \<circ>\<^sub>c j = right_cart_proj X X \<circ>\<^sub>c k
          \<and> fibered_product_left_proj X f f X \<circ>\<^sub>c j = left_cart_proj X X \<circ>\<^sub>c k \<Longrightarrow> z = j"
      using left_k_right_k_eq by (typecheck_cfuncs, auto)

    have k_eq: "fibered_product_morphism X f f X \<circ>\<^sub>c z = k"
      using k_right_eq k_left_eq
      unfolding fibered_product_right_proj_def fibered_product_left_proj_def
      by (typecheck_cfuncs_prems, smt cfunc_prod_comp cfunc_prod_unique)

    show "\<exists>!l. l : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and> fibered_product_morphism X f f X \<circ>\<^sub>c l = k \<and> b \<circ>\<^sub>c l = j"
    proof auto
      show "\<exists>l. l : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<and> fibered_product_morphism X f f X \<circ>\<^sub>c l = k \<and> b \<circ>\<^sub>c l = j"
      proof (rule_tac x=z in exI, auto simp add: k_eq z_type)
        have "fibered_product_morphism E h h E \<circ>\<^sub>c j = (g \<times>\<^sub>f g) \<circ>\<^sub>c k"
          by (simp add: k_h_eq)
        also have "... = (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X \<circ>\<^sub>c z"
          by (simp add: k_eq)
        also have "... = fibered_product_morphism E h h E \<circ>\<^sub>c b \<circ>\<^sub>c z"
          by (typecheck_cfuncs, simp add: b_eq comp_associative2)
        then show "b \<circ>\<^sub>c z = j"
          using assms(6) calculation cfunc_type_def fibered_product_morphism_monomorphism fibered_product_morphism_type h_type monomorphism_def
          by (typecheck_cfuncs, auto)
      qed
    next
      fix j y
      assume j_type[type_rule]: "j : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" and y_type[type_rule]: "y : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"

      assume "fibered_product_morphism X f f X \<circ>\<^sub>c y = fibered_product_morphism X f f X \<circ>\<^sub>c j"
      then show "j = y"
        using fibered_product_morphism_monomorphism fibered_product_morphism_type monomorphism_def cfunc_type_def f_type
        by (typecheck_cfuncs, auto)
    qed
  qed
  then have b_epi: "epimorphism b"
    using g_epi g_type cfunc_cross_prod_type product_of_epis_is_epi pullback_of_epi_is_epi1 h_type
    by blast

  have existence: "\<exists>b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and>
        fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
        fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
        epimorphism b"
  proof (rule_tac x=b in exI, auto)
    show "b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E"
      by (typecheck_cfuncs)
    show "fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X"
    proof -
      thm b_eq fibered_product_left_proj_def
      have "fibered_product_left_proj E h h E \<circ>\<^sub>c b
          = left_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c b"
        unfolding fibered_product_left_proj_def by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = left_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (simp add: b_eq)
      also have "... = g \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
      also have "... = g \<circ>\<^sub>c fibered_product_left_proj X f f X"
        unfolding fibered_product_left_proj_def by (typecheck_cfuncs)
      then show ?thesis
        using calculation by auto
    qed
    show "fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X"
    proof -
      thm b_eq fibered_product_right_proj_def
      have "fibered_product_right_proj E h h E \<circ>\<^sub>c b
          = right_cart_proj E E \<circ>\<^sub>c fibered_product_morphism E h h E \<circ>\<^sub>c b"
        unfolding fibered_product_right_proj_def by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = right_cart_proj E E \<circ>\<^sub>c (g \<times>\<^sub>f g) \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (simp add: b_eq)
      also have "... = g \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c fibered_product_morphism X f f X"
        by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
      also have "... = g \<circ>\<^sub>c fibered_product_right_proj X f f X"
        unfolding fibered_product_right_proj_def by (typecheck_cfuncs)
      then show ?thesis
        using calculation by auto
    qed
    show "epimorphism b"
      by (simp add: b_epi)
  qed  
  show "\<exists>!b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>h\<^esub>\<times>\<^sub>c\<^bsub>h\<^esub> E \<and>
         fibered_product_left_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
         fibered_product_right_proj E h h E \<circ>\<^sub>c b = g \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
         epimorphism b"
    by (typecheck_cfuncs, metis epimorphism_def2 existence g_eq iso_imp_epi_and_monic kern_pair_proj_iso_TFAE2 monomorphism_def3)
qed

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

definition const_on_rel :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "const_on_rel X R f = (\<forall>x y. x \<in>\<^sub>c X \<longrightarrow> y \<in>\<^sub>c X \<longrightarrow> \<langle>x, y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longrightarrow> f \<circ>\<^sub>c x = f \<circ>\<^sub>c y)"

axiomatization 
  quotient_set :: "cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> cset" and
  equiv_class :: "cset \<times> cfunc \<Rightarrow> cfunc" and
  quotient_func :: "cfunc \<Rightarrow> cset \<times> cfunc \<Rightarrow> cfunc"
where
  equiv_class_type[type_rule]: "equiv_rel_on X R \<Longrightarrow> equiv_class R : X \<rightarrow> quotient_set X R" and
  equiv_class_eq: "equiv_rel_on X R \<Longrightarrow> \<langle>x, y\<rangle> \<in>\<^sub>c X\<times>\<^sub>cX \<Longrightarrow>
    \<langle>x, y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> R \<longleftrightarrow> equiv_class R \<circ>\<^sub>c x = equiv_class R \<circ>\<^sub>c y" and
  quotient_func_type[type_rule]: 
    "equiv_rel_on X R \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> (const_on_rel X R f) \<Longrightarrow>
      quotient_func f R : quotient_set X R \<rightarrow> Y" and 
  quotient_func_eq: "equiv_rel_on X R \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> (const_on_rel X R f) \<Longrightarrow>
     quotient_func f R \<circ>\<^sub>c equiv_class R = f" and  
  quotient_func_unique: "equiv_rel_on X R \<Longrightarrow> f : X \<rightarrow> Y \<Longrightarrow> (const_on_rel X R f) \<Longrightarrow>
    h : quotient_set X R \<rightarrow> Y \<Longrightarrow> h \<circ>\<^sub>c equiv_class R = f \<Longrightarrow> h = quotient_func f R"
(*Note that quotient_func f R is just f_bar *)


definition coequalizer :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "coequalizer E m f g \<longleftrightarrow> (\<exists> X Y. (f : Y \<rightarrow> X) \<and> (g : Y \<rightarrow> X) \<and> (m : X \<rightarrow> E)
    \<and> (m \<circ>\<^sub>c f = m \<circ>\<^sub>c g)
    \<and> (\<forall> h F. ((h : X \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h)))"

lemma coequalizer_def2:
  assumes "f : Y \<rightarrow> X" "g : Y \<rightarrow> X" "m : X \<rightarrow> E"
  shows "coequalizer E m f g \<longleftrightarrow>
    (m \<circ>\<^sub>c f = m \<circ>\<^sub>c g)
      \<and> (\<forall> h F. ((h : X \<rightarrow> F) \<and> (h \<circ>\<^sub>c f = h \<circ>\<^sub>c g)) \<longrightarrow> (\<exists>! k. (k : E \<rightarrow> F) \<and> k \<circ>\<^sub>c m = h))"
  using assms unfolding coequalizer_def cfunc_type_def by auto

(* Exercise 2.3.1 *)
lemma coequalizer_unique:
  assumes "coequalizer E m f g" "coequalizer F n f g"
  shows "E \<cong> F"
proof - 
  have k_exists: "\<exists>! k. k: E \<rightarrow> F \<and> k \<circ>\<^sub>c m =  n"
    by (typecheck_cfuncs, smt assms cfunc_type_def coequalizer_def)
  then obtain k where k_def: "k: E \<rightarrow> F \<and> k \<circ>\<^sub>c m =  n"
    by blast
  have k'_exists: "\<exists>! k'. k': F \<rightarrow> E \<and> k' \<circ>\<^sub>c n =  m"
    by (typecheck_cfuncs, smt assms cfunc_type_def coequalizer_def)
  then obtain k' where k'_def: "k': F \<rightarrow> E \<and> k' \<circ>\<^sub>c n =  m"
    by blast

  have k''_exists: "\<exists>! k''. k'': F \<rightarrow> F \<and> k'' \<circ>\<^sub>c n =  n"
    by (typecheck_cfuncs, smt (verit) assms(2)  cfunc_type_def coequalizer_def)
  then obtain k'' where k''_def: "k'': F \<rightarrow> F \<and> k'' \<circ>\<^sub>c n =  n"
    by blast
  then have k''_def2: "k'' = id F"
    using assms(2) coequalizer_def id_left_unit2 k''_def by (typecheck_cfuncs, blast)

  have kk'_idF: "k \<circ>\<^sub>c k' = id F"
    by (typecheck_cfuncs, smt (verit) assms(2) cfunc_type_def coequalizer_def comp_associative k''_def k''_def2 k'_def k_def)

  have k'k_idE: "k' \<circ>\<^sub>c k = id E"
    by (typecheck_cfuncs, smt (verit) assms(1) coequalizer_def comp_associative2 id_left_unit2 k'_def k_def)

  show "E \<cong> F"
    using cfunc_type_def is_isomorphic_def isomorphism_def k'_def k'k_idE k_def kk'_idF by fastforce
qed



(* Exercise 2.3.2 *) 
(*the proof is just dual in every sense to the equalizer is monomorphism proof*)
lemma coequalizer_is_epimorphism:
  "coequalizer E m f g \<Longrightarrow>  epimorphism(m)"
  unfolding coequalizer_def epimorphism_def
proof auto
  fix ga h X Y
  assume f_type: "f : Y \<rightarrow> X"
  assume g_type: "g : Y \<rightarrow> X"
  assume m_type: "m : X \<rightarrow> E"
  assume fm_gm: "m \<circ>\<^sub>c f = m \<circ>\<^sub>c g"
  assume uniqueness: "\<forall>h F. h : X \<rightarrow> F \<and> h \<circ>\<^sub>c f = h \<circ>\<^sub>c g \<longrightarrow> (\<exists>!k. k : E \<rightarrow> F \<and> k \<circ>\<^sub>c m = h)"
  assume relation_ga: "domain ga =codomain m "
  assume relation_h: "domain h = codomain m" 
  assume m_ga_mh: "ga \<circ>\<^sub>c m = h \<circ>\<^sub>c m" 

  have "ga \<circ>\<^sub>c m \<circ>\<^sub>c f = h \<circ>\<^sub>c m \<circ>\<^sub>c g"
    using cfunc_type_def comp_associative fm_gm g_type m_ga_mh m_type relation_ga relation_h by auto

  then obtain z where "z: E \<rightarrow> codomain(ga) \<and> z \<circ>\<^sub>c m  = ga \<circ>\<^sub>c m \<and>
    (\<forall> j. j:E \<rightarrow> codomain(ga) \<and>  j \<circ>\<^sub>c m = ga \<circ>\<^sub>c m \<longrightarrow> j = z)"
    using uniqueness apply (erule_tac x="ga \<circ>\<^sub>c m" in allE, erule_tac x="codomain(ga)" in allE)
    by (smt cfunc_type_def codomain_comp comp_associative domain_comp f_type g_type m_ga_mh m_type relation_ga relation_h)

  then show "ga = h"
    by (metis cfunc_type_def codomain_comp m_ga_mh m_type relation_ga relation_h)
qed

lemma canonical_quotient_map_is_coequalizer:
  assumes "equiv_rel_on X (R,m)"
  shows "coequalizer (quotient_set X (R,m)) (equiv_class (R,m))
                     (left_cart_proj X X \<circ>\<^sub>c m) (right_cart_proj X X \<circ>\<^sub>c m)"
  unfolding coequalizer_def 
proof(rule_tac x=X in exI, rule_tac x= "R" in exI,auto)
  have m_type: "m: R \<rightarrow>X \<times>\<^sub>c X"
    using assms equiv_rel_on_def subobject_of_def2 transitive_on_def by blast
  show "left_cart_proj X X \<circ>\<^sub>c m : R \<rightarrow> X"
    using m_type by typecheck_cfuncs
  show "right_cart_proj X X \<circ>\<^sub>c m : R \<rightarrow> X"
    using m_type by typecheck_cfuncs
  show "equiv_class (R, m) : X \<rightarrow> quotient_set X (R,m)"
    by (simp add: assms equiv_class_type)
  show "equiv_class (R, m) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m = equiv_class (R, m) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m"
  proof(rule one_separator[where X="R", where Y = "quotient_set X (R,m)"])
    show "equiv_class (R, m) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m : R \<rightarrow> quotient_set X (R, m)"
      using m_type assms by typecheck_cfuncs
    show "equiv_class (R, m) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m : R \<rightarrow> quotient_set X (R, m)"
      using m_type assms by typecheck_cfuncs
  next
    fix x 
    assume x_type: "x \<in>\<^sub>c R"
    then have m_x_type: "m \<circ>\<^sub>c x \<in>\<^sub>c X \<times>\<^sub>c X"
      using m_type by typecheck_cfuncs
    then obtain a b where a_type: "a \<in>\<^sub>c X" and b_type: "b \<in>\<^sub>c X" and m_x_eq: "m \<circ>\<^sub>c x = \<langle>a,b\<rangle>"
      using cart_prod_decomp by blast
    then have ab_inR_relXX: "\<langle>a,b\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub>(R,m)"
      using assms cfunc_type_def equiv_rel_on_def factors_through_def m_x_type reflexive_on_def relative_member_def2 x_type by auto
    then have "equiv_class (R, m) \<circ>\<^sub>c a = equiv_class (R, m) \<circ>\<^sub>c b"
      using equiv_class_eq assms relative_member_def by blast
    then have "equiv_class (R, m) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c \<langle>a,b\<rangle> = equiv_class (R, m) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c \<langle>a,b\<rangle>"
      using a_type b_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
    then have "equiv_class (R, m) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c x = equiv_class (R, m) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c x"
      by (simp add: m_x_eq)
    then show "(equiv_class (R, m) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m) \<circ>\<^sub>c x = (equiv_class (R, m) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m) \<circ>\<^sub>c x"
      using x_type m_type assms by (typecheck_cfuncs, metis cfunc_type_def comp_associative m_x_eq)
  qed   
next
  fix h F 
  assume h_type: " h : X \<rightarrow> F"
  assume h_proj1_eqs_h_proj2: "h \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m = h \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m"

  (*have fact1: "\<forall>x. x\<in>\<^sub>c X\<times>\<^sub>c X \<longrightarrow> h \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c x = h \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c x"
    using cfunc_type_def comp_associative h_proj1_eqs_h_proj2 h_type left_cart_proj_type right_cart_proj_type by auto
  have fact2: "\<forall> x. x \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R,m) \<longrightarrow> equiv_class (R,m) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c x = equiv_class (R,m) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c x"
    by (smt equiv_class_eq assms cfunc_prod_unique cfunc_type_def codomain_comp domain_comp left_cart_proj_type relative_member_def right_cart_proj_type)
  have fact3: "(\<forall> x y. \<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R,m) \<longrightarrow> equiv_class (R, m) \<circ>\<^sub>c h \<circ>\<^sub>c x = equiv_class (R, m) \<circ>\<^sub>c h \<circ>\<^sub>c y) \<longrightarrow> quotient_func h (R,m) \<circ>\<^sub>c equiv_class (R,m) = h"
    using assms h_type quotient_func_eq by auto
  have fact4: "(\<forall> x y. \<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R,m) \<longrightarrow> equiv_class (R, m) \<circ>\<^sub>c h \<circ>\<^sub>c x = equiv_class (R, m) \<circ>\<^sub>c h \<circ>\<^sub>c y)"
    by (metis (mono_tags, hide_lams) ETCS_Equivalence.equiv_class_eq assms cfunc_prod_type cfunc_type_def id_type one_unique_element relative_member_def)
  have fact5: "quotient_func h (R,m) \<circ>\<^sub>c equiv_class (R,m) = h"
    using fact3 fact4 by blast
  have k_type: "quotient_func h (R,m):  quotient_set X (R, m) \<rightarrow> F"
    by (simp add: assms fact4 h_type quotient_func_type)*)

  have m_type: "m : R \<rightarrow> X \<times>\<^sub>c X"
    using assms equiv_rel_on_def reflexive_on_def subobject_of_def2 by blast

  have "const_on_rel X (R, m) h"
  proof (unfold const_on_rel_def, auto)
    fix x y
    assume x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X"
    assume "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (R, m)"
    then obtain xy where xy_type: "xy \<in>\<^sub>c R" and m_h_eq: "m \<circ>\<^sub>c xy = \<langle>x,y\<rangle>"
      unfolding relative_member_def2 factors_through_def using cfunc_type_def by auto

    have "h \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c xy = h \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c xy"
      using h_type m_type xy_type by (typecheck_cfuncs, smt comp_associative2 comp_type h_proj1_eqs_h_proj2)
    then have "h \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c \<langle>x,y\<rangle> = h \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c \<langle>x,y\<rangle>"
      using m_h_eq by auto
    then show "h \<circ>\<^sub>c x = h \<circ>\<^sub>c y"
      using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod x_type y_type by auto
  qed
  then show "\<exists>k. k : quotient_set X (R, m) \<rightarrow> F \<and> k \<circ>\<^sub>c equiv_class (R, m) = h"
    using assms h_type quotient_func_type quotient_func_eq
    by (rule_tac x="quotient_func h (R, m)" in exI, auto)
next
  fix F k y
  assume k_type: "k : quotient_set X (R, m) \<rightarrow> F"
  assume y_type: "y : quotient_set X (R, m) \<rightarrow> F"
  assume k_equiv_class_type: "k \<circ>\<^sub>c equiv_class (R, m) : X \<rightarrow> F"

  assume k_equiv_class_eq: "(k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m =
       (k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m"

  assume y_k_eq: "y \<circ>\<^sub>c equiv_class (R, m) = k \<circ>\<^sub>c equiv_class (R, m)"

  have m_type: "m : R \<rightarrow> X \<times>\<^sub>c X"
    using assms equiv_rel_on_def reflexive_on_def subobject_of_def2 by blast

  have y_eq: "y = quotient_func (y \<circ>\<^sub>c equiv_class (R, m)) (R, m)"
    using assms y_type k_equiv_class_type y_k_eq
  proof (rule_tac quotient_func_unique[where X=X, where Y=F], simp_all, unfold const_on_rel_def, auto)
    fix a b
    assume a_type: "a \<in>\<^sub>c X" and b_type: "b \<in>\<^sub>c X"
    assume ab_in_R: "\<langle>a,b\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (R, m)"
    then obtain h where h_type: "h \<in>\<^sub>c R" and m_h_eq: "m \<circ>\<^sub>c h = \<langle>a, b\<rangle>"
      unfolding relative_member_def factors_through_def using cfunc_type_def by auto 

    have "(k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c h =
       (k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c h"
      using k_type m_type h_type assms 
      by (typecheck_cfuncs, smt comp_associative2 comp_type k_equiv_class_eq)
    then have "(k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c \<langle>a, b\<rangle> =
       (k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c \<langle>a, b\<rangle>"
      by (simp add: m_h_eq)
    then show "(k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c a = (k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c b"
      using a_type b_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  qed

  have k_eq: "k = quotient_func (y \<circ>\<^sub>c equiv_class (R, m)) (R, m)"
    using assms k_type k_equiv_class_type y_k_eq
  proof (rule_tac quotient_func_unique[where X=X, where Y=F], simp_all, unfold const_on_rel_def, auto)
    fix a b
    assume a_type: "a \<in>\<^sub>c X" and b_type: "b \<in>\<^sub>c X"
    assume ab_in_R: "\<langle>a,b\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (R, m)"
    then obtain h where h_type: "h \<in>\<^sub>c R" and m_h_eq: "m \<circ>\<^sub>c h = \<langle>a, b\<rangle>"
      unfolding relative_member_def factors_through_def using cfunc_type_def by auto 
    
    have "(k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c h =
       (k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c m \<circ>\<^sub>c h"
      using k_type m_type h_type assms 
      by (typecheck_cfuncs, smt comp_associative2 comp_type k_equiv_class_eq)
    then have "(k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c left_cart_proj X X \<circ>\<^sub>c \<langle>a, b\<rangle> =
       (k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c \<langle>a, b\<rangle>"
      by (simp add: m_h_eq)
    then show "(k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c a = (k \<circ>\<^sub>c equiv_class (R, m)) \<circ>\<^sub>c b"
      using a_type b_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  qed

  show "k = y"
    using y_eq k_eq by auto
qed

lemma canonical_quot_map_is_epi:
  assumes "equiv_rel_on X (R,m)"
  shows "epimorphism((equiv_class (R,m)))"
  by (meson assms canonical_quotient_map_is_coequalizer coequalizer_is_epimorphism)

(* Exercise 2.3.3 *)
lemma kernel_pair_equiv_rel:
  assumes "f : X \<rightarrow> Y"
  shows "equiv_rel_on X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
proof (unfold equiv_rel_on_def, auto)

  show "reflexive_on X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
  proof (unfold reflexive_on_def, auto)
    show "(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) \<subseteq>\<^sub>c X \<times>\<^sub>c X"
      using assms kernel_pair_subset by auto
  next
    fix x
    assume x_type: "x \<in>\<^sub>c X"
    then show "\<langle>x,x\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
      by (smt assms comp_type diag_on_elements diagonal_type fibered_product_morphism_monomorphism
          fibered_product_morphism_type pair_factorsthru_fibered_product_morphism relative_member_def2)
  qed

  show "symmetric_on X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
  proof (unfold symmetric_on_def, auto)
    show "(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) \<subseteq>\<^sub>c X \<times>\<^sub>c X"
      using assms kernel_pair_subset by auto
  next 
    fix x y
    assume x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X"
    assume xy_in: "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    then have "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
      using assms fibered_product_pair_member x_type y_type by blast
    
    then show "\<langle>y,x\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
      using assms fibered_product_pair_member x_type y_type by auto
  qed

  show "transitive_on X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
  proof (unfold transitive_on_def, auto)
    show "(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) \<subseteq>\<^sub>c X \<times>\<^sub>c X"
      using assms kernel_pair_subset by auto
  next 
    fix x y z 
    assume x_type: "x \<in>\<^sub>c X" and y_type: "y \<in>\<^sub>c X" and z_type: "z \<in>\<^sub>c X"
    assume xy_in: "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    assume yz_in: "\<langle>y,z\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"

   have eqn1: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
     using assms fibered_product_pair_member x_type xy_in y_type by blast

   have eqn2: "f \<circ>\<^sub>c y = f \<circ>\<^sub>c z"
     using assms fibered_product_pair_member y_type yz_in z_type by blast

   show "\<langle>x,z\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
     using assms eqn1 eqn2 fibered_product_pair_member x_type z_type by auto
 qed
qed

(*abbreviation "kernel_pair_rel X f \<equiv> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"*)

 
 (*shows "coequalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) f (fibered_product_left_proj X f f X) (fibered_product_right_proj X f f X)"
*)

(* Definition 2.3.4 *)
definition regular_epimorphism :: "cfunc \<Rightarrow> bool" where
  "regular_epimorphism f = (\<exists> g h. coequalizer (codomain f) f g h)"

(* Exercise 2.3.5 *)
lemma reg_epi_and_mono_is_iso:
  assumes "f : X \<rightarrow> Y" "regular_epimorphism f" "monomorphism f"
  shows "isomorphism f"
proof -
  have coeq1: "(\<exists> g h. coequalizer (codomain f) f g h)"
    using assms(2) regular_epimorphism_def by auto
  then obtain g h where gh_def: "coequalizer (codomain f) f g h"
    by blast
  then have coequalized_fxns: "\<exists>W. (g: W \<rightarrow> X) \<and> (h: W \<rightarrow> X) \<and> (coequalizer Y f g h)"
    using assms(1) cfunc_type_def coequalizer_def by auto
  then obtain W where W_def: "(g: W \<rightarrow> X) \<and> (h: W \<rightarrow> X) \<and> (coequalizer Y f g h)"
    by blast
  have fg_eqs_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
    using coequalizer_def gh_def by blast
  then have gh_eqs: "g = h"
    using W_def assms(1) assms(3) monomorphism_def2 by blast
  then have "id(X)\<circ>\<^sub>c g = id(X) \<circ>\<^sub>c  h"
    by auto
  then have j_exists: "\<exists>! j. j: Y \<rightarrow> X \<and> j \<circ>\<^sub>c f =  id(X)"
     by (typecheck_cfuncs, smt (verit) cfunc_type_def coequalized_fxns coequalizer_def)
  then obtain j where j_def: "j: Y \<rightarrow> X \<and> j \<circ>\<^sub>c f =  id(X)"
     by auto


   have "id(Y) \<circ>\<^sub>c f = f \<circ>\<^sub>c id(X)"
     using assms(1) id_left_unit2 id_right_unit2 by auto
   also have "... = (f \<circ>\<^sub>c j) \<circ>\<^sub>c f"
     using assms(1) comp_associative2 j_def by fastforce

   then have "id(Y) = f \<circ>\<^sub>c j"
     by (typecheck_cfuncs, metis \<open>f \<circ>\<^sub>c id\<^sub>c X = (f \<circ>\<^sub>c j) \<circ>\<^sub>c f\<close> assms(1) calculation coequalized_fxns coequalizer_is_epimorphism epimorphism_def3 j_def)

   show "isomorphism f"
     by (meson CollectI assms(3) coequalized_fxns coequalizer_is_epimorphism epi_mon_is_iso)
 qed

(* Proposition 2.3.6 *)
lemma epimorphism_coequalizer_kernel_pair:
  assumes "f : X \<rightarrow> Y" "epimorphism f"
  shows "coequalizer Y f (fibered_product_left_proj X f f X) (fibered_product_right_proj X f f X)"
proof (unfold coequalizer_def, rule_tac x=X in exI, rule_tac x="X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" in exI, auto)
  show "fibered_product_left_proj X f f X : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> X"
    using assms by typecheck_cfuncs
  show "fibered_product_right_proj X f f X : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> X"
    using assms by typecheck_cfuncs
  show "f : X \<rightarrow>Y"
    using assms by typecheck_cfuncs

  show "f \<circ>\<^sub>c fibered_product_left_proj X f f X = f \<circ>\<^sub>c fibered_product_right_proj X f f X"
    using fibered_product_is_pullback assms unfolding is_pullback_def square_commutes_def by auto
next
  fix g E
  assume g_type: "g : X \<rightarrow> E"

  assume g_eq: "g \<circ>\<^sub>c fibered_product_left_proj X f f X = g \<circ>\<^sub>c fibered_product_right_proj X f f X"

  

  obtain F where F_def: "F = quotient_set X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    by auto
  obtain q where q_def: "q = equiv_class (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    by auto
  have q_type[type_rule]: "q : X \<rightarrow> F"
    using F_def assms(1) equiv_class_type kernel_pair_equiv_rel q_def by blast
    
  obtain f_bar where f_bar_def: "f_bar = quotient_func f (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    by auto
  have f_bar_type[type_rule]: "f_bar : F \<rightarrow> Y" 
      using F_def assms(1) const_on_rel_def f_bar_def fibered_product_pair_member kernel_pair_equiv_rel quotient_func_type by auto
  have fibr_proj_left_type[type_rule]: "fibered_product_left_proj F (f_bar) (f_bar) F : F \<^bsub>(f_bar)\<^esub>\<times>\<^sub>c\<^bsub>(f_bar)\<^esub> F \<rightarrow> F"
    by typecheck_cfuncs
  have fibr_proj_right_type[type_rule]: "fibered_product_right_proj F (f_bar) (f_bar) F : F \<^bsub>(f_bar)\<^esub>\<times>\<^sub>c\<^bsub>(f_bar)\<^esub> F \<rightarrow> F"
    by typecheck_cfuncs

  (*Outline*)
  (* show f_bar is iso using argument from the bottom of page 43, with g = q (axiom 6's q) and m = f_bar *)
    (* b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> F \<^bsub>m\<^esub>\<times>\<^sub>c\<^bsub>m\<^esub> F exists because fibered_product_morphism X f f X is an equalizer *)
    (* b exists and is an epimorphism by kernel_pair_connection *)
    (* also have "fibered_product_left_proj E m m E \<circ>\<^sub>c b = fibered_product_right_proj E m m E \<circ>\<^sub>c b" *)
    (* then "fibered_product_left_proj E m m E = fibered_product_right_proj E m m E", since b is epi *)
    (* then m is a monomorphism by kern_pair_proj_iso_TFAE2 *)
    (* but m is also an epimorphism since f = m \<circ>\<^sub>c g and f and g are epi, by comp_epi_imp_epi *)
    (* so m = f_bar is an isomorphism by epi_mon_is_iso *)
  (* take g_bar : F \<rightarrow> E and the inverse of f_bar to satisfy the required thesis *)

  have f_eqs: "f_bar \<circ>\<^sub>c q = f"
    proof - 
      have fact1: "equiv_rel_on X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
        by (meson assms(1) kernel_pair_equiv_rel)

      have fact2: "const_on_rel X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) f"
        using assms(1) const_on_rel_def fibered_product_pair_member by presburger
      show ?thesis
        using assms(1) f_bar_def fact1 fact2 q_def quotient_func_eq by blast
    qed


  have "\<exists>! b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> F \<^bsub>(f_bar)\<^esub>\<times>\<^sub>c\<^bsub>(f_bar)\<^esub> F \<and>
    fibered_product_left_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
    fibered_product_right_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
    epimorphism b"
  proof(rule kernel_pair_connection[where Y = Y])
    show "f : X \<rightarrow> Y"
      using assms by typecheck_cfuncs
    show "q : X \<rightarrow> F"
      by typecheck_cfuncs
    show "epimorphism q"
      using assms(1) canonical_quot_map_is_epi kernel_pair_equiv_rel q_def by blast
    show "f_bar \<circ>\<^sub>c q = f"
      by (simp add: f_eqs)
    show "q \<circ>\<^sub>c fibered_product_left_proj X f f X = q \<circ>\<^sub>c fibered_product_right_proj X f f X"
      by (metis assms(1) canonical_quotient_map_is_coequalizer coequalizer_def fibered_product_left_proj_def fibered_product_right_proj_def kernel_pair_equiv_rel q_def)
    show "f_bar : F \<rightarrow> Y" 
      by typecheck_cfuncs
  qed

  (* b exists and is an epimorphism by kernel_pair_connection *)
  (* also have "fibered_product_left_proj E m m E \<circ>\<^sub>c b = fibered_product_right_proj E m m E \<circ>\<^sub>c b" *)
  then obtain b where b_type[type_rule]: "b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> F \<^bsub>(f_bar)\<^esub>\<times>\<^sub>c\<^bsub>(f_bar)\<^esub> F" and
   left_b_eqs: "fibered_product_left_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj X f f X" and
   right_b_eqs:  "fibered_product_right_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj X f f X" and
   epi_b: "epimorphism b"
    by auto
  

 (* then "fibered_product_left_proj E m m E = fibered_product_right_proj E m m E", since b is epi *)
  have "fibered_product_left_proj F (f_bar) (f_bar) F = fibered_product_right_proj F (f_bar) (f_bar) F"
  proof - 
    have "(fibered_product_left_proj F (f_bar) (f_bar) F) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj X f f X"
      by (simp add: left_b_eqs)
    also have "... = q \<circ>\<^sub>c fibered_product_right_proj X f f X"
      using assms(1) canonical_quotient_map_is_coequalizer coequalizer_def fibered_product_left_proj_def fibered_product_right_proj_def kernel_pair_equiv_rel q_def by fastforce
    also have "... = fibered_product_right_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b"
      by (simp add: right_b_eqs)
    then have "fibered_product_left_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = fibered_product_right_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b"
      by (simp add: calculation)
    then show ?thesis
      using b_type epi_b epimorphism_def2 fibr_proj_left_type fibr_proj_right_type by blast
  qed

  
  (* b exists and is an epimorphism by kernel_pair_connection *)
  (* also have "fibered_product_left_proj E m m E \<circ>\<^sub>c b = fibered_product_right_proj E m m E \<circ>\<^sub>c b" *)
  then obtain b where b_type[type_rule]: "b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> F \<^bsub>(f_bar)\<^esub>\<times>\<^sub>c\<^bsub>(f_bar)\<^esub> F" and
   left_b_eqs: "fibered_product_left_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj X f f X" and
   right_b_eqs:  "fibered_product_right_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj X f f X" and
   epi_b: "epimorphism b"
    using b_type epi_b left_b_eqs right_b_eqs by blast
  

 (* then "fibered_product_left_proj E m m E = fibered_product_right_proj E m m E", since b is epi *)
  have "fibered_product_left_proj F (f_bar) (f_bar) F = fibered_product_right_proj F (f_bar) (f_bar) F"
  proof - 
    have "(fibered_product_left_proj F (f_bar) (f_bar) F) \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj X f f X"
      by (simp add: left_b_eqs)
    also have "... = q \<circ>\<^sub>c fibered_product_right_proj X f f X"
      using assms(1) canonical_quotient_map_is_coequalizer coequalizer_def fibered_product_left_proj_def fibered_product_right_proj_def kernel_pair_equiv_rel q_def by fastforce
    also have "... = fibered_product_right_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b"
      by (simp add: right_b_eqs)
    then have "fibered_product_left_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b = fibered_product_right_proj F (f_bar) (f_bar) F \<circ>\<^sub>c b"
      by (simp add: calculation)
    then show ?thesis
      using b_type epi_b epimorphism_def2 fibr_proj_left_type fibr_proj_right_type by blast
  qed
  (* then m = f_bar is a monomorphism by kern_pair_proj_iso_TFAE2 *)
  then have mono_fbar: "monomorphism(f_bar)"
    by (typecheck_cfuncs, simp add:  kern_pair_proj_iso_TFAE2)
  (* but m = f_bar is also an epimorphism since f = m \<circ>\<^sub>c g and f and g = q are epi, by comp_epi_imp_epi *)
  have "epimorphism(f_bar)"
    by (typecheck_cfuncs, metis assms(2) cfunc_type_def comp_epi_imp_epi f_eqs q_type)
  (* so m = f_bar is an isomorphism by epi_mon_is_iso *)
  then have "isomorphism(f_bar)"
    by (simp add: epi_mon_is_iso mono_fbar)

  (* take  g_bar : F \<rightarrow> E and the inverse of f_bar to satisfy the required thesis *)
  (* Recall that f_bar : F \<rightarrow> Y"*)

  obtain f_bar_inv where f_bar_inv_type[type_rule]: "f_bar_inv: Y \<rightarrow> F" and
                            f_bar_inv_eq1: "f_bar_inv \<circ>\<^sub>c f_bar = id(F)" and  
                            f_bar_inv_eq2: "f_bar \<circ>\<^sub>c f_bar_inv = id(Y)"
    using \<open>isomorphism f_bar\<close> cfunc_type_def isomorphism_def by (typecheck_cfuncs, force)
  
  obtain g_bar where g_bar_def: "g_bar = quotient_func g (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    by auto
  have "const_on_rel X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) g"
    unfolding const_on_rel_def 
    by (meson assms(1) fibered_product_pair_member2 g_eq g_type)
  then have g_bar_type[type_rule]: "g_bar : F \<rightarrow> E"
    using F_def assms(1) g_bar_def g_type kernel_pair_equiv_rel quotient_func_type by blast
  obtain k where k_def: "k = g_bar \<circ>\<^sub>c f_bar_inv" and k_type[type_rule]: "k : Y \<rightarrow> E"
    by typecheck_cfuncs   
  then show "\<exists>k. k : Y \<rightarrow> E \<and> k \<circ>\<^sub>c f = g"
    by (smt (z3) \<open>const_on_rel X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) g\<close> assms(1) comp_associative2 f_bar_inv_eq1 f_bar_inv_type f_bar_type f_eqs g_bar_def g_bar_type g_type id_left_unit2 kernel_pair_equiv_rel q_def q_type quotient_func_eq)
next
  show "\<And>F k y.
       k \<circ>\<^sub>c f : X \<rightarrow> F \<Longrightarrow>
       (k \<circ>\<^sub>c f) \<circ>\<^sub>c fibered_product_left_proj X f f X = (k \<circ>\<^sub>c f) \<circ>\<^sub>c fibered_product_right_proj X f f X \<Longrightarrow>
       k : Y \<rightarrow> F \<Longrightarrow> y : Y \<rightarrow> F \<Longrightarrow> y \<circ>\<^sub>c f = k \<circ>\<^sub>c f \<Longrightarrow> k = y"
    using assms epimorphism_def2 by blast
qed

(* Proposition 2.3.6b *)
lemma epimorphisms_are_regular:
  assumes "f : X \<rightarrow> Y" "epimorphism f"
  shows "regular_epimorphism f"
  by (meson assms(2) cfunc_type_def epimorphism_coequalizer_kernel_pair regular_epimorphism_def)

lemma epi_monic_factorization:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  shows "\<exists> g m E. g : X \<rightarrow> E \<and> m : E \<rightarrow> Y 
    \<and> coequalizer E g (fibered_product_left_proj X f f X) (fibered_product_right_proj X f f X)
    \<and> monomorphism m \<and> f = m \<circ>\<^sub>c g
    \<and> (\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
proof -
  obtain q where q_def: "q = equiv_class (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    by auto
  obtain E where E_def: "E = quotient_set X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    by auto
  obtain m where m_def: "m = quotient_func f (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
    by auto
  show "\<exists> g m E. g : X \<rightarrow> E \<and> m : E \<rightarrow> Y 
    \<and> coequalizer E g (fibered_product_left_proj X f f X) (fibered_product_right_proj X f f X)
    \<and> monomorphism m \<and> f = m \<circ>\<^sub>c g
    \<and> (\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
  proof (rule_tac x="q" in exI, rule_tac x="m" in exI, rule_tac x="E" in exI, auto)
    show q_type[type_rule]: "q : X \<rightarrow> E"
      unfolding q_def E_def using kernel_pair_equiv_rel by (typecheck_cfuncs, blast)
    
    have f_const: "const_on_rel X (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) f"
      unfolding const_on_rel_def using assms fibered_product_pair_member by auto
    then show m_type[type_rule]: "m : E \<rightarrow> Y"
      unfolding m_def E_def using kernel_pair_equiv_rel by (typecheck_cfuncs, blast)
    
    show q_coequalizer: "coequalizer E q (fibered_product_left_proj X f f X) (fibered_product_right_proj X f f X)"
      unfolding q_def fibered_product_left_proj_def fibered_product_right_proj_def E_def
      using canonical_quotient_map_is_coequalizer f_type kernel_pair_equiv_rel by auto 
    then have q_epi: "epimorphism q"
      using coequalizer_is_epimorphism by auto 

    show m_mono: "monomorphism m"
    proof -
      thm kernel_pair_connection[where E=E,where X=X, where h=m, where f=f, where g=q, where Y=Y]
      have q_eq: "q \<circ>\<^sub>c fibered_product_left_proj X f f X = q \<circ>\<^sub>c fibered_product_right_proj X f f X"
        using canonical_quotient_map_is_coequalizer coequalizer_def f_type fibered_product_left_proj_def fibered_product_right_proj_def kernel_pair_equiv_rel q_def by fastforce
      then have "\<exists>!b. b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>m\<^esub>\<times>\<^sub>c\<^bsub>m\<^esub> E \<and>
        fibered_product_left_proj E m m E \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj X f f X \<and>
        fibered_product_right_proj E m m E \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj X f f X \<and>
        epimorphism b"
        by (typecheck_cfuncs, rule_tac kernel_pair_connection[where Y=Y],
            simp_all add: q_epi, metis f_const kernel_pair_equiv_rel m_def q_def quotient_func_eq)
      then obtain b where b_type[type_rule]: "b : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> E \<^bsub>m\<^esub>\<times>\<^sub>c\<^bsub>m\<^esub> E" and
        b_left_eq: "fibered_product_left_proj E m m E \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_left_proj X f f X" and
        b_right_eq: "fibered_product_right_proj E m m E \<circ>\<^sub>c b = q \<circ>\<^sub>c fibered_product_right_proj X f f X" and
        b_epi: "epimorphism b"
        by auto

      have "fibered_product_left_proj E m m E \<circ>\<^sub>c b = fibered_product_right_proj E m m E \<circ>\<^sub>c b"
        using b_left_eq b_right_eq q_eq by force
      then have "fibered_product_left_proj E m m E = fibered_product_right_proj E m m E"
        using b_epi cfunc_type_def epimorphism_def by (typecheck_cfuncs_prems, auto)
      then show "monomorphism m"
        using kern_pair_proj_iso_TFAE2 m_type by auto
    qed

    show f_eq_m_q: "f = m \<circ>\<^sub>c q"
      using f_const f_type kernel_pair_equiv_rel m_def q_def quotient_func_eq by fastforce

    show "\<And>x. x : E \<rightarrow> Y \<Longrightarrow> f = x \<circ>\<^sub>c q \<Longrightarrow> x = m"
    proof -
      fix x
      assume x_type[type_rule]: "x : E \<rightarrow> Y"
      assume f_eq_x_q: "f = x \<circ>\<^sub>c q"
      have "x \<circ>\<^sub>c q = m \<circ>\<^sub>c q"
        using f_eq_m_q f_eq_x_q by auto
      then show "x = m"
        using epimorphism_def2 m_type q_epi q_type x_type by blast
    qed
  qed
qed

lemma epi_monic_factorization2:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  shows "\<exists> g m E. g : X \<rightarrow> E \<and> m : E \<rightarrow> Y 
    \<and> epimorphism g \<and> monomorphism m \<and> f = m \<circ>\<^sub>c g
    \<and> (\<forall>x. x : E \<rightarrow> Y \<longrightarrow> f = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
  using epi_monic_factorization coequalizer_is_epimorphism by (meson f_type)


thm epi_monic_factorization[where f = "f \<circ>\<^sub>c n", where X=A, where Y=Y]

(* Definition 2.3.7 *)
definition image_of :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cset" ("_[_]\<^bsub>_\<^esub>" [101,0,0]100) where
  "image_of f A n = (SOME fA. \<exists>g m.
   g : A \<rightarrow> fA \<and>
   m : fA \<rightarrow> codomain f \<and>
   coequalizer fA g (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) \<and>
   monomorphism m \<and> f \<circ>\<^sub>c n = m \<circ>\<^sub>c g \<and> (\<forall>x. x : fA \<rightarrow> codomain f \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c g \<longrightarrow> x = m))"

(*An above is (A,n) below 
so that fst An is just the set A 
while snd An is just n, and fA corresponds to f(A) or \<exists>\<^sub>f(f) in the text.*)

lemma image_of_def2:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "\<exists>g m.
    g : A \<rightarrow> f[A]\<^bsub>n\<^esub> \<and>
    m : f[A]\<^bsub>n\<^esub> \<rightarrow> Y \<and>
    coequalizer (f[A]\<^bsub>n\<^esub>) g (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) \<and>
    monomorphism m \<and> f \<circ>\<^sub>c n = m \<circ>\<^sub>c g \<and> (\<forall>x. x : f[A]\<^bsub>n\<^esub> \<rightarrow> Y \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
proof -
  have "\<exists>g m.
    g : A \<rightarrow> f[A]\<^bsub>n\<^esub> \<and>
    m : f[A]\<^bsub>n\<^esub> \<rightarrow> codomain f \<and>
    coequalizer (f[A]\<^bsub>n\<^esub>) g (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) \<and>
    monomorphism m \<and> f \<circ>\<^sub>c n = m \<circ>\<^sub>c g \<and> (\<forall>x. x : f[A]\<^bsub>n\<^esub> \<rightarrow> codomain f \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c g \<longrightarrow> x = m)"
    using assms cfunc_type_def comp_type epi_monic_factorization[where f="f \<circ>\<^sub>c n", where X=A, where Y="codomain f"] 
    by (unfold image_of_def, rule_tac someI_ex, auto)
  then show ?thesis
    using assms(1) cfunc_type_def by auto
qed

definition image_restriction_mapping :: "cfunc \<Rightarrow> cset \<times> cfunc \<Rightarrow> cfunc" ("_\<restriction>\<^bsub>_\<^esub>" [101,0]100) where
  "image_restriction_mapping f An = (SOME g. \<exists> m. g : fst An \<rightarrow> f[fst An]\<^bsub>snd An\<^esub> \<and> m : f[fst An]\<^bsub>snd An\<^esub> \<rightarrow> codomain f \<and>
    coequalizer (f[fst An]\<^bsub>snd An\<^esub>) g (fibered_product_left_proj (fst An) (f \<circ>\<^sub>c snd An) (f \<circ>\<^sub>c snd An) (fst An)) (fibered_product_right_proj (fst An) (f \<circ>\<^sub>c snd An) (f \<circ>\<^sub>c snd An) (fst An)) \<and>
    monomorphism m \<and> f \<circ>\<^sub>c snd An = m \<circ>\<^sub>c g \<and> (\<forall>x. x : f[fst An]\<^bsub>snd An\<^esub> \<rightarrow> codomain f \<longrightarrow> f \<circ>\<^sub>c snd An = x \<circ>\<^sub>c g \<longrightarrow> x = m))"

term "f\<restriction>\<^bsub>(A, n \<circ>\<^sub>c m)\<^esub>"

lemma image_restriction_mapping_def2:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "\<exists> m. f\<restriction>\<^bsub>(A, n)\<^esub> : A \<rightarrow> f[A]\<^bsub>n\<^esub> \<and> m : f[A]\<^bsub>n\<^esub> \<rightarrow> Y \<and>
    coequalizer (f[A]\<^bsub>n\<^esub>) (f\<restriction>\<^bsub>(A, n)\<^esub>) (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) \<and>
    monomorphism m \<and> f \<circ>\<^sub>c n = m \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<and> (\<forall>x. x : f[A]\<^bsub>n\<^esub> \<rightarrow> Y \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<longrightarrow> x = m)"
proof -
  have codom_f: "codomain f = Y"
    using assms(1) cfunc_type_def by auto
  have "\<exists> m. f\<restriction>\<^bsub>(A, n)\<^esub> : fst (A, n) \<rightarrow> f[fst (A, n)]\<^bsub>snd (A, n)\<^esub> \<and> m : f[fst (A, n)]\<^bsub>snd (A, n)\<^esub> \<rightarrow> codomain f \<and>
    coequalizer (f[fst (A, n)]\<^bsub>snd (A, n)\<^esub>) (f\<restriction>\<^bsub>(A, n)\<^esub>) (fibered_product_left_proj (fst (A, n)) (f \<circ>\<^sub>c snd (A, n)) (f \<circ>\<^sub>c snd (A, n)) (fst (A, n))) (fibered_product_right_proj (fst (A, n)) (f \<circ>\<^sub>c snd (A, n)) (f \<circ>\<^sub>c snd (A, n)) (fst (A, n))) \<and>
    monomorphism m \<and> f \<circ>\<^sub>c snd (A, n) = m \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<and> (\<forall>x. x : f[fst (A, n)]\<^bsub>snd (A, n)\<^esub> \<rightarrow> codomain f \<longrightarrow> f \<circ>\<^sub>c snd (A, n) = x \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<longrightarrow> x = m)"
    unfolding image_restriction_mapping_def by (rule someI_ex, insert assms image_of_def2 codom_f, auto)
  then show ?thesis
    using codom_f
    by simp 
qed

definition image_subobject_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" ("[_[_]\<^bsub>_\<^esub>]map" [101,0,0]100) where
  "[f[A]\<^bsub>n\<^esub>]map = (THE m. f\<restriction>\<^bsub>(A, n)\<^esub> : A \<rightarrow> f[A]\<^bsub>n\<^esub> \<and> m : f[A]\<^bsub>n\<^esub> \<rightarrow> codomain f \<and>
   coequalizer (f[A]\<^bsub>n\<^esub>) (f\<restriction>\<^bsub>(A, n)\<^esub>) (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) \<and>
   monomorphism m \<and> f \<circ>\<^sub>c n = m \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<and> (\<forall>x. x : (f[A]\<^bsub>n\<^esub>) \<rightarrow> codomain f \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<longrightarrow> x = m))"

lemma image_subobject_mapping_def2:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "f\<restriction>\<^bsub>(A, n)\<^esub> : A \<rightarrow> f[A]\<^bsub>n\<^esub> \<and> [f[A]\<^bsub>n\<^esub>]map : f[A]\<^bsub>n\<^esub> \<rightarrow> Y \<and>
    coequalizer (f[A]\<^bsub>n\<^esub>) (f\<restriction>\<^bsub>(A, n)\<^esub>) (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) \<and>
    monomorphism ([f[A]\<^bsub>n\<^esub>]map) \<and> f \<circ>\<^sub>c n = [f[A]\<^bsub>n\<^esub>]map \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<and> (\<forall>x. x : f[A]\<^bsub>n\<^esub> \<rightarrow> Y \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<longrightarrow> x = [f[A]\<^bsub>n\<^esub>]map)"
proof -
  have codom_f: "codomain f = Y"
    using assms(1) cfunc_type_def by auto
  have "f\<restriction>\<^bsub>(A, n)\<^esub> : A \<rightarrow> f[A]\<^bsub>n\<^esub> \<and> ([f[A]\<^bsub>n\<^esub>]map) : f[A]\<^bsub>n\<^esub> \<rightarrow> codomain f \<and>
   coequalizer (f[A]\<^bsub>n\<^esub>) (f\<restriction>\<^bsub>(A, n)\<^esub>) (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) \<and>
   monomorphism ([f[A]\<^bsub>n\<^esub>]map) \<and> f \<circ>\<^sub>c n = ([f[A]\<^bsub>n\<^esub>]map) \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<and> 
   (\<forall>x. x : (f[A]\<^bsub>n\<^esub>) \<rightarrow> codomain f \<longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<longrightarrow> x = ([f[A]\<^bsub>n\<^esub>]map))"
    unfolding image_subobject_mapping_def
    by (rule theI', insert assms codom_f image_restriction_mapping_def2, blast)
  then show ?thesis
    using codom_f by fastforce
qed

lemma image_rest_map_type[type_rule]:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "f\<restriction>\<^bsub>(A, n)\<^esub> : A \<rightarrow> f[A]\<^bsub>n\<^esub>"
  using assms image_restriction_mapping_def2 by blast

lemma image_rest_map_coequalizer:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "coequalizer (f[A]\<^bsub>n\<^esub>) (f\<restriction>\<^bsub>(A, n)\<^esub>) (fibered_product_left_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A) (fibered_product_right_proj A (f \<circ>\<^sub>c n) (f \<circ>\<^sub>c n) A)"
  using assms image_restriction_mapping_def2 by blast

lemma image_rest_map_epi:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "epimorphism (f\<restriction>\<^bsub>(A, n)\<^esub>)"
  using assms image_rest_map_coequalizer coequalizer_is_epimorphism by blast 

lemma image_subobj_map_type[type_rule]:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "[f[A]\<^bsub>n\<^esub>]map : f[A]\<^bsub>n\<^esub> \<rightarrow> Y"
  using assms image_subobject_mapping_def2 by blast

lemma image_subobj_map_mono:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "monomorphism ([f[A]\<^bsub>n\<^esub>]map)"
  using assms image_subobject_mapping_def2 by blast

lemma image_subobj_comp_image_rest:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "[f[A]\<^bsub>n\<^esub>]map \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) = f \<circ>\<^sub>c n"
  using assms image_subobject_mapping_def2 by auto

lemma image_subobj_map_unique:
  assumes "f : X \<rightarrow> Y" "n : A \<rightarrow> X"
  shows "x : f[A]\<^bsub>n\<^esub> \<rightarrow> Y \<Longrightarrow> f \<circ>\<^sub>c n = x \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, n)\<^esub>) \<Longrightarrow> x = [f[A]\<^bsub>n\<^esub>]map"
  using assms image_subobject_mapping_def2 by blast

lemma image_self:
  assumes "f : X \<rightarrow> Y" and "monomorphism f"
  assumes "a : A \<rightarrow> X" and "monomorphism a"
  shows "f[A]\<^bsub>a\<^esub> \<cong> A"
proof -
  have "monomorphism (f \<circ>\<^sub>c a)"
    using assms cfunc_type_def composition_of_monic_pair_is_monic by auto
  then have "monomorphism ([f[A]\<^bsub>a\<^esub>]map \<circ>\<^sub>c (f\<restriction>\<^bsub>(A, a)\<^esub>))"
    using assms image_subobj_comp_image_rest by auto
  then have "monomorphism (f\<restriction>\<^bsub>(A, a)\<^esub>)"
    by (meson assms comp_monic_imp_monic' image_rest_map_type image_subobj_map_type)
  then have "isomorphism (f\<restriction>\<^bsub>(A, a)\<^esub>)"
    using assms epi_mon_is_iso image_rest_map_epi by blast
  then have "A \<cong> f[A]\<^bsub>a\<^esub>"
    using assms unfolding is_isomorphic_def by (rule_tac x="f\<restriction>\<^bsub>(A, a)\<^esub>" in exI, typecheck_cfuncs)
  then show ?thesis
    by (simp add: isomorphic_is_symmetric)
qed

(*Now we show that f(A) is the smallest subobject of Y through which f factors (in the sense of epi-monic factorization)*)
(*Proposition 2.3.8*)
lemma image_smallest_subobject:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y" and a_type[type_rule]: "a : A \<rightarrow> X"
  shows "(B, n) \<subseteq>\<^sub>c Y \<Longrightarrow> f factorsthru n \<Longrightarrow> (f[A]\<^bsub>a\<^esub>, [f[A]\<^bsub>a\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B, n)"
proof -
  assume "(B, n) \<subseteq>\<^sub>c Y"
  then have n_type[type_rule]: "n : B \<rightarrow> Y" and n_mono: "monomorphism n"
    unfolding subobject_of_def2 by auto
  assume "f factorsthru n"
  then obtain g where g_type[type_rule]: "g : X \<rightarrow> B" and f_eq_ng: "n \<circ>\<^sub>c g = f"
    using factors_through_def2 by (typecheck_cfuncs, auto)

  have fa_type[type_rule]: "f \<circ>\<^sub>c a : A \<rightarrow> Y"
    by (typecheck_cfuncs)

  obtain p0 where p0_def[simp]: "p0 = fibered_product_left_proj A (f\<circ>\<^sub>ca) (f\<circ>\<^sub>ca) A"
    by auto
  obtain p1 where p1_def[simp]: "p1 = fibered_product_right_proj A (f\<circ>\<^sub>ca) (f\<circ>\<^sub>ca) A"
    by auto
  obtain E where E_def[simp]: "E = A \<^bsub>f \<circ>\<^sub>c a\<^esub>\<times>\<^sub>c\<^bsub>f \<circ>\<^sub>c a\<^esub> A"
    by auto

  have fa_coequalizes: "(f \<circ>\<^sub>c a) \<circ>\<^sub>c p0 = (f \<circ>\<^sub>c a) \<circ>\<^sub>c p1"
    using fa_type fibered_product_proj_eq by auto
  have ga_coequalizes: "(g \<circ>\<^sub>c a) \<circ>\<^sub>c p0 = (g \<circ>\<^sub>c a) \<circ>\<^sub>c p1"
  proof -
    from fa_coequalizes have "n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c p0) = n \<circ>\<^sub>c ((g \<circ>\<^sub>c a) \<circ>\<^sub>c p1)"
      by (auto, typecheck_cfuncs, auto simp add: f_eq_ng comp_associative2)
    then show "(g \<circ>\<^sub>c a) \<circ>\<^sub>c p0 = (g \<circ>\<^sub>c a) \<circ>\<^sub>c p1"
      using n_mono unfolding monomorphism_def2
      by (auto, typecheck_cfuncs_prems, meson)
  qed

  thm image_rest_map_coequalizer[where A=A, where n=a, where f=f, where X=X, where Y=Y]

  have "(\<forall>h F. h : A \<rightarrow> F \<and> h \<circ>\<^sub>c p0 = h \<circ>\<^sub>c p1 \<longrightarrow> (\<exists>!k. k : f[A]\<^bsub>a\<^esub> \<rightarrow> F \<and> k \<circ>\<^sub>c f\<restriction>\<^bsub>(A, a)\<^esub> = h))"
    using image_rest_map_coequalizer[where n=a] unfolding coequalizer_def 
    by (simp, typecheck_cfuncs, auto simp add: cfunc_type_def)
  then obtain k where k_type[type_rule]: "k : f[A]\<^bsub>a\<^esub> \<rightarrow> B" and k_e_eq_g: "k \<circ>\<^sub>c f\<restriction>\<^bsub>(A, a)\<^esub> = g \<circ>\<^sub>c a"
    using ga_coequalizes by (typecheck_cfuncs, blast)

  then have "n \<circ>\<^sub>c k = [f[A]\<^bsub>a\<^esub>]map"
    by (typecheck_cfuncs, smt (z3) comp_associative2 f_eq_ng g_type image_rest_map_type image_subobj_map_unique k_e_eq_g)
  then show "(f[A]\<^bsub>a\<^esub>, [f[A]\<^bsub>a\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B, n)"
    unfolding relative_subset_def2 using n_mono image_subobj_map_mono
    by (typecheck_cfuncs, auto, rule_tac x=k in exI, typecheck_cfuncs)
qed

lemma images_iso:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes m_type[type_rule]: "m : Z \<rightarrow> X" and n_type[type_rule]: "n : A \<rightarrow> Z" 
  shows "(f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub> \<cong> f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>"
proof -
  have f_m_image_coequalizer:
    "coequalizer ((f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>) ((f \<circ>\<^sub>c m)\<restriction>\<^bsub>(A, n)\<^esub>) 
      (fibered_product_left_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A) 
      (fibered_product_right_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A)"
    by (typecheck_cfuncs, smt comp_associative2 image_restriction_mapping_def2)

  have f_image_coequalizer:
    "coequalizer (f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>) (f\<restriction>\<^bsub>(A, m \<circ>\<^sub>c n)\<^esub>) 
      (fibered_product_left_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A) 
      (fibered_product_right_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A)"
    by (typecheck_cfuncs, smt comp_associative2 image_restriction_mapping_def2)

  from f_m_image_coequalizer f_image_coequalizer
  show "(f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub> \<cong> f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>"
    by (meson coequalizer_unique)
qed

lemma image_subset_conv:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes m_type[type_rule]: "m : Z \<rightarrow> X" and n_type[type_rule]: "n : A \<rightarrow> Z" 
  shows "\<exists>i. ((f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>, i) \<subseteq>\<^sub>c B \<Longrightarrow> \<exists>j. (f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>, j) \<subseteq>\<^sub>c B"
proof -
  assume "\<exists>i. ((f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>, i) \<subseteq>\<^sub>c B"
  then obtain i where
    i_type[type_rule]: "i : (f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub> \<rightarrow> B" and
    i_mono: "monomorphism i"
    unfolding subobject_of_def by force

  have "(f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub> \<cong> f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>"
    using f_type images_iso m_type n_type by blast
  then obtain k where
    k_type[type_rule]: "k : f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub> \<rightarrow> (f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>" and
    k_mono: "monomorphism k"
    by (meson is_isomorphic_def iso_imp_epi_and_monic isomorphic_is_symmetric)
  then show "\<exists>j. (f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>, j) \<subseteq>\<^sub>c B"
    unfolding subobject_of_def using composition_of_monic_pair_is_monic i_mono
    by (rule_tac x="i \<circ>\<^sub>c k" in exI, typecheck_cfuncs, simp add: cfunc_type_def)
qed

lemma 
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes m_type[type_rule]: "m : Z \<rightarrow> X" and n_type[type_rule]: "n : A \<rightarrow> Z"
  shows "\<exists>i. i : f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub> \<rightarrow> (f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub> \<and> [(f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>]map \<circ>\<^sub>c i = [f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>]map"
  oops
  

lemma image_rel_subset_conv:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes m_type[type_rule]: "m : Z \<rightarrow> X" and n_type[type_rule]: "n : A \<rightarrow> Z"
  assumes rel_sub1: "((f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>, [(f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B,b)"
  shows "(f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>, [f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B,b)"
  using rel_sub1 image_subobj_map_mono
  unfolding relative_subset_def2
proof (typecheck_cfuncs, auto)
  fix k
  assume k_type[type_rule]: "k : (f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub> \<rightarrow> B"
  assume b_type[type_rule]: "b : B \<rightarrow> Y"
  assume b_mono: "monomorphism b"
  assume b_k_eq_map: "b \<circ>\<^sub>c k = [(f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>]map"

  have f_m_image_coequalizer:
    "coequalizer ((f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>) ((f \<circ>\<^sub>c m)\<restriction>\<^bsub>(A, n)\<^esub>) 
      (fibered_product_left_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A) 
      (fibered_product_right_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A)"
    by (typecheck_cfuncs, smt comp_associative2 image_restriction_mapping_def2)
  then have f_m_image_coequalises: 
      "(f \<circ>\<^sub>c m)\<restriction>\<^bsub>(A, n)\<^esub> \<circ>\<^sub>c fibered_product_left_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A
        = (f \<circ>\<^sub>c m)\<restriction>\<^bsub>(A, n)\<^esub> \<circ>\<^sub>c fibered_product_right_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A"
    by (typecheck_cfuncs_prems, unfold coequalizer_def2, auto)

  have f_image_coequalizer:
    "coequalizer (f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>) (f\<restriction>\<^bsub>(A, m \<circ>\<^sub>c n)\<^esub>) 
      (fibered_product_left_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A) 
      (fibered_product_right_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A)"
    by (typecheck_cfuncs, smt comp_associative2 image_restriction_mapping_def2)
  then have "\<And> h F. h : A \<rightarrow> F \<Longrightarrow>
           h \<circ>\<^sub>c fibered_product_left_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A =
           h \<circ>\<^sub>c fibered_product_right_proj A (f \<circ>\<^sub>c m \<circ>\<^sub>c n) (f \<circ>\<^sub>c m \<circ>\<^sub>c n) A \<Longrightarrow>
           (\<exists>!k. k : f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub> \<rightarrow> F \<and> k \<circ>\<^sub>c f\<restriction>\<^bsub>(A, m \<circ>\<^sub>c n)\<^esub> = h)"
    by (typecheck_cfuncs_prems, unfold coequalizer_def2, auto)
  then have "\<exists>!k. k : f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub> \<rightarrow> (f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub> \<and> k \<circ>\<^sub>c f\<restriction>\<^bsub>(A, m \<circ>\<^sub>c n)\<^esub> = (f \<circ>\<^sub>c m)\<restriction>\<^bsub>(A, n)\<^esub>"
    using f_m_image_coequalises by (typecheck_cfuncs, presburger)
  then obtain k' where 
    k'_type[type_rule]: "k' : f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub> \<rightarrow> (f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>" and
    k'_eq: "k' \<circ>\<^sub>c f\<restriction>\<^bsub>(A, m \<circ>\<^sub>c n)\<^esub> = (f \<circ>\<^sub>c m)\<restriction>\<^bsub>(A, n)\<^esub>"
    by auto

  have k'_maps_eq: "[f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>]map = [(f \<circ>\<^sub>c m)[A]\<^bsub>n\<^esub>]map \<circ>\<^sub>c k'"
    by (typecheck_cfuncs, smt (z3) comp_associative2 image_subobject_mapping_def2 k'_eq)

  
  have k_mono: "monomorphism k"
    by (metis b_k_eq_map cfunc_type_def comp_monic_imp_monic k_type rel_sub1 relative_subset_def2)
  have k'_mono: "monomorphism k'"
    by (smt (verit, ccfv_SIG) cfunc_type_def comp_monic_imp_monic comp_type f_type image_subobject_mapping_def2 k'_maps_eq k'_type m_type n_type)

  show "\<exists>k. k : f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub> \<rightarrow> B \<and> b \<circ>\<^sub>c k = [f[A]\<^bsub>m \<circ>\<^sub>c n\<^esub>]map"
    by (rule_tac x="k \<circ>\<^sub>c k'" in exI, typecheck_cfuncs, simp add: b_k_eq_map comp_associative2 k'_maps_eq)
qed




(*I think this might be false... just consider {0} and {0,1} *)
lemma subsets_off_by_iso:
  assumes "(A,a) \<subseteq>\<^sub>c X" "(A,b) \<subseteq>\<^sub>c X"
  shows "\<exists> i. isomorphism(i) \<and> i \<circ>\<^sub>c a = b"
  oops


(*We might be able to upgrade the lemma below by getting rid of i on the RHS below.*)

(* Proposition 2.3.9 *)
lemma subset_inv_image_iff_image_subset:
  assumes "(A,a) \<subseteq>\<^sub>c X" "(B,m) \<subseteq>\<^sub>c Y" 
  assumes[type_rule]: "f : X \<rightarrow> Y"
  shows "((A, a) \<subseteq>\<^bsub>X\<^esub> (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>,[f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map)) = ((f[A]\<^bsub>a\<^esub>, [f[A]\<^bsub>a\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B,m))"
proof auto

  (*Facts about m_star, denoted m' *)
  thm inverse_image_subobject_mapping_type[where f=f, where X = X, where Y=Y,where m=m, where B=B]
  have b_mono: "monomorphism(m)"
    using assms(2) subobject_of_def2 by blast
  have b_type[type_rule]: "m : B  \<rightarrow> Y"
    using assms(2) subobject_of_def2 by blast
  obtain m' where m'_def: "m' = [f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map"
    by blast
  then have m'_type[type_rule]: "m' : f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<rightarrow> X"
    using assms(3) b_mono inverse_image_subobject_mapping_type m'_def by (typecheck_cfuncs, force)

  assume "(A, a) \<subseteq>\<^bsub>X\<^esub> (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>, [f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map)"
  then have a_type[type_rule]: "a : A \<rightarrow> X" and
    a_mono: "monomorphism a" and
    k_exists: "\<exists>k. k : A \<rightarrow> f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<and> [f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map \<circ>\<^sub>c k = a"
    unfolding relative_subset_def2 by auto
  then obtain k where k_type[type_rule]: "k : A \<rightarrow> f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>" and k_a_eq: "[f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map \<circ>\<^sub>c k = a"
    by auto

  obtain d where d_def: "d = m' \<circ>\<^sub>c k"
    by simp

  (*Facts about j *)
  obtain j where j_def: "j = [f[A]\<^bsub>d\<^esub>]map"
    by simp
  then have j_type[type_rule]: "j : f[A]\<^bsub>d\<^esub> \<rightarrow> Y"
    using assms(3) comp_type d_def m'_type image_subobj_map_type k_type by presburger



  (*Facts about e*)
  obtain e where e_def: "e = f\<restriction>\<^bsub>(A, d)\<^esub>"
    by simp
  then have e_type[type_rule]: "e : A \<rightarrow> f[A]\<^bsub>d\<^esub>"
    using assms(3) comp_type d_def image_rest_map_type k_type m'_type by blast

  have je_equals: "j \<circ>\<^sub>c e = f \<circ>\<^sub>c m' \<circ>\<^sub>c k"
    by (typecheck_cfuncs, simp add: d_def e_def image_subobj_comp_image_rest j_def)

  have "(f \<circ>\<^sub>c m' \<circ>\<^sub>c k) factorsthru m"
  proof(typecheck_cfuncs, unfold factors_through_def2) 

    obtain middle_arrow where middle_arrow_def: 
      "middle_arrow = (right_cart_proj X B) \<circ>\<^sub>c (inverse_image_mapping f B m)"
      by simp

    then have middle_arrow_type[type_rule]: "middle_arrow : f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<rightarrow> B"
      unfolding middle_arrow_def using b_mono by (typecheck_cfuncs)

    show "\<exists>h. h : A \<rightarrow> B \<and> m \<circ>\<^sub>c h = f \<circ>\<^sub>c m' \<circ>\<^sub>c k"
      by (rule_tac x="middle_arrow \<circ>\<^sub>c k" in exI, typecheck_cfuncs, 
          simp add: b_mono cfunc_type_def comp_associative2 inverse_image_mapping_eq inverse_image_subobject_mapping_def m'_def middle_arrow_def)
  qed

  thm image_smallest_subobject[where f="f \<circ>\<^sub>c (m' \<circ>\<^sub>c k)", where n=m, where X=A, where Y=Y,
      where A=A, where a="id A", where B=B]
  then have "((f \<circ>\<^sub>c m' \<circ>\<^sub>c k)[A]\<^bsub>id\<^sub>c A\<^esub>, [(f \<circ>\<^sub>c m' \<circ>\<^sub>c k)[A]\<^bsub>id\<^sub>c A\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B, m)"
    by (typecheck_cfuncs, meson assms(2) image_smallest_subobject)
  then have "((f \<circ>\<^sub>c a)[A]\<^bsub>id\<^sub>c A\<^esub>, [(f \<circ>\<^sub>c a)[A]\<^bsub>id\<^sub>c A\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B, m)"
    by (simp add: k_a_eq m'_def)   
  then show "(f[A]\<^bsub>a\<^esub>, [f[A]\<^bsub>a\<^esub>]map)\<subseteq>\<^bsub>Y\<^esub>(B, m)"
    by (typecheck_cfuncs, metis id_right_unit2 id_type image_rel_subset_conv)
next
  have m_mono: "monomorphism(m)"
    using assms(2) subobject_of_def2 by blast
  have m_type[type_rule]: "m : B  \<rightarrow> Y"
    using assms(2) subobject_of_def2 by blast

  assume "(f[A]\<^bsub>a\<^esub>, [f[A]\<^bsub>a\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (B, m)"
  then obtain s where 
      s_type[type_rule]: "s : f[A]\<^bsub>a\<^esub> \<rightarrow> B" and
      m_s_eq_subobj_map: "m \<circ>\<^sub>c s = [f[A]\<^bsub>a\<^esub>]map"
    unfolding relative_subset_def2 by auto

  have a_mono: "monomorphism a"
    using assms(1) unfolding subobject_of_def2 by auto

  have pullback_map1_type[type_rule]: "s \<circ>\<^sub>c f\<restriction>\<^bsub>(A, a)\<^esub> : A \<rightarrow> B"
    using assms(1) unfolding subobject_of_def2 by (auto, typecheck_cfuncs)
  have pullback_map2_type[type_rule]: "a : A \<rightarrow> X"
    using assms(1) unfolding subobject_of_def2 by auto
  have pullback_maps_commute: "m \<circ>\<^sub>c s \<circ>\<^sub>c f\<restriction>\<^bsub>(A, a)\<^esub> = f \<circ>\<^sub>c a"
    by (typecheck_cfuncs, simp add: comp_associative2 image_subobj_comp_image_rest m_s_eq_subobj_map)

  have "\<And>Z k h. k : Z \<rightarrow> B \<Longrightarrow> h : Z \<rightarrow> X \<Longrightarrow> m \<circ>\<^sub>c k = f \<circ>\<^sub>c h \<Longrightarrow>
     (\<exists>!j. j : Z \<rightarrow> f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<and>
           (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = k \<and>
           (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = h)"
    using inverse_image_pullback assms(3) m_mono m_type unfolding is_pullback_def by simp
  then obtain k where k_type[type_rule]: "k : A \<rightarrow> f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>" and
    k_right_eq: "(right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c k = s \<circ>\<^sub>c f\<restriction>\<^bsub>(A, a)\<^esub>" and
    k_left_eq: "(left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c k = a"
    using pullback_map1_type pullback_map2_type pullback_maps_commute by blast

  have "monomorphism ((left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c k) \<Longrightarrow> monomorphism k"
    using comp_monic_imp_monic' m_mono by (typecheck_cfuncs, blast)
  then have "monomorphism k"
    by (simp add: a_mono k_left_eq)
  then show "(A, a)\<subseteq>\<^bsub>X\<^esub>(f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>, [f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map)"
    unfolding relative_subset_def2 
    using assms a_mono m_mono inverse_image_subobject_mapping_mono
  proof (typecheck_cfuncs, auto)
    assume "monomorphism k"
    then show "\<exists>k. k : A \<rightarrow> f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<and> [f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map \<circ>\<^sub>c k = a"
      using assms(3) inverse_image_subobject_mapping_def2 k_left_eq k_type 
      by (rule_tac x=k in exI, force)
  qed
qed

(* Exercise 2.3.10 *)
lemma in_inv_image_of_image:
  assumes "(A,m) \<subseteq>\<^sub>c X" 
  assumes[type_rule]: "f : X \<rightarrow> Y"
  shows "(A,m) \<subseteq>\<^bsub>X\<^esub> (f\<^sup>-\<^sup>1[f[A]\<^bsub>m\<^esub>]\<^bsub>[f[A]\<^bsub>m\<^esub>]map\<^esub>, [f\<^sup>-\<^sup>1[f[A]\<^bsub>m\<^esub>]\<^bsub>[f[A]\<^bsub>m\<^esub>]map\<^esub>]map)"
proof -
  have m_type[type_rule]: "m : A \<rightarrow> X"
    using assms(1) unfolding subobject_of_def2 by auto
  have m_mono: "monomorphism m"
    using assms(1) unfolding subobject_of_def2 by auto

  have "((f[A]\<^bsub>m\<^esub>, [f[A]\<^bsub>m\<^esub>]map) \<subseteq>\<^bsub>Y\<^esub> (f[A]\<^bsub>m\<^esub>, [f[A]\<^bsub>m\<^esub>]map))"
    unfolding relative_subset_def2
    using m_mono image_subobj_map_mono id_right_unit2 id_type by (typecheck_cfuncs, blast)
  then show "(A,m) \<subseteq>\<^bsub>X\<^esub> (f\<^sup>-\<^sup>1[f[A]\<^bsub>m\<^esub>]\<^bsub>[f[A]\<^bsub>m\<^esub>]map\<^esub>, [f\<^sup>-\<^sup>1[f[A]\<^bsub>m\<^esub>]\<^bsub>[f[A]\<^bsub>m\<^esub>]map\<^esub>]map)"
    by (meson assms relative_subset_def2 subobject_of_def2 subset_inv_image_iff_image_subset)
qed


(*

lemma iso_to_mono_image:
  assumes f_type[type_rule]: "f : X \<rightarrow> Y"
  assumes f_mono: "monomorphism f"
  assumes  n_type[type_rule]: "n : Z \<rightarrow> X"
  shows "f[A]\<^bsub>n\<^esub> \<cong> A"
  using assms apply typecheck_cfuncs

*)



lemma left_pair_subset:
  assumes "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
  shows "(Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z)) \<subseteq>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
  unfolding subobject_of_def2 using assms
proof (typecheck_cfuncs, unfold monomorphism_def3, auto)
  fix g h A
  assume g_type: "g : A \<rightarrow> Y \<times>\<^sub>c Z"
  assume h_type: "h : A \<rightarrow> Y \<times>\<^sub>c Z"

  assume "(distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z)) \<circ>\<^sub>c g = (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h"
  then have "distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c g = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h"
    using assms g_type h_type by (typecheck_cfuncs, simp add: comp_associative2)
  then have "(m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c g = (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h"
    using assms g_type h_type distribute_right_mono distribute_right_type monomorphism_def2
    by (typecheck_cfuncs, blast)
  then show "g = h"
  proof -
    have "monomorphism (m \<times>\<^sub>f id\<^sub>c Z)"
      using assms cfunc_cross_prod_mono id_isomorphism id_type iso_imp_epi_and_monic by blast
    then show "(m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c g = (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h \<Longrightarrow> g = h"
      using assms g_type h_type unfolding monomorphism_def2 by (typecheck_cfuncs, blast)
  qed
qed

lemma right_pair_subset:
  assumes "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
  shows "(Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<subseteq>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)"
  unfolding subobject_of_def2 using assms
proof (typecheck_cfuncs, unfold monomorphism_def3, auto)
  fix g h A
  assume g_type: "g : A \<rightarrow> Z \<times>\<^sub>c Y"
  assume h_type: "h : A \<rightarrow> Z \<times>\<^sub>c Y"

  assume "(distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c g = (distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c h"
  then have "distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c g = distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c h"
    using assms g_type h_type by (typecheck_cfuncs, simp add: comp_associative2)
  then have "(id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c g = (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c h"
    using assms g_type h_type distribute_left_mono distribute_left_type monomorphism_def2
    by (typecheck_cfuncs, blast)
  then show "g = h"
  proof -
    have "monomorphism (id\<^sub>c Z \<times>\<^sub>f m)"
      using assms cfunc_cross_prod_mono id_isomorphism id_type iso_imp_epi_and_monic by blast
    then show "(id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c g = (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c h \<Longrightarrow> g = h"
      using assms g_type h_type unfolding monomorphism_def2 by (typecheck_cfuncs, blast)
  qed
qed




lemma reflexive_def2:
  assumes reflexive_Y: "reflexive_on X (Y, m)"
  assumes x_type: "x \<in>\<^sub>c X" 
  shows "\<exists>y. y \<in>\<^sub>c Y \<and>  m \<circ>\<^sub>c y = \<langle>x,x\<rangle>"
  using assms unfolding reflexive_on_def relative_member_def factors_through_def2
proof -
    assume a1: "(Y, m) \<subseteq>\<^sub>c X \<times>\<^sub>c X \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> \<langle>x,x\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X \<and> monomorphism (snd (Y, m)) \<and> snd (Y, m) : fst (Y, m) \<rightarrow> X \<times>\<^sub>c X \<and> \<langle>x,x\<rangle> factorsthru snd (Y, m))"
    have xx_type: "\<langle>x,x\<rangle> \<in>\<^sub>c X \<times>\<^sub>c X"
      by (typecheck_cfuncs, simp add: x_type)
    have "\<langle>x,x\<rangle> factorsthru m"
      using a1 x_type by auto
    then show ?thesis
      using a1 xx_type cfunc_type_def factors_through_def subobject_of_def2 by force
  qed

lemma symmetric_def2:
  assumes symmetric_Y: "symmetric_on X (Y, m)"
  assumes x_type: "x \<in>\<^sub>c X"
  assumes y_type: "y \<in>\<^sub>c X"
  assumes relation: "\<exists>v. v \<in>\<^sub>c Y \<and>  m \<circ>\<^sub>c v = \<langle>x,y\<rangle>"
  shows "\<exists>w. w \<in>\<^sub>c Y \<and>  m \<circ>\<^sub>c w = \<langle>y,x\<rangle>"
  using assms unfolding symmetric_on_def relative_member_def factors_through_def2
  by (metis cfunc_prod_type factors_through_def2 fst_conv snd_conv subobject_of_def2)

lemma transitive_def2:
  assumes transitive_Y: "transitive_on X (Y, m)"
  assumes x_type: "x \<in>\<^sub>c X"
  assumes y_type: "y \<in>\<^sub>c X"
  assumes z_type: "z \<in>\<^sub>c X"
  assumes relation1: "\<exists>v. v \<in>\<^sub>c Y \<and>  m \<circ>\<^sub>c v = \<langle>x,y\<rangle>"
  assumes relation2: "\<exists>w. w \<in>\<^sub>c Y \<and>  m \<circ>\<^sub>c w = \<langle>y,z\<rangle>"
  shows "\<exists>u. u \<in>\<^sub>c Y \<and>  m \<circ>\<^sub>c u = \<langle>x,z\<rangle>"
  using assms unfolding transitive_on_def relative_member_def factors_through_def2
  by (metis cfunc_prod_type factors_through_def2 fst_conv snd_conv subobject_of_def2)


   
lemma left_pair_reflexive:
  assumes "reflexive_on X (Y, m)"
  shows "reflexive_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z))"
proof (unfold reflexive_on_def, auto)
  have "m : Y \<rightarrow> X \<times>\<^sub>c X \<and> monomorphism m"
    using assms unfolding reflexive_on_def subobject_of_def2 by auto
  then show "(Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<subseteq>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z"
    by (simp add: left_pair_subset)
next
  fix xz
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X"
    using assms unfolding reflexive_on_def subobject_of_def2 by auto
  assume xz_type: "xz \<in>\<^sub>c X \<times>\<^sub>c Z"
  then obtain x z where x_type: "x \<in>\<^sub>c X" and z_type: "z \<in>\<^sub>c Z" and xz_def: "xz = \<langle>x, z\<rangle>"
    using cart_prod_decomp by blast
  then show "\<langle>xz,xz\<rangle> \<in>\<^bsub>(X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z\<^esub> (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
    using m_type
  proof (auto, typecheck_cfuncs, unfold relative_member_def2, auto)
    have "monomorphism m"
      using assms unfolding reflexive_on_def subobject_of_def2 by auto
    then show "monomorphism (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      using  cfunc_cross_prod_mono cfunc_type_def composition_of_monic_pair_is_monic distribute_right_mono id_isomorphism iso_imp_epi_and_monic m_type by (typecheck_cfuncs, auto)
  next
    have xzxz_type: "\<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z"
      using xz_type cfunc_prod_type xz_def by blast
    obtain y where y_def: "y \<in>\<^sub>c Y" "m \<circ>\<^sub>c y = \<langle>x, x\<rangle>"
      using assms reflexive_def2 x_type by blast
    have mid_type: "m \<times>\<^sub>f id\<^sub>c Z : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c X) \<times>\<^sub>c Z"
      by (simp add: cfunc_cross_prod_type id_type m_type)
    have dist_mid_type:"distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z"
      using comp_type distribute_right_type mid_type by force

    have yz_type: "\<langle>y,z\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z"
      by (typecheck_cfuncs, simp add: \<open>z \<in>\<^sub>c Z\<close> y_def)
    have "(distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>y,z\<rangle>  = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,z\<rangle>"
      using comp_associative2 mid_type yz_type by (typecheck_cfuncs, auto)
    also have "...  =  distribute_right X X Z \<circ>\<^sub>c  \<langle>m \<circ>\<^sub>c y,id(Z) \<circ>\<^sub>c z\<rangle>"
      using z_type cfunc_cross_prod_comp_cfunc_prod m_type y_def by (typecheck_cfuncs, auto)
    also have distxxz: "... = distribute_right X X Z \<circ>\<^sub>c  \<langle> \<langle>x, x\<rangle>, z\<rangle>"
      using z_type id_left_unit2 y_def by auto
    also have "... = \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle>"
      by (meson z_type distribute_right_ap x_type)
    then have "\<exists>h. \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle> = (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h"
      by (metis  calculation)
    then show "\<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle> factorsthru (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      using  xzxz_type z_type distribute_right_ap x_type dist_mid_type calculation factors_through_def2 yz_type by auto
  qed
qed

lemma right_pair_reflexive:
  assumes "reflexive_on X (Y, m)"
  shows "reflexive_on (Z \<times>\<^sub>c X) (Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
proof (unfold reflexive_on_def, auto)
  have "m : Y \<rightarrow> X \<times>\<^sub>c X \<and> monomorphism m"
    using assms unfolding reflexive_on_def subobject_of_def2 by auto
  then show "(Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<subseteq>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X"
    by (simp add: right_pair_subset)
  next
  fix zx
  have m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X"
    using assms unfolding reflexive_on_def subobject_of_def2 by auto
  assume zx_type: "zx \<in>\<^sub>c Z \<times>\<^sub>c X"
  then obtain z x where x_type: "x \<in>\<^sub>c X" and z_type: "z \<in>\<^sub>c Z" and zx_def: "zx = \<langle>z, x\<rangle>"
    using cart_prod_decomp by blast
  then show "\<langle>zx,zx\<rangle> \<in>\<^bsub>(Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X\<^esub> (Z \<times>\<^sub>c Y, distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
    using m_type
  proof (auto, typecheck_cfuncs, unfold relative_member_def2, auto)
    have "monomorphism m"
      using assms unfolding reflexive_on_def subobject_of_def2 by auto
    then show "monomorphism (distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
      using  cfunc_cross_prod_mono cfunc_type_def composition_of_monic_pair_is_monic distribute_left_mono id_isomorphism iso_imp_epi_and_monic m_type by (typecheck_cfuncs, auto)
  next
    have zxzx_type: "\<langle>\<langle>z,x\<rangle>,\<langle>z,x\<rangle>\<rangle> \<in>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X"
      using zx_type cfunc_prod_type zx_def by blast
    obtain y where y_def: "y \<in>\<^sub>c Y" "m \<circ>\<^sub>c y = \<langle>x, x\<rangle>"
      using assms reflexive_def2 x_type by blast
        have mid_type: "(id\<^sub>c Z \<times>\<^sub>f m) : Z \<times>\<^sub>c Y \<rightarrow>   Z \<times>\<^sub>c (X \<times>\<^sub>c X)"
      by (simp add: cfunc_cross_prod_type id_type m_type)
    have dist_mid_type:"distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) : Z \<times>\<^sub>c Y \<rightarrow> (Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X"
      using comp_type distribute_left_type mid_type by force

    have yz_type: "\<langle>z,y\<rangle> \<in>\<^sub>c Z \<times>\<^sub>c Y"
      by (typecheck_cfuncs, simp add: \<open>z \<in>\<^sub>c Z\<close> y_def)
    have "(distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y\<rangle>  = distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y\<rangle>"
      using comp_associative2 mid_type yz_type by (typecheck_cfuncs, auto)
    also have "...  =  distribute_left Z X X  \<circ>\<^sub>c  \<langle>id\<^sub>c Z \<circ>\<^sub>c z , m \<circ>\<^sub>c y \<rangle>"
      using z_type cfunc_cross_prod_comp_cfunc_prod m_type y_def by (typecheck_cfuncs, auto)
    also have distxxz: "... = distribute_left Z X X  \<circ>\<^sub>c  \<langle>z, \<langle>x, x\<rangle>\<rangle>"
      using z_type id_left_unit2 y_def by auto
    also have "... = \<langle>\<langle>z,x\<rangle>,\<langle>z,x\<rangle>\<rangle>"
      by (meson z_type distribute_left_ap x_type)
    then have "\<exists>h. \<langle>\<langle>z,x\<rangle>,\<langle>z,x\<rangle>\<rangle> = (distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c h"
      by (metis  calculation)
    then show "\<langle>\<langle>z,x\<rangle>,\<langle>z,x\<rangle>\<rangle> factorsthru (distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
      using z_type distribute_left_ap x_type calculation dist_mid_type factors_through_def2 yz_type zxzx_type by auto
  qed
qed

lemma subsets_off_by_iso:
  assumes "(A,a) \<subseteq>\<^sub>c X" "(A,b) \<subseteq>\<^sub>c X"
  shows "\<exists> i. isomorphism(i) \<and> i \<circ>\<^sub>c a = b"
  oops

(*
(*We might be able to upgrade the lemma below by getting rid of i on the RHS below.*)

(* Proposition 2.3.9 *)
lemma subset_inv_image_iff_image_subset:
  assumes "(A,a) \<subseteq>\<^sub>c X" "(B,m) \<subseteq>\<^sub>c Y" 
  assumes[type_rule]: "f : X \<rightarrow> Y"
  shows "(\<exists> k. (A, k) \<subseteq>\<^sub>c (f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>)) = (\<exists> j. (f[A]\<^bsub>a\<^esub>, j) \<subseteq>\<^sub>c B)"
proof auto

    (*Facts about m_star, denoted m' *)
    thm inverse_image_subobject_mapping_type[where f=f, where X = X, where Y=Y,where m=m, where B=B]
    have b_mono: "monomorphism(m)"
      using assms(2) subobject_of_def2 by blast
    have b_type[type_rule]: "m : B  \<rightarrow> Y"
      using assms(2) subobject_of_def2 by blast
    obtain m' where m'_def: "m' = [f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>]map"
      by blast
    then have m'_type[type_rule]: "m' : f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<rightarrow> X"
      using assms(3) b_mono inverse_image_subobject_mapping_type m'_def by (typecheck_cfuncs, force)

  show "\<And>k. (A, k) \<subseteq>\<^sub>c f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<Longrightarrow> \<exists>j. (f[A]\<^bsub>a\<^esub>, j) \<subseteq>\<^sub>c B"
  proof - 
    fix k 
    assume "(A, k) \<subseteq>\<^sub>c f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>"
    then have k_type[type_rule]: "k : A \<rightarrow> f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>"
      using  subobject_of_def2 by blast

    obtain d where d_def: "d = m' \<circ>\<^sub>c k"
      by simp

    (*Facts about j *)
    obtain j where j_def: "j = [f[A]\<^bsub>d\<^esub>]map"
      by simp
    then have j_type[type_rule]: "j : f[A]\<^bsub>d\<^esub> \<rightarrow> Y"
      using assms(3) comp_type d_def m'_type image_subobject_mapping_type k_type by presburger



    (*Facts about e*)
    obtain e where e_def: "e = f\<restriction>\<^bsub>(A, d)\<^esub>"
      by simp
    then have e_type[type_rule]: "e : A \<rightarrow> f[A]\<^bsub>d\<^esub>"
      using assms(3) comp_type d_def image_restriction_mapping_type k_type m'_type by blast

    have je_equals: "j \<circ>\<^sub>c e = f \<circ>\<^sub>c m' \<circ>\<^sub>c k"
      by (typecheck_cfuncs, metis assms(3) d_def e_def image_subobject_mapping_def2 j_def)

    have "(f \<circ>\<^sub>c m' \<circ>\<^sub>c k) factorsthru m"
    proof(typecheck_cfuncs, unfold factors_through_def2) 

      obtain middle_arrow where middle_arrow_def: 
        "middle_arrow = (right_cart_proj X B) \<circ>\<^sub>c (inverse_image_mapping f B m)"
        by simp

      then have middle_arrow_type[type_rule]: "middle_arrow : f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub> \<rightarrow> B"
        unfolding middle_arrow_def using b_mono by (typecheck_cfuncs)

      show "\<exists>h. h : A \<rightarrow> B \<and> m \<circ>\<^sub>c h = f \<circ>\<^sub>c m' \<circ>\<^sub>c k"
        by (rule_tac x="middle_arrow \<circ>\<^sub>c k" in exI, typecheck_cfuncs, 
            simp add: b_mono cfunc_type_def comp_associative2 inverse_image_mapping_eq inverse_image_subobject_mapping_def m'_def middle_arrow_def)
    qed

    have "\<exists>i. ((f \<circ>\<^sub>c (m' \<circ>\<^sub>c k))[A]\<^bsub>id A\<^esub>, i) \<subseteq>\<^sub>c B"
      by (metis \<open>(f \<circ>\<^sub>c m' \<circ>\<^sub>c k) factorsthru m\<close> assms(2) assms(3) cfunc_type_def codomain_comp domain_comp id_type image_smallest_subobject k_type m'_type)

    then have "\<exists>j. (f[A]\<^bsub> m' \<circ>\<^sub>c k\<^esub>, j) \<subseteq>\<^sub>c B"
      by (typecheck_cfuncs, metis id_right_unit2 id_type image_subset_conv)

    then show "\<exists>i j. (f[A]\<^bsub>i\<^esub>, j) \<subseteq>\<^sub>c B"
      by blast
  next
    show "\<And>i j. (f[A]\<^bsub>i\<^esub>, j) \<subseteq>\<^sub>c B \<Longrightarrow> \<exists>k. (A, k) \<subseteq>\<^sub>c f\<^sup>-\<^sup>1[B]\<^bsub>m\<^esub>"
      oops





      thm image_smallest_subobject[where f = "f \<circ>\<^sub>c m' \<circ>\<^sub>c k", where X = "(f \<circ>\<^sub>c m' \<circ>\<^sub>c k)[A]\<^bsub>a\<^esub>", where Y = Y, where a=a, where A = A,
          where B = B, where n = m]
*)



(*Definition 2.3.11*)
(*
definition functional :: "cset  \<times> cfunc \<Rightarrow> bool" where
  "functional R = (\<exists> X Y. R \<subseteq>\<^sub>c (X\<times>\<^sub>c Y) \<and> 
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<exists> y. (y \<in>\<^sub>c Y \<and> (\<langle>x,y\<rangle> \<in> R)))))"

Not sure how to define the above! *)

definition functional_on :: "cset \<Rightarrow> cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" where
  "functional_on X Y R = (R  \<subseteq>\<^sub>c X \<times>\<^sub>c Y \<and>
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (\<exists>! y.  y \<in>\<^sub>c Y \<and>  
      (\<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cY\<^esub> R))))" 


(*Definition 2.3.12*)

definition graph :: "cfunc \<Rightarrow> cset" where
 "graph f = (SOME E. \<exists> m. equalizer E m (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f)))"

lemma graph_equalizer:
  "\<exists> m. equalizer (graph f) m (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f))"
  by (unfold graph_def, typecheck_cfuncs, rule_tac someI_ex, simp add: cfunc_type_def equalizer_exists)
  
lemma graph_equalizer2:
  assumes "f : X \<rightarrow> Y"
  shows "\<exists> m. equalizer (graph f) m (f \<circ>\<^sub>c left_cart_proj X Y) (right_cart_proj X Y)"
  using assms by (typecheck_cfuncs, metis cfunc_type_def graph_equalizer)


definition graph_morph :: "cfunc \<Rightarrow> cfunc" where
 "graph_morph f = (SOME m. equalizer (graph f) m (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f)))"

lemma graph_equalizer3:
  "equalizer (graph f) (graph_morph f) (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f)) (right_cart_proj (domain f) (codomain f))"
   using graph_equalizer by (unfold graph_morph_def, typecheck_cfuncs, rule_tac someI_ex, blast)

lemma graph_equalizer4:
  assumes "f : X \<rightarrow> Y"
  shows "equalizer (graph f) (graph_morph f) (f \<circ>\<^sub>c left_cart_proj X Y) (right_cart_proj X Y)"
  using assms cfunc_type_def graph_equalizer3 by auto


lemma graph_subobject:
  assumes "f : X \<rightarrow> Y"
  shows "(graph f, graph_morph f)  \<subseteq>\<^sub>c (X\<times>\<^sub>c Y)"
  by (metis assms cfunc_type_def equalizer_def equalizer_is_monomorphism graph_equalizer3 right_cart_proj_type subobject_of_def2)



(*Exercise 2.3.13*)
lemma graphs_are_functional:
  assumes "f : X \<rightarrow> Y"
  shows "functional_on X Y (graph f, graph_morph f)"
proof(unfold functional_on_def, auto)
  show graph_subobj: "(graph f, graph_morph f)  \<subseteq>\<^sub>c (X\<times>\<^sub>c Y)"
    by (simp add: assms graph_subobject)
  show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> \<exists>y. y \<in>\<^sub>c Y \<and> \<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f)"
  proof - 
    fix x 
    assume x_type[type_rule]: "x \<in>\<^sub>c X"
    obtain y where y_def: "y = f \<circ>\<^sub>c x"
      by simp
    then have y_type[type_rule]: "y \<in>\<^sub>c Y"
      using assms comp_type x_type y_def by blast

    have "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f)"
    proof(unfold relative_member_def, auto)
      show "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y"
        by typecheck_cfuncs 
      show "monomorphism (graph_morph f)"
        using graph_subobj subobject_of_def2 by blast
      show "graph_morph f : graph f \<rightarrow> X \<times>\<^sub>c Y"
        using graph_subobj subobject_of_def2 by blast
      show "\<langle>x,y\<rangle> factorsthru graph_morph f"
      proof(subst xfactorthru_equalizer_iff_fx_eq_gx[where E = "graph f", where m = "graph_morph f", where 
f = "(f \<circ>\<^sub>c left_cart_proj X Y)", where g = "right_cart_proj X Y", where X = "X \<times>\<^sub>c Y", where Y = Y,
where x ="\<langle>x,y\<rangle>"])
        show "f \<circ>\<^sub>c left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y"
          using assms by typecheck_cfuncs
        show "right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y"
          by  typecheck_cfuncs
        show "equalizer (graph f) (graph_morph f) (f \<circ>\<^sub>c left_cart_proj X Y) (right_cart_proj X Y)"
          by (simp add: assms graph_equalizer4)
        show "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y"
          by typecheck_cfuncs
        show "(f \<circ>\<^sub>c left_cart_proj X Y) \<circ>\<^sub>c \<langle>x,y\<rangle> = right_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>"
          using assms  
          by (typecheck_cfuncs, smt (z3) comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod y_def)
      qed
    qed
    then show "\<exists>y. y \<in>\<^sub>c Y \<and> \<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f)"
      using y_type by blast
  qed
  show "\<And>x y ya.
       x \<in>\<^sub>c X \<Longrightarrow>
       y \<in>\<^sub>c Y \<Longrightarrow>
       \<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f) \<Longrightarrow> ya \<in>\<^sub>c Y \<Longrightarrow> \<langle>x,ya\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (graph f, graph_morph f) \<Longrightarrow> y = ya"
    using assms  
    by (smt (z3) comp_associative2 equalizer_def factors_through_def2 graph_equalizer4 left_cart_proj_cfunc_prod left_cart_proj_type relative_member_def2 right_cart_proj_cfunc_prod)
qed




(*Proposition 2.3.14*)


lemma functional_relations_are_graphs_isomorphism_clause:
  assumes "functional_on X Y (R,m)"
  shows "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
proof-
  have m_mono: "monomorphism(m)"
    using assms functional_on_def subobject_of_def2 by blast
  have pi0_m_type[type_rule]: "left_cart_proj X Y \<circ>\<^sub>c m : R \<rightarrow> X"
    using assms functional_on_def subobject_of_def2 by (typecheck_cfuncs, blast)
  have surj: "surjective(left_cart_proj X Y \<circ>\<^sub>c m)"
  proof(unfold surjective_def, auto)
    fix x 
    assume "x \<in>\<^sub>c codomain (left_cart_proj X Y \<circ>\<^sub>c m)"
    then have [type_rule]: "x \<in>\<^sub>c X"
      using cfunc_type_def pi0_m_type by force
    then have "\<exists>! y. (y \<in>\<^sub>c Y \<and>  \<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cY\<^esub> (R,m))"
      using assms functional_on_def  by force
    then show "\<exists>z. z \<in>\<^sub>c domain (left_cart_proj X Y \<circ>\<^sub>c m) \<and> (left_cart_proj X Y \<circ>\<^sub>c m) \<circ>\<^sub>c z = x"
      by (typecheck_cfuncs, smt (verit, best) cfunc_type_def comp_associative factors_through_def2 left_cart_proj_cfunc_prod relative_member_def2)
  qed
  have inj: "injective(left_cart_proj X Y \<circ>\<^sub>c m)"
  proof(unfold injective_def, auto)
    fix r1 r2 
    assume "r1 \<in>\<^sub>c domain (left_cart_proj X Y \<circ>\<^sub>c m)" then have r1_type[type_rule]: "r1 \<in>\<^sub>c R"
      by (metis cfunc_type_def pi0_m_type)
    assume "r2 \<in>\<^sub>c domain (left_cart_proj X Y \<circ>\<^sub>c m)" then have r2_type[type_rule]: "r2 \<in>\<^sub>c R"
      by (metis cfunc_type_def pi0_m_type)
    assume "(left_cart_proj X Y \<circ>\<^sub>c m) \<circ>\<^sub>c r1 = (left_cart_proj X Y \<circ>\<^sub>c m) \<circ>\<^sub>c r2"
    then have eq: "left_cart_proj X Y \<circ>\<^sub>c m \<circ>\<^sub>c r1 = left_cart_proj X Y \<circ>\<^sub>c m \<circ>\<^sub>c r2"
      using assms cfunc_type_def comp_associative functional_on_def subobject_of_def2 by (typecheck_cfuncs, auto)
    have mx_type[type_rule]: "m \<circ>\<^sub>c r1 \<in>\<^sub>c X\<times>\<^sub>cY"
      using assms functional_on_def subobject_of_def2 by (typecheck_cfuncs, blast)
    then obtain x1 and y1 where m1r1_eqs: "m \<circ>\<^sub>c r1 = \<langle>x1, y1\<rangle> \<and> x1 \<in>\<^sub>c X \<and> y1 \<in>\<^sub>c Y"
      using cart_prod_decomp by presburger
    have my_type[type_rule]: "m \<circ>\<^sub>c r2 \<in>\<^sub>c X\<times>\<^sub>cY"
      using assms functional_on_def subobject_of_def2 by (typecheck_cfuncs, blast)
    then obtain x2 and y2 where m2r2_eqs:"m \<circ>\<^sub>c r2 = \<langle>x2, y2\<rangle> \<and> x2 \<in>\<^sub>c X \<and> y2 \<in>\<^sub>c Y"
      using cart_prod_decomp by presburger
    have x_equal: "x1 = x2"
      using eq left_cart_proj_cfunc_prod m1r1_eqs m2r2_eqs by force
    have functional: "\<exists>! y. (y \<in>\<^sub>c Y \<and>  \<langle>x1,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cY\<^esub> (R,m))"
      using assms functional_on_def m1r1_eqs by force
    then have y_equal: "y1 = y2"
      by (metis prod.sel factors_through_def2 m1r1_eqs m2r2_eqs mx_type my_type r1_type r2_type relative_member_def x_equal)
    then show "r1 = r2"
      by (metis functional cfunc_type_def m1r1_eqs m2r2_eqs monomorphism_def r1_type r2_type relative_member_def2 x_equal)
  qed
  show "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
    by (metis epi_mon_is_iso inj injective_imp_monomorphism mem_Collect_eq surj surjective_is_epimorphism)
qed




(*It seems that we have that IF the graph exists then it is unique, and we have by the above that it is an isomorphism.
Is there a better way to state this?*)



lemma functional_relations_are_graphs_uniqueness_clause:
  assumes "functional_on X Y (R,m)"
  assumes "\<exists> f. (f : X \<rightarrow> Y \<and> (R,m) = (graph f, graph_morph f))"
  shows "\<exists>! f. (f : X \<rightarrow> Y \<and> (R,m) = (graph f, graph_morph f))"
proof(auto)
  show "\<exists>f. f : X \<rightarrow> Y \<and> R = graph f \<and> m = graph_morph f"
    using assms(2) by blast
  show "\<And>f g. f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> m = graph_morph g \<Longrightarrow> R = graph g \<Longrightarrow> graph f = graph g \<Longrightarrow> graph_morph f = graph_morph g \<Longrightarrow> f = g"
  proof-
    fix f g
    assume f_type[type_rule]: "f : X \<rightarrow> Y"
    assume g_type[type_rule]: "g : X \<rightarrow> Y"
    assume m_def: "m = graph_morph g"
    assume R_def: "R = graph g"
    assume equal_graphs: "graph f = graph g"
    assume equal_morphs: "graph_morph f = graph_morph g"
    have f1: "f \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m = right_cart_proj X Y \<circ>\<^sub>c m"
      by (typecheck_cfuncs, smt (verit) comp_associative2 equal_morphs equalizer_def graph_equalizer4 graph_subobject m_def subobject_of_def2)
    have f2: "g \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m = right_cart_proj X Y \<circ>\<^sub>c m"
      by (typecheck_cfuncs, smt (verit) comp_associative2 equal_morphs equalizer_def graph_equalizer4 graph_subobject m_def subobject_of_def2)
    have f3: "f \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m = g \<circ>\<^sub>c left_cart_proj X Y \<circ>\<^sub>c m"
      by (simp add: f1 f2)
    have "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
      using assms(1) functional_relations_are_graphs_isomorphism_clause by auto
    then show "f = g"
      using assms(1) cfunc_type_def codomain_comp epimorphism_def f3 f_type functional_on_def g_type iso_imp_epi_and_monic left_cart_proj_type subobject_of_def2 by force
  qed
qed








lemma functional_relations_are_graphs:
  assumes "functional_on X Y (R,m)"
  shows "\<exists>! f. (f : X \<rightarrow> Y \<and> (R,m) = (graph f, graph_morph f))"
proof(auto)
  have m_mono: "monomorphism(m)"
    using assms functional_on_def subobject_of_def2 by blast
  have pi0_m_type[type_rule]: "left_cart_proj X Y \<circ>\<^sub>c m : R \<rightarrow> X"
    using assms functional_on_def subobject_of_def2 by (typecheck_cfuncs, blast)
  have isomorphism: "isomorphism(left_cart_proj X Y \<circ>\<^sub>c m)"
    using assms functional_relations_are_graphs_isomorphism_clause by force

  show "\<And>f y. f : X \<rightarrow> Y \<Longrightarrow>
           y : X \<rightarrow> Y \<Longrightarrow>
           m = graph_morph y \<Longrightarrow> R = graph y \<Longrightarrow> graph f = graph y \<Longrightarrow> graph_morph f = graph_morph y \<Longrightarrow> f = y"
    by (metis assms functional_relations_are_graphs_uniqueness_clause)
  
  obtain h where h_type[type_rule]: "h: X \<rightarrow> R" and h_iso: "isomorphism(h)"
    by (meson is_isomorphic_def isomorphic_is_symmetric isomorphism pi0_m_type)
  obtain f where f_def: "f = (right_cart_proj X Y) \<circ>\<^sub>c m \<circ>\<^sub>c h"
    by auto
  then have f_type[type_rule]: "f : X \<rightarrow> Y"
    by (metis assms comp_type f_def functional_on_def h_type right_cart_proj_type subobject_of_def2)

  show "\<exists>f. f : X \<rightarrow> Y \<and> R = graph f \<and> m = graph_morph f"
  proof (rule_tac x=f in exI, auto)
    show "f : X \<rightarrow> Y"
      by (simp add: f_type)
    show "m = graph_morph f"

  oops

(*I think at this point the best we can say is that R \<cong> graph f*)
(*In particular how do you make equality with a "SOME" ?*)


(*
  have "R = graph f \<and> m = graph_morph f"
  proof(unfold graph_def, unfold graph_morph_def, auto)
    show "R =
    (SOME E.
        \<exists>m. equalizer E m (f \<circ>\<^sub>c left_cart_proj (domain f) (codomain f))
             (right_cart_proj (domain f) (codomain f)))"
      oops
*)






lemma left_pair_symmetric:
  assumes "symmetric_on X (Y, m)"
  shows "symmetric_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z))"
proof (unfold symmetric_on_def, auto)
  have "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 symmetric_on_def by auto
  then show "(Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<subseteq>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z"
    by (simp add: left_pair_subset)
next
  have m_def[type_rule]: "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 symmetric_on_def by auto

  fix s t 
  assume s_type[type_rule]: "s \<in>\<^sub>c X \<times>\<^sub>c Z"
  assume t_type[type_rule]: "t \<in>\<^sub>c X \<times>\<^sub>c Z"
  assume st_relation: "\<langle>s,t\<rangle> \<in>\<^bsub>(X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z\<^esub> (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
  
  obtain sx sz where s_def[type_rule]: " sx \<in>\<^sub>c X" "sz \<in>\<^sub>c Z" "s =  \<langle>sx,sz\<rangle>"
    using cart_prod_decomp s_type by blast
  obtain tx tz where t_def[type_rule]: "tx \<in>\<^sub>c X" "tz \<in>\<^sub>c Z" "t =  \<langle>tx,tz\<rangle>"
    using cart_prod_decomp t_type by blast 

  show "\<langle>t,s\<rangle> \<in>\<^bsub>(X \<times>\<^sub>c Z) \<times>\<^sub>c (X \<times>\<^sub>c Z)\<^esub> (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z))" 
    using s_def t_def m_def
  proof (simp, typecheck_cfuncs, auto, unfold relative_member_def2, auto)
    show "monomorphism (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      using relative_member_def2 st_relation by blast

    have "\<langle>\<langle>sx,sz\<rangle>, \<langle>tx,tz\<rangle>\<rangle> factorsthru (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      using st_relation s_def t_def unfolding relative_member_def2 by auto
    then obtain yz where yz_type[type_rule]: "yz \<in>\<^sub>c Y \<times>\<^sub>c Z"
      and yz_def: "(distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z)) \<circ>\<^sub>c yz = \<langle>\<langle>sx,sz\<rangle>, \<langle>tx,tz\<rangle>\<rangle>"
      using s_def t_def m_def by (typecheck_cfuncs, unfold factors_through_def2, auto)
    then obtain y z where
      y_type[type_rule]: "y \<in>\<^sub>c Y" and z_type[type_rule]: "z \<in>\<^sub>c Z" and yz_pair: "yz = \<langle>y, z\<rangle>"
      using cart_prod_decomp by blast
    then obtain my1 my2 where my_types[type_rule]: "my1 \<in>\<^sub>c X" "my2 \<in>\<^sub>c X" and my_def: "m \<circ>\<^sub>c y = \<langle>my1,my2\<rangle>"
      by (metis cart_prod_decomp cfunc_type_def codomain_comp domain_comp m_def(1))
    then obtain y' where y'_type[type_rule]: "y' \<in>\<^sub>c Y" and y'_def: "m \<circ>\<^sub>c y' = \<langle>my2,my1\<rangle>"
      using assms symmetric_def2 y_type by blast

    have "(distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z)) \<circ>\<^sub>c yz = \<langle>\<langle>my1,z\<rangle>, \<langle>my2,z\<rangle>\<rangle>"
    proof -
      have "(distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z)) \<circ>\<^sub>c yz = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>y, z\<rangle>"
        unfolding yz_pair by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = distribute_right X X Z \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c y, id\<^sub>c Z \<circ>\<^sub>c z\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      also have "... = distribute_right X X Z \<circ>\<^sub>c \<langle>\<langle>my1,my2\<rangle>, z\<rangle>"
        unfolding my_def by (typecheck_cfuncs, simp add: id_left_unit2)
      also have "... = \<langle>\<langle>my1,z\<rangle>, \<langle>my2,z\<rangle>\<rangle>"
        using distribute_right_ap by (typecheck_cfuncs, auto)
      then show ?thesis
        using calculation by auto
    qed   
    then have "\<langle>\<langle>sx,sz\<rangle>,\<langle>tx,tz\<rangle>\<rangle> = \<langle>\<langle>my1,z\<rangle>,\<langle>my2,z\<rangle>\<rangle>"
      using yz_def by auto
    then have "\<langle>sx,sz\<rangle> = \<langle>my1,z\<rangle> \<and> \<langle>tx,tz\<rangle> = \<langle>my2,z\<rangle>"
      using element_pair_eq by (typecheck_cfuncs, auto)
    then have eqs: "sx = my1 \<and> sz = z \<and> tx = my2 \<and> tz = z"
      using element_pair_eq by (typecheck_cfuncs, auto)

    have "(distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z)) \<circ>\<^sub>c \<langle>y',z\<rangle> = \<langle>\<langle>tx,tz\<rangle>, \<langle>sx,sz\<rangle>\<rangle>"
    proof -
      have "(distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z)) \<circ>\<^sub>c \<langle>y',z\<rangle> = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>y',z\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = distribute_right X X Z \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c y',id\<^sub>c Z \<circ>\<^sub>c z\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      also have "... = distribute_right X X Z \<circ>\<^sub>c \<langle>\<langle>my2,my1\<rangle>, z\<rangle>"
        unfolding y'_def by (typecheck_cfuncs, simp add: id_left_unit2)
      also have "... = \<langle>\<langle>my2,z\<rangle>, \<langle>my1,z\<rangle>\<rangle>"
        using distribute_right_ap by (typecheck_cfuncs, auto)
      also have "... = \<langle>\<langle>tx,tz\<rangle>, \<langle>sx,sz\<rangle>\<rangle>"
        using eqs by auto
      then show ?thesis
        using calculation by auto
    qed
    then show "\<langle>\<langle>tx,tz\<rangle>,\<langle>sx,sz\<rangle>\<rangle> factorsthru (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      by (typecheck_cfuncs, unfold factors_through_def2, rule_tac x="\<langle>y',z\<rangle>" in exI, typecheck_cfuncs)
  qed
qed

lemma right_pair_symmetric:
  assumes "symmetric_on X (Y, m)"
  shows "symmetric_on (Z \<times>\<^sub>c X) (Z \<times>\<^sub>c Y, distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
proof (unfold symmetric_on_def, auto)
  have "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 symmetric_on_def by auto
  then show "(Z \<times>\<^sub>c Y, distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<subseteq>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X"
    by (simp add: right_pair_subset)
next
  have m_def[type_rule]: "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 symmetric_on_def by auto

  fix s t 
  assume s_type[type_rule]: "s \<in>\<^sub>c Z \<times>\<^sub>c X"
  assume t_type[type_rule]: "t \<in>\<^sub>c Z \<times>\<^sub>c X"
  assume st_relation: "\<langle>s,t\<rangle> \<in>\<^bsub>(Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X\<^esub> (Z \<times>\<^sub>c Y, distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
  
  obtain xs zs where s_def[type_rule]: " xs \<in>\<^sub>c Z" "zs \<in>\<^sub>c X" "s =  \<langle>xs,zs\<rangle>"
    using cart_prod_decomp s_type by blast
  obtain xt zt where t_def[type_rule]: "xt \<in>\<^sub>c Z" "zt \<in>\<^sub>c X" "t =  \<langle>xt,zt\<rangle>"
    using cart_prod_decomp t_type by blast 

  show "\<langle>t,s\<rangle> \<in>\<^bsub>(Z \<times>\<^sub>c X) \<times>\<^sub>c (Z \<times>\<^sub>c X)\<^esub> (Z \<times>\<^sub>c Y, distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))" 
    using s_def t_def m_def
  proof (simp, typecheck_cfuncs, auto, unfold relative_member_def2, auto)
    show "monomorphism (distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
      using relative_member_def2 st_relation by blast

    have "\<langle>\<langle>xs,zs\<rangle>, \<langle>xt,zt\<rangle>\<rangle> factorsthru (distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
      using st_relation s_def t_def unfolding relative_member_def2 by auto
    then obtain zy where zy_type[type_rule]: "zy \<in>\<^sub>c Z \<times>\<^sub>c Y"
      and zy_def: "(distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c zy = \<langle>\<langle>xs,zs\<rangle>, \<langle>xt,zt\<rangle>\<rangle>"
      using s_def t_def m_def by (typecheck_cfuncs, unfold factors_through_def2, auto)
    then obtain y z where
      y_type[type_rule]: "y \<in>\<^sub>c Y" and z_type[type_rule]: "z \<in>\<^sub>c Z" and yz_pair: "zy = \<langle>z, y\<rangle>"
      using cart_prod_decomp by blast
    then obtain my1 my2 where my_types[type_rule]: "my1 \<in>\<^sub>c X" "my2 \<in>\<^sub>c X" and my_def: "m \<circ>\<^sub>c y = \<langle>my2,my1\<rangle>"
      by (metis cart_prod_decomp cfunc_type_def codomain_comp domain_comp m_def(1))
    then obtain y' where y'_type[type_rule]: "y' \<in>\<^sub>c Y" and y'_def: "m \<circ>\<^sub>c y' = \<langle>my1,my2\<rangle>"
      using assms symmetric_def2 y_type by blast

    have "(distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c zy = \<langle>\<langle>z,my2\<rangle>, \<langle>z,my1\<rangle>\<rangle>"
    proof -
      have "(distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c zy = distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c zy"
        unfolding yz_pair by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = distribute_left Z X X  \<circ>\<^sub>c \<langle>id\<^sub>c Z \<circ>\<^sub>c z , m \<circ>\<^sub>c y\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod yz_pair)
      also have "... = distribute_left Z X X  \<circ>\<^sub>c \<langle>z , \<langle>my2,my1\<rangle>\<rangle>"
        unfolding my_def by (typecheck_cfuncs, simp add: id_left_unit2)
      also have "... = \<langle>\<langle>z,my2\<rangle>, \<langle>z,my1\<rangle>\<rangle>"
        using distribute_left_ap by (typecheck_cfuncs, auto)
      then show ?thesis
        using calculation by auto
    qed   
    then have "\<langle>\<langle>xs,zs\<rangle>,\<langle>xt,zt\<rangle>\<rangle> = \<langle>\<langle>z,my2\<rangle>,\<langle>z,my1\<rangle>\<rangle>"
      using zy_def by auto
    then have "\<langle>xs,zs\<rangle> = \<langle>z,my2\<rangle> \<and> \<langle>xt,zt\<rangle> = \<langle>z, my1\<rangle>"
      using element_pair_eq by (typecheck_cfuncs, auto)
    then have eqs: "xs = z \<and> zs = my2 \<and> xt = z \<and> zt = my1"
      using element_pair_eq by (typecheck_cfuncs, auto)

    have "(distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y'\<rangle> = \<langle>\<langle>xt,zt\<rangle>, \<langle>xs,zs\<rangle>\<rangle>"
    proof -
      have "(distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>z,y'\<rangle> = distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>z,y'\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = distribute_left Z X X \<circ>\<^sub>c \<langle>id\<^sub>c Z \<circ>\<^sub>c z, m \<circ>\<^sub>c y'\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      also have "... = distribute_left Z X X \<circ>\<^sub>c \<langle>z, \<langle>my1,my2\<rangle>\<rangle>"
        unfolding y'_def by (typecheck_cfuncs, simp add: id_left_unit2)
      also have "... = \<langle>\<langle>z,my1\<rangle>, \<langle>z,my2\<rangle>\<rangle>"
        using distribute_left_ap by (typecheck_cfuncs, auto)
      also have "... = \<langle>\<langle>xt,zt\<rangle>, \<langle>xs,zs\<rangle>\<rangle>"
        using eqs by auto
      then show ?thesis
        using calculation by auto
    qed
    then show "\<langle>\<langle>xt,zt\<rangle>,\<langle>xs,zs\<rangle>\<rangle> factorsthru (distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
      by (typecheck_cfuncs, unfold factors_through_def2, rule_tac x="\<langle>z,y'\<rangle>" in exI, typecheck_cfuncs)
  qed
qed

lemma left_pair_transitive:
  assumes "transitive_on X (Y, m)"
  shows "transitive_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z))"
proof (unfold transitive_on_def, auto)
  have "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 transitive_on_def by auto
  then show "(Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<subseteq>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z"
    by (simp add: left_pair_subset)
next
  have m_def[type_rule]: "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 transitive_on_def by auto

  fix s t u
  assume s_type[type_rule]: "s \<in>\<^sub>c X \<times>\<^sub>c Z"
  assume t_type[type_rule]: "t \<in>\<^sub>c X \<times>\<^sub>c Z"
  assume u_type[type_rule]: "u \<in>\<^sub>c X \<times>\<^sub>c Z"

  assume st_relation: "\<langle>s,t\<rangle> \<in>\<^bsub>(X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z\<^esub> (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
  then obtain h where h_type[type_rule]: "h \<in>\<^sub>c Y \<times>\<^sub>c Z" and h_def: "(distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h = \<langle>s,t\<rangle>"
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
  then obtain hy hz where h_part_types[type_rule]: "hy \<in>\<^sub>c Y" "hz \<in>\<^sub>c Z" and h_decomp: "h = \<langle>hy, hz\<rangle>"
    using cart_prod_decomp by blast
  then obtain mhy1 mhy2 where mhy_types[type_rule]: "mhy1 \<in>\<^sub>c X" "mhy2 \<in>\<^sub>c X" and mhy_decomp:  "m \<circ>\<^sub>c hy = \<langle>mhy1, mhy2\<rangle>"
    using cart_prod_decomp by (typecheck_cfuncs, blast)

  have "\<langle>s,t\<rangle> = \<langle>\<langle>mhy1, hz\<rangle>, \<langle>mhy2, hz\<rangle>\<rangle>"
  proof -
    have "\<langle>s,t\<rangle> = (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>hy, hz\<rangle>"
      using h_decomp h_def by auto
    also have "... = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>hy, hz\<rangle>"
      by (typecheck_cfuncs, auto simp add: comp_associative2)
    also have "... = distribute_right X X Z \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c hy, hz\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
    also have "... = \<langle>\<langle>mhy1, hz\<rangle>, \<langle>mhy2, hz\<rangle>\<rangle>"
      unfolding mhy_decomp by (typecheck_cfuncs, simp add: distribute_right_ap)
    then show ?thesis
      using calculation by auto
  qed
  then have s_def: "s = \<langle>mhy1, hz\<rangle>" and t_def: "t = \<langle>mhy2, hz\<rangle>"
    using cart_prod_eq2 by (typecheck_cfuncs, auto, presburger)

  assume tu_relation: "\<langle>t,u\<rangle> \<in>\<^bsub>(X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z\<^esub> (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
  then obtain g where g_type[type_rule]: "g \<in>\<^sub>c Y \<times>\<^sub>c Z" and g_def: "(distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c g = \<langle>t,u\<rangle>"
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
  then obtain gy gz where g_part_types[type_rule]: "gy \<in>\<^sub>c Y" "gz \<in>\<^sub>c Z" and g_decomp: "g = \<langle>gy, gz\<rangle>"
    using cart_prod_decomp by blast
  then obtain mgy1 mgy2 where mgy_types[type_rule]: "mgy1 \<in>\<^sub>c X" "mgy2 \<in>\<^sub>c X" and mgy_decomp:  "m \<circ>\<^sub>c gy = \<langle>mgy1, mgy2\<rangle>"
    using cart_prod_decomp by (typecheck_cfuncs, blast)

  have "\<langle>t,u\<rangle> = \<langle>\<langle>mgy1, gz\<rangle>, \<langle>mgy2, gz\<rangle>\<rangle>"
  proof -
    have "\<langle>t,u\<rangle> = (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>gy, gz\<rangle>"
      using g_decomp g_def by auto
    also have "... = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>gy, gz\<rangle>"
      by (typecheck_cfuncs, auto simp add: comp_associative2)
    also have "... = distribute_right X X Z \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c gy, gz\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
    also have "... = \<langle>\<langle>mgy1, gz\<rangle>, \<langle>mgy2, gz\<rangle>\<rangle>"
      unfolding mgy_decomp by (typecheck_cfuncs, simp add: distribute_right_ap)
    then show ?thesis
      using calculation by auto
  qed
  then have t_def2: "t = \<langle>mgy1, gz\<rangle>" and u_def: "u = \<langle>mgy2, gz\<rangle>"
    using cart_prod_eq2 by (typecheck_cfuncs, auto, presburger)

  have mhy2_eq_mgy1: "mhy2 = mgy1"
    using t_def2 t_def cart_prod_eq2 by (auto, typecheck_cfuncs)
  have gy_eq_gz: "hz = gz"
    using t_def2 t_def cart_prod_eq2 by (auto, typecheck_cfuncs)

  have mhy_in_Y: "\<langle>mhy1, mhy2\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (Y, m)"
    using m_def h_part_types mhy_decomp
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
  have mgy_in_Y: "\<langle>mhy2, mgy2\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (Y, m)"
    using m_def g_part_types mgy_decomp mhy2_eq_mgy1
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)

  have "\<langle>mhy1, mgy2\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (Y, m)"
    using assms mhy_in_Y mgy_in_Y mgy_types mhy2_eq_mgy1 unfolding transitive_on_def
    by (typecheck_cfuncs, blast)
  then obtain y where y_type[type_rule]: "y \<in>\<^sub>c Y" and y_def: "m \<circ>\<^sub>c y = \<langle>mhy1, mgy2\<rangle>"
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)

  show " \<langle>s,u\<rangle> \<in>\<^bsub>(X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z\<^esub> (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z))" 
  proof (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
    show "monomorphism (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      using relative_member_def2 st_relation by blast

    show "\<exists>h. h \<in>\<^sub>c Y \<times>\<^sub>c Z \<and> (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h = \<langle>s,u\<rangle>"
      unfolding s_def u_def gy_eq_gz
    proof (rule_tac x="\<langle>y,gz\<rangle>" in exI, auto, typecheck_cfuncs)
      have "(distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>y,gz\<rangle> = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>y,gz\<rangle>"
        by (typecheck_cfuncs, auto simp add: comp_associative2)
      also have "... = distribute_right X X Z \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c y, gz\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
      also have "... = \<langle>\<langle>mhy1,gz\<rangle>,\<langle>mgy2,gz\<rangle>\<rangle>"
        unfolding y_def by (typecheck_cfuncs, simp add: distribute_right_ap)
      then show "(distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>y,gz\<rangle> = \<langle>\<langle>mhy1,gz\<rangle>,\<langle>mgy2,gz\<rangle>\<rangle>"
        using calculation by auto
    qed
  qed
qed

lemma right_pair_transitive:
  assumes "transitive_on X (Y, m)"
  shows "transitive_on (Z \<times>\<^sub>c X) (Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m))"
proof (unfold transitive_on_def, auto)
  have "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 transitive_on_def by auto
  then show "(Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m) \<subseteq>\<^sub>c (Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X"
    by (simp add: right_pair_subset)
next
  have m_def[type_rule]: "m : Y \<rightarrow> X \<times>\<^sub>c X" "monomorphism m"
    using assms subobject_of_def2 transitive_on_def by auto

  fix s t u
  assume s_type[type_rule]: "s \<in>\<^sub>c Z \<times>\<^sub>c X"
  assume t_type[type_rule]: "t \<in>\<^sub>c Z \<times>\<^sub>c X"
  assume u_type[type_rule]: "u \<in>\<^sub>c Z \<times>\<^sub>c X"

  assume st_relation: "\<langle>s,t\<rangle> \<in>\<^bsub>(Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X\<^esub> (Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m)"
  then obtain h where h_type[type_rule]: "h \<in>\<^sub>c Z \<times>\<^sub>c Y" and h_def: "(distribute_left Z X X  \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c h = \<langle>s,t\<rangle>"
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
  then obtain hy hz where h_part_types[type_rule]: "hy \<in>\<^sub>c Y" "hz \<in>\<^sub>c Z" and h_decomp: "h = \<langle>hz, hy\<rangle>"
    using cart_prod_decomp by blast
  then obtain mhy1 mhy2 where mhy_types[type_rule]: "mhy1 \<in>\<^sub>c X" "mhy2 \<in>\<^sub>c X" and mhy_decomp:  "m \<circ>\<^sub>c hy = \<langle>mhy1, mhy2\<rangle>"
    using cart_prod_decomp by (typecheck_cfuncs, blast)

  have "\<langle>s,t\<rangle> = \<langle>\<langle>hz, mhy1\<rangle>, \<langle>hz, mhy2\<rangle>\<rangle>"
  proof -
    have "\<langle>s,t\<rangle> = (distribute_left Z X X  \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>hz, hy\<rangle>"
      using h_decomp h_def by auto
    also have "... = distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>hz, hy\<rangle>"
      by (typecheck_cfuncs, auto simp add: comp_associative2)
    also have "... = distribute_left Z X X  \<circ>\<^sub>c \<langle> hz, m \<circ>\<^sub>c hy\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
    also have "... = \<langle>\<langle>hz, mhy1\<rangle>, \<langle>hz, mhy2\<rangle>\<rangle>"
      unfolding mhy_decomp by (typecheck_cfuncs, simp add: distribute_left_ap)
    then show ?thesis
      using calculation by auto
  qed
  then have s_def: "s = \<langle>hz, mhy1\<rangle>" and t_def: "t = \<langle>hz, mhy2\<rangle>"
    using cart_prod_eq2 by (typecheck_cfuncs, auto, presburger)

  assume tu_relation: "\<langle>t,u\<rangle> \<in>\<^bsub>(Z \<times>\<^sub>c X) \<times>\<^sub>c
               Z \<times>\<^sub>c X\<^esub> (Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m)"
  then obtain g where g_type[type_rule]: "g \<in>\<^sub>c Z \<times>\<^sub>c Y" and g_def: "(distribute_left Z X X  \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c g = \<langle>t,u\<rangle>"
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
  then obtain gy gz where g_part_types[type_rule]: "gy \<in>\<^sub>c Y" "gz \<in>\<^sub>c Z" and g_decomp: "g = \<langle>gz, gy\<rangle>"
    using cart_prod_decomp by blast
  then obtain mgy1 mgy2 where mgy_types[type_rule]: "mgy1 \<in>\<^sub>c X" "mgy2 \<in>\<^sub>c X" and mgy_decomp:  "m \<circ>\<^sub>c gy = \<langle>mgy2, mgy1\<rangle>"
    using cart_prod_decomp by (typecheck_cfuncs, blast)

  have "\<langle>t,u\<rangle> = \<langle>\<langle>gz, mgy2\<rangle>, \<langle>gz, mgy1\<rangle>\<rangle>"
  proof -
    have "\<langle>t,u\<rangle> = (distribute_left Z X X  \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz, gy\<rangle>"
      using g_decomp g_def by auto
    also have "... = distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz, gy\<rangle>"
      by (typecheck_cfuncs, auto simp add: comp_associative2)
    also have "... = distribute_left Z X X  \<circ>\<^sub>c \<langle>gz, m \<circ>\<^sub>c gy\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
    also have "... = \<langle>\<langle>gz, mgy2\<rangle>, \<langle>gz, mgy1\<rangle>\<rangle>"
      unfolding mgy_decomp by (typecheck_cfuncs, simp add: distribute_left_ap)
    then show ?thesis
      using calculation by auto
  qed
  then have t_def2: "t = \<langle>gz, mgy2\<rangle>" and u_def: "u = \<langle>gz, mgy1\<rangle>"
    using cart_prod_eq2 by (typecheck_cfuncs, auto, presburger)



  have mhy2_eq_mgy2: "mhy2 = mgy2"
    using t_def2 t_def cart_prod_eq2 by (auto, typecheck_cfuncs)
  have gy_eq_gz: "hz = gz"
    using t_def2 t_def cart_prod_eq2 by (auto, typecheck_cfuncs)

  have mhy_in_Y: "\<langle>mhy1, mhy2\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (Y, m)"
    using m_def h_part_types mhy_decomp
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
  have mgy_in_Y: "\<langle>mhy2, mgy1\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (Y, m)"
    using m_def g_part_types mgy_decomp mhy2_eq_mgy2
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)

  have "\<langle>mhy1, mgy1\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (Y, m)"
    using assms mhy_in_Y mgy_in_Y mgy_types mhy2_eq_mgy2 unfolding transitive_on_def
    by (typecheck_cfuncs, blast)
  then obtain y where y_type[type_rule]: "y \<in>\<^sub>c Y" and y_def: "m \<circ>\<^sub>c y = \<langle>mhy1, mgy1\<rangle>"
    by (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)

  show " \<langle>s,u\<rangle> \<in>\<^bsub>(Z \<times>\<^sub>c X) \<times>\<^sub>c Z \<times>\<^sub>c X\<^esub> (Z \<times>\<^sub>c Y, distribute_left Z X X \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m)" 
  proof (typecheck_cfuncs, unfold relative_member_def2 factors_through_def2, auto)
    show "monomorphism (distribute_left Z X X \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m)"
      using relative_member_def2 st_relation by blast

    show "\<exists>h. h \<in>\<^sub>c Z \<times>\<^sub>c Y \<and> (distribute_left Z X X \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c h = \<langle>s,u\<rangle>"
      unfolding s_def u_def gy_eq_gz
    proof (rule_tac x="\<langle>gz,y\<rangle>" in exI, auto, typecheck_cfuncs)
      have "(distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m)) \<circ>\<^sub>c \<langle>gz,y\<rangle> = distribute_left Z X X  \<circ>\<^sub>c (id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz,y\<rangle>"
        by (typecheck_cfuncs, auto simp add: comp_associative2)
      also have "... = distribute_left Z X X  \<circ>\<^sub>c \<langle>gz, m \<circ>\<^sub>c y\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
      also have "... = \<langle>\<langle>gz,mhy1\<rangle>,\<langle>gz,mgy1\<rangle>\<rangle>"
        by (typecheck_cfuncs, simp add: distribute_left_ap y_def)
      then show "(distribute_left Z X X \<circ>\<^sub>c id\<^sub>c Z \<times>\<^sub>f m) \<circ>\<^sub>c \<langle>gz,y\<rangle> = \<langle>\<langle>gz,mhy1\<rangle>,\<langle>gz,mgy1\<rangle>\<rangle>"
        using calculation by auto
    qed
  qed
qed


lemma left_pair_equiv_rel:
  assumes "equiv_rel_on X (Y, m)"
  shows "equiv_rel_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id Z))"
  using assms left_pair_reflexive left_pair_symmetric left_pair_transitive
  by (unfold equiv_rel_on_def, auto)

lemma right_pair_equiv_rel:
  assumes "equiv_rel_on X (Y, m)"
  shows "equiv_rel_on (Z \<times>\<^sub>c X) (Z \<times>\<^sub>c Y, distribute_left Z X X  \<circ>\<^sub>c (id Z \<times>\<^sub>f m))"
  using assms right_pair_reflexive right_pair_symmetric right_pair_transitive
  by (unfold equiv_rel_on_def, auto)




end