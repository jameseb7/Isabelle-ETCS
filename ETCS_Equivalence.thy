theory ETCS_Equivalence
  imports ETCS_Truth
begin

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

(*Proposition 2.3.2*) 
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
  assume "xz \<in>\<^sub>c X \<times>\<^sub>c Z"
  then obtain x z where x_type: "x \<in>\<^sub>c X" and "z \<in>\<^sub>c Z" and xz_def: "xz = \<langle>x, z\<rangle>"
    using cart_prod_decomp by blast
  then show "\<langle>xz,xz\<rangle> \<in>\<^bsub>(X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z\<^esub> (Y \<times>\<^sub>c Z, distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
    using m_type
  proof (auto, typecheck_cfuncs, unfold relative_member_def2, auto)
    have "monomorphism m"
      using assms unfolding reflexive_on_def subobject_of_def2 by auto
    then show "monomorphism (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      oops

(*lemma left_pair_equiv_rel:
  assumes "equiv_rel_on X (Y, m)"
  shows "equiv_rel_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, m \<times>\<^sub>f id Z)"
proof (unfold equiv_rel_on_def, auto)
  show "reflexive_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, m \<times>\<^sub>f id\<^sub>c Z)"*)

end