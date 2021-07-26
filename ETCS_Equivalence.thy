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
    by (typecheck_cfuncs, smt assms(2)  cfunc_type_def coequalizer_def)
  then obtain k'' where k''_def: "k'': F \<rightarrow> F \<and> k'' \<circ>\<^sub>c n =  n"
    by blast
  then have k''_def2: "k'' = id F"
    using assms(2) coequalizer_def id_left_unit2 k''_def by (typecheck_cfuncs, blast)

  have kk'_idF: "k \<circ>\<^sub>c k' = id F"
    by (typecheck_cfuncs, smt assms(2) cfunc_type_def coequalizer_def comp_associative k''_def k''_def2 k'_def k_def)

  have k'k_idE: "k' \<circ>\<^sub>c k = id E"
    by (typecheck_cfuncs, smt assms(1) coequalizer_def comp_associative2 id_left_unit2 k'_def k_def)

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
   have j_exists: "\<exists>! j. j: Y \<rightarrow> X \<and> j \<circ>\<^sub>c f =  id(X)"
     by (typecheck_cfuncs, smt \<open>id\<^sub>c X \<circ>\<^sub>c g = id\<^sub>c X \<circ>\<^sub>c h\<close> cfunc_type_def coequalized_fxns coequalizer_def)
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
  fix h F
  assume h_type: "h : X \<rightarrow> F"

  assume h_eq: "h \<circ>\<^sub>c fibered_product_left_proj X f f X = h \<circ>\<^sub>c fibered_product_right_proj X f f X"

  (* requires axiom of choice to obtain m : Y \<rightarrow> X (since f is an epimorphism), 
     from which we get k  = h \<circ>\<^sub>c m, can't handle Y smaller than X otherwise *)

  show "\<exists>k. k : Y \<rightarrow> F \<and> k \<circ>\<^sub>c f = h"
    oops


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
     show "monomorphism (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      using \<open>monomorphism m\<close> cfunc_cross_prod_mono cfunc_type_def composition_of_monic_pair_is_monic distribute_right_mono id_isomorphism iso_imp_epi_and_monic m_type by (typecheck_cfuncs, auto)
  next
    assume xzxz_type: "\<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z"
    assume m_type: "m : Y \<rightarrow> X \<times>\<^sub>c X"
    obtain y where y_def: "y \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c y = \<langle>x, x\<rangle>"
      using assms reflexive_def2 x_type by blast
    have mid_type: "m \<times>\<^sub>f id\<^sub>c Z : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c X) \<times>\<^sub>c Z"
      by (simp add: cfunc_cross_prod_type id_type m_type)
    have dist_mid_type:"distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c X \<times>\<^sub>c Z"
      using comp_type distribute_right_type mid_type by force

    have yz_tyep: "\<langle>y,z\<rangle> \<in>\<^sub>c Y \<times>\<^sub>c Z"
      by (typecheck_cfuncs, simp add: \<open>z \<in>\<^sub>c Z\<close> y_def)
    have "(distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c \<langle>y,z\<rangle>  = distribute_right X X Z \<circ>\<^sub>c (m \<times>\<^sub>f id(Z)) \<circ>\<^sub>c \<langle>y,z\<rangle>"
      using \<open>m \<times>\<^sub>f id\<^sub>c Z : Y \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c X) \<times>\<^sub>c Z\<close> comp_associative2 yz_tyep by (typecheck_cfuncs, auto)
    also have "...  =  distribute_right X X Z \<circ>\<^sub>c  \<langle>m \<circ>\<^sub>c y,id(Z) \<circ>\<^sub>c z\<rangle>"
      using \<open>z \<in>\<^sub>c Z\<close> cfunc_cross_prod_comp_cfunc_prod m_type y_def by (typecheck_cfuncs, auto)
    also have distxxz: "... = distribute_right X X Z \<circ>\<^sub>c  \<langle> \<langle>x, x\<rangle>, z\<rangle>"
      using \<open>z \<in>\<^sub>c Z\<close> id_left_unit2 y_def by auto
    also have "... = \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle>"
      by (meson \<open>z \<in>\<^sub>c Z\<close> distribute_right_ap x_type)
    then have "\<exists>h. \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle> = (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z) \<circ>\<^sub>c h"
      by (metis  calculation)
    then show "\<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle> factorsthru (distribute_right X X Z \<circ>\<^sub>c m \<times>\<^sub>f id\<^sub>c Z)"
      using  xzxz_type \<open>distribute_right X X Z \<circ>\<^sub>c \<langle>\<langle>x,x\<rangle>,z\<rangle> = \<langle>\<langle>x,z\<rangle>,\<langle>x,z\<rangle>\<rangle>\<close> dist_mid_type calculation factors_through_def2 yz_tyep by auto
  qed
qed




(*lemma left_pair_equiv_rel:
  assumes "equiv_rel_on X (Y, m)"
  shows "equiv_rel_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, m \<times>\<^sub>f id Z)"
proof (unfold equiv_rel_on_def, auto)
  show "reflexive_on (X \<times>\<^sub>c Z) (Y \<times>\<^sub>c Z, m \<times>\<^sub>f id\<^sub>c Z)"*)

end