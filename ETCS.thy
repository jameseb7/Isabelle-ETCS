theory ETCS
  imports Main
begin

(* Avoid HOL names interfering *)
hide_const id 

(* Declare types for category-theoretic sets and functions *)
typedecl cset
typedecl cfunc

section \<open>Axiom 1: Sets is a Category\<close>

(* Each cfunc is a morphism from its domain to its codomain *)
axiomatization
  domain :: "cfunc \<Rightarrow> cset" and
  codomain :: "cfunc \<Rightarrow> cset"

(* definition for specifying the type of a cfunc *)
abbreviation cfunc_type :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" ("_ : _ \<rightarrow> _" [50, 50, 50]50) where
  "(f : X \<rightarrow> Y) \<equiv> (domain f = X \<and> codomain f = Y)"

axiomatization
  comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<circ>\<^sub>c" 55) and
  id :: "cset \<Rightarrow> cfunc"
where
  compatible_comp_type: "domain g = codomain f \<Longrightarrow> g \<circ>\<^sub>c f : domain f \<rightarrow> codomain g" and
  comp_associative: "h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f" and (* TODO: should this require compatible types? *)
  id_type: "id X : X \<rightarrow> X" and
  id_right_unit: "f \<circ>\<^sub>c id (domain f) = f" and
  id_left_unit: "id (codomain f) \<circ>\<^sub>c f = f"

definition monomorphism :: "cfunc \<Rightarrow> bool" where
  "monomorphism f \<longleftrightarrow> 
    (\<forall> g h. (codomain g = domain f \<and> codomain h = domain f) \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"

definition epimorphism :: "cfunc \<Rightarrow> bool" where
  "epimorphism(f) \<longleftrightarrow> 
    (\<forall> g h. (domain(g) = codomain(f) \<and> domain(h) = codomain(f)) \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"

section \<open>Axiom 2: Cartesian Products\<close>

axiomatization
  cart_prod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<times>\<^sub>c" 65) and
  left_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("\<langle>_,_\<rangle>")
where
  left_cart_proj_type: "left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> X" and
  right_cart_proj_type: "right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y" and
  cfunc_prod_type: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> \<langle>f,g\<rangle> : Z \<rightarrow> X \<times>\<^sub>c Y" and
  left_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> left_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = f" and
  right_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> right_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = g" and
  cfunc_prod_unique: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> h : Z \<rightarrow> X \<times>\<^sub>c Y \<Longrightarrow>
    left_cart_proj X Y \<circ>\<^sub>c h = f \<Longrightarrow> right_cart_proj X Y \<circ>\<^sub>c h = g \<Longrightarrow> h = \<langle>f,g\<rangle>"

definition cfunc_cross_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<times>\<^sub>f" 65) where
  "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj (domain f) (domain g), g \<circ>\<^sub>c right_cart_proj (domain f) (domain g)\<rangle>"

lemma cfunc_cross_prod_type:
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> f \<times>\<^sub>f g : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z"
  unfolding cfunc_cross_prod_def
  using cfunc_prod_type compatible_comp_type left_cart_proj_type right_cart_proj_type by auto

section \<open>Axiom 3: Terminal Objects\<close>

axiomatization
  terminal_func :: "cset \<Rightarrow> cfunc" ("\<beta>\<^bsub>_\<^esub>" 100) and
  one :: "cset" ("\<^bold>1")
where
  terminal_func_type: "\<beta>\<^bsub>X\<^esub> : X \<rightarrow> \<^bold>1" and
  terminal_func_unique: "h :  X \<rightarrow> \<^bold>1 \<Longrightarrow> h = \<beta>\<^bsub>X\<^esub>" and
  one_separator: "f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> (\<And> x. x : \<^bold>1 \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c x = g \<circ>\<^sub>c x) \<Longrightarrow> f = g"

section \<open>Membership and subsets\<close>

abbreviation member :: "cfunc \<Rightarrow> cset \<Rightarrow> bool" (infix "\<in>\<^sub>c" 50) where
  "x \<in>\<^sub>c X \<equiv> (x : one \<rightarrow> X)"

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
  unfolding relative_subset_def2 subobject_of_def2 by (metis id_left_unit id_type monomorphism_def)

definition factors_through :: "cfunc  \<Rightarrow> cfunc \<Rightarrow> bool" (infix "factorsthru" 90)
  where "g factorsthru f \<longleftrightarrow> (\<exists> h. (h: domain(g)\<rightarrow> domain(f)) \<and> f \<circ>\<^sub>c h = g)"

definition relative_member :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" ("_ \<in>\<^bsub>_\<^esub> _" [51,50,51]50) where
  "x \<in>\<^bsub>X\<^esub> B \<longleftrightarrow> (x \<in>\<^sub>c X \<and> monomorphism (snd B) \<and> snd B : fst B \<rightarrow> X \<and> x factorsthru (snd B))"

lemma relative_member_def2:
  "x \<in>\<^bsub>X\<^esub> (B, m) = (x \<in>\<^sub>c X \<and> monomorphism m \<and> m : B \<rightarrow> X \<and> x factorsthru m)"
  unfolding relative_member_def by auto

section \<open>Axiom 4: Equalizers\<close>

definition equalizer :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "equalizer E m f g \<longleftrightarrow> (\<exists> X Y. (f : X \<rightarrow> Y) \<and> (g : X \<rightarrow> Y) \<and> (m : E \<rightarrow> X)
    \<and> (f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)
    \<and> (\<forall> h F. (h : F \<rightarrow> X \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)))"

axiomatization where
  equalizer_exists: "f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> \<exists> E m. equalizer E m f g"

section \<open>Axiom 5: Truth-Value Object\<close>

definition square_commutes :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "square_commutes A B C D ab bd ac cd \<longleftrightarrow>
    ((ab : A \<rightarrow> B) \<and> (bd : B \<rightarrow> D) \<and> (ac : A \<rightarrow> C) \<and> (cd : C \<rightarrow> D) \<and> (bd \<circ>\<^sub>c ab = cd \<circ>\<^sub>c ac))"

definition is_pullback :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "is_pullback A B C D ab bd ac cd \<longleftrightarrow> 
    (square_commutes A B C D ab bd ac cd \<and> 
    (\<forall> Z k h. (k : Z \<rightarrow> B \<and> h : Z \<rightarrow> C \<and> bd \<circ>\<^sub>c k = cd \<circ>\<^sub>c h)  \<longrightarrow>
      (\<exists>! j. j : Z \<rightarrow> A \<and> ab \<circ>\<^sub>c j = k \<and> ac \<circ>\<^sub>c j = h)))"

axiomatization
  true_func :: "cfunc" ("\<t>") and
  false_func  :: "cfunc" ("\<f>") and
  truth_value_set :: "cset" ("\<Omega>")
where
  true_func_type: "\<t> \<in>\<^sub>c \<Omega>" and
  false_func_type: "\<f> \<in>\<^sub>c \<Omega>" and
  true_false_distinct: "\<t> \<noteq> \<f>" and
  true_false_only_truth_values: "x \<in>\<^sub>c \<Omega> \<Longrightarrow> x = \<f> \<or> x = \<t>" and
  characteristic_function_exists:
    "m : B \<rightarrow> X \<Longrightarrow> 
      monomorphism m \<Longrightarrow> 
      (\<exists>! \<chi>. \<chi> : X \<rightarrow> \<Omega> \<and> \<t> \<circ>\<^sub>c \<beta>\<^bsub>B\<^esub> = \<chi> \<circ>\<^sub>c m \<and> 
        (\<forall>Z k h. k : Z \<rightarrow> \<^bold>1 \<and> h : Z \<rightarrow> X \<and> \<t> \<circ>\<^sub>c k = \<chi> \<circ>\<^sub>c h \<longrightarrow>
          (\<exists>!j. j : Z \<rightarrow> B \<and> \<beta>\<^bsub>B\<^esub> \<circ>\<^sub>c j = k \<and> m \<circ>\<^sub>c j = h)))"
  (* is_pullback B one X \<Omega> (\<beta>\<^bsub>B\<^esub>) \<t> m \<chi> *)

section  \<open>Axiom 6: Equivalence Classes\<close>

definition reflexive :: "cset \<Rightarrow> bool" where
  "reflexive R = (\<exists> X m. (R,m) \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and> 
    (\<forall>x. x \<in>\<^sub>c X \<longrightarrow>
      (\<langle>x,x\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R, m))))"

definition symmetric :: "cset \<Rightarrow> bool" where
  "symmetric R = (\<exists> X m. (R,m)  \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and>
    (\<forall>x y. x \<in>\<^sub>c X \<and>  y \<in>\<^sub>c X \<longrightarrow> 
      (\<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R, m) \<longrightarrow> \<langle>y,x\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R, m))))" 

definition transitive :: "cset \<Rightarrow> bool" where
  "transitive R = (\<exists> X m. (R,m)  \<subseteq>\<^sub>c X\<times>\<^sub>cX \<and>
    (\<forall>x y z. x \<in>\<^sub>c X \<and>  y \<in>\<^sub>c X \<and> z \<in>\<^sub>c X  \<longrightarrow>
      (\<langle>x,y\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R, m) \<and> \<langle>y,z\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R, m)
        \<longrightarrow> \<langle>x,z\<rangle> \<in>\<^bsub>X\<times>\<^sub>cX\<^esub> (R, m))))"

definition equivalance_rel :: "cset \<Rightarrow> bool" where
  "equivalance_rel R  \<longleftrightarrow> (reflexive R \<and> symmetric R \<and> transitive R)"

section  \<open>Axiom 7: Coproducts\<close>

axiomatization
  coprod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<Coprod>" 65) and
  left_coproj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_coproj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_coprod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<amalg>" 65)
where
  left_proj_type: "left_coproj X Y : X \<rightarrow> X\<Coprod>Y" and
  right_proj_type: "right_coproj X Y : Y \<rightarrow> X\<Coprod>Y" and
  cfunc_coprod_type: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> f\<amalg>g :  X\<Coprod>Y \<rightarrow> Z" and
  left_coproj_cfunc_coprod: "f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<Longrightarrow> f\<amalg>g \<circ>\<^sub>c (left_coproj X Y) = f" and
  right_coproj_cfunc_coprod: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> f\<amalg>g \<circ>\<^sub>c (right_coproj X Y)  = g" and
  cfunc_coprod_unique: "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow>
    h : X \<Coprod> Y \<rightarrow> Z \<Longrightarrow> (h \<circ>\<^sub>c left_coproj X Y = f) \<Longrightarrow> (h \<circ>\<^sub>c right_coproj X Y = g) \<Longrightarrow>  h = f\<amalg>g"


section  \<open>Axiom 8: Empty Set\<close>

axiomatization
  initial_func :: "cset \<Rightarrow> cfunc" ("\<alpha>\<^bsub>_\<^esub>" 100) and
  emptyset :: "cset" ("\<emptyset>")
where
  initial_func_type: "\<alpha>\<^bsub>X\<^esub> : \<emptyset> \<rightarrow> X" and
  initial_func_unique: "h : \<emptyset> \<rightarrow> X \<Longrightarrow> h = \<alpha>\<^bsub>X\<^esub>" and
  emptyset_is_empty: "\<not> (x \<in>\<^sub>c \<emptyset>)"


section \<open>Axiom 9: Exponential Objects\<close>

axiomatization
  exp_set :: "cset \<Rightarrow> cset \<Rightarrow> cset" ("_\<^bsup>_\<^esup>" [100,100]100) and
  eval_func  :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  transpose_func :: "cfunc \<Rightarrow> cfunc" ("_\<^sup>\<sharp>" [100]100)
where
  eval_func_type: "eval_func X A : A\<times>\<^sub>c X\<^bsup>A\<^esup> \<rightarrow> X" and
  transpose_func_def: "f : A \<times>\<^sub>c Z \<rightarrow> X \<Longrightarrow> f\<^sup>\<sharp> : Z \<rightarrow> X\<^bsup>A\<^esup> \<and> (eval_func X A) \<circ>\<^sub>c (id A) \<times>\<^sub>f (f\<^sup>\<sharp>) = f" and
  transpose_func_unique: "f : A\<times>\<^sub>cZ \<rightarrow> X \<Longrightarrow> g: Z \<rightarrow> X\<^bsup>A\<^esup> \<Longrightarrow> (eval_func X A) \<circ>\<^sub>c (id A) \<times>\<^sub>f g = f \<Longrightarrow> g = f\<^sup>\<sharp>"

section \<open>Axiom 10: Natural Number Object\<close>

axiomatization
  natural_numbers :: "cset" ("\<nat>\<^sub>c") and
  zero :: "cfunc" and
  successor :: "cfunc"
  where
  zero_type: "zero \<in>\<^sub>c \<nat>\<^sub>c" and 
  successor_type: "successor: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and 
  natural_number_object_property: 
    "q : one \<rightarrow> X \<Longrightarrow> f: X \<rightarrow> X \<Longrightarrow> (\<exists>!u. u: \<nat>\<^sub>c \<rightarrow> X \<and> u \<circ>\<^sub>c zero = q \<and> u \<circ>\<^sub>c successor = f \<circ>\<^sub>c u)"


section \<open>Axiom 11: Axiom of Choice\<close>

definition section_of :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" (infix "sectionof" 90)
  where "s sectionof f \<longleftrightarrow> s : codomain(f) \<rightarrow> domain(f) \<and> f \<circ>\<^sub>c s = id (codomain(f))"

axiomatization
  where
  axiom_of_choice :"epimorphism(f) \<longrightarrow> (\<exists> g . g sectionof f)"

end