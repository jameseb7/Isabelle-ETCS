section \<open>Basic Types and Operators for the Category of Sets\<close>

theory Cfunc
  imports FOL "HOL-Eisbach.Eisbach_Old_Appl_Syntax"
begin

typedecl cset
instance cset :: "term" ..
typedecl cfunc
instance cfunc :: "term" ..

text \<open>We declare @{type cset} and @{type cfunc} as types to represent the sets and functions within
  ETCS, as distinct from the ambient individuals of the surrounding first-order logic.
  The "c" prefix here is intended to stand for "category", and emphasises that these are
  category-theoretic objects.\<close>

text \<open>The axiomatization below corresponds to Axiom 1 (Sets Is a Category) in Halvorson.\<close>
axiomatization
  domain :: "cfunc \<Rightarrow> cset" and
  codomain :: "cfunc \<Rightarrow> cset" and
  comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<circ>\<^sub>c" 55) and
  id :: "cset \<Rightarrow> cfunc" ("id\<^sub>c")
where
  domain_comp: "domain(g) = codomain(f) \<Longrightarrow> domain(g \<circ>\<^sub>c f) = domain(f)" and
  codomain_comp: "domain(g) = codomain(f) \<Longrightarrow> codomain(g \<circ>\<^sub>c f) = codomain(g)" and
  comp_associative: "domain(h) = codomain(g) \<Longrightarrow> domain(g) = codomain(f) \<Longrightarrow> h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f" and
  id_domain: "domain(id(X)) = X" and
  id_codomain: "codomain(id(X)) = X" and
  id_right_unit: "f \<circ>\<^sub>c id(domain(f)) = f" and
  id_left_unit: "id (codomain(f)) \<circ>\<^sub>c f = f"

text \<open>We define a neater way of stating types and lift the type axioms into lemmas using it.\<close>
definition cfunc_type :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> o" ("_ : _ \<rightarrow> _" [50, 50, 50]50) where
  "(f : X \<rightarrow> Y) \<longleftrightarrow> (domain(f) = X \<and> codomain(f) = Y)"

lemma comp_type:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> g \<circ>\<^sub>c f : X \<rightarrow> Z"
  by (simp add: cfunc_type_def codomain_comp domain_comp)

lemma comp_associative2:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> h : Z \<rightarrow> W \<Longrightarrow> h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f"
  by (simp add: cfunc_type_def comp_associative)

lemma id_type: "id(X) : X \<rightarrow> X"
  unfolding cfunc_type_def using id_domain id_codomain by auto

lemma id_right_unit2: "f : X \<rightarrow> Y \<Longrightarrow> f \<circ>\<^sub>c id(X) = f"
  unfolding cfunc_type_def using id_right_unit by auto

lemma id_left_unit2: "f : X \<rightarrow> Y \<Longrightarrow> id(Y) \<circ>\<^sub>c f = f"
  unfolding cfunc_type_def using id_left_unit by auto

subsection \<open>Tactics for Applying Typing Rules\<close>

text \<open>ETCS lemmas often have assumptions on its ETCS type, which can often be cumbersome to prove.
  To simplify proofs involving ETCS types, we provide proof methods that apply type rules in a
  structured way to prove facts about ETCS function types.
  The type rules state the types of the basic constants and operators of ETCS and are declared as
  a named set of theorems called $type\_rule$.\<close>

named_theorems type_rule

declare id_type[type_rule]
declare comp_type[type_rule]

ML_file \<open>typecheck.ml\<close>

subsubsection \<open>typecheck\_cfuncs: Tactic to Construct Type Facts\<close>

method_setup typecheck_cfuncs =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_method\<close>
  "Check types of cfuncs in current goal and add as assumptions of the current goal"

method_setup typecheck_cfuncs_all =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_all_method\<close>
  "Check types of cfuncs in all subgoals and add as assumptions of the current goal"

method_setup typecheck_cfuncs_prems =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_prems_method\<close>
  "Check types of cfuncs in assumptions of the current goal and add as assumptions of the current goal"

subsubsection \<open>etcs\_rule: Tactic to Apply Rules with ETCS Typechecking\<close>

method_setup etcs_rule =
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_resolve_method\<close>
  "apply rule with ETCS type checking"

subsubsection \<open>etcs\_subst: Tactic to Apply Substitutions with ETCS Typechecking\<close>

method_setup etcs_subst =
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_subst_method\<close>
  "apply substitution with ETCS type checking"

method etcs_assocl declares type_rule = (etcs_subst comp_associative2)+
method etcs_assocr declares type_rule = (etcs_subst sym[OF comp_associative2])+

method_setup etcs_subst_asm =
  \<open>Runtime.exn_trace (fn _ => Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_subst_asm_method)\<close>
  "apply substitution to assumptions of the goal, with ETCS type checking"

method etcs_assocl_asm declares type_rule = (etcs_subst_asm comp_associative2)+
method etcs_assocr_asm declares type_rule = (etcs_subst_asm sym[OF comp_associative2])+

subsubsection \<open>etcs\_erule: Tactic to Apply Elimination Rules with ETCS Typechecking\<close>

method_setup etcs_erule =
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_eresolve_method\<close>
  "apply erule with ETCS type checking"

subsection \<open>Monomorphisms, Epimorphisms and Isomorphisms\<close>

subsubsection \<open>Monomorphisms\<close>

definition monomorphism :: "cfunc \<Rightarrow> o" where
  "monomorphism(f) \<longleftrightarrow> (\<forall> g h.
    (codomain(g) = domain(f) \<and> codomain(h) = domain(f)) \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"

lemma monomorphism_def2:
  "monomorphism(f) \<longleftrightarrow> (\<forall> g h A X Y. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<and> f : X \<rightarrow> Y \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"
  unfolding monomorphism_def cfunc_type_def
proof (rule iffI)
  assume mono: "\<forall>g h. codomain(g) = domain(f) \<and> codomain(h) = domain(f) \<longrightarrow> f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h"
  show "\<forall>g h A X Y.
    (domain(g) = A \<and> codomain(g) = X) \<and> (domain(h) = A \<and> codomain(h) = X) \<and>
    domain(f) = X \<and> codomain(f) = Y \<longrightarrow> f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h"
  proof (intro allI impI)
    fix g h A X Y
    assume props: "(domain(g) = A \<and> codomain(g) = X) \<and> (domain(h) = A \<and> codomain(h) = X) \<and> domain(f) = X \<and> codomain(f) = Y"
    assume fg_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
    from props have codoms: "codomain(g) = domain(f) \<and> codomain(h) = domain(f)" by auto
    show "g = h" by (rule mono[rule_format, where g=g and h=h, OF codoms fg_fh])
  qed
next
  assume rhs: "\<forall>g h A X Y.
    (domain(g) = A \<and> codomain(g) = X) \<and> (domain(h) = A \<and> codomain(h) = X) \<and>
    domain(f) = X \<and> codomain(f) = Y \<longrightarrow> f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h"
  show "\<forall>g h. codomain(g) = domain(f) \<and> codomain(h) = domain(f) \<longrightarrow> f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h"
  proof (intro allI impI)
    fix g h
    assume codoms: "codomain(g) = domain(f) \<and> codomain(h) = domain(f)"
    assume fg_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
    have dom_fg: "domain(f \<circ>\<^sub>c g) = domain(g)" "domain(f \<circ>\<^sub>c h) = domain(h)"
      using codoms domain_comp by auto
    then have dom_gh: "domain(g) = domain(h)"
      using fg_fh by auto
    show "g = h"
      using rhs[rule_format, where g=g and h=h and A="domain(g)" and X="codomain(g)" and Y="codomain(f)"]
            codoms dom_gh fg_fh by auto
  qed
qed

lemma monomorphism_def3:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "monomorphism(f) \<longleftrightarrow> (\<forall> g h A. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"
  unfolding monomorphism_def2
proof (rule iffI)
  assume general: "\<forall> g h A X' Y'. g : A \<rightarrow> X' \<and> h : A \<rightarrow> X' \<and> f : X' \<rightarrow> Y' \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h)"
  show "\<forall> g h A. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h)"
  proof (intro allI impI)
    fix g h A
    assume "g : A \<rightarrow> X \<and> h : A \<rightarrow> X" and fg_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
    then show "g = h"
      using general[rule_format, where g=g and h=h and A=A and X'=X and Y'=Y] f_type fg_fh by auto
  qed
next
  assume specific: "\<forall> g h A. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h)"
  show "\<forall> g h A X' Y'. g : A \<rightarrow> X' \<and> h : A \<rightarrow> X' \<and> f : X' \<rightarrow> Y' \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h)"
  proof (intro allI impI)
    fix g h A X' Y'
    assume typs: "g : A \<rightarrow> X' \<and> h : A \<rightarrow> X' \<and> f : X' \<rightarrow> Y'" and fg_fh: "f \<circ>\<^sub>c g = f \<circ>\<^sub>c h"
    have "X' = X" using typs f_type unfolding cfunc_type_def by auto
    then have "g : A \<rightarrow> X" "h : A \<rightarrow> X" using typs by auto
    then show "g = h" using specific[rule_format, where g=g and h=h and A=A] fg_fh by auto
  qed
qed

text \<open>The lemma below corresponds to Exercise 2.1.7a in Halvorson.\<close>
lemma comp_monic_imp_monic:
  assumes "domain(g) = codomain(f)"
  shows "monomorphism(g \<circ>\<^sub>c f) \<Longrightarrow> monomorphism(f)"
  unfolding monomorphism_def
proof clarify
  fix s t
  assume gf_monic: "\<forall>s. \<forall>t.
    codomain(s) = domain(g \<circ>\<^sub>c f) \<and> codomain(t) = domain(g \<circ>\<^sub>c f) \<longrightarrow>
          (g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_s: "codomain(s) = domain(f)"
  assume codomain_t: "codomain(t) = domain(f)"
  assume "f \<circ>\<^sub>c s = f \<circ>\<^sub>c t"

  then have gfs_eq_gft: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t"
    by (simp add: assms codomain_s codomain_t comp_associative[symmetric])
  have dom_gf: "domain(g \<circ>\<^sub>c f) = domain(f)"
    using assms domain_comp by auto
  then have cod_s_t: "codomain(s) = domain(g \<circ>\<^sub>c f)" "codomain(t) = domain(g \<circ>\<^sub>c f)"
    using codomain_s codomain_t by auto
  then show "s = t"
    using gf_monic[rule_format, where s=s and t=t] gfs_eq_gft by auto
qed

lemma comp_monic_imp_monic':
  assumes "f : X \<rightarrow> Y" "g : Y \<rightarrow> Z"
  shows "monomorphism(g \<circ>\<^sub>c f) \<Longrightarrow> monomorphism(f)"
  using assms comp_monic_imp_monic cfunc_type_def by auto

text \<open>The lemma below corresponds to Exercise 2.1.7c in Halvorson.\<close>
lemma composition_of_monic_pair_is_monic:
  assumes "codomain(f) = domain(g)"
  shows "monomorphism(f) \<Longrightarrow> monomorphism(g) \<Longrightarrow> monomorphism(g \<circ>\<^sub>c f)"
  unfolding monomorphism_def
proof clarify
  fix h k
  assume f_mono: "\<forall>s t.
    codomain(s) = domain(f) \<and> codomain(t) = domain(f) \<longrightarrow> f \<circ>\<^sub>c s = f \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume g_mono: "\<forall>s. \<forall>t.
    codomain(s) = domain(g) \<and> codomain(t) = domain(g) \<longrightarrow> g \<circ>\<^sub>c s = g \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_k: "codomain(k) = domain(g \<circ>\<^sub>c f)"
  assume codomain_h: "codomain(h) = domain(g \<circ>\<^sub>c f)"
  assume gfh_eq_gfk: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c k = (g \<circ>\<^sub>c f) \<circ>\<^sub>c h"

  have "g \<circ>\<^sub>c (f \<circ>\<^sub>c h) = (g  \<circ>\<^sub>c f)  \<circ>\<^sub>c h"
    by (simp add: assms codomain_h comp_associative domain_comp)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: gfh_eq_gfk)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: assms codomain_k comp_associative domain_comp)
  finally have gfh_gfk: "g \<circ>\<^sub>c (f \<circ>\<^sub>c h) = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)" .
  have dom_gf: "domain(g \<circ>\<^sub>c f) = domain(f)"
    using assms domain_comp by auto
  have cod_h_k: "codomain(h) = domain(f)" "codomain(k) = domain(f)"
    using codomain_h codomain_k dom_gf by auto
  then have cod_fh: "codomain(f \<circ>\<^sub>c h) = domain(g)" "codomain(f \<circ>\<^sub>c k) = domain(g)"
    using assms codomain_comp by auto
  then have fh_eq_fk: "f \<circ>\<^sub>c h = f \<circ>\<^sub>c k"
    using g_mono[rule_format, where s="f \<circ>\<^sub>c h" and t="f \<circ>\<^sub>c k"] gfh_gfk by auto
  then show "k = h"
    using f_mono[rule_format, where s=h and t=k] cod_h_k by auto
qed

subsubsection \<open>Epimorphisms\<close>

definition epimorphism :: "cfunc \<Rightarrow> o" where
  "epimorphism(f) \<longleftrightarrow> (\<forall> g h.
    (domain(g) = codomain(f) \<and> domain(h) = codomain(f)) \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"

lemma epimorphism_def2:
  "epimorphism(f) \<longleftrightarrow> (\<forall> g h A X Y. f : X \<rightarrow> Y \<and> g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"
  unfolding epimorphism_def cfunc_type_def
proof (rule iffI)
  assume epi: "\<forall>g h. domain(g) = codomain(f) \<and> domain(h) = codomain(f) \<longrightarrow> g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h"
  show "\<forall>g h A X Y.
    (domain(f) = X \<and> codomain(f) = Y) \<and> (domain(g) = Y \<and> codomain(g) = A) \<and>
    domain(h) = Y \<and> codomain(h) = A \<longrightarrow> g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h"
  proof (intro allI impI)
    fix g h A X Y
    assume props: "(domain(f) = X \<and> codomain(f) = Y) \<and> (domain(g) = Y \<and> codomain(g) = A) \<and> domain(h) = Y \<and> codomain(h) = A"
    assume gf_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
    from props have "domain(g) = codomain(f)" "domain(h) = codomain(f)" by auto
    then show "g = h" using epi[rule_format, where g=g and h=h] gf_hf by auto
  qed
next
  assume rhs: "\<forall>g h A X Y.
    (domain(f) = X \<and> codomain(f) = Y) \<and> (domain(g) = Y \<and> codomain(g) = A) \<and>
    domain(h) = Y \<and> codomain(h) = A \<longrightarrow> g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h"
  show "\<forall>g h. domain(g) = codomain(f) \<and> domain(h) = codomain(f) \<longrightarrow> g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h"
  proof (intro allI impI)
    fix g h
    assume doms: "domain(g) = codomain(f) \<and> domain(h) = codomain(f)"
    assume gf_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
    have cod_gf: "codomain(g \<circ>\<^sub>c f) = codomain(g)" "codomain(h \<circ>\<^sub>c f) = codomain(h)"
      using doms codomain_comp by auto
    then have cod_gh: "codomain(g) = codomain(h)"
      using gf_hf by auto
    show "g = h"
      using rhs[rule_format, where g=g and h=h and A="codomain(g)" and X="domain(f)" and Y="codomain(f)"]
            doms cod_gh gf_hf by auto
  qed
qed

lemma epimorphism_def3:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "epimorphism(f) \<longleftrightarrow> (\<forall> g h A. g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"
  unfolding epimorphism_def2
proof (rule iffI)
  assume general: "\<forall> g h A X' Y'. f : X' \<rightarrow> Y' \<and> g : Y' \<rightarrow> A \<and> h : Y' \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h)"
  show "\<forall> g h A. g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h)"
  proof (intro allI impI)
    fix g h A
    assume "g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A" and gf_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
    then show "g = h"
      using general[rule_format, where g=g and h=h and A=A and X'=X and Y'=Y] f_type gf_hf by auto
  qed
next
  assume specific: "\<forall> g h A. g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h)"
  show "\<forall> g h A X' Y'. f : X' \<rightarrow> Y' \<and> g : Y' \<rightarrow> A \<and> h : Y' \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h)"
  proof (intro allI impI)
    fix g h A X' Y'
    assume typs: "f : X' \<rightarrow> Y' \<and> g : Y' \<rightarrow> A \<and> h : Y' \<rightarrow> A" and gf_hf: "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
    have "Y' = Y" using typs f_type unfolding cfunc_type_def by auto
    then have "g : Y \<rightarrow> A" "h : Y \<rightarrow> A" using typs by auto
    then show "g = h" using specific[rule_format, where g=g and h=h and A=A] gf_hf by auto
  qed
qed

text \<open>The lemma below corresponds to Exercise 2.1.7b in Halvorson.\<close>
lemma comp_epi_imp_epi:
  assumes "domain(g) = codomain(f)"
  shows "epimorphism(g \<circ>\<^sub>c f) \<Longrightarrow> epimorphism(g)"
  unfolding epimorphism_def
proof clarify
  fix s t
  assume gf_epi: "\<forall>s. \<forall>t.
    domain(s) = codomain(g \<circ>\<^sub>c f) \<and> domain(t) = codomain(g \<circ>\<^sub>c f) \<longrightarrow>
          s \<circ>\<^sub>c g \<circ>\<^sub>c f = t \<circ>\<^sub>c g \<circ>\<^sub>c f \<longrightarrow> s = t"
  assume domain_s: "domain(s) = codomain(g)"
  assume domain_t: "domain(t) = codomain(g)"
  assume sf_eq_tf: "s \<circ>\<^sub>c g = t \<circ>\<^sub>c g"

  from sf_eq_tf have stgf_eq_ttgf: "s \<circ>\<^sub>c (g \<circ>\<^sub>c f) = t \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: assms comp_associative domain_s domain_t)
  have cod_gf: "codomain(g \<circ>\<^sub>c f) = codomain(g)"
    using assms codomain_comp by auto
  then have dom_s_t: "domain(s) = codomain(g \<circ>\<^sub>c f)" "domain(t) = codomain(g \<circ>\<^sub>c f)"
    using domain_s domain_t by auto
  then show "s = t"
    using gf_epi[rule_format, where s=s and t=t] stgf_eq_ttgf by auto
qed

text \<open>The lemma below corresponds to Exercise 2.1.7d in Halvorson.\<close>
lemma composition_of_epi_pair_is_epi:
assumes "codomain(f) = domain(g)"
  shows "epimorphism(f) \<Longrightarrow> epimorphism(g) \<Longrightarrow> epimorphism(g \<circ>\<^sub>c f)"
  unfolding epimorphism_def
proof clarify
  fix h k
  assume f_epi :"\<forall> s h.
    (domain(s) = codomain(f) \<and> domain(h) = codomain(f)) \<longrightarrow> (s \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> s = h)"
  assume g_epi :"\<forall> s h.
    (domain(s) = codomain(g) \<and> domain(h) = codomain(g)) \<longrightarrow> (s \<circ>\<^sub>c g = h \<circ>\<^sub>c g \<longrightarrow> s = h)"
  assume domain_k: "domain(k) = codomain(g \<circ>\<^sub>c f)"
  assume domain_h: "domain(h) = codomain(g \<circ>\<^sub>c f)"
  assume hgf_eq_kgf: "h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"

  have "(h \<circ>\<^sub>c g) \<circ>\<^sub>c f = h \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: assms codomain_comp comp_associative domain_h)
  also have "... = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: hgf_eq_kgf)
  also have "... =(k \<circ>\<^sub>c g) \<circ>\<^sub>c f "
    by (simp add: assms codomain_comp comp_associative domain_k)
  finally have hgf_eq_kgf2: "(h \<circ>\<^sub>c g) \<circ>\<^sub>c f = (k \<circ>\<^sub>c g) \<circ>\<^sub>c f" .
  have dom_hg: "domain(h \<circ>\<^sub>c g) = codomain(f)" "domain(k \<circ>\<^sub>c g) = codomain(f)"
    using assms codomain_comp domain_comp domain_h domain_k by auto
  then have hg_eq_kg: "h \<circ>\<^sub>c g = k \<circ>\<^sub>c g"
    using f_epi[rule_format, where s="h \<circ>\<^sub>c g" and h="k \<circ>\<^sub>c g"] hgf_eq_kgf2 by auto
  have dom_h_k: "domain(h) = codomain(g)" "domain(k) = codomain(g)"
    using assms codomain_comp domain_h domain_k by auto
  then show "h = k"
    using g_epi[rule_format, where s=h and h=k] hg_eq_kg by auto
qed

subsubsection \<open>Isomorphisms\<close>

definition isomorphism :: "cfunc \<Rightarrow> o" where
  "isomorphism(f) \<longleftrightarrow> (\<exists> g. domain(g) = codomain(f) \<and> codomain(g) = domain(f) \<and>
    g \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c g = id(domain(g)))"

lemma isomorphism_def2:
  "isomorphism(f) \<longleftrightarrow> (\<exists> g X Y. f : X \<rightarrow> Y \<and> g : Y \<rightarrow> X \<and> g \<circ>\<^sub>c f = id(X) \<and> f \<circ>\<^sub>c g = id(Y))"
  unfolding isomorphism_def cfunc_type_def by auto

lemma isomorphism_def3:
  assumes f_type: "f : X \<rightarrow> Y"
  shows "isomorphism(f) \<longleftrightarrow> (\<exists> g. g : Y \<rightarrow> X \<and> g \<circ>\<^sub>c f = id(X) \<and> f \<circ>\<^sub>c g = id(Y))"
  using assms unfolding isomorphism_def2 cfunc_type_def by auto

text \<open>Isabelle's plain \<open>FOL\<close> object logic, unlike HOL, does not provide a definite-description
  operator (\<open>THE\<close>) or a choice operator. We therefore first establish existence and uniqueness
  of the inverse directly, and then axiomatize @{text "f\<^bold>\<inverse>"} as the (Skolemized) witness to that
  fact -- a standard, conservative technique for introducing a function from a proven
  \<open>\<exists>!\<close> statement when no description operator is available.\<close>

lemma inverse_ex1:
  assumes iso_f: "isomorphism(f)"
  shows "\<exists>! g. g : codomain(f) \<rightarrow> domain(f) \<and> g \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c g = id(codomain(f))"
proof -
  obtain g where g_dom: "domain(g) = codomain(f)" and g_cod: "codomain(g) = domain(f)"
      and gf: "g \<circ>\<^sub>c f = id(domain(f))" and fg: "f \<circ>\<^sub>c g = id(domain(g))"
    using iso_f unfolding isomorphism_def by auto
  have g_type: "g : codomain(f) \<rightarrow> domain(f)"
    using g_dom g_cod unfolding cfunc_type_def by auto
  have fg': "f \<circ>\<^sub>c g = id(codomain(f))"
    using fg g_dom by auto
  show ?thesis
  proof (rule ex1I)
    show "g : codomain(f) \<rightarrow> domain(f) \<and> g \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c g = id(codomain(f))"
      using g_type gf fg' by auto
  next
    fix g'
    assume g'_props: "g' : codomain(f) \<rightarrow> domain(f) \<and> g' \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c g' = id(codomain(f))"
    then have g'_type: "g' : codomain(f) \<rightarrow> domain(f)"
      and g'f: "g' \<circ>\<^sub>c f = id(domain(f))" and fg'2: "f \<circ>\<^sub>c g' = id(codomain(f))"
      by auto
    have g'_dom: "domain(g') = codomain(f)"
      using g'_type unfolding cfunc_type_def by auto
    have fg'': "f \<circ>\<^sub>c g = id(domain(g'))"
      using fg' g'_dom by simp
    have step1: "g' = g' \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
      using fg'' by (simp add: id_right_unit)
    also have step2: "... = (g' \<circ>\<^sub>c f) \<circ>\<^sub>c g"
      using g'_dom g_cod[symmetric] by (simp add: comp_associative)
    also have step3: "... = id(domain(f)) \<circ>\<^sub>c g"
      using g'f by simp
    also have step4: "... = g"
      using g_cod[symmetric] by (simp add: id_left_unit)
    finally show "g' = g" .
  qed
qed

axiomatization inverse :: "cfunc \<Rightarrow> cfunc" ("_\<^bold>\<inverse>" [1000] 999)
where
  inverse_spec: "isomorphism(f) \<Longrightarrow>
    f\<^bold>\<inverse> : codomain(f) \<rightarrow> domain(f) \<and> f\<^bold>\<inverse> \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c f\<^bold>\<inverse> = id(codomain(f))"

lemma inverse_def2:
  assumes "isomorphism(f)"
  shows "f\<^bold>\<inverse> : codomain(f) \<rightarrow> domain(f) \<and> f\<^bold>\<inverse> \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c f\<^bold>\<inverse> = id(codomain(f))"
  using assms inverse_spec by auto

lemma inverse_type[type_rule]:
  assumes "isomorphism(f)" "f : X \<rightarrow> Y"
  shows "f\<^bold>\<inverse> : Y \<rightarrow> X"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_left:
  assumes "isomorphism(f)" "f : X \<rightarrow> Y"
  shows "f\<^bold>\<inverse> \<circ>\<^sub>c f = id(X)"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_right:
  assumes "isomorphism(f)" "f : X \<rightarrow> Y"
  shows "f \<circ>\<^sub>c f\<^bold>\<inverse> = id(Y)"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_iso:
  assumes "isomorphism(f)"
  shows "isomorphism(f\<^bold>\<inverse>)"
  using assms inverse_def2 unfolding isomorphism_def cfunc_type_def by (intro exI[where x=f], auto)

lemma inv_idempotent:
  assumes iso_f: "isomorphism(f)"
  shows "(f\<^bold>\<inverse>)\<^bold>\<inverse> = f"
proof -
  obtain X Y where f_type: "f : X \<rightarrow> Y"
    using iso_f unfolding isomorphism_def cfunc_type_def by auto
  have inv_type: "f\<^bold>\<inverse> : Y \<rightarrow> X"
    using iso_f f_type inverse_type by auto
  have inv_inv_type: "(f\<^bold>\<inverse>)\<^bold>\<inverse> : X \<rightarrow> Y"
    using iso_f f_type inv_iso inverse_type by auto
  have inv_inv_dom: "domain((f\<^bold>\<inverse>)\<^bold>\<inverse>) = X"
    using inv_inv_type unfolding cfunc_type_def by auto
  have inv_dom: "domain(f\<^bold>\<inverse>) = Y" and inv_cod: "codomain(f\<^bold>\<inverse>) = X"
    using inv_type unfolding cfunc_type_def by auto
  have f_dom: "domain(f) = X" and f_cod: "codomain(f) = Y"
    using f_type unfolding cfunc_type_def by auto
  have left1: "f\<^bold>\<inverse> \<circ>\<^sub>c f = id(X)"
    using iso_f f_type inv_left by auto
  have right1: "f \<circ>\<^sub>c f\<^bold>\<inverse> = id(Y)"
    using iso_f f_type inv_right by auto
  have left2: "(f\<^bold>\<inverse>)\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse> = id(Y)"
    using iso_f inv_iso inv_left inv_type by auto
  have "(f\<^bold>\<inverse>)\<^bold>\<inverse> = (f\<^bold>\<inverse>)\<^bold>\<inverse> \<circ>\<^sub>c id(X)"
    using inv_inv_dom[symmetric] by (simp add: id_right_unit)
  also have "... = (f\<^bold>\<inverse>)\<^bold>\<inverse> \<circ>\<^sub>c (f\<^bold>\<inverse> \<circ>\<^sub>c f)"
    using left1 by simp
  also have "... = ((f\<^bold>\<inverse>)\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) \<circ>\<^sub>c f"
    using inv_inv_dom inv_cod inv_dom f_cod by (simp add: comp_associative)
  also have "... = id(Y) \<circ>\<^sub>c f"
    using left2 by simp
  also have "... = f"
    using f_cod[symmetric] by (simp add: id_left_unit)
  finally show ?thesis .
qed

definition is_isomorphic :: "cset \<Rightarrow> cset \<Rightarrow> o" (infix "\<cong>" 50) where
  "X \<cong> Y \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> Y \<and> isomorphism(f))"

lemma id_isomorphism: "isomorphism(id(X))"
  unfolding isomorphism_def
proof (intro exI[where x="id(X)"])
  have dom_id: "domain(id(X)) = X" by (rule id_domain)
  have cod_id: "codomain(id(X)) = X" by (rule id_codomain)
  have idid: "id(X) \<circ>\<^sub>c id(X) = id(X)"
    using dom_id id_right_unit[of "id(X)"] by simp
  show "domain(id(X)) = codomain(id(X)) \<and> codomain(id(X)) = domain(id(X)) \<and>
        id(X) \<circ>\<^sub>c id(X) = id(domain(id(X))) \<and> id(X) \<circ>\<^sub>c id(X) = id(domain(id(X)))"
    using dom_id cod_id idid by auto
qed

lemma isomorphic_is_reflexive: "X \<cong> X"
  unfolding is_isomorphic_def
  using id_type id_isomorphism by auto

lemma isomorphic_is_symmetric: "X \<cong> Y \<longrightarrow> Y \<cong> X"
  unfolding is_isomorphic_def
proof
  assume "\<exists>f. f : X \<rightarrow> Y \<and> isomorphism(f)"
  then obtain f where f_type: "f : X \<rightarrow> Y" and f_iso: "isomorphism(f)" by auto
  have inv_type: "f\<^bold>\<inverse> : Y \<rightarrow> X" using f_iso f_type inverse_type by auto
  have inv_iso_f: "isomorphism(f\<^bold>\<inverse>)" using f_iso inv_iso by auto
  show "\<exists>f. f : Y \<rightarrow> X \<and> isomorphism(f)"
    using inv_type inv_iso_f by auto
qed

lemma isomorphism_comp':
  assumes f_type: "f : Y \<rightarrow> Z" and g_type: "g : X \<rightarrow> Y"
  shows "isomorphism(f) \<Longrightarrow> isomorphism(g) \<Longrightarrow> isomorphism(f \<circ>\<^sub>c g)"
proof -
  assume f_iso: "isomorphism(f)" and g_iso: "isomorphism(g)"
  have inv_f: "f\<^bold>\<inverse> : Z \<rightarrow> Y" using f_iso f_type inverse_type by auto
  have inv_g: "g\<^bold>\<inverse> : Y \<rightarrow> X" using g_iso g_type inverse_type by auto
  have witness_type: "g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse> : Z \<rightarrow> X"
    using inv_f inv_g comp_type by auto
  have f_dom: "domain(f) = Y" and f_cod: "codomain(f) = Z"
    using f_type unfolding cfunc_type_def by auto
  have g_dom: "domain(g) = X" and g_cod: "codomain(g) = Y"
    using g_type unfolding cfunc_type_def by auto
  have if_dom: "domain(f\<^bold>\<inverse>) = Z" and if_cod: "codomain(f\<^bold>\<inverse>) = Y"
    using inv_f unfolding cfunc_type_def by auto
  have ig_dom: "domain(g\<^bold>\<inverse>) = Y" and ig_cod: "codomain(g\<^bold>\<inverse>) = X"
    using inv_g unfolding cfunc_type_def by auto
  have left1: "f\<^bold>\<inverse> \<circ>\<^sub>c f = id(Y)"
    using f_iso f_type inv_left by auto
  have right1: "f \<circ>\<^sub>c f\<^bold>\<inverse> = id(Z)"
    using f_iso f_type inv_right by auto
  have left2: "g\<^bold>\<inverse> \<circ>\<^sub>c g = id(X)"
    using g_iso g_type inv_left by auto
  have right2: "g \<circ>\<^sub>c g\<^bold>\<inverse> = id(Y)"
    using g_iso g_type inv_right by auto
  have witness_dom: "domain(g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = Z" and witness_cod: "codomain(g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = X"
    using witness_type unfolding cfunc_type_def by auto
  have fg_dom: "domain(f \<circ>\<^sub>c g) = X" and fg_cod: "codomain(f \<circ>\<^sub>c g) = Z"
    using f_dom f_cod g_dom g_cod domain_comp codomain_comp by auto
  note all_types = f_dom f_cod g_dom g_cod if_dom if_cod ig_dom ig_cod
    witness_dom witness_cod fg_dom fg_cod
  have left_assoc1: "g\<^bold>\<inverse> \<circ>\<^sub>c (f\<^bold>\<inverse> \<circ>\<^sub>c (f \<circ>\<^sub>c g)) = (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    using comp_associative[of "g\<^bold>\<inverse>" "f\<^bold>\<inverse>" "f \<circ>\<^sub>c g"] ig_dom if_cod if_dom fg_cod by simp
  have left_assoc2: "f\<^bold>\<inverse> \<circ>\<^sub>c (f \<circ>\<^sub>c g) = (f\<^bold>\<inverse> \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    using comp_associative[of "f\<^bold>\<inverse>" f g] if_dom f_cod f_dom g_cod by simp
  have left_inv: "(g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) \<circ>\<^sub>c (f \<circ>\<^sub>c g) = id(X)"
  proof -
    have "(g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) \<circ>\<^sub>c (f \<circ>\<^sub>c g) = g\<^bold>\<inverse> \<circ>\<^sub>c (f\<^bold>\<inverse> \<circ>\<^sub>c (f \<circ>\<^sub>c g))"
      using left_assoc1 by simp
    also have "... = g\<^bold>\<inverse> \<circ>\<^sub>c ((f\<^bold>\<inverse> \<circ>\<^sub>c f) \<circ>\<^sub>c g)"
      using left_assoc2 by simp
    also have "... = g\<^bold>\<inverse> \<circ>\<^sub>c (id(Y) \<circ>\<^sub>c g)"
      using left1 by simp
    also have "... = g\<^bold>\<inverse> \<circ>\<^sub>c g"
      using g_cod[symmetric] by (simp add: id_left_unit)
    also have "... = id(X)"
      using left2 by simp
    finally show ?thesis .
  qed
  have right_assoc1: "f \<circ>\<^sub>c (g \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>)) = (f \<circ>\<^sub>c g) \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>)"
    using comp_associative[of f g "g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>"] f_dom g_cod g_dom witness_cod by simp
  have right_assoc2: "g \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = (g \<circ>\<^sub>c g\<^bold>\<inverse>) \<circ>\<^sub>c f\<^bold>\<inverse>"
    using comp_associative[of g "g\<^bold>\<inverse>" "f\<^bold>\<inverse>"] g_dom ig_cod ig_dom if_cod by simp
  have right_inv: "(f \<circ>\<^sub>c g) \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = id(Z)"
  proof -
    have "(f \<circ>\<^sub>c g) \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = f \<circ>\<^sub>c (g \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>))"
      using right_assoc1 by simp
    also have "... = f \<circ>\<^sub>c ((g \<circ>\<^sub>c g\<^bold>\<inverse>) \<circ>\<^sub>c f\<^bold>\<inverse>)"
      using right_assoc2 by simp
    also have "... = f \<circ>\<^sub>c (id(Y) \<circ>\<^sub>c f\<^bold>\<inverse>)"
      using right2 by simp
    also have "... = f \<circ>\<^sub>c f\<^bold>\<inverse>"
      using if_cod[symmetric] by (simp add: id_left_unit)
    also have "... = id(Z)"
      using right1 by simp
    finally show ?thesis .
  qed
  show "isomorphism(f \<circ>\<^sub>c g)"
    unfolding isomorphism_def
  proof (intro exI[where x="g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>"])
    show "domain(g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = codomain(f \<circ>\<^sub>c g) \<and> codomain(g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = domain(f \<circ>\<^sub>c g) \<and>
          (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) \<circ>\<^sub>c (f \<circ>\<^sub>c g) = id(domain(f \<circ>\<^sub>c g)) \<and>
          (f \<circ>\<^sub>c g) \<circ>\<^sub>c (g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>) = id(domain(g\<^bold>\<inverse> \<circ>\<^sub>c f\<^bold>\<inverse>))"
      using witness_dom witness_cod fg_dom fg_cod left_inv right_inv by auto
  qed
qed

lemma isomorphism_comp:
  assumes dom_eq: "domain(f) = codomain(g)" and f_iso: "isomorphism(f)" and g_iso: "isomorphism(g)"
  shows "isomorphism(f \<circ>\<^sub>c g)"
proof -
  have g_type: "g : domain(g) \<rightarrow> codomain(g)" unfolding cfunc_type_def by auto
  have f_type: "f : codomain(g) \<rightarrow> codomain(f)" using dom_eq unfolding cfunc_type_def by auto
  show ?thesis using isomorphism_comp'[OF f_type g_type f_iso g_iso] .
qed

lemma isomorphic_is_transitive: "(X \<cong> Y \<and> Y \<cong> Z) \<longrightarrow> X \<cong> Z"
  unfolding is_isomorphic_def
proof
  assume "(\<exists>f. f : X \<rightarrow> Y \<and> isomorphism(f)) \<and> (\<exists>g. g : Y \<rightarrow> Z \<and> isomorphism(g))"
  then obtain f g where f_type: "f : X \<rightarrow> Y" and f_iso: "isomorphism(f)"
    and g_type: "g : Y \<rightarrow> Z" and g_iso: "isomorphism(g)" by auto
  have gf_type: "g \<circ>\<^sub>c f : X \<rightarrow> Z" using f_type g_type comp_type by auto
  have gf_iso: "isomorphism(g \<circ>\<^sub>c f)" using f_type g_type f_iso g_iso isomorphism_comp' by auto
  show "\<exists>f. f : X \<rightarrow> Z \<and> isomorphism(f)"
    using gf_type gf_iso by auto
qed

text \<open>Isabelle's plain \<open>FOL\<close> does not ship HOL's \<open>Main\<close>-library notion of an \<open>equiv\<close>alence
  relation over \<open>UNIV\<close> (both are HOL-\<open>Set\<close>-specific), so we restate the same content -- that
  \<open>\<cong>\<close> is reflexive, symmetric and transitive -- directly.\<close>
lemma is_isomorphic_equivalence:
  "(\<forall>X. X \<cong> X) \<and> (\<forall>X Y. X \<cong> Y \<longrightarrow> Y \<cong> X) \<and> (\<forall>X Y Z. X \<cong> Y \<and> Y \<cong> Z \<longrightarrow> X \<cong> Z)"
proof (intro conjI allI impI)
  fix X show "X \<cong> X" by (rule isomorphic_is_reflexive)
next
  fix X Y assume "X \<cong> Y" then show "Y \<cong> X" using isomorphic_is_symmetric by auto
next
  fix X Y Z assume XY_YZ: "X \<cong> Y \<and> Y \<cong> Z"
  show "X \<cong> Z" by (rule mp[OF isomorphic_is_transitive XY_YZ])
qed

text \<open>The lemma below corresponds to Exercise 2.1.7e in Halvorson.\<close>
lemma iso_imp_epi_and_monic:
  "isomorphism(f) \<Longrightarrow> epimorphism(f) \<and> monomorphism(f)"
  unfolding isomorphism_def epimorphism_def monomorphism_def
proof safe
  fix g s t
  assume domain_g: "domain(g) = codomain(f)"
  assume codomain_g: "codomain(g) = domain(f)"
  assume gf_id: "g \<circ>\<^sub>c f = id(domain(f))"
  assume fg_id: "f \<circ>\<^sub>c g = id(domain(g))"
  assume domain_s: "domain(s) = codomain(f)"
  assume domain_t: "domain(t) = codomain(f)"
  assume sf_eq_tf: "s \<circ>\<^sub>c f = t \<circ>\<^sub>c f"

  have "s = s \<circ>\<^sub>c id(domain(s))"
    by (simp add: id_right_unit)
  also have "... = s \<circ>\<^sub>c id(codomain(f))"
    by (simp add: domain_s)
  also have "... = s \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    by (simp add: domain_g fg_id)
  also have "... = (s \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    by (simp add: codomain_g comp_associative domain_s)
  also have "... = (t \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    by (simp add: sf_eq_tf)
  also have "... = t \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    by (simp add: codomain_g comp_associative domain_t)
  also have "... = t \<circ>\<^sub>c id(codomain(f))"
    by (simp add: domain_g fg_id)
  also have "... = t \<circ>\<^sub>c id(domain(t))"
    by (simp add: domain_t)
  also have "... = t"
    by (simp add: id_right_unit)
  finally show "s = t" .
next
  fix g h k
  assume domain_g: "domain(g) = codomain(f)"
  assume codomain_g: "codomain(g) = domain(f)"
  assume gf_id: "g \<circ>\<^sub>c f = id(domain(f))"
  assume fg_id: "f \<circ>\<^sub>c g = id(domain(g))"
  assume codomain_h: "codomain(h) = domain(f)"
  assume codomain_k: "codomain(k) = domain(f)"
  assume fk_eq_fh: "f \<circ>\<^sub>c k = f \<circ>\<^sub>c h"

  have "h = id(codomain(h)) \<circ>\<^sub>c h"
    by (simp add: id_left_unit)
  also have "... = id(domain(f)) \<circ>\<^sub>c h"
    by (simp add: codomain_h)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c h"
    using gf_id by auto
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c h)"
    by (simp add: codomain_h comp_associative domain_g)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: fk_eq_fh)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: codomain_k comp_associative domain_g)
  also have "... = id(domain(f)) \<circ>\<^sub>c k"
    by (simp add: gf_id)
  also have "... = id(codomain(k)) \<circ>\<^sub>c k"
    by (simp add: codomain_k)
  also have "... = k"
    by (simp add: id_left_unit)
  finally show "k = h" by simp
qed

lemma isomorphism_sandwich:
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C" and h_type: "h: C \<rightarrow> D"
  assumes f_iso: "isomorphism(f)"
  assumes h_iso: "isomorphism(h)"
  assumes hgf_iso: "isomorphism(h \<circ>\<^sub>c g \<circ>\<^sub>c f)"
  shows "isomorphism(g)"
proof -
  have sandwich_iso: "isomorphism(h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse>)"
    using assms by (typecheck_cfuncs, simp add: f_iso h_iso hgf_iso inv_iso isomorphism_comp')
  have inv_h_type: "h\<^bold>\<inverse> : D \<rightarrow> C" using h_iso h_type inverse_type by auto
  have inv_f_type: "f\<^bold>\<inverse> : B \<rightarrow> A" using f_iso f_type inverse_type by auto
  have f_dom: "domain(f) = A" and f_cod: "codomain(f) = B"
    using f_type unfolding cfunc_type_def by auto
  have g_dom: "domain(g) = B" and g_cod: "codomain(g) = C"
    using g_type unfolding cfunc_type_def by auto
  have h_dom: "domain(h) = C" and h_cod: "codomain(h) = D"
    using h_type unfolding cfunc_type_def by auto
  have ih_dom: "domain(h\<^bold>\<inverse>) = D" and ih_cod: "codomain(h\<^bold>\<inverse>) = C"
    using inv_h_type unfolding cfunc_type_def by auto
  have if_dom: "domain(f\<^bold>\<inverse>) = B" and if_cod: "codomain(f\<^bold>\<inverse>) = A"
    using inv_f_type unfolding cfunc_type_def by auto
  have hleft: "h\<^bold>\<inverse> \<circ>\<^sub>c h = id(C)"
    using h_iso h_type inv_left by auto
  have fright: "f \<circ>\<^sub>c f\<^bold>\<inverse> = id(B)"
    using f_iso f_type inv_right by auto
  have gf_dom: "domain(g \<circ>\<^sub>c f) = A" and gf_cod: "codomain(g \<circ>\<^sub>c f) = C"
    using f_dom f_cod g_dom g_cod domain_comp codomain_comp by auto
  have sw_assoc1: "h \<circ>\<^sub>c ((g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse>) = (h \<circ>\<^sub>c (g \<circ>\<^sub>c f)) \<circ>\<^sub>c f\<^bold>\<inverse>"
    using comp_associative[of h "g \<circ>\<^sub>c f" "f\<^bold>\<inverse>"] h_dom gf_cod gf_dom if_cod by simp
  have sw_assoc2: "g \<circ>\<^sub>c (f \<circ>\<^sub>c f\<^bold>\<inverse>) = (g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse>"
    using comp_associative[of g f "f\<^bold>\<inverse>"] g_dom f_cod f_dom if_cod by simp
  have sw_assoc3: "h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c g) = (h\<^bold>\<inverse> \<circ>\<^sub>c h) \<circ>\<^sub>c g"
    using comp_associative[of "h\<^bold>\<inverse>" h g] ih_dom h_cod h_dom g_cod by simp
  have simplify: "h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse> = g"
  proof -
    have "h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse> = h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c ((g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse>))"
      using sw_assoc1 by simp
    also have "... = h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c (g \<circ>\<^sub>c (f \<circ>\<^sub>c f\<^bold>\<inverse>)))"
      using sw_assoc2 by simp
    also have "... = h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c (g \<circ>\<^sub>c id(B)))"
      using fright by simp
    also have "... = h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c g)"
      using g_dom[symmetric] by (simp add: id_right_unit)
    also have "... = (h\<^bold>\<inverse> \<circ>\<^sub>c h) \<circ>\<^sub>c g"
      using sw_assoc3 by simp
    also have "... = id(C) \<circ>\<^sub>c g"
      using hleft by simp
    also have "... = g"
      using g_cod[symmetric] by (simp add: id_left_unit)
    finally show ?thesis .
  qed
  show "isomorphism(g)"
    using sandwich_iso simplify by simp
qed

end
