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
  codomain :: "cfunc \<Rightarrow> cset" and
  comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<circ>\<^sub>c" 55) and
  id :: "cset \<Rightarrow> cfunc"
where
  comp_domain: "domain g = codomain f \<Longrightarrow> domain (g \<circ>\<^sub>c f) = domain f" and
  comp_codomain: "domain g = codomain f \<Longrightarrow> codomain (g \<circ>\<^sub>c f) = codomain g" and
  comp_associative: "domain h = codomain g \<Longrightarrow> domain g = codomain f \<Longrightarrow>
    h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f" and
  id_domain: "domain (id X) = X" and
  id_codomain: "codomain (id X) = X" and
  id_right_unit: "domain f = X \<Longrightarrow> f \<circ>\<^sub>c id X = f" and
  id_left_unit: "codomain f = Y \<Longrightarrow>  id Y \<circ>\<^sub>c f = f"

definition has_type :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" ("_ : _ \<rightarrow> _" [50,50,50]50) where
  "has_type f X Y \<equiv> domain f = X \<and> codomain f = Y"

named_theorems type_rule

lemma comp_type[type_rule]: "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> g \<circ>\<^sub>c f : X \<rightarrow> Z"
  unfolding has_type_def by (simp add: comp_codomain comp_domain)

lemma id_type[type_rule]: "id X : X \<rightarrow> X"
  unfolding has_type_def by (simp add: id_codomain id_domain)

definition monomorphism :: "cfunc \<Rightarrow> bool" where
  "monomorphism f \<longleftrightarrow> 
    (\<forall> g h. (codomain g = domain f \<and> codomain h = domain f) \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"

definition epimorphism :: "cfunc \<Rightarrow> bool" where
  "epimorphism f \<longleftrightarrow> 
    (\<forall> g h. (domain g = codomain f \<and> domain h  = codomain f) \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"

ML \<open>
  fun check_cfunc binder_typs (t : term) = 
    case fastype_of1 (binder_typs, t) of
      Type (name, []) => name = "ETCS.cfunc"
    | _ => false
\<close>

ML \<open>check_cfunc [] @{term "(\<lambda>x. x \<circ>\<^sub>c f) (id X)"};\<close>

ML \<open>
  fun find_cfunc_terms binder_typs (a $ b) =
        (if check_cfunc binder_typs (a $ b) then [(a $ b)] else []) 
          @ find_cfunc_terms binder_typs a @ find_cfunc_terms binder_typs b
    | find_cfunc_terms binder_typs (Abs (n, typ, t)) =
        (if check_cfunc binder_typs (Abs (n, typ, t)) then [(Abs (n, typ, t))] else []) 
          @ find_cfunc_terms (typ::binder_typs) t 
    | find_cfunc_terms binder_typs t = if check_cfunc binder_typs t then [t] else []
\<close>

ML_val \<open>find_cfunc_terms [] @{term "\<lambda>X. id Y \<circ>\<^sub>c f \<circ>\<^sub>c id X"}\<close>

ML_val \<open>Syntax.pretty_term @{context} @{term "(\<lambda>x. x \<circ>\<^sub>c f) (id X)"};\<close>

ML_val \<open>map (Syntax.pretty_term @{context}) (find_cfunc_terms [] @{term "(\<lambda>x. x \<circ>\<^sub>c f) (id X)"});\<close>

ML \<open>fun match_term bound_typs pat t = 
        let fun match_term' bound_typs (pat1 $ pat2) (t1 $ t2) =
                let val (matches1, success1) = match_term' bound_typs pat1 t1
                    val (matches2, success2) = match_term' bound_typs pat2 t2
                in (matches1 @ matches2, success1 andalso success2)
                end
            | match_term' bound_typs (Abs (_, patty, pat)) (Abs (_, ty, t)) =
                let val (matches, success) = match_term' (ty::bound_typs) pat t
                in (matches, success andalso patty = ty)
                end
            | match_term' bound_typs (Var (var, patty)) t =
                if fastype_of1 (bound_typs, t) = patty then ([(var, t)], true) else ([], false)
            | match_term' _ pat t = ([], pat aconv t)
            val (matches, success) = match_term' bound_typs pat t
        in if success then SOME matches else NONE
        end\<close>

ML_val \<open>match_term [] (Thm.full_prop_of @{thm id_type}) @{term "Trueprop (id X : X \<rightarrow> X)"};\<close>

ML \<open>fun extract_type_rule_term rule =
          case Thm.concl_of rule of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("ETCS.has_type", _) $ t) $ _ $ _ => SOME t
              | _ => NONE)
          | _ => NONE
                \<close>

ML_val \<open>extract_type_rule_term @{thm comp_type}\<close>

ML \<open>fun certify_instantiations ctxt bound_typs = 
      List.map (fn (x : indexname, t) => ((x, fastype_of1 (bound_typs, t)), Thm.cterm_of ctxt t)) \<close>

ML \<open>fun match_type_rule ctxt bound_typs t rule = 
          let val opt_insts =
                case extract_type_rule_term rule of
                  SOME pat => match_term bound_typs pat t
                | NONE => NONE
              val opt_insts' = Option.map (certify_instantiations ctxt bound_typs) opt_insts
          in case opt_insts' of
              SOME insts => SOME (Thm.instantiate ([], insts) rule)
            | NONE => NONE
          end\<close>

ML \<open>exception CFUNC_TYPE of string * term list * thm list\<close>

ML \<open>fun find_type_rule _ _ t [] = raise CFUNC_TYPE ("No typing rule for term", [t], [])
      | find_type_rule ctxt bound_typs t (rule::rules) =
          case match_type_rule ctxt bound_typs t rule of
            SOME rule' => rule'
          | NONE => find_type_rule ctxt bound_typs t rules\<close>

ML_val \<open>match_type_rule @{context} [] @{term "f \<circ>\<^sub>c id X"} @{thm comp_type}\<close>

ML \<open>fun elim_type_rule_prem _ thm _ [] = raise CFUNC_TYPE ("Cannot instantiate type rule", [], [thm])
      | elim_type_rule_prem ctxt thm prem (lem::lems) = 
          case match_term [] prem (Thm.prop_of lem) of
            SOME insts => 
              let val insts' = certify_instantiations ctxt [] insts
                  val inst_thm = Thm.instantiate ([], insts') thm
              in Thm.implies_elim inst_thm lem
              end
          | NONE => elim_type_rule_prem ctxt thm prem lems\<close>

ML_val \<open>let val type_rule = the (match_type_rule @{context} [] @{term "f \<circ>\<^sub>c id X"} @{thm comp_type})
        in elim_type_rule_prem @{context} type_rule (List.hd (Thm.prems_of type_rule))
              [the (match_type_rule @{context} [] @{term "id X"} @{thm id_type})]
        end\<close>

ML \<open>fun elim_type_rule_prems ctxt thm lems =
          case Thm.prems_of thm of
            [] => thm
          | prem::_ => elim_type_rule_prems ctxt (elim_type_rule_prem ctxt thm prem lems) lems\<close>

ML_val \<open>let val type_rule = the (match_type_rule @{context} [] @{term "f \<circ>\<^sub>c id X"} @{thm comp_type})
        in elim_type_rule_prems @{context} type_rule
              [the (match_type_rule @{context} [] @{term "id X"} @{thm id_type}), 
                Thm.assume (Thm.cterm_of @{context} @{term "Trueprop (f : X \<rightarrow> Y)"})]
        end\<close>

ML \<open>fun construct_cfunc_type_lemma ctxt rules binder_typs lems t = 
          let val rule = find_type_rule ctxt binder_typs t rules
          in elim_type_rule_prems ctxt rule lems
          end\<close>

ML \<open>fun construct_cfunc_type_lemmas1 ctxt rules binder_typs (t $ u) =
          let val left_lems = construct_cfunc_type_lemmas1 ctxt rules binder_typs t
              val right_lems = construct_cfunc_type_lemmas1 ctxt rules binder_typs u
              val sublems = left_lems @ right_lems
              val this_lem = 
                if check_cfunc binder_typs (t $ u)
                then [construct_cfunc_type_lemma ctxt rules binder_typs sublems (t $ u)]
                else []
          in this_lem @ sublems
          end
      | construct_cfunc_type_lemmas1 ctxt rules binder_typs (Abs (n, typ, t)) =
          let val sublems = construct_cfunc_type_lemmas1 ctxt rules (typ::binder_typs) t
              val this_lem = if check_cfunc binder_typs (Abs (n, typ, t))
                then [construct_cfunc_type_lemma ctxt rules binder_typs sublems (Abs (n, typ, t))]
                else []
          in this_lem @ sublems
          end
      | construct_cfunc_type_lemmas1 ctxt rules binder_typs t =
          if check_cfunc binder_typs t then [construct_cfunc_type_lemma ctxt rules binder_typs [] t] else []\<close>

ML \<open>fun construct_cfunc_type_lemmas ctxt rules t = construct_cfunc_type_lemmas1 ctxt rules [] t\<close>

ML_val \<open>let val type_rules = [Thm.assume (Thm.cterm_of @{context} @{term "Trueprop (f : X \<rightarrow> Y)"}),
                  @{thm id_type}, @{thm comp_type}]
        in construct_cfunc_type_lemmas @{context} type_rules @{term "id Y \<circ>\<^sub>c f \<circ>\<^sub>c id X"}
        end;\<close>

ML \<open>fun extract_prems ((@{term Trueprop}) $ P) = extract_prems P
      | extract_prems (@{term "Pure.imp"} $ P $ Q) = P::extract_prems Q
      | extract_prems _ = []\<close>

ML \<open>fun typecheck_cfuncs_subtac ctxt type_rules (subgoal, n) = 
          let val type_rules' = type_rules @ Named_Theorems.get ctxt "ETCS.type_rule"
              val lems = construct_cfunc_type_lemmas ctxt type_rules' subgoal
          in (Method.insert_tac ctxt lems n THEN asm_full_simp_tac ctxt n)
          end\<close>

ML \<open>fun typecheck_cfuncs_tac ctxt type_rules = SUBGOAL (typecheck_cfuncs_subtac ctxt type_rules)\<close>

ML \<open>fun typecheck_cfuncs_method ctxt = (fn thms => CONTEXT_TACTIC (typecheck_cfuncs_tac ctxt thms 1)) : Method.method\<close>

method_setup typecheck_cfuncs = \<open>Scan.succeed typecheck_cfuncs_method\<close> "Check types of cfuncs in current goal and add as assumptions"


  print_methods

section \<open>Axiom 2: Cartesian Products\<close>

axiomatization
  cart_prod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<times>\<^sub>c" 70) and
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

subsection \<open>Function cross product\<close>

definition cfunc_cross_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<times>\<^sub>f" 65) where
  "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj (domain f) (domain g), g \<circ>\<^sub>c right_cart_proj (domain f) (domain g)\<rangle>"

lemma cfunc_cross_prod_def2:
  assumes "domain f = X" "domain g = Y"
  shows "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj X Y, g \<circ>\<^sub>c right_cart_proj X Y\<rangle>"
  unfolding cfunc_cross_prod_def using assms by auto

lemma cfunc_cross_prod_domain:
  "f : X \<rightarrow> Z \<Longrightarrow> g : Y \<rightarrow> W \<Longrightarrow> f \<times>\<^sub>f g : X \<times>\<^sub>c Y \<rightarrow> Z \<times>\<^sub>c W"
  unfolding cfunc_cross_prod_def
  by (simp add: cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type)

lemma left_cfunc_cross_prod:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> W"
  shows "left_cart_proj Z W \<circ>\<^sub>c (f \<times>\<^sub>f g) = f \<circ>\<^sub>c left_cart_proj X Y"
  unfolding cfunc_cross_prod_def
  by (simp add: assms comp_type left_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_type)

lemma right_cfunc_cross_prod:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> W"
  shows "right_cart_proj Z W \<circ>\<^sub>c (f \<times>\<^sub>f g) = g \<circ>\<^sub>c right_cart_proj X Y"
  using assms type_rules by (unfold cfunc_cross_prod_def2, simp add: right_cart_proj_cfunc_prod)

lemma cfunc_cross_prod_unique: 
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> h : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z \<Longrightarrow>
    left_cart_proj Y Z \<circ>\<^sub>c h = f \<circ>\<^sub>c left_cart_proj W X \<Longrightarrow>
    right_cart_proj Y Z \<circ>\<^sub>c h = g \<circ>\<^sub>c right_cart_proj W X \<Longrightarrow> h = f \<times>\<^sub>f g"
  by (simp add: cfunc_cross_prod_def2 cfunc_prod_unique type_rules)

lemma cross_prod_comp_dist:
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C" and h_type: "h : X \<rightarrow> Y"
  shows "h \<times>\<^sub>f (g \<circ>\<^sub>c f) = (h \<times>\<^sub>f g) \<circ>\<^sub>c (id X \<times>\<^sub>f f)"
proof -
  have left: "left_cart_proj Y C \<circ>\<^sub>c h \<times>\<^sub>f g \<circ>\<^sub>c id X \<times>\<^sub>f f = h \<circ>\<^sub>c left_cart_proj X A"
    (is "?lhs = ?rhs")
  proof -
    have "?lhs = (h \<circ>\<^sub>c left_cart_proj X B) \<circ>\<^sub>c id X \<times>\<^sub>f f"
      using assms type_rules comp_associative left_cfunc_cross_prod by auto
    also have "... = h \<circ>\<^sub>c (left_cart_proj X B \<circ>\<^sub>c id X \<times>\<^sub>f f)"
      using assms type_rules comp_associative by auto
    also have "... = ?rhs"
      using assms type_rules left_cfunc_cross_prod id_left_unit by auto
    then show ?thesis using calculation by auto
  qed

  have right: "right_cart_proj Y C \<circ>\<^sub>c h \<times>\<^sub>f g \<circ>\<^sub>c id X \<times>\<^sub>f f = g \<circ>\<^sub>c f \<circ>\<^sub>c right_cart_proj X A"
    (is "?lhs = ?rhs")
  proof -
    have "?lhs = (g \<circ>\<^sub>c right_cart_proj X B) \<circ>\<^sub>c id X \<times>\<^sub>f f"
      using assms type_rules comp_associative right_cfunc_cross_prod by auto
    also have "... = g \<circ>\<^sub>c (right_cart_proj X B \<circ>\<^sub>c id X \<times>\<^sub>f f)"
      using assms type_rules comp_associative by auto
    also have "... = ?rhs"
      using assms type_rules right_cfunc_cross_prod id_left_unit by auto
    then show ?thesis using calculation by auto
  qed

  print_methods

  have "h \<times>\<^sub>f g \<circ>\<^sub>c id Y \<times>\<^sub>f f = h \<times>\<^sub>f (g \<circ>\<^sub>c f)"
    using assms left right type_rules
    apply (subst cfunc_cross_prod_unique[where h="(h \<times>\<^sub>f g) \<circ>\<^sub>c (id Y \<times>\<^sub>f f)", where f=h, where g = "g \<circ>\<^sub>c f", where W=X, where Y=Y, where X=A, where Z=C])
    using assms left right type_rules apply (auto)


    thm type_rules
      thm comp_assoc

      thm cfunc_cross_prod_unique
  thm cfunc_cross_prod_unique[where h="(h \<times>\<^sub>f g) \<circ>\<^sub>c (id Y \<times>\<^sub>f f)", where f=h, where g = "g \<circ>\<^sub>c f", where W=X, where Y=Y, where X=A, where Z=C]
  thm cfunc_cross_prod_unique[where f=h, where g = "g \<circ>\<^sub>c f", where W=X, where Y=Y, where X=A, where Z=C]


  have "left_cart_proj X C \<circ>\<^sub>c (h \<times>\<^sub>f g) \<circ>\<^sub>c (h \<times>\<^sub>f f) = h"

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

lemma id_cross_prod: "id X \<times>\<^sub>f id Y = id (X \<times>\<^sub>c Y)"
  unfolding cfunc_cross_prod_def 
  by (metis cfunc_prod_unique id_left_unit id_right_unit id_type left_cart_proj_type right_cart_proj_type)

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