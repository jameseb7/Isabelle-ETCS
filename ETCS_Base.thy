theory ETCS_Base
  imports Main
begin

typedecl cset
typedecl cfunc


section \<open>Axiom 1: Sets is a Category\<close>

axiomatization
  domain :: "cfunc \<Rightarrow> cset" and
  codomain :: "cfunc \<Rightarrow> cset" and
  comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<circ>\<^sub>c" 55) and
  id :: "cset \<Rightarrow> cfunc" ("id\<^sub>c") 
where
  domain_comp: "domain g = codomain f \<Longrightarrow> domain (g \<circ>\<^sub>c f) = domain f" and
  codomain_comp: "domain g = codomain f \<Longrightarrow> codomain (g \<circ>\<^sub>c f) = codomain g" and
  comp_associative: "domain h = codomain g \<Longrightarrow> domain g = codomain f \<Longrightarrow> h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f" and
  id_domain: "domain (id X) = X" and
  id_codomain: "codomain (id X) = X" and
  id_right_unit: "f \<circ>\<^sub>c id (domain f) = f" and
  id_left_unit: "id (codomain f) \<circ>\<^sub>c f = f"

definition cfunc_type :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" ("_ : _ \<rightarrow> _" [50, 50, 50]50) where
  "(f : X \<rightarrow> Y) \<longleftrightarrow> (domain(f) = X \<and> codomain(f) = Y)"

named_theorems type_rule

(* lift the lemmas from the axiom to use the new types *)
lemma comp_type[type_rule]:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> g \<circ>\<^sub>c f : X \<rightarrow> Z"
  by (simp add: cfunc_type_def codomain_comp domain_comp)

lemma comp_associative2:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> h : Z \<rightarrow> W \<Longrightarrow> h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f"
  by (simp add: cfunc_type_def comp_associative)

lemma id_type[type_rule]: "id X : X \<rightarrow> X"
  unfolding cfunc_type_def using id_domain id_codomain by auto

lemma id_right_unit2: "f : X \<rightarrow> Y \<Longrightarrow> f \<circ>\<^sub>c id X = f"
  unfolding cfunc_type_def using id_right_unit by auto

lemma id_left_unit2: "f : X \<rightarrow> Y \<Longrightarrow> id Y \<circ>\<^sub>c f = f"
  unfolding cfunc_type_def using id_left_unit by auto

subsection \<open>Tactic to construct type facts\<close>

(* check_cfunc determines if a given term is of type cfunc *)
ML \<open>
  fun check_cfunc binder_typs (t : term) = 
    case fastype_of1 (binder_typs, t) of
      Type (name, []) => (name = "ETCS_Base.cfunc") andalso not (loose_bvar (t, 0)) (* reject invalid terms with loose bvars *)
    | _ => false
\<close>

(* find_cfunc_terms finds all the subterms of type cfunc in a term and returns them as a list *)
ML \<open>
  fun find_cfunc_terms binder_typs (a $ b) =
        (if check_cfunc binder_typs (a $ b) then [(a $ b)] else []) 
          @ find_cfunc_terms binder_typs a @ find_cfunc_terms binder_typs b
    | find_cfunc_terms binder_typs (Abs (n, typ, t)) =
        (if check_cfunc binder_typs (Abs (n, typ, t)) then [(Abs (n, typ, t))] else []) 
          @ find_cfunc_terms (typ::binder_typs) t 
    | find_cfunc_terms binder_typs t = if check_cfunc binder_typs t then [t] else []
\<close>

(* match_term attempts to unify a term against a pattern, 
  returning a list of instantiations and a boolean indicating success *)
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

(* extract_type_rule_term extracts the term f of type cfunc from a theorem of the form f : X \<rightarrow> Y *)
ML \<open>fun extract_type_rule_term rule =
          case Thm.concl_of rule of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("ETCS_Base.cfunc_type", _) $ t) $ _ $ _ => SOME t
              | _ => NONE)
          | _ => NONE
                \<close>

(* certify_instantiations lifts a list of term instantiations to a list of certified term instantiations *)
ML \<open>fun certify_instantiations ctxt bound_typs = 
      List.map (fn (x : indexname, t) => ((x, fastype_of1 (bound_typs, t)), Thm.cterm_of ctxt t)) \<close>

(* match_type_rule checks if a given type rule is applicable to a given term,
  returning an instantiated version of the rule if it is *)
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

ML \<open>fun is_type_rule thm =
          case Thm.concl_of thm of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("ETCS_Base.cfunc_type", _) $ _) $ _ $ _ => true
              | _ => false)
          | _ => false
                \<close>

(* find_type_rule searches a list of type rules, attempting to match each in turn *)
ML \<open>fun find_type_rule _ _ _ [] = NONE (* no typing rules left *)
      | find_type_rule ctxt bound_typs t (rule::rules) =
          case match_type_rule ctxt bound_typs t rule of
            SOME rule' => SOME rule'
          | NONE => find_type_rule ctxt bound_typs t rules\<close>

(* elim_type_rule_prem attempts to eliminate a premise of a type rule by applying a lemma from a supplied list *)
ML \<open>fun elim_type_rule_prem _ _ _ [] = NONE (* no lemmas match the premise *)
      | elim_type_rule_prem ctxt thm prem (lem::lems) = 
          case match_term [] prem (Thm.prop_of lem) of
            SOME insts => 
              let val insts' = certify_instantiations ctxt [] insts
                  val inst_thm = Thm.instantiate ([], insts') thm
              in SOME (Thm.implies_elim inst_thm lem)
              end
          | NONE => elim_type_rule_prem ctxt thm prem lems\<close>

(* elim_type_rule_prems attempts to eliminate all premises of a type rule by applying lemmas from a supplied list,
  leaving those premises that cannot be eliminated *)
ML \<open>fun elim_type_rule_prems ctxt thm lems =
          let fun elim_type_rule_prems' thm [] = thm
                | elim_type_rule_prems' thm (prem::prems) =
                    case elim_type_rule_prem ctxt thm prem lems of
                      SOME thm' => elim_type_rule_prems' thm' prems
                    | NONE => (* can't eliminate premise, shift it to the back and continue *)
                        elim_type_rule_prems' (Thm.permute_prems 0 1 thm) prems
          in elim_type_rule_prems' thm (Thm.prems_of thm)
          end\<close>

(* construct_cfunc_type_lemma attempts to construct a type lemma for a given term
  using a list of typing rules and a list of existing typing lemmas;
  the lemma is returned in a list, which is empty if no lemma can be constructed *)
ML \<open>fun construct_cfunc_type_lemma ctxt rules binder_typs lems t = 
          case find_type_rule ctxt binder_typs t rules of
            SOME rule => [elim_type_rule_prems ctxt rule (lems @ rules)]
          | NONE => []\<close>

(* construct_cfunc_type_lemmas1 constructs all the typing lemmas for a given term,
  taking a list of bound variable term types in to determine which terms are cfuncs *)
ML \<open>fun construct_cfunc_type_lemmas1 ctxt rules binder_typs (t $ u) =
          let val left_lems = construct_cfunc_type_lemmas1 ctxt rules binder_typs t
              val right_lems = construct_cfunc_type_lemmas1 ctxt rules binder_typs u
              val sublems = left_lems @ right_lems
              val this_lem = 
                if check_cfunc binder_typs (t $ u)
                then construct_cfunc_type_lemma ctxt rules binder_typs sublems (t $ u)
                else []
          in this_lem @ sublems
          end
      | construct_cfunc_type_lemmas1 ctxt rules binder_typs (Abs (n, typ, t)) =
          let val sublems = construct_cfunc_type_lemmas1 ctxt rules (typ::binder_typs) t
              val this_lem = if check_cfunc binder_typs (Abs (n, typ, t))
                then construct_cfunc_type_lemma ctxt rules binder_typs sublems (Abs (n, typ, t))
                else []
          in this_lem @ sublems
          end
      | construct_cfunc_type_lemmas1 ctxt rules binder_typs t =
          if check_cfunc binder_typs t then construct_cfunc_type_lemma ctxt rules binder_typs [] t else []\<close>

(* construct_cfunc_type_lemmas constructs all the typing lemmas for a given term,
  assuming there are no unbound bound variables *)
ML \<open>fun construct_cfunc_type_lemmas ctxt rules t = construct_cfunc_type_lemmas1 ctxt rules [] t\<close>

(* extract_prems attempts to extract premises from a term that has the form of a theorem *)
ML \<open>fun extract_prems ((@{term Trueprop}) $ P) = extract_prems P
      | extract_prems (@{term "Pure.imp"} $ P $ Q) = P::extract_prems Q
      | extract_prems _ = []\<close>

(* typecheck_cfuncs_subproof implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the Subgoal.FOCUS combinator *)
ML \<open>fun typecheck_cfuncs_subproof ctxt type_rules subgoal n (focus : Subgoal.focus) = 
          let val type_rules' = type_rules @ (#prems focus) @ Named_Theorems.get ctxt "ETCS_Base.type_rule"
              val lems = construct_cfunc_type_lemmas ctxt type_rules' subgoal
          in Method.insert_tac ctxt lems n
          end\<close>

(* typecheck_cfuncs_subtac implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the SUBGOAL combinator *)
ML \<open>fun typecheck_cfuncs_subtac ctxt type_rules (subgoal, n) = 
          Subgoal.FOCUS (typecheck_cfuncs_subproof ctxt type_rules subgoal n) ctxt n
          THEN asm_full_simp_tac ctxt n\<close>

(* typecheck_cfuncs_tac lifts typecheck_cfuncs_subproof to a tactic
  that generates cfunc type facts as assumptions of a specified goal *)
ML \<open>fun typecheck_cfuncs_tac ctxt type_rules =
  SUBGOAL (typecheck_cfuncs_subtac ctxt type_rules)\<close>

(* typecheck_cfuncs_method lifts typecheck_cfuncs_tac to a proof method that
  generates cfunc type facts for the first goal *)
ML \<open>fun typecheck_cfuncs_method ctxt = 
          (fn thms => CONTEXT_TACTIC (typecheck_cfuncs_tac ctxt thms 1)) : Method.method\<close>

(* setup typecheck_cfuncs_method as a proof method in the theory *)
method_setup typecheck_cfuncs =
  \<open>Scan.succeed typecheck_cfuncs_method\<close>
  "Check types of cfuncs in current goal and add as assumptions of the current goal"

(* typecheck_cfuncs_prems_subproof implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the Subgoal.FOCUS combinator *)
ML \<open>fun typecheck_cfuncs_prems_subproof ctxt assms _ n (focus : Subgoal.focus) = 
          let val type_rules' = assms @ (#prems focus) @ Named_Theorems.get ctxt "ETCS_Base.type_rule"
              val assms_to_typecheck = (filter (fn x => not (is_type_rule x)) assms)
              val prems_to_typecheck = (filter (fn x => not (is_type_rule x)) (#prems focus))
              val to_typecheck = assms_to_typecheck @ prems_to_typecheck
              val typecheck_func = fn x => construct_cfunc_type_lemmas ctxt type_rules' (Thm.prop_of x)
              val lems = flat (map typecheck_func to_typecheck)
          in Method.insert_tac ctxt lems n
          end\<close>

(* typecheck_cfuncs_prems_subtac implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the SUBGOAL combinator *)
ML \<open>fun typecheck_cfuncs_prems_subtac ctxt type_rules (subgoal, n) = 
          Subgoal.FOCUS (typecheck_cfuncs_prems_subproof ctxt type_rules subgoal n) ctxt n
          THEN asm_full_simp_tac ctxt n\<close>

(* typecheck_cfuncs_prems_tac lifts typecheck_cfuncs_subproof to a tactic
  that generates cfunc type facts as assumptions of a specified goal *)
ML \<open>fun typecheck_cfuncs_prems_tac ctxt type_rules =
  SUBGOAL (typecheck_cfuncs_prems_subtac ctxt type_rules)\<close>

(* typecheck_cfuncs_prems_method lifts typecheck_cfuncs_tac to a proof method that
  generates cfunc type facts for the first goal *)
ML \<open>fun typecheck_cfuncs_prems_method ctxt = 
          (fn thms => CONTEXT_TACTIC (typecheck_cfuncs_prems_tac ctxt thms 1)) : Method.method\<close>

(* setup typecheck_cfuncs_prems_method as a proof method in the theory *)
method_setup typecheck_cfuncs_prems =
  \<open>Scan.succeed typecheck_cfuncs_prems_method\<close>
  "Check types of cfuncs in assumptions of the current goal and add as assumptions of the current goal"

(*ML \<open>fun typecheck_proof_tac_facts_subtac ctxt rules facts tac (subgoal, n) =
          let val type_rules = rules @ Named_Theorems.get ctxt "ETCS_Base.type_rule"
              val type_lems = construct_cfunc_type_lemmas ctxt type_rules subgoal
              val typechecked_facts = List.map 
          in ()
          end\<close>

ML_val \<open>elim_type_rule_prems\<close>
ML_val \<open>SUBGOAL\<close>
ML_val \<open>Method.rule_tac\<close>
ML_val \<open>Method.rule\<close>
ML_val \<open>fn x => Attrib.thms >> x\<close>
ML_val \<open>Scan.succeed\<close>*)

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
  "monomorphism(f) \<longleftrightarrow> (\<forall> g h. 
    (codomain(g) = domain(f) \<and> codomain(h) = domain(f)) \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"

lemma monomorphism_def2:
  "monomorphism f \<longleftrightarrow> (\<forall> g h A X Y. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<and> f : X \<rightarrow> Y \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"
  unfolding monomorphism_def by (smt cfunc_type_def domain_comp)

lemma monomorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "monomorphism f \<longleftrightarrow> (\<forall> g h A. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"
  unfolding monomorphism_def2 using assms cfunc_type_def by auto 

definition epimorphism :: "cfunc \<Rightarrow> bool" where
  "epimorphism f \<longleftrightarrow> (\<forall> g h. 
    (domain(g) = codomain(f) \<and> domain(h) = codomain(f)) \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"

lemma epimorphism_def2:
  "epimorphism f \<longleftrightarrow> (\<forall> g h A X Y. f : X \<rightarrow> Y \<and> g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"
  unfolding epimorphism_def by (smt cfunc_type_def codomain_comp) 

lemma epimorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "epimorphism f \<longleftrightarrow> (\<forall> g h A. g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"
  unfolding epimorphism_def2 using assms cfunc_type_def by auto

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
  by (metis cfunc_type_def)

lemma isomorphism_comp: 
  "domain f = codomain g \<Longrightarrow> isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  unfolding isomorphism_def
proof (auto, rule_tac x="gaa \<circ>\<^sub>c ga" in exI, auto)
  fix ga gaa
  assume domain_f: "domain f = codomain g"
  assume domain_ga: "domain ga = codomain f"
  assume domain_gaa: "domain gaa = codomain g"
  assume codomain_ga: "codomain ga = codomain g"
  assume codomain_gaa: "codomain gaa = domain g"

  show "domain (gaa \<circ>\<^sub>c ga) = codomain (f \<circ>\<^sub>c g)"
    by (simp add: codomain_comp codomain_ga domain_comp domain_f domain_ga domain_gaa)
  show "codomain (gaa \<circ>\<^sub>c ga) = domain (f \<circ>\<^sub>c g)"
    by (simp add: codomain_comp codomain_ga codomain_gaa domain_comp domain_f domain_gaa)
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
    by (metis codomain_comp codomain_ga comp_associative domain_f domain_ga domain_gaa ga_comp_f)
  also have "... = gaa \<circ>\<^sub>c g"
    by (simp add: domain_f id_left_unit)
  also have "... = id (domain (f \<circ>\<^sub>c g))"
    by (simp add: domain_comp domain_f gaa_comp_g)
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
    by (metis codomain_comp codomain_ga codomain_gaa comp_associative domain_f domain_gaa g_comp_gaa)
  also have "... = f \<circ>\<^sub>c ga"
    by (metis codomain_ga id_left_unit)
  also have "... = id (domain (gaa \<circ>\<^sub>c ga))"
    by (simp add: codomain_ga domain_comp domain_ga domain_gaa f_comp_ga)
  then show "(f \<circ>\<^sub>c g) \<circ>\<^sub>c gaa \<circ>\<^sub>c ga = id (domain (gaa \<circ>\<^sub>c ga))"
    using calculation by auto
qed

lemma isomorphism_comp': 
  assumes "f : Y \<rightarrow> Z" "g : X \<rightarrow> Y"
  shows "isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  using assms(1) assms(2) cfunc_type_def isomorphism_comp by auto

lemma isomorphic_is_transitive: "(X \<cong> Y \<and> Y \<cong> Z) \<longrightarrow> X \<cong> Z"
  unfolding is_isomorphic_def 
  by (auto, rule_tac x="fa \<circ>\<^sub>c f" in exI, auto simp add: isomorphism_comp' comp_type)

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
  assumes "domain g = codomain f"
  shows "monomorphism (g \<circ>\<^sub>c f) \<Longrightarrow> monomorphism f"
  unfolding monomorphism_def
proof auto
  fix s t
  assume gf_monic: "\<forall>s. \<forall>t. 
    codomain s = domain (g \<circ>\<^sub>c f) \<and> codomain t = domain (g \<circ>\<^sub>c f) \<longrightarrow>
          (g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_s: "codomain s = domain f"
  assume codomain_t: "codomain t = domain f"
  assume fs_eq_ft: "f \<circ>\<^sub>c s = f \<circ>\<^sub>c t"

  from fs_eq_ft have "(g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t"
    by (metis assms codomain_s codomain_t comp_associative)
  then show "s = t"
    using gf_monic codomain_s codomain_t domain_comp by (simp add: assms)
qed      

(*Exercise 2.1.7b*)
lemma comp_epi_imp_epi:
  assumes "domain g = codomain f"
  shows "epimorphism (g \<circ>\<^sub>c f) \<Longrightarrow> epimorphism g"
  unfolding epimorphism_def
proof auto
  fix s t
  assume gf_epi: "\<forall>s. \<forall>t.
    domain s = codomain (g \<circ>\<^sub>c f) \<and> domain t = codomain (g \<circ>\<^sub>c f) \<longrightarrow>
          s \<circ>\<^sub>c g \<circ>\<^sub>c f = t \<circ>\<^sub>c g \<circ>\<^sub>c f \<longrightarrow> s = t"
  assume domain_s: "domain s = codomain g"
  assume domain_t: "domain t = codomain g"
  assume sf_eq_tf: "s \<circ>\<^sub>c g = t \<circ>\<^sub>c g"

  from sf_eq_tf have "s \<circ>\<^sub>c (g \<circ>\<^sub>c f) = t \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: assms comp_associative domain_s domain_t)
  then show "s = t"
    using gf_epi codomain_comp domain_s domain_t by (simp add: assms)
qed

(*Exercise 2.1.7c*)
lemma composition_of_monic_pair_is_monic:
  assumes "codomain f = domain g"
  shows "monomorphism f \<Longrightarrow> monomorphism g \<Longrightarrow> monomorphism (g \<circ>\<^sub>c f)"
  unfolding monomorphism_def
proof auto
  fix h k
  assume f_mono: "\<forall>s t. 
    codomain s = domain f \<and> codomain t = domain f \<longrightarrow> f \<circ>\<^sub>c s = f \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume g_mono: "\<forall>s. \<forall>t. 
    codomain s = domain g \<and> codomain t = domain g \<longrightarrow> g \<circ>\<^sub>c s = g \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_k: "codomain k = domain (g \<circ>\<^sub>c f)"
  assume codomain_h: "codomain h = domain (g \<circ>\<^sub>c f)"
  assume gfh_eq_gfk: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c k = (g \<circ>\<^sub>c f) \<circ>\<^sub>c h"
 
  have "g \<circ>\<^sub>c (f \<circ>\<^sub>c h) = (g  \<circ>\<^sub>c f)  \<circ>\<^sub>c h"
    by (simp add: assms codomain_h comp_associative domain_comp)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: gfh_eq_gfk)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: assms codomain_k comp_associative domain_comp)
  
  then have "f \<circ>\<^sub>c h = f \<circ>\<^sub>c k"
    using assms calculation cfunc_type_def codomain_h codomain_k comp_type domain_comp g_mono by auto
  then show "k = h"
    by (simp add: codomain_h codomain_k domain_comp f_mono assms)
qed

(*Exercise 2.1.7d*)
lemma composition_of_epi_pair_is_epi:
assumes "codomain f = domain g"
  shows "epimorphism f \<Longrightarrow> epimorphism g \<Longrightarrow> epimorphism (g \<circ>\<^sub>c f)"
  unfolding epimorphism_def
proof auto
  fix h k
  assume f_epi :"\<forall> s h.
    (domain(s) = codomain(f) \<and> domain(h) = codomain(f)) \<longrightarrow> (s \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> s = h)"
  assume g_epi :"\<forall> s h.
    (domain(s) = codomain(g) \<and> domain(h) = codomain(g)) \<longrightarrow> (s \<circ>\<^sub>c g = h \<circ>\<^sub>c g \<longrightarrow> s = h)"
  assume domain_k: "domain k = codomain (g \<circ>\<^sub>c f)"
  assume domain_h: "domain h = codomain (g \<circ>\<^sub>c f)"
  assume hgf_eq_kgf: "h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
  
  have "(h \<circ>\<^sub>c g) \<circ>\<^sub>c f = h \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: assms codomain_comp comp_associative domain_h)
  also have "... = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: hgf_eq_kgf)
  also have "... =(k \<circ>\<^sub>c g) \<circ>\<^sub>c f "
    by (simp add: assms codomain_comp comp_associative domain_k)
 
  then have "h \<circ>\<^sub>c g = k \<circ>\<^sub>c g"
    by (simp add: assms calculation codomain_comp domain_comp domain_h domain_k f_epi)
  then show "h = k"
    by (simp add: codomain_comp domain_h domain_k g_epi assms)
qed


(*Exercise 2.1.7e*)
lemma iso_imp_epi_and_monic:
  "isomorphism f \<Longrightarrow> epimorphism f \<and> monomorphism f"
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
    by (simp add: codomain_g comp_associative domain_s)
  also have "... = (t \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    by (simp add: sf_eq_tf)
  also have "... = t \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    by (simp add: codomain_g comp_associative domain_t)
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
    by (simp add: codomain_h comp_associative domain_g)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: fk_eq_fh)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: codomain_k comp_associative domain_g)
  also have "... = id(domain(f)) \<circ>\<^sub>c k"
    by (simp add: gf_id)
  also have "... = k"
    by (metis codomain_k id_left_unit)

  then show "k = h"
    using calculation by auto
qed


lemma isomorphism_sandwich: 
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C" and h_type: "h: C \<rightarrow> D"
  assumes f_iso: "isomorphism(f)"
  assumes h_iso: "isomorphism(h)"
  assumes hgf_iso: "isomorphism(h \<circ>\<^sub>c g \<circ>\<^sub>c f)"
  shows "isomorphism(g)"
proof -
  obtain cc :: "cfunc \<Rightarrow> cfunc" where
       f1: "\<forall>c. (\<not> isomorphism c \<or> domain (cc c) = codomain c \<and> codomain (cc c) = domain c \<and> cc c \<circ>\<^sub>c c = id\<^sub>c (domain c) \<and> c \<circ>\<^sub>c cc c = id\<^sub>c (domain (cc c))) \<and> (isomorphism c \<or> (\<forall>ca. domain ca \<noteq> codomain c \<or> codomain ca \<noteq> domain c \<or> ca \<circ>\<^sub>c c \<noteq> id\<^sub>c (domain c) \<or> c \<circ>\<^sub>c ca \<noteq> id\<^sub>c (domain ca)))"
    using isomorphism_def by moura
  have f2: "\<forall>c ca cb. domain c \<noteq> codomain ca \<or> domain ca \<noteq> codomain cb \<or> c \<circ>\<^sub>c ca \<circ>\<^sub>c cb = (c \<circ>\<^sub>c ca) \<circ>\<^sub>c cb"
    using comp_associative by blast
  have f3: "\<forall>c ca cb. (c : ca \<rightarrow> cb) = (domain c = ca \<and> codomain c = cb)"
    using cfunc_type_def by blast
  then have f4: "domain g = B \<and> codomain g = C"
    using g_type by blast
  have f5: "domain h = C \<and> codomain h = D"
    using f3 h_type by blast
  then have f6: "domain h = codomain g"
    using f4 by simp
  have f7: "\<forall>c ca. domain c \<noteq> codomain ca \<or> domain (c \<circ>\<^sub>c ca) = domain ca"
    using domain_comp by blast
  have f8: "\<forall>c ca. domain c \<noteq> codomain ca \<or> codomain (c \<circ>\<^sub>c ca) = codomain c"
    using codomain_comp by blast
  have f9: "domain g = B \<and> codomain g = C"
    using f3 g_type by blast
  have f10: "domain f = A \<and> codomain f = B"
    using f3 f_type by presburger
  then have f11: "domain g = codomain f"
    using f9 by meson
  then have f12: "domain h = codomain (g \<circ>\<^sub>c f)"
    using f8 f5 f4 by presburger
  then have f13: "domain (h \<circ>\<^sub>c g \<circ>\<^sub>c f) = domain (g \<circ>\<^sub>c f)"
    using f7 by blast
  have f14: "domain (g \<circ>\<^sub>c f) = domain f"
    using f11 f7 by blast
  have f15: "domain (cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) = codomain (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<and> codomain (cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) = domain (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<and> cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c h \<circ>\<^sub>c g \<circ>\<^sub>c f = id\<^sub>c (domain (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) \<and> (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f) = id\<^sub>c (domain (cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)))"
    using f1 hgf_iso by blast
  then have f16: "domain f = codomain (cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f))"
    using f14 f13 by presburger
  have f17: "h \<circ>\<^sub>c g \<circ>\<^sub>c f = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f"
    using f11 f6 f2 by blast
  have f18: "codomain (h \<circ>\<^sub>c g \<circ>\<^sub>c f) = codomain h"
    using f12 f8 by blast
  then have f19: "domain (f \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) = codomain h"
    using f16 f15 f7 by auto
  have f20: "domain (cc f) = codomain f \<and> codomain (cc f) = domain f \<and> cc f \<circ>\<^sub>c f = id\<^sub>c (domain f) \<and> f \<circ>\<^sub>c cc f = id\<^sub>c (domain (cc f))"
    using f1 f_iso by blast
  then have f21: "domain (cc f) = B"
    using f10 by meson
  have "domain (cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) = codomain h"
    using f15 f12 f8 by presburger
  then have f22: "domain (cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) = codomain (h \<circ>\<^sub>c g)"
    using f8 f6 by auto
  have f23: "(h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c cc f = h \<circ>\<^sub>c g"
    using f21 f20 f14 f12 f11 f2 by (metis (no_types) g_type id_right_unit2)
  have f24: "domain (cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) = codomain ((h \<circ>\<^sub>c g) \<circ>\<^sub>c f)"
    using f17 f15 by presburger
  have "domain f = A \<and> codomain f = B"
    using f3 f_type by blast
  then have f25: "cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c (h \<circ>\<^sub>c g) \<circ>\<^sub>c f = id\<^sub>c A"
    using f17 f15 f14 f13 by presburger
  have f26: "id\<^sub>c B = f \<circ>\<^sub>c cc f"
    using f21 f20 by presburger
  have f27: "codomain (id\<^sub>c B) = B"
    using f20 f10 f8 by (metis (full_types))
  have f28: "domain (id\<^sub>c B) = codomain f"
    using f26 f20 f7 by metis
  have f29: "\<forall>c ca cb. \<not> c : ca \<rightarrow> cb \<or> id\<^sub>c cb \<circ>\<^sub>c c = c"
    using id_left_unit2 by presburger
  then have f30: "((f \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) \<circ>\<^sub>c h) \<circ>\<^sub>c g = id\<^sub>c B"
    using f28 f27 f25 f24 f23 f22 f20 f19 f16 f14 f13 f10 f9 f6 f2 by (metis (no_types) f_type)
  have f31: "codomain ((f \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) \<circ>\<^sub>c h) = B"
    using f19 f16 f10 f8 by presburger
  have f32: "domain ((f \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) \<circ>\<^sub>c h) = codomain g"
    using f19 f7 f5 f4 by presburger
  have f33: "domain (h \<circ>\<^sub>c g) = domain g"
    using f7 f6 by blast
  have f34: "domain (cc h) = codomain h \<and> codomain (cc h) = domain h \<and> cc h \<circ>\<^sub>c h = id\<^sub>c (domain h) \<and> h \<circ>\<^sub>c cc h = id\<^sub>c (domain (cc h))"
    using f1 h_iso by blast
  have f35: "id\<^sub>c C \<circ>\<^sub>c g = g"
    using f29 g_type by blast
  have f36: "codomain f = domain g"
    using f10 f9 by presburger
  have f37: "codomain (h \<circ>\<^sub>c g) = codomain h"
    using f8 f6 by blast
  have f38: "domain h = C \<and> codomain h = D"
    using f3 h_type by blast
  have f39: "g \<circ>\<^sub>c f \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f) = cc h \<circ>\<^sub>c id\<^sub>c (domain (cc h))"
    using f37 f36 f35 f34 f33 f18 f16 f15 f6 f5 f2 by (metis (full_types))
  have f40: "domain (id\<^sub>c (domain (cc h))) = codomain h"
    using f34 f7 by (metis (no_types))
  have "id\<^sub>c (domain (cc h)) \<circ>\<^sub>c h = h"
    using f38 f34 f29 h_type by presburger
  then have f41: "g \<circ>\<^sub>c (f \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) \<circ>\<^sub>c h = id\<^sub>c C"
    using f40 f39 f34 f19 f16 f10 f9 f8 f5 f2 by fastforce
  have "domain ((f \<circ>\<^sub>c cc (h \<circ>\<^sub>c g \<circ>\<^sub>c f)) \<circ>\<^sub>c h) = C"
    using f19 f7 f5 by presburger
  then show ?thesis
    using f41 f32 f31 f30 f9 f1 by blast
qed
  
  

end