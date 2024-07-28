theory Cfunc
  imports Main "HOL-Eisbach.Eisbach"
begin

section \<open>Basic types and operators for the category of sets\<close>

typedecl cset
typedecl cfunc

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

subsection \<open>Tactics for applying typing rules\<close>

subsubsection \<open>typecheck_cfuncs: Tactic to construct type facts\<close>

(* check_cfunc determines if a given term is of type cfunc *)
ML \<open>
  fun check_cfunc binder_typs (t : term) = 
    case fastype_of1 (binder_typs, t) of
      Type (name, []) => (name = "Cfunc.cfunc") andalso not (loose_bvar (t, 0)) (* reject invalid terms with loose bvars *)
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
                (Const ("Cfunc.cfunc_type", _) $ t) $ _ $ _ => SOME t
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
              SOME insts => SOME (Thm.instantiate (TVars.empty, Vars.make insts) rule)
            | NONE => NONE
          end\<close>

ML \<open>fun is_type_rule_term t =
          case Logic.strip_imp_concl t of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("Cfunc.cfunc_type", _) $ _) $ _ $ _ => true
              | _ => false)
          | _ => false
                \<close>

ML \<open>fun is_type_rule thm = is_type_rule_term (Thm.concl_of thm)\<close>

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
                  val inst_thm = Thm.instantiate (TVars.empty, Vars.make insts') thm
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

ML \<open>fun elim_type_rule_prems_opt ctxt thm lems =
          let fun elim_type_rule_prems' thm [] = SOME thm
                | elim_type_rule_prems' thm (prem::prems) =
                    case elim_type_rule_prem ctxt thm prem lems of
                      SOME thm' => elim_type_rule_prems' thm' prems
                    | NONE => NONE
          in elim_type_rule_prems' thm (Thm.prems_of thm)
          end\<close>

(* variant that only eliminates type rules *)
ML \<open>fun elim_type_rule_prems_opt' ctxt thm lems =
          let fun elim_type_rule_prems' thm [] = SOME thm
                | elim_type_rule_prems' thm (prem::prems) =
                    case elim_type_rule_prem ctxt thm prem lems of
                      SOME thm' => elim_type_rule_prems' thm' prems
                    | NONE => if is_type_rule_term prem 
                              then NONE 
                              else (elim_type_rule_prems' (Thm.permute_prems 0 1 thm) prems)
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

ML \<open>fun typecheck_cfunc ctxt rules t = 
      let val rules' = rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
          val lems = construct_cfunc_type_lemmas ctxt rules' t
      in hd lems
      end\<close>

(* extract_prems attempts to extract premises from a term that has the form of a theorem *)
ML \<open>fun extract_prems ((@{term Trueprop}) $ P) = extract_prems P
      | extract_prems (@{term "Pure.imp"} $ P $ Q) = P::extract_prems Q
      | extract_prems _ = []\<close>

(* typecheck_cfuncs_subproof implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the Subgoal.FOCUS combinator *)
ML \<open>fun typecheck_cfuncs_subproof ctxt type_rules subgoal n (focus : Subgoal.focus) = 
          let val type_rules' = type_rules @ (#prems focus) @ Named_Theorems.get ctxt "Cfunc.type_rule"
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
ML \<open>fun typecheck_cfuncs_method opt_type_rules ctxt = 
      (fn thms => CONTEXT_TACTIC (typecheck_cfuncs_tac ctxt (these opt_type_rules @ thms) 1))\<close>

(* setup typecheck_cfuncs_method as a proof method in the theory *)
method_setup typecheck_cfuncs =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_method\<close>
  "Check types of cfuncs in current goal and add as assumptions of the current goal"

(* typecheck_cfuncs_all_method lifts typecheck_cfuncs_tac to a proof method that
  generates cfunc type facts for the first goal *)
ML \<open>fun typecheck_cfuncs_all_method opt_type_rule ctxt = 
      CONTEXT_METHOD (fn thms => 
        CONTEXT_TACTIC (ALLGOALS (typecheck_cfuncs_tac ctxt (these opt_type_rule @ thms))))\<close>

(* setup typecheck_cfuncs_method as a proof method in the theory *)
method_setup typecheck_cfuncs_all =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_all_method\<close>
  "Check types of cfuncs in all subgoals and add as assumptions of the current goal"

(* typecheck_cfuncs_prems_subproof implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the Subgoal.FOCUS combinator *)
ML \<open>fun typecheck_cfuncs_prems_subproof ctxt assms _ n (focus : Subgoal.focus) = 
          let val type_rules' = assms @ (#prems focus) @ Named_Theorems.get ctxt "Cfunc.type_rule"
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
ML \<open>fun typecheck_cfuncs_prems_method opt_type_rules ctxt = 
          (fn thms => CONTEXT_TACTIC (typecheck_cfuncs_prems_tac ctxt (these opt_type_rules @ thms) 1))\<close>

(* setup typecheck_cfuncs_prems_method as a proof method in the theory *)
method_setup typecheck_cfuncs_prems =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_prems_method\<close>
  "Check types of cfuncs in assumptions of the current goal and add as assumptions of the current goal"

subsubsection \<open>etcs_rule: Tactic to apply rules with ETCS typechecking\<close>

ML \<open>fun ETCS_resolve_subtac ctxt type_rules thm i (foc : Subgoal.focus) = 
      (* try to match the given theorem against the current subgoal*)
      case match_term [] (Thm.concl_of thm) (Thm.term_of (#concl foc)) of
        SOME insts =>
              (* certify any instantiations that result *)
          let val insts' = certify_instantiations ctxt [] insts
              (* instantiate the given theorem *)
              val inst_thm = Thm.instantiate (TVars.empty, Vars.make insts') thm
              (* generate typing lemmas and eliminate any typing premises required *)
              val type_lems =
                construct_cfunc_type_lemmas ctxt ((#prems foc) @ type_rules) (Thm.prop_of inst_thm)
              val inst_thm' = elim_type_rule_prems ctxt inst_thm type_lems
              (* generate typing lemmas for any remaining premises of the goal and try to eliminate them *)
              val prem_type_lems =
                flat (map (construct_cfunc_type_lemmas ctxt (type_rules)) (Thm.prems_of inst_thm'))
              val inst_thm'' = elim_type_rule_prems ctxt inst_thm' prem_type_lems
              (* look for unresolved type premises of the theorem *)
              val prems = Thm.prems_of inst_thm'';
              val type_prems = (filter (fn x => is_type_rule_term x) prems)
            (* resolve the current subgoal using the instantiated theorem *)
          in case type_prems of
               [] => resolve_tac ctxt [inst_thm''] i
             | _  => no_tac (* unresolved type premises, fail *)
          end
      | NONE => no_tac\<close>

ML \<open>fun ETCS_resolve_tac _    _          []          _ = all_tac
      | ETCS_resolve_tac ctxt type_rules (thm::thms) i = 
          (Subgoal.FOCUS (ETCS_resolve_subtac ctxt type_rules thm i) ctxt i)
            THEN ETCS_resolve_tac ctxt type_rules thms i\<close>

ML \<open>fun ETCS_resolve_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_resolve_tac ctxt (type_rules @ add_rules) thms 1)
      end\<close>

method_setup etcs_rule = 
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_resolve_method\<close>
  "apply rule with ETCS type checking"

subsubsection \<open>etcs_subst: Tactic to apply substitutions with ETCS typechecking\<close>

(* extract_subst_term extracts the term f of type cfunc from a theorem of the form "f = g" or "f \<equiv> g" *)
ML \<open>fun extract_subst_term rule =
          case Thm.concl_of rule of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("HOL.eq", _) $ t) $ _ => SOME t
              | _ => NONE)
          | (Const ("Pure.eq", _) $ t) $ _ => SOME t
          | _ => NONE
                \<close>

(* match_nested_term tries to apply match_term over the structure of a term until it finds a match *)
ML \<open>fun match_nested_term bound_typs pat (t1 $ t2) = (
        (* try matching the toplevel first *)
        case match_term bound_typs pat (t1 $ t2) of
          SOME insts => SOME insts
        | NONE =>
            (* otherwise try matching in left of application *)
            case match_nested_term bound_typs pat t1 of
              SOME insts => SOME insts
              (* otherwise try matching in right of application *)
            | NONE => match_nested_term bound_typs pat t2
      )
    | match_nested_term bound_typs pat (Abs (v, ty, t)) = (
        (* try matching the toplevel first *)
        case match_term bound_typs pat (Abs (v, ty, t)) of
          SOME insts => SOME insts
          (* otherwise try matching quantified term *)
        | NONE => match_nested_term bound_typs pat t
      )
      (* finally, just try regular match *)
    | match_nested_term bound_typs pat t = match_term bound_typs pat t
          \<close>

ML \<open>fun instantiate_typecheck ctxt thm type_rules insts =
      let val cinsts = certify_instantiations ctxt [] insts
          val inst_thm = Thm.instantiate (TVars.empty, Vars.make cinsts) thm
          val gen_type_lems = construct_cfunc_type_lemmas ctxt type_rules
          val type_lems = flat (map (gen_type_lems o snd) insts)
      in elim_type_rule_prems_opt ctxt inst_thm type_lems
      end\<close>

ML \<open>fun instantiate_typecheck' ctxt thm type_rules insts =
      let val cinsts = certify_instantiations ctxt [] insts
          val inst_thm = Thm.instantiate (TVars.empty, Vars.make cinsts) thm
          val gen_type_lems = construct_cfunc_type_lemmas ctxt type_rules
          val type_lems = flat (map (gen_type_lems o snd) insts)
      in elim_type_rule_prems_opt' ctxt inst_thm type_lems
      end\<close>

(* match_nested_term_typecheck tries to apply match_term over the structure of a term until it finds
  a match that typechecks to leave no premises*)
ML \<open>fun match_nested_term_typecheck ctxt thm type_rules bound_typs pat (t1 $ t2) = (
        (* try matching the toplevel first and check if it passes typechecking *)
        case Option.mapPartial 
              (instantiate_typecheck ctxt thm type_rules)
              (match_term bound_typs pat (t1 $ t2)) of
          SOME inst_thm => SOME inst_thm
        | NONE =>
            (* otherwise try matching in left of application *)
            case match_nested_term_typecheck ctxt thm type_rules bound_typs pat t1 of
              SOME inst_thm => SOME inst_thm
              (* otherwise try matching in right of application *)
            | NONE => match_nested_term_typecheck ctxt thm type_rules bound_typs pat t2
      )
    | match_nested_term_typecheck ctxt thm type_rules bound_typs pat (Abs (v, ty, t)) = (
       (* try matching the toplevel first and check if it passes typechecking *)
        case Option.mapPartial 
              (instantiate_typecheck ctxt thm type_rules)
              (match_term bound_typs pat (Abs (v, ty, t))) of
          SOME inst_thm => SOME inst_thm
          (* otherwise try matching quantified term *)
        | NONE => match_nested_term_typecheck ctxt thm type_rules bound_typs pat t
      )
      (* finally, just try regular match and instantiate *)
    | match_nested_term_typecheck ctxt thm type_rules bound_typs pat t = 
        Option.mapPartial 
          (instantiate_typecheck ctxt thm type_rules)
          (match_term bound_typs pat t)
          \<close>

ML \<open>fun ETCS_subst_subtac ctxt type_rules thm i (foc : Subgoal.focus) =
          (* extract the left-hand side from the conclusion of the theorem *) 
      let val subst_term = extract_subst_term thm
          (* extract current subgoal *)
          val subgoal = (Thm.term_of (#concl foc))
          (* try to match the given theorem against the current subgoal*)
          val inst_thm_opt = case subst_term of
              SOME t => match_nested_term_typecheck ctxt thm ((#prems foc) @ type_rules) [] t subgoal
            | NONE   => NONE
      in 
        case inst_thm_opt of
          SOME inst_thm => EqSubst.eqsubst_tac ctxt [0] [inst_thm] i
          | NONE => no_tac
      end\<close>

ML \<open>fun ETCS_subst_tac _    _          []          _ = all_tac
      | ETCS_subst_tac ctxt type_rules (thm::thms) i = 
          (Subgoal.FOCUS (ETCS_subst_subtac ctxt type_rules thm i) ctxt i)
            THEN ETCS_subst_tac ctxt type_rules thms i\<close>

ML \<open>fun ETCS_subst_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_subst_tac ctxt (type_rules @ add_rules) thms 1)
      end\<close>

method_setup etcs_subst = 
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_subst_method\<close> 
  "apply substitution with ETCS type checking"

method etcs_assocl declares type_rule = (etcs_subst comp_associative2)+
method etcs_assocr declares type_rule = (etcs_subst sym[OF comp_associative2])+

ML \<open>fun string_of_var (Const (str, _))    = str
      | string_of_var (Free (str, _))     = str
      | string_of_var (Var ((str, _), _)) = str
      | string_of_var _ = "" (*raise TERM ("string_of_var", [t])*)\<close>

ML \<open>fun ETCS_subst_asm_subtac type_rules thm i (foc : Subgoal.focus) =
          (* extract the left-hand side from the conclusion of the theorem *) 
          let val subst_term = (extract_subst_term thm)
          (* extract current subgoal *)
          val subgoal_prems = (#prems foc)
          val ctxt = (#context foc)
          (* try to match the given theorem against the current subgoal*)
          fun match_asm t (asm::asms) = 
              (* match_nested_term_typecheck ctxt thm type_rules bound_typs pat t *)
              (case match_nested_term_typecheck ctxt thm ((#prems foc) @ type_rules) [] t (Thm.prop_of asm) of
                SOME inst_thm => SOME (inst_thm, asm)
              | NONE => match_asm t asms)
            | match_asm _ [] = NONE;
          val inst_thm_opt = case subst_term of
              SOME t => match_asm t subgoal_prems
            | NONE   => NONE
          
      in 
        case inst_thm_opt of
          SOME (inst_thm, selected_prem) =>
                (* generalize selected premise for use outside of focus *)
            let val names_to_generalize = map (string_of_var o Thm.term_of o snd) (#params foc)
                val generalized_prem = Thm.generalize_cterm (Names.empty, Names.make_set names_to_generalize) 0 (Thm.cprop_of selected_prem)
                (* insert selected premise and substitute it using the instantiated theorem *)
            in ((cut_tac selected_prem i) THEN (EqSubst.eqsubst_asm_tac ctxt [0] [inst_thm] i),
                SOME generalized_prem)
            end
          | NONE => (no_tac, NONE)
      end\<close>

ML \<open>fun ETCS_subst_asm_tac _    _          []          _ goal = all_tac goal
      | ETCS_subst_asm_tac ctxt type_rules (thm::thms) i goal = 
          if Thm.nprems_of goal < i then Seq.empty
          else
            let val (foc as {context = ctxt', asms, params, ...}, goal') = Subgoal.focus ctxt i NONE goal
                val (inner_tac, selected_prem_opt) = ETCS_subst_asm_subtac type_rules thm i foc
                val tac1 = (Seq.lifts (Subgoal.retrofit ctxt' ctxt params asms i) (inner_tac goal'))
                val tac2 = case selected_prem_opt of
                  SOME selected_prem => 
                    let val match_prem = fn t => is_none (match_term [] (Thm.term_of selected_prem) t)
                        val remove_prem_tac = fn (foc : Subgoal.focus) => filter_prems_tac (#context foc) match_prem i
                    in (Subgoal.FOCUS_PARAMS remove_prem_tac ctxt i) THEN (Tactic.rotate_tac (0-1) i)
                    end
                | NONE => no_tac
            in (tac1 THEN tac2 THEN (ETCS_subst_asm_tac ctxt type_rules thms i)) goal
            end\<close>

ML \<open>fun ETCS_subst_asm_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_subst_asm_tac ctxt (type_rules @ add_rules) thms 1)
      end\<close>

method_setup etcs_subst_asm = 
  \<open>Runtime.exn_trace (fn _ => Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_subst_asm_method)\<close> 
  "apply substitution to assumptions of the goal, with ETCS type checking"

method etcs_assocl_asm declares type_rule = (etcs_subst_asm comp_associative2)+
method etcs_assocr_asm declares type_rule = (etcs_subst_asm sym[OF comp_associative2])+

subsubsection \<open>etcs_erule: Tactic to apply elimination rules with ETCS typechecking\<close>

ML \<open>fun ETCS_eresolve_subtac type_rules thm i (foc : Subgoal.focus) = 
      (* extract the first premise of the given theorem*)
      let val first_prem = try hd (Thm.prems_of thm)
          val subgoal_prems = (#prems foc)
          val ctxt = (#context foc)
          (* try to match the extracted premise against the current subgoal*)
          fun match_asm_inst t (asm::asms)= 
              (case Option.mapPartial
                  (instantiate_typecheck' ctxt thm ((#prems foc) @ type_rules)) 
                  (match_term [] t (Thm.prop_of asm)) of
                SOME thm => SOME (thm, asm)
              | NONE => match_asm_inst t asms)
            | match_asm_inst _ [] = NONE;
      in case Option.mapPartial (fn prem => match_asm_inst prem subgoal_prems) first_prem of
         SOME (inst_thm, selected_prem) =>
                (* generalize selected premise for use outside of focus *)
            let val names_to_generalize = map (string_of_var o Thm.term_of o snd) (#params foc)
                val generalized_prem = Thm.generalize_cterm (Names.empty, Names.make_set names_to_generalize) 0 (Thm.cprop_of selected_prem)
                (* insert selected premise and substitute it using the instantiated theorem *)
            in ((cut_tac selected_prem i) THEN (eresolve_tac ctxt [inst_thm] i),
                SOME generalized_prem)
            end
         | NONE => (no_tac, NONE)
               (*[] => eresolve_tac ctxt [inst_thm''] i*)
      end\<close>

ML \<open>fun ETCS_eresolve_tac _    _          []          _ goal = all_tac goal
      | ETCS_eresolve_tac ctxt type_rules (thm::thms) i goal = 
          if Thm.nprems_of goal < i then Seq.empty
          else
            let val (foc as {context = ctxt', asms, params, ...}, goal') = Subgoal.focus ctxt i NONE goal
                val (inner_tac, selected_prem_opt) = ETCS_eresolve_subtac type_rules thm i foc
                val tac1 = (Seq.lifts (Subgoal.retrofit ctxt' ctxt params asms i) (inner_tac goal'))
                val tac2 = case selected_prem_opt of
                  SOME selected_prem => 
                    let val match_prem = fn t => is_none (match_term [] (Thm.term_of selected_prem) t)
                        val remove_prem_tac = fn (foc : Subgoal.focus) => filter_prems_tac (#context foc) match_prem i
                    in (Subgoal.FOCUS_PARAMS remove_prem_tac ctxt i) THEN (Tactic.rotate_tac (0-1) i)
                    end
                | NONE => no_tac
            in (tac1 THEN tac2 THEN (ETCS_eresolve_tac ctxt type_rules thms i)) goal
            end\<close>

ML \<open>fun ETCS_eresolve_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_eresolve_tac ctxt (type_rules @ add_rules) thms 1)
      end\<close>

method_setup etcs_erule = 
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_eresolve_method\<close>
  "apply erule with ETCS type checking"

subsection \<open>Monomorphisms, Epimorphisms and Isomorphisms\<close>

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

lemma isomorphism_def2:
  "isomorphism(f) \<longleftrightarrow> (\<exists> g X Y. f : X \<rightarrow> Y \<and> g : Y \<rightarrow> X \<and> g \<circ>\<^sub>c f = id X \<and> f \<circ>\<^sub>c g = id Y)"
  unfolding isomorphism_def cfunc_type_def by auto

lemma isomorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "isomorphism(f) \<longleftrightarrow> (\<exists> g. g : Y \<rightarrow> X \<and> g \<circ>\<^sub>c f = id X \<and> f \<circ>\<^sub>c g = id Y)"
  using assms unfolding isomorphism_def2 cfunc_type_def by auto

definition inverse :: "cfunc \<Rightarrow> cfunc" ("_\<^bold>\<inverse>" [1000] 999) where
  "inverse(f) = (THE g. g : codomain(f) \<rightarrow> domain(f) \<and> g \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c g = id(codomain(f)))"

lemma inverse_def2:
  assumes "isomorphism(f)"
  shows "f\<^bold>\<inverse> : codomain(f) \<rightarrow> domain(f) \<and> f\<^bold>\<inverse> \<circ>\<^sub>c f = id(domain(f)) \<and> f \<circ>\<^sub>c f\<^bold>\<inverse> = id(codomain(f))"
proof (unfold inverse_def, rule theI', auto)
  show "\<exists>g. g : codomain f \<rightarrow> domain f \<and> g \<circ>\<^sub>c f = id\<^sub>c (domain f) \<and> f \<circ>\<^sub>c g = id\<^sub>c (codomain f)"
    using assms unfolding isomorphism_def cfunc_type_def by auto
next
  fix g1 g2
  assume g1_f: "g1 \<circ>\<^sub>c f = id\<^sub>c (domain f)" and f_g1: "f \<circ>\<^sub>c g1 = id\<^sub>c (codomain f)"
  assume g2_f: "g2 \<circ>\<^sub>c f = id\<^sub>c (domain f)" and f_g2: "f \<circ>\<^sub>c g2 = id\<^sub>c (codomain f)"
  assume "g1 : codomain f \<rightarrow> domain f" "g2 : codomain f \<rightarrow> domain f"
  then have "codomain(g1) = domain(f)" "domain(g2) = codomain(f)"
    unfolding cfunc_type_def by auto
  then show "g1 = g2"
    by (metis comp_associative f_g1 g2_f id_left_unit id_right_unit)
qed

lemma inverse_type[type_rule]:
  assumes "isomorphism(f)" "f : X \<rightarrow> Y"
  shows "f\<^bold>\<inverse> : Y \<rightarrow> X"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_left:
  assumes "isomorphism(f)" "f : X \<rightarrow> Y"
  shows "f\<^bold>\<inverse> \<circ>\<^sub>c f = id X"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_right:
  assumes "isomorphism(f)" "f : X \<rightarrow> Y"
  shows "f \<circ>\<^sub>c f\<^bold>\<inverse> = id Y"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_iso:
  assumes "isomorphism(f)"
  shows "isomorphism(f\<^bold>\<inverse>)"
  using assms inverse_def2 unfolding isomorphism_def cfunc_type_def by (rule_tac x=f in exI, auto)

lemma inv_idempotent:
  assumes "isomorphism(f)"
  shows "(f\<^bold>\<inverse>)\<^bold>\<inverse> = f"
  by (smt assms cfunc_type_def comp_associative id_left_unit inv_iso inverse_def2)
  
definition is_isomorphic :: "cset \<Rightarrow> cset \<Rightarrow> bool" (infix "\<cong>" 50)  where
  "X \<cong> Y \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> Y \<and> isomorphism(f))"

lemma id_isomorphism: "isomorphism (id X)"
  unfolding isomorphism_def
  by (rule_tac x="id X" in exI, auto simp add: id_codomain id_domain, metis id_domain id_right_unit)

lemma isomorphic_is_reflexive: "X \<cong> X"
  unfolding is_isomorphic_def
  by (rule_tac x="id X" in exI, auto simp add: id_domain id_codomain id_isomorphism id_type)

lemma isomorphic_is_symmetric: "X \<cong> Y \<longrightarrow> Y \<cong> X"
  unfolding is_isomorphic_def isomorphism_def 
  by (auto, rule_tac x="g" in exI, auto, metis cfunc_type_def)

lemma isomorphism_comp: 
  "domain f = codomain g \<Longrightarrow> isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  unfolding isomorphism_def by (auto, smt codomain_comp comp_associative domain_comp id_right_unit)

lemma isomorphism_comp': 
  assumes "f : Y \<rightarrow> Z" "g : X \<rightarrow> Y"
  shows "isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  using assms cfunc_type_def isomorphism_comp by auto

lemma isomorphic_is_transitive: "(X \<cong> Y \<and> Y \<cong> Z) \<longrightarrow> X \<cong> Z"
  unfolding is_isomorphic_def by (auto, metis cfunc_type_def comp_type isomorphism_comp)

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


text \<open>The lemma below corresponds to Exercise 2.1.7a in Halvorson\<close>
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
  assume "f \<circ>\<^sub>c s = f \<circ>\<^sub>c t"

  then have "(g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t"
    by (metis assms codomain_s codomain_t comp_associative)
  then show "s = t"
    using gf_monic codomain_s codomain_t domain_comp by (simp add: assms)
qed      

lemma comp_monic_imp_monic':
  assumes "f : X \<rightarrow> Y" "g : Y \<rightarrow> Z"
  shows "monomorphism (g \<circ>\<^sub>c f) \<Longrightarrow> monomorphism f"
  by (metis assms cfunc_type_def comp_monic_imp_monic)

text \<open>The lemma below corresponds to Exercise 2.1.7b in Halvorson\<close>
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

text \<open>The lemma below corresponds to Exercise 2.1.7c in Halvorson\<close>
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

text \<open>The lemma below corresponds to Exercise 2.1.7d in Halvorson\<close>
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

text \<open>The lemma below corresponds to Exercise 2.1.7e in Halvorson\<close>
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
  assumes f_iso: "isomorphism f"
  assumes h_iso: "isomorphism h"
  assumes hgf_iso: "isomorphism(h \<circ>\<^sub>c g \<circ>\<^sub>c f)"
  shows "isomorphism g"
proof -
  have "isomorphism(h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse>)"
    using assms by (typecheck_cfuncs, simp add: f_iso h_iso hgf_iso inv_iso isomorphism_comp')
  then show "isomorphism(g)"
    using assms by (typecheck_cfuncs_prems, smt comp_associative2 id_left_unit2 id_right_unit2 inv_left inv_right)
qed

end