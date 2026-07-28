# FOL Port Diary

A running log of porting `Category_Set/Cfunc.thy` (HOL) to `FOL/Cfunc.thy` (plain Isabelle `FOL`).
Companion file: `FOL/typecheck.ml` (patched copy of `Category_Set/typecheck.ml`).

**Ground rule for this whole effort: `Category_Set/` and the old top-level `ETCS_*.thy` files are
never modified.** The FOL port is strictly additive under `FOL/`.

## Starting point

James Baxter's commit `61f74f4` ("Add beginning of FOL-based ETCS") added `FOL/Cfunc.thy` containing
only the Axiom-1 `axiomatization` block — genuinely just a beginning, and not even buildable: it was
missing the closing `end`. First fix was trivial (add `end`), confirmed via a headless
`isabelle build` of a throwaway session depending on `FOL`.

## Why this is harder than a search-and-replace

Isabelle's plain `FOL` object logic is a different foundation from `HOL`, not just different notation:

- No `smt`/`metis`/sledgehammer usable — see the `fol-proof-patterns-no-sledgehammer` memory for why
  (short version: if the session depends on `HOL-Eisbach`, these methods are technically *callable*
  but built entirely around HOL's type system, and hang for 60–90s+ on FOL goals instead of failing
  fast). Every `smt`/`metis` call in the HOL source had to be rewritten as an explicit proof.
- No `THE`/`Eps`/choice operator at all (confirmed empirically — `@{const_name The}` doesn't even
  elaborate). HOL's `inverse f = (THE g. ...)` has no direct FOL translation.
- No HOL `Main`-library vocabulary (`equiv`, `UNIV`, `Set`/`Relation` theory). HOL's
  `is_isomorphic_equiv : equiv UNIV {(X,Y). X \<cong> Y}` has no direct FOL translation either.
- `rule_format`+positional `of`, `proof safe` on an iff, and `auto`/`blast` on bundled conjunctions
  all behave subtly differently than in HOL and cost real debugging time (see the patterns memory).

## Section-by-section

**Base axiomatization + `cfunc_type` + basic lemmas (`comp_type`, `id_type`, etc.)** — ported
essentially mechanically. One real content change: `cfunc_type`'s codomain type is `o` (FOL's
formula type) not `bool` (that's HOL's) — every subsequent `bool`-returning definition
(`monomorphism`, `epimorphism`, `isomorphism`, `is_isomorphic`) needed the same change.

**`typecheck_cfuncs`/`etcs_*` tactic infrastructure** (`typecheck.ml` + the `method_setup`/`method`
block) — ported with two changes, nothing lost:
1. `typecheck.ml` hardcodes `Const ("HOL.Trueprop", _)` and `Const ("HOL.eq", _)` in a few spots
   (constant-name pattern matching for extracting typing/substitution facts). Everything else in that
   file is generic Pure/`Thm`/`Subgoal` ML with no HOL dependency. Patched the two names to their FOL
   equivalents (`IFOL.Trueprop`, `IFOL.eq`), confirmed via a small `ML \<open>error (...)\<close>` probe rather
   than guessing.
2. The `etcs_assocl`/`etcs_assocr`/`etcs_*_asm` macros use Eisbach's `method` keyword, which needs
   Eisbach loaded. Used `imports ... "HOL-Eisbach.Eisbach_Old_Appl_Syntax"` — Isabelle's own documented
   "Alternative Eisbach entry point for FOL, ZF etc." — rather than plain `Eisbach`. `HOL-Eisbach` was
   already built/cached on this machine, so depending on it cost nothing.

**Monomorphism/epimorphism section** — this is where `proof safe` vs `proof (rule iffI)` and the
`rule_format`+`of` positional-argument bug were found and fixed (full detail in the patterns memory).
One genuine *mathematical* gap, not just a tactic issue: `monomorphism_def2`'s converse direction
assumes only `codomain(g) = domain(f)` and `codomain(h) = domain(f)` (nothing about `domain(g)` vs
`domain(h)`), but the general `\<forall>g h A X Y. g:A→X \<and> h:A→X \<and> ...` fact needs a *shared* `A` for both
— i.e. needs `domain(g) = domain(h)`, not given directly. It's derivable: since `f \<circ>\<^sub>c g = f \<circ>\<^sub>c h` as
raw values, `domain(f \<circ>\<^sub>c g) = domain(f \<circ>\<^sub>c h)` follows from congruence, and `domain_comp` relates each
side back to `domain(g)`/`domain(h)`. (Epimorphism's converse direction has the dual gap, closed the
dual way via `codomain_comp`.) Verified with `isabelle eval_at ... "thm monomorphism_def3"` at the
user's request, confirming the exact intended statement.

**Isomorphism section** (in progress) — `inverse`/`f\<^bold>\<inverse>` redesigned as: prove `inverse_ex1`
(`\<exists>!`) directly by hand (mirroring the HOL uniqueness argument: `g' = g' \<circ>\<^sub>c id = g' \<circ>\<^sub>c (f \<circ>\<^sub>c g) =
(g' \<circ>\<^sub>c f) \<circ>\<^sub>c g = id \<circ>\<^sub>c g = g`), then `axiomatization inverse ... where inverse_spec: "isomorphism(f)
\<Longrightarrow> ..."` — a conservative Skolemization of the just-proved fact, not a new mathematical
commitment. `is_isomorphic_equiv` restated as `is_isomorphic_equivalence`, an explicit
`(\<forall>refl) \<and> (\<forall>sym) \<and> (\<forall>trans)` conjunction proved from the three separate component lemmas, since
HOL's `equiv`/`UNIV` packaging isn't available.

Recurring failure mode while writing this section: `auto`/`blast` failing (sometimes hanging) to
combine two separately-derived facts (e.g. `have "domain g' = codomain f"` and a separate premise)
back into the single bundled conjunction (`domain g' = codomain f \<and> codomain g' = domain f`, from
unfolding `cfunc_type_def`) that an instantiated rule's premise actually needs. Fix each time: derive
the *exact* bundled or unbundled shape the next step needs as its own named `have`, rather than
leaving the recombination to automation.

## Status

**`FOL/Cfunc.thy` is complete and independently verified** (2026-07-28): a from-scratch headless
`isabelle build` of the committed file (fresh session dir, not the dev scratch copy) finishes with
zero errors. Covers, in full: the Axiom-1 axiomatization, `cfunc_type` and basic composition lemmas,
the entire `typecheck_cfuncs`/`etcs_*` tactic infrastructure, monomorphism/epimorphism (with defs 2/3
and all composition lemmas), and isomorphism (defs 2/3, `inverse`/`f\<^bold>\<inverse>` via the Skolem-axiomatization
approach, `is_isomorphic`, `is_isomorphic_equivalence`, `iso_imp_epi_and_monic`, `isomorphism_sandwich`).
Sectioned to mirror the HOL original's structure (`section`/`subsection`/`subsubsection` headers match).

One recurring lesson from finishing the isomorphism section, worth restating: `comp_associative` used
as a bare `simp add:` rule always drives *both* sides of a goal toward full left-association, which
can destroy the exact adjacent pairing (e.g. `f\<^bold>\<inverse> \<circ>\<^sub>c f`) a cancellation step needs next. When a
`simp add: comp_associative` step fails with a goal that's "almost" but not quite matching, don't
throw more facts at it — compute the specific `comp_associative[of h g f]` instance explicitly (with
its two preconditions verified by hand) and chain named facts through an explicit `also have`
sequence instead. This was more reliable than any blanket `simp` invocation for multi-step
re-associations. See `fol-proof-patterns-no-sledgehammer` for this alongside the other patterns.

Next: pick the next theory in the HOL dependency order after `Cfunc.thy` (check `Category_Set/ROOT`
rather than guessing) and port it the same way.
