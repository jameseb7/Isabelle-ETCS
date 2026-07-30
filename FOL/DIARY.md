# FOL Port Diary

A running log of porting the ETCS `Category_Set/*.thy` (HOL) theories to plain Isabelle `FOL` under
`FOL/`. The independent port currently runs from `Cfunc.thy` through the in-progress
`Exponential_Objects.thy` in the theory order recorded below.
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

## Theory port order

Dustin specified the full remaining port order (2026-07-28), so this no longer needs to be
re-derived from `Category_Set/*.thy` imports each time. After `Cfunc.thy` and `Product.thy`
(both done), the order is: **Terminal** (in progress) → Equalizer → Truth → Equivalence →
Coproduct → Axiom_Of_Choice → Initial → Exponential_Objects → Cardinality → Nats → Pred_Logic →
Fixed_Points → Quant_Logic → Nat_Parity → Countable → **ETCS** (last). Follow this list rather
than re-checking `imports` statements, unless a theory turns out to need something out of order.

## `FOL/Product.thy`

Ported `Category_Set/Product.thy` (729 lines HOL) section by section, verifying each section against
a headless build before moving to the next, same discipline as `Cfunc.thy`. Covers: the `cart_prod`
Axiom-2 axiomatization, `is_cart_prod` (dropping HOL's `is_cart_prod_triple` tuple-bundling
abbreviation — FOL has no tuple type, so the three components stay separate arguments throughout),
`canonical_cart_prod_is_cart_prod`, `cart_prods_isomorphic`, `product_commutes`, the `cart_prod_eq`
family (`eq`/`eqI`/`eq2`/`decomp`), `diagonal`/`cfunc_cross_prod` and their whole lemma family
(`identity_distributes_across_composition`, `cfunc_cross_prod_comp_cfunc_prod`, `id_cross_prod`,
`cfunc_cross_prod_comp_diagonal`, `cfunc_cross_prod_comp_cfunc_cross_prod`, `cfunc_cross_prod_mono`),
`swap` (`swap_ap`/`swap_cross_prod`/`swap_idempotent`/`swap_mono`), `associate_right`/`associate_left`
(with `right_left`/`left_right`/`product_associates`/both `crossprod_ap` lemmas), and finally
`distribute_right`/`distribute_left` (each with their `_left`/`_right` helper functions and `_mono`)
plus the "selecting pairs from a pair of pairs" family (`outers`/`inners`/`lefts`/`rights`).

Every HOL `smt`/`metis` call in this file (there were dozens — `associate_right_ap`,
`distribute_right_left_ap`, `right_left`, `left_right`, etc. all originally relied on them) was
rewritten as an explicit proof. The dominant technique throughout was the one from pattern #13:
compute each needed `comp_associative2`/`cfunc_prod_comp`/`cfunc_cross_prod_comp_cfunc_prod` instance
via `fact[OF arg1 arg2 arg3]` with the argument order matched by hand against the lemma's stated
variable order, then chain the results through explicit `have`/`also have` sequences — never left a
multi-step rewrite to `simp`/`blast`/`auto` search. This scaled to every lemma in the file, including
the large four-argument `outers`/`inners`/`lefts`/`rights` family, with no `smt`/`metis` substitute
ever needed.

Two new patterns beyond the `Cfunc.thy` set (recorded in `fol-proof-patterns-no-sledgehammer`, items
14–15):
- **Cancelling a doubled `id(X) \<circ>\<^sub>c id(X) \<circ>\<^sub>c f` requires an explicit intermediate typed fact for
  `id(X) \<circ>\<^sub>c f` itself**, then applying `id_left_unit2` to *that* combined term via `OF` — `simp add:
  id_left_unit2` alone doesn't chain two applications of the same conditional rewrite automatically
  when the two hits are nested rather than adjacent.
- **`right_left`/`left_right`-style "these two constructed isomorphisms cancel" proofs are much
  cleaner via the identity-decomposition trick than via induction on all objects**: apply
  `cart_prod_decomp` directly to `id(X)` itself (twice, for a doubly-nested product) to obtain
  `id(X) = \<langle>x1, \<langle>y, z\<rangle>\<rangle>` for fresh `x1`/`y`/`z`, rewrite `id`'s two occurrences via this, then the
  goal reduces to a single application of each direction's `_ap` lemma — no need for a general
  "equal after every generalized element" argument.

**Status: `FOL/Product.thy` is complete and independently verified** (2026-07-28): a from-scratch
`isabelle build -c` (clean, forcing full recompilation) of the committed file finishes with zero
errors, alongside the already-verified `FOL/Cfunc.thy`.

## `FOL/Terminal.thy`

Ported `Category_Set/Terminal.thy` (740 lines HOL) section by section against the theory port order
above. Covers: the Axiom-3 `terminal_func`/`one_set` axiomatization plus `one_separator`, the
`\<in>\<^sub>c` membership abbreviation and `nonempty`/`is_empty`, `terminal_object` (with
`terminal_objects_isomorphic`, `iso_to1_is_term`, `iso_to_term_is_term`, `single_elem_iso_one`),
`injective`/`surjective` (with the `cfunc_cross_prod_inj`/`_surj`/`_mono_converse`/`_surj_converse`
family), the interactions-with-terminal-objects family (`diag_on_elements`, `X_is_cart_prod1`/`2`,
`A_x_one_iso_A`, the four `left`/`right_cart_proj_one_*_inverse` lemmas,
`cfunc_cross_prod_right_terminal_decomp`, `cart_prod_elem_eq`, `element_pair_eq`, the two
`nonempty_*_imp_*_proj_epimorphism` lemmas, `cart_prod_extract_left`/`right`), and finally
`is_pullback`/`pullback_unique`/`pullback_iff_product`.

One design choice beyond a literal port: HOL's `iso_to1_is_term` and the forward direction of
`single_elem_iso_one` both independently re-derive "a set with one distinguished element `x` is
terminal" (build the unique `Y \<rightarrow> X` map as `x \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>`, then use `one_separator` to show every
`h : Y \<rightarrow> X` equals it by testing against elements of `Y`). Factored this out once as a private
helper lemma `unique_elem_gives_terminal`, used by both — same mathematical content as the HOL
original, just not duplicated.

Two new patterns beyond the `Product.thy` set (recorded in `fol-proof-patterns-no-sledgehammer`,
items 16-17):
- **`terminal_func_unique`, applied via plain `using ... terminal_func_unique by auto`, reliably
  proves `h = \<beta>\<^bsub>X\<^esub>` for a single typed `h`, but unreliably proves `A = B` for two *different*
  typed expressions both landing in `\<one>`** (e.g. `\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c p = q` where both sides are separately
  known to have type `... \<rightarrow> \<one>`). `auto` needs to instantiate the same conditional rule twice (once
  per side) and chain through transitivity, and it doesn't reliably do that when both instantiations
  are left implicit. Fix: name both applications explicitly — `have e1: "A = \<beta>\<^bsub>...\<^esub>\<close> using
  A_type terminal_func_unique by auto`, `have e2: "B = \<beta>\<^bsub>...\<^esub>\<close> using B_type terminal_func_unique
  by auto`, then `show "A = B" using e1 e2 by simp`. Same root cause as pattern #3, but easy to miss
  here because the "bundling" is a *transitivity* chain rather than a conjunction.
- **A pair of propositions that are logically equivalent but not literal object-level formulas
  (e.g. `is_pullback(...)` and `is_cart_prod(...)`, both type `o`) must be related with `\<longleftrightarrow>`, not
  HOL's `=`.** Plain FOL's `=` (`IFOL.eq`) is typed for `term`-sorted values only, not `o`; writing
  `(P) = (Q)` for two `o`-typed propositions is a type error (`No type arity o :: term`), not a proof
  failure — caught instantly at parse time, not during proof search. `pullback_iff_product`'s
  statement needed this fix (HOL's `(is_pullback ...) = (is_cart_prod ...)` became
  `is_pullback(...) \<longleftrightarrow> is_cart_prod(...)`).

**Status: `FOL/Terminal.thy` is complete and independently verified** (2026-07-28): a from-scratch
`isabelle build -c` of the committed file (alongside `Cfunc.thy` and `Product.thy`) finishes with
zero errors.

## `FOL/Equalizer.thy`

Ported `Category_Set/Equalizer.thy` (927 lines HOL) — the largest and structurally hardest theory so
far, for two reasons neither of which came up in `Cfunc.thy`/`Product.thy`/`Terminal.thy`:

1. **Hilbert's choice operator (`SOME`).** HOL defines `inverse_image`, `inverse_image_mapping`,
   `fibered_product`, and `fibered_product_morphism` all via `SOME`, which plain FOL has no
   equivalent of. Fix: the same conservative-Skolemization technique already used for
   `inverse`/`f\<^bold>\<inverse>` in `Cfunc.thy` — since `equalizer_exists` (Axiom 4) already proves existence
   for *any* parallel pair of same-codomain morphisms, applying it to the specific pair
   `f \<circ>\<^sub>c left_cart_proj(X,B)` / `m \<circ>\<^sub>c right_cart_proj(X,B)` (resp. the fibered-product analogue)
   licenses axiomatizing `inverse_image`+`inverse_image_mapping` together (resp.
   `fibered_product`+`fibered_product_morphism`) as its Skolem witness in one shot. This is a strict
   simplification over the HOL original: HOL needed *two* nested `SOME`s per construction (one for
   the object, one for the mapping, each separately justified via `someI2_ex`/`someI_ex`), which
   collapses to *one* axiomatization here, eliminating the intermediate `_is_equalizer`
   (existence-only) lemmas entirely — `_is_equalizer2` becomes a one-line corollary of the
   axiomatization.
2. **HOL tuples.** `subobject_of`, `relative_subset`, and `relative_member` all bundle a subobject's
   underlying set and its monomorphism into a HOL `cset \<times> cfunc` pair, accessed via `fst`/`snd`, and
   written with infix notation on the pair (`(B,m) \<subseteq>\<^sub>c X`, `x \<in>\<^bsub>X\<^esub> (B,m)`). FOL has no tuple type.
   Fix: flatten to plain multi-argument predicates — `subobject_of(B, m, X)`,
   `relative_subset(B, m, X, A, n)`, `relative_member(x, X, B, m)` — same convention already used for
   `is_cart_prod`/`is_pullback`. This loses the HOL infix syntax (a custom multi-slot mixfix
   preserving the `(_,_) \<subseteq>\<^sub>c _` surface form was considered but rejected as an unnecessary risk for
   a purely cosmetic win — plain predicate-call syntax is consistent with the rest of the port). Every
   downstream lemma referencing these (`inverse_image_subobject`, `in_inverse_image`,
   `fibered_product_pair_member`, `kernel_pair_subset`, ...) was rewritten accordingly; the separate
   `_def2` lemmas HOL needed to un-bundle `fst`/`snd` become unnecessary since the flat form *is* the
   primary definition.

Covers, in full: `equalizer`/`equalizer_def2`/`equalizer_eq`/`similar_equalizers`, Axiom 4
(`equalizer_exists`) + `equalizer_exists2`, `equalizers_isomorphic`,
`isomorphic_to_equalizer_is_equalizer`, `equalizer_is_monomorphism`, `regular_monomorphism` +
`epi_regmon_is_iso`, the Subobjects family (`factors_through`, `subobject_of`, `relative_subset`,
`relative_member`, `subobject_is_relative_subset`, `relative_subobject_member`), the Inverse Image
family (Skolemized `inverse_image`/`inverse_image_mapping` + all 9 dependent lemmas including
`inverse_image_pullback` and `in_inverse_image`), and the Fibered Products family (Skolemized
`fibered_product`/`fibered_product_morphism` + all 13 dependent lemmas including
`fibered_product_is_pullback`, the three `kern_pair_proj_iso_TFAE` lemmas, and
`terminal_fib_prod_iso`). Every HOL `smt`/`metis` call was rewritten as an explicit proof.

One simplification found while porting `kern_pair_proj_iso_TFAE1`: the HOL original case-splits on
whether the fibered product `X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X` is empty (using an element-based argument in one
branch, `one_separator`'s vacuous-implication trick in the other) to show
`fibered_product_left_proj = fibered_product_right_proj` when `f` is monomorphism. This is
unnecessary: `fibered_product_proj_eq` (the pullback's commutation clause) *already* gives
`f \<circ>\<^sub>c left_proj = f \<circ>\<^sub>c right_proj` directly for the kernel-pair case (setting `g := f`), so a single
`monomorphism_def3` cancellation closes it with no case split at all.

**Status: `FOL/Equalizer.thy` is complete and independently verified** (2026-07-28): a from-scratch
`isabelle build -c` of the committed file (alongside `Cfunc.thy`, `Product.thy`, `Terminal.thy`)
finishes with zero errors.

## `FOL/Truth.thy`

Ported `Category_Set/Truth.thy` (1291 lines HOL) — Axiom 5 (the truth-value object) plus everything
built on top of it: characteristic functions, the equality predicate, monomorphism/epimorphism
properties, pullbacks of epis/monos, fibers, the `kernel_pair_connection` lemma, set subtraction, and
graphs. This is the biggest theory ported so far (2191 lines FOL), both in raw size and in the number
of distinct design decisions it needed.

**Axiom 5 and `characteristic_func`.** `true_func`/`false_func`/`truth_value_set` (`\<t>`/`\<f>`/`\<Omega>`)
are axiomatized directly, matching the HOL original almost verbatim. HOL's `characteristic_func` is
`THE`-defined off `characteristic_function_exists`'s `\<exists>!`; ported via the by-now-standard
conservative-Skolemization technique (same as `inverse`/`f\<^bold>\<inverse>` in `Cfunc.thy`).

**`eq_pred` needed no fresh Skolemization at all.** Since `diagonal(X)` is always monic (`diag_mono`,
proved in `Product.thy`), HOL's separately-`THE`-defined `eq_pred(X)` is simply
`characteristic_func(diagonal(X))` — a direct instance of the already-Skolemized `characteristic_func`,
with no new axiomatization needed.

**Set Subtraction: a real (non-mechanical) Skolemization-design decision.** HOL's `set_subtraction`/
`complement_morphism` are `SOME`-defined off `Y \<setminus> (X,m)`, a `cset \<times> (cset \<times> cfunc)` bundle. The
obvious flattening — Skolemize `set_subtraction`/`complement_morphism` directly as functions of the
mono `m` alone (matching the `graph`/`graph_morph` precedent) — is WRONG: it silently breaks
`set_subtraction_right_iso` (`C \<setminus> (A,m) = C \<setminus> (B, m \<circ>\<^sub>c i)` for `i` iso), which crucially depends on
HOL's `SOME`-expression being syntactically a function of `characteristic_func(m)` alone, not of `m`
directly — two different monics with the *same* characteristic function are guaranteed the *same*
`SOME`-witness in HOL, a guarantee a naive per-`m` Skolemization would NOT reproduce. Fix: Skolemize
a primitive pair `set_subtraction_chi`/`complement_chi` directly off the characteristic function
`\<chi> : Y \<rightarrow> \<Omega>` (mirroring HOL's actual dependency), then define the user-facing
`set_subtraction(m)`/`m\<^sup>c` as `set_subtraction_chi(characteristic_func(m))`/
`complement_chi(characteristic_func(m))`. This makes `set_subtraction_right_iso`'s closing step —
"two monics with equal characteristic functions have equal complements" — a one-line congruence
(`set_subtraction_cong`/`complement_morphism_cong`) instead of an unprovable dead end.

**Graphs: same tuple-flattening convention as `Equalizer.thy`.** `functional_on(X, Y, R, m)` flattens
HOL's `cset \<times> cfunc` relation-bundle to a 4-argument predicate. `graph`/`graph_morph` Skolemize
cleanly off `f` alone (single `cfunc` argument, typed premise), matching the `graph`/`graph_morph`
precedent HOL itself already used (`domain f`/`codomain f`, no separate `X`/`Y` needed).
`graphs_are_functional`'s two-part goal (`\<exists>!y. ...`) was restructured around a single reusable
`\<And>y. relative_member(\<langle>x,y\<rangle>, ..., graph(f), graph_morph(f)) \<longleftrightarrow> f \<circ>\<^sub>c x = y` helper fact rather than
proving existence and uniqueness by separate ad hoc arguments (as HOL does) — mathematically the same
content, just less duplicated work. Likewise `functional_relations_are_graphs`'s surjectivity-of-`i`
argument was organized around one reusable `core_eq` helper (`f \<circ>\<^sub>c (lp \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)) =
rp \<circ>\<^sub>c (graph_morph(f) \<circ>\<^sub>c z)` for any `z : \<one> \<rightarrow> graph(f)`) instead of inlining the same associativity
chain twice.

**`kernel_pair_connection`: the single hardest lemma in the file, and the source of two new bug
patterns** (recorded as items 18-20 in `fol-proof-patterns-no-sledgehammer`):
- A bulk `using s1 s2 ... s7 by simp` closing a multi-hop derivation chain can silently over-rewrite
  *past* the intended target if the stated goal has the wrong intermediate form — `simp` doesn't stop
  at "the step you meant," it keeps applying every given fact until nothing more fires, which can
  produce a residual goal that's false in general rather than failing cleanly. The fix (once suspected)
  is always the same: restructure as an explicit `have ... also have ... finally show` chain, one
  named step per line, so each substitution is forced to happen exactly once in exactly the intended
  place.
- `equalizer_def`'s `\<exists> X Y. f:X\<rightarrow>Y \<and> ...` existential, unfolded directly via `unfolding equalizer_def
  by auto`, unpredictably succeeds or fails depending on whether the goal needs the schematic `X`/`Y`
  unified with a *specific already-known* type — succeeds when the conclusion doesn't mention that
  type at all (e.g. extracting a bare commutation equation), fails when it does (e.g. extracting a
  fact literally typed `... \<rightarrow> B` for a concrete `B`). `equalizer_def2` (which takes the parallel
  pair's type as an explicit premise, forcing the unification up front rather than leaving it to
  `auto`'s luck) is the robust fix whenever the extracted fact's own conclusion needs a named type.

Full lemma-by-lemma coverage: Section A (Axiom 5, `characteristic_func` + 4 basic lemmas), Section B
(4 relative-membership lemmas), the Equality Predicate subsection (`eq_pred` + 9 lemmas), the
Monomorphism/Epimorphism-properties subsection (`regmono_is_mono`, `mono_is_regmono`,
`epi_mon_is_iso`, `epi_is_surj`), `pullback_of_epi_is_epi1/2` + `pullback_of_mono_is_mono1/2`, the
Fiber subsection (`fiber`, `fiber_morphism` + 7 lemmas), `kernel_pair_connection`, the Set Subtraction
subsection (Skolemized `set_subtraction`/`complement_morphism` + 9 lemmas including the two
isomorphism lemmas), and the Graphs subsection (`functional_on`, Skolemized `graph`/`graph_morph` + 5
lemmas). The one deliberate omission is HOL's unnamed `card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4` fact (Proposition
2.2.2) — no `card`/set-comprehension theory exists in plain FOL, the fact is unnamed so nothing can
reference it, and nothing downstream depends on it; a `text` comment documents the omission in place.

**Status: `FOL/Truth.thy` is complete and independently verified** (2026-07-28): a from-scratch
`isabelle build -c` of the committed file (alongside `Cfunc.thy`, `Product.thy`, `Terminal.thy`,
`Equalizer.thy`) finishes with zero errors.

## FOL/Equivalence.thy

Ports `Category_Set/Equivalence.thy` (1487-line HOL original) to `FOL/Equivalence.thy` (~2012 lines),
the largest theory in the port so far. Covers equivalence relations, coequalizers, Axiom 6, regular
epimorphisms, epi-monic factorization, the image of a function, and `distribute_left`/`distribute_right`
as equivalence relations.

**Relations, flattened.** HOL bundles a relation's underlying set and monomorphism into a
`cset \<times> cfunc` pair for `reflexive_on`/`symmetric_on`/`transitive_on`/`equiv_rel_on`/`const_on_rel`;
flattened here to separate arguments, matching `subobject_of`'s convention throughout this port.
Each gets a `_def2` lemma exposing the underlying `\<exists>` witness directly (e.g. `reflexive_def2:
reflexive_on(X,Y,m) \<Longrightarrow> x \<in>\<^sub>c X \<Longrightarrow> \<exists>y. y \<in>\<^sub>c Y \<and> m \<circ>\<^sub>c y = \<langle>x,x\<rangle>`), used throughout the rest of
the file instead of re-unfolding `reflexive_on_def` each time. Two hangs were fixed here (before
either of the two new bug classes below were identified) by extracting a definitional `\<forall>` clause
into its own named `have ... unfolding ..._on_def by auto` fact first, then instantiating via
`[rule_format, where ...]`, rather than combining `unfolding X_on_def using ... by auto` in one step.

**Axiom 6** (`quotient_set`/`equiv_class`/`quotient_func`) is given directly via `axiomatization`,
not Skolemized — HOL already introduces these via direct `axiomatization`, not `SOME`/`THE`. The
tupled `R` (cset×cfunc pair) flattens to separate `R, m` args throughout. HOL's `[x]\<^bsub>R\<^esub>` notation
becomes a plain (non-bracket-nested, so notation-hang-safe — see below) `equiv_class_ap(x, R, m) \<equiv>
equiv_class(R, m) \<circ>\<^sub>c x` abbreviation.

**`coequalizer`** is new this theory (dual of `equalizer`): `coequalizer(E, m, f, g) \<longleftrightarrow> (\<exists>X Y. f:Y\<rightarrow>X
\<and> g:Y\<rightarrow>X \<and> m:X\<rightarrow>E \<and> m\<circ>\<^sub>cf=m\<circ>\<^sub>cg \<and> (\<forall>h F. h:X\<rightarrow>F \<and> h\<circ>\<^sub>cf=h\<circ>\<^sub>cg \<longrightarrow> \<exists>!k. k:E\<rightarrow>F \<and> k\<circ>\<^sub>cm=h))`.
`coequalizer_def2` needs the same `obtain X' Y' ... have XX': X=X' using ... unfolding cfunc_type_def
by auto` bridging pattern as `equalizer_def2` (documented as proof-pattern item 19 from `Truth.thy`,
re-encountered identically here in `coequalizer_unique` and `reg_epi_and_mono_is_iso`).

**`epi_monic_factorization`** (with the `coequalizer(...)` conjunct) is kept distinct from
`epi_monic_factorization2` (drops `coequalizer`, keeps `epimorphism(g)` instead), because the
Skolemized `image_of` axiomatization needs the coequalizer-preserving version — downstream lemmas
(`image_rest_map_coequalizer`, used via `coequalizer_unique` in `images_iso`/`image_rel_subset_conv`)
need the coequalizer fact, not just epimorphism.

**`image_of`/`image_restriction_mapping`/`image_subobject_mapping`**: Skolemized together off
`epi_monic_factorization`, collapsing HOL's 3-stage `SOME`/`SOME`/`THE` chain into one
`axiomatization` (`image_of_spec`). **First attempt used custom mixfix notation mirroring HOL's
`f\<lparr>A\<rparr>\<^bsub>n\<^esub>` / `f\<restriction>\<^bsub>A,n\<^esub>` / `[f\<lparr>A\<rparr>\<^bsub>n\<^esub>]map` (the last nesting `[...]` around `\<lparr>...\<rparr>`),
and this caused numerous unrelated `by simp`/`by auto` calls to hang indefinitely (100s+, zero
progress) — a failure mode never seen anywhere else in this multi-thousand-line port. Root cause:
parser/pretty-printer pathology from the nested bracket notation itself, not a proof error. Fix:
dropped all custom notation, switched to plain function-call syntax (`image_of(f, A, n)` etc.,
matching the established "no custom mixfix for flattened multi-arg constants" convention already used
for `subobject_of`/`relative_subset`) — the whole batch then built in ~28s with zero hangs. Recorded
as proof-pattern item 21.

**`subset_inv_image_iff_image_subset`** (Proposition 2.3.9) hit a genuine `also`/`finally`
"Vacuous calculation result" error in its `fd_eq`/`mh_eq` derivations — the same calc-chain idiom
that works everywhere else in this file (dozens of successful uses) failed here for reasons not
fully diagnosed. Fixed by replacing the `also`/`finally` chain with an explicit flat sequence of
named `have`s (`s1`, `s2`, ...) closed by a single `using s1 s2 ... by simp`, the more defensive
style already favored elsewhere when a derivation chain is nested inside other `have`/`proof -`
blocks.

**Two more new proof-pattern bugs**, both surfaced while extracting conjuncts from the Skolemized
`image_of_spec` and while closing `epi_monic_factorization`'s witness existential — recorded as
items 22-23 in `fol-proof-patterns-no-sledgehammer`:
- `conjunct1`/`conjunct2` must chain onto the *fact*, not the standalone rule: `fact[..., THEN
  conjunct2] by (rule conjunct1)`, never `by (rule conjunct2[THEN conjunct1])`.
- Building a flat "witness" conjunction for an `\<exists>x y. P \<and> Q \<and> ...`-shaped goal must be split into
  two safe steps: (1) `have witness: "A \<and> B \<and> ..." proof (intro conjI) show "A" by (rule factA)
  next ... qed` (safe, no existential wrapper), then (2) `show ?thesis by (rule exI[where x=...], ...,
  rule witness)` (safe, trivial match after instantiation) — combining `exI` and `conjI` in one
  `intro` on an existential+conjunction goal fails cleanly with "Failed to refine any pending goal"
  every time it was tried, reconfirming proof-pattern item 12 from `Product.thy`.

**`distribute_left`/`distribute_right` as Equivalence Relations**: `left_pair_subset`/
`right_pair_subset` reuse `distribute_right`/`distribute_left` and `cfunc_cross_prod_mono` (both
already in `Product.thy`) plus `composition_of_monic_pair_is_monic`. `left`/`right_pair_reflexive`,
`left`/`right_pair_symmetric`, and `left`/`right_pair_transitive` are built directly against `s`/`t`/
`u` as whole elements (never decomposed into `X`/`Z`-components unless the decomposition is actually
needed to invoke `symmetric_def2`/`transitive_def2`), which is a simplification versus HOL's own
proof style — same mathematical content, fewer intermediate obtains. `left_pair_equiv_rel`/
`right_pair_equiv_rel` are one-line combinations via `equiv_rel_on_def`.

Full lemma-by-lemma coverage: `reflexive_on`/`symmetric_on`/`transitive_on`/`equiv_rel_on`/
`const_on_rel` + 3 `_def2` lemmas + `kernel_pair_equiv_rel`, Axiom 6 + `equiv_class_ap`,
`coequalizer`/`coequalizer_def2`/`coequalizer_unique`/`coequalizer_is_epimorphism`,
`canonical_quotient_map_is_coequalizer`/`canonical_quot_map_is_epi`, `regular_epimorphism`/
`reg_epi_and_mono_is_iso`, `epimorphism_coequalizer_kernel_pair`/`epimorphisms_are_regular`,
`epi_monic_factorization`(2), the Skolemized `image_of` triple + 7 lemmas, `image_self`/
`image_smallest_subobject`/`images_iso`/`image_subset_conv`/`image_rel_subset_conv`,
`subset_inv_image_iff_image_subset`/`in_inv_image_of_image`, and the 10-lemma
`distribute_left`/`distribute_right`-as-equivalence-relations family.

**Status: `FOL/Equivalence.thy` is complete and independently verified** (2026-07-29): a from-scratch
`isabelle build -c` of the file (alongside `Cfunc.thy`, `Product.thy`, `Terminal.thy`, `Equalizer.thy`,
`Truth.thy`) finishes with zero errors. Committed as `f2139f4` (pushed).

## FOL/Coproduct.thy

Ports `Category_Set/Coproduct.thy` (2407-line HOL original) to `FOL/Coproduct.thy` (3309 lines), the
largest theory in the port so far. Covers Axiom 7 (coproducts), coproduct function properties, the
equality predicate's interaction with coproducts, the bowtie product, boolean cases, distribution of
products over coproducts (both directions), casting between a set and a subset/complement, generic
case-analysis (`cases`/`true_case`/`false_case`), and coproduct set properties (commutativity,
associativity, distribution, isomorphism-preservation, `X \<Coprod> X \<cong> X \<times>\<^sub>c \<Omega>`).

**`is_coprod`** drops HOL's `is_coprod_triple` tuple-abbreviation (`cset \<times> cfunc \<times> cfunc`) entirely —
FOL has no tuple type, so it simply takes all five arguments (`W, i0, i1, X, Y`) directly, matching the
`subobject_of`-style convention used throughout the port.

**Two constants defined directly as the generic isomorphism-inverse** (`_\<^bold>\<inverse>`, from `Cfunc.thy`)
rather than freshly Skolemized, once the corresponding map was already shown to be an isomorphism —
the same technique introduced for `case_bool` and `dist_prod_coprod_left` this theory, avoiding HOL's
`THE` entirely with zero fresh Skolemization:
- `case_bool = (\<t> \<amalg> \<f>)\<^bold>\<inverse>` (inverse of `truth_value_set_iso_1u1`)
- `dist_prod_coprod_left(A, B, C) = (factor_prod_coprod_left(A, B, C))\<^bold>\<inverse>` (inverse of
  `dist_prod_coprod_iso`)
- `try_cast(m) = (into_super(m))\<^bold>\<inverse>` (inverse of `into_super_iso`)

`dist_prod_coprod_right`/`factor_prod_coprod_right` are instead derived *algebraically*, composed
from `swap` and the left-side functions (`factor_prod_coprod_right(A,B,C) = swap(C,A∐B) \<circ>\<^sub>c
factor_prod_coprod_left(C,A,B) \<circ>\<^sub>c (swap(A,C)⋈swap(B,C))`), reusing every left-side lemma rather than
re-deriving injectivity/surjectivity for the right-hand family from scratch. The mutual-inverse
cancellation lemmas (`factor_dist_prod_coprod_right`/`dist_factor_prod_coprod_right`) needed long but
fully mechanical `swap_idempotent`/`cfunc_bowtie_prod_comp_cfunc_bowtie_prod`/`id_bowtie_prod`
cancellation chains, using `define` to abbreviate the two composite bowtie maps.

**A general Cfunc/Terminal-level fact never needed until this theory, `injective_imp_monomorphism`,
was added locally** (not re-opening the already-committed `Terminal.thy`) the first time it was
needed, in `left_coproj_are_monomorphisms`.

**Several lemmas were proven with a noticeably shorter strategy than HOL's own low-level
injective/surjective case-split proofs**, once the relevant coproduct machinery was in place:
- `coprod_pres_iso` (`A≅C ⟹ B≅D ⟹ A∐B≅C∐D`) and `prod_pres_iso` are proven by directly constructing
  the two-sided inverse (`(left_coproj(C,D)∘f) \<amalg> (right_coproj(C,D)∘g)` and its mirror, or
  `f\<^bold>\<inverse> \<times>\<^sub>f g\<^bold>\<inverse>`) and checking cancellation on the four generators/via
  `cfunc_cross_prod_comp_cfunc_cross_prod`, instead of HOL's full injective/surjective proof from
  scratch.
- `coprod_case_bool_true`/`coprod_case_bool_false`, `cfunc_bowtieprod_inj`/`_surj_converse` and
  several others were restructured around small reusable pointwise helper facts (e.g. `lc_fg`/`rc_fg`
  in `cfunc_bowtieprod_inj`) proven once and reused across all case-split branches, rather than
  re-deriving the same associativity chain in each branch as HOL does.

**Recurring new proof-pattern bug, now the single most common fix needed in this port:
composition-associativity grouping mismatches.** `\<circ>\<^sub>c` is right-associative infixr, so a stated goal
`f \<circ>\<^sub>c g \<circ>\<^sub>c h` parses as `f \<circ>\<^sub>c (g \<circ>\<^sub>c h)`, never `(f \<circ>\<^sub>c g) \<circ>\<^sub>c h` — whenever a `have`'s stated goal used
the opposite (explicitly-parenthesized) grouping from what a cited fact naturally produces, `by simp`
failed with "Failed to apply initial proof method" even though the two terms are provably equal via
associativity. The fix is always the same: insert an explicit intermediate `have` using
`comp_associative2[OF f_type g_type h_type]` to bridge the two groupings before combining — this
became routine in the long composition chains built from `swap`/`cfunc_bowtie_prod`/
`factor_prod_coprod_left` pieces (`factor_prod_coprod_right_ap_left`/`_ap_right`,
`dist_prod_coprod_right_ap_left`/`_ap_right`, `factor_dist_prod_coprod_right`/
`dist_factor_prod_coprod_right`, `coproduct_associates`, `coprod_pres_iso`, `coproduct_with_self_iso`
all needed multiple such bridges). A closely related hard parse error (not a proof failure):
parenthesizing a nested fact expression directly inside an `[OF ...]` list, e.g. `comp_associative2[OF
a_type b_type (foo[OF c_type])]`, is invalid syntax ("Bad arguments for attribute OF") — the nested
fact must always be extracted as its own named `have` first. Also re-hit the letter+digit
variable-collision bug (proof-pattern item 20) with `h2` as a bound variable name inside `is_coprod`'s
own definition, fixed by renaming to `hh` throughout.

Full lemma-by-lemma coverage: Axiom 7 + `is_coprod`/`is_coprod_def2`/`canonical_coprod_is_coprod`/
`coprods_isomorphic`; the Coproduct Function Properties section (`cfunc_coprod_comp`, `id_coprod`,
`injective_imp_monomorphism`, `coproducts_disjoint`, `left`/`right_coproj_are_monomorphisms`,
`coprod_eq`/`eqI`/`eq2`/`decomp`, `coprojs_jointly_surj`, `maps_into_1u1`, `coprod_preserves_left`/
`right_epi`, `truth_value_set_iso_1u1`); `eq_pred_left`/`right_coproj`; the Bowtie Product section
(`cfunc_bowtie_prod` def+type+ap+unique, `identity_distributes_across_composition_dual`,
`coproduct_of_beta`, `cfunc_bowtieprod_comp_cfunc_coprod`, `id_bowtie_prod`,
`cfunc_bowtie_prod_comp_cfunc_bowtie_prod`, `cfunc_bowtieprod_epi`/`inj`/`inj_converse`/`iso`/
`surj_converse`); Boolean Cases (`case_bool` + 8 lemmas); the full Distribution of Products over
Coproducts section, both left (`factor_prod_coprod_left`/`dist_prod_coprod_left` + 13 lemmas) and
right (`factor_prod_coprod_right`/`dist_prod_coprod_right` + 10 lemmas); Casting between Sets
(`into_super` + 4 lemmas, `try_cast` + 7 lemmas); Cases (`cases`/`true_case`/`false_case`); and
Coproduct Set Properties (`coproduct_commutes`, `coproduct_associates`,
`product_distribute_over_coproduct_left`/`right`, `prod_pres_iso`, `coprod_pres_iso`,
`coproduct_with_self_iso`, `oneUone_iso_\<Omega>`). The one deliberate omission is HOL's unnamed `card {x. x
\<in>\<^sub>c \<Omega> \<Coprod> \<Omega>} = 4` fact (dual to Proposition 2.2.2) — matching the identical omission of `Truth.thy`'s
`card {x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c \<Omega>} = 4`: no `card`/set-comprehension theory exists in plain FOL, the fact is
unnamed so nothing can reference it, and nothing downstream depends on it.

**Status: `FOL/Coproduct.thy` is complete and independently verified** (2026-07-29): a from-scratch
`isabelle build -c` of the file (alongside `Cfunc.thy`, `Product.thy`, `Terminal.thy`, `Equalizer.thy`,
`Truth.thy`, `Equivalence.thy`) finishes with zero errors. Copied into
`/home/dusty/Isabelle-ETCS/FOL/Coproduct.thy`; not yet committed pending user confirmation.

## FOL/Axiom_Of_Choice.thy

Ports `Category_Set/Axiom_Of_Choice.thy` (135-line HOL original, by far the smallest theory in the
port so far) — `section_of`/`split_epimorphism` (Definition 2.7.1), Axiom 11 (Axiom of Choice), and
five consequence lemmas. No new Skolemization or tuple-flattening was needed: every dependency
(`nonempty`, `epi_monic_factorization2`, `monomorphism_def2`/`3`, `epimorphism_def2`/`3`,
`regular_epimorphism`, `epimorphisms_are_regular`, `coequalizer_is_epimorphism`, `mono_is_regmono`,
`try_cast`/`try_cast_m_m`/`set_subtraction` from `Coproduct.thy`/`Truth.thy`) already existed with a
matching signature.

**Two proofs simplified relative to HOL's own route**, both by proving `epimorphism`/`monomorphism`
directly via `epimorphism_def3`/`monomorphism_def3` from the section/retraction equation, rather than
building a `coequalizer(...)` from scratch and going through `coequalizer_is_epimorphism`:
- `split_epis_are_regular` (Exercise 2.7.2i): given `f \<circ>\<^sub>c s = id(Y)`, for any `a,b : Y \<rightarrow> A` with
  `a \<circ>\<^sub>c f = b \<circ>\<^sub>c f`, composing both sides with `s` on the right and simplifying via `f \<circ>\<^sub>c s = id(Y)`
  gives `a = b` directly — `epimorphism(f)` in ~7 lines, then `epimorphisms_are_regular` finishes it.
- `sections_are_regular_monos` (Exercise 2.7.2ii): the dual argument (compose on the left with `f`)
  gives `monomorphism(s)` directly, then `mono_is_regmono` finishes it.

Both are markedly shorter than HOL's `unfolding coequalizer_def` + heavy `smt` construction, and
needed no `also`/`finally` chain, matching the general "prove the simpler intermediate fact directly,
then reuse an existing general lemma" strategy already used repeatedly in `Coproduct.thy`.

**`monos_give_epis` (Proposition 2.6.8)**, the largest lemma in the file, follows HOL's own strategy
closely: factor `f = m \<circ>\<^sub>c g` (epi-monic factorization), show `g` is also monic (hence iso, via
`epi_mon_is_iso`), take an arbitrary element `x : X` to handle the "off-image" branch of `Y`, and
build the retraction as `h = (g\<^bold>\<inverse> \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>Y\<setminus>(E,m)\<^esub>)) \<circ>\<^sub>c try_cast(m)`, reusing `try_cast_m_m`
and `left_coproj_cfunc_coprod` to show `h \<circ>\<^sub>c f = id(X)` pointwise, then `one_separator` to lift to
full equality and `surjective_is_epimorphism` for the epimorphism conclusion. One associativity-grouping
bug (proof-pattern item 24, the same class as `Coproduct.thy`'s most common fix) hit on the first build
attempt: `h \<circ>\<^sub>c (f \<circ>\<^sub>c yy)` with `f` unfolded to `m \<circ>\<^sub>c g` produces `h \<circ>\<^sub>c ((m \<circ>\<^sub>c g) \<circ>\<^sub>c yy)`, which does not
`simp`-match the intended `h \<circ>\<^sub>c (m \<circ>\<^sub>c (g \<circ>\<^sub>c yy))` without an explicit bridging
`comp_associative2[OF yy_type g_type m_type]` step first — fixed by inserting that as its own named
`have` before the substitution, the standard fix for this bug class.

Full lemma-by-lemma coverage: `section_of`/`split_epimorphism`/`split_epimorphism_def2`/
`sections_define_splits`, Axiom 11 (`axiom_of_choice`), `epis_give_monos`/`epis_are_split`,
`monos_give_epis`, `split_epis_are_regular`, `sections_are_regular_monos`.

**Status: `FOL/Axiom_Of_Choice.thy` is complete and independently verified** (2026-07-29): a
from-scratch `isabelle build -c` of the file (alongside `Cfunc.thy`, `Product.thy`, `Terminal.thy`,
`Equalizer.thy`, `Truth.thy`, `Equivalence.thy`, `Coproduct.thy`) finishes with zero errors. Copied
into `/home/dusty/Isabelle-ETCS/FOL/Axiom_Of_Choice.thy`; not yet committed pending user confirmation.

Next theory per the port order above: **Initial**.

## FOL/Initial.thy

Ports `Category_Set/Initial.thy` (230-line HOL original) to `FOL/Initial.thy`. The theory continues
to import `Coproduct`, exactly as the HOL theory does; it does not introduce an unnecessary
dependency on `Axiom_Of_Choice` merely because that independent theory precedes it in the requested
port order.

**Axiom 8 and initial objects.** `initial_func`/`emptyset` and their three axioms port directly,
with `initial_object` returning FOL's proposition type `o` rather than HOL's `bool`.
`emptyset_is_initial` explicitly constructs the unique map. For `initial_iso_empty`, the HOL proof's
single `metis` invocation is replaced by a direct argument: obtain the map `X \<rightarrow> \<emptyset>` supplied
by initiality, show that any alleged element of `X` would compose to an impossible element of
`\<emptyset>`, and hence prove the map injective and surjective vacuously before applying
`epi_mon_is_iso`.

**Empty coproducts and products.** `coproduct_with_empty` explicitly uses
`id(X) \<amalg> initial_func(X)` and `left_coproj(X, \<emptyset>)` as inverse maps. Their first cancellation is
`left_coproj_cfunc_coprod`; the second is proved on both coproduct injections and lifted by
`cfunc_coprod_unique`. `empty_prod_X` and `X_prod_empty` then apply
`function_to_empty_is_iso` to the appropriate product projection. This replaces all HOL
`metis`/`smt` calls with typed, named steps.

**Emptiness consequences.** `no_el_iff_iso_empty`, `initial_maps_mono`,
`iso_empty_initial`, `function_to_empty_set_is_iso`, and both
`prod_iso_to_empty_left`/`right` are all ported. The recurring proof is made explicit throughout:
turn `is_empty(X)` into `\<not>(\<exists>x. x \<in>\<^sub>c X)`, eliminate an alleged witness with `exE`, and use
`notE` after composition or pairing produces the forbidden element. In particular,
`iso_empty_initial` uses `one_separator` with a meta-level `\<And>x` premise, not an object-level
`\<forall>x` formula.

The HOL tuple notation `(\<emptyset>, \<alpha>\<^bsub>X\<^esub>) \<subseteq>\<^sub>c X` in `empty_subset` is flattened to
`subobject_of(\<emptyset>, initial_func(X), X)`, matching the FOL `Equalizer.thy` convention.
The final four initial/terminal-object coproduct/product isomorphisms are retained in full and use
the already-ported `coprod_pres_iso`, `prod_pres_iso`, coproduct/product commutativity, and explicit
instances of isomorphism transitivity.

One unnamed HOL-only fact is deliberately omitted: Proposition 2.2.1,
`card ({(X,m). (X,m) \<subseteq>\<^sub>c \<one>} // ...) = 2`. Plain FOL has no HOL set-comprehension,
quotient-set, or cardinality library with which to state it; because the theorem is unnamed, nothing
downstream can reference it. A `text` block records the omission in `Initial.thy`, consistently with
the analogous unnamed cardinality omissions in `Truth.thy` and `Coproduct.thy`.

Two FOL proof-engineering lessons were reinforced during this theory:
- Do not ask `auto` to unpack `\<forall>Y. \<exists>!f. ...` and choose a concrete `Y` in one step. Split it
  into `iffD1`, `spec`, `ex1E`, and `exE`; the broad call can enter expensive search.
- A negated premise such as `emptyset_is_empty: \<not>(x \<in>\<^sub>c \<emptyset>)` is not itself a rule with
  conclusion `False`; combine it with the positive fact explicitly via `notE`. Likewise,
  `one_separator` requires its stated meta-level `\<And>x` premise, not an object-level universal.

**Status: `FOL/Initial.thy` is complete and independently verified** (2026-07-29): the full theory
processes successfully in Isabelle/jEdit, and a headless `isabelle build` of the independent
`ETCS_FOL_Initial` session finishes with zero errors. The next theory per the requested port order
is **Exponential_Objects**.

## FOL/Exponential_Objects.thy

**Progress checkpoint (2026-07-29).** The independent FOL port is in progress. The exponential
object/evaluation axioms, transpose operation, exponential action on arrows, inverse transpose,
elementwise sharp/flat results, `metafunc`, `cnufatem`, and the first meta-composition results have
been translated. The HOL source remains unchanged.

HOL definitions that used definite description (`THE`) have no direct FOL counterpart. They are
being replaced by conservative Skolem constants with specification axioms proved satisfiable from
the corresponding existence-and-uniqueness results before use. This has been done for inverse
transpose, `cnufatem`, `meta_comp2`, and the parameter maps reached so far.

The recurring proof changes are explicit FOL typing with `typecheck_cfuncs`, tuple-form arguments
such as `eval_func(X,A)`, and named equality chains in place of HOL-only automation. In the current
meta-composition proof, product elements are decomposed using `cart_prod_decomp` together with
`one_unique_element`; `fastforce` then identifies the terminal component. A separate typed fact
`domain(K) = X` is used to normalize the `left_cart_proj(domain(K),\<one>)` expression left by
unfolding `metafunc`.

**Verified frontier:** headless `isabelle eval_at -l FOL` succeeds through `exp_pres_iso_left`,
including
`meta_comp_on_els`, `meta_comp2_def5`, the meta-composition identity and associativity laws, both
parameter-map element laws, `exp_one`, `exp_empty`, and `one_exp`.
`meta_comp_on_els` now proves its difficult point-evaluation step explicitly: it calculates the
right product projection, applies `inv_transpose_of_composition`, and concludes with
`transpose_func_unique`. The identity laws are explicit calculation chains through
`meta_comp2_def3`, `cnufatem_metafunc`, and the typed composition unit laws.

The `exp_one` surjectivity argument now uses a concrete inverse pair for
`left_cart_proj(\<one>,\<one>)` and an explicit transpose-based witness. Its evaluation equation is
proved by typed associativity and inverse/unit calculations rather than broad proof search.
In `exp_empty`, equality of `id(\<emptyset>) \<times>\<^sub>f z` and
`id(\<emptyset>) \<times>\<^sub>f f\<^sup>\<sharp>` is proved directly with `one_separator`: an alleged
element of their domain `\<emptyset> \<times>\<^sub>c \<one>` projects to an element of `\<emptyset>`,
contradicting `emptyset_is_empty`. This removes the unused product/empty isomorphism witnesses from
the HOL proof and supplies the meta-level element premise that `blast` could not synthesize.
For `one_exp`, the original single `metis`-style uniqueness step is split explicitly. Nonemptiness
provides a witness, terminality gives every element the same evaluation equation, and
`transpose_func_unique` identifies every element with
`\<beta>\<^bsub>X \<times>\<^sub>c \<one>\<^esub>\<^sup>\<sharp>`.
`power_rule` is complete. Its `is_cart_prod_def2` expansion cannot use the HOL
`etcs_subst` call directly because the FOL lemma has explicit projection-typing premises. The two
lifted projections are now typed first, and the proof applies `iffD2` to the instantiated
equivalence; `eval_at` confirms that this enters the intended universal-property goal. Both
projection equations for the proposed mediator
`\<langle>f\<^sup>\<flat>,g\<^sup>\<flat>\<rangle>\<^sup>\<sharp>` are also verified using parallel,
explicit calculation chains through `transpose_of_comp`, the appropriate product projection, and
`sharp_cancels_flat`. Mediator uniqueness is proved directly with `cfunc_prod_unique`.

`exponential_coprod_distribution`, `empty_exp_nonempty`, and `exp_pres_iso_left` are also complete.
The coproduct-distribution proof required tuple-form applications throughout the translated tail
(`eval_func(Z,A)`, `left_coproj(X,Y)`, `dist_prod_coprod_right(X,Y,H)`, and similar constants).
Its associativity subproofs now state full left-hand sides rather than beginning a nested
calculation with `...`, because an ellipsis there inherits the preceding outer fact in Isabelle.
Each application of `comp_associative2` is supplied with three named arrow-type facts. The
left/right coproduct uniqueness cases were checked independently with `eval_at`.

For preservation of an isomorphism in the exponential base, the HOL proof's broad search for the
second inverse equation is replaced by an explicit inverse witness from
`isomorphism_def3`. A short typed calculation proves that the selected left inverse is that
witness, after which the induced exponential arrow is shown isomorphic directly with
`isomorphism_def3` and `is_isomorphic_def`.

Work is now in `expset_power_tower`. The former failing expansion of `\<psi>` is verified: the
four-arrow term must be reassociated in two explicit `comp_associative2` steps, since the displayed
source layout hides the parser's right association. Headless `eval_at` succeeds through that
calculation (the current source checkpoint ending at the local proof formerly reported as line
2351). The remainder of `expset_power_tower` is not yet claimed to compile.

The Isabelle method syntax was also normalized throughout the remaining source. Facts must be
supplied before a method with `using`; `blast`, `force`, and `fastforce` are terminal method names,
not prefixes accepting trailing theorem arguments. Thus forms such as
`by (typecheck_cfuncs, blast theorem_name)` have been eliminated from the entire theory in favor
of `using theorem_name by (typecheck_cfuncs, blast)`. This prevents the repeated parse failures
encountered in the untranslated tail.

**Status: `FOL/Exponential_Objects.thy` is complete and independently verified** (2026-07-29): a
from-scratch `isabelle build -c` of a fresh session containing every already-committed `FOL/*.thy`
file (`Cfunc` through `Axiom_Of_Choice`) plus `Initial` and this theory finishes with zero errors,
in ~30s total. Full lemma coverage matches the HOL original: Axiom 9, `exp_func`, `transpose_of_comp`,
the flat/sharp cancellation family, `metafunc`/`cnufatem` and their Skolemized inverses, the full
`meta_comp`/`meta_comp2` family (identity, associativity, comp-as-metacomp), `left_param`/`right_param`,
`exp_one`, `exp_empty`, `one_exp`, `power_rule`, `exponential_coprod_distribution`, `empty_exp_nonempty`,
`exp_pres_iso_left`/`_right`/`exp_pres_iso`, `expset_power_tower`, the empty/nonempty exponential family
(`empty_to_nonempty`, `exp_is_empty`, `nonempty_to_nonempty`, `empty_to_nonempty_converse`), `powerset`,
and `sets_squared`.

Finishing this theory (continuing from a large in-progress draft) surfaced four recurring bug classes,
none seen in quite this combination before, now folded into
[[fol-proof-patterns-no-sledgehammer]] as items 25-28:
- **Curried calls to constants with custom mixfix notation must use the notation's own template, not
  bare juxtaposition.** `eval_func A \<Omega>` (space-separated, mimicking the HOL original's curried
  syntax) is a hard parse error; only `eval_func(A, \<Omega>)` parses, because plain multi-argument
  constants in this port rely on the generic `_applC`-style call syntax rather than true HOL-style
  currying. This was the single most common defect in the draft handed off mid-theory and matches
  the user's own diagnosis from direct jEdit inspection.
- **`rule cfunc_prod_comp[OF ...]`/`rule comp_associative2[OF ...]` require the goal to already be
  stated with the EXACT grouping the rule's conclusion produces** (e.g. `\<langle>(a \<circ>\<^sub>c f), (b
  \<circ>\<^sub>c f)\<rangle>`, not the flatter `\<langle>a \<circ>\<^sub>c f, b \<circ>\<^sub>c f\<rangle>` a reader would
  write by hand) — `rule` does exact syntactic matching, so a goal phrased in the "natural" flat
  form fails even though the two terms are equal by associativity. The robust fix used throughout:
  state the bridging fact with `using cfunc_prod_comp[OF ...] comp_associative2[OF ...] ... by simp`
  instead of `rule`, letting `simp`'s rewriting (which is direction- and grouping-agnostic) close the
  gap; when several sequential re-associations/distributions are needed (e.g. un-bundling a pair
  composed with `f` all the way down to its two separately-composed components), each one may need
  its own explicit `comp_associative2`/`cfunc_prod_comp` instance supplied to `simp`, since `simp`
  will not discover an un-given instantiation on its own.
- **`also`/`...` tracks the single most-recently-established fact (`this`), not "the most recent step
  of an `also`-chain."** Inserting an ordinary `have` (even one needed only as a side lemma) between
  two `also have "..."` steps breaks the chain with a confusing "Vacuous calculation result" error,
  because the `...` in the next `also have` resolves against the intervening plain `have` instead of
  the chain's actual last link. Reconfirms and sharpens the general guidance already in
  [[fol-proof-patterns-no-sledgehammer]] to prefer flat named `have s1`/`s2`/... steps combined by a
  final `using s1 s2 ... by simp` over `also`/`finally` chains whenever any other reasoning must be
  interleaved.
- **A nested fact expression inside an `[OF ...]` list must always be its own named `have` first**
  (`comp_associative2[OF a_type b_type (cfunc_cross_prod_type[OF c_type d_type])]` is a hard
  "Bad arguments for attribute OF" parse error) — this bit twice in `exp_pres_iso_right`, both times
  because a plain `\<psi> : A \<rightarrow> X`/`\<phi> : X \<rightarrow> A` fact was not itself tagged
  `[type_rule]`, which is also worth tagging on any such fact used later by `typecheck_cfuncs` in the
  same lemma.

`FOL/Initial.thy` was completed in an earlier segment of this same port (see its own status note
above) and is committed alongside `Exponential_Objects.thy` in this step.

**Status: `FOL/Cardinality.thy` is complete and independently verified** (2026-07-29): a
from-scratch `isabelle build -c` of a fresh session containing every already-committed `FOL/*.thy`
file (`Cfunc` through `Exponential_Objects`) plus this theory finishes with zero errors in ~24s.
Full lemma coverage matches the 1147-line HOL original (`Category_Set/Cardinality.thy`), ported to
a 1927-line FOL file: `is_finite`/`is_infinite`/`either_finite_or_infinite`, `is_smaller_than`
(`\<le>\<^sub>c`) and `subobject_iff_smaller_than`/`set_card_transitive`, `all_emptysets_are_finite`,
`emptyset_is_smallest_set`, `truth_set_is_finite`, `smaller_than_finite_is_finite`,
`larger_than_infinite_is_infinite`, `iso_pres_finite`/`iso_pres_infinite`, `not_finite_and_infinite`,
`size_2_sets`/`size_2plus_sets`, `not_init_not_term`, `sets_size_3_plus`,
`smaller_than_coproduct1`/`2`, `smaller_than_product1`/`2`, `Y_nonempty_then_X_le_XtoY`,
`non_init_non_ter_sets`, `exp_preserves_card1`/`2`/`3`, and the two hardest lemmas,
**`coprod_leq_product`** and **`prod_leq_exp`**.

`coprod_leq_product` deliberately uses a SIMPLER witness construction than HOL's own
`try_cast`/`set_subtraction`-based one: given `X`, `Y` both non-initial/non-terminal (so each has
two distinct elements `x1\<noteq>x2`, `y1\<noteq>y2`), define `q : Y \<rightarrow> X \<times>\<^sub>c Y` by
`q = \<langle>x2\<circ>\<^sub>c\<beta>_Y, id(Y)\<rangle>` (constant-`x2` on the first coordinate) and
`p : X \<rightarrow> X \<times>\<^sub>c Y` via a single `eq_pred(X)`/`case_bool`/`dist_prod_coprod_left(X,\<one>,\<one>)`
case split giving `p(x2)=\<langle>x1,y2\<rangle>` and `p(x)=\<langle>x,y1\<rangle>` for `x\<noteq>x2`; then `m = p \<amalg> q`
is shown monic by a full case split on `coprojs_jointly_surj` (left/left, left/right, right/left,
right/right) using the explicit value facts and `cart_prod_eq2` to derive contradictions from the
distinctness of `x1,x2` and `y1,y2`.

`prod_leq_exp` follows HOL's own case structure (`initial_object Y`, `X \<cong> \<Omega>`,
`initial_object X`, `terminal_object X`, and the general case) and in the hardest branch builds the
same `\<Theta>` witness as HOL via `dist_prod_coprod_left`/`eq_pred`/`case_bool`/`swap`/
`associate_right`, then proves `injective(\<Theta>)` by an explicit 9-leaf case split (on whether
`y`/`t` equal `y1`/`y2` and whether `x` equals `s`) instead of HOL's `metis`-driven case analysis,
using a `third_point` helper lemma (pigeonhole-style: given any two elements of a \<ge>3-element set,
find a third element distinct from both, proved via `sets_size_3_plus` plus nested `disjE`
case-splits, no `cases`/`case True`/`case False`) to supply a witness `z` distinct from both
compared points whenever needed.

Finishing this theory surfaced several new proof-pattern gotchas, now folded into
[[fol-proof-patterns-no-sledgehammer]] as items 28-32:
- **`proof (clarify)` cannot open a goal whose statement is already meta-level** (i.e. a `have
  "\<And>x y z. ... \<Longrightarrow> ... \<Longrightarrow> concl"` string) — it fails with "Failed to apply
  initial proof method" because `clarify` expects an OBJECT-level `\<forall>`/`\<longrightarrow>`/`\<and>`
  to simplify into meta form; when the goal is already stated with meta `\<And>`/`\<Longrightarrow>`,
  use plain `proof -` followed directly by `fix`/`assume`/`show`. `proof (clarify)` remains correct
  and necessary when the goal starts as an object-level formula (e.g. right after `unfolding
  injective_def2[OF f_type]`, whose RHS is `\<forall>x y. ... \<longrightarrow> ...`).
- **`conjI[OF conjI[OF A B] C]` and `conjI[OF A conjI[OF B C]]` are NOT interchangeable** even though
  `A \<and> B \<and> C` "looks the same" either way — a lemma's LHS conjunction associates according to
  how it was literally written (`\<and>` is right-associative, so `P \<and> Q \<and> R` means `P \<and> (Q
  \<and> R)`), and `OF`'s unifier will reject the wrong nesting with "no unifiers" rather than silently
  fixing it. Always match the target lemma's own parenthesization exactly when building a conjunction
  via nested `conjI`.
- **`comp_associative2` (`h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f`) as a `simp` rule only
  ever rewrites TOWARD full left-association** — feeding it to `simp` can prove two *different*
  left-grouped parenthesizations of the same composition-chain-applied-to-an-argument are equal (both
  normalize to the same canonical left-associated form), but it can NEVER produce or match a
  right-associated target (e.g. the natural `A \<circ>\<^sub>c B \<circ>\<^sub>c C \<circ>\<^sub>c x` chain, which
  parses right-associatively since `\<circ>\<^sub>c` is `infixr`), because the rule only fires in one
  direction. When a lemma's *stated* conclusion is a right-associated chain, close it by peeling one
  layer at a time with named `have step_k : ... = ...` facts each proved via `sym[OF
  comp_associative2[OF ...]]` (the symmetric/right-associating direction), rather than reaching for a
  blanket `simp add: comp_associative2`.
- **A `have`/`show` goal combining several large opaque terms (e.g. involving `\<Theta>\<^sup>\<flat>`
  applied to a giant composite) via a plain `using fact1 fact2 fact3 by simp` can be genuinely SLOW
  (tens of seconds, occasionally hitting the ML stack limit and getting killed as
  `Interrupt_Breakdown`) even when the combination is logically trivial** — `simp`'s default behavior
  of pulling in the entire local proof context as additional (conditional) rewrite rules can make it
  thrash searching for a rewrite path through a large in-scope fact set (e.g. several big generalized
  lemmas like `f1`/`f2`/`f3` from an enclosing `have`, each a `\<forall>`-schematic conditional
  equation matching the same term shape). The robust, fast fix: use `fact[unfolded eq_thm]` to
  perform a single, targeted rewrite of ONE specific fact by ONE specific equation (this does not
  consult the ambient context at all), then close the final numeric/scalar equality with a direct
  `rule trans[OF fact_a[symmetric] fact_b]` instead of `by simp` — this reduces a search that was
  timing out to sub-second, purely syntactic term matching.
- **The "pigeonhole: given two points, find a third element of a \<ge>3-element set distinct from
  both" pattern** (needed repeatedly for injectivity arguments over sets that are merely known to be
  "big enough", e.g. via `sets_size_3_plus`) has no library lemma and must be hand-built each time via
  nested `disjE`-based case splits (never `cases`/`case True`/`case False`, per longstanding
  practice) on whether the first/second of three obtained distinct witnesses coincides with either of
  the two given points; worth extracting as a reusable local helper lemma (named `third_point` in
  this file) rather than inlining the six-way case split at each call site.

**Status: FOL/Nats.thy is complete** (1593 lines), verified via a full from-scratch headless build
(`Finished ETCS_FOL_Nats`) plus an independent verification build in a fresh scratch directory against
fresh copies of every already-committed `FOL/*.thy` file (`Finished ETCS_FOL_Nats_Verify`).

Full lemma coverage matches HOL's `Nats.thy`: the `\<nat>\<^sub>c`/`zero`/`successor` axiomatization and
`natural_number_object_property`/`_property2`, `natural_number_object_func_unique`; `is_NNO`,
`N_is_a_NNO`, `NNOs_are_iso_N`, `Iso_to_N_is_NNO`; `zero_is_not_successor`,
`oneUN_iso_N_isomorphism` (Proposition 2.6.6), `nonzero_is_succ`; `predecessor'`/`predecessor` and
their defining lemmas; `Peano's_Axioms`, `succ_inject`; `nat_induction`; the `ITER_curried`/`ITER`
axiomatization and `ITER_zero`/`ITER_zero'`/`ITER_succ`/`ITER_one`; `iter_comp` (notation
`_\<^bsup>\<circ>_\<^esup>`) and `iter_comp_type`/`iter_comp_def3`, `zero_iters`, `succ_iters`, `one_iter`,
`eval_lemma_for_ITER`, `n_accessible_by_succ_iter_aux`, `n_accessible_by_succ_iter`; and finally
`oneUN_iso_N`/`NUone_iso_N`.

Design decisions vs. HOL:
- **Dropped `zUs_epic`, `zUs_surj`, `nonzero_is_succ_aux`** (confirmed via grep they are referenced
  nowhere else in the HOL repo). `nonzero_is_succ` is instead proved directly off the already-derived
  isomorphism `zero \<amalg> successor` and its generic inverse `(zero \<amalg> successor)\<^bold>\<inverse>`
  (reusing the `f\<^bold>\<inverse>` operator from `Cfunc.thy` rather than a fresh `THE`-based
  Skolemization) plus `coprojs_jointly_surj`, bypassing HOL's `surjective_def`-based route entirely.
- **`predecessor'` is defined directly as `(zero \<amalg> successor)\<^bold>\<inverse>`** for the same reason —
  once `oneUN_iso_N_isomorphism` establishes `isomorphism(zero \<amalg> successor)`, the generic
  inverse operator already has everything needed (`inverse_def2`), so no separate Skolem constant is
  introduced for the predecessor map on `\<one> \<Coprod> \<nat>\<^sub>c`.
- **`ITER_curried :: cset \<Rightarrow> cfunc` is axiomatized directly via its defining spec** (existence +
  uniqueness guaranteed pointwise by `natural_number_object_property2`), the same conservative-extension
  justification used throughout the port for `inverse`, `cnufatem`, etc. `ITER` is then a plain
  `definition` unfolding to `(ITER_curried(U))\<^sup>\<flat>`.
- Added one small reusable helper not present in HOL, **`eval_func_cnufatem`**
  (`eval_func(Y,X) \<circ>\<^sub>c \<langle>x,g\<rangle> = cnufatem(g) \<circ>\<^sub>c x` for `g \<in>\<^sub>c Y\<^bsup>X\<^esup>`,
  `x \<in>\<^sub>c X`), factored out of `eval_lemma_for_ITER`'s inline derivation and reused again in
  `n_accessible_by_succ_iter_aux`/`n_accessible_by_succ_iter` to avoid duplicating the same
  `cnufatem_def2` + associativity/`cfunc_prod_comp` unwinding twice.

New proof-pattern bugs found and fixed this file (folded into
[[fol-proof-patterns-no-sledgehammer]] as items 33-35):
- **A `have`/`axiomatization`-adjacent type judgement for a long composition chain can be flatly
  FALSE if the domain/codomain of an intermediate factor is miscomputed** — e.g. for
  `meta_comp(U,U,U) \<circ>\<^sub>c (id \<times>\<^sub>f eval) \<circ>\<^sub>c associate_right(...) \<circ>\<^sub>c (diagonal(...) \<times>\<^sub>f id(...))`,
  the correct domain is `(U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>` (the domain of the
  *rightmost* factor, `diagonal(...) \<times>\<^sub>f id(...)`), NOT
  `(U\<^bsup>U\<^esup>) \<times>\<^sub>c ((U\<^bsup>U\<^esup>) \<times>\<^sub>c (U\<^bsup>U\<^esup>)\<^bsup>U\<^bsup>U\<^esup>\<^esup>)` (an intermediate stage's
  *codomain*, after `associate_right` reassociates) — `typecheck_cfuncs` failing with a large dumped
  goal listing many partially-matched premises is a strong signal to re-derive the domain/codomain of
  the WHOLE chain by hand from its rightmost/leftmost factors before assuming the tactic is simply
  "not smart enough."
- **When `typecheck_cfuncs` alone cannot close a deep (3+ factor) composition-chain type goal, build
  it bottom-up as individual named `have ..._type[type_rule]` facts, one `comp_type[OF inner outer]`
  application per factor** (innermost/rightmost first), rather than one blanket
  `by typecheck_cfuncs` call on the whole chain — this both diagnoses exactly which stage's type is
  wrong (per the item above) and reliably succeeds once every stage's type is individually correct.
- **`using fact_a by simp` where `fact_a`'s statement and the goal differ only by
  left-vs-right-association of the same three-term composition chain is NOT closed by `simp` alone**
  (this is the same underlying `comp_associative2`-direction issue as items 28-32, but caught here in
  a *fresh* spot: restating a previously-derived equation `id(\<nat>\<^sub>c) \<circ>\<^sub>c n = A \<circ>\<^sub>c B \<circ>\<^sub>c n`
  post-substitution). Diagnosed from the exact `Failed to apply initial proof method ... using this:
  ... goal (1 subgoal): ...` shape (the "using this" fact and the goal are visibly the same terms in
  different parenthesizations) — fix by inserting an explicit intermediate `have` in the
  matching (left-associated) parenthesization first, then bridging to the target parenthesization via
  a named `comp_associative2`/`sym[OF comp_associative2]` step, exactly as for a fresh derivation.

Next theory per the port order: **Pred_Logic**.
