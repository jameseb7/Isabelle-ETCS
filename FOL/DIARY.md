# FOL Port Diary

A running log of porting the ETCS `Category_Set/*.thy` (HOL) theories to plain Isabelle `FOL` under
`FOL/`. So far: `Category_Set/Cfunc.thy` → `FOL/Cfunc.thy`, and `Category_Set/Product.thy` →
`FOL/Product.thy` (the next theory in HOL `imports` dependency order after `Cfunc.thy`).
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
`Truth.thy`) finishes with zero errors. Copied into `/home/dusty/Isabelle-ETCS/FOL/Equivalence.thy`;
not yet committed pending user confirmation.

Next theory per the port order above: **Coproduct**.
