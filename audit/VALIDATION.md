# VALIDATION — why this formalization is faithful

This document is addressed to a mathematician who knows graphons as in Lovász, *Large
Networks and Graph Limits* (2012; "LNGL"). It makes the case that the Lean library in this
repository is a **correct formalization of dense graph limit theory** — not a type-checked
look-alike. The companion [`VERIFICATION.md`](VERIFICATION.md) is the dictionary (definitions
and theorem statements, side by side with the informal theory, plus the audit recipe); this
document is the argument.

## §0 The skeptic's position, stated fairly

Type-checking guarantees that *proofs* are correct relative to *statements*. It guarantees
nothing about the statements: a subtly wrong definition — a wrong product measure, an
edge-orientation slip, a misplaced quantifier — will happily prove subtly wrong theorems,
flawlessly. So the only legitimate validation question is:

> **Are these definitions the objects of LNGL, and do the proved statements say what the
> book's theorems say?**

No single check can settle this; convergent independent evidence can. The library provides
six lines of evidence, each attacking the question from a direction the others cannot. They
are presented in increasing order of strength. (Labels "Tier A–F" are the repository's
internal index for the test suites and recur in `HISTORY.md`; theorem names below are
searchable in `Graphons/`.)

---

## §1 The definitions compute the right numbers (Tier A)

If `homDensity` were wrong, it would compute wrong values. It computes, as proved theorems:

- `t(F, W) ∈ [0,1]` (`homDensity_mem_Icc`); `t(F, W_p) = p^{e(F)}` for the constant graphon —
  the Erdős–Rényi sanity check (`homDensity_const`); `t(K₂,W) = ∫∫W`; the explicit triple
  integral for `t(K₃,W)` (`homDensity_edge`, `homDensity_triangle`).
- **Concrete rationals, cross-checked outside Lean.** `Graphons/Tests/Concrete.lean` proves,
  inside Lean, instances such as `t(K₂, W_{K₄}) = 3/4`, `t(K₃, W_{C₅}) = 0` (the 5-cycle is
  triangle-free), `t(P₃, W_{1/2}) = 1/4`, `t(C₄, W_{1/2}) = 1/16`; the same numbers are
  recomputed by an independent brute-force Python script
  (`scripts/hom_density_reference.py`), which knows nothing of the Lean encoding. Agreement
  rules out the classic encoding bugs (vertex ordering, unordered-edge handling,
  normalization).

Similarly the cut norm: the seminorm laws, `cutNorm W = t(K₂,W)` for graphons, and
`cutNorm ≤ ∫∫|W|` pin its normalization and scale.

## §2 The objects satisfy the structural laws that interlock them (Tier B)

Correct definitions must cohere. Proved, all axiom-free:

- the **Counting Lemma** `|t(F,U) − t(F,W)| ≤ e(F)·‖U−W‖□` and its cross-carrier `δ□`
  version (`abs_homDensity_sub_le`, `abs_homDensity_sub_le_cutDist`) — the inequality that
  couples the density functional to the metric, with the book's constant `e(F)`;
- `δ□` is a pseudometric whose triangle inequality across three different carriers is the
  **Gluing Lemma**, proved by disintegration as in the classical argument (`cutDist_triangle`);
- multiplicativity over disjoint unions (`homDensity_sum`); finite-graph compatibility
  `t(F, W_G) = hom(F,G)/n^{|V(F)|}` (`homDensity_step`).

**Robustness: the encoding choices wash out.** Where this library's definitions pick one of
several textbook formulations, the alternatives are proved equivalent, so no result depends on
the choice: test-function cut norm = set form, *exactly* (`cutNorm_eq_cutNormSet`); signed
test functions within the classical factor 4 (`cutNorm ≤ cutNormSigned ≤ 4·cutNorm`);
coupling-based `δ□` vs measure-preserving maps (maps bound couplings,
`cutDist_le_cutNorm_pullback_sub`; pullback along a measure-preserving map is `δ□`-invisible,
`cutDist_pullback_self`; transport along one map preserves `δ□` exactly,
`cutDist_pullback_pullback`). The one classical equivalence *not* proved — that maps attain
the coupling infimum on atomless standard Borel spaces (LNGL Lemma 8.13) — is blocked by a
known gap in Mathlib (the measure-isomorphism theorem) and is documented, not hidden.

## §3 The named theorems of the theory hold (Tier C)

The theorems that *define* the subject, for these definitions:

1. **Weak (Frieze–Kannan) Regularity** with the standard complexity bound `4^{⌈1/ε²⌉}`
   (`weak_regularity`, `weak_regularity_card`) — axiom-free.
2. **Step graphons are `δ□`-dense** (`exists_stepGraphon_cutDist_le`) and `(GraphonSpace, δ□)` is
   **totally bounded** (`graphonSpace_totallyBounded`) — axiom-free.
3. **Completeness and compactness** of graphon space over `([0,1], Leb)` — the
   Lovász–Szegedy compactness theorem (`instCompactSpaceGraphonSpaceUnit`) — proved **modulo
   axioms #1–2** (see §7).
4. **The counting lemma, both directions**: `δ□(U,W) = 0 ⇔ ∀F, t(F,U) = t(F,W)`
   (`cutDist_eq_zero_iff_homDensity_eq`); the moment map is injective on graphon space.
   Forward direction axiom-free; converse = **axiom #3** (inverse counting, LNGL Thm 11.3).
5. **Lovász–Szegedy representability**: graph parameters of the form `t(·,W)` are exactly the
   multiplicative, normalized, reflection-positive, `[0,1]`-bounded ones
   (`representability`); "only if" proved, "if" = **axiom #4**.

Together: limits exist (compactness), finite graphs are dense (completion picture), the
densities separate points, and the image of the moment map is characterized — the standard
description of the theory, here as machine-checked statements about *these* definitions.

## §4 The theory proves classical theorems it was never designed for (Tier D)

Items §1–§3 share a weakness: the acceptance tests were written by the same process that wrote
the definitions. The strongest antidote is **downstream consequences** — named results of
extremal graph theory, proved purely through the public `t(F,·)` interface, that were not
design targets. All axiom-free:

- **Goodman's bound** (1959): `t(K₃,W) ≥ 2t(K₂,W)² − t(K₂,W)` (`goodman`);
- **Sidorenko's inequality for `C₄`**: `t(C₄,W) ≥ t(K₂,W)⁴` (`sidorenko_C4`) — numerically
  *tight* at `W_{K₄}` (`81/256 ≤ 84/256`, both sides pinned in the test suite);
- **Mantel's theorem for graphons**: `t(K₃,W) = 0 ⇒ t(K₂,W) ≤ 1/2` (`mantel`).

A wrong product measure or edge-handling slip would not produce these inequalities with these
constants. The proofs are the standard analytic ones (Cauchy–Schwarz on degree and co-degree
functions; for Mantel, a.e. disjointness of neighborhoods), visible in
`Graphons/Extremal/`.

## §5 The definitions are *forced*: an axiomatic characterization with one model (Tier E)

This is the strongest claim, and it addresses the look-alike objection at its root.

A four-line specification of "a dense graph limit theory" is stated independently of every
implementation choice in this library — auditable against LNGL Ch. 8 and 11 in minutes,
without reading any of the `Graphon`/`cutNorm` code:

> a complete metric space `X`; a distance-preserving map `ι` into `X` from the finite
> weighted graphs carrying the cut premetric, with dense image; and for each finite simple
> graph `F` a continuous `t_F : X → ℝ` restricting to the finite homomorphism density on
> the image of `ι`.

(See `IsDenseGraphLimitTheory` in `Graphons/Characterization/LimitSpec.lean`; the
specification text passed an independent review — [`LIMIT_SPEC_REVIEW.md`](LIMIT_SPEC_REVIEW.md).)
Two theorems then close the loop:

- **Existence** (`isDenseGraphLimitTheory_graphonSpace`): this library's graphon space over
  `[0,1]` *is* a model — via an interval step transport proved to preserve both `δ□` and all
  densities, and the `δ□`-density of finite weighted graphs (weak regularity + a
  mass-rounding argument). Uses axioms #1–2 only through completeness.
- **Uniqueness** (`isDenseGraphLimitTheory_unique`, **axiom-free**): any two models are
  canonically isometric, compatibly with `ι` and with *every* density functional — the
  universal property of metric completions. Corollary: every model is canonically isometric
  to this library's `GraphonSpace`.

Consequence: to trust the entire construction, a reader need only (i) agree that the
four-line specification says "dense graph limit theory" — a judgment about ten lines of
mathematics, not thousands — and (ii) accept the machine-checked existence and uniqueness.
The definitions are then not merely *consistent with* the theory; up to canonical isometry
they are the *only* thing satisfying it.

## §6 The theory is connected to its probabilistic origin (Tier F)

Graphons exist to be limits of random and large dense graphs. The W-random graph `G(n,W)` is
formalized with no shortcuts — i.i.d. vertex positions, then a genuine product-Bernoulli
measure for the edge coins, so that **independence is a proved theorem about the measure**
(`integral_coin_prod`), not a definition. Then, axiom-free:

- the **exact identity**: injective placements of `V(F)` contribute exactly `t(F,W)` to the
  expected density — for every `n` and every carrier;
- the **first sampling lemma** (expectation form):
  `|E[t(F, G(n,W))] − t(F,W)| ≤ k(k−1)/n`, hence `E[t(F, G(n,W))] → t(F,W)`
  (`abs_expectedHomDensity_sub_le`, `tendsto_expectedHomDensity`), the deficit being exactly
  the non-injective placement mass.

This exercises `homDensity` against an independently constructed probabilistic object — an
axis none of §1–§5 touches.

## §7 Adversarial hardening (the suite polices itself)

- **The axiom ledger cannot silently grow.** Exactly four classical theorems are assumed
  (stated in full in [`VERIFICATION.md`](VERIFICATION.md) §4, each independently vetted; one
  earlier candidate was caught **false as stated** during vetting and rejected —
  `HISTORY.md` items 36–37). `Graphons/Tests/AxiomGuard.lean` pins the verbatim
  `#print axioms` output of every flagship theorem: any new assumption anywhere in the
  dependency graph fails the build.
- **The acceptance suite has discriminating power.** Mutation testing
  (`scripts/mutation_test.sh`, results in [`MUTATION_MATRIX.md`](MUTATION_MATRIX.md)):
  five deliberate single-definition bugs — product→sum in the density integrand, complemented
  step graphon, cut norm without the absolute value, complemented constant graphon, kernel
  subtraction→addition — were each rejected by the suite ("killed"), and the clean tree
  rebuilds green. A surviving mutant would have indicated a missing acceptance theorem.

## §8 What is **not** claimed (honest limitations)

1. **Four classical theorems are assumed, not proved** (axioms #1–4; full statements,
   dependency map, and discharge plans in `VERIFICATION.md` §4 and `HISTORY.md`). Everything
   outside completeness/compactness, the inverse counting direction, and the representability
   "if" direction is axiom-free — including the uniqueness theorem of §5 and all of §§1, 2,
   4, 6.
2. **Compactness and completeness are proved over `([0,1], Leb)` only**, not over an
   arbitrary atomless standard Borel carrier (blocked by the same Mathlib gap as the
   maps-vs-couplings equivalence: no measure-isomorphism theorem). All other results are
   carrier-general.
3. **The characterization's finite objects are weighted graphs.** Replacing them by simple
   graphs requires the weighted→simple `δ□`-approximation (classically via sampling), open
   here.
4. **Sampling is in expectation.** The almost-sure first sampling lemma and the second
   sampling lemma (`δ□(G(n,W), W) → 0`, LNGL Lemma 10.16) are not yet formalized.
5. **Turán is formalized for `K₃` (Mantel) only**; general `r` is open here.
6. A.e.-equal graphons are distinct *objects* (functions) identified only in `GraphonSpace`
   (`δ□ = 0`); all metric-level and density-level results respect this identification.
   This is a presentation choice, not a mathematical difference — see `VERIFICATION.md` §2.1.

## §9 Summary for the impatient referee

Read `VERIFICATION.md` §2 (the seven definitions, ~2 pages) and decide they are LNGL's
objects; skim the statements of `weak_regularity`, `cutDist_eq_zero_iff_homDensity_eq`,
`instCompactSpaceGraphonSpaceUnit`, `goodman`, `mantel`, `abs_expectedHomDensity_sub_le`,
`isDenseGraphLimitTheory_unique`; read the four axiom statements in `VERIFICATION.md` §4; run
`lake build` (or trust CI) and `python3 scripts/hom_density_reference.py`. That is the entire
trust base. Everything else — proof scripts, development history, AI provenance
(`METHODOLOGY.md`, `HISTORY.md`) — is outside it.
