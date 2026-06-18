# Object contracts

One card per **constructed object** (not per theorem). A contract lets a reviewer judge
whether the object is the right one — and where it is *proven* vs *asserted* — **without
reading any Lean proof**. Format + rationale:
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance).

Each card carries the informal description + source, the Lean *signature only*, a
`characterization` (id'd claims including ≥1 **anti-degeneracy** clause), and a
`known_values` **test matrix** (`instance → expected → theorem → status`) whose status is
read from `#print axioms` (so it can't be fudged).

> **Objects vs axioms.** These cards are for *constructed objects* you can evaluate at
> instances. The project's four **axioms** are not evaluable, so they carry the right
> artifact instead — per-axiom **vetting records** in [`../vetting/`](../vetting/) plus the
> closure-status [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md).

## Cards

- [`homDensity.md`](homDensity.md) — homomorphism density `t(F, W)`. Rows: Erdős–Rényi
  `p^{e(F)}`, edge/triangle integrals, multiplicativity, step-graphon agreement, `[0,1]` range.
  Anti-degeneracy: agreement with the finite homomorphism density on step graphons.
- [`Graphon.md`](Graphon.md) — `Graphon` / `SymmKernel`. Symmetry, `[0,1]` vs the module on
  differences, `const`/`step` instances, ext. Anti-degeneracy: the cut-metric module lives on
  `SymmKernel` because differences leave `[0,1]`.
- [`cutNorm.md`](cutNorm.md) — the cut norm. Seminorm laws, the sup-over-rectangles **set form**,
  `cutNorm(graphon) = ∫∫W`, the factor-4 signed sandwich. Anti-degeneracy: it is the sup, not `|∫∫W|`.
- [`cutDist.md`](cutDist.md) — the cut distance δ□. Pseudometric laws (triangle = Gluing Lemma) +
  relabelling-invariance. Anti-degeneracy: the coupling **infimum** (witnessed by `cutDist_pullback_self`),
  not `cutNorm(U−W)`.
- [`GraphonSpace.md`](GraphonSpace.md) — graphons mod weak isomorphism. Quotient/metric/continuity
  (axiom-clean) + the separation/moment-injectivity row (`proven_mod_axioms`). Demonstrates **mixed
  status** in one card. Anti-degeneracy: the quotient is exactly the moment-determined relation.
