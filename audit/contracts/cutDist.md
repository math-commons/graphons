---
object: Graphons.cutDist
informal: >
  The cut distance δ□(U, W): the infimum, over couplings of the two carrier measures (via the
  overlay kernel), of the cut norm of the difference. It is the metric of dense graph limit
  theory — invariant under measure-preserving relabelling, so it sees graphons up to weak
  isomorphism.
sources:
  - "Lovász, Large Networks and Graph Limits (AMS, 2012), §8.2 (cut distance); §8.2/Ch.8 (gluing/triangle)"
lean:
  name: Graphons.cutDist
  signature: "(U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : ℝ"
  body: "inf over couplings of cutNorm of the overlaid difference."
characterization:
  - id: C1-pseudometric
    claim: "δ□ is a pseudometric: `0 ≤ δ□`, `δ□ U W = δ□ W U`, `δ□ U U = 0`, and the triangle inequality `δ□ U W ≤ δ□ U V + δ□ V W` (the Gluing Lemma, on a StandardBorelSpace)."
  - id: C2-coupling-inf
    anti_degeneracy: true
    claim: >
      δ□ is the INFIMUM over couplings, not cutNorm(U − W) on a fixed identification. That is what
      makes it relabelling-invariant: `δ□(W, pullback of W along a measure-preserving map) = 0`.
      A "cut distance" without the coupling inf would change under relabelling and fail this.
known_values:
  - instance: "δ□ U W"
    expected: "≥ 0"
    theorem: Graphons.cutDist_nonneg
    status: PROVEN_CORE_AXIOMS
  - instance: "δ□ U W vs δ□ W U"
    expected: "equal (symmetry)"
    theorem: Graphons.cutDist_comm
    status: PROVEN_CORE_AXIOMS
  - instance: "δ□ U U"
    expected: "0"
    theorem: Graphons.cutDist_self_eq_zero
    status: PROVEN_CORE_AXIOMS
  - instance: "δ□ U W (triangle)"
    expected: "≤ δ□ U V + δ□ V W"
    theorem: Graphons.cutDist_triangle
    status: PROVEN_CORE_AXIOMS
    note: "via the Gluing Lemma; #print axioms pinned in Graphons/Tests/AxiomGuard.lean"
  - instance: "δ□(W, pullback W along m.p. map)"
    expected: "0 (relabelling-invariant)"
    theorem: Graphons.cutDist_pullback_self
    status: PROVEN_CORE_AXIOMS
    note: "the anti-hack C2 witness"
well_definedness: >
  The coupling family is nonempty (the product coupling) and `cutNorm` of the overlay is
  nonneg and bounded, so the infimum exists; the triangle inequality needs a StandardBorelSpace
  carrier (for the gluing/coupling composition).
anti_degeneracy:
  history: >
    Defining δ□ as `cutNorm (U − W)` on a fixed coordinate identification is the classic wrong
    move: it is not relabelling-invariant, so weakly isomorphic graphons get nonzero distance and
    the quotient GraphonSpace is wrong.
  current_guard: >
    `cutDist_pullback_self` pins relabelling-invariance (δ□ = 0 under a measure-preserving
    pullback); the pseudometric laws (`cutDist_self_eq_zero`, `cutDist_triangle`) pin the rest.
status: >
  All rows PROVEN_CORE_AXIOMS (standard three); `cutDist_triangle` is kernel-pinned in
  Graphons/Tests/AxiomGuard.lean.
---

# Contract — `Graphons.cutDist`

The cut distance δ□. Anti-degeneracy clause **C2** (the coupling infimum, witnessed by
`cutDist_pullback_self`) is what distinguishes the real δ□ from the naive `cutNorm(U−W)`:
only the inf is relabelling-invariant, which is exactly what makes `GraphonSpace` a metric
space of graphons-up-to-weak-isomorphism. The `known_values` rows are the proved pseudometric
laws plus the pullback-invariance witness.
