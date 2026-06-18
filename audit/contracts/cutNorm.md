---
object: Graphons.cutNorm
informal: >
  The cut norm of a kernel W: the supremum, over measurable sets S, T ⊆ Ω, of
  |∫_{S×T} W d(μ×μ)|. It measures W's "macroscopic" mass, ignoring high-frequency sign
  cancellation, and is the seminorm underlying the cut distance.
sources:
  - "Lovász, Large Networks and Graph Limits (AMS, 2012), §8.2 (cut norm / cut distance)"
lean:
  name: Graphons.cutNorm
  signature: "(W : SymmKernel Ω μ) : ℝ"
  body: "the test-function sup form; equal to the set-form sup_{S,T meas} |∫_{S×T} W| (cutNorm_eq_cutNormSet)."
characterization:
  - id: C1-seminorm
    claim: "cutNorm is a seminorm: nonneg, `cutNorm (c•W) = |c|·cutNorm W`, `cutNorm (U+W) ≤ cutNorm U + cutNorm W`, `cutNorm 0 = 0`, `cutNorm (-W) = cutNorm W`."
  - id: C2-set-form
    anti_degeneracy: true
    claim: >
      `cutNorm W = sup_{S,T measurable} |∫_{S×T} W|` — the sup over rectangles, NOT the single
      number |∫∫ W|. A "cut norm" defined as |∫∫ W| would vanish on a balanced ±-pattern that is
      macroscopically far from 0; the sup form is what makes it a genuine norm.
  - id: C3-graphon-edge
    claim: "For a [0,1]-valued graphon, `cutNorm W = ∫∫ W = t(K₂, W)` (the integrand is nonnegative, so the sup is at S=T=Ω)."
  - id: C4-sandwich
    claim: "`cutNorm W ≤ cutNormSigned W ≤ 4·cutNorm W` (signed/unsigned test functions agree up to a factor 4)."
known_values:
  - instance: "cutNorm (c • W)"
    expected: "|c| · cutNorm W"
    theorem: Graphons.cutNorm_smul
    status: PROVEN_CORE_AXIOMS
  - instance: "cutNorm (U + W)"
    expected: "≤ cutNorm U + cutNorm W"
    theorem: Graphons.cutNorm_add_le
    status: PROVEN_CORE_AXIOMS
  - instance: "cutNorm 0"
    expected: "0"
    theorem: Graphons.cutNorm_zero
    status: PROVEN_CORE_AXIOMS
  - instance: "cutNorm (-W), cutNorm W"
    expected: "≥ 0; cutNorm (-W) = cutNorm W"
    theorem: "Graphons.cutNorm_nonneg, Graphons.cutNorm_neg"
    status: PROVEN_CORE_AXIOMS
  - instance: "cutNorm W (set vs test-function form)"
    expected: "sup_{S,T} |∫_{S×T} W|"
    theorem: Graphons.cutNorm_eq_cutNormSet
    status: PROVEN_CORE_AXIOMS
    note: "#print axioms pinned in Graphons/Tests/AxiomGuard.lean"
  - instance: "cutNorm W for a graphon W"
    expected: "∫∫ W = t(K₂, W)"
    theorem: Graphons.cutNorm_graphon
    status: PROVEN_CORE_AXIOMS
  - instance: "cutNormSigned vs cutNorm"
    expected: "cutNorm ≤ cutNormSigned ≤ 4·cutNorm"
    theorem: "Graphons.cutNorm_le_cutNormSigned, Graphons.cutNormSigned_le_four_mul"
    status: PROVEN_CORE_AXIOMS
well_definedness: >
  Test functions / indicators are bounded measurable; against a bounded measurable kernel on a
  probability space every slice integral is finite, and the family of rectangle integrals is
  bounded (so the sup exists — `bddAbove`).
anti_degeneracy:
  history: >
    The natural wrong definition |∫∫ W| (or an L¹/L² norm) misses sign-structured kernels and is
    not the cut norm: it would make δ□ collapse distinct graphons.
  current_guard: >
    `cutNorm_eq_cutNormSet` pins the sup-over-rectangles form, and the factor-4 sandwich
    (`cutNorm_le_cutNormSigned`, `cutNormSigned_le_four_mul`) pins the normalization against the
    signed variant.
status: >
  All rows PROVEN_CORE_AXIOMS (standard three); `cutNorm_eq_cutNormSet` is kernel-pinned in
  Graphons/Tests/AxiomGuard.lean.
---

# Contract — `Graphons.cutNorm`

The cut norm. Anti-degeneracy clause **C2** is the whole point: it is the **sup over measurable
rectangles**, not `|∫∫ W|` — the seminorm laws plus the set-form and the factor-4 sandwich pin
the definition. A reader checks the `known_values` rows (each a proved seminorm law or the
graphon-edge identity) without reading proofs.
