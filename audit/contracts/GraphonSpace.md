---
object: Graphons.GraphonSpace
informal: >
  The space of graphons modulo cut distance zero (weak isomorphism): the quotient of `Graphon Ω μ`
  by the setoid `graphonSetoid`, with the δ□ metric descended to it and homomorphism densities
  `t(F, ·)` descending to continuous functions. This is the metric space in which dense graph
  limits live.
sources:
  - "Lovász, Large Networks and Graph Limits (AMS, 2012), §8.2, Ch. 11 (the space of graphons; convergence); Thm 11.3 (separation)"
lean:
  name: Graphons.GraphonSpace
  signature: "def GraphonSpace : Type _ := Quotient (graphonSetoid Ω μ)   -- + GraphonSpace.dist, GraphonSpace.homDensity"
  body: "quotient by graphonSetoid; dist via cutDist (well-defined by cutDist_congr); homDensity descended (homDensity_mk)."
characterization:
  - id: C1-quotient
    claim: "`GraphonSpace.homDensity F ⟦W⟧ = homDensity F W` and `GraphonSpace.dist ⟦U⟧ ⟦W⟧ = cutDist U W` (the descents are well-defined)."
  - id: C2-metric
    claim: "δ□ descends to a (pseudo)metric on the quotient; `t(F, ·)` is Lipschitz/continuous in it (`lipschitzWith_homDensity`, constant e(F))."
  - id: C3-separation
    anti_degeneracy: true
    claim: >
      The quotient identifies exactly the graphons with equal homomorphism densities:
      `⟦U⟧ = ⟦W⟧ ↔ ∀ F, t(F,U) = t(F,W)` (moment map injective). A quotient that is too coarse
      (identifying density-distinct graphons) or too fine (separating weakly isomorphic ones)
      fails this — it is the defining property of the limit space.
known_values:
  - instance: "GraphonSpace.homDensity F ⟦W⟧"
    expected: "homDensity F W"
    theorem: Graphons.GraphonSpace.homDensity_mk
    status: PROVEN_CORE_AXIOMS
  - instance: "GraphonSpace.dist ⟦U⟧ ⟦W⟧"
    expected: "cutDist U W"
    theorem: Graphons.GraphonSpace.dist_mk
    status: PROVEN_CORE_AXIOMS
  - instance: "|t(F,x) − t(F,y)|"
    expected: "≤ e(F) · dist x y (Lipschitz)"
    theorem: "Graphons.GraphonSpace.abs_homDensity_sub_le_dist, lipschitzWith_homDensity"
    status: PROVEN_CORE_AXIOMS
  - instance: "t(F, ·) on GraphonSpace"
    expected: "continuous"
    theorem: Graphons.GraphonSpace.continuous_homDensity
    status: PROVEN_CORE_AXIOMS
  - instance: "⟦U⟧ = ⟦W⟧  (on the canonical carrier)"
    expected: "↔ ∀ F, t(F,U) = t(F,W) (moment map injective)"
    theorem: Graphons.GraphonSpace.eq_iff_homDensity_eq
    status: proven_mod_axioms
    note: "depends on cutDist_eq_zero_of_homDensity_eq (inverse counting lemma) — see AXIOM_AUDIT.md"
well_definedness: >
  The descents rely on `cutDist_congr` (cutDist respects the setoid) and `homDensity_mk`
  (homDensity is constant on equivalence classes); the metric on the quotient is the descended
  cutDist (a genuine metric once δ□ = 0 ⇒ equal classes).
anti_degeneracy:
  history: >
    A quotient by the wrong relation (e.g. raw pointwise a.e. equality, ignoring relabelling)
    would not be the graphon limit space — it would separate weakly isomorphic graphons.
  current_guard: >
    `eq_iff_homDensity_eq` pins the quotient to exactly the moment-determined relation
    (forward direction proved; converse via the inverse-counting axiom — hence the
    `proven_mod_axioms` status on that row, honestly surfaced).
status: >
  Quotient/metric/continuity rows PROVEN_CORE_AXIOMS (standard three). The separation/injectivity
  row is `proven_mod_axioms` (one vetted classical axiom, `cutDist_eq_zero_of_homDensity_eq`) —
  recorded here and in AXIOM_AUDIT.md; this card deliberately shows the mixed status.
---

# Contract — `Graphons.GraphonSpace`

The space of graphons up to weak isomorphism. This card illustrates **mixed status**: the
quotient/metric/continuity structure is axiom-clean (`PROVEN_CORE_AXIOMS`), while the
defining **separation** property (anti-degeneracy clause **C3**, moment-map injectivity) is
`proven_mod_axioms` — its converse rests on the vetted inverse-counting axiom. A reader sees,
without reading proofs, exactly which part of "this is the limit space" is unconditional and
which leans on a documented axiom.
