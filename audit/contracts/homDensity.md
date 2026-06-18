---
object: Graphons.homDensity
informal: >
  The homomorphism density t(F, W) of a finite simple graph F in a graphon W: the
  integral over Ω^{V(F)} (product probability measure) of the product, over the edges
  of F, of W at the endpoints — ∫ ∏_{e=(i,j)∈E(F)} W(x_i, x_j) d(μ^{V(F)}). For the step
  graphon of a finite graph G it is the combinatorial homomorphism density
  t(F, G) = hom(F, G) / |V(G)|^{|V(F)|}.
sources:
  - "Lovász, Large Networks and Graph Limits (AMS, 2012), §5.2, §7.2 (homomorphism densities t(F,W))"
lean:
  name: Graphons.homDensity
  signature: "{V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) : ℝ"
  body: "∫ x, (∏ e ∈ F.edgeFinset, edgeVal W x e) ∂(piMeasure V μ)   -- edges via Sym2.lift"
characterization:
  - id: C1-range
    claim: "t(F, W) ∈ [0,1] for every F, W."
  - id: C2-constant
    claim: "Erdős–Rényi: t(F, const p) = p^{e(F)} (the exponent is the EDGE count)."
  - id: C3-edge
    claim: "t(K₂, W) = ∫∫ W dμ dμ."
  - id: C4-multiplicative
    claim: "t(F₁ ⊕ F₂, W) = t(F₁, W) · t(F₂, W) over disjoint union."
  - id: C5-step-agreement
    anti_degeneracy: true
    claim: >
      On the step graphon of a finite graph G, t(F, step G) equals the combinatorial
      homomorphism density of G. This is the anti-hack clause: a look-alike that sums
      instead of multiplies over edges, or integrates over Ω^{E(F)} rather than Ω^{V(F)},
      satisfies neither C2 nor C5.
known_values:
  # instance -> expected -> witnessing theorem -> status (kernel-derived) -> note
  - instance: "t(K₂, const p)"
    expected: "p"
    theorem: Graphons.homDensity_const
    status: PROVEN_CORE_AXIOMS
    note: "e(K₂)=1; #print axioms pinned in Graphons/Tests/AxiomGuard.lean"
  - instance: "t(K₃, const p)"
    expected: "p^3"
    theorem: Graphons.homDensity_const
    status: PROVEN_CORE_AXIOMS
    note: "e(K₃)=3; AxiomGuard-pinned"
  - instance: "t(K₂, W)"
    expected: "∫∫ W dμ dμ"
    theorem: Graphons.homDensity_edge
    status: PROVEN_CORE_AXIOMS
    note: "AxiomGuard-pinned"
  - instance: "t(K₃, W)"
    expected: "∫ W(x₁,x₂)·W(x₁,x₃)·W(x₂,x₃)"
    theorem: Graphons.homDensity_triangle
    status: PROVEN_CORE_AXIOMS
    note: "AxiomGuard-pinned"
  - instance: "t(F₁ ⊕ F₂, W)"
    expected: "t(F₁, W) · t(F₂, W)"
    theorem: Graphons.homDensity_sum
    status: PROVEN_CORE_AXIOMS
    note: "AxiomGuard-pinned"
  - instance: "t(F, step G)"
    expected: "combinatorial homomorphism density hom(F,G)/|V(G)|^{|V(F)|}"
    theorem: Graphons.homDensity_step
    status: PROVEN_CORE_AXIOMS
    note: "AxiomGuard-pinned; the anti-hack C5 witness"
  - instance: "t(F, W) ∈ [0,1]"
    expected: "0 ≤ t ≤ 1"
    theorem: Graphons.homDensity_mem_Icc
    status: PROVEN_CORE_AXIOMS
    note: "basic layer (not separately AxiomGuard-pinned)"
well_definedness: >
  The integrand is a finite product of a bounded measurable kernel, hence integrable on
  the probability space Ω^{V(F)} under the product measure `piMeasure V μ`; edges are
  taken via `Sym2.lift`, so `edgeVal` is well-defined (symmetric in the endpoints).
anti_degeneracy:
  history: >
    The two natural wrong definitions are (a) dropping the edge product to a single factor
    — gives t(F, const p) = p, failing C2 — and (b) integrating over Ω^{E(F)} instead of
    Ω^{V(F)} — breaks the step-graphon agreement C5 (no shared vertices).
  current_guard: >
    C2 (homDensity_const) and C5 (homDensity_step) pin both failure modes; their
    `#print axioms` traces are CI-pinned in Graphons/Tests/AxiomGuard.lean, so the guards
    cannot silently rot.
status: >
  Validated on the seven rows above; const/edge/triangle/sum/step are kernel-pinned
  (#print axioms = the standard three) in Graphons/Tests/AxiomGuard.lean.
---

# Contract — `Graphons.homDensity`

The homomorphism density `t(F, W)`. A reader can confirm this is *the* graphon
homomorphism density, not a look-alike, **without reading any proof**: check the
`known_values` rows against the cited theorems (each carries a kernel-verified status),
and check the anti-degeneracy clause **C5** (agreement with the finite homomorphism
density on step graphons) — the property a wrong definition fails. Status values are
read from `#print axioms`; the witnessing theorems for the small cases are pinned in
[`Graphons/Tests/AxiomGuard.lean`](../../Graphons/Tests/AxiomGuard.lean).
