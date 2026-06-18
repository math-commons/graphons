---
object: Graphons.Graphon (and Graphons.SymmKernel)
informal: >
  A graphon is a symmetric, measurable, bounded, [0,1]-valued kernel W : Ω × Ω → ℝ on a
  probability space (Ω, μ) — the limit object of dense graph sequences. `SymmKernel` is the
  symmetric measurable bounded ℝ-kernel without the [0,1] constraint; it carries the
  AddCommGroup + ℝ-Module structure, so that differences `U - W` of graphons (which leave
  [0,1]) live in `SymmKernel` and feed the cut metric.
sources:
  - "Lovász, Large Networks and Graph Limits (AMS, 2012), §7.1 (graphons / kernels)"
lean:
  name: Graphons.Graphon
  signature: "structure Graphon (Ω) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] extends SymmKernel Ω μ  -- + [0,1]-valued"
  body: "SymmKernel: { toFun : Ω→Ω→ℝ, symm' : ∀ x y, toFun x y = toFun y x, meas', bdd' }; Graphon adds the [0,1] bound."
characterization:
  - id: C1-symmetric
    claim: "W x y = W y x (the kernel is symmetric)."
  - id: C2-valued
    anti_degeneracy: true
    claim: >
      A Graphon is [0,1]-valued; a bare symmetric kernel is a SymmKernel. The cut-metric
      module lives on SymmKernel, NOT Graphon, precisely because a difference U - W of
      graphons leaves [0,1] — baking [0,1] into the additive object would be the wrong design.
  - id: C3-module
    claim: "SymmKernel is an AddCommGroup and ℝ-Module (so U - W and c • W are well-typed)."
  - id: C4-ext
    claim: "Pointwise equality of kernels implies equality (extensionality)."
known_values:
  - instance: "W x y vs W y x"
    expected: "equal (symmetry)"
    theorem: Graphons.SymmKernel.symm'
    status: PROVEN_CORE_AXIOMS
    note: "structure field"
  - instance: "Graphon.const p (0≤p≤1)"
    expected: "a Graphon, value p at every (x,y)"
    theorem: Graphons.Graphon.const_apply
    status: PROVEN_CORE_AXIOMS
  - instance: "Graphon.step G (finite graph G)"
    expected: "a Graphon (the step graphon W_G)"
    theorem: Graphons.step_apply
    status: PROVEN_CORE_AXIOMS
  - instance: "U - W, c • W"
    expected: "SymmKernel (AddCommGroup + Module)"
    theorem: "Graphons.SymmKernel instances (AddCommGroup, Module ℝ)"
    status: PROVEN_CORE_AXIOMS
  - instance: "U x y = W x y for all x,y"
    expected: "U = W"
    theorem: Graphons.SymmKernel.ext
    status: PROVEN_CORE_AXIOMS
well_definedness: >
  `bdd'` (a uniform bound) + `meas'` (joint measurability of the uncurried kernel) are what
  make every downstream integral (homDensity, cutNorm) well-defined on the probability space.
anti_degeneracy:
  history: >
    Two wrong designs: (a) dropping symmetry — then cutNorm/homDensity lose the Sym2 structure;
    (b) putting the AddCommGroup/Module on Graphon itself — then `U - W` would be forced into
    [0,1] and the cut metric on differences breaks.
  current_guard: >
    `symm'` is a structure field (cannot be omitted); the module instances are declared on
    `SymmKernel`, and `Graphon` is the [0,1] sub-collection — so differences land in `SymmKernel`
    by construction.
status: >
  Structural laws all PROVEN_CORE_AXIOMS (standard three). Symmetry/measurability/boundedness
  are fields; the AddCommGroup/Module on SymmKernel is the carrier of the cut metric.
---

# Contract — `Graphons.Graphon` / `Graphons.SymmKernel`

The graphon object. The load-bearing design decision — recorded as anti-degeneracy clause
**C2** — is that the additive/scalar structure lives on `SymmKernel` (no [0,1] constraint),
because differences `U - W` of graphons leave [0,1]; `Graphon` is the [0,1] sub-collection.
A reader can confirm the object is right without reading proofs: symmetry is a field, and the
`known_values` rows pin the standard instances (`const`, `step`) and the module structure.
