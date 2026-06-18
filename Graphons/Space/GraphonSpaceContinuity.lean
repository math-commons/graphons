/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits):
  **Continuity of homomorphism densities on graphon space.**  Each map
    `t(F, ·) : GraphonSpace Ω μ → ℝ`
  is `e(F)`-Lipschitz (hence continuous) for the cut metric `δ□`.  Together over all finite
  graphs `F`, these continuous functions form the separating family realizing the universal
  embedding `GraphonSpace ↪ ℝ^{graphs}`.  Sources: Lovász, "Large Networks and Graph Limits"
  (2012), counting lemma + cut-metric chapter.

The content is the counting lemma `abs_homDensity_sub_le_cutDist`, which after passing to the
quotient (`Quotient.inductionOn₂` + the `dist_mk`/`homDensity_mk` simp lemmas) gives the
quotient-level bound `|t(F,x) − t(F,y)| ≤ e(F)·dist x y`.  `LipschitzWith` and `Continuous`
then follow from the standard `ℝ`-valued `LipschitzWith.of_dist_le_mul` API.
-/
import Graphons.Space.GraphonSpace
import Graphons.Space.GraphonSpaceMetric
import Graphons.Counting.CountingLemmaCutDist

open MeasureTheory

namespace Graphons

section Continuity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [StandardBorelSpace Ω]

/-- **Quotient-level counting lemma.**  The homomorphism density `t(F, ·)` on graphon space is
`e(F)`-Lipschitz for the cut metric: `|t(F,x) − t(F,y)| ≤ e(F)·dist x y`. -/
theorem GraphonSpace.abs_homDensity_sub_le_dist {V} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (x y : GraphonSpace Ω μ) :
    |GraphonSpace.homDensity F x - GraphonSpace.homDensity F y| ≤
      (F.edgeFinset.card : ℝ) * dist x y := by
  induction x using Quotient.inductionOn with
  | _ U =>
    induction y using Quotient.inductionOn with
    | _ W =>
      -- On representatives this is exactly the cross-carrier counting lemma.
      simpa using abs_homDensity_sub_le_cutDist F U W

/-- **`t(F, ·)` is `e(F)`-Lipschitz on graphon space.**  The Lipschitz constant is the `ℝ≥0`
cast of the edge count `e(F)`. -/
theorem GraphonSpace.lipschitzWith_homDensity {V} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] :
    LipschitzWith (F.edgeFinset.card) (GraphonSpace.homDensity (Ω := Ω) (μ := μ) F) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  -- `((e(F) : ℝ≥0) : ℝ) = (e(F) : ℝ)`, then apply the quotient-level bound.
  simpa using GraphonSpace.abs_homDensity_sub_le_dist F x y

/-- **`t(F, ·)` is continuous on graphon space.**  Immediate from Lipschitz continuity. -/
theorem GraphonSpace.continuous_homDensity {V} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] :
    Continuous (GraphonSpace.homDensity (Ω := Ω) (μ := μ) F) :=
  (GraphonSpace.lipschitzWith_homDensity F).continuous

end Continuity

end Graphons
