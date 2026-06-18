/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier E, item E2 — **existence: `GraphonSpace ℝ unitMeasure` is a
model of the dense-graph-limit-theory spec** (recommended check #1 of
an independent spec review).

The model data:
  * `FinWeighted.toSpace` — the interval step transport `G ↦ ⟦G.toUnit⟧` into graphon space;
  * `GraphonSpace.homDensity` — the descended homomorphism-density functionals.

The four spec fields:
  * `dist_ι`     : `dist (toSpace G) (toSpace H) = δ□(G, H)` — from `cutDist_toUnit`
    (`δ□(G.toUnit, G) = 0`, the graph-coupling lemma) + four cross-carrier triangle
    inequalities (Gluing Lemma);
  * `dense_range`: from weak regularity (`exists_stepGraphon_cutDist_le`) + the
    mass-rounding approximation (`exists_finWeighted_cutDist_le`);
  * `continuous_t`, `compat_t`: from `GraphonSpace.continuous_homDensity` and
    `homDensity_toUnit` (hom densities are invariant under the interval transport).

Axiom budget: inherits the two completeness ledger axioms (`cutNorm_alignment_unit`,
`dyadic_l1Cauchy_approx_unit`) through `instCompleteSpaceGraphonSpaceUnit` — and nothing else
(pinned in `Tests/AxiomGuard.lean`).
-/
import Graphons.Characterization.LimitSpecDensity
import Graphons.Space.GraphonSpaceContinuity
import Graphons.Limits.CompletenessUnit

open MeasureTheory

namespace Graphons

/-! ### The transport into graphon space -/

/-- The **step transport into graphon space**: a finite weighted graph maps to the class of
    its interval step graphon. NOT injective — weakly isomorphic weighted graphs (e.g.
    blow-ups) land on the same point, as the spec requires. -/
noncomputable def FinWeighted.toSpace (G : FinWeighted) : GraphonSpace ℝ unitMeasure :=
  Quotient.mk (graphonSetoid ℝ unitMeasure) G.toUnit

/-- The transport is distance-preserving: `dist (toSpace G) (toSpace H) = δ□(G, H)`.
    Both inequalities follow from `cutDist_toUnit` (`δ□(toUnit G, G) = 0`) and the
    cross-carrier triangle inequality. -/
theorem FinWeighted.dist_toSpace (G H : FinWeighted) :
    dist G.toSpace H.toSpace = finCutDist G H := by
  show GraphonSpace.dist _ _ = _
  rw [FinWeighted.toSpace, FinWeighted.toSpace, GraphonSpace.dist_mk]
  have tG : cutDist G.toUnit G.2 = 0 := cutDist_toUnit G
  have tH : cutDist H.toUnit H.2 = 0 := cutDist_toUnit H
  have tG' : cutDist G.2 G.toUnit = 0 := by rw [cutDist_comm]; exact tG
  have tH' : cutDist H.2 H.toUnit = 0 := by rw [cutDist_comm]; exact tH
  -- ≤ : uG → G → H → uH ;  ≥ : G → uG → uH → H
  have t1 := cutDist_triangle G.toUnit G.2 H.toUnit
  have t2 := cutDist_triangle G.2 H.2 H.toUnit
  have t3 := cutDist_triangle G.2 G.toUnit H.2
  have t4 := cutDist_triangle G.toUnit H.toUnit H.2
  show cutDist G.toUnit H.toUnit = cutDist G.2 H.2
  refine le_antisymm (by linarith) (by linarith)

/-- The transport has dense range: every graphon class is approximated by finite weighted
    graphs (weak regularity + mass rounding). -/
theorem FinWeighted.denseRange_toSpace : DenseRange FinWeighted.toSpace := by
  rw [Metric.denseRange_iff]
  intro x r hr
  obtain ⟨W, rfl⟩ := Quotient.exists_rep x
  obtain ⟨G, hG⟩ := exists_finWeighted_cutDist_le W (half_pos hr)
  refine ⟨G, ?_⟩
  show GraphonSpace.dist _ _ < r
  rw [FinWeighted.toSpace, GraphonSpace.dist_mk]
  have hcomm : cutDist W G.toUnit = cutDist G.toUnit W := cutDist_comm W G.toUnit
  linarith

/-! ### E2 — the existence theorem -/

/-- The density functionals of the model: the descended homomorphism densities. -/
noncomputable def spaceHomDensity : ∀ ⦃n : ℕ⦄ (F : SimpleGraph (Fin n)),
    DecidableRel F.Adj → GraphonSpace ℝ unitMeasure → ℝ :=
  fun _ F inst x => letI := inst; GraphonSpace.homDensity F x

/-- **E2 (existence).** `GraphonSpace ℝ unitMeasure`, with the interval step transport and
    the descended homomorphism densities, is a model of the dense-graph-limit-theory spec.
    (With E3 — uniqueness of models — this forces the construction up to canonical isometry.) -/
theorem isDenseGraphLimitTheory_graphonSpace :
    IsDenseGraphLimitTheory (GraphonSpace ℝ unitMeasure) FinWeighted.toSpace
      spaceHomDensity where
  dense_range := FinWeighted.denseRange_toSpace
  dist_ι := FinWeighted.dist_toSpace
  continuous_t := fun _ F inst => by
    letI := inst
    exact GraphonSpace.continuous_homDensity F
  compat_t := fun _ F inst G => by
    letI := inst
    show GraphonSpace.homDensity F (Quotient.mk (graphonSetoid ℝ unitMeasure) G.toUnit) = _
    rw [GraphonSpace.homDensity_mk, homDensity_toUnit]
    rfl

end Graphons
