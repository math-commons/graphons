/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits), Tier C:
  **Step graphons are dense in the cut distance** (the density half of the completion /
  universal property).  This is an immediate corollary of the weak regularity lemma: for every
  graphon `W` and `ε > 0` there is a step graphon `stepGraphon W P` with `δ□(W, stepGraphon W P) ≤ ε`.
  Source: Lovász, "Large Networks and Graph Limits" (2012), §9.

DESIGN.
* `cutDist_le_cutNorm` — over the SAME carrier `(Ω, μ)`, the cut distance is bounded by the cut
  norm of the difference, via the **diagonal coupling** `μ.map (x ↦ (x,x))`.  The overlaid
  difference along the diagonal is `U(x)(y) − W(x)(y)`, whose cut norm is `≤` (in fact `=`)
  `cutNorm (U − W)`.  The `≤` direction (which is all we need) follows by a change of variables:
  any test pair `(u, v)` on `Ω × Ω` restricts along the diagonal to a test pair on `Ω`.
* `stepGraphon W P` — `stepW W P` packaged as a `Graphon` (it is `[0,1]`-valued for a graphon `W`,
  by `stepW_mem_Icc`).
* `exists_stepGraphon_cutDist_le` — combine `weak_regularity` with `cutDist_le_cutNorm`.
-/
import Graphons.Limits.WeakRegularity
import Graphons.CutMetric.CutDist

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## `cutDist ≤ cutNorm` over the same carrier (via the diagonal coupling) -/

/-- **Change of variables along the diagonal.**  For a coupling-free statement on the same carrier:
    the overlay integral of `U, W` over the diagonal coupling, against test functions `u, v` on
    `Ω × Ω`, equals the cut-norm integral of the difference kernel `U − W` against the
    *diagonal-restricted* test functions `a ↦ u (a, a)`, `c ↦ v (c, c)`. -/
theorem integral_overlay_diag (U W : Graphon Ω μ) {u v : Ω × Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v) :
    ∫ p, (overlay U W (diagCoupling μ)).toFun p.1 p.2 * u p.1 * v p.2
        ∂((diagCoupling μ).prod (diagCoupling μ))
      = ∫ p, (U.toSymmKernel - W.toSymmKernel).toFun p.1 p.2
          * (fun a => u (a, a)) p.1 * (fun c => v (c, c)) p.2 ∂(μ.prod μ) := by
  haveI : IsProbabilityMeasure (diagCoupling μ) :=
    (isCoupling_diagCoupling μ).isProbabilityMeasure
  have hdiag : Measurable (fun x : Ω => (x, x)) := measurable_id.prodMk measurable_id
  have hmap : (diagCoupling μ).prod (diagCoupling μ)
      = (μ.prod μ).map (Prod.map (fun x => (x, x)) (fun x => (x, x))) := by
    rw [diagCoupling, Measure.map_prod_map _ _ hdiag hdiag]
  rw [hmap, integral_map]
  · refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [Prod.map_apply', overlay_apply, SymmKernel.sub_apply]
  · exact (Measurable.prodMap hdiag hdiag).aemeasurable
  · exact (measurable_integrand (overlay U W (diagCoupling μ)) hu hv).aestronglyMeasurable

/-- The overlay of `U, W` over the diagonal coupling has cut norm `≤` that of the difference kernel
    `U − W` (on the same carrier).  Any test pair `(u, v)` on `Ω × Ω` restricts along the diagonal
    to the test pair `(a ↦ u (a, a), c ↦ v (c, c))` on `Ω`, and the two integrals coincide. -/
theorem cutNorm_overlay_diag_le (U W : Graphon Ω μ) :
    cutNorm (overlay U W (diagCoupling μ)) ≤ cutNorm (U.toSymmKernel - W.toSymmKernel) := by
  haveI : IsProbabilityMeasure (diagCoupling μ) :=
    (isCoupling_diagCoupling μ).isProbabilityMeasure
  rw [cutNorm]
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      -- The diagonal-restricted test functions.
      have hu' : IsTestFun (fun a : Ω => u (a, a)) :=
        ⟨hu.measurable.comp (measurable_id.prodMk measurable_id), fun a => hu.2 (a, a)⟩
      have hv' : IsTestFun (fun c : Ω => v (c, c)) :=
        ⟨hv.measurable.comp (measurable_id.prodMk measurable_id), fun c => hv.2 (c, c)⟩
      rw [integral_overlay_diag U W hu.measurable hv.measurable]
      exact le_cutNorm (U.toSymmKernel - W.toSymmKernel) hu' hv'
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using cutNorm_nonneg _
  · rw [ciSup_neg hu]; simpa using cutNorm_nonneg _

/-- **`cutDist ≤ cutNorm` (same carrier).**  The cut distance between graphons `U, W` over the
    common probability space `(Ω, μ)` is bounded by the cut norm of their difference, using the
    diagonal coupling. -/
theorem cutDist_le_cutNorm (U W : Graphon Ω μ) :
    cutDist U W ≤ cutNorm (U.toSymmKernel - W.toSymmKernel) :=
  le_trans (cutDist_le_of_coupling U W ⟨diagCoupling μ, isCoupling_diagCoupling μ⟩)
    (cutNorm_overlay_diag_le U W)

/-! ## Step graphons -/

/-- The **step graphon** of `W` w.r.t. partition `P`: the block-averaged step kernel `stepW W P`
    packaged as a `Graphon` (it is `[0,1]`-valued for a graphon `W`, by `stepW_mem_Icc`). -/
noncomputable def stepGraphon (W : Graphon Ω μ) (P : MeasPartition Ω μ) : Graphon Ω μ :=
  Graphon.mk' (stepW W.toSymmKernel P).toFun (stepW W.toSymmKernel P).symm'
    (stepW W.toSymmKernel P).meas'
    (fun x y => (stepW_mem_Icc W P x y).1) (fun x y => (stepW_mem_Icc W P x y).2)

@[simp] theorem stepGraphon_toSymmKernel (W : Graphon Ω μ) (P : MeasPartition Ω μ) :
    (stepGraphon W P).toSymmKernel = stepW W.toSymmKernel P := rfl

/-! ## Density of step graphons -/

/-- **Step graphons are dense in the cut distance.**  For every graphon `W` and `ε > 0` there is a
    finite measurable partition `P` such that the step graphon `stepGraphon W P` is within cut
    distance `ε` of `W`.  Immediate from the weak regularity lemma (`weak_regularity`) and
    `cutDist_le_cutNorm`. -/
theorem exists_stepGraphon_cutDist_le (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MeasPartition Ω μ, cutDist W (stepGraphon W P) ≤ ε := by
  obtain ⟨P, hP⟩ := weak_regularity W hε
  refine ⟨P, ?_⟩
  refine le_trans (cutDist_le_cutNorm W (stepGraphon W P)) ?_
  rwa [stepGraphon_toSymmKernel]

end Graphons
