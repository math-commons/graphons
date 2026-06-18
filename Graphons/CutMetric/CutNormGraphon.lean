/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

The **cut norm of a graphon equals its edge density**. This is the key tie between the
analytic `cutNorm` (test-function supremum) and the combinatorial `homDensity` of the single
edge `K₂ = (⊤ : SimpleGraph (Fin 2))`.

For a `Graphon Ω μ` `W` (a `[0,1]`-valued symmetric kernel):
  * `cutNorm_graphon`      : `cutNorm W.toSymmKernel = ∫∫ W`.
  * `cutNorm_eq_homDensity`: `cutNorm W.toSymmKernel = homDensity (⊤ : SimpleGraph (Fin 2)) W`.

The supremum is attained at the constant test function `u = v = 1`: since `W ≥ 0` and every
test function lies in `[0,1]`, each integrand `∫ W·u·v` is between `0` and `∫ W·1·1 = ∫∫ W`.
-/
import Graphons.CutMetric.CutNorm
import Graphons.Core.Examples

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The constant `1` function is a test function. -/
theorem isTestFun_one : IsTestFun (fun _ : Ω => (1 : ℝ)) :=
  ⟨measurable_const, fun _ => ⟨zero_le_one, le_refl 1⟩⟩

/-- For a graphon `W` and test functions `u, v`, the value `|∫ W·u·v|` is bounded above by
    the edge density `∫∫ W`. Everything is `≥ 0` (`W ≥ 0`, `u, v ∈ [0,1]`), so the absolute
    value drops and `integral_mono` against `W·1·1 = W` finishes. -/
theorem abs_integral_le_edgeDensity (W : Graphon Ω μ) {u v : Ω → ℝ}
    (hu : IsTestFun u) (hv : IsTestFun v) :
    |∫ p : Ω × Ω, W.toSymmKernel.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
      ≤ ∫ p : Ω × Ω, W.toFun p.1 p.2 ∂(μ.prod μ) := by
  -- The integrand is pointwise `≥ 0`.
  have hnonneg : ∀ p : Ω × Ω, 0 ≤ W.toSymmKernel.toFun p.1 p.2 * u p.1 * v p.2 := by
    intro p
    exact mul_nonneg (mul_nonneg (W.nonneg' p.1 p.2) (hu.nonneg p.1)) (hv.nonneg p.2)
  -- Drop the absolute value.
  rw [abs_of_nonneg (integral_nonneg hnonneg)]
  -- Pointwise `W·u·v ≤ W` (using `u, v ≤ 1` and `W ≥ 0`).
  refine integral_mono (integrable_integrand W.toSymmKernel hu hv) W.integrable_uncurry
    fun p => ?_
  have hWnn : 0 ≤ W.toSymmKernel.toFun p.1 p.2 := W.nonneg' p.1 p.2
  calc W.toSymmKernel.toFun p.1 p.2 * u p.1 * v p.2
      ≤ W.toSymmKernel.toFun p.1 p.2 * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (hu.le_one p.1) hWnn)
          (hv.le_one p.2) (hv.nonneg p.2)
        exact mul_nonneg hWnn zero_le_one
    _ = W.toFun p.1 p.2 := by simp

/-- **Cut norm of a graphon = edge density.** For a graphon `W`,
    `cutNorm W.toSymmKernel = ∫∫ W dμ dμ`.

    Lower bound: the constant `1` test pair gives `|∫ W·1·1| = ∫∫ W` (as `W ≥ 0`).
    Upper bound: for any test pair `u,v`, `0 ≤ W·u·v ≤ W·1·1` pointwise, so
    `|∫ W·u·v| ≤ ∫ W·1·1 = ∫∫ W`. -/
theorem cutNorm_graphon (W : Graphon Ω μ) :
    cutNorm W.toSymmKernel = ∫ p : Ω × Ω, W.toFun p.1 p.2 ∂(μ.prod μ) := by
  set I : ℝ := ∫ p : Ω × Ω, W.toFun p.1 p.2 ∂(μ.prod μ) with hI
  have hInonneg : 0 ≤ I := integral_nonneg fun p => W.nonneg' p.1 p.2
  refine le_antisymm ?_ ?_
  · -- Upper bound: cutNorm ≤ I. Collapse the binders as in `inner_le_bound`/`cutNorm_le_bound`.
    rw [cutNorm]
    refine ciSup_le fun u => ciSup_le fun v => ?_
    by_cases hu : IsTestFun u
    · by_cases hv : IsTestFun v
      · simp only [ciSup_pos hu, ciSup_pos hv]
        exact abs_integral_le_edgeDensity W hu hv
      · rw [ciSup_pos hu, ciSup_neg hv]; simpa using hInonneg
    · rw [ciSup_neg hu]; simpa using hInonneg
  · -- Lower bound: I ≤ cutNorm, via the constant `1` test pair.
    have h := le_cutNorm W.toSymmKernel isTestFun_one isTestFun_one
    simp only [mul_one] at h
    rwa [abs_of_nonneg hInonneg] at h

/-- **Cut norm of a graphon = its edge homomorphism density.** Combines `cutNorm_graphon`
    with `homDensity_edge`: `cutNorm W = t(K₂, W)`. -/
theorem cutNorm_eq_homDensity (W : Graphon Ω μ) :
    cutNorm W.toSymmKernel = homDensity (⊤ : SimpleGraph (Fin 2)) W := by
  rw [cutNorm_graphon, homDensity_edge]

end Graphons
