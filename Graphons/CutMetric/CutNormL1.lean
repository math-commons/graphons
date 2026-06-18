/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits), VALIDATION.md Tier B:
  The **cut-norm ≤ L¹** comparison `‖W‖□ ≤ ∫∫ |W|`.

For every test pair `u, v` (measurable, `[0,1]`-valued) the integrand value satisfies
  `|∫ W·u·v| ≤ ∫ |W·u·v| = ∫ |W|·u·v ≤ ∫ |W|`,
using `|·| ∘ ∫ ≤ ∫ ∘ |·|`, `u, v ≥ 0` (to drop absolute values off `u, v`), and `u, v ≤ 1`
with `|W| ≥ 0` (monotonicity of the integral).  The supremum over test pairs is then bounded by
the constant `∫ |W|` via the same nested-`ciSup` peeling used for `cutNorm_le_bound`.
-/
import Graphons.CutMetric.CutNorm

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `(x,y) ↦ |W x y|` is integrable against `μ ×ˢ μ` (it is bounded by `W.bound ≥ 0`). -/
theorem integrable_abs_kernel (W : SymmKernel Ω μ) :
    Integrable (fun p : Ω × Ω => |W.toFun p.1 p.2|) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd
    (W.meas'.comp (measurable_fst.prodMk measurable_snd) |>.abs) (C := W.bound) (fun p => ?_)
  obtain ⟨x, y⟩ := p
  rw [abs_abs]
  exact W.abs_le_bound x y

omit [IsProbabilityMeasure μ] in
/-- Pointwise, for a test pair: `|W x y · u x · v y| = |W x y| · u x · v y`, since `u, v ≥ 0`. -/
theorem abs_integrand_eq (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) (x y : Ω) :
    |W.toFun x y * u x * v y| = |W.toFun x y| * u x * v y := by
  rw [abs_mul, abs_mul, abs_of_nonneg (hu.nonneg x), abs_of_nonneg (hv.nonneg y)]

/-- The core per-test-pair estimate: `|∫ W·u·v| ≤ ∫ |W|`. -/
theorem abs_integral_le_L1 (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) :
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
      ≤ ∫ p : Ω × Ω, |W.toFun p.1 p.2| ∂(μ.prod μ) := by
  calc |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
      ≤ ∫ p, |W.toFun p.1 p.2 * u p.1 * v p.2| ∂(μ.prod μ) := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ.prod μ)
            (fun p => W.toFun p.1 p.2 * u p.1 * v p.2)
    _ = ∫ p, |W.toFun p.1 p.2| * u p.1 * v p.2 ∂(μ.prod μ) := by
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        obtain ⟨x, y⟩ := p
        exact abs_integrand_eq W hu hv x y
    _ ≤ ∫ p, |W.toFun p.1 p.2| ∂(μ.prod μ) := by
        refine integral_mono ?_ (integrable_abs_kernel W) (fun p => ?_)
        · -- `|W|·u·v` is integrable: it is `|·|` of the original integrand, by the pointwise eq.
          refine ((integrable_integrand W hu hv).abs).congr (ae_of_all _ fun p => ?_)
          obtain ⟨x, y⟩ := p
          exact abs_integrand_eq W hu hv x y
        · obtain ⟨x, y⟩ := p
          -- `|W|·u·v ≤ |W|·1·1 = |W|`, using `u,v ≤ 1` and `|W| ≥ 0`.
          calc |W.toFun x y| * u x * v y
              ≤ |W.toFun x y| * 1 * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hu.le_one x) (abs_nonneg _))
                  (hv.le_one y) (hv.nonneg y)
                  (mul_nonneg (abs_nonneg _) zero_le_one)
            _ = |W.toFun x y| := by ring

/-- For a fixed `u`, the inner `⨆` over the `Prop`-binders is `≤ ∫ |W|` (mirrors `inner_le_bound`). -/
theorem inner_le_L1 (W : SymmKernel Ω μ) (u v : Ω → ℝ) :
    (⨆ (_ : IsTestFun u) (_ : IsTestFun v),
      |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|)
      ≤ ∫ p : Ω × Ω, |W.toFun p.1 p.2| ∂(μ.prod μ) := by
  have hL1 : 0 ≤ ∫ p : Ω × Ω, |W.toFun p.1 p.2| ∂(μ.prod μ) :=
    integral_nonneg (fun _ => abs_nonneg _)
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · simp only [ciSup_pos hu, ciSup_pos hv]
      exact abs_integral_le_L1 W hu hv
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using hL1
  · rw [ciSup_neg hu]; simpa using hL1

/-- **The cut-norm ≤ L¹ comparison** (VALIDATION.md Tier B):
    `‖W‖□ ≤ ∫∫ |W(x,y)| dμ dμ`. -/
theorem cutNorm_le_L1 (W : SymmKernel Ω μ) :
    cutNorm W ≤ ∫ p : Ω × Ω, |W.toFun p.1 p.2| ∂(μ.prod μ) := by
  rw [cutNorm]
  exact ciSup_le fun u => ciSup_le fun v => inner_le_L1 W u v

end Graphons
