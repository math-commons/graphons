/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

The step graphon realizes the FINITE homomorphism density (VALIDATION.md Tier B;
"graphons extend finite graphs"). For a finite graph `F` on a fintype `V` and a finite graph
`G : SimpleGraph (Fin n)`, the homomorphism density of `F` into the step graphon `Graphon.step G`
equals the average over all maps `φ : V → Fin n` of `∏_{e ∈ E(F)} (step G)(φ a)(φ b)`, i.e. the
(normalized) homomorphism count. The two ingredients are:
  * the product of the uniform measure on `Fin n` over `V` is the uniform measure on `V → Fin n`,
  * the integral against a uniform measure on a fintype is the average `(∑ over the fintype)/card`.
-/
import Graphons.Core.Step

open MeasureTheory

namespace Graphons

variable {n : ℕ} [NeZero n] {V : Type*} [Fintype V] [DecidableEq V]

/-- The product over `V` of the uniform measure on `Fin n` is the uniform measure on `V → Fin n`.
    Both sides are determined by their values on singletons (the space is countable with measurable
    singletons); `Measure.pi_singleton` gives `∏_v (1/n)` and the uniform PMF gives `1/n^{|V|}`. -/
theorem piMeasure_unifFin_eq :
    piMeasure V (unifFin n) = (PMF.uniformOfFintype (V → Fin n)).toMeasure := by
  refine Measure.ext_of_singleton (fun φ => ?_)
  rw [piMeasure, unifFin, Measure.pi_singleton,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton φ),
    PMF.uniformOfFintype_apply, Fintype.card_pi, Fintype.card_fin, Finset.prod_const]
  -- LHS: `∏ i, (uniform (Fin n)).toMeasure {φ i}`; each factor is `(n : ℝ≥0∞)⁻¹`.
  have hfac : ∀ i : V, (PMF.uniformOfFintype (Fin n)).toMeasure {φ i} = (n : ENNReal)⁻¹ := by
    intro i
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
  simp only [hfac, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.inv_pow, ← Nat.cast_pow]

/-- Integral against the uniform measure on a fintype is the average over the fintype. -/
theorem integral_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ∫ a, f a ∂((PMF.uniformOfFintype α).toMeasure) = (∑ a, f a) / (Fintype.card α : ℝ) := by
  rw [PMF.integral_eq_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [PMF.uniformOfFintype_apply]
  rw [smul_eq_mul, div_eq_inv_mul]
  congr 1
  rw [ENNReal.toReal_inv]
  simp

/-- **The step graphon realizes the finite homomorphism density.** The homomorphism density of
    `F` into the step graphon of `G` is the average over all maps `φ : V → Fin n` of the product
    over the edges of `F` of `(step G)(φ a)(φ b)` — i.e. the homomorphism count divided by
    `n ^ |V|`. -/
theorem homDensity_step
    (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    homDensity F (Graphon.step G)
      = (∑ φ : V → Fin n, ∏ e ∈ F.edgeFinset, edgeVal (Graphon.step G) φ e)
          / (n : ℝ) ^ (Fintype.card V) := by
  rw [homDensity]
  simp only [homDensityIntegrand]
  rw [piMeasure_unifFin_eq, integral_uniformOfFintype]
  congr 1
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

end Graphons
