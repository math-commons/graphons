/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

VALIDATION.md Tier A — sanity / encoding-correctness theorems pinning down that
`homDensity = t(F,W)` computes the right number.

  * `Graphon.const p`         : the constant graphon (Erdős–Rényi carrier).
  * `homDensity_bot`          : `t(⊥, W) = 1` (no edges ⇒ empty product ⇒ 1).
  * `homDensity_const`        : `t(F, const p) = p ^ e(F)` (Erdős–Rényi sanity).
  * `homDensity_edge`         : `t(K₂, W) = ∫∫ W` (edge density via `μ ⊗ μ`).
-/
import Graphons.Core.Basic

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The constant graphon -/

/-- The **constant graphon** with value `p ∈ [0,1]`: `W x y = p` for all `x, y`.
    Its homomorphism densities are `p ^ e(F)` (the Erdős–Rényi model). -/
def Graphon.const (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : Graphon Ω μ :=
  Graphon.mk' (μ := μ) (fun _ _ => p)
    (fun _ _ => rfl)
    measurable_const
    (fun _ _ => hp.1)
    (fun _ _ => hp.2)

@[simp] theorem Graphon.const_apply {p : ℝ} {hp : p ∈ Set.Icc (0:ℝ) 1} (x y : Ω) :
    (Graphon.const (μ := μ) p hp).toFun x y = p := rfl

/-- `edgeVal` of a constant graphon is the constant `p`, for any edge. -/
@[simp] theorem edgeVal_const {V : Type*} {p : ℝ} {hp : p ∈ Set.Icc (0:ℝ) 1}
    (x : V → Ω) (e : Sym2 V) :
    edgeVal (Graphon.const (μ := μ) p hp) x e = p := by
  induction e with
  | _ a b => rfl

/-! ### `t(⊥, W) = 1` -/

/-- The homomorphism density of the **empty graph** `⊥` into any graphon is `1`:
    `⊥` has no edges, so the integrand is the empty product `1`, and the integral of `1`
    against the product probability measure is `1`. -/
theorem homDensity_bot {V : Type*} [Fintype V] (W : Graphon Ω μ) :
    homDensity (⊥ : SimpleGraph V) W = 1 := by
  have h : homDensityIntegrand (⊥ : SimpleGraph V) W = fun _ => (1 : ℝ) := by
    funext x
    simp only [homDensityIntegrand]
    rw [Finset.prod_eq_one]
    intro e he
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot,
      Set.mem_empty_iff_false] at he
  unfold homDensity
  simp only [h]
  rw [integral_const, probReal_univ, smul_eq_mul, mul_one]

/-! ### Erdős–Rényi sanity: `t(F, const p) = p ^ e(F)` -/

/-- **Erdős–Rényi sanity check.** The homomorphism density of any finite graph `F` into the
    constant-`p` graphon is `p ^ e(F)`, where `e(F) = F.edgeFinset.card`. This is the single
    cleanest correctness check: the integrand is the *constant* `∏ e ∈ E(F), p = p ^ e(F)`,
    so the integral over the product probability measure is exactly that constant. -/
theorem homDensity_const {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    homDensity F (Graphon.const (μ := μ) p hp) = p ^ F.edgeFinset.card := by
  unfold homDensity homDensityIntegrand
  simp only [edgeVal_const, Finset.prod_const]
  rw [integral_const]
  simp

/-! ### Edge density: `t(K₂, W) = ∫∫ W` -/

/-- **Edge density.** The homomorphism density of the single-edge graph (`⊤` on `Fin 2`,
    i.e. `K₂`) into a graphon `W` is `∫∫ W dμ dμ`. We transport the integral over
    `piMeasure (Fin 2) μ` on `Fin 2 → Ω` to the product measure `μ ×ˢ μ` on `Ω × Ω` via the
    measure-preserving equivalence `MeasurableEquiv.piFinTwo`. -/
theorem homDensity_edge (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W = ∫ p : Ω × Ω, W.toFun p.1 p.2 ∂(μ.prod μ) := by
  -- `(⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0,1)}`, so the integrand is `W (x 0) (x 1)`.
  have hint : ∀ x : Fin 2 → Ω,
      homDensityIntegrand (⊤ : SimpleGraph (Fin 2)) W x = W.toFun (x 0) (x 1) := by
    intro x
    unfold homDensityIntegrand
    have hedge : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
      decide
    rw [hedge, Finset.prod_singleton]
    rfl
  unfold homDensity
  simp only [hint]
  -- transport along the measure-preserving equiv `(Fin 2 → Ω) ≃ᵐ Ω × Ω`.
  have hmp : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Ω))
      (piMeasure (Fin 2) μ) (μ.prod μ) := by
    have := (measurePreserving_piFinTwo (fun _ : Fin 2 => μ))
    simpa [piMeasure] using this
  rw [← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)]
  rfl

end Graphons
