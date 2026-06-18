/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier D, item D3 — **Sidorenko's inequality for `C₄`**
(Lovász, "Large Networks and Graph Limits", §2.1, Prop. 14.13-adjacent; the `C₄` case of
Sidorenko's conjecture, classical):

  t(C₄, W) ≥ t(K₂, W)⁴.

Proof chain (two Cauchy–Schwarz applications):
  1. `homDensity_C4` : `t(C₄, W) = ∫∫ coDeg²` — group the 4-cycle by its two diagonal
     vertices; the two 2-edge paths between them each integrate to `coDeg`.
  2. `∫∫ coDeg² ≥ (∫∫ coDeg)²` (variance on `μ ⊗ μ`), and `∫∫ coDeg = ∫ deg² = t(P₃,W)`.
  3. `t(P₃,W) ≥ t(K₂,W)²` (D1, `homDensity_cherry_ge`), so `t(C₄) ≥ t(P₃)² ≥ t(K₂)⁴`.

Tier-D significance: with Goodman (D2), the second named extremal consequence proved
through the public API only.
-/
import Graphons.Counting.CoDegree

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `[0,1]`-bound bookkeeping -/

private lemma mul_mem01 {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a * b ∧ a * b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩

private lemma W01 (W : Graphon Ω μ) (x y : Ω) : 0 ≤ W.toFun x y ∧ W.toFun x y ≤ 1 :=
  ⟨W.nonneg' x y, W.le_one' x y⟩

private lemma coDeg01 (W : Graphon Ω μ) (x y : Ω) : 0 ≤ W.coDeg x y ∧ W.coDeg x y ≤ 1 :=
  ⟨W.coDeg_nonneg x y, W.coDeg_le_one x y⟩

private lemma abs_le_one_of_mem01 {x : ℝ} (h : 0 ≤ x ∧ x ≤ 1) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [h.1], h.2⟩

/-! ### Integrability of the C₄ integrand and its partial integrals -/

section Integrability

variable (W : Graphon Ω μ)

private lemma ih4 :
    Integrable (fun p : Ω × Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.2.1 p.2.2.1
      * (W.toFun p.2.2.1 p.2.2.2 * W.toFun p.1 p.2.2.2)) (μ.prod (μ.prod (μ.prod μ))) := by
  have hx0 : Measurable fun p : Ω × Ω × Ω × Ω => p.1 := measurable_fst
  have hx1 : Measurable fun p : Ω × Ω × Ω × Ω => p.2.1 := measurable_fst.comp measurable_snd
  have hx2 : Measurable fun p : Ω × Ω × Ω × Ω => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hx3 : Measurable fun p : Ω × Ω × Ω × Ω => p.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  refine SymmKernel.integrable_of_bdd
    (((W.meas'.comp (hx0.prodMk hx1)).mul (W.meas'.comp (hx1.prodMk hx2))).mul
      ((W.meas'.comp (hx2.prodMk hx3)).mul (W.meas'.comp (hx0.prodMk hx3))))
    (C := 1) (fun p => abs_le_one_of_mem01
      (mul_mem01 (mul_mem01 (W01 W _ _) (W01 W _ _)) (mul_mem01 (W01 W _ _) (W01 W _ _))))

private lemma ih3 (x0 : Ω) :
    Integrable (fun q : Ω × Ω × Ω => W.toFun x0 q.1 * W.toFun q.1 q.2.1
      * (W.toFun q.2.1 q.2.2 * W.toFun x0 q.2.2)) (μ.prod (μ.prod μ)) := by
  have hx1 : Measurable fun q : Ω × Ω × Ω => q.1 := measurable_fst
  have hx2 : Measurable fun q : Ω × Ω × Ω => q.2.1 := measurable_fst.comp measurable_snd
  have hx3 : Measurable fun q : Ω × Ω × Ω => q.2.2 := measurable_snd.comp measurable_snd
  refine SymmKernel.integrable_of_bdd
    (((W.meas'.comp (measurable_const.prodMk hx1)).mul (W.meas'.comp (hx1.prodMk hx2))).mul
      ((W.meas'.comp (hx2.prodMk hx3)).mul (W.meas'.comp (measurable_const.prodMk hx3))))
    (C := 1) (fun q => abs_le_one_of_mem01
      (mul_mem01 (mul_mem01 (W01 W _ _) (W01 W _ _)) (mul_mem01 (W01 W _ _) (W01 W _ _))))

private lemma ih2 (x0 x1 : Ω) :
    Integrable (fun r : Ω × Ω => W.toFun x0 x1 * W.toFun x1 r.1
      * (W.toFun r.1 r.2 * W.toFun x0 r.2)) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd
    ((measurable_const.mul (W.meas'.comp (measurable_const.prodMk measurable_fst))).mul
      ((W.meas'.comp (measurable_fst.prodMk measurable_snd)).mul
        (W.meas'.comp (measurable_const.prodMk measurable_snd))))
    (C := 1) (fun r => abs_le_one_of_mem01
      (mul_mem01 (mul_mem01 (W01 W _ _) (W01 W _ _)) (mul_mem01 (W01 W _ _) (W01 W _ _))))

private lemma ihswap (x0 : Ω) :
    Integrable (Function.uncurry fun x1 x2 : Ω =>
      W.toFun x0 x1 * W.toFun x1 x2 * W.coDeg x2 x0) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd
    (((W.meas'.comp (measurable_const.prodMk measurable_fst)).mul
      (W.meas'.comp (measurable_fst.prodMk measurable_snd))).mul
      (W.measurable_coDeg.comp (measurable_snd.prodMk measurable_const)))
    (C := 1) (fun r => abs_le_one_of_mem01
      (mul_mem01 (mul_mem01 (W01 W _ _) (W01 W _ _)) (coDeg01 W _ _)))

private lemma ihsq :
    Integrable (Function.uncurry fun x0 x2 : Ω => (W.coDeg x0 x2) ^ 2) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd (W.measurable_coDeg.pow_const 2)
    (C := 1) (fun p => abs_le_one_of_mem01
      ⟨sq_nonneg _, pow_le_one₀ (W.coDeg_nonneg _ _) (W.coDeg_le_one _ _)⟩)

end Integrability

/-! ### The C₄ pair normal form on the quadruple product space -/

/-- Grouping the 4-cycle integrand by its diagonal `(x₀, x₂)`: integrating
    `W(x₀,x₁)W(x₁,x₂)·W(x₂,x₃)W(x₀,x₃)` over `Ω⁴` gives the second moment of the
    co-degree. -/
theorem integral_C4_pairform (W : Graphon Ω μ) :
    ∫ p : Ω × Ω × Ω × Ω, W.toFun p.1 p.2.1 * W.toFun p.2.1 p.2.2.1
        * (W.toFun p.2.2.1 p.2.2.2 * W.toFun p.1 p.2.2.2) ∂(μ.prod (μ.prod (μ.prod μ)))
      = ∫ p : Ω × Ω, (W.coDeg p.1 p.2) ^ 2 ∂(μ.prod μ) := by
  rw [integral_prod _ (ih4 W)]
  show (∫ x0 : Ω, ∫ q : Ω × Ω × Ω, W.toFun x0 q.1 * W.toFun q.1 q.2.1
      * (W.toFun q.2.1 q.2.2 * W.toFun x0 q.2.2) ∂(μ.prod (μ.prod μ)) ∂μ) = _
  have houter : ∀ x0 : Ω,
      (∫ q : Ω × Ω × Ω, W.toFun x0 q.1 * W.toFun q.1 q.2.1
        * (W.toFun q.2.1 q.2.2 * W.toFun x0 q.2.2) ∂(μ.prod (μ.prod μ)))
      = ∫ x2, (W.coDeg x0 x2) ^ 2 ∂μ := by
    intro x0
    rw [integral_prod _ (ih3 W x0)]
    show (∫ x1 : Ω, ∫ r : Ω × Ω, W.toFun x0 x1 * W.toFun x1 r.1
        * (W.toFun r.1 r.2 * W.toFun x0 r.2) ∂(μ.prod μ) ∂μ) = _
    -- innermost two integrals: `∫_{x2} ∫_{x3}` evaluates the second path to `coDeg x2 x0`
    have hB : ∀ x1 : Ω,
        (∫ r : Ω × Ω, W.toFun x0 x1 * W.toFun x1 r.1
          * (W.toFun r.1 r.2 * W.toFun x0 r.2) ∂(μ.prod μ))
        = ∫ x2, W.toFun x0 x1 * W.toFun x1 x2 * W.coDeg x2 x0 ∂μ := by
      intro x1
      rw [integral_prod _ (ih2 W x0 x1)]
      show (∫ x2 : Ω, ∫ x3 : Ω, W.toFun x0 x1 * W.toFun x1 x2
          * (W.toFun x2 x3 * W.toFun x0 x3) ∂μ ∂μ) = _
      have hC : ∀ x2 : Ω,
          (∫ x3, W.toFun x0 x1 * W.toFun x1 x2 * (W.toFun x2 x3 * W.toFun x0 x3) ∂μ)
          = W.toFun x0 x1 * W.toFun x1 x2 * W.coDeg x2 x0 := by
        intro x2
        rw [integral_const_mul]
        rfl
      rw [funext hC]
    rw [funext hB]
    -- swap `x1 ↔ x2`, then the first path evaluates to `coDeg x0 x2`
    rw [integral_integral_swap (ihswap W x0)]
    have hE : ∀ x2 : Ω,
        (∫ x1, W.toFun x0 x1 * W.toFun x1 x2 * W.coDeg x2 x0 ∂μ) = (W.coDeg x0 x2) ^ 2 := by
      intro x2
      rw [integral_mul_const]
      have h1 : (fun x1 => W.toFun x0 x1 * W.toFun x1 x2)
          = fun x1 => W.toFun x0 x1 * W.toFun x2 x1 := by
        funext x1
        rw [W.symm' x1 x2]
      rw [h1, show (∫ x1, W.toFun x0 x1 * W.toFun x2 x1 ∂μ) = W.coDeg x0 x2 from rfl,
        W.coDeg_symm x2 x0, sq]
    rw [funext hE]
  rw [funext houter]
  exact integral_integral (ihsq W)

/-! ### The C₄ density normal form -/

/-- **C₄ density** (`t(C₄, W) = ∫∫ coDeg²`): the homomorphism density of the 4-cycle is the
    second moment of the co-degree function. (`C₄ = SimpleGraph.cycleGraph 4`.) -/
theorem homDensity_C4 (W : Graphon Ω μ) :
    homDensity (SimpleGraph.cycleGraph 4) W
      = ∫ p : Ω × Ω, (W.coDeg p.1 p.2) ^ 2 ∂(μ.prod μ) := by
  -- `C₄.edgeFinset = {s(0,1), s(1,2), s(2,3), s(0,3)}`; integrand grouped by the diagonal.
  have hint : ∀ x : Fin 4 → Ω,
      homDensityIntegrand (SimpleGraph.cycleGraph 4) W x
        = W.toFun (x 0) (x 1) * W.toFun (x 1) (x 2)
          * (W.toFun (x 2) (x 3) * W.toFun (x 0) (x 3)) := by
    intro x
    unfold homDensityIntegrand
    have hedge : (SimpleGraph.cycleGraph 4).edgeFinset
        = {s(0, 1), s(1, 2), s(2, 3), s(0, 3)} := by decide
    rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [edgeVal, Sym2.lift_mk]
    ring
  unfold homDensity
  simp only [hint]
  -- transport along `(Fin 4 → Ω) ≃ᵐ Ω × Ω × Ω × Ω` (iterated `piFinSuccAbove`)
  set e3 : (Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0).trans
      ((MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Ω)))
      with he3
  set e : (Fin 4 → Ω) ≃ᵐ Ω × Ω × Ω × Ω :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => Ω) 0).trans
      ((MeasurableEquiv.refl Ω).prodCongr e3) with he
  have hmp1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0)
      (piMeasure (Fin 3) μ) (μ.prod (piMeasure (Fin 2) μ)) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0
    simpa [piMeasure] using this
  have hmp2 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Ω))
      (piMeasure (Fin 2) μ) (μ.prod μ) := by
    have := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
    simpa [piMeasure] using this
  have hmp3 : MeasurePreserving e3 (piMeasure (Fin 3) μ) (μ.prod (μ.prod μ)) :=
    (((MeasurePreserving.id μ).prod hmp2).comp hmp1 : _)
  have hmp4 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => Ω) 0)
      (piMeasure (Fin 4) μ) (μ.prod (piMeasure (Fin 3) μ)) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin 4 => μ) 0
    simpa [piMeasure] using this
  have hmp : MeasurePreserving e (piMeasure (Fin 4) μ) (μ.prod (μ.prod (μ.prod μ))) :=
    (((MeasurePreserving.id μ).prod hmp3).comp hmp4 : _)
  rw [← integral_C4_pairform]
  rw [← hmp.integral_comp'
    (fun p : Ω × Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.2.1 p.2.2.1
      * (W.toFun p.2.2.1 p.2.2.2 * W.toFun p.1 p.2.2.2))]
  have hex : ∀ x : Fin 4 → Ω, e x = (x 0, x 1, x 2, x 3) := by
    intro x
    simp only [he, he3, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  simp only [hex]

/-! ### D3 — Sidorenko's inequality for C₄ -/

/-- **Sidorenko for `C₄`** (D3): `t(C₄, W) ≥ t(K₂, W)⁴`. Two applications of
    Cauchy–Schwarz: `t(C₄) = ∫∫ coDeg² ≥ (∫∫ coDeg)² = t(P₃)² ≥ (t(K₂)²)²`. -/
theorem sidorenko_C4 (W : Graphon Ω μ) :
    (homDensity (⊤ : SimpleGraph (Fin 2)) W) ^ 4 ≤ homDensity (SimpleGraph.cycleGraph 4) W := by
  have hCS2 : (∫ p : Ω × Ω, W.coDeg p.1 p.2 ∂(μ.prod μ)) ^ 2
      ≤ ∫ p : Ω × Ω, (W.coDeg p.1 p.2) ^ 2 ∂(μ.prod μ) :=
    sq_integral_le_of_mem01 W.measurable_coDeg
      (fun p => W.coDeg_nonneg p.1 p.2) (fun p => W.coDeg_le_one p.1 p.2)
  have hcherry : homDensity cherry W = ∫ p : Ω × Ω, W.coDeg p.1 p.2 ∂(μ.prod μ) := by
    rw [homDensity_cherry, ← integral_coDeg]
  calc (homDensity (⊤ : SimpleGraph (Fin 2)) W) ^ 4
      = ((homDensity (⊤ : SimpleGraph (Fin 2)) W) ^ 2) ^ 2 := by ring
    _ ≤ (homDensity cherry W) ^ 2 := by
        have h := homDensity_cherry_ge W
        have h0 : (0:ℝ) ≤ (homDensity (⊤ : SimpleGraph (Fin 2)) W) ^ 2 := sq_nonneg _
        nlinarith
    _ = (∫ p : Ω × Ω, W.coDeg p.1 p.2 ∂(μ.prod μ)) ^ 2 := by rw [hcherry]
    _ ≤ ∫ p : Ω × Ω, (W.coDeg p.1 p.2) ^ 2 ∂(μ.prod μ) := hCS2
    _ = homDensity (SimpleGraph.cycleGraph 4) W := (homDensity_C4 W).symm

end Graphons
