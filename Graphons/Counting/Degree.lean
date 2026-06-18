/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier D, items D0/D1 — degree infrastructure + the Cauchy–Schwarz
warm-up. (Lovász, "Large Networks and Graph Limits", §7.1; Goodman 1959 uses these.)

  * `Graphon.deg`            : the degree function `deg_W(x) = ∫ W(x,y) dμ(y)`.
  * `integral_deg`           : `∫ deg = t(K₂, W)` (edge density).
  * `cherry`                 : the 2-edge path `P₃` on `Fin 3`, centered at `0`.
  * `homDensity_cherry`      : `t(P₃, W) = ∫ deg²` — the cherry normal form.
  * `homDensity_cherry_ge`   : `t(P₃, W) ≥ t(K₂, W)²` (Cauchy–Schwarz / variance ≥ 0).

These are the first Tier-D results: consequences of the definitions that were never design
targets, certifying the `homDensity` encoding against classical extremal graph theory.
-/
import Graphons.Core.Examples

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The degree function -/

/-- The **degree function** of a graphon: `deg_W(x) = ∫ W(x,y) dμ(y)` — the "fractional
    neighborhood size" of the point `x`. -/
noncomputable def Graphon.deg (W : Graphon Ω μ) (x : Ω) : ℝ := ∫ y, W.toFun x y ∂μ

/-- One-variable slice of a graphon is measurable. -/
theorem Graphon.measurable_toFun_left (W : Graphon Ω μ) (x : Ω) :
    Measurable (W.toFun x) :=
  W.meas'.comp measurable_prodMk_left

/-- One-variable slice of a graphon is integrable. -/
theorem Graphon.integrable_toFun_left (W : Graphon Ω μ) (x : Ω) :
    Integrable (W.toFun x) μ :=
  SymmKernel.integrable_of_bdd (W.measurable_toFun_left x) (C := 1)
    (fun y => abs_le.2 ⟨by linarith [W.nonneg' x y], W.le_one' x y⟩)

theorem Graphon.deg_nonneg (W : Graphon Ω μ) (x : Ω) : 0 ≤ W.deg x :=
  integral_nonneg (fun y => W.nonneg' x y)

theorem Graphon.deg_le_one (W : Graphon Ω μ) (x : Ω) : W.deg x ≤ 1 := by
  calc W.deg x ≤ ∫ _, (1 : ℝ) ∂μ :=
        integral_mono (W.integrable_toFun_left x) (integrable_const 1) (fun y => W.le_one' x y)
    _ = 1 := by simp

/-- The degree function is measurable. -/
theorem Graphon.measurable_deg (W : Graphon Ω μ) : Measurable W.deg :=
  (W.meas'.stronglyMeasurable.integral_prod_right).measurable

/-- The degree function is square-integrable (it is bounded on a probability space). -/
theorem Graphon.memLp_deg (W : Graphon Ω μ) : MemLp W.deg 2 μ :=
  MemLp.of_bound W.measurable_deg.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [W.deg_nonneg x], W.deg_le_one x⟩)

/-- **The degree integrates to the edge density**: `∫ deg_W dμ = t(K₂, W)`. -/
theorem integral_deg (W : Graphon Ω μ) :
    ∫ x, W.deg x ∂μ = homDensity (⊤ : SimpleGraph (Fin 2)) W := by
  rw [homDensity_edge]
  exact integral_integral W.integrable_uncurry

/-! ### The cherry `P₃` (2-edge path) and its normal form `t(P₃, W) = ∫ deg²` -/

/-- The **cherry** (the 2-edge path `P₃`): the graph on `Fin 3` with edges `{0,1}` and `{0,2}`
    (center `0`). Its homomorphism density is the second moment of the degree function. -/
def cherry : SimpleGraph (Fin 3) where
  Adj a b := (a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0)
  symm := by intro a b h; tauto
  loopless := ⟨fun a h => by tauto⟩

instance : DecidableRel cherry.Adj := fun a b =>
  inferInstanceAs (Decidable ((a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0)))

/-- The product-space normal form of the cherry integrand: integrating
    `W(x,y)·W(x,z)` over `Ω³` gives the second moment of the degree. -/
theorem integral_cherry_left (W : Graphon Ω μ) :
    ∫ p : Ω × Ω × Ω, W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2 ∂(μ.prod (μ.prod μ))
      = ∫ x, (W.deg x) ^ 2 ∂μ := by
  have hmeas : Measurable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2) := by
    have h1 : Measurable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1) :=
      W.meas'.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.2) :=
      W.meas'.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact h1.mul h2
  have hint : Integrable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2)
      ((μ.prod (μ.prod μ))) := by
    refine SymmKernel.integrable_of_bdd hmeas (C := 1) (fun p => ?_)
    rw [abs_le]
    constructor
    · nlinarith [W.nonneg' p.1 p.2.1, W.nonneg' p.1 p.2.2]
    · nlinarith [W.nonneg' p.1 p.2.1, W.nonneg' p.1 p.2.2,
        W.le_one' p.1 p.2.1, W.le_one' p.1 p.2.2]
  rw [integral_prod _ hint]
  have hinner : ∀ x : Ω,
      (∫ q : Ω × Ω, W.toFun x q.1 * W.toFun x q.2 ∂(μ.prod μ)) = (W.deg x) ^ 2 := by
    intro x
    rw [integral_prod_mul (f := W.toFun x) (g := W.toFun x), sq]
    rfl
  simp only [hinner]

/-- **Cherry density** (`t(P₃, W) = ∫ deg²`): the homomorphism density of the 2-edge path
    is the second moment of the degree function. -/
theorem homDensity_cherry (W : Graphon Ω μ) :
    homDensity cherry W = ∫ x, (W.deg x) ^ 2 ∂μ := by
  -- `cherry.edgeFinset = {s(0,1), s(0,2)}`, so the integrand is `W (x 0) (x 1) * W (x 0) (x 2)`.
  have hint : ∀ x : Fin 3 → Ω,
      homDensityIntegrand cherry W x = W.toFun (x 0) (x 1) * W.toFun (x 0) (x 2) := by
    intro x
    unfold homDensityIntegrand
    have hedge : cherry.edgeFinset = {s(0, 1), s(0, 2)} := by decide
    rw [hedge, Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [edgeVal, Sym2.lift_mk]
  unfold homDensity
  simp only [hint]
  -- Transport along the measure-preserving equiv `(Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω` (as in
  -- `homDensity_triangle`), then evaluate via `integral_cherry_left`.
  set e : (Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0).trans
      ((MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Ω)))
      with he
  have hmp1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0)
      (piMeasure (Fin 3) μ) (μ.prod (piMeasure (Fin 2) μ)) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0
    simpa [piMeasure] using this
  have hmp2 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Ω))
      (piMeasure (Fin 2) μ) (μ.prod μ) := by
    have := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
    simpa [piMeasure] using this
  have hmpr : MeasurePreserving
      (Prod.map (id : Ω → Ω) (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Ω)))
      (μ.prod (piMeasure (Fin 2) μ)) (μ.prod (μ.prod μ)) :=
    (MeasurePreserving.id μ).prod hmp2
  have hmp : MeasurePreserving e (piMeasure (Fin 3) μ) (μ.prod (μ.prod μ)) :=
    hmpr.comp hmp1
  rw [← integral_cherry_left]
  rw [← hmp.integral_comp'
    (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2)]
  have hex : ∀ x : Fin 3 → Ω, e x = (x 0, x 1, x 2) := by
    intro x
    simp only [he, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  simp only [hex]

/-! ### D1: `t(P₃, W) ≥ t(K₂, W)²` (Cauchy–Schwarz / Jensen) -/

/-- Second moment dominates the squared mean (variance non-negativity, specialized to the
    degree function): `(∫ deg)² ≤ ∫ deg²`. -/
theorem sq_integral_deg_le (W : Graphon Ω μ) :
    (∫ x, W.deg x ∂μ) ^ 2 ≤ ∫ x, (W.deg x) ^ 2 ∂μ := by
  have h := ProbabilityTheory.variance_nonneg W.deg μ
  rw [ProbabilityTheory.variance_eq_sub W.memLp_deg] at h
  have hpow : (W.deg ^ 2 : Ω → ℝ) = fun x => (W.deg x) ^ 2 := by
    funext x
    simp [Pi.pow_apply]
  rw [hpow] at h
  linarith

/-- **D1 — the cherry bound** (Cauchy–Schwarz warm-up): `t(P₃, W) ≥ t(K₂, W)²`. The first
    Tier-D consequence: an extremal inequality that was never a design target. -/
theorem homDensity_cherry_ge (W : Graphon Ω μ) :
    (homDensity (⊤ : SimpleGraph (Fin 2)) W) ^ 2 ≤ homDensity cherry W := by
  rw [homDensity_cherry, ← integral_deg]
  exact sq_integral_deg_le W

end Graphons
