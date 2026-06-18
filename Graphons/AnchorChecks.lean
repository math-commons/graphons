/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

VALIDATION.md Tier A — remaining anchor / sanity checks pinning down `homDensity = t(F,W)`.

  * `Graphon.mem_Icc`         : `W x y ∈ [0,1]` (graphon values lie in the unit interval).
  * `homDensity_triangle`     : `t(K₃, W) = ∫∫∫ W(x,y) W(x,z) W(y,z)` (triangle density).
-/
import Graphons.Core.Basic
import Graphons.Core.Examples

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Graphon range -/

/-- A graphon's values lie in the unit interval `[0,1]`. -/
theorem Graphon.mem_Icc (W : Graphon Ω μ) (x y : Ω) : W.toFun x y ∈ Set.Icc (0:ℝ) 1 :=
  ⟨W.nonneg' x y, W.le_one' x y⟩

/-! ### Triangle density: `t(K₃, W) = ∫∫∫ W(x,y) W(x,z) W(y,z)` -/

/-- **Triangle density.** The homomorphism density of the triangle (`⊤` on `Fin 3`, i.e. `K₃`)
    into a graphon `W` is `∫∫∫ W(x,y) W(x,z) W(y,z)`, integrated against the triple product
    measure `μ ⊗ (μ ⊗ μ)` on `Ω × Ω × Ω`. -/
theorem homDensity_triangle (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W
      = ∫ p : Ω × Ω × Ω, W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2 * W.toFun p.2.1 p.2.2
          ∂(μ.prod (μ.prod μ)) := by
  -- `(⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0,1), s(0,2), s(1,2)}`, so the integrand is
  -- `W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2)`.
  have hint : ∀ x : Fin 3 → Ω,
      homDensityIntegrand (⊤ : SimpleGraph (Fin 3)) W x
        = W.toFun (x 0) (x 1) * W.toFun (x 0) (x 2) * W.toFun (x 1) (x 2) := by
    intro x
    unfold homDensityIntegrand
    have hedge : (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
      decide
    rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    simp only [edgeVal, Sym2.lift_mk]
    ring
  unfold homDensity
  simp only [hint]
  -- Build the measure-preserving equiv `(Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω`, `x ↦ (x 0, x 1, x 2)`,
  -- by composing `piFinSuccAbove 0 : (Fin 3 → Ω) ≃ᵐ Ω × (Fin 2 → Ω)` with `id × piFinTwo`.
  set e : (Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0).trans
      ((MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Ω))) with he
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
  rw [← hmp.integral_comp'
    (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2 * W.toFun p.2.1 p.2.2)]
  -- `e x = (x 0, x 1, x 2)`, so the composed integrand matches the LHS integrand.
  have hex : ∀ x : Fin 3 → Ω, e x = (x 0, x 1, x 2) := by
    intro x
    simp only [he, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  simp only [hex]

end Graphons
