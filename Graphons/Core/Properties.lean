/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG targets (random-fields roadmap, layer L9 — dense graph limits):
  C11303 "Cut distance δ□" (induces the equivalence on graphon space),
  C12954/C13065 "Homomorphism density t(F,W)" (monotonicity in W).
  Sources: Lovász, "Large Networks and Graph Limits" (2012).

Structural properties of graphons:
  * `GraphonEquiv`: the equivalence underlying graphon space, `δ□(U, W) = 0`
    (reflexive and symmetric here; transitivity awaits `cutDist_triangle`).
  * `homDensity_mono`: homomorphism density is monotone in the (pointwise) kernel order.
-/
import Graphons.CutMetric.CutDist

open MeasureTheory

namespace Graphons

/-! ### Graphon equivalence

Two graphons (possibly on different carriers) are **equivalent** when their cut distance is `0`.
This is the equivalence relation whose quotient is *graphon space*. -/

section Equiv

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- Two graphons are **equivalent** when their cut distance is zero. (Cross-carrier OK.) -/
def GraphonEquiv (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : Prop := cutDist U W = 0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `GraphonEquiv` is reflexive: every graphon is equivalent to itself. -/
theorem graphonEquiv_refl (U : Graphon Ω μ) : GraphonEquiv U U :=
  cutDist_self_eq_zero U

/-- `GraphonEquiv` is symmetric. -/
theorem graphonEquiv_symm {U : Graphon Ω₁ μ₁} {W : Graphon Ω₂ μ₂}
    (h : GraphonEquiv U W) : GraphonEquiv W U := by
  rw [GraphonEquiv, cutDist_comm]; exact h

-- transitivity (`graphonEquiv_trans`) lives in `Graphons.Space.GraphonSpace`, where it is derived from
-- the now-proved `cutDist_triangle` (Gluing Lemma) — completing the setoid for graphon space.

end Equiv

/-! ### Monotonicity of homomorphism density

If `U ≤ W` pointwise (same carrier), then `t(F, U) ≤ t(F, W)` for every finite simple graph `F`:
each edge factor is nonnegative and monotone, so the product (hence the integrand) is monotone,
and `integral_mono` lifts this to the densities. -/

section Mono

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Pointwise monotonicity of the edge value in the (pointwise) kernel order. -/
theorem edgeVal_mono {V : Type*} {U W : Graphon Ω μ} (h : ∀ x y, U.toFun x y ≤ W.toFun x y)
    (x : V → Ω) (e : Sym2 V) : edgeVal U x e ≤ edgeVal W x e := by
  induction e with
  | _ a b => exact h (x a) (x b)

/-- The homomorphism-density integrand is monotone in the kernel. -/
theorem homDensityIntegrand_mono {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    {U W : Graphon Ω μ} (h : ∀ x y, U.toFun x y ≤ W.toFun x y) (x : V → Ω) :
    homDensityIntegrand F U x ≤ homDensityIntegrand F W x :=
  Finset.prod_le_prod
    (fun e _ => Graphon.edgeVal_nonneg U x e)
    (fun e _ => edgeVal_mono h x e)

/-- **Monotonicity of homomorphism density.** If `U ≤ W` pointwise, then `t(F, U) ≤ t(F, W)`. -/
theorem homDensity_mono {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    {U W : Graphon Ω μ} (h : ∀ x y, U.toFun x y ≤ W.toFun x y) :
    homDensity F U ≤ homDensity F W := by
  letI : MeasurableSpace V := ⊤
  refine integral_mono (Graphon.integrable_homDensityIntegrand F U)
    (Graphon.integrable_homDensityIntegrand F W) ?_
  exact fun x => homDensityIntegrand_mono F h x

end Mono

end Graphons
