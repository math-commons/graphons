/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier D, item D0 (second half) — **co-degree infrastructure**
for Sidorenko-C₄ (D3).

  * `Graphon.coDeg`        : `coDeg_W(x,y) = ∫ W(x,u)·W(y,u) dμ(u)` (common-neighborhood mass).
  * `integral_coDeg`       : `∫∫ coDeg = ∫ deg²  (= t(P₃, W))`.
  * `sq_integral_le_of_mem01` : the reusable variance inequality `(∫f)² ≤ ∫f²` for
    `[0,1]`-valued measurable `f` on a probability space (generalizes `sq_integral_deg_le`).
-/
import Graphons.Counting.Degree

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The general variance inequality -/

/-- Second moment dominates the squared mean for any `[0,1]`-valued measurable function on a
    probability space: `(∫ f)² ≤ ∫ f²` (variance non-negativity). -/
theorem sq_integral_le_of_mem01 {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → ℝ} (hm : Measurable f)
    (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) :
    (∫ a, f a ∂ν) ^ 2 ≤ ∫ a, (f a) ^ 2 ∂ν := by
  have hLp : MemLp f 2 ν :=
    MemLp.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [h0 a], h1 a⟩)
  have h := ProbabilityTheory.variance_nonneg f ν
  rw [ProbabilityTheory.variance_eq_sub hLp] at h
  have hpow : (f ^ 2 : α → ℝ) = fun a => (f a) ^ 2 := by
    funext a
    simp [Pi.pow_apply]
  rw [hpow] at h
  linarith

/-! ### The co-degree function -/

/-- The **co-degree function** of a graphon: `coDeg_W(x,y) = ∫ W(x,u)·W(y,u) dμ(u)` — the
    (fractional) common-neighborhood mass of `x` and `y`. The C₄ density is its second
    moment (`homDensity_C4`, in `Extremal/Sidorenko.lean`). -/
noncomputable def Graphon.coDeg (W : Graphon Ω μ) (x y : Ω) : ℝ :=
  ∫ u, W.toFun x u * W.toFun y u ∂μ

theorem Graphon.coDeg_symm (W : Graphon Ω μ) (x y : Ω) : W.coDeg x y = W.coDeg y x := by
  unfold Graphon.coDeg
  congr 1
  funext u
  ring

theorem Graphon.coDeg_nonneg (W : Graphon Ω μ) (x y : Ω) : 0 ≤ W.coDeg x y :=
  integral_nonneg fun u => mul_nonneg (W.nonneg' x u) (W.nonneg' y u)

/-- The two-variable slice `u ↦ W(x,u)·W(y,u)` is integrable. -/
theorem Graphon.integrable_coDeg_slice (W : Graphon Ω μ) (x y : Ω) :
    Integrable (fun u => W.toFun x u * W.toFun y u) μ :=
  SymmKernel.integrable_of_bdd ((W.measurable_toFun_left x).mul (W.measurable_toFun_left y))
    (C := 1) (fun u => abs_le.2
      ⟨by nlinarith [W.nonneg' x u, W.nonneg' y u],
        mul_le_one₀ (W.le_one' x u) (W.nonneg' y u) (W.le_one' y u)⟩)

theorem Graphon.coDeg_le_one (W : Graphon Ω μ) (x y : Ω) : W.coDeg x y ≤ 1 := by
  calc W.coDeg x y ≤ ∫ _, (1 : ℝ) ∂μ :=
        integral_mono (W.integrable_coDeg_slice x y) (integrable_const 1)
          (fun u => mul_le_one₀ (W.le_one' x u) (W.nonneg' y u) (W.le_one' y u))
    _ = 1 := by simp

/-- The uncurried co-degree `(x,y) ↦ coDeg_W(x,y)` is measurable. -/
theorem Graphon.measurable_coDeg (W : Graphon Ω μ) :
    Measurable (fun p : Ω × Ω => W.coDeg p.1 p.2) := by
  have hm : StronglyMeasurable (fun q : (Ω × Ω) × Ω => W.toFun q.1.1 q.2 * W.toFun q.1.2 q.2) :=
    ((W.meas'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (W.meas'.comp ((measurable_snd.comp measurable_fst).prodMk
        measurable_snd))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- `∫∫ coDeg = ∫ deg²` — integrating the co-degree over both arguments gives the cherry
    second moment (so `∫∫ coDeg = t(P₃, W)` via `homDensity_cherry`). -/
theorem integral_coDeg (W : Graphon Ω μ) :
    ∫ p : Ω × Ω, W.coDeg p.1 p.2 ∂(μ.prod μ) = ∫ u, (W.deg u) ^ 2 ∂μ := by
  -- swap the order of integration: `∫_{(x,y)} ∫_u = ∫_u ∫_{(x,y)}`
  have hint : Integrable
      (Function.uncurry fun (p : Ω × Ω) (u : Ω) => W.toFun p.1 u * W.toFun p.2 u)
      ((μ.prod μ).prod μ) := by
    refine SymmKernel.integrable_of_bdd ?_ (C := 1) ?_
    · exact (W.meas'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        (W.meas'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    · intro q
      show |W.toFun q.1.1 q.2 * W.toFun q.1.2 q.2| ≤ 1
      refine abs_le.2 ⟨?_, mul_le_one₀ (W.le_one' q.1.1 q.2) (W.nonneg' q.1.2 q.2)
        (W.le_one' q.1.2 q.2)⟩
      nlinarith [W.nonneg' q.1.1 q.2, W.nonneg' q.1.2 q.2]
  have hswap := integral_integral_swap
    (f := fun (p : Ω × Ω) (u : Ω) => W.toFun p.1 u * W.toFun p.2 u) hint
  -- LHS of `hswap` is `∫∫ coDeg` by definition
  rw [show (fun p : Ω × Ω => W.coDeg p.1 p.2)
      = fun p : Ω × Ω => ∫ u, W.toFun p.1 u * W.toFun p.2 u ∂μ from rfl]
  rw [hswap]
  -- inner integral at fixed `u` factors as `deg u * deg u`
  have hinner : ∀ u : Ω,
      (∫ p : Ω × Ω, W.toFun p.1 u * W.toFun p.2 u ∂(μ.prod μ)) = (W.deg u) ^ 2 := by
    intro u
    rw [integral_prod_mul (f := fun x => W.toFun x u) (g := fun y => W.toFun y u)]
    have hslice : (fun x => W.toFun x u) = W.toFun u := by
      funext x
      exact W.symm' x u
    rw [hslice, sq]
    rfl
  simp only [hinner]

end Graphons
