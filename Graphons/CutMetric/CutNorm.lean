/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits):
  C11257 "Cut norm" (def). Sources: Lovász, "Large Networks and Graph Limits" (2012);
  Borgs–Chayes–Lovász–Sós–Vesztergombi (2007).

The **cut norm** of a `SymmKernel` `W` over an abstract probability space `(Ω, μ)`, in the
*test-function* form (DESIGN.md §8):
  ‖W‖□ = sup_{u,v test fns} |∫∫ W(x,y) u(x) v(y) dμ dμ|,
where a *test function* is a measurable `[0,1]`-valued function `Ω → ℝ`.

This is a genuine `⨆` over the reals, so we must avoid the junk-`sSup`-`= 0` trap: the family is
bounded above by `W.bound` (each integrand `|∫ W·u·v| ≤ ∫|W| ≤ W.bound`, using that `μ ×ˢ μ` is a
probability measure and `|u|,|v| ≤ 1`), and the index `Ω → ℝ` is nonempty (the `0` function is a
test function).  All order facts go through the conditionally-complete-lattice API
(`ciSup_le'`, `le_ciSup`, `BddAbove`).
-/
import Graphons.Core.Basic

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A **test function**: a measurable `[0,1]`-valued function `Ω → ℝ`. -/
def IsTestFun (u : Ω → ℝ) : Prop := Measurable u ∧ ∀ x, u x ∈ Set.Icc (0 : ℝ) 1

/-- The constant `0` function is a test function (so the index type is nonempty). -/
theorem isTestFun_zero : IsTestFun (fun _ : Ω => (0 : ℝ)) :=
  ⟨measurable_const, fun _ => ⟨le_refl 0, zero_le_one⟩⟩

theorem IsTestFun.measurable {u : Ω → ℝ} (hu : IsTestFun u) : Measurable u := hu.1

theorem IsTestFun.nonneg {u : Ω → ℝ} (hu : IsTestFun u) (x : Ω) : 0 ≤ u x := (hu.2 x).1

theorem IsTestFun.le_one {u : Ω → ℝ} (hu : IsTestFun u) (x : Ω) : u x ≤ 1 := (hu.2 x).2

theorem IsTestFun.abs_le_one {u : Ω → ℝ} (hu : IsTestFun u) (x : Ω) : |u x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hu.nonneg x], hu.le_one x⟩

/-- The integrand `(x,y) ↦ W x y · u x · v y` as a function on `Ω × Ω`. -/
private def integrandFun (W : SymmKernel Ω μ) (u v : Ω → ℝ) (p : Ω × Ω) : ℝ :=
  W.toFun p.1 p.2 * u p.1 * v p.2

/-- The **cut norm** of a symmetric kernel `W` (test-function form):
    `‖W‖□ = sup_{u,v test} |∫∫ W·u·v|`. -/
noncomputable def cutNorm (W : SymmKernel Ω μ) : ℝ :=
  ⨆ (u : Ω → ℝ) (v : Ω → ℝ) (_ : IsTestFun u) (_ : IsTestFun v),
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|

section Bounds

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The integrand `(x,y) ↦ W x y · u x · v y` is measurable. -/
theorem measurable_integrand (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : Measurable u)
    (hv : Measurable v) :
    Measurable (fun p : Ω × Ω => W.toFun p.1 p.2 * u p.1 * v p.2) :=
  (W.meas'.mul (hu.comp measurable_fst)).mul (hv.comp measurable_snd)

omit [IsProbabilityMeasure μ] in
/-- Pointwise: `|W x y · u x · v y| ≤ W.bound`, using `|W| ≤ bound` and `|u|,|v| ≤ 1`. -/
theorem abs_integrand_le_bound (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) (x y : Ω) : |W.toFun x y * u x * v y| ≤ W.bound := by
  calc |W.toFun x y * u x * v y|
      = |W.toFun x y| * |u x| * |v y| := by rw [abs_mul, abs_mul]
    _ ≤ W.bound * 1 * 1 :=
        mul_le_mul (mul_le_mul (W.abs_le_bound x y) (hu.abs_le_one x) (abs_nonneg _)
            W.bound_nonneg) (hv.abs_le_one y) (abs_nonneg _)
          (mul_nonneg W.bound_nonneg zero_le_one)
    _ = W.bound := by ring

/-- The integrand is integrable against `μ ×ˢ μ` (it is bounded by `W.bound`). -/
theorem integrable_integrand (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) :
    Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * u p.1 * v p.2) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd (measurable_integrand W hu.measurable hv.measurable)
    (C := W.bound) (fun p => ?_)
  obtain ⟨x, y⟩ := p
  exact abs_integrand_le_bound W hu hv x y

/-- Each integrand value `|∫ W·u·v|` is bounded by `W.bound`. -/
theorem abs_integral_le_bound (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) :
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| ≤ W.bound := by
  calc |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
      ≤ ∫ p, |W.toFun p.1 p.2 * u p.1 * v p.2| ∂(μ.prod μ) := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ.prod μ)
            (fun p => W.toFun p.1 p.2 * u p.1 * v p.2)
    _ ≤ ∫ _, W.bound ∂(μ.prod μ) := by
        refine integral_mono (integrable_integrand W hu hv).abs (integrable_const _) (fun p => ?_)
        obtain ⟨x, y⟩ := p
        exact abs_integrand_le_bound W hu hv x y
    _ = W.bound := by simp

/-- For a *fixed* `u`, the family `⨆ (_:IsTestFun u) (_:IsTestFun v), |∫ W·u·v|` (as a function
    of `v`) is bounded above by `W.bound`. This is the reusable inner-bound building block:
    `ciSup_le'` peels each binder and the `Prop` binders collapse to `0 ≤ W.bound` when false. -/
theorem inner_le_bound (W : SymmKernel Ω μ) (u v : Ω → ℝ) :
    (⨆ (_ : IsTestFun u) (_ : IsTestFun v),
      |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|) ≤ W.bound := by
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · simp only [ciSup_pos hu, ciSup_pos hv]
      exact abs_integral_le_bound W hu hv
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using W.bound_nonneg
  · rw [ciSup_neg hu]; simpa using W.bound_nonneg

/-- For a fixed `u`, the family over `v` is `BddAbove` (witness `W.bound`). -/
theorem bddAbove_inner (W : SymmKernel Ω μ) (u : Ω → ℝ) :
    BddAbove (Set.range (fun v : Ω → ℝ =>
      ⨆ (_ : IsTestFun u) (_ : IsTestFun v),
        |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|)) := by
  refine ⟨W.bound, ?_⟩
  rintro a ⟨v, rfl⟩
  exact inner_le_bound W u v

/-- The outer family (over `u`) is `BddAbove` (witness `W.bound`). -/
theorem bddAbove_cutNorm_family (W : SymmKernel Ω μ) :
    BddAbove (Set.range (fun u : Ω → ℝ =>
      ⨆ (v : Ω → ℝ) (_ : IsTestFun u) (_ : IsTestFun v),
        |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|)) := by
  refine ⟨W.bound, ?_⟩
  rintro a ⟨u, rfl⟩
  exact ciSup_le fun v => inner_le_bound W u v

/-- The family defining `cutNorm` is bounded above by `W.bound`; hence `cutNorm W ≤ W.bound`. -/
theorem cutNorm_le_bound (W : SymmKernel Ω μ) : cutNorm W ≤ W.bound := by
  rw [cutNorm]
  exact ciSup_le fun u => ciSup_le fun v => inner_le_bound W u v

/-- A single test-function pair value is `≤ cutNorm W` (uses `BddAbove`). -/
theorem le_cutNorm (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u) (hv : IsTestFun v) :
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| ≤ cutNorm W := by
  show _ ≤ ⨆ (u : Ω → ℝ) (v : Ω → ℝ) (_ : IsTestFun u) (_ : IsTestFun v),
      |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
  calc |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
      = ⨆ (_ : IsTestFun u) (_ : IsTestFun v),
          |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| := by
        rw [ciSup_pos hu, ciSup_pos hv]
    _ ≤ ⨆ (v : Ω → ℝ) (_ : IsTestFun u) (_ : IsTestFun v),
          |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| :=
        le_ciSup_of_le (bddAbove_inner W u) v (le_refl _)
    _ ≤ _ := le_ciSup (bddAbove_cutNorm_family W) u

/-- `cutNorm W ≥ 0`: the family contains `0` (take `u = v = 0`). -/
theorem cutNorm_nonneg (W : SymmKernel Ω μ) : 0 ≤ cutNorm W := by
  have hzero : IsTestFun (fun _ : Ω => (0 : ℝ)) := isTestFun_zero
  -- The value at `u = v = 0` is `0`, and it is ≤ cutNorm W since the family is BddAbove.
  refine le_trans (le_of_eq ?_) (le_cutNorm W hzero hzero)
  simp

/-! ### Scalar multiplication -/

omit [IsProbabilityMeasure μ] in
/-- The integrand of `c • W` is `c` times that of `W`, pointwise. -/
theorem smul_integrand (c : ℝ) (W : SymmKernel Ω μ) (u v : Ω → ℝ) (p : Ω × Ω) :
    (c • W).toFun p.1 p.2 * u p.1 * v p.2 = c * (W.toFun p.1 p.2 * u p.1 * v p.2) := by
  simp only [SymmKernel.smul_apply]; ring

/-- One direction of `cutNorm_smul`: `cutNorm (c • W) ≤ |c| * cutNorm W`. -/
theorem cutNorm_smul_le (c : ℝ) (W : SymmKernel Ω μ) :
    cutNorm (c • W) ≤ |c| * cutNorm W := by
  rw [cutNorm]
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      -- value at (u,v) for `c•W` equals `|c| * value for W`, which is ≤ |c| * cutNorm W.
      have hI : ∫ p, (c • W).toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)
          = c * ∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun p => smul_integrand c W u v p)
      rw [hI, abs_mul]
      exact mul_le_mul_of_nonneg_left (le_cutNorm W hu hv) (abs_nonneg c)
    · rw [ciSup_pos hu, ciSup_neg hv]
      exact le_trans (by simp) (mul_nonneg (abs_nonneg c) (cutNorm_nonneg W))
  · rw [ciSup_neg hu]
    exact le_trans (by simp) (mul_nonneg (abs_nonneg c) (cutNorm_nonneg W))

/-- **Scalar homogeneity** of the cut norm: `cutNorm (c • W) = |c| * cutNorm W`. -/
theorem cutNorm_smul (c : ℝ) (W : SymmKernel Ω μ) :
    cutNorm (c • W) = |c| * cutNorm W := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_smul, abs_zero, zero_mul]
    -- cutNorm 0 = 0: it is nonneg and ≤ bound, but more directly its family is all 0.
    refine le_antisymm ?_ (cutNorm_nonneg _)
    rw [cutNorm]
    refine ciSup_le fun u => ciSup_le fun v => ?_
    by_cases hu : IsTestFun u <;> by_cases hv : IsTestFun v <;>
      simp [ciSup_neg, hu, hv]
  · refine le_antisymm (cutNorm_smul_le c W) ?_
    -- Reverse: |c| * cutNorm W ≤ cutNorm (c • W).
    have key : cutNorm W ≤ |c|⁻¹ * cutNorm (c • W) := by
      have h := cutNorm_smul_le c⁻¹ (c • W)
      rwa [inv_smul_smul₀ hc, abs_inv] at h
    have hcabs : (0 : ℝ) < |c| := abs_pos.2 hc
    calc |c| * cutNorm W ≤ |c| * (|c|⁻¹ * cutNorm (c • W)) :=
          mul_le_mul_of_nonneg_left key (le_of_lt hcabs)
      _ = cutNorm (c • W) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcabs), one_mul]

/-- `cutNorm 0 = 0` (every integrand is `0`). Follows from `cutNorm_smul` with `c = 0`. -/
theorem cutNorm_zero : cutNorm (0 : SymmKernel Ω μ) = 0 := by
  have h := cutNorm_smul (0 : ℝ) (0 : SymmKernel Ω μ)
  simpa using h

/-- `cutNorm (-W) = cutNorm W`. Follows from `cutNorm_smul` with `c = -1`. -/
theorem cutNorm_neg (W : SymmKernel Ω μ) : cutNorm (-W) = cutNorm W := by
  have h := cutNorm_smul (-1 : ℝ) W
  simpa using h

/-! ### Subadditivity (triangle inequality) -/

/-- **Subadditivity** of the cut norm: `cutNorm (U + W) ≤ cutNorm U + cutNorm W`. -/
theorem cutNorm_add_le (U W : SymmKernel Ω μ) :
    cutNorm (U + W) ≤ cutNorm U + cutNorm W := by
  rw [cutNorm]
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      -- integrand of U+W splits; integral splits; triangle on |·|.
      have hsplit : ∫ p, (U + W).toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)
          = (∫ p, U.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ))
            + ∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ) := by
        rw [← integral_add (integrable_integrand U hu hv) (integrable_integrand W hu hv)]
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        simp only [SymmKernel.add_apply]; ring
      rw [hsplit]
      exact le_trans (abs_add_le _ _)
        (add_le_add (le_cutNorm U hu hv) (le_cutNorm W hu hv))
    · rw [ciSup_pos hu, ciSup_neg hv]
      exact le_trans (by simp) (add_nonneg (cutNorm_nonneg U) (cutNorm_nonneg W))
  · rw [ciSup_neg hu]
    exact le_trans (by simp) (add_nonneg (cutNorm_nonneg U) (cutNorm_nonneg W))

end Bounds

end Graphons
