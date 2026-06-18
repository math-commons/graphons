/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits), VALIDATION.md Tier B, C11258:
  **Set-form cut norm equivalence.** The test-function cut norm `cutNorm` (DESIGN.md §8) equals the
  textbook supremum over measurable rectangles:
    ‖W‖□ = sup_{S,T measurable} |∫∫ W(x,y) 𝟙_S(x) 𝟙_T(y) dμ dμ|.
  Sources: Lovász, "Large Networks and Graph Limits" (2012); Borgs–Chayes–Lovász–Sós–Vesztergombi
  (2007).

The proof is `le_antisymm`:
* `cutNormSet ≤ cutNorm` (easy): indicators of measurable sets are test functions.
* `cutNorm ≤ cutNormSet` (the content): a pointwise *bang-bang* argument. For fixed test `u, v`,
  Fubini turns `∫∫ W·u·v` into `∫ x, g x · u x` with `g x = ∫ y, W x y · v y`. Pointwise, for
  `u x ∈ [0,1]`, with `S := {x | 0 ≤ g x}` we have `g·𝟙_{Sᶜ} ≤ g·u ≤ g·𝟙_S`, so
  `|∫ g·u| ≤ max |∫ g·𝟙_S| |∫ g·𝟙_{Sᶜ}|`. Each of these is `|∫∫ W·𝟙_·v|` (Fubini back), and the same
  argument in the `v`-slot lands at `|∫∫ W·𝟙_S·𝟙_T| ≤ cutNormSet`. NO extreme-point theorem.
-/
import Graphons.CutMetric.CutNorm

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **set-form cut norm**: supremum over measurable rectangles `S × T` of
    `|∫∫ W·𝟙_S·𝟙_T|`. The indicator `Set.indicator S 1` is the `{0,1}`-valued indicator. -/
noncomputable def cutNormSet (W : SymmKernel Ω μ) : ℝ :=
  ⨆ (S : Set Ω) (T : Set Ω) (_ : MeasurableSet S) (_ : MeasurableSet T),
    |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
      * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)|

/-- The indicator `Set.indicator S 1` of a measurable set is a test function:
    measurable, with values in `{0,1} ⊆ [0,1]`. -/
theorem isTestFun_indicator {S : Set Ω} (hS : MeasurableSet S) :
    IsTestFun (Set.indicator S (1 : Ω → ℝ)) := by
  refine ⟨(measurable_const : Measurable (1 : Ω → ℝ)).indicator hS, fun x => ?_⟩
  classical
  rw [Set.indicator_apply]
  by_cases hx : x ∈ S <;> simp [hx]

/-! ### Bang-bang reduction (1D)

For a fixed measurable function `g` and a test function `u`, replacing `u` by the indicator of
`S := {x | 0 ≤ g x}` (or its complement) does not decrease `|∫ g·u|`. This is the pointwise
"bang-bang" step that drives both extremization slots. -/

/-- Pointwise bang-bang bound: for `u x ∈ [0,1]` and `S := {x | 0 ≤ g x}`,
    `g x · 𝟙_{Sᶜ}(x) ≤ g x · u x ≤ g x · 𝟙_S(x)`. -/
theorem bangbang_pointwise {g u : Ω → ℝ} (hu : IsTestFun u) (x : Ω) :
    g x * (Set.indicator {x | 0 ≤ g x}ᶜ (1 : Ω → ℝ) x) ≤ g x * u x ∧
    g x * u x ≤ g x * (Set.indicator {x | 0 ≤ g x} (1 : Ω → ℝ) x) := by
  classical
  by_cases hx : 0 ≤ g x
  · -- `x ∈ S`, `x ∉ Sᶜ`: indicator_S = 1, indicator_Sᶜ = 0.
    have hS : x ∈ {x | 0 ≤ g x} := hx
    have hSc : x ∉ {x | 0 ≤ g x}ᶜ := by simpa using hx
    rw [Set.indicator_of_mem hS, Set.indicator_of_notMem hSc]
    constructor
    · simp; exact mul_nonneg hx (hu.nonneg x)
    · simp; exact mul_le_of_le_one_right hx (hu.le_one x)
  · -- `x ∉ S`, `x ∈ Sᶜ`: indicator_S = 0, indicator_Sᶜ = 1.  Here `g x < 0`.
    have hgneg : g x < 0 := lt_of_not_ge hx
    have hS : x ∉ {x | 0 ≤ g x} := hx
    have hSc : x ∈ {x | 0 ≤ g x}ᶜ := hx
    rw [Set.indicator_of_notMem hS, Set.indicator_of_mem hSc]
    constructor
    · simp; exact le_mul_of_le_one_right (le_of_lt hgneg) (hu.le_one x)
    · simp; exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hgneg) (hu.nonneg x)

/-- `g · u` is integrable when `g` is integrable and `u` is a test function (bounded by 1). -/
theorem integrable_mul_testFun {g u : Ω → ℝ} (hg : Integrable g μ) (hu : IsTestFun u) :
    Integrable (fun x => g x * u x) μ := by
  have h : Integrable (fun x => u x * g x) μ :=
    hg.bdd_mul hu.measurable.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hu.abs_le_one x)
  simpa only [mul_comm] using h

/-- Integral bang-bang bound (1D): for `g` integrable and `u` a test function, with
    `S := {x | 0 ≤ g x}`,
    `|∫ g·u| ≤ max |∫ g·𝟙_S| |∫ g·𝟙_{Sᶜ}|`. -/
theorem bangbang_integral {g u : Ω → ℝ} (hg : Integrable g μ) (hgm : Measurable g)
    (hu : IsTestFun u) :
    |∫ x, g x * u x ∂μ| ≤
      max |∫ x, g x * (Set.indicator {x | 0 ≤ g x} (1 : Ω → ℝ) x) ∂μ|
          |∫ x, g x * (Set.indicator {x | 0 ≤ g x}ᶜ (1 : Ω → ℝ) x) ∂μ| := by
  have hSmeas : MeasurableSet {x : Ω | 0 ≤ g x} := measurableSet_le measurable_const hgm
  have hindS : IsTestFun (Set.indicator {x | 0 ≤ g x} (1 : Ω → ℝ)) :=
    isTestFun_indicator hSmeas
  have hindSc : IsTestFun (Set.indicator {x | 0 ≤ g x}ᶜ (1 : Ω → ℝ)) :=
    isTestFun_indicator hSmeas.compl
  -- integrability of the three integrands
  have iu := integrable_mul_testFun hg hu
  have iS := integrable_mul_testFun hg hindS
  have iSc := integrable_mul_testFun hg hindSc
  -- a ≤ t ≤ b from the pointwise bound, then |t| ≤ max |b| |a|
  have hle₁ : (∫ x, g x * (Set.indicator {x | 0 ≤ g x}ᶜ (1 : Ω → ℝ) x) ∂μ)
      ≤ ∫ x, g x * u x ∂μ :=
    integral_mono iSc iu (fun x => (bangbang_pointwise hu x).1)
  have hle₂ : (∫ x, g x * u x ∂μ)
      ≤ ∫ x, g x * (Set.indicator {x | 0 ≤ g x} (1 : Ω → ℝ) x) ∂μ :=
    integral_mono iu iS (fun x => (bangbang_pointwise hu x).2)
  have := abs_le_max_abs_abs hle₁ hle₂
  rwa [max_comm] at this

section Bounds

variable [IsProbabilityMeasure μ]

/-! ### Fubini bridges between the 2D integral and the 1D bang-bang form -/

/-- Fubini bridge (`u`-slot): `∫∫ W·u·v = ∫ x, (∫ y, W x y · v y) · u x`. -/
theorem integral_eq_slice_u (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) :
    (∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ))
      = ∫ x, (∫ y, W.toFun x y * v y ∂μ) * u x ∂μ := by
  rw [integral_prod _ (integrable_integrand W hu hv)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  -- inner: ∫ y, W x y * u x * v y = (∫ y, W x y * v y) * u x
  rw [show (∫ y, W.toFun x y * u x * v y ∂μ) = ∫ y, u x * (W.toFun x y * v y) ∂μ from
        integral_congr_ae (ae_of_all _ fun y => by ring),
      integral_const_mul, mul_comm (u x)]

/-- Fubini bridge (`v`-slot): `∫∫ W·u·v = ∫ y, (∫ x, W x y · u x) · v y`. -/
theorem integral_eq_slice_v (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) :
    (∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ))
      = ∫ y, (∫ x, W.toFun x y * u x ∂μ) * v y ∂μ := by
  rw [integral_prod_symm _ (integrable_integrand W hu hv)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [show (∫ x, W.toFun x y * u x * v y ∂μ) = ∫ x, v y * (W.toFun x y * u x) ∂μ from
        integral_congr_ae (ae_of_all _ fun x => by ring),
      integral_const_mul, mul_comm (v y)]

omit [IsProbabilityMeasure μ] in
/-- The pair-integrand `(x,y) ↦ W x y · v y` (no `u`-factor) is measurable. -/
theorem measurable_pair_v (W : SymmKernel Ω μ) {v : Ω → ℝ} (hv : Measurable v) :
    Measurable (fun p : Ω × Ω => W.toFun p.1 p.2 * v p.2) :=
  W.meas'.mul (hv.comp measurable_snd)

omit [IsProbabilityMeasure μ] in
/-- The pair-integrand `(x,y) ↦ W x y · u x` (no `v`-factor) is measurable. -/
theorem measurable_pair_u (W : SymmKernel Ω μ) {u : Ω → ℝ} (hu : Measurable u) :
    Measurable (fun p : Ω × Ω => W.toFun p.1 p.2 * u p.1) :=
  W.meas'.mul (hu.comp measurable_fst)

/-- The `v`-slice `g x = ∫ y, W x y · v y` is (genuinely) measurable in `x`. -/
theorem measurable_slice_v (W : SymmKernel Ω μ) {v : Ω → ℝ} (hv : Measurable v) :
    Measurable (fun x => ∫ y, W.toFun x y * v y ∂μ) :=
  ((measurable_pair_v W hv).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- The `u`-slice `h y = ∫ x, W x y · u x` is (genuinely) measurable in `y`. -/
theorem measurable_slice_u (W : SymmKernel Ω μ) {u : Ω → ℝ} (hu : Measurable u) :
    Measurable (fun y => ∫ x, W.toFun x y * u x ∂μ) :=
  ((measurable_pair_u W hu).stronglyMeasurable.integral_prod_left' (μ := μ)).measurable

/-- The pair-integrand `(x,y) ↦ W x y · v y` is integrable against `μ ×ˢ μ`. -/
theorem integrable_pair_v (W : SymmKernel Ω μ) {v : Ω → ℝ} (hv : IsTestFun v) :
    Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * v p.2) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd (measurable_pair_v W hv.measurable)
    (C := W.bound) (fun p => ?_)
  calc |W.toFun p.1 p.2 * v p.2| = |W.toFun p.1 p.2| * |v p.2| := abs_mul _ _
    _ ≤ W.bound * 1 := mul_le_mul (W.abs_le_bound _ _) (hv.abs_le_one _) (abs_nonneg _)
        W.bound_nonneg
    _ = W.bound := mul_one _

/-- The pair-integrand `(x,y) ↦ W x y · u x` is integrable against `μ ×ˢ μ`. -/
theorem integrable_pair_u (W : SymmKernel Ω μ) {u : Ω → ℝ} (hu : IsTestFun u) :
    Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * u p.1) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd (measurable_pair_u W hu.measurable)
    (C := W.bound) (fun p => ?_)
  calc |W.toFun p.1 p.2 * u p.1| = |W.toFun p.1 p.2| * |u p.1| := abs_mul _ _
    _ ≤ W.bound * 1 := mul_le_mul (W.abs_le_bound _ _) (hu.abs_le_one _) (abs_nonneg _)
        W.bound_nonneg
    _ = W.bound := mul_one _

/-- The `v`-slice `g x = ∫ y, W x y · v y` is integrable in `x`. -/
theorem integrable_slice_v (W : SymmKernel Ω μ) {v : Ω → ℝ} (hv : IsTestFun v) :
    Integrable (fun x => ∫ y, W.toFun x y * v y ∂μ) μ :=
  (integrable_pair_v W hv).integral_prod_left

/-- The `u`-slice `h y = ∫ x, W x y · u x` is integrable in `y`. -/
theorem integrable_slice_u (W : SymmKernel Ω μ) {u : Ω → ℝ} (hu : IsTestFun u) :
    Integrable (fun y => ∫ x, W.toFun x y * u x ∂μ) μ :=
  (integrable_pair_u W hu).integral_prod_right

/-! ### Easy direction: `cutNormSet ≤ cutNorm` -/

/-- Every member of the `cutNormSet` family is a member of the `cutNorm` family (indicators are
    test functions), so `cutNormSet W ≤ cutNorm W`. -/
theorem cutNormSet_le_cutNorm (W : SymmKernel Ω μ) : cutNormSet W ≤ cutNorm W := by
  rw [cutNormSet]
  refine ciSup_le fun S => ciSup_le fun T => ?_
  by_cases hS : MeasurableSet S
  · by_cases hT : MeasurableSet T
    · rw [ciSup_pos hS, ciSup_pos hT]
      exact le_cutNorm W (isTestFun_indicator hS) (isTestFun_indicator hT)
    · rw [ciSup_pos hS, ciSup_neg hT]; simpa using cutNorm_nonneg W
  · rw [ciSup_neg hS]; simpa using cutNorm_nonneg W

/-! ### `BddAbove` infrastructure for `cutNormSet` (mirrors `CutNorm`) -/

/-- A `cutNormSet` integrand value (indicators of measurable `S, T`) is `≤ W.bound`. -/
theorem abs_integral_indicator_le_bound (W : SymmKernel Ω μ) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
        * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)| ≤ W.bound :=
  abs_integral_le_bound W (isTestFun_indicator hS) (isTestFun_indicator hT)

/-- For a fixed `S`, the inner `⨆` over the `Prop` binders is `≤ W.bound`. -/
theorem inner_le_bound_set (W : SymmKernel Ω μ) (S T : Set Ω) :
    (⨆ (_ : MeasurableSet S) (_ : MeasurableSet T),
      |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
        * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)|) ≤ W.bound := by
  by_cases hS : MeasurableSet S
  · by_cases hT : MeasurableSet T
    · simp only [ciSup_pos hS, ciSup_pos hT]
      exact abs_integral_indicator_le_bound W hS hT
    · rw [ciSup_pos hS, ciSup_neg hT]; simpa using W.bound_nonneg
  · rw [ciSup_neg hS]; simpa using W.bound_nonneg

/-- For a fixed `S`, the family over `T` is `BddAbove`. -/
theorem bddAbove_inner_set (W : SymmKernel Ω μ) (S : Set Ω) :
    BddAbove (Set.range (fun T : Set Ω =>
      ⨆ (_ : MeasurableSet S) (_ : MeasurableSet T),
        |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
          * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)|)) := by
  refine ⟨W.bound, ?_⟩
  rintro a ⟨T, rfl⟩
  exact inner_le_bound_set W S T

/-- The outer family (over `S`) is `BddAbove`. -/
theorem bddAbove_cutNormSet_family (W : SymmKernel Ω μ) :
    BddAbove (Set.range (fun S : Set Ω =>
      ⨆ (T : Set Ω) (_ : MeasurableSet S) (_ : MeasurableSet T),
        |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
          * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)|)) := by
  refine ⟨W.bound, ?_⟩
  rintro a ⟨S, rfl⟩
  exact ciSup_le fun T => inner_le_bound_set W S T

/-- A single measurable-rectangle value is `≤ cutNormSet W`. -/
theorem le_cutNormSet (W : SymmKernel Ω μ) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
        * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)| ≤ cutNormSet W := by
  show _ ≤ ⨆ (S : Set Ω) (T : Set Ω) (_ : MeasurableSet S) (_ : MeasurableSet T),
      |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
        * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)|
  calc |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
          * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)|
      = ⨆ (_ : MeasurableSet S) (_ : MeasurableSet T),
          |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
            * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)| := by
        rw [ciSup_pos hS, ciSup_pos hT]
    _ ≤ ⨆ (T : Set Ω) (_ : MeasurableSet S) (_ : MeasurableSet T),
          |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
            * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)| :=
        le_ciSup_of_le (bddAbove_inner_set W S) T (le_refl _)
    _ ≤ _ := le_ciSup (bddAbove_cutNormSet_family W) S

/-- `0 ≤ cutNormSet W` (take `S = T = ∅`, value `0`). -/
theorem cutNormSet_nonneg (W : SymmKernel Ω μ) : 0 ≤ cutNormSet W := by
  refine le_trans (le_of_eq ?_) (le_cutNormSet W (MeasurableSet.empty) (MeasurableSet.empty))
  simp

/-! ### `v`-slot reduction: indicator-left vs. test-`v` -/

/-- For a measurable set `S` and a test function `v`, the value `|∫∫ W·𝟙_S·v|` is bounded by
    `cutNormSet W`: run the bang-bang argument in the `v`-slot, landing on `|∫∫ W·𝟙_S·𝟙_T|`. -/
theorem le_cutNormSet_of_indicator_left (W : SymmKernel Ω μ) {S : Set Ω} (hS : MeasurableSet S)
    {v : Ω → ℝ} (hv : IsTestFun v) :
    |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1) * v p.2 ∂(μ.prod μ)|
      ≤ cutNormSet W := by
  set s : Ω → ℝ := Set.indicator S (1 : Ω → ℝ) with hs
  have hsTest : IsTestFun s := isTestFun_indicator hS
  set h : Ω → ℝ := fun y => ∫ x, W.toFun x y * s x ∂μ with hh
  have hhmeas : Measurable h := measurable_slice_u W hsTest.measurable
  have hhint : Integrable h μ := integrable_slice_u W hsTest
  -- bridge to the 1D v-slot
  have hbridge : (∫ p, W.toFun p.1 p.2 * s p.1 * v p.2 ∂(μ.prod μ))
      = ∫ y, h y * v y ∂μ := integral_eq_slice_v W hsTest hv
  rw [hbridge]
  -- bang-bang in the v-slot
  have hbb := bangbang_integral hhint hhmeas hv
  set T : Set Ω := {y | 0 ≤ h y} with hT
  have hTmeas : MeasurableSet T := measurableSet_le measurable_const hhmeas
  -- each ∫ h·𝟙_T = ∫∫ W·𝟙_S·𝟙_T  (bridge_v backward)
  have hconv : ∀ (R : Set Ω), MeasurableSet R →
      (∫ y, h y * (Set.indicator R (1 : Ω → ℝ) y) ∂μ)
        = ∫ p, W.toFun p.1 p.2 * s p.1 * (Set.indicator R (1 : Ω → ℝ) p.2) ∂(μ.prod μ) := by
    intro R hR
    rw [integral_eq_slice_v W hsTest (isTestFun_indicator hR)]
  rw [hconv T hTmeas, hconv Tᶜ hTmeas.compl] at hbb
  refine le_trans hbb (max_le ?_ ?_)
  · exact le_cutNormSet W hS hTmeas
  · exact le_cutNormSet W hS hTmeas.compl

/-! ### Hard direction: `cutNorm ≤ cutNormSet` -/

/-- For test functions `u, v`, the value `|∫∫ W·u·v|` is bounded by `cutNormSet W`: bang-bang in
    the `u`-slot reduces to `|∫∫ W·𝟙_S·v|`, which the `v`-slot reduction sends to `cutNormSet`. -/
theorem abs_integral_le_cutNormSet (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsTestFun u)
    (hv : IsTestFun v) :
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| ≤ cutNormSet W := by
  set g : Ω → ℝ := fun x => ∫ y, W.toFun x y * v y ∂μ with hg
  have hgmeas : Measurable g := measurable_slice_v W hv.measurable
  have hgint : Integrable g μ := integrable_slice_v W hv
  -- bridge to the 1D u-slot
  rw [integral_eq_slice_u W hu hv]
  -- bang-bang in the u-slot
  have hbb := bangbang_integral hgint hgmeas hu
  set S : Set Ω := {x | 0 ≤ g x} with hS
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const hgmeas
  -- each ∫ g·𝟙_S = ∫∫ W·𝟙_S·v  (bridge_u backward)
  have hconv : ∀ (R : Set Ω), MeasurableSet R →
      (∫ x, g x * (Set.indicator R (1 : Ω → ℝ) x) ∂μ)
        = ∫ p, W.toFun p.1 p.2 * (Set.indicator R (1 : Ω → ℝ) p.1) * v p.2 ∂(μ.prod μ) := by
    intro R hR
    rw [integral_eq_slice_u W (isTestFun_indicator hR) hv]
  rw [hconv S hSmeas, hconv Sᶜ hSmeas.compl] at hbb
  refine le_trans hbb (max_le ?_ ?_)
  · exact le_cutNormSet_of_indicator_left W hSmeas hv
  · exact le_cutNormSet_of_indicator_left W hSmeas.compl hv

/-- The test-function cut norm is bounded by the set-form cut norm. -/
theorem cutNorm_le_cutNormSet (W : SymmKernel Ω μ) : cutNorm W ≤ cutNormSet W := by
  rw [cutNorm]
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      exact abs_integral_le_cutNormSet W hu hv
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using cutNormSet_nonneg W
  · rw [ciSup_neg hu]; simpa using cutNormSet_nonneg W

/-- **Set-form cut-norm equivalence** (C11258): the test-function cut norm equals the textbook
    supremum over measurable rectangles. -/
theorem cutNorm_eq_cutNormSet (W : SymmKernel Ω μ) : cutNorm W = cutNormSet W :=
  le_antisymm (cutNorm_le_cutNormSet W) (cutNormSet_le_cutNorm W)

end Bounds

end Graphons
