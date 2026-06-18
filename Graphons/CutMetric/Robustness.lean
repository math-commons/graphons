/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md WS4 — **definition robustness**: validate the repo's cut-metric
design decisions against alternative textbook formulations (Lovász, "Large Networks and Graph
Limits", §8.1–8.2). Each "two formulations agree" theorem is a validation of a design choice.

Main results:
* `Graphon.pullback` — pullback of a graphon along a measurable map (carrier transport).
* `cutDist_le_cutNorm_pullback_sub` (R1, Lovász Lemma 8.13, provable half) — any pair of
  measure-preserving maps from a common space realizes an upper bound for the coupling-infimum
  cut distance. (The converse needs the measure-isomorphism theorem, absent from Mathlib —
  out of scope.)
* `cutDist_pullback_self` (R2a, generalizes `cutDist_toUnit`) — pulling back along a
  measure-preserving map moves a graphon zero cut-distance.
* `cutDist_pullback_pullback` (R2) — pulling back BOTH graphons along one measure-preserving
  map preserves the cut distance exactly.
* `cutNorm_le_cutNormSigned` / `cutNormSigned_le_four_mul` (R3, Lovász Lemma 8.10/8.11
  flavor) — the `[0,1]`- and `[-1,1]`-test-function cut norms agree up to a factor 4.
-/
import Graphons.CutMetric.Gluing

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### R0: the carrier-transport primitive -/

section Pullback

variable [IsProbabilityMeasure μ]

/-- **R0**: pullback of a graphon along a measurable map (the carrier-transport primitive). -/
noncomputable def Graphon.pullback {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (W : Graphon Ω μ) (φ : Ω' → Ω) (hφ : Measurable φ) :
    Graphon Ω' μ' :=
  Graphon.mk' (fun x y => W.toFun (φ x) (φ y))
    (fun x y => W.symm' (φ x) (φ y))
    (W.meas'.comp ((hφ.comp measurable_fst).prodMk (hφ.comp measurable_snd)))
    (fun x y => W.nonneg' (φ x) (φ y))
    (fun x y => W.le_one' (φ x) (φ y))

@[simp] theorem Graphon.pullback_apply {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (W : Graphon Ω μ) (φ : Ω' → Ω) (hφ : Measurable φ) (x y : Ω') :
    (W.pullback (μ' := μ') φ hφ).toFun x y = W.toFun (φ x) (φ y) := rfl

end Pullback

/-! ### R1: couplings dominate maps (Lovász Lemma 8.13, the provable half) -/

/-- **R1 (couplings dominate maps)**: any pair of measure-preserving maps from a common space
    realizes an upper bound for the coupling-infimum cut distance, via the graph coupling
    `π = (φ, ψ)_* μ'`. (The converse — that maps suffice to compute the infimum — needs the
    measure-isomorphism theorem, absent from Mathlib; documented out of scope.) -/
theorem cutDist_le_cutNorm_pullback_sub {Ω' Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ' : Measure Ω'} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {φ : Ω' → Ω₁} {ψ : Ω' → Ω₂}
    (hφ : MeasurePreserving φ μ' μ₁) (hψ : MeasurePreserving ψ μ' μ₂) :
    cutDist U W ≤ cutNorm ((U.pullback (μ' := μ') φ hφ.measurable).toSymmKernel
      - (W.pullback (μ' := μ') ψ hψ.measurable).toSymmKernel) := by
  set g : Ω' → Ω₁ × Ω₂ := fun x => (φ x, ψ x) with hgdef
  have hg : Measurable g := hφ.measurable.prodMk hψ.measurable
  have hcoup : IsCoupling μ₁ μ₂ (μ'.map g) := by
    constructor
    · rw [Measure.map_map measurable_fst hg]
      exact hφ.map_eq
    · rw [Measure.map_map measurable_snd hg]
      exact hψ.map_eq
  haveI : IsProbabilityMeasure (μ'.map g) := hcoup.isProbabilityMeasure
  have hgp : MeasurePreserving g μ' (μ'.map g) := ⟨hg, rfl⟩
  refine le_trans (cutDist_le_of_coupling U W ⟨μ'.map g, hcoup⟩) ?_
  show cutNorm (overlay U W (μ'.map g))
      ≤ cutNorm ((U.pullback (μ' := μ') φ hφ.measurable).toSymmKernel
        - (W.pullback (μ' := μ') ψ hψ.measurable).toSymmKernel)
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      -- The pulled-back test functions on `Ω'`.
      have hu' : IsTestFun (fun x : Ω' => u (g x)) := ⟨hu.1.comp hg, fun x => hu.2 (g x)⟩
      have hv' : IsTestFun (fun x : Ω' => v (g x)) := ⟨hv.1.comp hg, fun x => hv.2 (g x)⟩
      -- Change of variables along the graph map `g`: the two integrals are EQUAL.
      have key : ∫ p, (overlay U W (μ'.map g)).toFun p.1 p.2 * u p.1 * v p.2
            ∂((μ'.map g).prod (μ'.map g))
          = ∫ p, ((U.pullback (μ' := μ') φ hφ.measurable).toSymmKernel
              - (W.pullback (μ' := μ') ψ hψ.measurable).toSymmKernel).toFun p.1 p.2
              * u (g p.1) * v (g p.2) ∂(μ'.prod μ') := by
        rw [← (hgp.prod hgp).map_eq,
          integral_map (hg.prodMap hg).aemeasurable
            (measurable_integrand (overlay U W (μ'.map g)) hu.1 hv.1).aestronglyMeasurable]
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        show (overlay U W (μ'.map g)).toFun (Prod.map g g p).1 (Prod.map g g p).2
            * u (Prod.map g g p).1 * v (Prod.map g g p).2
          = ((U.pullback (μ' := μ') φ hφ.measurable).toSymmKernel
              - (W.pullback (μ' := μ') ψ hψ.measurable).toSymmKernel).toFun p.1 p.2
              * u (g p.1) * v (g p.2)
        simp only [Prod.map_fst, Prod.map_snd, overlay_apply, SymmKernel.sub_apply,
          Graphon.pullback_apply, hgdef]
      rw [key]
      exact le_cutNorm _ hu' hv'
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using cutNorm_nonneg _
  · rw [ciSup_neg hu]; simpa using cutNorm_nonneg _

/-! ### R2a: pullback is invisible to the cut metric -/

section PullbackInvariance

variable [IsProbabilityMeasure μ]

/-- **R2a** (generalizes `cutDist_toUnit`): pulling back along a measure-preserving map moves a
    graphon zero cut-distance — pullback is invisible to the cut metric. Special case of R1 with
    the identity as the first map: the pullback-difference kernel vanishes identically. -/
theorem cutDist_pullback_self {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (W : Graphon Ω μ) {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ μ' μ) :
    cutDist (W.pullback (μ' := μ') φ hφ.measurable) W = 0 := by
  refine le_antisymm ?_ (cutDist_nonneg _ _)
  -- The pullback-difference kernel for `(id, φ)` is identically zero.
  have hzero : ((W.pullback (μ' := μ') φ hφ.measurable).pullback (μ' := μ') id
        (MeasurePreserving.id μ').measurable).toSymmKernel
      - (W.pullback (μ' := μ') φ hφ.measurable).toSymmKernel = 0 := by
    ext x y
    simp
  have h0 : cutNorm (((W.pullback (μ' := μ') φ hφ.measurable).pullback (μ' := μ') id
        (MeasurePreserving.id μ').measurable).toSymmKernel
      - (W.pullback (μ' := μ') φ hφ.measurable).toSymmKernel) = 0 := by
    rw [hzero]; exact cutNorm_zero
  exact le_trans
    (cutDist_le_cutNorm_pullback_sub _ W (MeasurePreserving.id μ') hφ) (le_of_eq h0)

/-! ### R2: carrier-transport invariance -/

/-- **R2 (carrier-transport invariance)**: pulling back BOTH graphons along one
    measure-preserving map preserves the cut distance exactly. Four applications of the
    cross-carrier triangle inequality through `cutDist_pullback_self`. -/
theorem cutDist_pullback_pullback {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    [Nonempty Ω] [Nonempty Ω'] (U W : Graphon Ω μ) {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ μ' μ) :
    cutDist (U.pullback (μ' := μ') φ hφ.measurable) (W.pullback (μ' := μ') φ hφ.measurable)
      = cutDist U W := by
  set Up := U.pullback (μ' := μ') φ hφ.measurable with hUp
  set Wp := W.pullback (μ' := μ') φ hφ.measurable with hWp
  have tU : cutDist Up U = 0 := cutDist_pullback_self U hφ
  have tW : cutDist Wp W = 0 := cutDist_pullback_self W hφ
  have tU' : cutDist U Up = 0 := by rw [cutDist_comm]; exact tU
  have tW' : cutDist W Wp = 0 := by rw [cutDist_comm]; exact tW
  -- ≤ : Up → U → W → Wp ;  ≥ : U → Up → Wp → W
  have t1 := cutDist_triangle Up U Wp
  have t2 := cutDist_triangle U W Wp
  have t3 := cutDist_triangle U Up W
  have t4 := cutDist_triangle Up Wp W
  exact le_antisymm (by linarith) (by linarith)

end PullbackInvariance

/-! ### R3: the signed-test-function (`∞→1`) formulation, up to a factor 4 -/

/-- **Signed test functions** (`[-1,1]`-valued) — the functional-analytic `∞→1` formulation. -/
def IsSignedTestFun (u : Ω → ℝ) : Prop := Measurable u ∧ ∀ x, u x ∈ Set.Icc (-1 : ℝ) 1

/-- The constant `0` function is a signed test function. -/
theorem isSignedTestFun_zero : IsSignedTestFun (fun _ : Ω => (0 : ℝ)) :=
  ⟨measurable_const, fun _ => ⟨by norm_num, zero_le_one⟩⟩

theorem IsSignedTestFun.measurable {u : Ω → ℝ} (hu : IsSignedTestFun u) : Measurable u := hu.1

theorem IsSignedTestFun.abs_le_one {u : Ω → ℝ} (hu : IsSignedTestFun u) (x : Ω) : |u x| ≤ 1 :=
  abs_le.2 ⟨(hu.2 x).1, (hu.2 x).2⟩

/-- Every `[0,1]`-valued test function is a signed test function (`Icc 0 1 ⊆ Icc (-1) 1`). -/
theorem IsTestFun.isSignedTestFun {u : Ω → ℝ} (hu : IsTestFun u) : IsSignedTestFun u :=
  ⟨hu.1, fun x => ⟨le_trans (by norm_num) (hu.2 x).1, (hu.2 x).2⟩⟩

/-- The positive part `x ↦ max (u x) 0` of a signed test function is a test function. -/
theorem IsSignedTestFun.isTestFun_posPart {u : Ω → ℝ} (hu : IsSignedTestFun u) :
    IsTestFun (fun x => max (u x) 0) :=
  ⟨hu.1.max measurable_const, fun x => ⟨le_max_right _ _, max_le (hu.2 x).2 zero_le_one⟩⟩

/-- The negative part `x ↦ max (-u x) 0` of a signed test function is a test function. -/
theorem IsSignedTestFun.isTestFun_negPart {u : Ω → ℝ} (hu : IsSignedTestFun u) :
    IsTestFun (fun x => max (-u x) 0) :=
  ⟨hu.1.neg.max measurable_const,
    fun x => ⟨le_max_right _ _, max_le (by linarith [(hu.2 x).1]) zero_le_one⟩⟩

/-- The **signed-test-function cut norm**: `sup` over `[-1,1]`-valued test pairs. -/
noncomputable def cutNormSigned (W : SymmKernel Ω μ) : ℝ :=
  ⨆ (u : Ω → ℝ) (v : Ω → ℝ) (_ : IsSignedTestFun u) (_ : IsSignedTestFun v),
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|

section SignedBounds

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Pointwise: `|W x y · u x · v y| ≤ W.bound` for a signed test pair. -/
theorem abs_integrand_le_bound_signed (W : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : IsSignedTestFun u) (hv : IsSignedTestFun v) (x y : Ω) :
    |W.toFun x y * u x * v y| ≤ W.bound := by
  calc |W.toFun x y * u x * v y|
      = |W.toFun x y| * |u x| * |v y| := by rw [abs_mul, abs_mul]
    _ ≤ W.bound * 1 * 1 :=
        mul_le_mul (mul_le_mul (W.abs_le_bound x y) (hu.abs_le_one x) (abs_nonneg _)
            W.bound_nonneg) (hv.abs_le_one y) (abs_nonneg _)
          (mul_nonneg W.bound_nonneg zero_le_one)
    _ = W.bound := by ring

/-- The signed-test-pair integrand is integrable against `μ ×ˢ μ`. -/
theorem integrable_integrand_signed (W : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : IsSignedTestFun u) (hv : IsSignedTestFun v) :
    Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * u p.1 * v p.2) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd (measurable_integrand W hu.measurable hv.measurable)
    (C := W.bound) (fun p => ?_)
  obtain ⟨x, y⟩ := p
  exact abs_integrand_le_bound_signed W hu hv x y

/-- Each signed-test-pair value `|∫ W·u·v|` is bounded by `W.bound`. -/
theorem abs_integral_le_bound_signed (W : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : IsSignedTestFun u) (hv : IsSignedTestFun v) :
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| ≤ W.bound := by
  calc |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
      ≤ ∫ p, |W.toFun p.1 p.2 * u p.1 * v p.2| ∂(μ.prod μ) := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ.prod μ)
            (fun p => W.toFun p.1 p.2 * u p.1 * v p.2)
    _ ≤ ∫ _, W.bound ∂(μ.prod μ) := by
        refine integral_mono (integrable_integrand_signed W hu hv).abs (integrable_const _)
          (fun p => ?_)
        obtain ⟨x, y⟩ := p
        exact abs_integrand_le_bound_signed W hu hv x y
    _ = W.bound := by simp

/-- For a fixed `u`, the inner signed family (`Prop`-binders peeled) is `≤ W.bound`. -/
theorem inner_le_bound_signed (W : SymmKernel Ω μ) (u v : Ω → ℝ) :
    (⨆ (_ : IsSignedTestFun u) (_ : IsSignedTestFun v),
      |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|) ≤ W.bound := by
  by_cases hu : IsSignedTestFun u
  · by_cases hv : IsSignedTestFun v
    · simp only [ciSup_pos hu, ciSup_pos hv]
      exact abs_integral_le_bound_signed W hu hv
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using W.bound_nonneg
  · rw [ciSup_neg hu]; simpa using W.bound_nonneg

/-- For a fixed `u`, the signed family over `v` is `BddAbove` (witness `W.bound`). -/
theorem bddAbove_inner_signed (W : SymmKernel Ω μ) (u : Ω → ℝ) :
    BddAbove (Set.range (fun v : Ω → ℝ =>
      ⨆ (_ : IsSignedTestFun u) (_ : IsSignedTestFun v),
        |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|)) := by
  refine ⟨W.bound, ?_⟩
  rintro a ⟨v, rfl⟩
  exact inner_le_bound_signed W u v

/-- The outer signed family (over `u`) is `BddAbove` (witness `W.bound`). -/
theorem bddAbove_cutNormSigned_family (W : SymmKernel Ω μ) :
    BddAbove (Set.range (fun u : Ω → ℝ =>
      ⨆ (v : Ω → ℝ) (_ : IsSignedTestFun u) (_ : IsSignedTestFun v),
        |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|)) := by
  refine ⟨W.bound, ?_⟩
  rintro a ⟨u, rfl⟩
  exact ciSup_le fun v => inner_le_bound_signed W u v

/-- A single signed-test-pair value is `≤ cutNormSigned W` (uses `BddAbove`). -/
theorem le_cutNormSigned (W : SymmKernel Ω μ) {u v : Ω → ℝ} (hu : IsSignedTestFun u)
    (hv : IsSignedTestFun v) :
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| ≤ cutNormSigned W := by
  show _ ≤ ⨆ (u : Ω → ℝ) (v : Ω → ℝ) (_ : IsSignedTestFun u) (_ : IsSignedTestFun v),
      |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
  calc |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
      = ⨆ (_ : IsSignedTestFun u) (_ : IsSignedTestFun v),
          |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| := by
        rw [ciSup_pos hu, ciSup_pos hv]
    _ ≤ ⨆ (v : Ω → ℝ) (_ : IsSignedTestFun u) (_ : IsSignedTestFun v),
          |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| :=
        le_ciSup_of_le (bddAbove_inner_signed W u) v (le_refl _)
    _ ≤ _ := le_ciSup (bddAbove_cutNormSigned_family W) u

/-- `cutNormSigned W ≥ 0` (take `u = v = 0`). -/
theorem cutNormSigned_nonneg (W : SymmKernel Ω μ) : 0 ≤ cutNormSigned W := by
  have hzero : IsSignedTestFun (fun _ : Ω => (0 : ℝ)) := isSignedTestFun_zero
  refine le_trans (le_of_eq ?_) (le_cutNormSigned W hzero hzero)
  simp

/-! #### The factor-4 sandwich -/

/-- **R3 (easy direction)**: every `[0,1]` test pair is a `[-1,1]` test pair, so
    `cutNorm W ≤ cutNormSigned W`. -/
theorem cutNorm_le_cutNormSigned (W : SymmKernel Ω μ) : cutNorm W ≤ cutNormSigned W := by
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      exact le_cutNormSigned W hu.isSignedTestFun hv.isSignedTestFun
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using cutNormSigned_nonneg W
  · rw [ciSup_neg hu]; simpa using cutNormSigned_nonneg W

/-- Per-signed-pair estimate behind the factor-4 bound: decompose `u = u⁺ - u⁻`,
    `v = v⁺ - v⁻` into `[0,1]` test functions, split the integral into four pieces, and bound
    each by `cutNorm W`. -/
private theorem abs_integral_le_four_mul_cutNorm (W : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : IsSignedTestFun u) (hv : IsSignedTestFun v) :
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)| ≤ 4 * cutNorm W := by
  have hup := hu.isTestFun_posPart
  have hun := hu.isTestFun_negPart
  have hvp := hv.isTestFun_posPart
  have hvn := hv.isTestFun_negPart
  -- Integrability of all the pieces (each integrand is bounded by `W.bound`).
  have hIvp : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * u p.1 * max (v p.2) 0)
      (μ.prod μ) := integrable_integrand_signed W hu hvp.isSignedTestFun
  have hIvn : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * u p.1 * max (-v p.2) 0)
      (μ.prod μ) := integrable_integrand_signed W hu hvn.isSignedTestFun
  have hIpp : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * max (u p.1) 0 * max (v p.2) 0)
      (μ.prod μ) := integrable_integrand W hup hvp
  have hInp : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * max (-u p.1) 0 * max (v p.2) 0)
      (μ.prod μ) := integrable_integrand W hun hvp
  have hIpn : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * max (u p.1) 0 * max (-v p.2) 0)
      (μ.prod μ) := integrable_integrand W hup hvn
  have hInn : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * max (-u p.1) 0 * max (-v p.2) 0)
      (μ.prod μ) := integrable_integrand W hun hvn
  -- Split `v = v⁺ - v⁻`.
  have hsplit_v : (∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ))
      = (∫ p, W.toFun p.1 p.2 * u p.1 * max (v p.2) 0 ∂(μ.prod μ))
        - ∫ p, W.toFun p.1 p.2 * u p.1 * max (-v p.2) 0 ∂(μ.prod μ) := by
    rw [← integral_sub hIvp hIvn]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show W.toFun p.1 p.2 * u p.1 * v p.2
        = W.toFun p.1 p.2 * u p.1 * max (v p.2) 0 - W.toFun p.1 p.2 * u p.1 * max (-v p.2) 0
    rcases le_total 0 (v p.2) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  -- Split `u = u⁺ - u⁻` under `v⁺`.
  have hsplit_p : (∫ p, W.toFun p.1 p.2 * u p.1 * max (v p.2) 0 ∂(μ.prod μ))
      = (∫ p, W.toFun p.1 p.2 * max (u p.1) 0 * max (v p.2) 0 ∂(μ.prod μ))
        - ∫ p, W.toFun p.1 p.2 * max (-u p.1) 0 * max (v p.2) 0 ∂(μ.prod μ) := by
    rw [← integral_sub hIpp hInp]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show W.toFun p.1 p.2 * u p.1 * max (v p.2) 0
        = W.toFun p.1 p.2 * max (u p.1) 0 * max (v p.2) 0
          - W.toFun p.1 p.2 * max (-u p.1) 0 * max (v p.2) 0
    rcases le_total 0 (u p.1) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  -- Split `u = u⁺ - u⁻` under `v⁻`.
  have hsplit_n : (∫ p, W.toFun p.1 p.2 * u p.1 * max (-v p.2) 0 ∂(μ.prod μ))
      = (∫ p, W.toFun p.1 p.2 * max (u p.1) 0 * max (-v p.2) 0 ∂(μ.prod μ))
        - ∫ p, W.toFun p.1 p.2 * max (-u p.1) 0 * max (-v p.2) 0 ∂(μ.prod μ) := by
    rw [← integral_sub hIpn hInn]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show W.toFun p.1 p.2 * u p.1 * max (-v p.2) 0
        = W.toFun p.1 p.2 * max (u p.1) 0 * max (-v p.2) 0
          - W.toFun p.1 p.2 * max (-u p.1) 0 * max (-v p.2) 0
    rcases le_total 0 (u p.1) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  -- Each of the four `[0,1]`-pair integrals is ≤ cutNorm W.
  have h1 : |∫ p, W.toFun p.1 p.2 * max (u p.1) 0 * max (v p.2) 0 ∂(μ.prod μ)| ≤ cutNorm W :=
    le_cutNorm W hup hvp
  have h2 : |∫ p, W.toFun p.1 p.2 * max (-u p.1) 0 * max (v p.2) 0 ∂(μ.prod μ)| ≤ cutNorm W :=
    le_cutNorm W hun hvp
  have h3 : |∫ p, W.toFun p.1 p.2 * max (u p.1) 0 * max (-v p.2) 0 ∂(μ.prod μ)| ≤ cutNorm W :=
    le_cutNorm W hup hvn
  have h4 : |∫ p, W.toFun p.1 p.2 * max (-u p.1) 0 * max (-v p.2) 0 ∂(μ.prod μ)| ≤ cutNorm W :=
    le_cutNorm W hun hvn
  have habs : ∀ a b c d : ℝ, |a - b - (c - d)| ≤ |a| + |b| + |c| + |d| := fun a b c d => by
    calc |a - b - (c - d)| ≤ |a - b| + |c - d| := abs_sub _ _
      _ ≤ (|a| + |b|) + (|c| + |d|) := add_le_add (abs_sub _ _) (abs_sub _ _)
      _ = |a| + |b| + |c| + |d| := by ring
  rw [hsplit_v, hsplit_p, hsplit_n]
  exact le_trans (habs _ _ _ _) (by linarith)

/-- **R3 (factor-4 direction, Lovász Lemma 8.10/8.11 flavor)**:
    `cutNormSigned W ≤ 4 * cutNorm W`, by decomposing signed test functions into positive and
    negative `[0,1]`-valued parts. -/
theorem cutNormSigned_le_four_mul (W : SymmKernel Ω μ) : cutNormSigned W ≤ 4 * cutNorm W := by
  have h4 : (0 : ℝ) ≤ 4 * cutNorm W := mul_nonneg (by norm_num) (cutNorm_nonneg W)
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsSignedTestFun u
  · by_cases hv : IsSignedTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      exact abs_integral_le_four_mul_cutNorm W hu hv
    · rw [ciSup_pos hu, ciSup_neg hv]; simpa using h4
  · rw [ciSup_neg hu]; simpa using h4

end SignedBounds

end Graphons
