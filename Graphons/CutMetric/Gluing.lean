/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

The **coupling Gluing Lemma** for the cut metric (DESIGN.md §4/§8), the measure-theoretic
heart of the triangle inequality `cutDist_triangle`.

Given a coupling `π₁₂` of `(μ₁, μ₂)` and a coupling `π₂₃` of `(μ₂, μ₃)` (probability measures
sharing the middle marginal `μ₂`), we **glue** them over `μ₂` to produce a coupling `π₁₃` of
`(μ₁, μ₃)` such that

  `cutNorm (overlay U V π₁₃) ≤ cutNorm (overlay U W π₁₂) + cutNorm (overlay W V π₂₃)`.

The construction uses **disintegration along `μ₂`**: viewing the relevant marginal of each coupling
as a measure on `Ω₂ × _`, its `condKernel` gives a Markov kernel `Ω₂ → Measure _` (this needs
`Ω₁, Ω₃` to be `StandardBorelSpace`). The independent product of the two conditional kernels over
`μ₂` builds a measure `γ` on `Ω₂ × Ω₁ × Ω₃`; `π₁₃` is its `(Ω₁, Ω₃)`-marginal.
-/
import Graphons.CutMetric.CutDist

open MeasureTheory ProbabilityTheory

namespace Graphons

variable {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]

section Gluing

variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃]
variable [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] [StandardBorelSpace Ω₃]
variable [Nonempty Ω₁] [Nonempty Ω₂] [Nonempty Ω₃]

/-! ### The conditional kernels along the middle marginal `μ₂` -/

/-- The conditional kernel of a coupling `π₁₂` of `(μ₁, μ₂)` along the middle factor `μ₂`,
    obtained by swapping to a measure on `Ω₂ × Ω₁` and disintegrating. A Markov kernel
    `Ω₂ → Measure Ω₁`. -/
noncomputable def leftCondKernel (π₁₂ : Measure (Ω₁ × Ω₂)) [IsFiniteMeasure π₁₂] :
    Kernel Ω₂ Ω₁ :=
  (π₁₂.map Prod.swap).condKernel

/-- The conditional kernel of a coupling `π₂₃` of `(μ₂, μ₃)` along the first factor `μ₂`.
    A Markov kernel `Ω₂ → Measure Ω₃`. -/
noncomputable def rightCondKernel (π₂₃ : Measure (Ω₂ × Ω₃)) [IsFiniteMeasure π₂₃] :
    Kernel Ω₂ Ω₃ :=
  π₂₃.condKernel

instance (π₁₂ : Measure (Ω₁ × Ω₂)) [IsFiniteMeasure π₁₂] :
    IsMarkovKernel (leftCondKernel π₁₂) := by
  unfold leftCondKernel; infer_instance

instance (π₂₃ : Measure (Ω₂ × Ω₃)) [IsFiniteMeasure π₂₃] :
    IsMarkovKernel (rightCondKernel π₂₃) := by
  unfold rightCondKernel; infer_instance

/-- Disintegration of the swapped coupling: `μ₂ ⊗ₘ (leftCondKernel π₁₂) = π₁₂.map Prod.swap`. -/
theorem compProd_leftCondKernel {π₁₂ : Measure (Ω₁ × Ω₂)} [IsFiniteMeasure π₁₂]
    (h : IsCoupling μ₁ μ₂ π₁₂) :
    μ₂ ⊗ₘ (leftCondKernel π₁₂) = π₁₂.map Prod.swap := by
  have hfst : (π₁₂.map Prod.swap).fst = μ₂ := by
    rw [Measure.fst_map_swap]; exact h.2
  unfold leftCondKernel
  rw [← hfst]
  exact (π₁₂.map Prod.swap).disintegrate (π₁₂.map Prod.swap).condKernel

/-- Disintegration of the coupling: `μ₂ ⊗ₘ (rightCondKernel π₂₃) = π₂₃`. -/
theorem compProd_rightCondKernel {π₂₃ : Measure (Ω₂ × Ω₃)} [IsFiniteMeasure π₂₃]
    (h : IsCoupling μ₂ μ₃ π₂₃) :
    μ₂ ⊗ₘ (rightCondKernel π₂₃) = π₂₃ := by
  have hfst : π₂₃.fst = μ₂ := h.1
  unfold rightCondKernel
  rw [← hfst]
  exact π₂₃.disintegrate π₂₃.condKernel

/-! ### The glued triple measure and the `(1,3)`-coupling -/

/-- The **glued triple measure** on `Ω₂ × (Ω₁ × Ω₃)`: given `x₂ ∼ μ₂`, sample `x₁` and `x₃`
    *independently* from the two conditional kernels. -/
noncomputable def gluedTriple (μ₂ : Measure Ω₂) (π₁₂ : Measure (Ω₁ × Ω₂))
    (π₂₃ : Measure (Ω₂ × Ω₃)) [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] :
    Measure (Ω₂ × (Ω₁ × Ω₃)) :=
  μ₂ ⊗ₘ ((leftCondKernel π₁₂) ×ₖ (rightCondKernel π₂₃))

instance (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂] (π₁₂ : Measure (Ω₁ × Ω₂))
    (π₂₃ : Measure (Ω₂ × Ω₃)) [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] :
    IsProbabilityMeasure (gluedTriple μ₂ π₁₂ π₂₃) := by
  unfold gluedTriple; infer_instance

/-- The **glued coupling** of `(μ₁, μ₃)`: the `(Ω₁, Ω₃)`-marginal of the glued triple. -/
noncomputable def gluedCoupling (μ₂ : Measure Ω₂) (π₁₂ : Measure (Ω₁ × Ω₂))
    (π₂₃ : Measure (Ω₂ × Ω₃)) [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] :
    Measure (Ω₁ × Ω₃) :=
  (gluedTriple μ₂ π₁₂ π₂₃).map Prod.snd

instance (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂] (π₁₂ : Measure (Ω₁ × Ω₂))
    (π₂₃ : Measure (Ω₂ × Ω₃)) [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] :
    IsProbabilityMeasure (gluedCoupling μ₂ π₁₂ π₂₃) := by
  unfold gluedCoupling
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-! ### Marginals of the glued triple -/

/-- The `(Ω₂, Ω₁)`-marginal of the glued triple is `μ₂ ⊗ₘ κ₁`, i.e. `π₁₂.map Prod.swap`. -/
theorem gluedTriple_map_left {π₁₂ : Measure (Ω₁ × Ω₂)} {π₂₃ : Measure (Ω₂ × Ω₃)}
    [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] (h₁₂ : IsCoupling μ₁ μ₂ π₁₂) :
    (gluedTriple μ₂ π₁₂ π₂₃).map (Prod.map id Prod.fst) = π₁₂.map Prod.swap := by
  unfold gluedTriple
  rw [← Measure.compProd_map measurable_fst]
  have hfst : ((leftCondKernel π₁₂) ×ₖ (rightCondKernel π₂₃)).map Prod.fst
      = leftCondKernel π₁₂ := by
    rw [← Kernel.fst_eq]; exact Kernel.fst_prod _ _
  rw [hfst, compProd_leftCondKernel h₁₂]

/-- The `(Ω₂, Ω₃)`-marginal of the glued triple is `μ₂ ⊗ₘ κ₃ = π₂₃`. -/
theorem gluedTriple_map_right {π₁₂ : Measure (Ω₁ × Ω₂)} {π₂₃ : Measure (Ω₂ × Ω₃)}
    [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] (h₂₃ : IsCoupling μ₂ μ₃ π₂₃) :
    (gluedTriple μ₂ π₁₂ π₂₃).map (Prod.map id Prod.snd) = π₂₃ := by
  unfold gluedTriple
  rw [← Measure.compProd_map measurable_snd]
  have hsnd : ((leftCondKernel π₁₂) ×ₖ (rightCondKernel π₂₃)).map Prod.snd
      = rightCondKernel π₂₃ := by
    rw [← Kernel.snd_eq]; exact Kernel.snd_prod _ _
  rw [hsnd, compProd_rightCondKernel h₂₃]

/-- **`gluedCoupling` is a coupling of `(μ₁, μ₃)`.** -/
theorem gluedCoupling_isCoupling {π₁₂ : Measure (Ω₁ × Ω₂)} {π₂₃ : Measure (Ω₂ × Ω₃)}
    [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] (h₁₂ : IsCoupling μ₁ μ₂ π₁₂)
    (h₂₃ : IsCoupling μ₂ μ₃ π₂₃) :
    IsCoupling μ₁ μ₃ (gluedCoupling μ₂ π₁₂ π₂₃) := by
  constructor
  · -- fst-marginal = μ₁
    rw [gluedCoupling, Measure.map_map measurable_fst measurable_snd]
    -- (fun p => (p.2).1) = Prod.snd ∘ (Prod.map id Prod.fst)
    have : (Prod.fst ∘ Prod.snd : Ω₂ × (Ω₁ × Ω₃) → Ω₁)
        = Prod.snd ∘ (Prod.map id Prod.fst) := rfl
    rw [this, ← Measure.map_map measurable_snd (by fun_prop), gluedTriple_map_left h₁₂,
      Measure.map_map measurable_snd measurable_swap]
    have : (Prod.snd ∘ Prod.swap : Ω₁ × Ω₂ → Ω₁) = Prod.fst := rfl
    rw [this]; exact h₁₂.1
  · -- snd-marginal = μ₃
    rw [gluedCoupling, Measure.map_map measurable_snd measurable_snd]
    have : (Prod.snd ∘ Prod.snd : Ω₂ × (Ω₁ × Ω₃) → Ω₃)
        = Prod.snd ∘ (Prod.map id Prod.snd) := rfl
    rw [this, ← Measure.map_map measurable_snd (by fun_prop), gluedTriple_map_right h₂₃]
    exact h₂₃.2

/-! ### The telescoping cut-norm bound (marginalization)

The geometric heart of the triangle inequality: the cut-norm of the overlay over the glued
coupling is bounded by the sum of the cut-norms over `π₁₂` and `π₂₃`. We isolate the single
delicate measure-theoretic fact — that the cut-norm integral over a *pushforward* coupling
`ν.map (g₁, g₂)`, with test weights pulled back to the source `ν`, is bounded by `cutNorm` of the
overlay over that pushforward — as `cutNorm_overlay_le_of_pushforward`. Conditional expectation
(disintegration of `ν` along `(g₁, g₂)`) replaces the source weights `a, b` by `[0,1]`-valued
weights `abar, bbar` on the target, which are genuine test functions; the bound is then `le_cutNorm`. -/

/-- Disintegration along a measurable map `h : Z → Ω`. With `ξ := ν.map (fun z => (h z, z))`,
    `π = ξ.fst = ν.map h`, and `ρ = ξ.condKernel`, the integral of `z ↦ Φ (h z) z` against `ν`
    factors as `∫_ω ∫_{z'} Φ ω z' dρ(ω) dπ`. We take `π, ρ` as explicit arguments (with the
    defining equalities) to keep the conclusion in clean folded form. -/
theorem integral_disintegrate_along {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [StandardBorelSpace Z] [Nonempty Z] (ν : Measure Z) [IsProbabilityMeasure ν]
    {h : Z → Ω} (hh : Measurable h) {Φ : Ω → Z → ℝ}
    (hΦ : Measurable (Function.uncurry Φ))
    (hint : Integrable (fun p : Ω × Z => Φ p.1 p.2) (ν.map (fun z => (h z, z))))
    (π : Measure Ω) [SFinite π] (ρ : Kernel Ω Z) [IsSFiniteKernel ρ]
    (hπρ : ν.map (fun z => (h z, z)) = π ⊗ₘ ρ) :
    ∫ z, Φ (h z) z ∂ν = ∫ ω, ∫ z', Φ ω z' ∂(ρ ω) ∂π := by
  -- ∫ z, Φ (h z) z dν = ∫ p, Φ p.1 p.2 d(ν.map (h,id))  (change of variables along (h, id))
  have hcov : ∫ p, Φ p.1 p.2 ∂(ν.map (fun z => (h z, z))) = ∫ z, Φ (h z) z ∂ν := by
    rw [integral_map (φ := fun z => (h z, z)) (f := fun p => Φ p.1 p.2)
      (hh.prodMk measurable_id).aemeasurable hΦ.aestronglyMeasurable]
  rw [← hcov, hπρ, Measure.integral_compProd (hπρ ▸ hint)]

/-- **Marginalization bound (isolated measure-theoretic core).** Let `ν` be a probability measure
    on a standard-Borel space `Z`, `g₁ : Z → Ω₁`, `g₂ : Z → Ω₂` measurable, and
    `π := ν.map (fun z => (g₁ z, g₂ z))` the induced coupling. For `[0,1]`-valued measurable
    weights `a, b : Z → ℝ`, the source integral of the overlaid difference is bounded by the
    cut-norm of the overlay over `π`:
      `|∫∫ (U(g₁ z₁, g₁ z₂) − W(g₂ z₁, g₂ z₂)) · a z₁ · b z₂ dν dν| ≤ cutNorm (overlay U W π)`.

    PROOF: disintegrate `ν` along the measurable map `(g₁, g₂) : Z → Ω₁ × Ω₂` via its conditional
    kernel `ρ` (`integral_disintegrate_along`; requires `Z` standard Borel). The conditional
    averages `abar(ω) = ∫ a dρ(ω)`, `bbar(ω) = ∫ b dρ(ω)` are `[0,1]`-valued measurable functions
    on `Ω₁ × Ω₂` (genuine test functions). Disintegrating the inner then outer integral and using
    Fubini rewrites the source double integral as
      `∫∫ (U(ω₁.1,ω₂.1) − W(ω₁.2,ω₂.2)) · abar ω₁ · bbar ω₂ dπ dπ`,
    whence `le_cutNorm`. -/
theorem cutNorm_overlay_le_of_pushforward {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    [Nonempty Z] (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (ν : Measure Z) [IsProbabilityMeasure ν]
    {g₁ : Z → Ω₁} {g₂ : Z → Ω₂} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    {a b : Z → ℝ} (ha : IsTestFun a) (hb : IsTestFun b)
    (π : Measure (Ω₁ × Ω₂)) [IsProbabilityMeasure π]
    (hπ : π = ν.map (fun z => (g₁ z, g₂ z))) :
    |∫ z, (U.toFun (g₁ z.1) (g₁ z.2) - W.toFun (g₂ z.1) (g₂ z.2)) * a z.1 * b z.2 ∂(ν.prod ν)|
      ≤ cutNorm (overlay U W π) := by
  classical
  -- The middle map and its `(image, point)` graph; disintegrate ν along it.
  set h : Z → Ω₁ × Ω₂ := fun z => (g₁ z, g₂ z) with hh_def
  have hh : Measurable h := hg₁.prodMk hg₂
  set χ : Measure ((Ω₁ × Ω₂) × Z) := ν.map (fun z => (h z, z)) with hχ
  haveI : IsProbabilityMeasure χ :=
    Measure.isProbabilityMeasure_map (hh.prodMk measurable_id).aemeasurable
  set ρ : Kernel (Ω₁ × Ω₂) Z := χ.condKernel with hρ
  haveI : IsMarkovKernel ρ := by rw [hρ]; infer_instance
  have hHm : Measurable (fun z : Z => (h z, z)) := hh.prodMk measurable_id
  have hχfst : χ.fst = π := by
    have e1 : χ.fst = χ.map Prod.fst := rfl
    rw [e1, hχ, Measure.map_map measurable_fst hHm, hπ, hh_def]
    rfl
  have hπρ : χ = π ⊗ₘ ρ := by
    have hd := χ.disintegrate χ.condKernel
    rw [hχfst] at hd
    rw [hρ]; exact hd.symm
  -- The conditionally-averaged test weights `abar, bbar`.
  set abar : Ω₁ × Ω₂ → ℝ := fun ω => ∫ z', a z' ∂(ρ ω) with habar
  set bbar : Ω₁ × Ω₂ → ℝ := fun ω => ∫ z', b z' ∂(ρ ω) with hbbar
  have habar_test : IsTestFun abar := by
    refine ⟨ha.measurable.stronglyMeasurable.integral_kernel.measurable, fun ω => ?_⟩
    constructor
    · exact integral_nonneg fun z' => ha.nonneg z'
    · calc abar ω ≤ ∫ _, (1 : ℝ) ∂(ρ ω) :=
            integral_mono (SymmKernel.integrable_of_bdd ha.measurable
              (C := 1) (fun z' => ha.abs_le_one z'))
              (integrable_const 1) (fun z' => ha.le_one z')
        _ = 1 := by simp
  have hbbar_test : IsTestFun bbar := by
    refine ⟨hb.measurable.stronglyMeasurable.integral_kernel.measurable, fun ω => ?_⟩
    constructor
    · exact integral_nonneg fun z' => hb.nonneg z'
    · calc bbar ω ≤ ∫ _, (1 : ℝ) ∂(ρ ω) :=
            integral_mono (SymmKernel.integrable_of_bdd hb.measurable
              (C := 1) (fun z' => hb.abs_le_one z'))
              (integrable_const 1) (fun z' => hb.le_one z')
        _ = 1 := by simp
  -- Abbreviate the bilinear overlaid difference.
  set F : (Ω₁ × Ω₂) → (Ω₁ × Ω₂) → ℝ :=
    fun p q => U.toFun p.1 q.1 - W.toFun p.2 q.2 with hF
  have hFm : Measurable (fun pq : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) => F pq.1 pq.2) := by
    have hU : Measurable (fun pq : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) => U.toFun pq.1.1 pq.2.1) :=
      U.meas'.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
    have hW : Measurable (fun pq : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) => W.toFun pq.1.2 pq.2.2) :=
      W.meas'.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
    exact hU.sub hW
  have hFbdd : ∀ p q, |F p q| ≤ U.toSymmKernel.bound + W.toSymmKernel.bound := fun p q =>
    (abs_sub _ _).trans (add_le_add (U.toSymmKernel.abs_le_bound _ _)
      (W.toSymmKernel.abs_le_bound _ _))
  have hBnn : (0 : ℝ) ≤ U.toSymmKernel.bound + W.toSymmKernel.bound :=
    add_nonneg U.toSymmKernel.bound_nonneg W.toSymmKernel.bound_nonneg
  -- Disintegrate the inner integral over `z₂` for fixed `ω₁`.
  have hinner : ∀ ω₁ : Ω₁ × Ω₂,
      ∫ z₂, F ω₁ (h z₂) * b z₂ ∂ν = ∫ ω₂, F ω₁ ω₂ * bbar ω₂ ∂π := by
    intro ω₁
    have hstep := integral_disintegrate_along ν hh
      (Φ := fun ω₂ z₂ => F ω₁ ω₂ * b z₂)
      (by
        have : Measurable (Function.uncurry fun ω₂ z₂ => F ω₁ ω₂ * b z₂) :=
          ((hFm.comp (measurable_const.prodMk measurable_fst)).mul
            (hb.measurable.comp measurable_snd))
        exact this)
      (by
        refine SymmKernel.integrable_of_bdd
          ((hFm.comp (measurable_const.prodMk measurable_fst)).mul
            (hb.measurable.comp measurable_snd))
          (C := U.toSymmKernel.bound + W.toSymmKernel.bound) (fun p => ?_)
        rw [abs_mul]
        calc |F ω₁ p.1| * |b p.2|
            ≤ (U.toSymmKernel.bound + W.toSymmKernel.bound) * 1 :=
              mul_le_mul (hFbdd _ _) (hb.abs_le_one _) (abs_nonneg _) hBnn
          _ = U.toSymmKernel.bound + W.toSymmKernel.bound := by ring)
      π ρ (hχ.symm.trans hπρ)
    -- hstep : ∫ z, F ω₁ (h z) * b z ∂ν = ∫ ω₂, ∫ z', F ω₁ ω₂ * b z' ∂ρ ω₂ ∂π
    rw [hstep]
    refine integral_congr_ae (ae_of_all _ fun ω₂ => ?_)
    simp only []
    rw [integral_const_mul]
  -- Disintegrate the outer integral over `z₁`.
  have houter :
      ∫ z₁, (∫ z₂, F (h z₁) (h z₂) * b z₂ ∂ν) * a z₁ ∂ν
        = ∫ ω₁, (∫ ω₂, F ω₁ ω₂ * bbar ω₂ ∂π) * abar ω₁ ∂π := by
    simp_rw [hinner]
    have hGmeas : Measurable
        (fun ω₁ : Ω₁ × Ω₂ => ∫ ω₂, F ω₁ ω₂ * bbar ω₂ ∂π) := by
      have : StronglyMeasurable (fun p : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) => F p.1 p.2 * bbar p.2) :=
        (hFm.mul (hbbar_test.measurable.comp measurable_snd)).stronglyMeasurable
      exact (this.integral_prod_right).measurable
    have hstep := integral_disintegrate_along ν hh
      (Φ := fun ω₁ z₁ => (∫ ω₂, F ω₁ ω₂ * bbar ω₂ ∂π) * a z₁)
      (by
        exact (hGmeas.comp measurable_fst).mul (ha.measurable.comp measurable_snd))
      (by
        refine SymmKernel.integrable_of_bdd
          ((hGmeas.comp measurable_fst).mul (ha.measurable.comp measurable_snd))
          (C := U.toSymmKernel.bound + W.toSymmKernel.bound) (fun p => ?_)
        rw [abs_mul]
        calc |∫ ω₂, F p.1 ω₂ * bbar ω₂ ∂π| * |a p.2|
            ≤ (U.toSymmKernel.bound + W.toSymmKernel.bound) * 1 := by
              refine mul_le_mul ?_ (ha.abs_le_one _) (abs_nonneg _) hBnn
              calc |∫ ω₂, F p.1 ω₂ * bbar ω₂ ∂π|
                  ≤ ∫ ω₂, |F p.1 ω₂ * bbar ω₂| ∂π := by
                    simpa [Real.norm_eq_abs] using
                      norm_integral_le_integral_norm (μ := π) (fun ω₂ => F p.1 ω₂ * bbar ω₂)
                _ ≤ ∫ _, (U.toSymmKernel.bound + W.toSymmKernel.bound) ∂π := by
                    refine integral_mono ?_ (integrable_const _) (fun ω₂ => ?_)
                    · refine SymmKernel.integrable_of_bdd
                        ((hFm.comp (measurable_const.prodMk measurable_id)).mul
                          hbbar_test.measurable) (C := U.toSymmKernel.bound + W.toSymmKernel.bound)
                        (fun ω₂ => ?_) |>.abs
                      rw [abs_mul]
                      calc |F p.1 ω₂| * |bbar ω₂|
                          ≤ (U.toSymmKernel.bound + W.toSymmKernel.bound) * 1 :=
                            mul_le_mul (hFbdd _ _) (hbbar_test.abs_le_one _) (abs_nonneg _)
                              hBnn
                        _ = U.toSymmKernel.bound + W.toSymmKernel.bound := by ring
                    · rw [abs_mul]
                      calc |F p.1 ω₂| * |bbar ω₂|
                          ≤ (U.toSymmKernel.bound + W.toSymmKernel.bound) * 1 :=
                            mul_le_mul (hFbdd _ _) (hbbar_test.abs_le_one _) (abs_nonneg _)
                              hBnn
                        _ = U.toSymmKernel.bound + W.toSymmKernel.bound := by ring
                _ = U.toSymmKernel.bound + W.toSymmKernel.bound := by simp
          _ = U.toSymmKernel.bound + W.toSymmKernel.bound := by ring)
      π ρ (hχ.symm.trans hπρ)
    rw [hstep]
    refine integral_congr_ae (ae_of_all _ fun ω₁ => ?_)
    simp only []
    rw [integral_const_mul]
  -- Assemble: the double integral over ν×ν equals the overlay integral over π×π.
  haveI : IsProbabilityMeasure ν := ‹_›
  have hdouble :
      ∫ z, (U.toFun (g₁ z.1) (g₁ z.2) - W.toFun (g₂ z.1) (g₂ z.2)) * a z.1 * b z.2 ∂(ν.prod ν)
        = ∫ ω, (overlay U W π).toFun ω.1 ω.2 * abar ω.1 * bbar ω.2 ∂(π.prod π) := by
    -- Fubini both sides into iterated integrals, then use hinner / houter.
    have hintν : Integrable
        (fun z : Z × Z =>
          (U.toFun (g₁ z.1) (g₁ z.2) - W.toFun (g₂ z.1) (g₂ z.2)) * a z.1 * b z.2) (ν.prod ν) := by
      refine SymmKernel.integrable_of_bdd ?_ (C := U.toSymmKernel.bound + W.toSymmKernel.bound)
        (fun z => ?_)
      · have hUm : Measurable (fun z : Z × Z => U.toFun (g₁ z.1) (g₁ z.2)) :=
          U.meas'.comp ((hg₁.comp measurable_fst).prodMk (hg₁.comp measurable_snd))
        have hWm : Measurable (fun z : Z × Z => W.toFun (g₂ z.1) (g₂ z.2)) :=
          W.meas'.comp ((hg₂.comp measurable_fst).prodMk (hg₂.comp measurable_snd))
        exact ((hUm.sub hWm).mul (ha.measurable.comp measurable_fst)).mul
          (hb.measurable.comp measurable_snd)
      · rw [abs_mul, abs_mul]
        calc |U.toFun (g₁ z.1) (g₁ z.2) - W.toFun (g₂ z.1) (g₂ z.2)| * |a z.1| * |b z.2|
            ≤ (U.toSymmKernel.bound + W.toSymmKernel.bound) * 1 * 1 :=
              mul_le_mul (mul_le_mul (hFbdd (h z.1) (h z.2)) (ha.abs_le_one _) (abs_nonneg _)
                hBnn) (hb.abs_le_one _) (abs_nonneg _) (mul_nonneg hBnn zero_le_one)
          _ = U.toSymmKernel.bound + W.toSymmKernel.bound := by ring
    have hintπ : Integrable
        (fun ω : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) =>
          (overlay U W π).toFun ω.1 ω.2 * abar ω.1 * bbar ω.2) (π.prod π) :=
      integrable_integrand (overlay U W π) habar_test hbbar_test
    rw [integral_prod _ hintν, integral_prod _ hintπ]
    -- LHS inner: ∫ z₂ ... ; recognise F (h z.1) (h z₂).
    have hLHS : ∀ z₁ : Z,
        ∫ z₂, (U.toFun (g₁ z₁) (g₁ z₂) - W.toFun (g₂ z₁) (g₂ z₂)) * a z₁ * b z₂ ∂ν
          = (∫ z₂, F (h z₁) (h z₂) * b z₂ ∂ν) * a z₁ := by
      intro z₁
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun z₂ => ?_)
      simp only [hF, hh_def]; ring
    simp_rw [hLHS]
    rw [houter]
    refine integral_congr_ae (ae_of_all _ fun ω₁ => ?_)
    simp only []
    rw [mul_comm, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω₂ => ?_)
    simp only [overlay_apply, hF]; ring
  rw [hdouble]
  exact le_cutNorm (overlay U W π) habar_test hbbar_test

/-- Pushforward identity: the `(x₁, x₂)`-projection of the glued triple is `π₁₂`. -/
theorem gluedTriple_map_x1x2 {π₁₂ : Measure (Ω₁ × Ω₂)} {π₂₃ : Measure (Ω₂ × Ω₃)}
    [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] (h₁₂ : IsCoupling μ₁ μ₂ π₁₂) :
    (gluedTriple μ₂ π₁₂ π₂₃).map (fun z => (z.2.1, z.1)) = π₁₂ := by
  have hcomp : (fun z : Ω₂ × Ω₁ × Ω₃ => (z.2.1, z.1))
      = Prod.swap ∘ (Prod.map id Prod.fst) := rfl
  rw [hcomp, ← Measure.map_map measurable_swap (by fun_prop), gluedTriple_map_left h₁₂,
    Measure.map_map measurable_swap measurable_swap]
  simp

/-- Pushforward identity: the `(x₂, x₃)`-projection of the glued triple is `π₂₃`. -/
theorem gluedTriple_map_x2x3 {π₁₂ : Measure (Ω₁ × Ω₂)} {π₂₃ : Measure (Ω₂ × Ω₃)}
    [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃] (h₂₃ : IsCoupling μ₂ μ₃ π₂₃) :
    (gluedTriple μ₂ π₁₂ π₂₃).map (fun z => (z.1, z.2.2)) = π₂₃ := by
  have hcomp : (fun z : Ω₂ × Ω₁ × Ω₃ => (z.1, z.2.2)) = Prod.map id Prod.snd := rfl
  rw [hcomp, gluedTriple_map_right h₂₃]

/-- **The telescoping bound.** `cutNorm (overlay U V (gluedCoupling …)) ≤
    cutNorm (overlay U W π₁₂) + cutNorm (overlay W V π₂₃)`.

    The overlaid difference `U − V` telescopes through the middle coordinate as
    `(U − W) + (W − V)`; change of variables to the glued triple `γ`, subadditivity of `|·|`, and
    two applications of `cutNorm_overlay_le_of_pushforward` (one toward `π₁₂`, one toward `π₂₃`)
    give the bound. -/
theorem cutNorm_overlay_gluedCoupling_le {μ₃ : Measure Ω₃} [IsProbabilityMeasure μ₃]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (V : Graphon Ω₃ μ₃)
    {π₁₂ : Measure (Ω₁ × Ω₂)} {π₂₃ : Measure (Ω₂ × Ω₃)}
    (h₁₂ : IsCoupling μ₁ μ₂ π₁₂) (h₂₃ : IsCoupling μ₂ μ₃ π₂₃) :
    haveI : IsProbabilityMeasure π₁₂ := h₁₂.isProbabilityMeasure
    haveI : IsProbabilityMeasure π₂₃ := h₂₃.isProbabilityMeasure
    haveI : IsProbabilityMeasure (gluedCoupling μ₂ π₁₂ π₂₃) := inferInstance
    cutNorm (overlay U V (gluedCoupling μ₂ π₁₂ π₂₃))
      ≤ cutNorm (overlay U W π₁₂) + cutNorm (overlay W V π₂₃) := by
  haveI hp12 : IsProbabilityMeasure π₁₂ := h₁₂.isProbabilityMeasure
  haveI hp23 : IsProbabilityMeasure π₂₃ := h₂₃.isProbabilityMeasure
  set γ := gluedTriple μ₂ π₁₂ π₂₃ with hγ
  haveI : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
  set π₁₃ := gluedCoupling μ₂ π₁₂ π₂₃ with hπ₁₃
  haveI : IsProbabilityMeasure π₁₃ := by rw [hπ₁₃]; infer_instance
  -- Abbreviations for the source-coordinate accessors.
  let f₁ : Ω₂ × Ω₁ × Ω₃ → Ω₁ := fun z => z.2.1
  let f₂ : Ω₂ × Ω₁ × Ω₃ → Ω₂ := fun z => z.1
  let f₃ : Ω₂ × Ω₁ × Ω₃ → Ω₃ := fun z => z.2.2
  have hf₁ : Measurable f₁ := measurable_fst.comp measurable_snd
  have hf₂ : Measurable f₂ := measurable_fst
  have hf₃ : Measurable f₃ := measurable_snd.comp measurable_snd
  rw [cutNorm]
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      -- Change of variables π₁₃ × π₁₃ → γ × γ along (Prod.snd, Prod.snd).
      have hmap : (π₁₃.prod π₁₃) = (γ.prod γ).map (Prod.map Prod.snd Prod.snd) := by
        rw [hπ₁₃, gluedCoupling, Measure.map_prod_map _ _ measurable_snd measurable_snd]
      rw [hmap, integral_map (by fun_prop)
        ((measurable_integrand (overlay U V π₁₃) hu.measurable
          hv.measurable).aestronglyMeasurable)]
      -- The two telescope-piece integrands and the pulled-back weights.
      set a : Ω₂ × Ω₁ × Ω₃ → ℝ := fun z => u (z.2) with ha_def
      set b : Ω₂ × Ω₁ × Ω₃ → ℝ := fun z => v (z.2) with hb_def
      have ha : IsTestFun a := ⟨hu.measurable.comp measurable_snd, fun z => hu.2 _⟩
      have hb : IsTestFun b := ⟨hv.measurable.comp measurable_snd, fun z => hv.2 _⟩
      -- Pointwise telescope identity on γ × γ.
      have htel : ∀ z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃),
          (overlay U V π₁₃).toFun (Prod.map Prod.snd Prod.snd z).1
              (Prod.map Prod.snd Prod.snd z).2 * u (Prod.map Prod.snd Prod.snd z).1
              * v (Prod.map Prod.snd Prod.snd z).2
            = ((U.toFun (f₁ z.1) (f₁ z.2) - W.toFun (f₂ z.1) (f₂ z.2)) * a z.1 * b z.2)
              + ((W.toFun (f₂ z.1) (f₂ z.2) - V.toFun (f₃ z.1) (f₃ z.2)) * a z.1 * b z.2) := by
        intro z; simp only [Prod.map_fst, Prod.map_snd, overlay_apply, f₁, f₂, f₃, a, b]; ring
      rw [integral_congr_ae (ae_of_all _ htel)]
      -- Split the integral of a sum (both pieces bounded ⇒ integrable).
      have hbddU := U.toSymmKernel.bound_nonneg
      have hbddW := W.toSymmKernel.bound_nonneg
      have hbddV := V.toSymmKernel.bound_nonneg
      have hUm : Measurable (fun z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃) =>
          U.toFun (f₁ z.1) (f₁ z.2)) := U.meas'.comp ((hf₁.comp measurable_fst).prodMk
            (hf₁.comp measurable_snd))
      have hWm : Measurable (fun z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃) =>
          W.toFun (f₂ z.1) (f₂ z.2)) := W.meas'.comp ((hf₂.comp measurable_fst).prodMk
            (hf₂.comp measurable_snd))
      have hVm : Measurable (fun z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃) =>
          V.toFun (f₃ z.1) (f₃ z.2)) := V.meas'.comp ((hf₃.comp measurable_fst).prodMk
            (hf₃.comp measurable_snd))
      have ham : Measurable (fun z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃) => a z.1) :=
        ha.measurable.comp measurable_fst
      have hbm : Measurable (fun z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃) => b z.2) :=
        hb.measurable.comp measurable_snd
      have hint1 : Integrable
          (fun z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃) =>
            (U.toFun (f₁ z.1) (f₁ z.2) - W.toFun (f₂ z.1) (f₂ z.2)) * a z.1 * b z.2)
          (γ.prod γ) := by
        refine SymmKernel.integrable_of_bdd
          (((hUm.sub hWm).mul ham).mul hbm)
          (C := U.toSymmKernel.bound + W.toSymmKernel.bound) (fun z => ?_)
        calc |(U.toFun (f₁ z.1) (f₁ z.2) - W.toFun (f₂ z.1) (f₂ z.2)) * a z.1 * b z.2|
            = |U.toFun (f₁ z.1) (f₁ z.2) - W.toFun (f₂ z.1) (f₂ z.2)| * |a z.1| * |b z.2| := by
              rw [abs_mul, abs_mul]
          _ ≤ (U.toSymmKernel.bound + W.toSymmKernel.bound) * 1 * 1 :=
              mul_le_mul (mul_le_mul ((abs_sub _ _).trans (add_le_add
                (U.toSymmKernel.abs_le_bound _ _) (W.toSymmKernel.abs_le_bound _ _)))
                (ha.abs_le_one _) (abs_nonneg _) (by positivity)) (hb.abs_le_one _)
                (abs_nonneg _) (by positivity)
          _ = U.toSymmKernel.bound + W.toSymmKernel.bound := by ring
      have hint2 : Integrable
          (fun z : (Ω₂ × Ω₁ × Ω₃) × (Ω₂ × Ω₁ × Ω₃) =>
            (W.toFun (f₂ z.1) (f₂ z.2) - V.toFun (f₃ z.1) (f₃ z.2)) * a z.1 * b z.2)
          (γ.prod γ) := by
        refine SymmKernel.integrable_of_bdd
          (((hWm.sub hVm).mul ham).mul hbm)
          (C := W.toSymmKernel.bound + V.toSymmKernel.bound) (fun z => ?_)
        calc |(W.toFun (f₂ z.1) (f₂ z.2) - V.toFun (f₃ z.1) (f₃ z.2)) * a z.1 * b z.2|
            = |W.toFun (f₂ z.1) (f₂ z.2) - V.toFun (f₃ z.1) (f₃ z.2)| * |a z.1| * |b z.2| := by
              rw [abs_mul, abs_mul]
          _ ≤ (W.toSymmKernel.bound + V.toSymmKernel.bound) * 1 * 1 :=
              mul_le_mul (mul_le_mul ((abs_sub _ _).trans (add_le_add
                (W.toSymmKernel.abs_le_bound _ _) (V.toSymmKernel.abs_le_bound _ _)))
                (ha.abs_le_one _) (abs_nonneg _) (by positivity)) (hb.abs_le_one _)
                (abs_nonneg _) (by positivity)
          _ = W.toSymmKernel.bound + V.toSymmKernel.bound := by ring
      rw [integral_add hint1 hint2]
      -- Each piece is bounded by the corresponding cut-norm via the marginalization lemma.
      have hpf1 : π₁₂ = γ.map (fun z => (f₁ z, f₂ z)) := (gluedTriple_map_x1x2 h₁₂).symm
      have hpf2 : π₂₃ = γ.map (fun z => (f₂ z, f₃ z)) := (gluedTriple_map_x2x3 h₂₃).symm
      have hbound1 := cutNorm_overlay_le_of_pushforward U W γ hf₁ hf₂ ha hb π₁₂ hpf1
      have hbound2 := cutNorm_overlay_le_of_pushforward W V γ hf₂ hf₃ ha hb π₂₃ hpf2
      exact (abs_add_le _ _).trans (add_le_add hbound1 hbound2)
    · rw [ciSup_pos hu, ciSup_neg hv]
      exact le_trans (by simp) (add_nonneg (cutNorm_nonneg _) (cutNorm_nonneg _))
  · rw [ciSup_neg hu]
    exact le_trans (by simp) (add_nonneg (cutNorm_nonneg _) (cutNorm_nonneg _))

/-! ### The triangle inequality -/

/-- **Item 7 (the cut metric triangle inequality):** `cutDist U V ≤ cutDist U W + cutDist W V`,
    via the coupling Gluing Lemma. For any couplings `π₁₂` of `(μ₁, μ₂)` and `π₂₃` of `(μ₂, μ₃)`,
    `gluedCoupling` glues them over the common middle marginal `μ₂` into a coupling of `(μ₁, μ₃)`
    realizing `‖overlay U V π₁₃‖□ ≤ ‖overlay U W π₁₂‖□ + ‖overlay W V π₂₃‖□`; taking infima over the
    two couplings gives the result. The `StandardBorelSpace` hypotheses (carried on the section)
    power the disintegration along `μ₂`. -/
theorem cutDist_triangle {μ₃ : Measure Ω₃} [IsProbabilityMeasure μ₃]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (V : Graphon Ω₃ μ₃) :
    cutDist U V ≤ cutDist U W + cutDist W V := by
  -- For any couplings `π₁₂, π₂₃`, the glued coupling bounds `cutDist U V`.
  have key : ∀ (π₁₂ : {π : Measure (Ω₁ × Ω₂) // IsCoupling μ₁ μ₂ π})
      (π₂₃ : {π : Measure (Ω₂ × Ω₃) // IsCoupling μ₂ μ₃ π}),
      cutDist U V ≤ cutDistFun U W π₁₂ + cutDistFun W V π₂₃ := by
    rintro ⟨π₁₂, h₁₂⟩ ⟨π₂₃, h₂₃⟩
    haveI : IsProbabilityMeasure π₁₂ := h₁₂.isProbabilityMeasure
    haveI : IsProbabilityMeasure π₂₃ := h₂₃.isProbabilityMeasure
    calc cutDist U V
        ≤ cutDistFun U V ⟨gluedCoupling μ₂ π₁₂ π₂₃, gluedCoupling_isCoupling h₁₂ h₂₃⟩ :=
          cutDist_le_of_coupling U V _
      _ = cutNorm (overlay U V (gluedCoupling μ₂ π₁₂ π₂₃)) := rfl
      _ ≤ cutNorm (overlay U W π₁₂) + cutNorm (overlay W V π₂₃) :=
          cutNorm_overlay_gluedCoupling_le U W V h₁₂ h₂₃
      _ = cutDistFun U W ⟨π₁₂, h₁₂⟩ + cutDistFun W V ⟨π₂₃, h₂₃⟩ := rfl
  -- Step A: for fixed `π₁₂`, take the infimum over `π₂₃`.
  have stepA : ∀ π₁₂ : {π : Measure (Ω₁ × Ω₂) // IsCoupling μ₁ μ₂ π},
      cutDist U V ≤ cutDistFun U W π₁₂ + cutDist W V := by
    intro π₁₂
    have : cutDist U V - cutDistFun U W π₁₂ ≤ cutDist W V :=
      le_ciInf fun π₂₃ => by linarith [key π₁₂ π₂₃]
    linarith
  -- Step B: take the infimum over `π₁₂`.
  have : cutDist U V - cutDist W V ≤ cutDist U W :=
    le_ciInf fun π₁₂ => by linarith [stepA π₁₂]
  linarith

end Gluing

end Graphons
