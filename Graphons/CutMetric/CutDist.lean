/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG targets (random-fields roadmap, layer L9 — dense graph limits):
  C11303 "Cut distance δ□" (def), C12898/C13168 "Cut metric via couplings".
  Sources: Lovász, "Large Networks and Graph Limits" (2012); Borgs–Chayes–Lovász–
  Sós–Vesztergombi (2007); Janson (2010).

The **cut distance** between graphons `U` on `(Ω₁, μ₁)` and `W` on `(Ω₂, μ₂)`, defined via
**couplings** (DESIGN.md §4/§8). A coupling is a probability measure `π` on `Ω₁ × Ω₂` whose
marginals are `μ₁` and `μ₂`. Given a coupling `π`, the *overlaid difference* is the symmetric
kernel on `Ω₁ × Ω₂`
  D p q = U (p.1) (q.1) - W (p.2) (q.2),
which is a `SymmKernel (Ω₁ × Ω₂) π` (symmetry/measurability/boundedness inherited from `U`, `W`).
The cut distance is the infimum, over couplings `π`, of `cutNorm (overlay U W π)`.

As with `cutNorm`, this is a genuine `⨅` over the reals, so we must avoid the junk-`sInf`-`= 0`
trap from the other side: the family is bounded **below** by `0` (each `cutNorm ≥ 0`) and the
index — couplings of `μ₁, μ₂` — is **nonempty** (the product measure `μ₁ ×ˢ μ₂` is a coupling).
All order facts go through the conditionally-complete-lattice API (`le_ciInf`, `ciInf_le`,
`BddBelow`).
-/
import Graphons.CutMetric.CutNorm

open MeasureTheory

namespace Graphons

variable {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]

/-! ### Couplings -/

/-- A **coupling** of measures `μ₁` on `Ω₁` and `μ₂` on `Ω₂` is a measure `π` on `Ω₁ × Ω₂`
    whose two marginals (pushforwards under the projections) are `μ₁` and `μ₂`. -/
def IsCoupling (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (π : Measure (Ω₁ × Ω₂)) : Prop :=
  π.map Prod.fst = μ₁ ∧ π.map Prod.snd = μ₂

namespace IsCoupling

theorem map_fst {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {π : Measure (Ω₁ × Ω₂)}
    (h : IsCoupling μ₁ μ₂ π) : π.map Prod.fst = μ₁ := h.1

theorem map_snd {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {π : Measure (Ω₁ × Ω₂)}
    (h : IsCoupling μ₁ μ₂ π) : π.map Prod.snd = μ₂ := h.2

/-- A coupling of probability measures is itself a probability measure: its total mass equals the
    total mass of either marginal, namely `1`. -/
theorem isProbabilityMeasure {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {π : Measure (Ω₁ × Ω₂)}
    [IsProbabilityMeasure μ₁] (h : IsCoupling μ₁ μ₂ π) : IsProbabilityMeasure π := by
  refine ⟨?_⟩
  have h1 : π Set.univ = μ₁ Set.univ := by
    conv_lhs => rw [← Set.preimage_univ (f := Prod.fst),
      ← Measure.map_apply measurable_fst MeasurableSet.univ, h.1]
  rw [h1, measure_univ]

/-- The **product measure** `μ₁ ×ˢ μ₂` is a coupling of `μ₁` and `μ₂` (the *independent* coupling),
    so the index set of couplings is nonempty. -/
theorem prod (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] : IsCoupling μ₁ μ₂ (μ₁.prod μ₂) :=
  ⟨Measure.map_fst_prod.trans (by rw [measure_univ, one_smul]),
   Measure.map_snd_prod.trans (by rw [measure_univ, one_smul])⟩

/-- The pushforward of a coupling `π` of `(μ₁, μ₂)` under `Prod.swap` is a coupling of `(μ₂, μ₁)`. -/
theorem swap {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {π : Measure (Ω₁ × Ω₂)}
    (h : IsCoupling μ₁ μ₂ π) : IsCoupling μ₂ μ₁ (π.map Prod.swap) := by
  constructor
  · rw [Measure.map_map measurable_fst measurable_swap]; exact h.2
  · rw [Measure.map_map measurable_snd measurable_swap]; exact h.1

end IsCoupling

/-! ### The overlay kernel -/

/-- The **overlaid difference** of graphons `U` on `(Ω₁, μ₁)` and `W` on `(Ω₂, μ₂)`, viewed as a
    symmetric kernel on the coupled space `(Ω₁ × Ω₂, π)`:
      `overlay U W π (p) (q) = U (p.1) (q.1) - W (p.2) (q.2)`.
    Symmetry comes from `U.symm'`/`W.symm'`, measurability from the projections, and the bound
    from `U.bound + W.bound`. -/
noncomputable def overlay {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (U : Graphon Ω₁ μ₁)
    (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂)) : SymmKernel (Ω₁ × Ω₂) π where
  toFun p q := U.toFun p.1 q.1 - W.toFun p.2 q.2
  symm' p q := by rw [U.symm' p.1 q.1, W.symm' p.2 q.2]
  meas' := by
    have hU : Measurable (fun pq : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) => U.toFun pq.1.1 pq.2.1) :=
      U.meas'.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
    have hW : Measurable (fun pq : (Ω₁ × Ω₂) × (Ω₁ × Ω₂) => W.toFun pq.1.2 pq.2.2) :=
      W.meas'.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
    exact hU.sub hW
  bdd' := by
    refine ⟨U.toSymmKernel.bound + W.toSymmKernel.bound, fun p q => ?_⟩
    calc |U.toFun p.1 q.1 - W.toFun p.2 q.2|
        ≤ |U.toFun p.1 q.1| + |W.toFun p.2 q.2| := abs_sub _ _
      _ ≤ U.toSymmKernel.bound + W.toSymmKernel.bound :=
          add_le_add (U.toSymmKernel.abs_le_bound p.1 q.1) (W.toSymmKernel.abs_le_bound p.2 q.2)

@[simp] theorem overlay_apply {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (U : Graphon Ω₁ μ₁)
    (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂)) (p q : Ω₁ × Ω₂) :
    (overlay U W π).toFun p q = U.toFun p.1 q.1 - W.toFun p.2 q.2 := rfl

/-! ### Cut distance -/

/-- The cut-norm of the overlay over a coupling `π`, as a function of the coupling. We package the
    couplings as a subtype so the `⨅` ranges over a genuine (nonempty, bounded-below) index. -/
noncomputable def cutDistFun {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (U : Graphon Ω₁ μ₁)
    (W : Graphon Ω₂ μ₂) (π : {π : Measure (Ω₁ × Ω₂) // IsCoupling μ₁ μ₂ π}) : ℝ :=
  cutNorm (overlay U W π.1)

/-- The **cut distance** between graphons `U` on `(Ω₁, μ₁)` and `W` on `(Ω₂, μ₂)`:
      `δ□(U, W) = inf over couplings π of ‖overlay U W π‖□`.
    The index (couplings of `μ₁, μ₂`) is nonempty via the product coupling, and the family is
    bounded below by `0` (each `cutNorm ≥ 0`), so this is a genuine infimum and not junk. -/
noncomputable def cutDist {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : ℝ :=
  ⨅ π : {π : Measure (Ω₁ × Ω₂) // IsCoupling μ₁ μ₂ π}, cutDistFun U W π

section CutDist

variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃]

/-- The couplings subtype is nonempty (the product coupling). -/
instance instNonemptyCoupling : Nonempty {π : Measure (Ω₁ × Ω₂) // IsCoupling μ₁ μ₂ π} :=
  ⟨⟨μ₁.prod μ₂, IsCoupling.prod μ₁ μ₂⟩⟩

/-- Each coupling, made a probability measure, lets `cutNorm` use its `[IsProbabilityMeasure]`
    machinery. (Helper to provide the instance when computing `cutDistFun`.) -/
theorem cutDistFun_nonneg (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (π : {π : Measure (Ω₁ × Ω₂) // IsCoupling μ₁ μ₂ π}) : 0 ≤ cutDistFun U W π := by
  haveI : IsProbabilityMeasure π.1 := π.2.isProbabilityMeasure
  exact cutNorm_nonneg _

/-- The cut-distance family is bounded below by `0`. -/
theorem bddBelow_cutDist (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    BddBelow (Set.range (cutDistFun U W)) := by
  refine ⟨0, ?_⟩
  rintro a ⟨π, rfl⟩
  exact cutDistFun_nonneg U W π

/-- **Item 4 (non-negotiable):** `0 ≤ cutDist U W`. -/
theorem cutDist_nonneg (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : 0 ≤ cutDist U W :=
  le_ciInf fun π => cutDistFun_nonneg U W π

/-- A single coupling gives an upper bound on `cutDist`. -/
theorem cutDist_le_of_coupling (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (π : {π : Measure (Ω₁ × Ω₂) // IsCoupling μ₁ μ₂ π}) :
    cutDist U W ≤ cutDistFun U W π :=
  ciInf_le (bddBelow_cutDist U W) π

/-! #### Symmetry -/

/-- Change-of-variables identity behind `cutNorm_overlay_swap`: the cut-norm integrand for the
    overlay of `W, U` over the swapped coupling `π.map Prod.swap`, at test functions `u, v`, is the
    *negative* of the integrand for the overlay of `U, W` over `π`, at the swapped test functions
    `u ∘ swap`, `v ∘ swap`. (The overlay difference flips sign under swapping the two graphons.) -/
theorem integral_overlay_swap (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    {π : Measure (Ω₁ × Ω₂)} (hπ : IsCoupling μ₁ μ₂ π) {u v : Ω₂ × Ω₁ → ℝ}
    (hu : Measurable u) (hv : Measurable v) :
    ∫ p, (overlay W U (π.map Prod.swap)).toFun p.1 p.2 * u p.1 * v p.2
        ∂((π.map Prod.swap).prod (π.map Prod.swap))
      = - ∫ p, (overlay U W π).toFun p.1 p.2 * (u (Prod.swap p.1)) * (v (Prod.swap p.2))
        ∂(π.prod π) := by
  haveI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  haveI : IsProbabilityMeasure (π.map Prod.swap) :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  have hmap : (π.map Prod.swap).prod (π.map Prod.swap)
      = (π.prod π).map (Prod.map Prod.swap Prod.swap) := by
    rw [Measure.map_prod_map _ _ measurable_swap measurable_swap]
  rw [hmap, integral_map]
  · rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [Prod.map_fst, Prod.map_snd, overlay_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  · exact (Measurable.prodMap measurable_swap measurable_swap).aemeasurable
  · exact (measurable_integrand (overlay W U (π.map Prod.swap)) hu hv).aestronglyMeasurable

theorem cutNorm_overlay_swap (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    {π : Measure (Ω₁ × Ω₂)} (hπ : IsCoupling μ₁ μ₂ π) :
    cutNorm (overlay W U (π.map Prod.swap)) = cutNorm (overlay U W π) := by
  haveI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  haveI : IsProbabilityMeasure (π.map Prod.swap) :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  -- Both `cutNorm`s have the same value: the integrand families agree up to sign (absorbed by `|·|`)
  -- under the test-function bijection `u ↦ u ∘ Prod.swap`.
  apply le_antisymm
  · refine ciSup_le fun u => ciSup_le fun v => ?_
    by_cases hu : IsTestFun u
    · by_cases hv : IsTestFun v
      · rw [ciSup_pos hu, ciSup_pos hv]
        have huv := le_cutNorm (overlay U W π)
          (u := fun p => u (Prod.swap p)) (v := fun p => v (Prod.swap p))
          ⟨hu.measurable.comp measurable_swap, fun x => hu.2 (Prod.swap x)⟩
          ⟨hv.measurable.comp measurable_swap, fun x => hv.2 (Prod.swap x)⟩
        refine le_trans (le_of_eq ?_) huv
        rw [integral_overlay_swap U W hπ hu.measurable hv.measurable, abs_neg]
      · rw [ciSup_pos hu, ciSup_neg hv]; simpa using cutNorm_nonneg _
    · rw [ciSup_neg hu]; simpa using cutNorm_nonneg _
  · refine ciSup_le fun u => ciSup_le fun v => ?_
    by_cases hu : IsTestFun u
    · by_cases hv : IsTestFun v
      · rw [ciSup_pos hu, ciSup_pos hv]
        have huv := le_cutNorm (overlay W U (π.map Prod.swap))
          (u := fun p => u (Prod.swap p)) (v := fun p => v (Prod.swap p))
          ⟨hu.measurable.comp measurable_swap, fun x => hu.2 (Prod.swap x)⟩
          ⟨hv.measurable.comp measurable_swap, fun x => hv.2 (Prod.swap x)⟩
        refine le_trans (le_of_eq ?_) huv
        -- |∫ overlay U W π · u · v| = |∫ overlay W U (π.map swap) · (u∘swap) · (v∘swap)|.
        rw [integral_overlay_swap U W hπ (u := fun p => u (Prod.swap p))
          (v := fun p => v (Prod.swap p)) (hu.measurable.comp measurable_swap)
          (hv.measurable.comp measurable_swap), abs_neg]
        simp only [Prod.swap_swap]
      · rw [ciSup_pos hu, ciSup_neg hv]; simpa using cutNorm_nonneg _
    · rw [ciSup_neg hu]; simpa using cutNorm_nonneg _

/-- **Item 5:** the cut distance is symmetric. -/
theorem cutDist_comm (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    cutDist U W = cutDist W U := by
  apply le_antisymm
  · refine le_ciInf fun π => ?_
    -- π : coupling of μ₂, μ₁; swap it to a coupling of μ₁, μ₂.
    refine le_trans (cutDist_le_of_coupling U W
      ⟨π.1.map Prod.swap, π.2.swap⟩) ?_
    exact le_of_eq (cutNorm_overlay_swap W U π.2)
  · refine le_ciInf fun π => ?_
    refine le_trans (cutDist_le_of_coupling W U
      ⟨π.1.map Prod.swap, π.2.swap⟩) ?_
    exact le_of_eq (cutNorm_overlay_swap U W π.2)

/-! #### Self distance is zero (diagonal coupling) -/

/-- The **diagonal coupling** of `μ` with itself: the pushforward of `μ` under `x ↦ (x, x)`. -/
noncomputable def diagCoupling (μ : Measure Ω₁) : Measure (Ω₁ × Ω₁) :=
  μ.map (fun x => (x, x))

theorem isCoupling_diagCoupling (μ : Measure Ω₁) [IsProbabilityMeasure μ] :
    IsCoupling μ μ (diagCoupling μ) := by
  have hdiag : Measurable (fun x : Ω₁ => (x, x)) := measurable_id.prodMk measurable_id
  constructor
  · rw [diagCoupling, Measure.map_map measurable_fst hdiag]
    exact Measure.map_id'
  · rw [diagCoupling, Measure.map_map measurable_snd hdiag]
    exact Measure.map_id'

/-- The overlay of `U` with itself over the diagonal coupling has cut norm `0`: on the diagonal,
    `U p.1 q.1 - U p.2 q.2 = U a c - U a c = 0`, so every integrand vanishes. -/
theorem cutNorm_overlay_diag (U : Graphon Ω₁ μ₁) :
    cutNorm (overlay U U (diagCoupling μ₁)) = 0 := by
  haveI : IsProbabilityMeasure (diagCoupling μ₁) :=
    (isCoupling_diagCoupling μ₁).isProbabilityMeasure
  have hdiag : Measurable (fun x : Ω₁ => (x, x)) := measurable_id.prodMk measurable_id
  refine le_antisymm ?_ (cutNorm_nonneg _)
  rw [cutNorm]
  refine ciSup_le fun u => ciSup_le fun v => ?_
  by_cases hu : IsTestFun u
  · by_cases hv : IsTestFun v
    · rw [ciSup_pos hu, ciSup_pos hv]
      -- the integral is 0; we compute it via change of variables to `μ₁.prod μ₁`.
      have hzero : ∫ p, (overlay U U (diagCoupling μ₁)).toFun p.1 p.2 * u p.1 * v p.2
          ∂((diagCoupling μ₁).prod (diagCoupling μ₁)) = 0 := by
        have hmap : (diagCoupling μ₁).prod (diagCoupling μ₁)
            = (μ₁.prod μ₁).map (Prod.map (fun x => (x, x)) (fun x => (x, x))) := by
          rw [diagCoupling, Measure.map_prod_map _ _ hdiag hdiag]
        rw [hmap, integral_map]
        · refine integral_eq_zero_of_ae (ae_of_all _ fun p => ?_)
          simp only [Prod.map_apply', overlay_apply, Pi.zero_apply]
          ring
        · exact (Measurable.prodMap hdiag hdiag).aemeasurable
        · refine (measurable_integrand (overlay U U (diagCoupling μ₁)) hu.measurable
            hv.measurable).aestronglyMeasurable
      rw [hzero, abs_zero]
    · rw [ciSup_pos hu, ciSup_neg hv, Real.sSup_empty]
  · rw [ciSup_neg hu, Real.sSup_empty]

/-- **Item 6:** the cut distance of a graphon to itself is `0`. -/
theorem cutDist_self_eq_zero (U : Graphon Ω₁ μ₁) : cutDist U U = 0 := by
  refine le_antisymm ?_ (cutDist_nonneg U U)
  refine le_trans (cutDist_le_of_coupling U U
    ⟨diagCoupling μ₁, isCoupling_diagCoupling μ₁⟩) ?_
  exact le_of_eq (cutNorm_overlay_diag U)

/-! #### Triangle inequality (Gluing Lemma)

**Item 7:** the cut distance satisfies the triangle inequality. Stated and proved (with
`StandardBorelSpace` hypotheses) in `Graphons/Gluing.lean` via the coupling Gluing Lemma; see
`Graphons.cutDist_triangle` there. -/

end CutDist

end Graphons
