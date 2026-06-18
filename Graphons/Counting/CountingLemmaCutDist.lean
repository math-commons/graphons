/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits):
  The **cross-carrier counting lemma** (Tier-C forward direction):
    |t(F, U) − t(F, W)| ≤ e(F) · δ□(U, W),
  where `U, W` live on POSSIBLY DIFFERENT probability spaces `(Ω₁, μ₁)`, `(Ω₂, μ₂)` and `δ□`
  is the coupling cut distance.  Sources: Lovász, "Large Networks and Graph Limits" (2012),
  Lemma 10.23 + the cut-metric chapter; Borgs–Chayes–Lovász–Sós–Vesztergombi (2007).

The same-carrier counting lemma `abs_homDensity_sub_le` lives on a single space.  To bridge two
spaces we fix a coupling `π` of `(μ₁, μ₂)` (a probability measure on `Ω₁ × Ω₂` with the right
marginals) and lift `U, W` to **projection-overlay graphons** on `(Ω₁ × Ω₂, π)`:
  `Uπ p q := U (p.1) (q.1)`,  `Wπ p q := W (p.2) (q.2)`.
Then `overlay U W π = Uπ − Wπ` (definitionally), and the same-carrier lemma applied to `Uπ, Wπ`
gives `|t(F,Uπ) − t(F,Wπ)| ≤ e(F)·‖overlay U W π‖□`.  The **marginalization lemma**
`homDensity_overlayFst`/`_snd` identifies `t(F,Uπ) = t(F,U)` and `t(F,Wπ) = t(F,W)`: the
integrand of `t(F,Uπ)` depends only on the first coordinates, and the pushforward of `μ_π^{⊗V}`
under the coordinatewise first projection is `μ₁^{⊗V}` (`IsCoupling` + `measurePreserving_pi`).
Taking the infimum over couplings yields the cut-distance bound.
-/
import Graphons.Counting.CountingLemma
import Graphons.CutMetric.CutDist

open MeasureTheory

namespace Graphons

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-! ### Projection-overlay graphons -/

/-- The **first projection-overlay graphon**: lift `U` on `(Ω₁, μ₁)` to a graphon on the coupled
    space `(Ω₁ × Ω₂, π)` by reading off the first coordinates, `Uπ p q := U (p.1) (q.1)`. -/
noncomputable def overlayFst (U : Graphon Ω₁ μ₁) (π : Measure (Ω₁ × Ω₂))
    [IsProbabilityMeasure π] : Graphon (Ω₁ × Ω₂) π :=
  Graphon.mk' (fun p q => U.toFun p.1 q.1)
    (fun p q => U.symm' p.1 q.1)
    (U.meas'.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))
    (fun p q => U.nonneg' p.1 q.1)
    (fun p q => U.le_one' p.1 q.1)

/-- The **second projection-overlay graphon**: lift `W` on `(Ω₂, μ₂)` to `(Ω₁ × Ω₂, π)` by reading
    off the second coordinates, `Wπ p q := W (p.2) (q.2)`. -/
noncomputable def overlaySnd (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂))
    [IsProbabilityMeasure π] : Graphon (Ω₁ × Ω₂) π :=
  Graphon.mk' (fun p q => W.toFun p.2 q.2)
    (fun p q => W.symm' p.2 q.2)
    (W.meas'.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
    (fun p q => W.nonneg' p.2 q.2)
    (fun p q => W.le_one' p.2 q.2)

@[simp] theorem overlayFst_apply (U : Graphon Ω₁ μ₁) (π : Measure (Ω₁ × Ω₂))
    [IsProbabilityMeasure π] (p q : Ω₁ × Ω₂) :
    (overlayFst U π) p q = U.toFun p.1 q.1 := rfl

@[simp] theorem overlaySnd_apply (W : Graphon Ω₂ μ₂) (π : Measure (Ω₁ × Ω₂))
    [IsProbabilityMeasure π] (p q : Ω₁ × Ω₂) :
    (overlaySnd W π) p q = W.toFun p.2 q.2 := rfl

/-- **Step 1.**  The overlay kernel is exactly the difference of the two projection-overlay
    graphons: `overlay U W π = (overlayFst U π).toSymmKernel − (overlaySnd W π).toSymmKernel`. -/
theorem overlay_eq_sub (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (π : Measure (Ω₁ × Ω₂)) [IsProbabilityMeasure π] :
    overlay U W π = (overlayFst U π).toSymmKernel - (overlaySnd W π).toSymmKernel := by
  ext p q
  simp [overlayFst, overlaySnd]

/-! ### Marginalization (the crux)

The integrand of `t(F, Uπ)` over `V → (Ω₁ × Ω₂)` depends only on the first coordinates.  The
pushforward of the product measure `π^{⊗V}` under the coordinatewise first projection
`y ↦ (fun i ↦ (y i).1)` is `μ₁^{⊗V}` (because `π.map Prod.fst = μ₁` and `Measure.pi` commutes with
coordinatewise `map`, `measurePreserving_pi`).  Hence `t(F, Uπ) = t(F, U)`. -/

section Marginal

variable {V : Type*} [Fintype V] [MeasurableSpace V]

/-- The coordinatewise first projection `(V → Ω₁ × Ω₂) → (V → Ω₁)`, `y ↦ fun i ↦ (y i).1`, is
    measure-preserving from `π^{⊗V}` to `μ₁^{⊗V}` when `π` is a coupling of `(μ₁, μ₂)`. -/
theorem measurePreserving_piFst {π : Measure (Ω₁ × Ω₂)} (hπ : IsCoupling μ₁ μ₂ π) :
    MeasurePreserving (fun y : V → Ω₁ × Ω₂ => fun i => (y i).1)
      (piMeasure V π) (piMeasure V μ₁) := by
  haveI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hfst : MeasurePreserving (Prod.fst : Ω₁ × Ω₂ → Ω₁) π μ₁ := ⟨measurable_fst, hπ.map_fst⟩
  simpa [piMeasure] using
    measurePreserving_pi (fun _ : V => π) (fun _ : V => μ₁) (fun _ => hfst)

/-- The coordinatewise second projection `(V → Ω₁ × Ω₂) → (V → Ω₂)` is measure-preserving from
    `π^{⊗V}` to `μ₂^{⊗V}` when `π` is a coupling of `(μ₁, μ₂)`. -/
theorem measurePreserving_piSnd {π : Measure (Ω₁ × Ω₂)} (hπ : IsCoupling μ₁ μ₂ π) :
    MeasurePreserving (fun y : V → Ω₁ × Ω₂ => fun i => (y i).2)
      (piMeasure V π) (piMeasure V μ₂) := by
  haveI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hsnd : MeasurePreserving (Prod.snd : Ω₁ × Ω₂ → Ω₂) π μ₂ := ⟨measurable_snd, hπ.map_snd⟩
  simpa [piMeasure] using
    measurePreserving_pi (fun _ : V => π) (fun _ : V => μ₂) (fun _ => hsnd)

/-- The `Uπ`-integrand at `y` is the `U`-integrand at the first-projected point. -/
theorem homDensityIntegrand_overlayFst (F : SimpleGraph V) [DecidableRel F.Adj]
    (U : Graphon Ω₁ μ₁) {π : Measure (Ω₁ × Ω₂)} [IsProbabilityMeasure π] (y : V → Ω₁ × Ω₂) :
    homDensityIntegrand F (overlayFst U π) y
      = homDensityIntegrand F U (fun i => (y i).1) := by
  unfold homDensityIntegrand
  refine Finset.prod_congr rfl (fun e _ => ?_)
  induction e with
  | _ a b => simp [edgeVal]

/-- The `Wπ`-integrand at `y` is the `W`-integrand at the second-projected point. -/
theorem homDensityIntegrand_overlaySnd (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon Ω₂ μ₂) {π : Measure (Ω₁ × Ω₂)} [IsProbabilityMeasure π] (y : V → Ω₁ × Ω₂) :
    homDensityIntegrand F (overlaySnd W π) y
      = homDensityIntegrand F W (fun i => (y i).2) := by
  unfold homDensityIntegrand
  refine Finset.prod_congr rfl (fun e _ => ?_)
  induction e with
  | _ a b => simp [edgeVal]

/-- **Marginalization lemma (first coordinate).**  The homomorphism density of `F` into the
    projection-overlay graphon `Uπ` equals that into `U`. -/
theorem homDensity_overlayFst (F : SimpleGraph V) [DecidableRel F.Adj]
    (U : Graphon Ω₁ μ₁) {π : Measure (Ω₁ × Ω₂)} [IsProbabilityMeasure π]
    (hπ : IsCoupling μ₁ μ₂ π) :
    homDensity F (overlayFst U π) = homDensity F U := by
  have hmp := measurePreserving_piFst (V := V) hπ
  unfold homDensity
  -- `∫ x, g x ∂μ₁^{⊗V} = ∫ y, g (proj y) ∂π^{⊗V}` via `map_eq` + `integral_map`.
  rw [← hmp.map_eq,
    integral_map hmp.measurable.aemeasurable
      (Graphon.measurable_homDensityIntegrand F U).aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  rw [homDensityIntegrand_overlayFst]

/-- **Marginalization lemma (second coordinate).**  The homomorphism density of `F` into the
    projection-overlay graphon `Wπ` equals that into `W`. -/
theorem homDensity_overlaySnd (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon Ω₂ μ₂) {π : Measure (Ω₁ × Ω₂)} [IsProbabilityMeasure π]
    (hπ : IsCoupling μ₁ μ₂ π) :
    homDensity F (overlaySnd W π) = homDensity F W := by
  have hmp := measurePreserving_piSnd (V := V) hπ
  unfold homDensity
  rw [← hmp.map_eq,
    integral_map hmp.measurable.aemeasurable
      (Graphon.measurable_homDensityIntegrand F W).aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  rw [homDensityIntegrand_overlaySnd]

end Marginal

/-! ### The cross-carrier counting lemma -/

/-- **Step 3 (per-coupling bound).**  For a fixed coupling `π`, the same-carrier counting lemma
    applied to the projection-overlay graphons `Uπ, Wπ` (on the common carrier `(Ω₁ × Ω₂, π)`),
    combined with marginalization, gives
      `|t(F,U) − t(F,W)| ≤ e(F)·‖overlay U W π‖□`. -/
theorem abs_homDensity_sub_le_cutNorm_overlay {V} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    {π : Measure (Ω₁ × Ω₂)} (hπ : IsCoupling μ₁ μ₂ π) :
    |homDensity F U - homDensity F W| ≤
      (F.edgeFinset.card : ℝ) * cutNorm (overlay U W π) := by
  classical
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  haveI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hkey := abs_homDensity_sub_le F (overlayFst U π) (overlaySnd W π)
  rw [homDensity_overlayFst F U hπ, homDensity_overlaySnd F W hπ,
    ← overlay_eq_sub U W π] at hkey
  exact hkey

/-- **Cross-carrier counting lemma (Tier-C forward direction).**
    `|t(F, U) − t(F, W)| ≤ e(F) · δ□(U, W)` for graphons on possibly different carriers. -/
theorem abs_homDensity_sub_le_cutDist {V} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    |homDensity F U - homDensity F W| ≤ (F.edgeFinset.card : ℝ) * cutDist U W := by
  rw [cutDist]
  -- The LHS is independent of `π`, so it sits under the infimum on the RHS.
  rw [Real.mul_iInf_of_nonneg (Nat.cast_nonneg _)]
  refine le_ciInf fun π => ?_
  exact abs_homDensity_sub_le_cutNorm_overlay F U W π.2

/-- **Corollary.**  If the cut distance is zero, the homomorphism densities agree. -/
theorem homDensity_eq_of_cutDist_eq_zero {V} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (h : cutDist U W = 0) :
    homDensity F U = homDensity F W := by
  have hbound := abs_homDensity_sub_le_cutDist F U W
  rw [h, mul_zero] at hbound
  have : |homDensity F U - homDensity F W| = 0 := le_antisymm hbound (abs_nonneg _)
  rwa [abs_eq_zero, sub_eq_zero] at this

end Graphons
