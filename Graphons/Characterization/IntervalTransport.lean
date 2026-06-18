/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

**Interval transport** (Tier E, towards E2): the measure-preserving map
`intervalIdx n : [0,1] → Fin (n+1)` sending `x` to the index of the subinterval
`[i/(n+1), (i+1)/(n+1))` containing it, and the induced pullback
`FinWeighted.toUnit : FinWeighted → Graphon ℝ unitMeasure`.

Main results:
* `measurePreserving_intervalIdx` — `intervalIdx n` pushes `unitMeasure` to `unifFin (n+1)`;
* `cutDist_toUnit` — the pullback is at cut distance `0` from the original finite weighted
  graph (witnessed by the graph coupling `x ↦ (x, intervalIdx n x)`);
* `homDensity_toUnit` — the pullback has the same homomorphism densities.
-/
import Graphons.Characterization.LimitSpec
import Graphons.CutMetric.CutNormL1

open MeasureTheory
open scoped ENNReal

namespace Graphons

/-! ### The interval-to-index map -/

/-- Send `x ∈ [0,1]` to the index of the subinterval `[i/(n+1), (i+1)/(n+1))` containing it
    (clamped to `Fin (n+1)`; `x = 1` lands in the last index `n`). -/
noncomputable def intervalIdx (n : ℕ) (x : ℝ) : Fin (n + 1) :=
  ⟨min n ⌊x * (n + 1)⌋₊, by omega⟩

/-- Membership characterization for `intervalIdx`. -/
private lemma intervalIdx_eq_iff (n : ℕ) (x : ℝ) (i : Fin (n + 1)) :
    intervalIdx n x = i ↔ min n ⌊x * ((n : ℝ) + 1)⌋₊ = i.val := by
  rw [Fin.ext_iff]
  exact Iff.rfl

theorem measurable_intervalIdx (n : ℕ) : Measurable (intervalIdx n) := by
  have h : Measurable (fun x : ℝ => ⌊x * ((n : ℝ) + 1)⌋₊) :=
    (measurable_id.mul_const _).nat_floor
  exact (measurable_of_countable
    (fun k : ℕ => (⟨min n k, by omega⟩ : Fin (n + 1)))).comp h

/-! ### Preimages of singletons and their measure -/

/-- For a non-last index `i < n`, the preimage of `{i}` inside `[0,1]` is the half-open
    subinterval `[i/(n+1), (i+1)/(n+1))`. -/
private lemma intervalIdx_preimage_inter_lt (n : ℕ) (i : Fin (n + 1)) (hi : i.val < n) :
    intervalIdx n ⁻¹' {i} ∩ Set.Icc (0 : ℝ) 1
      = Set.Ico ((i.val : ℝ) / ((n : ℝ) + 1)) (((i.val : ℝ) + 1) / ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Icc,
    Set.mem_Ico, intervalIdx_eq_iff]
  constructor
  · rintro ⟨hidx, hx0, _⟩
    have hxm0 : (0 : ℝ) ≤ x * ((n : ℝ) + 1) := mul_nonneg hx0 hn.le
    have hfl : ⌊x * ((n : ℝ) + 1)⌋₊ = i.val := by omega
    rw [Nat.floor_eq_iff hxm0] at hfl
    obtain ⟨h1, h2⟩ := hfl
    exact ⟨(div_le_iff₀ hn).mpr h1, (lt_div_iff₀ hn).mpr h2⟩
  · rintro ⟨hlo, hhi⟩
    have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) hlo
    have hx1 : x ≤ 1 := by
      refine le_trans hhi.le ?_
      rw [div_le_one hn]
      have : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.le
      linarith
    refine ⟨?_, hx0, hx1⟩
    have hxm0 : (0 : ℝ) ≤ x * ((n : ℝ) + 1) := mul_nonneg hx0 hn.le
    have hfl : ⌊x * ((n : ℝ) + 1)⌋₊ = i.val := by
      rw [Nat.floor_eq_iff hxm0]
      exact ⟨(div_le_iff₀ hn).mp hlo, (lt_div_iff₀ hn).mp hhi⟩
    omega

/-- For the last index `i = n`, the preimage of `{i}` inside `[0,1]` is the closed
    subinterval `[n/(n+1), 1]` (in particular `x = 1` lands there). -/
private lemma intervalIdx_preimage_inter_last (n : ℕ) (i : Fin (n + 1)) (hi : i.val = n) :
    intervalIdx n ⁻¹' {i} ∩ Set.Icc (0 : ℝ) 1
      = Set.Icc ((n : ℝ) / ((n : ℝ) + 1)) 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Icc,
    intervalIdx_eq_iff, hi]
  constructor
  · rintro ⟨hidx, hx0, hx1⟩
    have hge : n ≤ ⌊x * ((n : ℝ) + 1)⌋₊ := by omega
    have h1 : (n : ℝ) ≤ x * ((n : ℝ) + 1) :=
      (Nat.le_floor_iff (mul_nonneg hx0 hn.le)).mp hge
    exact ⟨(div_le_iff₀ hn).mpr h1, hx1⟩
  · rintro ⟨hlo, hx1⟩
    have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) hlo
    have hge : n ≤ ⌊x * ((n : ℝ) + 1)⌋₊ := Nat.le_floor ((div_le_iff₀ hn).mp hlo)
    exact ⟨by omega, hx0, hx1⟩

/-- `ENNReal.ofReal (1/(n+1)) = (↑(n+1))⁻¹`. -/
private lemma ofReal_one_div_succ (n : ℕ) :
    ENNReal.ofReal (1 / ((n : ℝ) + 1)) = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity),
    show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    ENNReal.ofReal_natCast]

/-- Each of the `n+1` index preimages has `unitMeasure`-measure exactly `1/(n+1)`. -/
theorem unitMeasure_intervalIdx_preimage (n : ℕ) (i : Fin (n + 1)) :
    unitMeasure (intervalIdx n ⁻¹' {i}) = (↑(n + 1))⁻¹ := by
  have hmeas : MeasurableSet (intervalIdx n ⁻¹' {i}) :=
    measurable_intervalIdx n (MeasurableSet.singleton i)
  rw [unitMeasure, Measure.restrict_apply hmeas]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with hi | hi
  · rw [intervalIdx_preimage_inter_lt n i hi, Real.volume_Ico,
      show ((i.val : ℝ) + 1) / ((n : ℝ) + 1) - (i.val : ℝ) / ((n : ℝ) + 1)
        = 1 / ((n : ℝ) + 1) by ring]
    exact ofReal_one_div_succ n
  · rw [intervalIdx_preimage_inter_last n i hi, Real.volume_Icc,
      show (1 : ℝ) - (n : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) by
        have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring]
    exact ofReal_one_div_succ n

/-! ### Measure preservation -/

/-- **The interval transport is measure-preserving**: `intervalIdx n` pushes the uniform
    measure on `[0,1]` forward to the uniform measure on `Fin (n+1)`. -/
theorem measurePreserving_intervalIdx (n : ℕ) :
    MeasurePreserving (intervalIdx n) unitMeasure (unifFin (n + 1)) := by
  refine ⟨measurable_intervalIdx n, Measure.ext_of_singleton fun i => ?_⟩
  rw [Measure.map_apply (measurable_intervalIdx n) (MeasurableSet.singleton i),
    unitMeasure_intervalIdx_preimage, unifFin,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton i),
    PMF.uniformOfFintype_apply, Fintype.card_fin]

/-! ### The pullback graphon on `([0,1], unitMeasure)` -/

/-- **Pull a finite weighted graph back to the unit interval**: the step-function graphon
    `(x, y) ↦ G (intervalIdx x) (intervalIdx y)` on `([0,1], unitMeasure)`. -/
noncomputable def FinWeighted.toUnit (G : FinWeighted) : Graphon ℝ unitMeasure :=
  Graphon.mk' (fun x y => G.2.toFun (intervalIdx G.1 x) (intervalIdx G.1 y))
    (fun _ _ => G.2.symm' _ _)
    (G.2.meas'.comp (((measurable_intervalIdx _).comp measurable_fst).prodMk
      ((measurable_intervalIdx _).comp measurable_snd)))
    (fun _ _ => G.2.nonneg' _ _)
    (fun _ _ => G.2.le_one' _ _)

@[simp] theorem FinWeighted.toUnit_apply (G : FinWeighted) (x y : ℝ) :
    G.toUnit.toFun x y = G.2.toFun (intervalIdx G.1 x) (intervalIdx G.1 y) := rfl

/-! ### The transport is a weak isomorphism: cut distance `0` -/

/-- **The pullback is at cut distance `0` from the original finite weighted graph.**
    Witness: the graph coupling `π = (id, intervalIdx)_* unitMeasure`, on which the overlay
    difference vanishes identically. -/
theorem cutDist_toUnit (G : FinWeighted) : cutDist G.toUnit G.2 = 0 := by
  set g : ℝ → ℝ × Fin (G.1 + 1) := fun x => (x, intervalIdx G.1 x) with hgdef
  have hg : Measurable g := measurable_id.prodMk (measurable_intervalIdx G.1)
  have hcoup : IsCoupling unitMeasure (unifFin (G.1 + 1)) (unitMeasure.map g) := by
    constructor
    · rw [Measure.map_map measurable_fst hg]
      exact Measure.map_id
    · rw [Measure.map_map measurable_snd hg]
      exact (measurePreserving_intervalIdx G.1).map_eq
  haveI : IsProbabilityMeasure (unitMeasure.map g) := hcoup.isProbabilityMeasure
  have hgp : MeasurePreserving g unitMeasure (unitMeasure.map g) := ⟨hg, rfl⟩
  refine le_antisymm ?_ (cutDist_nonneg _ _)
  refine le_trans (cutDist_le_of_coupling G.toUnit G.2 ⟨unitMeasure.map g, hcoup⟩) ?_
  have hover : Measurable (fun p : (ℝ × Fin (G.1 + 1)) × (ℝ × Fin (G.1 + 1)) =>
      |(overlay G.toUnit G.2 (unitMeasure.map g)).toFun p.1 p.2|) :=
    (overlay G.toUnit G.2 (unitMeasure.map g)).meas'.abs
  have hzero : ∫ p : (ℝ × Fin (G.1 + 1)) × (ℝ × Fin (G.1 + 1)),
      |(overlay G.toUnit G.2 (unitMeasure.map g)).toFun p.1 p.2|
        ∂((unitMeasure.map g).prod (unitMeasure.map g)) = 0 := by
    rw [← (hgp.prod hgp).map_eq,
      integral_map (hg.prodMap hg).aemeasurable hover.aestronglyMeasurable]
    have hpt : ∀ p : ℝ × ℝ,
        |(overlay G.toUnit G.2 (unitMeasure.map g)).toFun
          (Prod.map g g p).1 (Prod.map g g p).2| = 0 := by
      intro p
      simp [hgdef, overlay_apply, Prod.map_fst, Prod.map_snd]
    simp only [hpt]
    exact integral_zero _ _
  calc cutDistFun G.toUnit G.2 ⟨unitMeasure.map g, hcoup⟩
      = cutNorm (overlay G.toUnit G.2 (unitMeasure.map g)) := rfl
    _ ≤ ∫ p : (ℝ × Fin (G.1 + 1)) × (ℝ × Fin (G.1 + 1)),
          |(overlay G.toUnit G.2 (unitMeasure.map g)).toFun p.1 p.2|
            ∂((unitMeasure.map g).prod (unitMeasure.map g)) := cutNorm_le_L1 _
    _ = 0 := hzero

/-! ### The transport preserves homomorphism densities -/

/-- **The pullback has the same homomorphism densities** as the original finite weighted
    graph: change of variables along the measure-preserving postcomposition
    `(V → [0,1]) → (V → Fin (n+1))`. -/
theorem homDensity_toUnit {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (G : FinWeighted) : homDensity F G.toUnit = homDensity F G.2 := by
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  have hΦ : MeasurePreserving (fun (φ : V → ℝ) (i : V) => intervalIdx G.1 (φ i))
      (piMeasure V unitMeasure) (piMeasure V (unifFin (G.1 + 1))) :=
    measurePreserving_pi _ _ (fun _ => measurePreserving_intervalIdx G.1)
  have hpt : ∀ φ : V → ℝ, homDensityIntegrand F G.toUnit φ
      = homDensityIntegrand F G.2 (fun i => intervalIdx G.1 (φ i)) := fun _ => rfl
  calc homDensity F G.toUnit
      = ∫ φ, homDensityIntegrand F G.2 (fun i => intervalIdx G.1 (φ i))
          ∂(piMeasure V unitMeasure) := integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ ψ, homDensityIntegrand F G.2 ψ
          ∂((piMeasure V unitMeasure).map (fun (φ : V → ℝ) (i : V) => intervalIdx G.1 (φ i))) :=
        (integral_map hΦ.aemeasurable
          (Graphon.measurable_homDensityIntegrand F G.2).aestronglyMeasurable).symm
    _ = homDensity F G.2 := by rw [hΦ.map_eq]; rfl

end Graphons
