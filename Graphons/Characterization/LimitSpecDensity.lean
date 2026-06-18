/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

**Density of finite weighted graphs in the cut distance** (towards E2): every graphon on
`([0,1], unitMeasure)` is within cut distance `ε` of (the unit-interval pullback of) some finite
weighted graph.

Route: weak regularity gives a step graphon `stepGraphon W P` at distance `≤ ε/2`; the part
masses of `P` are rounded to rationals `c i / (M+1)` with `∑ c = M+1` (total rounding error
`≤ ε/8`); grouping the `M+1` uniform subintervals of `[0,1]` into fibers of sizes `c i` yields a
partition `Q` whose step graphon w.r.t. the block averages of `W` over `P` IS the pullback
`FinWeighted.toUnit` of a finite weighted graph on `M+1` vertices; `cutDist_step_le_of_equiv`
(near-diagonal block coupling) bounds the distance between the two step graphons by twice the
rounding error.
-/
import Graphons.Characterization.IntervalTransport
import Graphons.Limits.BlockCoupling
import Graphons.Core.Density

open MeasureTheory
open scoped ENNReal

namespace Graphons

/-! ### Graphon extensionality -/

/-- Two graphons with identical kernels are equal (proof irrelevance for the `[0,1]` bounds). -/
private theorem graphon_ext {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U V : Graphon Ω μ}
    (h : ∀ x y, U.toFun x y = V.toFun x y) : U = V := by
  obtain ⟨KU, hU1, hU2⟩ := U
  obtain ⟨KV, hV1, hV2⟩ := V
  have hK : KU = KV := SymmKernel.ext h
  subst hK
  rfl

/-! ### Measure of interval preimages of finsets -/

/-- The `unitMeasure`-mass of the union of the subintervals indexed by a finset `S` is
    `S.card / (M+1)`. -/
private lemma unitMeasure_intervalIdx_preimage_finset (M : ℕ) (S : Finset (Fin (M + 1))) :
    unitMeasure (intervalIdx M ⁻¹' (S : Set (Fin (M + 1))))
      = (S.card : ℝ≥0∞) * ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  have hcover : (S : Set (Fin (M + 1))) = ⋃ j ∈ S, ({j} : Set (Fin (M + 1))) := by
    ext j
    simp
  rw [hcover, Set.preimage_iUnion₂,
    measure_biUnion_finset
      (fun a _ b _ hab => (Set.disjoint_singleton.mpr hab).preimage (intervalIdx M))
      (fun j _ => measurable_intervalIdx M (MeasurableSet.singleton j))]
  simp [unitMeasure_intervalIdx_preimage, Finset.sum_const, nsmul_eq_mul]

/-! ### The rounding lemma -/

/-- **Rounding of a positive probability vector to denominators `M+1`**: there exist `M : ℕ` and
    positive integers `c i` with `∑ c = M + 1` and total rounding error
    `∑ |r i − c i/(M+1)| ≤ η`. -/
private lemma exists_rounding {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    (r : ι → ℝ) (hpos : ∀ i, 0 < r i) (hsum : ∑ i, r i = 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ (M : ℕ) (c : ι → ℕ), (∀ i, 1 ≤ c i) ∧ (∑ i, c i = M + 1) ∧
      (∑ i, |r i - (c i : ℝ) / ((M : ℝ) + 1)|) ≤ η := by
  haveI : Nonempty ι := ⟨i₀⟩
  have hk1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hk1R : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hk1
  -- Choose `M` large enough.
  obtain ⟨M, hM⟩ := exists_nat_ge (max (2 * (Fintype.card ι : ℝ) / η)
    (Finset.univ.sup' Finset.univ_nonempty fun i => (r i)⁻¹))
  have hNpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hM1 : 2 * (Fintype.card ι : ℝ) / η ≤ (M : ℝ) + 1 :=
    le_trans (le_trans (le_max_left _ _) hM) (by linarith)
  have hM2 : ∀ i, (r i)⁻¹ ≤ (M : ℝ) + 1 := fun i =>
    le_trans (le_trans (le_trans
      (Finset.le_sup' (fun i => (r i)⁻¹) (Finset.mem_univ i)) (le_max_right _ _)) hM)
      (by linarith)
  have h2kN : 2 * (Fintype.card ι : ℝ) / ((M : ℝ) + 1) ≤ η := by
    rw [div_le_iff₀ hNpos]
    have h := (div_le_iff₀ hη).1 hM1
    linarith [mul_comm η ((M : ℝ) + 1)]
  have hNr : ∀ i, 1 ≤ r i * ((M : ℝ) + 1) := by
    intro i
    have h := mul_le_mul_of_nonneg_left (hM2 i) (hpos i).le
    rwa [mul_inv_cancel₀ (hpos i).ne'] at h
  -- Floors.
  set c₀ : ι → ℕ := fun i => ⌊r i * ((M : ℝ) + 1)⌋₊ with hc₀
  have hfl : ∀ i, (c₀ i : ℝ) ≤ r i * ((M : ℝ) + 1) := fun i =>
    Nat.floor_le (mul_nonneg (hpos i).le (by positivity))
  have hfu : ∀ i, r i * ((M : ℝ) + 1) < (c₀ i : ℝ) + 1 := fun i =>
    Nat.lt_floor_add_one (r i * ((M : ℝ) + 1))
  have h1c : ∀ i, 1 ≤ c₀ i := fun i => Nat.le_floor (by exact_mod_cast hNr i)
  have hsum_le : ∑ i, c₀ i ≤ M + 1 := by
    have hcast : ((∑ i, c₀ i : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
      push_cast
      calc ∑ i, (c₀ i : ℝ) ≤ ∑ i, r i * ((M : ℝ) + 1) :=
            Finset.sum_le_sum fun i _ => hfl i
        _ = (∑ i, r i) * ((M : ℝ) + 1) := (Finset.sum_mul _ _ _).symm
        _ = (M : ℝ) + 1 := by rw [hsum, one_mul]
    exact_mod_cast hcast
  have hsum_gt : M + 1 < ∑ i, c₀ i + Fintype.card ι := by
    have hcast : (M : ℝ) + 1 < ((∑ i, c₀ i : ℕ) : ℝ) + (Fintype.card ι : ℝ) := by
      have h1 : (M : ℝ) + 1 = (∑ i, r i) * ((M : ℝ) + 1) := by rw [hsum, one_mul]
      have h2 : (∑ i, r i) * ((M : ℝ) + 1) = ∑ i, r i * ((M : ℝ) + 1) :=
        Finset.sum_mul _ _ _
      have h3 : ∑ i, r i * ((M : ℝ) + 1) < ∑ i, ((c₀ i : ℝ) + 1) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hfu i
      have h4 : ∑ i, ((c₀ i : ℝ) + 1) = (∑ i, (c₀ i : ℝ)) + (Fintype.card ι : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have h5 : (∑ i, (c₀ i : ℝ)) = ((∑ i, c₀ i : ℕ) : ℝ) := by push_cast; rfl
      linarith
    exact_mod_cast hcast
  -- Distribute the deficit onto `i₀`.
  set c : ι → ℕ := fun i => if i = i₀ then c₀ i + ((M + 1) - ∑ j, c₀ j) else c₀ i with hc
  have hc1 : ∀ i, 1 ≤ c i := by
    intro i
    have h1 := h1c i
    by_cases h : i = i₀
    · simp only [hc, if_pos h]
      omega
    · simp only [hc, if_neg h]
      omega
  have hcsum : ∑ i, c i = M + 1 := by
    have hpt : ∀ i, c i = c₀ i + (if i = i₀ then (M + 1) - ∑ j, c₀ j else 0) := by
      intro i
      by_cases h : i = i₀ <;> simp [hc, h]
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i₀ (fun _ => (M + 1) - ∑ j, c₀ j)]
    simp only [Finset.mem_univ, if_true]
    exact Nat.add_sub_cancel' hsum_le
  refine ⟨M, c, hc1, hcsum, ?_⟩
  -- Per-index error bounds.
  have herr : ∀ i, i ≠ i₀ → |r i - (c i : ℝ) / ((M : ℝ) + 1)| ≤ 1 / ((M : ℝ) + 1) := by
    intro i h
    have hci : c i = c₀ i := by simp [hc, h]
    have ha : (c₀ i : ℝ) / ((M : ℝ) + 1) ≤ r i := (div_le_iff₀ hNpos).2 (hfl i)
    have hb : r i ≤ ((c₀ i : ℝ) + 1) / ((M : ℝ) + 1) := (le_div_iff₀ hNpos).2 (hfu i).le
    have hadd : ((c₀ i : ℝ) + 1) / ((M : ℝ) + 1)
        = (c₀ i : ℝ) / ((M : ℝ) + 1) + 1 / ((M : ℝ) + 1) := add_div _ _ _
    rw [hci]
    refine abs_le.2 ⟨?_, ?_⟩
    · have h0 : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
      linarith
    · linarith
  have herr₀ : |r i₀ - (c i₀ : ℝ) / ((M : ℝ) + 1)|
      ≤ (Fintype.card ι : ℝ) / ((M : ℝ) + 1) := by
    have hci : c i₀ = c₀ i₀ + ((M + 1) - ∑ j, c₀ j) := by simp [hc]
    have hdR : (((M + 1) - ∑ j, c₀ j : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) - 1 := by
      have hdlt : ((M + 1) - ∑ j, c₀ j) + 1 ≤ Fintype.card ι := by omega
      have h' := (Nat.cast_le (α := ℝ)).mpr hdlt
      push_cast at h'
      linarith
    have hd0 : (0 : ℝ) ≤ (((M + 1) - ∑ j, c₀ j : ℕ) : ℝ) / ((M : ℝ) + 1) := by positivity
    have ha : (c₀ i₀ : ℝ) / ((M : ℝ) + 1) ≤ r i₀ := (div_le_iff₀ hNpos).2 (hfl i₀)
    have hb : r i₀ ≤ ((c₀ i₀ : ℝ) + 1) / ((M : ℝ) + 1) := (le_div_iff₀ hNpos).2 (hfu i₀).le
    have hcR : (c i₀ : ℝ) = (c₀ i₀ : ℝ) + (((M + 1) - ∑ j, c₀ j : ℕ) : ℝ) := by
      rw [hci]
      push_cast
      ring
    have hsplit : ((c₀ i₀ : ℝ) + (((M + 1) - ∑ j, c₀ j : ℕ) : ℝ)) / ((M : ℝ) + 1)
        = (c₀ i₀ : ℝ) / ((M : ℝ) + 1)
          + (((M + 1) - ∑ j, c₀ j : ℕ) : ℝ) / ((M : ℝ) + 1) := add_div _ _ _
    have hdN : (((M + 1) - ∑ j, c₀ j : ℕ) : ℝ) / ((M : ℝ) + 1)
        ≤ ((Fintype.card ι : ℝ) - 1) / ((M : ℝ) + 1) := by
      gcongr
    have hkN : ((Fintype.card ι : ℝ) - 1) / ((M : ℝ) + 1)
        ≤ (Fintype.card ι : ℝ) / ((M : ℝ) + 1) := by
      gcongr
      linarith
    have hadd : ((c₀ i₀ : ℝ) + 1) / ((M : ℝ) + 1)
        = (c₀ i₀ : ℝ) / ((M : ℝ) + 1) + 1 / ((M : ℝ) + 1) := add_div _ _ _
    have h1N : 1 / ((M : ℝ) + 1) ≤ (Fintype.card ι : ℝ) / ((M : ℝ) + 1) := by
      gcongr
    rw [hcR, hsplit]
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith
    · linarith
  -- Total.
  rw [← Finset.add_sum_erase Finset.univ (fun i => |r i - (c i : ℝ) / ((M : ℝ) + 1)|)
    (Finset.mem_univ i₀)]
  have herase : ∑ i ∈ Finset.univ.erase i₀, |r i - (c i : ℝ) / ((M : ℝ) + 1)|
      ≤ ((Fintype.card ι : ℝ) - 1) * (1 / ((M : ℝ) + 1)) := by
    have hb := Finset.sum_le_card_nsmul (Finset.univ.erase i₀)
      (fun i => |r i - (c i : ℝ) / ((M : ℝ) + 1)|) (1 / ((M : ℝ) + 1))
      (fun i hi => herr i (Finset.ne_of_mem_erase hi))
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ] at hb
    refine hb.trans ?_
    rw [nsmul_eq_mul]
    have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]
      norm_num
    rw [hcast]
  have hfinal : (Fintype.card ι : ℝ) / ((M : ℝ) + 1)
      + ((Fintype.card ι : ℝ) - 1) * (1 / ((M : ℝ) + 1)) ≤ η := by
    have heq : (Fintype.card ι : ℝ) / ((M : ℝ) + 1)
        + ((Fintype.card ι : ℝ) - 1) * (1 / ((M : ℝ) + 1))
        = (2 * (Fintype.card ι : ℝ) - 1) / ((M : ℝ) + 1) := by
      rw [mul_one_div, ← add_div]
      ring_nf
    rw [heq]
    have hle2 : (2 * (Fintype.card ι : ℝ) - 1) / ((M : ℝ) + 1)
        ≤ 2 * (Fintype.card ι : ℝ) / ((M : ℝ) + 1) := by
      gcongr
      linarith
    linarith
  linarith [herr₀, herase, hfinal]

/-! ### The group map `Fin (M+1) → ι` with prescribed fiber sizes -/

private lemma card_sigma_fin {ι : Type} [Fintype ι] {N : ℕ} (c : ι → ℕ)
    (hc : ∑ i, c i = N) : Fintype.card (Σ i : ι, Fin (c i)) = N := by
  rw [Fintype.card_sigma]
  simpa using hc

/-- An identification of `Fin N` with the disjoint union of fibers of sizes `c i`. -/
private noncomputable def groupEquiv {ι : Type} [Fintype ι] {N : ℕ} (c : ι → ℕ)
    (hc : ∑ i, c i = N) : (Σ i : ι, Fin (c i)) ≃ Fin N :=
  Fintype.equivFinOfCardEq (card_sigma_fin c hc)

/-- The grouping map: `v : Fin N` is sent to the index of the fiber containing it. -/
private noncomputable def groupMap {ι : Type} [Fintype ι] {N : ℕ} (c : ι → ℕ)
    (hc : ∑ i, c i = N) : Fin N → ι :=
  fun v => ((groupEquiv c hc).symm v).1

/-- The `groupMap` fiber over `i` has exactly `c i` elements. -/
private lemma card_groupMap_fiber {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (c : ι → ℕ) (hc : ∑ i, c i = N) (i : ι) :
    (Finset.univ.filter (fun v : Fin N => groupMap c hc v = i)).card = c i := by
  rw [Finset.card_filter]
  have h1 : ∑ v : Fin N, (if groupMap c hc v = i then 1 else 0)
      = ∑ p : Σ j : ι, Fin (c j), (if p.1 = i then 1 else 0) :=
    Fintype.sum_equiv (groupEquiv c hc).symm _ _ (fun _ => rfl)
  rw [h1, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  have h2 : ∀ j : ι, (∑ _x : Fin (c j), if j = i then (1 : ℕ) else 0)
      = if j = i then c j else 0 := by
    intro j
    by_cases h : j = i <;> simp [h]
  rw [Finset.sum_congr rfl fun j _ => h2 j,
    Finset.sum_ite_eq' Finset.univ i (fun j => c j)]
  simp

/-! ### The regrouped partition of `[0,1]` -/

/-- The mass of the `g ∘ intervalIdx` fiber over `i` is `(fiber card)/(M+1)`. -/
private lemma unitMeasure_groupFiber (M : ℕ) {ι : Type} [DecidableEq ι]
    (g : Fin (M + 1) → ι) (i : ι) :
    unitMeasure ((fun x => g (intervalIdx M x)) ⁻¹' {i})
      = ((Finset.univ.filter (fun v => g v = i)).card : ℝ≥0∞) * ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  have hset : ((fun x => g (intervalIdx M x)) ⁻¹' {i})
      = intervalIdx M ⁻¹'
          ((Finset.univ.filter (fun v => g v = i) : Finset (Fin (M + 1))) : Set (Fin (M + 1))) := by
    ext x
    simp
  rw [hset]
  exact unitMeasure_intervalIdx_preimage_finset M _

/-- **The regrouped partition** of `([0,1], unitMeasure)`: part `i` is the union of the
    `M+1`-grid subintervals whose index is sent to `i` by `g`. -/
private noncomputable def regroupPartition (M : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (g : Fin (M + 1) → ι)
    (hg : ∀ i : ι, 0 < (Finset.univ.filter (fun v => g v = i)).card) :
    MeasPartition ℝ unitMeasure where
  ι := ι
  part i := (fun x => g (intervalIdx M x)) ⁻¹' {i}
  measurable_part i := ((measurable_of_countable g).comp (measurable_intervalIdx M))
    (MeasurableSet.singleton i)
  pos i := by
    rw [unitMeasure_groupFiber M g i]
    exact ENNReal.mul_pos (by exact_mod_cast (hg i).ne')
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  block x := g (intervalIdx M x)
  measurable_block := (measurable_of_countable g).comp (measurable_intervalIdx M)
  block_preimage _ := rfl
  mem_block _ := rfl

private lemma regroupPartition_mass (M : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (g : Fin (M + 1) → ι)
    (hg : ∀ i : ι, 0 < (Finset.univ.filter (fun v => g v = i)).card) (i : ι) :
    unitMeasure ((regroupPartition M g hg).part i)
      = ((Finset.univ.filter (fun v => g v = i)).card : ℝ≥0∞) * ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
  unitMeasure_groupFiber M g i

/-! ### The block-average finite weighted graph -/

/-- The finite weighted graph on `M+1` vertices whose `(v,w)` entry is the `P`-block average of
    `W` over the blocks `g v`, `g w`. -/
private noncomputable def avgGraphon {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Graphon Ω μ) (P : MeasPartition Ω μ) {M : ℕ}
    (g : Fin (M + 1) → P.ι) : Graphon (Fin (M + 1)) (unifFin (M + 1)) :=
  Graphon.mk' (fun v w => blockAvg W.toSymmKernel P (g v) (g w))
    (fun v w => blockAvg_symm W.toSymmKernel P (g v) (g w))
    (measurable_of_countable _)
    (fun v w => (blockAvg_mem_Icc W P (g v) (g w)).1)
    (fun v w => (blockAvg_mem_Icc W P (g v) (g w)).2)

/-- A block average of a kernel that is constant on the block rectangle equals that constant. -/
private lemma blockAvg_of_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (K : SymmKernel Ω μ) (P : MeasPartition Ω μ) (i j : P.ι)
    (v : ℝ) (h : ∀ x ∈ P.part i, ∀ y ∈ P.part j, K.toFun x y = v) :
    blockAvg K P i j = v := by
  have hi := P.toReal_measure_part_pos i
  have hj := P.toReal_measure_part_pos j
  have hR : MeasurableSet ((P.part i) ×ˢ (P.part j)) :=
    (P.measurable_part i).prod (P.measurable_part j)
  unfold blockAvg
  rw [setIntegral_congr_fun hR (fun p hp => h p.1 hp.1 p.2 hp.2), setIntegral_const,
    smul_eq_mul, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  exact mul_div_cancel_left₀ v (mul_pos hi hj).ne'

/-! ### The key estimate -/

/-- **Step graphon vs finite weighted graph**: the cut distance between `stepGraphon W P` and the
    unit-interval pullback of the block-average finite weighted graph (on `M+1` vertices, fibers
    of sizes `c i`) is bounded by twice the total mass-rounding error. -/
private lemma cutDist_step_toUnit_le (W : Graphon ℝ unitMeasure)
    (P : MeasPartition ℝ unitMeasure) [DecidableEq P.ι] {k : ℕ} (e : P.ι ≃ Fin k)
    (M : ℕ) (c : P.ι → ℕ) (hc1 : ∀ i, 1 ≤ c i) (hcsum : ∑ i, c i = M + 1) :
    cutDist (stepGraphon W P)
        (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩)
      ≤ 2 * ∑ i : P.ι, |(unitMeasure (P.part i)).toReal - (c i : ℝ) / ((M : ℝ) + 1)| := by
  have hfib : ∀ i : P.ι,
      0 < (Finset.univ.filter (fun v => groupMap c hcsum v = i)).card := by
    intro i
    rw [card_groupMap_fiber c hcsum i]
    exact hc1 i
  set Q : MeasPartition ℝ unitMeasure := regroupPartition M (groupMap c hcsum) hfib with hQdef
  -- The pullback is constant on the rectangles of `Q`, with value the `P`-block average.
  have hconst : ∀ (i j : P.ι), ∀ x ∈ Q.part i, ∀ y ∈ Q.part j,
      (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩).toFun x y
        = blockAvg W.toSymmKernel P i j := by
    intro i j x hx y hy
    have hx' : groupMap c hcsum (intervalIdx M x) = i := hx
    have hy' : groupMap c hcsum (intervalIdx M y) = j := hy
    show blockAvg W.toSymmKernel P (groupMap c hcsum (intervalIdx M x))
        (groupMap c hcsum (intervalIdx M y)) = blockAvg W.toSymmKernel P i j
    rw [hx', hy']
  have hQavg : ∀ i j : P.ι,
      blockAvg (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩).toSymmKernel Q i j
        = blockAvg W.toSymmKernel P i j := fun i j =>
    blockAvg_of_const _ Q i j _ (hconst i j)
  -- The pullback is its own step graphon w.r.t. `Q`.
  have hstep : stepGraphon (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩) Q
      = FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩ := by
    apply graphon_ext
    intro x y
    show blockAvg
        (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩).toSymmKernel Q
        (Q.block x) (Q.block y)
      = (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩).toFun x y
    rw [hQavg]
    exact (hconst (Q.block x) (Q.block y) x (Q.mem_block x) y (Q.mem_block y)).symm
  -- Matched blocks have equal averages.
  have hmatch : ∀ i j k₂ l, e i = e j → e k₂ = e l →
      |blockAvg W.toSymmKernel P i k₂
        - blockAvg
            (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩).toSymmKernel Q j l|
      ≤ 0 := by
    intro i j k₂ l hij hkl
    obtain rfl : i = j := e.injective hij
    obtain rfl : k₂ = l := e.injective hkl
    rw [hQavg, sub_self, abs_zero]
  have hkey := cutDist_step_le_of_equiv (μ := unitMeasure) W
    (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩) P Q e e 0 le_rfl hmatch
  rw [hstep, zero_add] at hkey
  refine hkey.trans ?_
  -- Bound the mass-mismatch sum by the rounding error.
  have hterm : ∀ i : P.ι,
      (unitMeasure (P.part i)
          - min (unitMeasure (P.part i)) (unitMeasure (Q.part i))).toReal
        ≤ |(unitMeasure (P.part i)).toReal - (c i : ℝ) / ((M : ℝ) + 1)| := by
    intro i
    have hPt : unitMeasure (P.part i) ≠ ∞ := P.measure_part_ne_top i
    have hQr : (unitMeasure (Q.part i)).toReal = (c i : ℝ) / ((M : ℝ) + 1) := by
      have h1 : unitMeasure (Q.part i) = (c i : ℝ≥0∞) * ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        have hm := regroupPartition_mass M (groupMap c hcsum) hfib i
        rw [card_groupMap_fiber c hcsum i] at hm
        exact hm
      rw [h1, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_natCast]
      push_cast
      rw [div_eq_mul_inv]
    rcases le_total (unitMeasure (P.part i)) (unitMeasure (Q.part i)) with hle | hle
    · rw [min_eq_left hle, tsub_self]
      simp
    · rw [min_eq_right hle, ENNReal.toReal_sub_of_le hle hPt, hQr]
      exact le_abs_self _
  have hS : (∑ a : Fin k, (unitMeasure (P.part (e.symm a))
        - min (unitMeasure (P.part (e.symm a))) (unitMeasure (Q.part (e.symm a)))).toReal)
      ≤ ∑ i : P.ι, |(unitMeasure (P.part i)).toReal - (c i : ℝ) / ((M : ℝ) + 1)| := by
    rw [← Equiv.sum_comp e.symm
      (fun i : P.ι => |(unitMeasure (P.part i)).toReal - (c i : ℝ) / ((M : ℝ) + 1)|)]
    exact Finset.sum_le_sum fun a _ => hterm (e.symm a)
  exact mul_le_mul_of_nonneg_left hS (by norm_num)

/-! ### The main theorem -/

/-- **Finite weighted graphs are dense in the cut distance**: every graphon on
    `([0,1], unitMeasure)` is within cut distance `ε` of the unit-interval pullback of some
    finite weighted graph. -/
theorem exists_finWeighted_cutDist_le (W : Graphon ℝ unitMeasure) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : FinWeighted, cutDist G.toUnit W ≤ ε := by
  classical
  obtain ⟨P, hP⟩ := exists_stepGraphon_cutDist_le W (show (0 : ℝ) < ε / 2 by linarith)
  haveI : Nonempty P.ι := ⟨P.block 0⟩
  haveI : DecidableEq P.ι := Classical.decEq _
  obtain ⟨M, c, hc1, hcsum, hcerr⟩ := exists_rounding (Classical.arbitrary P.ι)
    (fun i => (unitMeasure (P.part i)).toReal)
    (fun i => P.toReal_measure_part_pos i)
    P.sum_toReal_measure_part_eq_one
    (show (0 : ℝ) < ε / 8 by linarith)
  have hcerr' : ∑ i, |(unitMeasure (P.part i)).toReal - (c i : ℝ) / ((M : ℝ) + 1)| ≤ ε / 8 :=
    hcerr
  refine ⟨⟨M, avgGraphon W P (groupMap c hcsum)⟩, ?_⟩
  have hkey := cutDist_step_toUnit_le W P (Fintype.equivFin P.ι) M c hc1 hcsum
  have h1 : cutDist (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩)
      (stepGraphon W P) ≤ ε / 4 := by
    rw [cutDist_comm]
    refine hkey.trans ?_
    linarith
  have h2 : cutDist (stepGraphon W P) W ≤ ε / 2 := by
    rw [cutDist_comm]
    exact hP
  have htri := cutDist_triangle
    (FinWeighted.toUnit ⟨M, avgGraphon W P (groupMap c hcsum)⟩) (stepGraphon W P) W
  linarith

end Graphons
