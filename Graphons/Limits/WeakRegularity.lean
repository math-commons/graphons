/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits), Tier C:
  **Weak regularity lemma (cut-norm form), energy-increment proof.**
  For every `ε > 0` and graphon `W` there is a finite measurable partition `P` of `Ω` with
    `cutNorm (W − stepW W P) ≤ ε`,
  where `stepW W P` is the block-averaged (conditional-expectation) step kernel.
  Source: Lovász, "Large Networks and Graph Limits" (2012), §9.2 (Frieze–Kannan weak
  regularity via the energy-increment argument).

This is **Phase 1**: framework + statement + the easy infrastructure proved sorry-free, with the
genuinely-analytic core(s) isolated as the fewest, finest labelled `sorry`s.

DESIGN.
* `MeasPartition Ω μ` — a finite measurable partition: an index `Fintype`, a family of measurable
  parts of positive measure, with a measurable block-assignment `block : Ω → ι` landing each point
  in its part.  (Exact disjoint cover, encoded by `block`; this is all `stepW` needs and keeps the
  step kernel pointwise-clean.)
* `stepW W P : SymmKernel Ω μ` — the **explicit block average**: on `(x,y)`, with `i = block x`,
  `j = block y`, output `(∫_{Pᵢ×Pⱼ} W) / (μ Pᵢ * μ Pⱼ)`.  (NOT `condExp`: an explicit average gives
  pointwise symmetry/measurability/boundedness directly, which is what `SymmKernel` requires.)
* `energy W P := ∫ (stepW W P)²` — the `L²` energy.
-/
import Graphons.CutMetric.CutNormSet

open MeasureTheory
open scoped ENNReal NNReal

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Finite measurable partitions -/

/-- A **finite measurable partition** of `(Ω, μ)`: a finite index type `ι`, a family of measurable
    parts `part i` each of *positive* measure, together with a measurable block-assignment
    `block : Ω → ι` placing every point into its part.  This encodes an (exact) disjoint cover:
    `block` selects, for each `x`, the unique part containing it. -/
structure MeasPartition (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The (finite) index type of the parts (in `Type` — finite indices need no higher universe). -/
  ι : Type
  /-- `ι` is finite. -/
  [fintype : Fintype ι]
  /-- `ι` carries a `MeasurableSpace` so `block` can be `Measurable`. -/
  [measurableSpace : MeasurableSpace ι]
  /-- Singletons of `ι` are measurable (so functions out of the finite `ι` are measurable). -/
  [singletonClass : MeasurableSingletonClass ι]
  /-- The parts of the partition. -/
  part : ι → Set Ω
  /-- Each part is measurable. -/
  measurable_part : ∀ i, MeasurableSet (part i)
  /-- Each part has positive measure (no empty blocks). -/
  pos : ∀ i, 0 < μ (part i)
  /-- The block-assignment: the index of the part containing a point. -/
  block : Ω → ι
  /-- `block` is measurable (`ι` carrying its top σ-algebra via `Fintype`). -/
  measurable_block : Measurable block
  /-- The parts are *exactly* the fibers of `block`: `block ⁻¹' {i} = part i`.  This is what makes
      `(part i)` a genuine (disjoint, exact) partition of `Ω` indexed by `block`, so that the
      part-average `blockAvg` coincides with the fiber-conditional expectation that `stepW`
      represents.  (Implies both `mem_block` and disjointness of the parts.) -/
  block_preimage : ∀ i, block ⁻¹' {i} = part i
  /-- Each point lies in the part its block names. -/
  mem_block : ∀ x, x ∈ part (block x)

namespace MeasPartition

attribute [instance] MeasPartition.fintype MeasPartition.measurableSpace
  MeasPartition.singletonClass

variable [IsProbabilityMeasure μ]

/-- The measure of a part is finite (probability measure). -/
theorem measure_part_ne_top (P : MeasPartition Ω μ) (i : P.ι) : μ (P.part i) ≠ ∞ :=
  (measure_ne_top μ _)

/-- The (real) measure of a part is positive. -/
theorem toReal_measure_part_pos (P : MeasPartition Ω μ) (i : P.ι) :
    0 < (μ (P.part i)).toReal :=
  ENNReal.toReal_pos (P.pos i).ne' (P.measure_part_ne_top i)

/-- The block measures sum to `1` (the parts are a measurable disjoint cover of `Ω`). -/
theorem sum_toReal_measure_part_eq_one (P : MeasPartition Ω μ) :
    (∑ i, (μ (P.part i)).toReal) = 1 := by
  classical
  have hcover : (∑ i, μ (P.part i)) = 1 := by
    have h := MeasureTheory.sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset P.ι)
      (f := P.block) (fun i _ => by rw [P.block_preimage i]; exact P.measurable_part i)
    simp only [P.block_preimage] at h
    rw [h]
    simp only [Finset.coe_univ, Set.preimage_univ, measure_univ]
  rw [← ENNReal.toReal_sum (fun i _ => P.measure_part_ne_top i), hcover, ENNReal.toReal_one]

omit [IsProbabilityMeasure μ] in
/-- A point lies in `part i` iff its block is `i` (parts are exactly the fibers of `block`). -/
theorem mem_part_iff (P : MeasPartition Ω μ) (x : Ω) (i : P.ι) :
    x ∈ P.part i ↔ P.block x = i := by
  rw [← P.block_preimage i]; rfl

omit [IsProbabilityMeasure μ] in
/-- The indicator of `part i` at `x` is `1` if `block x = i`. -/
theorem indicator_part_eq_one (P : MeasPartition Ω μ) {x : Ω} {i : P.ι} (h : P.block x = i) :
    Set.indicator (P.part i) (1 : Ω → ℝ) x = 1 :=
  Set.indicator_of_mem ((P.mem_part_iff x i).2 h) _

omit [IsProbabilityMeasure μ] in
/-- The indicator of `part i` at `x` is `0` if `block x ≠ i`. -/
theorem indicator_part_eq_zero (P : MeasPartition Ω μ) {x : Ω} {i : P.ι} (h : P.block x ≠ i) :
    Set.indicator (P.part i) (1 : Ω → ℝ) x = 0 :=
  Set.indicator_of_notMem (fun hx => h ((P.mem_part_iff x i).1 hx)) _

omit [IsProbabilityMeasure μ] in
/-- The indicator of `part i` at `x` is bounded by `1` in absolute value. -/
theorem abs_indicator_part_le_one (P : MeasPartition Ω μ) (x : Ω) (i : P.ι) :
    |Set.indicator (P.part i) (1 : Ω → ℝ) x| ≤ 1 := by
  by_cases h : P.block x = i
  · rw [P.indicator_part_eq_one h]; norm_num
  · rw [P.indicator_part_eq_zero h]; norm_num

end MeasPartition

/-! ## The block-averaged step kernel `stepW` -/

variable [IsProbabilityMeasure μ]

/-- The block average value of `W` on the block `part i × part j`:
    `(∫_{part i × part j} W) / (μ (part i) * μ (part j))`.  This is the constant value the step
    kernel takes on that block.  Defined as an explicit average over a measurable rectangle. -/
noncomputable def blockAvg (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) (i j : P.ι) : ℝ :=
  (∫ p in (P.part i) ×ˢ (P.part j), W.toFun p.1 p.2 ∂(μ.prod μ))
    / ((μ (P.part i)).toReal * (μ (P.part j)).toReal)

/-- The block average is **symmetric** in its two block indices (since `W` is symmetric).  This is
    the key fact making `stepW` a `SymmKernel`. -/
theorem blockAvg_symm (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) (i j : P.ι) :
    blockAvg W P i j = blockAvg W P j i := by
  unfold blockAvg
  rw [mul_comm ((μ (P.part i)).toReal)]
  congr 1
  -- ∫_{Pi×Pj} W(x,y) = ∫_{Pj×Pi} W(x,y) by swapping coordinates and using W symmetric
  have hswap := setIntegral_prod_swap (μ := μ) (ν := μ) (P.part j) (P.part i)
    (fun p : Ω × Ω => W.toFun p.2 p.1)
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  rw [hswap]
  refine setIntegral_congr_fun ((P.measurable_part j).prod (P.measurable_part i)) ?_
  intro p _
  exact (W.symm' p.2 p.1)

/-- Pointwise bound on the block average: `|blockAvg W P i j| ≤ W.bound`.  (The average of values in
    `[-C, C]` over a positive-measure rectangle lies in `[-C, C]`.) -/
theorem abs_blockAvg_le_bound (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) (i j : P.ι) :
    |blockAvg W P i j| ≤ W.bound := by
  have hi := P.toReal_measure_part_pos i
  have hj := P.toReal_measure_part_pos j
  have hden : 0 < (μ (P.part i)).toReal * (μ (P.part j)).toReal := mul_pos hi hj
  unfold blockAvg
  rw [abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  -- |∫_{Pi×Pj} W| ≤ ∫_{Pi×Pj} W.bound = W.bound * μ(Pi×Pj) = W.bound * μPi.toReal * μPj.toReal
  set R : Set (Ω × Ω) := (P.part i) ×ˢ (P.part j) with hR
  have hRmeas : MeasurableSet R := (P.measurable_part i).prod (P.measurable_part j)
  have hWint : Integrable (Function.uncurry W.toFun) (μ.prod μ) := W.integrable_uncurry
  have hWintR : Integrable (fun p => W.toFun p.1 p.2) ((μ.prod μ).restrict R) :=
    hWint.restrict
  calc |∫ p in R, W.toFun p.1 p.2 ∂(μ.prod μ)|
      ≤ ∫ p in R, |W.toFun p.1 p.2| ∂(μ.prod μ) := by
        simpa [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := (μ.prod μ).restrict R)
            (fun p => W.toFun p.1 p.2))
    _ ≤ ∫ _ in R, W.bound ∂(μ.prod μ) := by
        refine setIntegral_mono_on hWintR.abs ?_ hRmeas (fun p _ => W.abs_le_bound p.1 p.2)
        exact (integrable_const W.bound).restrict
    _ = W.bound * ((μ.prod μ).real R) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]
    _ = W.bound * ((μ (P.part i)).toReal * (μ (P.part j)).toReal) := by
        rw [measureReal_def, hR, Measure.prod_prod, ENNReal.toReal_mul]

/-- The **step kernel** of `W` w.r.t. partition `P`: the block-averaged kernel, constant on each
    block `part i × part j` with value `blockAvg W P i j`.  It is a genuine `SymmKernel`:
    symmetric (from `blockAvg_symm`), measurable (`block` is measurable and `ι` is discrete), and
    bounded (by `W.bound`, from `abs_blockAvg_le_bound`). -/
noncomputable def stepW (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) : SymmKernel Ω μ where
  toFun x y := blockAvg W P (P.block x) (P.block y)
  symm' x y := blockAvg_symm W P (P.block x) (P.block y)
  meas' := by
    -- `ι` carries the top σ-algebra, so every function out of `ι × ι` is measurable; precompose
    -- with the measurable `block × block`.
    have hbb : Measurable (fun p : Ω × Ω => (P.block p.1, P.block p.2)) :=
      (P.measurable_block.comp measurable_fst).prodMk (P.measurable_block.comp measurable_snd)
    have hf : Measurable (fun q : P.ι × P.ι => blockAvg W P q.1 q.2) :=
      measurable_of_countable _
    exact hf.comp hbb
  bdd' := ⟨W.bound, fun x y => abs_blockAvg_le_bound W P (P.block x) (P.block y)⟩

@[simp] theorem stepW_apply (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) (x y : Ω) :
    (stepW W P).toFun x y = blockAvg W P (P.block x) (P.block y) := rfl

/-- `stepW` is pointwise bounded by `W.bound`. -/
theorem abs_stepW_le_bound (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) (x y : Ω) :
    |(stepW W P).toFun x y| ≤ W.bound :=
  abs_blockAvg_le_bound W P (P.block x) (P.block y)

/-! ## Energy -/

/-- The **energy** of `W` relative to partition `P`: the `L²`-norm-squared of the step kernel,
    `∫∫ (stepW W P)²`.  (Lovász §9.2; the increasing-energy quantity driving the iteration.) -/
noncomputable def energy (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) : ℝ :=
  ∫ p, ((stepW W P).toFun p.1 p.2) ^ 2 ∂(μ.prod μ)

/-- The squared step integrand is integrable (bounded by `W.bound²`). -/
theorem integrable_stepW_sq (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) :
    Integrable (fun p : Ω × Ω => ((stepW W P).toFun p.1 p.2) ^ 2) (μ.prod μ) := by
  refine SymmKernel.integrable_of_bdd ?_ (C := W.bound ^ 2) (fun p => ?_)
  · exact ((stepW W P).meas'.pow_const 2)
  · rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_stepW_le_bound W P p.1 p.2) 2

/-- **Energy is nonnegative** (it is an integral of a square). -/
theorem energy_nonneg (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) : 0 ≤ energy W P :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- For a graphon (`0 ≤ W ≤ 1`), the block average lies in `[0,1]`. -/
theorem blockAvg_mem_Icc (W : Graphon Ω μ) (P : MeasPartition Ω μ) (i j : P.ι) :
    blockAvg W.toSymmKernel P i j ∈ Set.Icc (0 : ℝ) 1 := by
  have hi := P.toReal_measure_part_pos i
  have hj := P.toReal_measure_part_pos j
  have hden : 0 < (μ (P.part i)).toReal * (μ (P.part j)).toReal := mul_pos hi hj
  set R : Set (Ω × Ω) := (P.part i) ×ˢ (P.part j) with hR
  have hRmeas : MeasurableSet R := (P.measurable_part i).prod (P.measurable_part j)
  have hWint : Integrable (fun p => W.toFun p.1 p.2) ((μ.prod μ).restrict R) :=
    (W.toSymmKernel.integrable_uncurry).restrict
  have hmeasReal : (μ.prod μ).real R = (μ (P.part i)).toReal * (μ (P.part j)).toReal := by
    rw [measureReal_def, hR, Measure.prod_prod, ENNReal.toReal_mul]
  refine ⟨?_, ?_⟩
  · -- 0 ≤ avg : numerator ≥ 0
    rw [blockAvg]
    apply div_nonneg _ (le_of_lt hden)
    exact setIntegral_nonneg hRmeas (fun p _ => W.nonneg' p.1 p.2)
  · -- avg ≤ 1 : numerator ≤ μ(R).toReal = denominator
    rw [blockAvg, div_le_one hden]
    calc ∫ p in R, W.toFun p.1 p.2 ∂(μ.prod μ)
        ≤ ∫ _ in R, (1 : ℝ) ∂(μ.prod μ) := by
          refine setIntegral_mono_on hWint ?_ hRmeas (fun p _ => W.le_one' p.1 p.2)
          exact (integrable_const 1).restrict
      _ = (μ.prod μ).real R := by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = (μ (P.part i)).toReal * (μ (P.part j)).toReal := hmeasReal

/-- For a graphon, `stepW` is `[0,1]`-valued. -/
theorem stepW_mem_Icc (W : Graphon Ω μ) (P : MeasPartition Ω μ) (x y : Ω) :
    (stepW W.toSymmKernel P).toFun x y ∈ Set.Icc (0 : ℝ) 1 :=
  blockAvg_mem_Icc W P (P.block x) (P.block y)

/-- **Energy is bounded by `1`** for a graphon: the step kernel is `[0,1]`-valued, so its square is
    `≤ 1`, and `μ ×ˢ μ` is a probability measure. -/
theorem energy_le_one (W : Graphon Ω μ) (P : MeasPartition Ω μ) :
    energy W.toSymmKernel P ≤ 1 := by
  unfold energy
  calc ∫ p, ((stepW W.toSymmKernel P).toFun p.1 p.2) ^ 2 ∂(μ.prod μ)
      ≤ ∫ _, (1 : ℝ) ∂(μ.prod μ) := by
        refine integral_mono (integrable_stepW_sq _ _) (integrable_const 1) (fun p => ?_)
        have h := stepW_mem_Icc W P p.1 p.2
        nlinarith [h.1, h.2]
    _ = 1 := by simp

/-! ## Energy as a finite block sum

The step kernel is block-constant, so its integrals reduce to finite sums over `P.ι × P.ι`
weighted by the block measures.  `integral_block_const` is the general fact; `energy_eq_sum`
is the `G = (blockAvg)²` instance. -/

/-- A point's first coordinate indicator picks out its block: a useful pointwise rewrite. -/
private theorem indicator_block_prod (P : MeasPartition Ω μ) (G : P.ι → P.ι → ℝ) (p : Ω × Ω) :
    (∑ i, ∑ j, G i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
        * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2))
      = G (P.block p.1) (P.block p.2) := by
  classical
  rw [Finset.sum_eq_single (P.block p.1)]
  · rw [Finset.sum_eq_single (P.block p.2)]
    · rw [P.indicator_part_eq_one (rfl), P.indicator_part_eq_one (rfl)]; ring
    · intro j _ hj; rw [P.indicator_part_eq_zero (Ne.symm hj)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    rw [P.indicator_part_eq_zero (Ne.symm hi)]
    rw [Finset.sum_eq_zero]; intro j _; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Block-integral decomposition.**  For any `G : P.ι → P.ι → ℝ`, the integral of the
    block-constant function `(x,y) ↦ G (block x) (block y)` against `μ ×ˢ μ` is the finite sum
    `∑ i ∑ j, μ(part i).toReal · μ(part j).toReal · G i j`.  (Parts are the fibers of `block`.) -/
theorem integral_block_const (P : MeasPartition Ω μ) (G : P.ι → P.ι → ℝ) :
    (∫ p, G (P.block p.1) (P.block p.2) ∂(μ.prod μ))
      = ∑ i, ∑ j, (μ (P.part i)).toReal * (μ (P.part j)).toReal * G i j := by
  classical
  -- rewrite the integrand as a finite sum of indicator-scaled constants
  have hpt : ∀ p : Ω × Ω, G (P.block p.1) (P.block p.2)
      = ∑ i, ∑ j, G i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
          * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2) := by
    intro p; rw [indicator_block_prod P G p]
  rw [integral_congr_ae (ae_of_all _ hpt)]
  -- integrability of each summand
  have hint : ∀ i j, Integrable (fun p : Ω × Ω =>
      G i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
        * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)) (μ.prod μ) := by
    intro i j
    have hb : ∀ p : Ω × Ω,
        |G i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
          * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)| ≤ |G i j| := by
      intro p
      rw [abs_mul, abs_mul]
      have h1 : |Set.indicator (P.part i) (1 : Ω → ℝ) p.1| ≤ 1 :=
        P.abs_indicator_part_le_one p.1 i
      have h2 : |Set.indicator (P.part j) (1 : Ω → ℝ) p.2| ≤ 1 :=
        P.abs_indicator_part_le_one p.2 j
      calc |G i j| * |Set.indicator (P.part i) (1 : Ω → ℝ) p.1|
              * |Set.indicator (P.part j) (1 : Ω → ℝ) p.2|
          ≤ |G i j| * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2 (abs_nonneg _)
              (mul_nonneg (abs_nonneg _) (by norm_num))
        _ = |G i j| := by ring
    have hmeas : Measurable (fun p : Ω × Ω =>
        G i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
          * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)) := by
      refine (measurable_const.mul ?_).mul ?_
      · exact (((measurable_const).indicator (P.measurable_part i)).comp measurable_fst)
      · exact (((measurable_const).indicator (P.measurable_part j)).comp measurable_snd)
    exact SymmKernel.integrable_of_bdd hmeas hb
  -- swap integral and the two finite sums
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finset_sum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- single term: ∫ Gij · 𝟙_{Pi}(x) · 𝟙_{Pj}(y) = Gij · μPi · μPj
  have hrw : ∀ p : Ω × Ω,
      G i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
        * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)
      = G i j * Set.indicator (P.part i ×ˢ P.part j) (1 : Ω × Ω → ℝ) p := by
    intro p; rw [mul_assoc, Set.indicator_prod_one]
  rw [integral_congr_ae (ae_of_all _ hrw), integral_const_mul, integral_indicator_one
    ((P.measurable_part i).prod (P.measurable_part j)), measureReal_def, Measure.prod_prod,
    ENNReal.toReal_mul]
  ring

/-- **Integral against a block-constant coefficient.**  For a kernel `V` and block-constant
    coefficients `K (block x) (block y)`, the integral `∫ V·(K∘block⊗block)` decomposes as the
    finite sum of `K i j · ∫_{Pi×Pj} V`.  (Like `integral_block_const`, but `V` need not be
    block-constant; this is the inner-product of `V` against a block-constant function.) -/
theorem integral_mul_block_const (V : SymmKernel Ω μ) (P : MeasPartition Ω μ)
    (K : P.ι → P.ι → ℝ) :
    (∫ p, V.toFun p.1 p.2 * K (P.block p.1) (P.block p.2) ∂(μ.prod μ))
      = ∑ i, ∑ j, K i j * ∫ p in (P.part i) ×ˢ (P.part j), V.toFun p.1 p.2 ∂(μ.prod μ) := by
  classical
  -- pointwise: V·(K∘block) = ∑∑ V · K i j · 𝟙_Pi(x) · 𝟙_Pj(y)
  have hpt : ∀ p : Ω × Ω, V.toFun p.1 p.2 * K (P.block p.1) (P.block p.2)
      = ∑ i, ∑ j, V.toFun p.1 p.2 * K i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
          * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2) := by
    intro p
    rw [← indicator_block_prod P K p, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [integral_congr_ae (ae_of_all _ hpt)]
  -- integrability of each summand (bounded by |Kij|·V.bound)
  have hint : ∀ i j, Integrable (fun p : Ω × Ω =>
      V.toFun p.1 p.2 * K i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
        * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)) (μ.prod μ) := by
    intro i j
    have hb : ∀ p : Ω × Ω,
        |V.toFun p.1 p.2 * K i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
          * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)| ≤ V.bound * |K i j| := by
      intro p
      rw [abs_mul, abs_mul, abs_mul]
      have h1 : |Set.indicator (P.part i) (1 : Ω → ℝ) p.1| ≤ 1 := P.abs_indicator_part_le_one p.1 i
      have h2 : |Set.indicator (P.part j) (1 : Ω → ℝ) p.2| ≤ 1 := P.abs_indicator_part_le_one p.2 j
      have hVb := V.abs_le_bound p.1 p.2
      have hKnn : (0:ℝ) ≤ |K i j| := abs_nonneg _
      have hstep : |V.toFun p.1 p.2| * |K i j| * |Set.indicator (P.part i) (1 : Ω → ℝ) p.1|
              * |Set.indicator (P.part j) (1 : Ω → ℝ) p.2|
          ≤ V.bound * |K i j| * 1 * 1 := by
        apply mul_le_mul _ h2 (abs_nonneg _)
          (mul_nonneg (mul_nonneg V.bound_nonneg hKnn) zero_le_one)
        apply mul_le_mul _ h1 (abs_nonneg _) (mul_nonneg V.bound_nonneg hKnn)
        exact mul_le_mul hVb le_rfl hKnn V.bound_nonneg
      calc |V.toFun p.1 p.2| * |K i j| * |Set.indicator (P.part i) (1 : Ω → ℝ) p.1|
              * |Set.indicator (P.part j) (1 : Ω → ℝ) p.2|
          ≤ V.bound * |K i j| * 1 * 1 := hstep
        _ = V.bound * |K i j| := by ring
    have hmeas : Measurable (fun p : Ω × Ω =>
        V.toFun p.1 p.2 * K i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
          * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)) := by
      refine (((V.meas'.mul measurable_const).mul ?_).mul ?_)
      · exact (((measurable_const).indicator (P.measurable_part i)).comp measurable_fst)
      · exact (((measurable_const).indicator (P.measurable_part j)).comp measurable_snd)
    exact SymmKernel.integrable_of_bdd hmeas hb
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finset_sum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- single term: ∫ V·Kij·𝟙_Pi·𝟙_Pj = Kij·∫_{Pi×Pj} V
  have hrw : ∀ p : Ω × Ω,
      V.toFun p.1 p.2 * K i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
        * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)
      = K i j * (V.toFun p.1 p.2 * Set.indicator (P.part i ×ˢ P.part j) (1 : Ω × Ω → ℝ) p) := by
    intro p
    rw [show V.toFun p.1 p.2 * K i j * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1)
            * (Set.indicator (P.part j) (1 : Ω → ℝ) p.2)
          = K i j * (V.toFun p.1 p.2 * (Set.indicator (P.part i) (1 : Ω → ℝ) p.1
            * Set.indicator (P.part j) (1 : Ω → ℝ) p.2)) by ring,
      Set.indicator_prod_one]
  rw [integral_congr_ae (ae_of_all _ hrw), integral_const_mul]
  congr 1
  rw [← integral_indicator ((P.measurable_part i).prod (P.measurable_part j))]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  by_cases hp : p ∈ (P.part i) ×ˢ (P.part j)
  · simp only [Set.indicator_of_mem hp, Pi.one_apply, mul_one]
  · simp only [Set.indicator_of_notMem hp, mul_zero]

/-- **Energy as a finite block sum.**  `energy W P = ∑ i ∑ j μPi·μPj·(blockAvg W P i j)²`. -/
theorem energy_eq_sum (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) :
    energy W P = ∑ i, ∑ j,
      (μ (P.part i)).toReal * (μ (P.part j)).toReal * (blockAvg W P i j) ^ 2 := by
  unfold energy
  rw [show (fun p : Ω × Ω => ((stepW W P).toFun p.1 p.2) ^ 2)
        = (fun p : Ω × Ω => (fun i j => (blockAvg W P i j) ^ 2) (P.block p.1) (P.block p.2)) from
      rfl]
  rw [integral_block_const P (fun i j => (blockAvg W P i j) ^ 2)]

/-! ## Refinement -/

/-- `P'` **refines** `P` (`P'` is finer) when the coarse block-assignment factors through the fine
    one: there is `f : P'.ι → P.ι` with `P.block = f ∘ P'.block`.  Equivalently every `P`-block is a
    union of `P'`-blocks, so the `P`-block σ-algebra is contained in the `P'`-block σ-algebra. -/
def IsRefinement (P' P : MeasPartition Ω μ) : Prop :=
  ∃ f : P'.ι → P.ι, ∀ x, P.block x = f (P'.block x)

omit [IsProbabilityMeasure μ] in
/-- Refinement is reflexive. -/
theorem IsRefinement.rfl (P : MeasPartition Ω μ) : IsRefinement P P :=
  ⟨id, fun _ => Eq.symm (id_eq _)⟩

omit [IsProbabilityMeasure μ] in
/-- Refinement is transitive. -/
theorem IsRefinement.trans {P'' P' P : MeasPartition Ω μ}
    (h₁ : IsRefinement P'' P') (h₂ : IsRefinement P' P) : IsRefinement P'' P := by
  obtain ⟨f, hf⟩ := h₂
  obtain ⟨g, hg⟩ := h₁
  exact ⟨f ∘ g, fun x => by rw [hf x, hg x, Function.comp_apply]⟩

/-! ## Constructing a refinement by intersecting with a measurable set

Given a `MeasPartition P` and a measurable set `A`, `refineBySet P A hA` splits every block of `P`
into its `A`- and `Aᶜ`-parts.  To keep the *positivity* invariant of `MeasPartition` we drop the
empty atoms by indexing over the subtype of positive-measure raw atoms, and we redirect any point
whose own atom is null into the (necessarily positive) sibling atom of its `P`-block. -/

namespace MeasPartition

section RefineBySet

open scoped Classical

variable (P : MeasPartition Ω μ) {A : Set Ω} (hA : MeasurableSet A)

omit [IsProbabilityMeasure μ]

/-- The raw `(i,b)`-atom: `part i ∩ A` (for `b = true`) or `part i ∩ Aᶜ` (for `b = false`). -/
private def rawPart (q : P.ι × Bool) : Set Ω := P.part q.1 ∩ (cond q.2 A Aᶜ)

include hA in
private theorem measurableSet_rawPart (q : P.ι × Bool) : MeasurableSet (P.rawPart (A := A) q) := by
  refine (P.measurable_part q.1).inter ?_
  cases q.2 <;> simp only [cond_true, cond_false]
  · exact hA.compl
  · exact hA

include hA in
/-- The two raw atoms of a block partition its measure. -/
private theorem measure_part_eq_add_rawPart (i : P.ι) :
    μ (P.part i) = μ (P.rawPart (A := A) (i, true)) + μ (P.rawPart (A := A) (i, false)) := by
  simp only [rawPart, cond_true, cond_false]
  rw [← measure_inter_add_diff (P.part i) hA, Set.diff_eq]

variable [IsProbabilityMeasure μ]

include hA in
/-- If one raw atom of a block is null, the sibling carries all of the (positive) block measure. -/
private theorem rawPart_sibling_pos (i : P.ι) {b : Bool} (h : ¬ 0 < μ (P.rawPart (A := A) (i, b))) :
    0 < μ (P.rawPart (A := A) (i, !b)) := by
  have hz : μ (P.rawPart (A := A) (i, b)) = 0 := by
    by_contra h0; exact h (pos_iff_ne_zero.2 h0)
  have hsum := P.measure_part_eq_add_rawPart hA i
  have hpos := P.pos i
  cases b with
  | false =>
    simp only [Bool.not_false] at *
    rw [hz, add_zero] at hsum
    rwa [← hsum]
  | true =>
    simp only [Bool.not_true] at *
    rw [hz, zero_add] at hsum
    rwa [← hsum]

/-- The chosen bool for `x` in block `i`: its own side `b` if that atom is positive, else `!b`. -/
private noncomputable def chosenBool (i : P.ι) (b : Bool) : Bool := by
  classical
  exact if 0 < μ (P.rawPart (A := A) (i, b)) then b else !b

include hA in
private theorem chosenBool_pos (i : P.ι) (b : Bool) :
    0 < μ (P.rawPart (A := A) (i, P.chosenBool (A := A) i b)) := by
  classical
  unfold chosenBool
  by_cases h : 0 < μ (P.rawPart (A := A) (i, b))
  · simpa [h] using h
  · simp only [h, if_false]
    exact P.rawPart_sibling_pos hA i h

/-- The index type of `refineBySet`: the positive-measure raw atoms. -/
@[reducible] private def refineIdx : Type := {q : P.ι × Bool // 0 < μ (P.rawPart (A := A) q)}

noncomputable instance : Fintype (P.refineIdx (A := A)) := by
  classical exact Subtype.fintype _

instance : MeasurableSpace (P.refineIdx (A := A)) := ⊤
instance : MeasurableSingletonClass (P.refineIdx (A := A)) := ⟨fun _ => trivial⟩

/-- The raw block-assignment landing in `P.ι × Bool`: `(P.block x, chosen side of x)`. -/
private noncomputable def rawBlockFn (x : Ω) : P.ι × Bool := by
  classical
  exact (P.block x, P.chosenBool (A := A) (P.block x) ((if x ∈ A then true else false)))

include hA in
private theorem rawBlockFn_pos (x : Ω) : 0 < μ (P.rawPart (A := A) (P.rawBlockFn (A := A) x)) := by
  classical
  simpa only [rawBlockFn] using P.chosenBool_pos hA (P.block x) ((if x ∈ A then true else false))

/-- The block-assignment of `refineBySet`, landing in the positive-atom subtype. -/
private noncomputable def blockFn (x : Ω) : P.refineIdx (A := A) :=
  ⟨P.rawBlockFn (A := A) x, P.rawBlockFn_pos hA x⟩

/-- The fiber `blockFn ⁻¹' {q}` written set-theoretically. -/
private theorem blockFn_preimage_eq (q : P.refineIdx (A := A)) :
    P.blockFn (A := A) hA ⁻¹' {q}
      = P.part q.1.1 ∩ {x | P.chosenBool (A := A) q.1.1 ((if x ∈ A then true else false)) = q.1.2} := by
  classical
  ext x
  simp only [blockFn, rawBlockFn, Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff,
    Prod.ext_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(P.mem_part_iff x q.1.1).2 h1, ?_⟩
    rw [← h1]; exact h2
  · rintro ⟨hx, h2⟩
    have h1 : P.block x = q.1.1 := (P.mem_part_iff x q.1.1).1 hx
    refine ⟨h1, ?_⟩
    rw [h1]; exact h2

include hA in
/-- Each `refineBySet` fiber is measurable. -/
private theorem measurableSet_blockFn_preimage (q : P.refineIdx (A := A)) :
    MeasurableSet (P.blockFn (A := A) hA ⁻¹' {q}) := by
  classical
  rw [blockFn_preimage_eq]
  refine (P.measurable_part q.1.1).inter ?_
  have heq : {x | P.chosenBool (A := A) q.1.1 ((if x ∈ A then true else false)) = q.1.2}
      = (if P.chosenBool (A := A) q.1.1 true = q.1.2 then A else ∅)
        ∪ (if P.chosenBool (A := A) q.1.1 false = q.1.2 then Aᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ A
    · simp only [Set.mem_setOf_eq, Set.mem_union, if_pos hx]
      by_cases hc : P.chosenBool (A := A) q.1.1 true = q.1.2 <;>
        simp [hc, hx, Set.mem_compl_iff]
    · simp only [Set.mem_setOf_eq, Set.mem_union, if_neg hx]
      by_cases hc : P.chosenBool (A := A) q.1.1 false = q.1.2 <;>
        simp [hc, hx, Set.mem_compl_iff]
  rw [heq]
  refine MeasurableSet.union ?_ ?_
  · split <;> [exact hA; exact MeasurableSet.empty]
  · split <;> [exact hA.compl; exact MeasurableSet.empty]

include hA in
/-- The raw atom `rawPart (i,b)` is contained in the `refineBySet` fiber of `(i,b)`. -/
private theorem rawPart_subset_blockFn_preimage (q : P.refineIdx (A := A)) :
    P.rawPart (A := A) q.1 ⊆ P.blockFn (A := A) hA ⁻¹' {q} := by
  classical
  intro x hx
  obtain ⟨⟨i, b⟩, hq⟩ := q
  simp only [rawPart] at hx
  obtain ⟨hxi, hxb⟩ := hx
  rw [blockFn_preimage_eq]
  refine ⟨hxi, ?_⟩
  simp only [Set.mem_setOf_eq]
  have hdec : ((if x ∈ A then true else false)) = b := by
    cases b with
    | true => simp only [cond_true] at hxb; simp [if_pos hxb]
    | false => simp only [cond_false, Set.mem_compl_iff] at hxb; simp [if_neg hxb]
  rw [hdec]
  unfold chosenBool
  simp only [hq, if_true]

include hA in
/-- Each `refineBySet` fiber has positive measure (it contains its positive raw atom). -/
private theorem pos_blockFn_preimage (q : P.refineIdx (A := A)) :
    0 < μ (P.blockFn (A := A) hA ⁻¹' {q}) :=
  lt_of_lt_of_le q.2 (measure_mono (P.rawPart_subset_blockFn_preimage hA q))

/-- **Refinement of `P` by a measurable set `A`.**  Splits each block of `P` into its `A`- and
    `Aᶜ`-parts, dropping null atoms and redirecting their points to a positive sibling. -/
noncomputable def refineBySet : MeasPartition Ω μ where
  ι := P.refineIdx (A := A)
  part := fun q => P.blockFn (A := A) hA ⁻¹' {q}
  measurable_part := fun q => P.measurableSet_blockFn_preimage hA q
  pos := fun q => P.pos_blockFn_preimage hA q
  block := P.blockFn (A := A) hA
  measurable_block := by
    classical
    exact measurable_to_countable' (fun q => P.measurableSet_blockFn_preimage hA q)
  block_preimage := fun _ => rfl
  mem_block := fun _ => rfl

/-- `refineBySet P A` refines `P` (forget the `A`-side bool). -/
theorem isRefinement_refineBySet : IsRefinement (P.refineBySet (A := A) hA) P :=
  ⟨fun q => q.1.1, fun _ => rfl⟩

/-- The refinement-by-a-set at most **doubles** the part count: the index type is a subtype of
    `P.ι × Bool`, which has `2 · card P.ι` elements. -/
theorem card_refineBySet_le :
    Fintype.card (P.refineBySet (A := A) hA).ι ≤ 2 * Fintype.card P.ι := by
  show Fintype.card (P.refineIdx (A := A)) ≤ 2 * Fintype.card P.ι
  calc Fintype.card (P.refineIdx (A := A))
      ≤ Fintype.card (P.ι × Bool) := Fintype.card_subtype_le _
    _ = Fintype.card P.ι * 2 := by rw [Fintype.card_prod, Fintype.card_bool]
    _ = 2 * Fintype.card P.ι := by ring

/-- The S-side bool of the refined block equals `x ∈ A`, whenever `x` lies in a positive-measure
    raw atom (i.e. no redirect happened). -/
private theorem refineBySet_block_bool (x : Ω)
    (hx : 0 < μ (P.rawPart (A := A) (P.block x, (if x ∈ A then true else false)))) :
    ((P.refineBySet (A := A) hA).block x).1.2 = (if x ∈ A then true else false) := by
  classical
  show (P.rawBlockFn (A := A) x).2 = _
  simp only [rawBlockFn, chosenBool]
  rw [if_pos hx]

/-- The "bad" set where a point lies in a *null* raw atom (where the refinement may redirect). -/
private def badSet : Set Ω :=
  ⋃ q ∈ {q : P.ι × Bool | μ (P.rawPart (A := A) q) = 0}, P.rawPart (A := A) q

include hA in
private theorem measurableSet_badSet : MeasurableSet (P.badSet (A := A)) := by
  classical
  refine MeasurableSet.biUnion (Set.to_countable _) (fun q _ => P.measurableSet_rawPart hA q)

include hA in
private theorem measure_badSet_zero : μ (P.badSet (A := A)) = 0 := by
  classical
  refine (measure_biUnion_null_iff (Set.to_countable _)).2 ?_
  intro q hq
  exact hq

include hA in
/-- Every point not in the bad set lies in its own positive raw atom. -/
private theorem rawPart_block_pos_of_notMem_badSet (x : Ω) (hx : x ∉ P.badSet (A := A)) :
    0 < μ (P.rawPart (A := A) (P.block x, (if x ∈ A then true else false))) := by
  classical
  rcases eq_or_ne (μ (P.rawPart (A := A) (P.block x, (if x ∈ A then true else false)))) 0
    with h0 | h0
  · exfalso
    apply hx
    simp only [badSet, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨(P.block x, (if x ∈ A then true else false)), h0, ?_⟩
    simp only [rawPart]
    refine ⟨P.mem_block x, ?_⟩
    by_cases hxA : x ∈ A <;> simp [hxA]
  · exact pos_iff_ne_zero.2 h0

include hA in
/-- The indicator of `A` is a.e. equal to the `A`-side bool of the refined block.  (They differ
    only on the null bad set.) -/
theorem indicator_refineBySet_ae :
    (Set.indicator A (1 : Ω → ℝ)) =ᵐ[μ]
      fun x => (if ((P.refineBySet (A := A) hA).block x).1.2 = true then (1 : ℝ) else 0) := by
  classical
  refine (ae_iff.2 ?_)
  refine measure_mono_null ?_ (P.measure_badSet_zero hA)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_contra hxbad
  apply hx
  have hpos := P.rawPart_block_pos_of_notMem_badSet hA x hxbad
  rw [P.refineBySet_block_bool hA x hpos]
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA, Pi.one_apply, if_pos hxA, if_pos rfl]
  · rw [Set.indicator_of_notMem hxA, if_neg hxA, if_neg (by simp)]

end RefineBySet

end MeasPartition

/-! ## Refinement: block decomposition and energy monotonicity -/

section Refines

variable {W : SymmKernel Ω μ} {P' P : MeasPartition Ω μ}

open scoped Classical in
/-- The **fiber** of the refinement map over a coarse index `i`: the fine indices `i'` with
    `f i' = i`. -/
private noncomputable def fiber (f : P'.ι → P.ι) (i : P.ι) : Finset P'.ι :=
  Finset.univ.filter (fun i' => f i' = i)

omit [IsProbabilityMeasure μ] in
/-- Each coarse part is the disjoint union of the fine parts over its fiber. -/
private theorem part_eq_biUnion {f : P'.ι → P.ι} (hf : ∀ x, P.block x = f (P'.block x))
    (i : P.ι) : P.part i = ⋃ i' ∈ fiber f i, P'.part i' := by
  classical
  ext x
  simp only [Set.mem_iUnion, fiber, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [P.mem_part_iff x i]
  constructor
  · intro hx
    exact ⟨P'.block x, by rw [← hf x, hx], (P'.mem_part_iff x (P'.block x)).2 rfl⟩
  · rintro ⟨i', hi', hx'⟩
    rw [hf x, (P'.mem_part_iff x i').1 hx', hi']

omit [IsProbabilityMeasure μ] in
/-- The fine parts over a fixed fiber are pairwise disjoint (distinct fibers of `block P'`). -/
private theorem part_pairwiseDisjoint (i : P.ι) (f : P'.ι → P.ι) :
    (fiber f i : Set P'.ι).PairwiseDisjoint P'.part := by
  intro a _ b _ hab
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact hab (by rw [← (P'.mem_part_iff x a).1 hxa, (P'.mem_part_iff x b).1 hxb])

/-- Coarse part measure = sum of fine part measures over the fiber. -/
private theorem measure_part_eq_sum {f : P'.ι → P.ι} (hf : ∀ x, P.block x = f (P'.block x))
    (i : P.ι) : μ (P.part i) = ∑ i' ∈ fiber f i, μ (P'.part i') := by
  classical
  rw [part_eq_biUnion hf i]
  rw [measure_biUnion_finset (part_pairwiseDisjoint i f) (fun i' _ => P'.measurable_part i')]

/-- Coarse block-integral numerator = sum of fine numerators over the product fiber. -/
private theorem setIntegral_part_prod_eq_sum {f : P'.ι → P.ι}
    (hf : ∀ x, P.block x = f (P'.block x)) (i j : P.ι) :
    (∫ p in (P.part i) ×ˢ (P.part j), W.toFun p.1 p.2 ∂(μ.prod μ))
      = ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j,
          ∫ p in (P'.part i') ×ˢ (P'.part j'), W.toFun p.1 p.2 ∂(μ.prod μ) := by
  classical
  have hint : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2) (μ.prod μ) := W.integrable_uncurry
  -- the coarse rectangle is the disjoint union over the product fiber of fine rectangles
  set Q : Finset (P'.ι × P'.ι) := (fiber f i) ×ˢ (fiber f j) with hQ
  set R : P'.ι × P'.ι → Set (Ω × Ω) := fun q => (P'.part q.1) ×ˢ (P'.part q.2) with hR
  have hcover : (P.part i) ×ˢ (P.part j) = ⋃ q ∈ Q, R q := by
    rw [part_eq_biUnion hf i, part_eq_biUnion hf j]
    ext p
    simp only [hQ, hR, Set.mem_iUnion, Set.mem_prod, Finset.mem_product, Finset.mem_coe,
      exists_prop]
    constructor
    · rintro ⟨⟨i', hi', hp1⟩, j', hj', hp2⟩; exact ⟨(i', j'), ⟨hi', hj'⟩, hp1, hp2⟩
    · rintro ⟨⟨i', j'⟩, ⟨hi', hj'⟩, hp1, hp2⟩; exact ⟨⟨i', hi', hp1⟩, j', hj', hp2⟩
  rw [hcover]
  have hmeas : ∀ q ∈ Q, MeasurableSet (R q) := fun q _ =>
    (P'.measurable_part q.1).prod (P'.measurable_part q.2)
  have hdisj : Set.Pairwise (↑Q) (Function.onFun Disjoint R) := by
    intro a _ b _ hab
    simp only [Function.onFun, hR, Set.disjoint_left]
    rintro p ⟨hpa1, hpa2⟩ ⟨hpb1, hpb2⟩
    apply hab
    have e1 : a.1 = b.1 := by
      rw [← (P'.mem_part_iff p.1 a.1).1 hpa1, (P'.mem_part_iff p.1 b.1).1 hpb1]
    have e2 : a.2 = b.2 := by
      rw [← (P'.mem_part_iff p.2 a.2).1 hpa2, (P'.mem_part_iff p.2 b.2).1 hpb2]
    exact Prod.ext e1 e2
  have hintOn : ∀ q ∈ Q, IntegrableOn (fun p : Ω × Ω => W.toFun p.1 p.2) (R q) (μ.prod μ) :=
    fun q _ => hint.integrableOn
  rw [integral_biUnion_finset Q hmeas hdisj hintOn, hQ, Finset.sum_product]

/-- Real measure of a coarse part = sum of real measures of the fine parts over its fiber. -/
private theorem measure_part_toReal_eq_sum {f : P'.ι → P.ι}
    (hf : ∀ x, P.block x = f (P'.block x)) (i : P.ι) :
    (μ (P.part i)).toReal = ∑ i' ∈ fiber f i, (μ (P'.part i')).toReal := by
  rw [measure_part_eq_sum hf i, ENNReal.toReal_sum]
  exact fun i' _ => P'.measure_part_ne_top i'

/-- `blockAvg` numerator identity: `blockAvg W P i j · (μPi·μPj) = ∫_{Pi×Pj} W`. -/
private theorem blockAvg_mul_measure (W : SymmKernel Ω μ) (P : MeasPartition Ω μ) (i j : P.ι) :
    blockAvg W P i j * ((μ (P.part i)).toReal * (μ (P.part j)).toReal)
      = ∫ p in (P.part i) ×ˢ (P.part j), W.toFun p.1 p.2 ∂(μ.prod μ) := by
  unfold blockAvg
  rw [div_mul_cancel₀]
  exact (mul_pos (P.toReal_measure_part_pos i) (P.toReal_measure_part_pos j)).ne'

/-- **Projection identity.**  The coarse `blockAvg` (times its block weight) equals the
    weighted sum of the fine `blockAvg`s over its product fiber.  (The coarse step kernel is the
    block-average of the fine step kernel; this is the discrete tower/projection property.) -/
theorem blockAvg_coarse_eq_sum {f : P'.ι → P.ι} (hf : ∀ x, P.block x = f (P'.block x))
    (i j : P.ι) :
    (μ (P.part i)).toReal * (μ (P.part j)).toReal * blockAvg W P i j
      = ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j,
          (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * blockAvg W P' i' j' := by
  classical
  rw [mul_comm _ (blockAvg W P i j), blockAvg_mul_measure W P i j,
    setIntegral_part_prod_eq_sum hf i j]
  refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => ?_))
  rw [show (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * blockAvg W P' i' j'
        = blockAvg W P' i' j' * ((μ (P'.part i')).toReal * (μ (P'.part j')).toReal) by ring,
    blockAvg_mul_measure W P' i' j']

/-- The step kernel `stepW W P` is constant `= blockAvg W P (f i') (f j')` on the fine block
    `part i' × part j'`, so its integral there is that value times the block measure. -/
theorem setIntegral_stepW_part_prod {f : P'.ι → P.ι} (hf : ∀ x, P.block x = f (P'.block x))
    (i' j' : P'.ι) :
    (∫ p in (P'.part i') ×ˢ (P'.part j'), (stepW W P).toFun p.1 p.2 ∂(μ.prod μ))
      = blockAvg W P (f i') (f j')
        * ((μ (P'.part i')).toReal * (μ (P'.part j')).toReal) := by
  classical
  have hcongr : (∫ p in (P'.part i') ×ˢ (P'.part j'), (stepW W P).toFun p.1 p.2 ∂(μ.prod μ))
      = ∫ _ in (P'.part i') ×ˢ (P'.part j'), blockAvg W P (f i') (f j') ∂(μ.prod μ) := by
    refine setIntegral_congr_fun ((P'.measurable_part i').prod (P'.measurable_part j')) ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have e1 : P.block p.1 = f i' := by rw [hf p.1, (P'.mem_part_iff p.1 i').1 hp1]
    have e2 : P.block p.2 = f j' := by rw [hf p.2, (P'.mem_part_iff p.2 j').1 hp2]
    simp only [stepW_apply, e1, e2]
  rw [hcongr, setIntegral_const, smul_eq_mul, measureReal_def, Measure.prod_prod,
    ENNReal.toReal_mul]
  ring

/-- The integral of `W − stepW W P` over a fine block equals the block weight times the
    fine-minus-coarse `blockAvg` gap. -/
theorem setIntegral_sub_stepW_part_prod {f : P'.ι → P.ι} (hf : ∀ x, P.block x = f (P'.block x))
    (i' j' : P'.ι) :
    (∫ p in (P'.part i') ×ˢ (P'.part j'), (W - stepW W P).toFun p.1 p.2 ∂(μ.prod μ))
      = (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
        * (blockAvg W P' i' j' - blockAvg W P (f i') (f j')) := by
  classical
  have hWint : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2)
      ((μ.prod μ).restrict ((P'.part i') ×ˢ (P'.part j'))) :=
    W.integrable_uncurry.restrict
  have hSint : Integrable (fun p : Ω × Ω => (stepW W P).toFun p.1 p.2)
      ((μ.prod μ).restrict ((P'.part i') ×ˢ (P'.part j'))) :=
    (stepW W P).integrable_uncurry.restrict
  have hsub : ∀ p : Ω × Ω, (W - stepW W P).toFun p.1 p.2
      = W.toFun p.1 p.2 - (stepW W P).toFun p.1 p.2 := fun p => rfl
  simp only [hsub]
  rw [integral_sub hWint hSint, setIntegral_stepW_part_prod hf i' j',
    ← blockAvg_mul_measure W P' i' j']
  ring

omit [IsProbabilityMeasure μ] in
/-- A finite Cauchy–Schwarz lower bound: if `∑ c²·w ≤ 1` and `0 ≤ w`, then
    `(∑ c·w·v)² ≤ ∑ w·v²`.  (Used with `c` a `{0,1}` block selector, `w` block weights, `v` the
    fine-minus-coarse `blockAvg` gap.) -/
theorem cs_lower_bound {κ : Type*} (s : Finset κ) (c w v : κ → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hc : (∑ k ∈ s, c k ^ 2 * w k) ≤ 1) :
    (∑ k ∈ s, c k * w k * v k) ^ 2 ≤ ∑ k ∈ s, w k * v k ^ 2 := by
  classical
  -- Cauchy–Schwarz with f = c·√w, g = √w·v
  have hCS : (∑ k ∈ s, (c k * Real.sqrt (w k)) * (Real.sqrt (w k) * v k)) ^ 2
      ≤ (∑ k ∈ s, (c k * Real.sqrt (w k)) ^ 2) * ∑ k ∈ s, (Real.sqrt (w k) * v k) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  have hsqrt : ∀ k ∈ s, Real.sqrt (w k) * Real.sqrt (w k) = w k := fun k hk =>
    Real.mul_self_sqrt (hw k hk)
  -- rewrite the three sums into the c·w·v / c²·w / w·v² forms
  have e1 : (∑ k ∈ s, (c k * Real.sqrt (w k)) * (Real.sqrt (w k) * v k))
      = ∑ k ∈ s, c k * w k * v k := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have : (c k * Real.sqrt (w k)) * (Real.sqrt (w k) * v k)
          = c k * (Real.sqrt (w k) * Real.sqrt (w k)) * v k := by ring
    rw [this, hsqrt k hk]
  have e2 : (∑ k ∈ s, (c k * Real.sqrt (w k)) ^ 2) = ∑ k ∈ s, c k ^ 2 * w k := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mul_pow, Real.sq_sqrt (hw k hk)]
  have e3 : (∑ k ∈ s, (Real.sqrt (w k) * v k) ^ 2) = ∑ k ∈ s, w k * v k ^ 2 := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mul_pow, Real.sq_sqrt (hw k hk)]
  rw [e1, e2, e3] at hCS
  have hv2 : (0 : ℝ) ≤ ∑ k ∈ s, w k * v k ^ 2 :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (sq_nonneg _))
  calc (∑ k ∈ s, c k * w k * v k) ^ 2
      ≤ (∑ k ∈ s, c k ^ 2 * w k) * ∑ k ∈ s, w k * v k ^ 2 := hCS
    _ ≤ 1 * ∑ k ∈ s, w k * v k ^ 2 := by
        exact mul_le_mul_of_nonneg_right hc hv2
    _ = ∑ k ∈ s, w k * v k ^ 2 := one_mul _

/-- **Per-block Cauchy–Schwarz.**  Over the product fiber of `(i,j)`, the coarse energy term
    `μPi·μPj·blockAvg²` is dominated by the sum of the fine energy terms. -/
private theorem energy_block_le {f : P'.ι → P.ι} (hf : ∀ x, P.block x = f (P'.block x))
    (i j : P.ι) :
    (μ (P.part i)).toReal * (μ (P.part j)).toReal * (blockAvg W P i j) ^ 2
      ≤ ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j,
          (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * (blockAvg W P' i' j') ^ 2 := by
  classical
  set Q : Finset (P'.ι × P'.ι) := (fiber f i) ×ˢ (fiber f j) with hQ
  -- weight and value over the product fiber
  set a : P'.ι × P'.ι → ℝ := fun q => (μ (P'.part q.1)).toReal * (μ (P'.part q.2)).toReal with ha
  set x : P'.ι × P'.ι → ℝ := fun q => blockAvg W P' q.1 q.2 with hx
  have ha_nonneg : ∀ q ∈ Q, 0 ≤ a q := fun q _ =>
    mul_nonneg (P'.toReal_measure_part_pos q.1).le (P'.toReal_measure_part_pos q.2).le
  -- denominator
  set D : ℝ := (μ (P.part i)).toReal * (μ (P.part j)).toReal with hD
  have hDpos : 0 < D := mul_pos (P.toReal_measure_part_pos i) (P.toReal_measure_part_pos j)
  -- ∑_Q a = D
  have hsumA : ∑ q ∈ Q, a q = D := by
    rw [hQ, Finset.sum_product, hD, measure_part_toReal_eq_sum hf i,
      measure_part_toReal_eq_sum hf j, Finset.sum_mul_sum]
  -- ∑_Q a·x = D · blockAvg W P i j   (numerator decomposition)
  have hsumAX : ∑ q ∈ Q, a q * x q = D * blockAvg W P i j := by
    rw [hD, mul_comm _ (blockAvg W P i j), blockAvg_mul_measure W P i j,
      setIntegral_part_prod_eq_sum hf i j, hQ, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [ha, hx]
    rw [show (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * blockAvg W P' i' j'
          = blockAvg W P' i' j' * ((μ (P'.part i')).toReal * (μ (P'.part j')).toReal) by ring,
      blockAvg_mul_measure W P' i' j']
  -- Cauchy–Schwarz: (∑ a x)² ≤ (∑ a)(∑ a x²)
  have hCS : (∑ q ∈ Q, a q * x q) ^ 2 ≤ (∑ q ∈ Q, a q) * ∑ q ∈ Q, a q * x q ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Q ha_nonneg
      (fun q hq => mul_nonneg (ha_nonneg q hq) (sq_nonneg _)) (fun q _ => le_of_eq (by ring))
  -- finish: D · blockAvg² ≤ ∑ a x²  (divide CS by D), then unfold RHS
  rw [hsumA, hsumAX] at hCS
  have hkey : D * (blockAvg W P i j) ^ 2 ≤ ∑ q ∈ Q, a q * x q ^ 2 := by
    have : (D * blockAvg W P i j) ^ 2 = D * (D * (blockAvg W P i j) ^ 2) := by ring
    rw [this] at hCS
    exact le_of_mul_le_mul_left hCS hDpos
  calc (μ (P.part i)).toReal * (μ (P.part j)).toReal * (blockAvg W P i j) ^ 2
      = D * (blockAvg W P i j) ^ 2 := by rw [hD]
    _ ≤ ∑ q ∈ Q, a q * x q ^ 2 := hkey
    _ = ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j,
          (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * (blockAvg W P' i' j') ^ 2 := by
        rw [hQ, Finset.sum_product]

omit [IsProbabilityMeasure μ] in
/-- Regrouping a double fiber sum back to a sum over the fine indices.  Since the fibers of `f`
    partition `P'.ι`, summing `g` over `(i,j)` and then over the fibers of `(i,j)` recovers the
    full double sum over `P'.ι × P'.ι`. -/
private theorem sum_sum_fiber_eq {f : P'.ι → P.ι} (_hf : ∀ x, P.block x = f (P'.block x))
    (g : P'.ι → P'.ι → ℝ) :
    (∑ i, ∑ j, ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j, g i' j')
      = ∑ i', ∑ j', g i' j' := by
  classical
  -- collapse the i/i' fibers first by pulling the inner three sums together
  have step1 : ∀ i : P.ι,
      (∑ j, ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j, g i' j')
        = ∑ i' ∈ fiber f i, ∑ j', g i' j' := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    exact Finset.sum_fiberwise Finset.univ f (fun j' => g i' j')
  rw [Finset.sum_congr rfl (fun i _ => step1 i)]
  exact Finset.sum_fiberwise Finset.univ f (fun i' => ∑ j', g i' j')

omit [IsProbabilityMeasure μ] in
/-- Membership in a fiber means the refinement map sends the index there. -/
private theorem fiber_apply {f : P'.ι → P.ι} {i : P.ι} {i' : P'.ι} (h : i' ∈ fiber f i) :
    f i' = i := by
  simpa only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- **Pythagoras (finite form).**  For `P'` refining `P`, the energy increment equals the squared
    `L²`-distance between the fine and coarse step kernels, written as the weighted sum over fine
    blocks of `(blockAvg W P' i' j' − blockAvg W P (f i') (f j'))²`. -/
theorem energy_sub_eq_normSq {f : P'.ι → P.ι} (hf : ∀ x, P.block x = f (P'.block x)) :
    energy W P' - energy W P
      = ∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
          * (blockAvg W P' i' j' - blockAvg W P (f i') (f j')) ^ 2 := by
  classical
  set c : P'.ι → P'.ι → ℝ := fun i' j' => blockAvg W P (f i') (f j') with hc
  -- Claim B: ∑ μi'μj' c² = energy P
  have hB : (∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * c i' j' ^ 2)
      = energy W P := by
    rw [energy_eq_sum, ← sum_sum_fiber_eq hf (fun i' j' =>
      (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * c i' j' ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    -- inner: ∑_{fib i}∑_{fib j} μi'μj' (bA i j)² = μiμj (bA i j)²
    have hcij : ∀ i' ∈ fiber f i, ∀ j' ∈ fiber f j, c i' j' = blockAvg W P i j := by
      intro i' hi' j' hj'; rw [hc]; simp only; rw [fiber_apply hi', fiber_apply hj']
    rw [Finset.sum_congr rfl (fun i' hi' => Finset.sum_congr rfl (fun j' hj' => by
      rw [hcij i' hi' j' hj']))]
    -- now ∑∑ μi'μj' (bA i j)² = (∑ μi')(∑ μj') (bA i j)² = μiμj (bA ij)²
    have hmm : (μ (P.part i)).toReal * (μ (P.part j)).toReal
        = ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j, (μ (P'.part i')).toReal * (μ (P'.part j')).toReal := by
      rw [measure_part_toReal_eq_sum hf i, measure_part_toReal_eq_sum hf j, Finset.sum_mul_sum]
    rw [hmm, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [Finset.sum_mul]
  -- Claim A: ∑ μi'μj' bA' c = energy P
  have hA : (∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
        * (blockAvg W P' i' j' * c i' j'))
      = energy W P := by
    rw [energy_eq_sum, ← sum_sum_fiber_eq hf (fun i' j' =>
      (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * (blockAvg W P' i' j' * c i' j'))]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    -- inner: ∑∑ μi'μj' bA'(i'j') (bA ij) = (bA ij) ∑∑ μi'μj' bA'(i'j') = (bA ij)(μiμj bA ij)
    have hcij : ∀ i' ∈ fiber f i, ∀ j' ∈ fiber f j,
        (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * (blockAvg W P' i' j' * c i' j')
          = blockAvg W P i j
            * ((μ (P'.part i')).toReal * (μ (P'.part j')).toReal * blockAvg W P' i' j') := by
      intro i' hi' j' hj'; rw [hc]; simp only; rw [fiber_apply hi', fiber_apply hj']; ring
    rw [Finset.sum_congr rfl (fun i' hi' => Finset.sum_congr rfl (fun j' hj' =>
      hcij i' hi' j' hj'))]
    -- LHS = (bA ij) · ∑∑ μi'μj' bA' = (bA ij)·(μiμj·bA ij) = μiμj (bA ij)²
    rw [Finset.sum_congr rfl (fun i' (_ : i' ∈ fiber f i) => (Finset.mul_sum _ _ _).symm),
      ← Finset.mul_sum, ← blockAvg_coarse_eq_sum hf i j]
    ring
  -- assemble: RHS = ∑ μi'μj'(bA'² - 2 bA' c + c²) = energy P' - 2·energyP + energyP
  have hexpand : (∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
        * (blockAvg W P' i' j' - c i' j') ^ 2)
      = (∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
          * (blockAvg W P' i' j') ^ 2)
        - 2 * (∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
          * (blockAvg W P' i' j' * c i' j'))
        + (∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal * c i' j' ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    ring
  show energy W P' - energy W P
      = ∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
          * (blockAvg W P' i' j' - c i' j') ^ 2
  rw [hexpand, ← energy_eq_sum, hA, hB]
  ring

end Refines

/-! ## The hard analytic cores (Phase 2/3 targets)

The two lemmas below are the genuine analytic content of the energy-increment proof of weak
regularity (Lovász §9.2).  They are stated precisely and left as labelled `sorry`s; everything above
and the assembly theorem below are built on top of them.  Both rest on viewing `stepW W P` as the
`L²`-conditional expectation of `W` onto the block σ-algebra `𝒢_P` of `P`, so that:

* `stepW` is the orthogonal `L²`-projection of `W` onto `𝒢_P`-measurable kernels, and
* refinement enlarges `𝒢_P`, hence the projection grows in `L²`-norm (Pythagoras). -/

/-- **HARD CORE 1 — energy monotonicity under refinement.**
    Refining a partition cannot decrease the energy.  PHASE-2 PROOF: `stepW W P` and `stepW W P'`
    are the `L²`-projections of `W` onto the (nested) block σ-algebras `𝒢_P ⊆ 𝒢_{P'}`; the
    projection onto the larger subspace has `≥ L²`-norm (Pythagoras / tower property of conditional
    expectation, `MeasureTheory.condExp`).  Needs: `stepW = 𝔼[W | 𝒢_P]`, then
    `‖𝔼[W|𝒢_P]‖₂ ≤ ‖𝔼[W|𝒢_{P'}]‖₂` for `𝒢_P ⊆ 𝒢_{P'}`. -/
theorem energy_le_of_refines (W : Graphon Ω μ) {P' P : MeasPartition Ω μ}
    (h : IsRefinement P' P) : energy W.toSymmKernel P ≤ energy W.toSymmKernel P' := by
  classical
  obtain ⟨f, hf⟩ := h
  rw [energy_eq_sum, energy_eq_sum]
  -- group the fine sum by fibers, then dominate each coarse block by its fiber
  calc ∑ i, ∑ j, (μ (P.part i)).toReal * (μ (P.part j)).toReal
            * (blockAvg W.toSymmKernel P i j) ^ 2
      ≤ ∑ i, ∑ j, ∑ i' ∈ fiber f i, ∑ j' ∈ fiber f j,
          (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
            * (blockAvg W.toSymmKernel P' i' j') ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
          (fun j _ => energy_block_le hf i j))
    _ = ∑ i', ∑ j', (μ (P'.part i')).toReal * (μ (P'.part j')).toReal
            * (blockAvg W.toSymmKernel P' i' j') ^ 2 :=
        sum_sum_fiber_eq hf _

omit [IsProbabilityMeasure μ] in
/-- From `ε < cutNormSet W` (with `0 ≤ ε`), extract a measurable rectangle witness `S × T` with
    `ε < |∫_{S×T} W|`.  (Peeling the four-fold `⨆` defining `cutNormSet`.) -/
theorem exists_cutNormSet_witness (W : SymmKernel Ω μ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ε < cutNormSet W) :
    ∃ S T : Set Ω, MeasurableSet S ∧ MeasurableSet T ∧
      ε < |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
            * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)| := by
  rw [cutNormSet] at h
  obtain ⟨S, hS⟩ : ∃ S : Set Ω, ε < ⨆ (T : Set Ω) (_ : MeasurableSet S) (_ : MeasurableSet T),
      |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
        * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)| := exists_lt_of_lt_ciSup h
  obtain ⟨T, hT⟩ : ∃ T : Set Ω, ε < ⨆ (_ : MeasurableSet S) (_ : MeasurableSet T),
      |∫ p, W.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
        * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ)| := exists_lt_of_lt_ciSup hS
  by_cases hSm : MeasurableSet S
  · by_cases hTm : MeasurableSet T
    · rw [ciSup_pos hSm, ciSup_pos hTm] at hT
      exact ⟨S, T, hSm, hTm, hT⟩
    · rw [ciSup_pos hSm, ciSup_neg hTm, Real.sSup_empty] at hT
      exact absurd hT (not_lt.2 hε)
  · rw [ciSup_neg hSm, Real.sSup_empty] at hT
    exact absurd hT (not_lt.2 hε)

/-- **HARD CORE 2 — energy-increment lemma.**
    If the step kernel is `ε`-far from `W` in cut norm, there is a refinement of `P` whose energy
    exceeds that of `P` by at least `ε²`.  PHASE-3 PROOF: take the cut-norm witness sets `S, T`
    (from `cutNormSet`, since `cutNorm = cutNormSet`) realizing `|∫_{S×T}(W − stepW W P)| > ε`;
    refine `P` by intersecting its blocks with `S, T` (the new partition `P'`).  Then
    `W − stepW W P` is `𝒢_{P'}`-orthogonal to `stepW W P − stepW W P'`-free directions and the
    inner product `⟨W − stepW W P, 𝟙_S ⊗ 𝟙_T⟩ = ∫_{S×T}(W − stepW W P)` lower-bounds the projection
    increment, giving `energy W P' − energy W P ≥ (∫_{S×T}(W−stepW W P))² ≥ ε²` via Pythagoras
    (`‖𝔼[W|𝒢_{P'}]‖₂² − ‖𝔼[W|𝒢_P]‖₂² = ‖𝔼[W|𝒢_{P'}] − 𝔼[W|𝒢_P]‖₂² ≥ ⟨…⟩²`).
    Needs: the `condExp` projection picture + Cauchy–Schwarz lower bound from the cut witness. -/
theorem exists_refinement_energy_increment (W : Graphon Ω μ) (P : MeasPartition Ω μ) {ε : ℝ}
    (hε : 0 < ε) (hcut : ε < cutNorm (W.toSymmKernel - stepW W.toSymmKernel P)) :
    ∃ P' : MeasPartition Ω μ, IsRefinement P' P ∧
      Fintype.card P'.ι ≤ 4 * Fintype.card P.ι ∧
      energy W.toSymmKernel P + ε ^ 2 ≤ energy W.toSymmKernel P' := by
  classical
  set V : SymmKernel Ω μ := W.toSymmKernel - stepW W.toSymmKernel P with hV
  -- 1. cut-norm witness S, T with |∫_{S×T} V| > ε
  rw [cutNorm_eq_cutNormSet] at hcut
  obtain ⟨S, T, hS, hT, hST⟩ := exists_cutNormSet_witness V hε.le hcut
  -- the witness integral, rewritten as a set-integral of V over S ×ˢ T
  set D : ℝ := ∫ p, V.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
      * (Set.indicator T (1 : Ω → ℝ) p.2) ∂(μ.prod μ) with hD
  have hDε : ε < |D| := hST
  -- 2. the refinement P' := refine P by S, then by T
  set P' : MeasPartition Ω μ := (P.refineBySet hS).refineBySet hT with hP'
  have href : IsRefinement P' P :=
    (MeasPartition.isRefinement_refineBySet _ hT).trans (MeasPartition.isRefinement_refineBySet P hS)
  -- card bound: each `refineBySet` at most doubles the part count.
  have hcard : Fintype.card P'.ι ≤ 4 * Fintype.card P.ι := by
    calc Fintype.card P'.ι
        ≤ 2 * Fintype.card (P.refineBySet hS).ι :=
          MeasPartition.card_refineBySet_le (P.refineBySet hS) hT
      _ ≤ 2 * (2 * Fintype.card P.ι) := by
          exact Nat.mul_le_mul_left 2 (MeasPartition.card_refineBySet_le P hS)
      _ = 4 * Fintype.card P.ι := by ring
  refine ⟨P', href, hcard, ?_⟩
  obtain ⟨f, hf⟩ := href
  -- 3. Pythagoras: energy P' - energy P = ∑∑ μμ (bA' - c)²
  have hpyth := energy_sub_eq_normSq (W := W.toSymmKernel) hf
  -- 4. CS lower bound: ∑∑ μμ (bA' - c)² ≥ D²   (and |D| > ε ⟹ ≥ ε²)
  have hCSbound : D ^ 2 ≤ energy W.toSymmKernel P' - energy W.toSymmKernel P := by
    classical
    set PS : MeasPartition Ω μ := P.refineBySet hS with hPS
    -- the {0,1} block selectors for S and T
    set gfun : P'.ι → ℝ := fun q' => if q'.1.1.1.2 = true then (1:ℝ) else 0 with hgfun
    set hfun : P'.ι → ℝ := fun q' => if q'.1.2 = true then (1:ℝ) else 0 with hhfun
    -- a.e. block-constancy of the indicators (μ-ae)
    have hae_T : (Set.indicator T (1 : Ω → ℝ)) =ᵐ[μ] fun x => hfun (P'.block x) :=
      MeasPartition.indicator_refineBySet_ae PS hT
    have hae_S : (Set.indicator S (1 : Ω → ℝ)) =ᵐ[μ] fun x => gfun (P'.block x) := by
      have h0 := MeasPartition.indicator_refineBySet_ae P hS
      refine h0.trans (Filter.Eventually.of_forall (fun x => ?_))
      -- (PS.block x).1.2 = (P'.block x).1.1.1.2  via PS.block = (P'.block).1.1
      rfl
    -- lift to μ⊗μ-ae and combine: the integrand equals V·(gfun⊗hfun)∘block
    have haeST : (fun p : Ω × Ω => V.toFun p.1 p.2 * (Set.indicator S (1 : Ω → ℝ) p.1)
          * (Set.indicator T (1 : Ω → ℝ) p.2))
        =ᵐ[μ.prod μ] fun p => V.toFun p.1 p.2 * (gfun (P'.block p.1) * hfun (P'.block p.2)) := by
      have hS2 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp hae_S
      have hT2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp hae_T
      filter_upwards [hS2, hT2] with p hp1 hp2
      simp only [Function.comp_apply] at hp1 hp2
      rw [hp1, hp2]; ring
    -- D as a finite block sum
    have hDsum : D = ∑ i', ∑ j', (gfun i' * hfun j')
        * ((μ (P'.part i')).toReal * (μ (P'.part j')).toReal
          * (blockAvg W.toSymmKernel P' i' j' - blockAvg W.toSymmKernel P (f i') (f j'))) := by
      rw [hD, integral_congr_ae haeST,
        integral_mul_block_const V P' (fun i' j' => gfun i' * hfun j')]
      refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => ?_))
      rw [hV, setIntegral_sub_stepW_part_prod hf i' j']
    -- collapse the double sums to single sums over P'.ι × P'.ι
    set w : P'.ι × P'.ι → ℝ := fun q => (μ (P'.part q.1)).toReal * (μ (P'.part q.2)).toReal with hw
    set v : P'.ι × P'.ι → ℝ :=
      fun q => blockAvg W.toSymmKernel P' q.1 q.2 - blockAvg W.toSymmKernel P (f q.1) (f q.2) with hv
    set cf : P'.ι × P'.ι → ℝ := fun q => gfun q.1 * hfun q.2 with hcf
    have hDq : D = ∑ q : P'.ι × P'.ι, cf q * w q * v q := by
      rw [hDsum, ← Finset.univ_product_univ, Finset.sum_product]
      refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => ?_))
      rw [hcf, hw, hv]; ring
    have hpyth' : energy W.toSymmKernel P' - energy W.toSymmKernel P
        = ∑ q : P'.ι × P'.ι, w q * v q ^ 2 := by
      rw [hpyth, ← Finset.univ_product_univ, Finset.sum_product]
    rw [hpyth', hDq]
    -- weights nonneg, and ∑ cf² w ≤ 1
    have hwnn : ∀ q ∈ Finset.univ, 0 ≤ w q := fun q _ =>
      mul_nonneg (P'.toReal_measure_part_pos q.1).le (P'.toReal_measure_part_pos q.2).le
    have hcf_le : (∑ q : P'.ι × P'.ι, cf q ^ 2 * w q) ≤ 1 := by
      have hbound : ∀ b : Bool, (if b = true then (1:ℝ) else 0) ^ 2 ≤ 1 := by
        intro b; cases b <;> norm_num
      calc (∑ q : P'.ι × P'.ι, cf q ^ 2 * w q)
          = (∑ i', gfun i' ^ 2 * (μ (P'.part i')).toReal)
              * (∑ j', hfun j' ^ 2 * (μ (P'.part j')).toReal) := by
            rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
            refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => ?_))
            rw [hcf, hw]; ring
        _ ≤ 1 * 1 := by
            refine mul_le_mul ?_ ?_ ?_ (by norm_num)
            · calc (∑ i', gfun i' ^ 2 * (μ (P'.part i')).toReal)
                  ≤ ∑ i', 1 * (μ (P'.part i')).toReal := by
                    refine Finset.sum_le_sum (fun i' _ => ?_)
                    exact mul_le_mul_of_nonneg_right (hbound _) (P'.toReal_measure_part_pos i').le
                _ = 1 := by simp only [one_mul]; exact P'.sum_toReal_measure_part_eq_one
            · calc (∑ j', hfun j' ^ 2 * (μ (P'.part j')).toReal)
                  ≤ ∑ j', 1 * (μ (P'.part j')).toReal := by
                    refine Finset.sum_le_sum (fun j' _ => ?_)
                    exact mul_le_mul_of_nonneg_right (hbound _) (P'.toReal_measure_part_pos j').le
                _ = 1 := by simp only [one_mul]; exact P'.sum_toReal_measure_part_eq_one
            · exact Finset.sum_nonneg (fun i' _ =>
                mul_nonneg (sq_nonneg _) (P'.toReal_measure_part_pos i').le)
        _ = 1 := by norm_num
    exact cs_lower_bound Finset.univ cf w v hwnn hcf_le
  -- 5. conclude
  have hε2 : ε ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs D]; exact pow_le_pow_left₀ hε.le hDε.le 2
  linarith

/-! ## The trivial (one-block) partition -/

/-- The **trivial partition** with a single block `univ`.  Index type `Unit`; positive measure
    because `μ` is a probability measure. -/
noncomputable def trivialPartition : MeasPartition Ω μ where
  ι := Unit
  part := fun _ => Set.univ
  measurable_part := fun _ => MeasurableSet.univ
  pos := fun _ => by rw [measure_univ]; exact one_pos
  block := fun _ => ()
  measurable_block := measurable_const
  block_preimage := fun _ => by ext x; simp
  mem_block := fun _ => Set.mem_univ _

/-! ## Assembly: weak regularity by the energy-increment iteration

`energy ∈ [0,1]` and each bad refinement step adds `≥ ε²`, so the iteration terminates: at most
`⌈1/ε²⌉` refinements suffice.  The descent is packaged in `weak_regularity_aux` (induction on a
budget `n` bounding the remaining energy deficit), then specialized at the trivial partition. -/

/-- Energy-increment descent.  If the energy deficit `1 − energy W P` fits in `n` increments of
    `ε²`, then some refinement of `P` is `ε`-close to `W` in cut norm.  Pure induction on `n` on top
    of the two hard cores (only `exists_refinement_energy_increment` and `energy_le_one` are used). -/
theorem weak_regularity_aux (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ (n : ℕ) (P : MeasPartition Ω μ), 1 - energy W.toSymmKernel P ≤ (n : ℝ) * ε ^ 2 →
      ∃ P' : MeasPartition Ω μ, IsRefinement P' P ∧
        cutNorm (W.toSymmKernel - stepW W.toSymmKernel P') ≤ ε := by
  intro n
  induction n with
  | zero =>
    intro P hP
    -- deficit ≤ 0 ⇒ energy = 1; a further increment would exceed 1, so `P` is already good.
    by_cases hgood : cutNorm (W.toSymmKernel - stepW W.toSymmKernel P) ≤ ε
    · exact ⟨P, IsRefinement.rfl P, hgood⟩
    · exfalso
      simp only [not_le] at hgood
      obtain ⟨P', _, _, hinc⟩ := exists_refinement_energy_increment W P hε hgood
      have h1 : energy W.toSymmKernel P' ≤ 1 := energy_le_one W P'
      have hsq : (0 : ℝ) < ε ^ 2 := by positivity
      simp only [Nat.cast_zero, zero_mul] at hP
      -- energy P ≥ 1, so energy P' ≥ 1 + ε² > 1, contradiction
      linarith
  | succ n ih =>
    intro P hP
    by_cases hgood : cutNorm (W.toSymmKernel - stepW W.toSymmKernel P) ≤ ε
    · exact ⟨P, IsRefinement.rfl P, hgood⟩
    · simp only [not_le] at hgood
      obtain ⟨P', href, _, hinc⟩ := exists_refinement_energy_increment W P hε hgood
      -- deficit shrinks by ε²: 1 - energy P' ≤ n ε²
      have hP' : 1 - energy W.toSymmKernel P' ≤ (n : ℝ) * ε ^ 2 := by
        push_cast at hP ⊢
        nlinarith [hinc]
      obtain ⟨P'', href', hgood'⟩ := ih P' hP'
      exact ⟨P'', href'.trans href, hgood'⟩

/-- **Weak regularity lemma (cut-norm form).**  For every graphon `W` and every `ε > 0` there is a
    finite measurable partition `P` of `Ω` such that the block-averaged step kernel is within `ε`
    of `W` in cut norm:  `cutNorm (W − stepW W P) ≤ ε`.

    Proof: the energy-increment iteration (`weak_regularity_aux`) starting from the trivial
    partition; `⌈1/ε²⌉` increments of `ε²` cover the energy deficit `≤ 1`. -/
theorem weak_regularity (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MeasPartition Ω μ,
      cutNorm (W.toSymmKernel - stepW W.toSymmKernel P) ≤ ε := by
  set n : ℕ := ⌈1 / ε ^ 2⌉₊ with hn
  have hsq : (0 : ℝ) < ε ^ 2 := by positivity
  -- 1 ≤ n * ε² since n ≥ 1/ε²
  have hcover : 1 - energy W.toSymmKernel trivialPartition ≤ (n : ℝ) * ε ^ 2 := by
    have h0 : 0 ≤ energy W.toSymmKernel trivialPartition := energy_nonneg _ _
    have hge : (1 : ℝ) / ε ^ 2 ≤ (n : ℝ) := Nat.le_ceil _
    have : (1 : ℝ) ≤ (n : ℝ) * ε ^ 2 := by
      rw [div_le_iff₀ hsq] at hge
      linarith
    linarith
  obtain ⟨P, _, hgood⟩ := weak_regularity_aux W hε n trivialPartition hcover
  exact ⟨P, hgood⟩

/-! ## Weak regularity with an explicit part-count bound

The energy-increment iteration runs `⌈1/ε²⌉` times and each increment multiplies the part count by
`≤ 4` (two `refineBySet` splits), so starting from the one-block `trivialPartition` (card `1`) the
final partition has `card ι ≤ 4 ^ ⌈1/ε²⌉`.  We track this bound through a card-aware variant of the
descent. -/

/-- Energy-increment descent **with a part-count bound**: starting from `P`, after `n` budgeted
    increments the resulting refinement has `card ι ≤ 4 ^ n · card P.ι`.  Same induction as
    `weak_regularity_aux`, additionally carrying the multiplicative card bound through each step. -/
theorem weak_regularity_card_aux (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ (n : ℕ) (P : MeasPartition Ω μ), 1 - energy W.toSymmKernel P ≤ (n : ℝ) * ε ^ 2 →
      ∃ P' : MeasPartition Ω μ, IsRefinement P' P ∧
        Fintype.card P'.ι ≤ 4 ^ n * Fintype.card P.ι ∧
        cutNorm (W.toSymmKernel - stepW W.toSymmKernel P') ≤ ε := by
  intro n
  induction n with
  | zero =>
    intro P hP
    by_cases hgood : cutNorm (W.toSymmKernel - stepW W.toSymmKernel P) ≤ ε
    · exact ⟨P, IsRefinement.rfl P, by simp, hgood⟩
    · exfalso
      simp only [not_le] at hgood
      obtain ⟨P', _, _, hinc⟩ := exists_refinement_energy_increment W P hε hgood
      have h1 : energy W.toSymmKernel P' ≤ 1 := energy_le_one W P'
      have hsq : (0 : ℝ) < ε ^ 2 := by positivity
      simp only [Nat.cast_zero, zero_mul] at hP
      linarith
  | succ n ih =>
    intro P hP
    by_cases hgood : cutNorm (W.toSymmKernel - stepW W.toSymmKernel P) ≤ ε
    · refine ⟨P, IsRefinement.rfl P, ?_, hgood⟩
      calc Fintype.card P.ι = 1 * Fintype.card P.ι := (one_mul _).symm
        _ ≤ 4 ^ (n + 1) * Fintype.card P.ι :=
            Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by norm_num))
    · simp only [not_le] at hgood
      obtain ⟨P', href, hcardstep, hinc⟩ := exists_refinement_energy_increment W P hε hgood
      have hP' : 1 - energy W.toSymmKernel P' ≤ (n : ℝ) * ε ^ 2 := by
        push_cast at hP ⊢
        nlinarith [hinc]
      obtain ⟨P'', href', hcard'', hgood'⟩ := ih P' hP'
      refine ⟨P'', href'.trans href, ?_, hgood'⟩
      -- card P'' ≤ 4^n · card P' ≤ 4^n · (4 · card P) = 4^(n+1) · card P
      calc Fintype.card P''.ι
          ≤ 4 ^ n * Fintype.card P'.ι := hcard''
        _ ≤ 4 ^ n * (4 * Fintype.card P.ι) := Nat.mul_le_mul_left _ hcardstep
        _ = 4 ^ (n + 1) * Fintype.card P.ι := by ring

/-- **Weak regularity with an explicit part-count bound.**  For every graphon `W` and `ε > 0` there
    is a finite measurable partition `P` with `cutNorm (W − stepW W P) ≤ ε` **and** at most
    `4 ^ ⌈1/ε²⌉` parts.  This makes the family of step graphons relevant to total boundedness range
    over partitions of bounded complexity. -/
theorem weak_regularity_card (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MeasPartition Ω μ, Fintype.card P.ι ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧
      cutNorm (W.toSymmKernel - stepW W.toSymmKernel P) ≤ ε := by
  set n : ℕ := ⌈1 / ε ^ 2⌉₊ with hn
  have hsq : (0 : ℝ) < ε ^ 2 := by positivity
  have hcover : 1 - energy W.toSymmKernel trivialPartition ≤ (n : ℝ) * ε ^ 2 := by
    have h0 : 0 ≤ energy W.toSymmKernel trivialPartition := energy_nonneg _ _
    have hge : (1 : ℝ) / ε ^ 2 ≤ (n : ℝ) := Nat.le_ceil _
    have : (1 : ℝ) ≤ (n : ℝ) * ε ^ 2 := by
      rw [div_le_iff₀ hsq] at hge
      linarith
    linarith
  obtain ⟨P, _, hcard, hgood⟩ := weak_regularity_card_aux W hε n trivialPartition hcover
  refine ⟨P, ?_, hgood⟩
  -- trivialPartition has card 1 (index type `Unit`)
  have hcard1 : Fintype.card (trivialPartition : MeasPartition Ω μ).ι = 1 := by
    show Fintype.card Unit = 1
    simp
  rw [hcard1, mul_one] at hcard
  exact hcard
