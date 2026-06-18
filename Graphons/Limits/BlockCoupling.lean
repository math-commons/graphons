/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

CORE A coupling toolkit (Group 1) — block-to-block couplings of `(μ, μ)` for total boundedness
of graphon space.  Companion to `COUPLING_TOOLKIT.md` §2 Group 1 and §4 (atoms).

Given two finite measurable partitions `P, P'` of `(Ω, μ)`, and a *joint block law*
`J : P.ι → P'.ι → ℝ≥0∞` coupling the two part-measure vectors, we build a coupling
`blockCoupling P P' J : Measure (Ω × Ω)` of `(μ, μ)` as the finite mixture

  `blockCoupling = ∑_{i,j} J i j • (normProb P i).prod (normProb P' j)`,

where `normProb P i := (μ (P.part i))⁻¹ • μ.restrict (P.part i)` is the normalized restriction of `μ`
to block `i` (a probability measure, since blocks have positive finite measure).  No disintegration /
`condKernel` plumbing is needed: the construction is a finite sum of products of restricted measures,
and the marginal computation is elementary (`map_fst_prod`, `map_snd_prod`, `restrict_iUnion`).

This avoids building μ-independent canonical grid representatives (unrealizable on atomic μ, §4):
the net is the finite *range* of a rounding map, with closeness witnessed by
`cutDist_step_le_of_grid_close`.
-/
import Graphons.CutMetric.Gluing
import Graphons.Core.Density
import Graphons.CutMetric.CutNormL1

open MeasureTheory
open scoped ENNReal NNReal

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Normalized restriction of `μ` to a block -/

/-- The normalized restriction of `μ` to block `i` of `P`: a probability measure supported on
`P.part i`. -/
noncomputable def normProb (P : MeasPartition Ω μ) (i : P.ι) : Measure Ω :=
  (μ (P.part i))⁻¹ • μ.restrict (P.part i)

instance (P : MeasPartition Ω μ) (i : P.ι) : IsProbabilityMeasure (normProb P i) := by
  refine ⟨?_⟩
  rw [normProb, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel (P.pos i).ne' (P.measure_part_ne_top i)]

/-- `μ (P.part i) • normProb P i = μ.restrict (P.part i)` (renormalization undone). -/
theorem smul_normProb (P : MeasPartition Ω μ) (i : P.ι) :
    (μ (P.part i)) • normProb P i = μ.restrict (P.part i) := by
  rw [normProb, smul_smul, ENNReal.mul_inv_cancel (P.pos i).ne' (P.measure_part_ne_top i), one_smul]

/-- The blocks cover `Ω`: `⋃ i, P.part i = univ`. -/
theorem iUnion_part_eq_univ (P : MeasPartition Ω μ) : (⋃ i, P.part i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨P.block x, P.mem_block x⟩

/-- The blocks are pairwise disjoint (distinct fibers of `block`). -/
theorem part_pairwise_disjoint (P : MeasPartition Ω μ) :
    Pairwise (Function.onFun Disjoint P.part) := by
  intro a b hab
  simp only [Function.onFun, Set.disjoint_left]
  intro x hxa hxb
  exact hab (by rw [← (P.mem_part_iff x a).1 hxa, (P.mem_part_iff x b).1 hxb])

/-- `μ` decomposes as the finite sum of its restrictions to the blocks. -/
theorem measure_eq_sum_restrict (P : MeasPartition Ω μ) :
    μ = Measure.sum (fun i => μ.restrict (P.part i)) := by
  conv_lhs => rw [← Measure.restrict_univ (μ := μ), ← iUnion_part_eq_univ P]
  exact Measure.restrict_iUnion (part_pairwise_disjoint P)
    (fun i => P.measurable_part i)

/-- `μ` as a *finite* (Finset over `univ`) sum of restrictions to blocks. -/
theorem measure_eq_finset_sum_restrict (P : MeasPartition Ω μ) :
    μ = ∑ i, μ.restrict (P.part i) := by
  ext s hs
  conv_lhs => rw [measure_eq_sum_restrict P]
  rw [Measure.sum_apply _ hs, Measure.finsetSum_apply _ _ s, tsum_fintype]

/-- Push a finite sum of measures through a measurable map. -/
theorem map_finset_sum {ι : Type*} {β : Type*} [MeasurableSpace β] (s : Finset ι)
    (m : ι → Measure (Ω × Ω)) {f : Ω × Ω → β} (hf : Measurable f) :
    (∑ i ∈ s, m i).map f = ∑ i ∈ s, (m i).map f := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

/-- Push a finite sum of measures through a measurable map (alias used for the block-pair map). -/
theorem map_finset_sum_prod {ι : Type*} {β : Type*} [MeasurableSpace β]
    {m : ι → Measure (Ω × Ω)} {f : Ω × Ω → β} (s : Finset ι) (hf : Measurable f) :
    (∑ i ∈ s, m i).map f = ∑ i ∈ s, (m i).map f :=
  map_finset_sum s m hf

/-! ## The block-to-block coupling -/

/-- **Block coupling** of `(μ, μ)` along partitions `P, P'` with prescribed joint block law `J`.
The finite mixture `∑_{i,j} J i j • (normProb P i).prod (normProb P' j)`.  When `J` has the two
part-measure vectors as marginals (`row_sum`, `col_sum`), this is a coupling of `(μ, μ)`. -/
noncomputable def blockCoupling (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞) :
    Measure (Ω × Ω) :=
  ∑ i, ∑ j, J i j • ((normProb P i).prod (normProb P' j))

/-- The first marginal of `blockCoupling` is `μ`, given the row-sum constraint `∑_j J i j = μ Pᵢ`. -/
theorem blockCoupling_map_fst (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) :
    (blockCoupling P P' J).map Prod.fst = μ := by
  rw [blockCoupling, map_finset_sum _ _ measurable_fst]
  -- inner: map fst over j-sum
  have hinner : ∀ i, (∑ j, J i j • ((normProb P i).prod (normProb P' j))).map Prod.fst
      = (∑ j, J i j) • normProb P i := by
    intro i
    rw [map_finset_sum _ _ measurable_fst, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul]
  simp_rw [hinner, hrow]
  -- ∑ i, μ Pᵢ • normProb P i = ∑ i, μ.restrict Pᵢ = μ
  conv_rhs => rw [measure_eq_finset_sum_restrict P]
  exact Finset.sum_congr rfl (fun i _ => smul_normProb P i)

/-- The second marginal of `blockCoupling` is `μ`, given the col-sum constraint `∑_i J i j = μ P'ⱼ`. -/
theorem blockCoupling_map_snd (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (hcol : ∀ j, ∑ i, J i j = μ (P'.part j)) :
    (blockCoupling P P' J).map Prod.snd = μ := by
  rw [blockCoupling, map_finset_sum _ _ measurable_snd]
  have hinner : ∀ i, (∑ j, J i j • ((normProb P i).prod (normProb P' j))).map Prod.snd
      = ∑ j, J i j • normProb P' j := by
    intro i
    rw [map_finset_sum _ _ measurable_snd]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Measure.map_smul, Measure.map_snd_prod, measure_univ, one_smul]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  -- ∑ j, (∑ i, J i j) • normProb P' j = ∑ j, μ P'ⱼ • normProb P' j = μ
  have : ∀ j, (∑ i, J i j • normProb P' j) = (μ (P'.part j)) • normProb P' j := by
    intro j; rw [← Finset.sum_smul, hcol j]
  simp_rw [this]
  conv_rhs => rw [measure_eq_finset_sum_restrict P']
  exact Finset.sum_congr rfl (fun j _ => smul_normProb P' j)

/-- **`blockCoupling` is a coupling of `(μ, μ)`** under the row/col marginal constraints on `J`. -/
theorem blockCoupling_isCoupling (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) (hcol : ∀ j, ∑ i, J i j = μ (P'.part j)) :
    IsCoupling μ μ (blockCoupling P P' J) :=
  ⟨blockCoupling_map_fst P P' J hrow, blockCoupling_map_snd P P' J hcol⟩

/-! ## Block pushforward: `normProb` is a point mass on its block index -/

/-- `normProb P i` is supported on block `i`, so pushing forward by `P.block` gives `dirac i`. -/
theorem normProb_map_block (P : MeasPartition Ω μ) (i : P.ι) :
    (normProb P i).map P.block = Measure.dirac i := by
  have hae : P.block =ᵐ[normProb P i] (fun _ => i) := by
    have hsupp : ∀ᵐ x ∂(normProb P i), x ∈ P.part i := by
      rw [normProb]
      exact Measure.ae_smul_measure (ae_restrict_mem (P.measurable_part i)) _
    filter_upwards [hsupp] with x hx
    exact (P.mem_part_iff x i).1 hx
  rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]

/-- Block-pair pushforward of one mixture cell `(normProb P i).prod (normProb P' j)` is `dirac (i,j)`. -/
theorem blockPair_map_cell (P P' : MeasPartition Ω μ) (i : P.ι) (j : P'.ι) :
    ((normProb P i).prod (normProb P' j)).map (fun q => (P.block q.1, P'.block q.2))
      = Measure.dirac (i, j) := by
  have hm : (fun q : Ω × Ω => (P.block q.1, P'.block q.2))
      = Prod.map P.block P'.block := rfl
  rw [hm, ← Measure.map_prod_map _ _ P.measurable_block P'.measurable_block,
    normProb_map_block, normProb_map_block, Measure.dirac_prod_dirac]

/-- **Block-pair law of `blockCoupling`.**  Pushing `blockCoupling P P' J` forward by the block-pair
map `(x, x') ↦ (P.block x, P'.block x')` recovers the prescribed joint law `J` (as the finite
combination of point masses `∑ J i j • dirac (i,j)`). -/
theorem blockCoupling_map_blockPair (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞) :
    (blockCoupling P P' J).map (fun q => (P.block q.1, P'.block q.2))
      = ∑ i, ∑ j, J i j • Measure.dirac (i, j) := by
  have hbp : Measurable (fun q : Ω × Ω => (P.block q.1, P'.block q.2)) :=
    (P.measurable_block.comp measurable_fst).prodMk (P'.measurable_block.comp measurable_snd)
  rw [blockCoupling, map_finset_sum_prod _ hbp]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_finset_sum_prod _ hbp]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Measure.map_smul, blockPair_map_cell]

/-- The block-pair law of `blockCoupling` is a probability measure (it is a coupling). -/
instance instIsProbBlockCoupling (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) (hcol : ∀ j, ∑ i, J i j = μ (P'.part j)) :
    IsProbabilityMeasure (blockCoupling P P' J) :=
  (blockCoupling_isCoupling P P' J hrow hcol).isProbabilityMeasure

/-- The block-pair map. -/
private def Bmap (P P' : MeasPartition Ω μ) : Ω × Ω → P.ι × P'.ι :=
  fun q => (P.block q.1, P'.block q.2)

private theorem measurable_Bmap (P P' : MeasPartition Ω μ) : Measurable (Bmap P P') :=
  (P.measurable_block.comp measurable_fst).prodMk (P'.measurable_block.comp measurable_snd)

/-- The block-pair law evaluated at a singleton `(i, j)` returns `J i j`. -/
theorem blockLaw_singleton (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (i : P.ι) (j : P'.ι) :
    (∑ a, ∑ b, J a b • Measure.dirac (a, b)) {(i, j)} = J i j := by
  classical
  rw [Measure.finsetSum_apply _ _ _]
  rw [Finset.sum_eq_single i]
  · rw [Measure.finsetSum_apply _ _ _, Finset.sum_eq_single j]
    · rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), smul_eq_mul,
        mul_one]
    · intro b _ hb
      have hni : (i, b) ∉ ({(i, j)} : Set (P.ι × P'.ι)) := by
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]; exact fun h => hb h.2
      rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_notMem hni, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    rw [Measure.finsetSum_apply _ _ _, Finset.sum_eq_zero]
    intro b _
    have hni : (a, b) ∉ ({(i, j)} : Set (P.ι × P'.ι)) := by
      simp only [Set.mem_singleton_iff, Prod.mk.injEq]; exact fun h => ha h.1
    rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton _),
      Set.indicator_of_notMem hni, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The real mass of the block-pair law of `blockCoupling` at a singleton is `(J i j).toReal`. -/
theorem blockCoupling_blockLaw_real (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (i : P.ι) (j : P'.ι) :
    ((blockCoupling P P' J).map (Bmap P P')).real {(i, j)} = (J i j).toReal := by
  rw [Measure.real, show Bmap P P' = (fun q => (P.block q.1, P'.block q.2)) from rfl,
    blockCoupling_map_blockPair, blockLaw_singleton]

/-- **Reduction of a block-constant double integral to a finite sum** (the engine of the cut-norm
estimate).  For any `h : (P.ι × P'.ι) → (P.ι × P'.ι) → ℝ`, integrating
`(p, q) ↦ h (Bmap p) (Bmap q)` against `π.prod π` (where `π = blockCoupling P P' J` is a coupling)
equals the finite double sum weighted by `J`. -/
theorem integral_blockConst_eq_sum (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) (hcol : ∀ j, ∑ i, J i j = μ (P'.part j))
    (h : (P.ι × P'.ι) → (P.ι × P'.ι) → ℝ) :
    ∫ pq : (Ω × Ω) × (Ω × Ω),
        h (Bmap P P' pq.1) (Bmap P P' pq.2) ∂((blockCoupling P P' J).prod (blockCoupling P P' J))
      = ∑ i, ∑ j, ∑ k, ∑ l,
          (J i j).toReal * (J k l).toReal * h (i, j) (k, l) := by
  classical
  haveI : IsProbabilityMeasure (blockCoupling P P' J) :=
    instIsProbBlockCoupling P P' J hrow hcol
  set π := blockCoupling P P' J with hπ
  set ν := π.map (Bmap P P') with hν
  haveI : IsProbabilityMeasure ν := by
    rw [hν]; exact Measure.isProbabilityMeasure_map (measurable_Bmap P P').aemeasurable
  -- Change of variables along `Prod.map Bmap Bmap`.
  have hmap : (π.prod π).map (Prod.map (Bmap P P') (Bmap P P')) = ν.prod ν := by
    rw [hν, Measure.map_prod_map _ _ (measurable_Bmap P P') (measurable_Bmap P P')]
  have hcov : ∫ pq : (Ω × Ω) × (Ω × Ω),
        h (Bmap P P' pq.1) (Bmap P P' pq.2) ∂(π.prod π)
      = ∫ b : (P.ι × P'.ι) × (P.ι × P'.ι), h b.1 b.2 ∂(ν.prod ν) := by
    rw [← hmap, integral_map
      ((measurable_Bmap P P').prodMap (measurable_Bmap P P')).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    rfl
  rw [hcov]
  -- Finite discrete integral over the product Fintype.
  rw [integral_fintype (μ := ν.prod ν) Integrable.of_finite]
  -- (ν.prod ν).real {(b1,b2)} = ν.real {b1} * ν.real {b2}, and ν.real {(i,j)} = (J i j).toReal.
  have hsing : ∀ b1 b2 : P.ι × P'.ι,
      (ν.prod ν).real {(b1, b2)} = ν.real {b1} * ν.real {b2} := by
    intro b1 b2
    rw [Measure.real, Measure.real, Measure.real,
      show ({(b1, b2)} : Set ((P.ι × P'.ι) × (P.ι × P'.ι)))
        = {b1} ×ˢ {b2} from by ext x; simp [Prod.ext_iff],
      Measure.prod_prod, ENNReal.toReal_mul]
  -- Re-index the product-fintype sum as four nested sums.
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
  rw [hsing, hν, blockCoupling_blockLaw_real, blockCoupling_blockLaw_real, smul_eq_mul]

/-! ## Cut-norm of the overlay over `blockCoupling` -/

/-- **Cut norm of the overlay over `blockCoupling` as a finite sum.**  For step graphons
`U = stepGraphon W P` and `V = stepGraphon W' P'`, with `π = blockCoupling P P' J` (a coupling),
the cut norm of the overlay is bounded by the finite double sum of `J`-weighted block-value
differences. -/
theorem cutNorm_overlay_blockCoupling_le (W W' : Graphon Ω μ) (P P' : MeasPartition Ω μ)
    (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) (hcol : ∀ j, ∑ i, J i j = μ (P'.part j)) :
    cutNorm (overlay (stepGraphon W P) (stepGraphon W' P') (blockCoupling P P' J))
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, (J i j).toReal * (J k l).toReal *
          |blockAvg W.toSymmKernel P i k - blockAvg W'.toSymmKernel P' j l| := by
  haveI : IsProbabilityMeasure (blockCoupling P P' J) :=
    instIsProbBlockCoupling P P' J hrow hcol
  set π := blockCoupling P P' J with hπ
  refine le_trans (cutNorm_le_L1 _) (le_of_eq ?_)
  -- The L¹ integrand is `|h (Bmap p) (Bmap q)|` for the block-difference `h`.
  set h : (P.ι × P'.ι) → (P.ι × P'.ι) → ℝ :=
    fun a b => |blockAvg W.toSymmKernel P a.1 b.1 - blockAvg W'.toSymmKernel P' a.2 b.2| with hh
  have hpt : ∀ p : (Ω × Ω) × (Ω × Ω),
      |(overlay (stepGraphon W P) (stepGraphon W' P') π).toFun p.1 p.2|
        = h (Bmap P P' p.1) (Bmap P P' p.2) := by
    intro p
    rw [overlay_apply, hh]
    simp only [stepGraphon_toSymmKernel, stepW_apply, Bmap]
  calc ∫ p : (Ω × Ω) × (Ω × Ω),
          |(overlay (stepGraphon W P) (stepGraphon W' P') π).toFun p.1 p.2| ∂(π.prod π)
      = ∫ p : (Ω × Ω) × (Ω × Ω), h (Bmap P P' p.1) (Bmap P P' p.2) ∂(π.prod π) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (J i j).toReal * (J k l).toReal * h (i, j) (k, l) :=
        integral_blockConst_eq_sum P P' J hrow hcol h
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (J i j).toReal * (J k l).toReal *
          |blockAvg W.toSymmKernel P i k - blockAvg W'.toSymmKernel P' j l| := by
        simp only [hh]

/-! ## Telescoping estimate on the finite block-difference sum -/

/-- The total real mass of a coupling law `J` of the two part-measure vectors is `1`. -/
theorem sum_J_toReal_eq_one (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) :
    ∑ i, ∑ j, (J i j).toReal = 1 := by
  have hsum : (∑ i, ∑ j, J i j) = 1 := by
    simp_rw [hrow]
    have := P.sum_toReal_measure_part_eq_one
    rw [← ENNReal.toReal_sum (fun i _ => P.measure_part_ne_top i)] at this
    rw [← ENNReal.ofReal_one, ← this, ENNReal.ofReal_toReal]
    exact (ENNReal.sum_lt_top.2 (fun i _ => (P.measure_part_ne_top i).lt_top)).ne
  have hfin : ∀ i j, J i j ≠ ∞ := by
    intro i j
    refine ne_top_of_le_ne_top (P.measure_part_ne_top i) ?_
    rw [← hrow i]
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)
  calc ∑ i, ∑ j, (J i j).toReal
      = (∑ i, ∑ j, J i j).toReal := by
        rw [ENNReal.toReal_sum (fun i _ => ?_)]
        · exact Finset.sum_congr rfl (fun i _ => (ENNReal.toReal_sum (fun j _ => hfin i j)).symm)
        · exact (ENNReal.sum_lt_top.2 (fun j _ => (hfin i j).lt_top)).ne
    _ = 1 := by rw [hsum, ENNReal.toReal_one]

/-- **Telescoping bound** on the finite block-difference sum.  Given matching maps
`σ : P.ι → Fin k`, `σ' : P'.ι → Fin k` and:
* a `[0,1]`-bound on the block values (`hMle1` — automatic for graphons),
* a uniform `δ`-bound on the matched entries (`hmatch`),
the `J`-weighted block-difference sum is `≤ δ + 2 D`, where `D = ∑_{σ i ≠ σ' j} (J i j).toReal` is
the off-matching mass. -/
theorem blockDiff_sum_le {k : ℕ} (P P' : MeasPartition Ω μ) (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) (M : P.ι → P.ι → ℝ) (M' : P'.ι → P'.ι → ℝ)
    (σ : P.ι → Fin k) (σ' : P'.ι → Fin k) (δ : ℝ) (hδ : 0 ≤ δ)
    (hMabs : ∀ i k, M i k ∈ Set.Icc (0:ℝ) 1) (hM'abs : ∀ j l, M' j l ∈ Set.Icc (0:ℝ) 1)
    (hmatch : ∀ i j k l, σ i = σ' j → σ k = σ' l → |M i k - M' j l| ≤ δ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (J i j).toReal * (J k l).toReal * |M i k - M' j l|)
      ≤ δ + 2 * (∑ i, ∑ j, if σ i = σ' j then 0 else (J i j).toReal) := by
  classical
  set T : P.ι → P'.ι → ℝ := fun i j => (J i j).toReal with hT
  have hTnn : ∀ i j, 0 ≤ T i j := fun i j => ENNReal.toReal_nonneg
  have hStot : ∑ i, ∑ j, T i j = 1 := sum_J_toReal_eq_one P P' J hrow
  set D : ℝ := ∑ i, ∑ j, if σ i = σ' j then 0 else T i j with hD
  have hDnn : 0 ≤ D := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => by by_cases h : σ i = σ' j <;> simp [h, hTnn]))
  -- Pointwise bound on the absolute block difference.
  have hpt : ∀ i j k l, |M i k - M' j l|
      ≤ δ + (if σ i = σ' j then 0 else 1) + (if σ k = σ' l then 0 else 1) := by
    intro i j k l
    have hM1 : |M i k - M' j l| ≤ 1 := by
      have h1 := hMabs i k; have h2 := hM'abs j l
      rw [abs_le]; constructor <;> [nlinarith [h1.1, h1.2, h2.1, h2.2];
        nlinarith [h1.1, h1.2, h2.1, h2.2]]
    by_cases hij : σ i = σ' j
    · by_cases hkl : σ k = σ' l
      · simp only [hij, hkl, if_true]; linarith [hmatch i j k l hij hkl]
      · simp only [hij, hkl, if_true, if_false]; linarith
    · by_cases hkl : σ k = σ' l
      · simp only [hij, hkl, if_true, if_false]; linarith
      · simp only [hij, hkl, if_false]; linarith
  -- Bound the sum termwise then factor.
  calc ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * |M i k - M' j l|
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l *
          (δ + (if σ i = σ' j then 0 else 1) + (if σ k = σ' l then 0 else 1)) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))))
        exact mul_le_mul_of_nonneg_left (hpt i j k l)
          (mul_nonneg (hTnn i j) (hTnn k l))
    _ = δ + 2 * D := by
        -- distribute and factor each piece into products of total / off-matching sums.
        have hfac : ∀ (g : P.ι → P'.ι → ℝ),
            ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * g i j
              = (∑ i, ∑ j, T i j * g i j) * (∑ k, ∑ l, T k l) := by
          intro g
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
        have hfac' : ∀ (g : P.ι → P'.ι → ℝ),
            ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * g k l
              = (∑ i, ∑ j, T i j) * (∑ k, ∑ l, T k l * g k l) := by
          intro g
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
        -- split the integrand into three pieces.
        have hsplit : ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l *
              (δ + (if σ i = σ' j then 0 else 1) + (if σ k = σ' l then 0 else 1))
            = (∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * δ)
              + (∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * (if σ i = σ' j then 0 else 1))
              + (∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * (if σ k = σ' l then 0 else 1)) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
        rw [hsplit]
        -- piece 1: δ · 1 · 1 = δ
        have hp1 : ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * δ = δ := by
          rw [hfac (fun _ _ => δ), hStot, mul_one]
          rw [show (∑ i, ∑ j, T i j * δ) = (∑ i, ∑ j, T i j) * δ by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_mul]]
          rw [hStot, one_mul]
        -- piece 2: D · 1 = D
        have hp2 : ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * (if σ i = σ' j then 0 else 1) = D := by
          rw [hfac (fun i j => if σ i = σ' j then 0 else 1), hStot, mul_one, hD]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          by_cases h : σ i = σ' j <;> simp [h]
        -- piece 3: 1 · D = D
        have hp3 : ∑ i, ∑ j, ∑ k, ∑ l, T i j * T k l * (if σ k = σ' l then 0 else 1) = D := by
          rw [hfac' (fun k l => if σ k = σ' l then 0 else 1), hStot, one_mul, hD]
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
          by_cases h : σ k = σ' l <;> simp [h]
        rw [hp1, hp2, hp3]; ring

/-! ## Near-diagonal coupling of two finite measure vectors (combinatorial core of the net) -/

/-- **Near-diagonal coupling of two equal-mass vectors.**  Given `a, b : ι → ℝ≥0∞` (finite entries)
with equal totals, there is a joint law `J : ι → ι → ℝ≥0∞` with row marginal `a`, column marginal
`b`, whose off-diagonal mass is bounded by the "excess" `∑ i, a i - min (a i) (b i)` (= half the ℓ¹
distance of `a, b`).  Construction: `min (a i) (b i)` on the diagonal, plus the normalized product of
the two residuals off-diagonal. -/
theorem exists_nearDiag_coupling {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ≥0∞)
    (ha : ∀ i, a i ≠ ∞) (hb : ∀ i, b i ≠ ∞) (htot : ∑ i, a i = ∑ i, b i) :
    ∃ J : ι → ι → ℝ≥0∞, (∀ i, ∑ j, J i j = a i) ∧ (∀ j, ∑ i, J i j = b j) ∧
      (∑ i, ∑ j, if i = j then 0 else J i j) ≤ ∑ i, (a i - min (a i) (b i)) := by
  classical
  set c : ι → ℝ≥0∞ := fun i => min (a i) (b i) with hc
  set ra : ι → ℝ≥0∞ := fun i => a i - c i with hra
  set rb : ι → ℝ≥0∞ := fun i => b i - c i with hrb
  set R : ℝ≥0∞ := ∑ i, ra i with hR
  -- ∑ ra = ∑ rb (both equal ∑a - ∑c = ∑b - ∑c).
  have hcle_a : ∀ i, c i ≤ a i := fun i => min_le_left _ _
  have hcle_b : ∀ i, c i ≤ b i := fun i => min_le_right _ _
  have hcfin : ∀ i, c i ≠ ∞ := fun i => ne_top_of_le_ne_top (ha i) (hcle_a i)
  have hra_fin : ∀ i, ra i ≠ ∞ := fun i => ne_top_of_le_ne_top (ha i) (by rw [hra]; exact tsub_le_self)
  have hrb_fin : ∀ i, rb i ≠ ∞ := fun i => ne_top_of_le_ne_top (hb i) (by rw [hrb]; exact tsub_le_self)
  have hac : ∀ i, a i = c i + ra i := fun i => (add_tsub_cancel_of_le (hcle_a i)).symm
  have hbc : ∀ i, b i = c i + rb i := fun i => (add_tsub_cancel_of_le (hcle_b i)).symm
  have hsumc_fin : (∑ i, c i) ≠ ∞ := (ENNReal.sum_lt_top.2 (fun i _ => (hcfin i).lt_top)).ne
  -- ∑a = ∑c + R  and  ∑b = ∑c + ∑rb, hence R = ∑rb (cancel finite ∑c).
  have heqa : (∑ i, a i) = (∑ i, c i) + R := by
    rw [hR]; simp_rw [hac]; rw [Finset.sum_add_distrib]
  have heqb : (∑ i, b i) = (∑ i, c i) + (∑ i, rb i) := by
    simp_rw [hbc]; rw [Finset.sum_add_distrib]
  have hRrb : R = ∑ i, rb i := by
    have hcc : (∑ i, c i) + R = (∑ i, c i) + (∑ i, rb i) := by rw [← heqa, ← heqb, htot]
    exact (ENNReal.add_right_inj hsumc_fin).1 hcc
  have hRfin : R ≠ ∞ :=
    ne_top_of_le_ne_top ((ENNReal.sum_lt_top.2 (fun i _ => (hra_fin i).lt_top)).ne) le_rfl
  -- The coupling.
  refine ⟨fun i j => (if i = j then c i else 0) + ra i * rb j / R, ?_, ?_, ?_⟩
  · -- row sums = a i
    intro i
    rw [Finset.sum_add_distrib]
    have h1 : (∑ j, if i = j then c i else 0) = c i := by
      rw [Finset.sum_ite_eq Finset.univ i (fun _ => c i)]; simp
    rw [h1]
    have h2 : (∑ j, ra i * rb j / R) = ra i := by
      simp_rw [div_eq_mul_inv, mul_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← hRrb]
      rcases eq_or_ne R 0 with hR0 | hR0
      · -- R = 0 ⟹ ra i = 0
        have hrai : ra i = 0 := by
          have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset ι))
            (f := ra) (fun _ _ => bot_le)).1 (by rw [← hR]; exact hR0)
          exact hz i (Finset.mem_univ i)
        rw [hrai]; simp
      · rw [ENNReal.mul_inv_cancel hR0 hRfin, mul_one]
    rw [h2, hra, add_tsub_cancel_of_le (hcle_a i)]
  · -- col sums = b j
    intro j
    rw [Finset.sum_add_distrib]
    have h1 : (∑ i, if i = j then c i else 0) = c j := by
      rw [Finset.sum_ite_eq' Finset.univ j (fun i => c i)]; simp
    rw [h1]
    have h2 : (∑ i, ra i * rb j / R) = rb j := by
      simp_rw [div_eq_mul_inv]
      rw [show (∑ i, ra i * rb j * R⁻¹) = (∑ i, ra i) * rb j * R⁻¹ by
        rw [Finset.sum_mul, Finset.sum_mul]]
      rw [← hR]
      rcases eq_or_ne R 0 with hR0 | hR0
      · have hrbj : rb j = 0 := by
          have hz : ∑ i, rb i = 0 := by rw [← hRrb]; exact hR0
          exact (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset ι))
            (f := rb) (fun _ _ => bot_le)).1 hz j (Finset.mem_univ j)
        rw [hrbj]; simp
      · rw [mul_comm R (rb j), mul_assoc, ENNReal.mul_inv_cancel hR0 hRfin, mul_one]
    rw [h2, hrb, add_tsub_cancel_of_le (hcle_b j)]
  · -- off-diagonal mass ≤ ∑ ra
    have hoff : ∀ i j, (if i = j then (0:ℝ≥0∞) else (if i = j then c i else 0) + ra i * rb j / R)
        = if i = j then 0 else ra i * rb j / R := by
      intro i j; by_cases h : i = j <;> simp [h]
    simp_rw [hoff]
    calc ∑ i, ∑ j, (if i = j then (0:ℝ≥0∞) else ra i * rb j / R)
        ≤ ∑ i, ∑ j, ra i * rb j / R := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          by_cases h : i = j <;> simp [h]
      _ = (∑ i, ra i) * (∑ j, rb j) / R := by
          have hdd : ∑ i, ∑ j, ra i * rb j / R
              = (∑ i, ∑ j, ra i * rb j) * R⁻¹ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [div_eq_mul_inv]
          rw [hdd, Finset.sum_mul_sum, div_eq_mul_inv]
      _ ≤ ∑ i, ra i := by
          rw [← hR, ← hRrb]
          rcases eq_or_ne R 0 with hR0 | hR0
          · rw [hR0]; simp
          · rw [mul_div_assoc, ENNReal.div_self hR0 hRfin, mul_one]


/-! ## The grid-closeness bound on cut distance (Group 1.2) -/

/-- **Cut distance between two step graphons via a block coupling.**  If `J` is a coupling of the two
part-measure vectors, `σ, σ'` are matching maps to a common index set `Fin k`, and the block-value
matrices agree to within `δ` on matched entries, then
  `cutDist (stepGraphon W P) (stepGraphon W' P') ≤ δ + 2 D`,
where `D = ∑_{σ i ≠ σ' j} (J i j).toReal` is the off-matching mass of the coupling. -/
theorem cutDist_step_le_of_blockCoupling {k : ℕ} (W W' : Graphon Ω μ) (P P' : MeasPartition Ω μ)
    (J : P.ι → P'.ι → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, J i j = μ (P.part i)) (hcol : ∀ j, ∑ i, J i j = μ (P'.part j))
    (σ : P.ι → Fin k) (σ' : P'.ι → Fin k) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmatch : ∀ i j k l, σ i = σ' j → σ k = σ' l →
      |blockAvg W.toSymmKernel P i k - blockAvg W'.toSymmKernel P' j l| ≤ δ) :
    cutDist (stepGraphon W P) (stepGraphon W' P')
      ≤ δ + 2 * (∑ i, ∑ j, if σ i = σ' j then 0 else (J i j).toReal) := by
  haveI : IsProbabilityMeasure (blockCoupling P P' J) :=
    instIsProbBlockCoupling P P' J hrow hcol
  refine le_trans (cutDist_le_of_coupling _ _
    ⟨blockCoupling P P' J, blockCoupling_isCoupling P P' J hrow hcol⟩) ?_
  refine le_trans (cutNorm_overlay_blockCoupling_le W W' P P' J hrow hcol) ?_
  exact blockDiff_sum_le P P' J hrow
    (blockAvg W.toSymmKernel P) (blockAvg W'.toSymmKernel P') σ σ' δ hδ
    (fun i k => blockAvg_mem_Icc W P i k) (fun j l => blockAvg_mem_Icc W' P' j l) hmatch

/-- **Cut distance between two equal-card step graphons that grid-match.**  Given equivalences
`eP : P.ι ≃ Fin k`, `eP' : P'.ι ≃ Fin k` identifying the parts of the two partitions with a common
`Fin k`, a per-entry bound `δ` on the matched block values, and a `[0,1]`-valued grid-rounding of the
part measures whose error per part is `≤ η/k` (encoded abstractly through the near-diagonal coupling
of the two part-measure vectors), the cut distance is bounded by `δ + 2 D`, where `D` is the
off-diagonal mass of the near-diagonal coupling.  This is the concrete consumer of
`exists_nearDiag_coupling` + `cutDist_step_le_of_blockCoupling`. -/
theorem cutDist_step_le_of_equiv {k : ℕ} (W W' : Graphon Ω μ) (P P' : MeasPartition Ω μ)
    (eP : P.ι ≃ Fin k) (eP' : P'.ι ≃ Fin k) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmatch : ∀ i j k₂ l, eP i = eP' j → eP k₂ = eP' l →
      |blockAvg W.toSymmKernel P i k₂ - blockAvg W'.toSymmKernel P' j l| ≤ δ) :
    cutDist (stepGraphon W P) (stepGraphon W' P')
      ≤ δ + 2 * (∑ a : Fin k, (μ (P.part (eP.symm a))
          - min (μ (P.part (eP.symm a))) (μ (P'.part (eP'.symm a)))).toReal) := by
  classical
  -- Part-measure vectors transported to `Fin k`.
  set av : Fin k → ℝ≥0∞ := fun a => μ (P.part (eP.symm a)) with hav
  set bv : Fin k → ℝ≥0∞ := fun a => μ (P'.part (eP'.symm a)) with hbv
  have havfin : ∀ a, av a ≠ ∞ := fun a => P.measure_part_ne_top _
  have hbvfin : ∀ a, bv a ≠ ∞ := fun a => P'.measure_part_ne_top _
  have htot : ∑ a, av a = ∑ a, bv a := by
    have h1 : ∑ a : Fin k, av a = 1 := by
      rw [hav, Equiv.sum_comp eP.symm (fun i => μ (P.part i))]
      have := P.sum_toReal_measure_part_eq_one
      rw [← ENNReal.toReal_sum (fun i _ => P.measure_part_ne_top i)] at this
      rw [← ENNReal.ofReal_one, ← this, ENNReal.ofReal_toReal
        (ENNReal.sum_lt_top.2 (fun i _ => (P.measure_part_ne_top i).lt_top)).ne]
    have h2 : ∑ a : Fin k, bv a = 1 := by
      rw [hbv, Equiv.sum_comp eP'.symm (fun j => μ (P'.part j))]
      have := P'.sum_toReal_measure_part_eq_one
      rw [← ENNReal.toReal_sum (fun j _ => P'.measure_part_ne_top j)] at this
      rw [← ENNReal.ofReal_one, ← this, ENNReal.ofReal_toReal
        (ENNReal.sum_lt_top.2 (fun j _ => (P'.measure_part_ne_top j).lt_top)).ne]
    rw [h1, h2]
  obtain ⟨JF, hrowF, hcolF, hoffF⟩ := exists_nearDiag_coupling av bv havfin hbvfin htot
  -- Pull back to a coupling on `P.ι × P'.ι`.
  set J : P.ι → P'.ι → ℝ≥0∞ := fun i j => JF (eP i) (eP' j) with hJ
  have hrow : ∀ i, ∑ j, J i j = μ (P.part i) := by
    intro i
    simp only [hJ]
    rw [Equiv.sum_comp eP' (fun b => JF (eP i) b), hrowF (eP i)]
    simp only [hav, Equiv.symm_apply_apply]
  have hcol : ∀ j, ∑ i, J i j = μ (P'.part j) := by
    intro j
    simp only [hJ]
    rw [Equiv.sum_comp eP (fun a => JF a (eP' j)), hcolF (eP' j)]
    simp only [hbv, Equiv.symm_apply_apply]
  -- The off-matching mass of `J` equals the off-diagonal mass of `JF`.
  have hDeq : (∑ i, ∑ j, if eP i = eP' j then 0 else (J i j).toReal)
      = (∑ a : Fin k, ∑ b : Fin k, if a = b then (0:ℝ) else (JF a b).toReal) := by
    rw [← Equiv.sum_comp eP.symm
      (fun i => ∑ j, if eP i = eP' j then (0:ℝ) else (J i j).toReal)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Equiv.sum_comp eP'.symm
      (fun j => if eP (eP.symm a) = eP' j then (0:ℝ) else (J (eP.symm a) j).toReal)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hJ, Equiv.apply_symm_apply]
  refine le_trans (cutDist_step_le_of_blockCoupling W W' P P' J hrow hcol eP eP' δ hδ ?_) ?_
  · intro i j k₂ l hij hkl; exact hmatch i j k₂ l hij hkl
  · rw [hDeq]
    -- D = ∑∑ off-diagonal JF ≤ ∑ (av - min) by hoffF; rewrite via toReal.
    have hJFfin : ∀ a b, JF a b ≠ ∞ := by
      intro a b
      refine ne_top_of_le_ne_top (havfin a) ?_
      rw [← hrowF a]
      exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ b)
    have hlhs : (∑ a : Fin k, ∑ b : Fin k, if a = b then (0:ℝ) else (JF a b).toReal)
        = (∑ a, ∑ b, if a = b then (0:ℝ≥0∞) else JF a b).toReal := by
      rw [ENNReal.toReal_sum (fun a _ => (ENNReal.sum_lt_top.2 (fun b _ => by
        by_cases h : a = b <;> simp [h, (hJFfin a b).lt_top])).ne)]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [ENNReal.toReal_sum (fun b _ => by by_cases h : a = b <;> simp [h, hJFfin a b])]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases h : a = b <;> simp [h]
    have hrhs : (∑ a : Fin k, (av a - min (av a) (bv a)).toReal)
        = (∑ a, (av a - min (av a) (bv a))).toReal := by
      rw [ENNReal.toReal_sum (fun a _ => ne_top_of_le_ne_top (havfin a) tsub_le_self)]
    rw [hlhs, hrhs]
    have hle : (∑ a, ∑ b, if a = b then (0:ℝ≥0∞) else JF a b).toReal
        ≤ (∑ a, (av a - min (av a) (bv a))).toReal :=
      ENNReal.toReal_mono
        ((ENNReal.sum_lt_top.2 (fun a _ =>
          (ne_top_of_le_ne_top (havfin a) tsub_le_self).lt_top)).ne) hoffF
    have hfin := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 2)
    linarith

/-! ## Grid rounding (for the finite net) -/

/-- Round `x ∈ [0,1]` to the `m`-grid index `⌊x·m⌋` (clamped to `Fin (m+1)`). -/
noncomputable def gridIdx (m : ℕ) (x : ℝ) : Fin (m + 1) :=
  ⟨min m ⌊x * m⌋₊, by omega⟩

/-- The rounding error: for `x ∈ [0,1]` and `m ≥ 1`,
`|x - (gridIdx m x).val / m| ≤ 1/m`. -/
theorem gridIdx_close {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - ((gridIdx m x).val : ℝ) / m| ≤ 1 / m := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hxm0 : 0 ≤ x * m := mul_nonneg hx0 hmR.le
  have hxm_le : x * m ≤ m := by nlinarith
  have hfloor_le : ⌊x * m⌋₊ ≤ m := by
    have := Nat.floor_le_floor (R := ℝ) hxm_le
    simpa [Nat.floor_natCast] using this
  have hidx : ((gridIdx m x).val : ℕ) = ⌊x * m⌋₊ := by
    simp only [gridIdx, Fin.val_mk]; omega
  rw [hidx]
  -- ⌊x*m⌋₊ ≤ x*m < ⌊x*m⌋₊+1.
  have hfl : (⌊x * m⌋₊ : ℝ) ≤ x * m := Nat.floor_le hxm0
  have hflu : x * m < (⌊x * m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hd1 : (⌊x * m⌋₊ : ℝ) / m ≤ x := by rw [div_le_iff₀ hmR]; exact hfl
  have hd2 : x - (⌊x * m⌋₊ : ℝ) / m ≤ 1 / m := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hmR]; nlinarith [hflu]
  rw [abs_le]
  refine ⟨by linarith [div_nonneg (by positivity : (0:ℝ) ≤ 1) hmR.le], hd2⟩

end Graphons
