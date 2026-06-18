/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

**Completeness of the concrete graphon space `GraphonSpace ℝ unitMeasure`.**

The general completeness instance `instCompleteSpaceGraphonSpace` is blocked at
`CarrierLimit.exists_carrier_limit` by the absence of a measure-isomorphism theorem transporting
the carrier limit `W∞` (living on `(Ω^ℕ, seqGlue π)`) back to the atomic carrier `(Ω, μ)`.

This file develops the *carrier-internal* limit machinery that is the genuinely-Mathlib-powered
core of the limit step, free of any transport:

  **`cutNorm_tendsto_of_L1Cauchy`-style lemma** — over a FIXED carrier `(α, ρ)`, an `L¹`-Cauchy
  sequence of graphons (i.e. `∫∫ |Wₙ − Wₘ| → 0`) converges to a genuine `[0,1]`-valued symmetric
  limit graphon `W∞ : Graphon α ρ` with `∫∫ |Wₙ − W∞| → 0`, hence (via `cutDist_le_cutNorm` +
  `cutNorm_le_L1`) `cutDist (Wₙ, W∞) → 0`.

The limit graphon is extracted from the `Lp 1` limit of the uncurried integrands by
`Lp.instCompleteSpace`, symmetrized and clamped to `[0,1]` to land back in `Graphon`.
-/
import Graphons.Limits.Compactness
import Graphons.Core.Density
import Graphons.Limits.WeakRegularity

open MeasureTheory Filter Topology

namespace Graphons

namespace CompletenessUnit

/-! ### A carrier-internal limit from an L¹-Cauchy sequence of graphons

We work over a fixed standard-Borel probability carrier `(α, ρ)`. The uncurried integrands
`fₙ := uncurry (Wₙ).toFun : α × α → ℝ` live in `Lp 1 (ρ.prod ρ)`; if the `fₙ` are `L¹`-Cauchy we
obtain an `Lp`-limit and, from a measurable `[0,1]`-valued symmetric representative of it, a genuine
limit graphon. -/

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α} [IsProbabilityMeasure ρ]

/-- The uncurried integrand of a graphon, as a member of `Lp 1 (ρ.prod ρ)`. -/
noncomputable def toLpFun (W : Graphon α ρ) : Lp ℝ 1 (ρ.prod ρ) :=
  (memLp_one_iff_integrable.mpr (W.toSymmKernel.integrable_uncurry)).toLp _

/-- `toLpFun W` is a.e. equal to the uncurried integrand of `W`. -/
theorem coeFn_toLpFun (W : Graphon α ρ) :
    toLpFun W =ᵐ[ρ.prod ρ] Function.uncurry W.toFun :=
  MemLp.coeFn_toLp _

/-- The `Lp 1` distance between two graphons' integrands equals the `L¹` distance
`∫∫ |U − W|` of the kernels. -/
theorem dist_toLpFun (U W : Graphon α ρ) :
    dist (toLpFun U) (toLpFun W)
      = ∫ p : α × α, |U.toFun p.1 p.2 - W.toFun p.1 p.2| ∂(ρ.prod ρ) := by
  rw [dist_eq_norm_sub, L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (toLpFun U) (toLpFun W), coeFn_toLpFun U, coeFn_toLpFun W]
    with p hsub hU hW
  rw [hsub, Pi.sub_apply, hU, hW, Real.norm_eq_abs]
  rfl

/-- **The key bridge:** on a fixed carrier `(α, ρ)`, the cut distance is bounded by the `Lp 1`
distance of the integrands.  Combines `cutDist_le_cutNorm`, `cutNorm_le_L1` and `dist_toLpFun`. -/
theorem cutDist_le_dist_toLpFun (U W : Graphon α ρ) :
    cutDist U W ≤ dist (toLpFun U) (toLpFun W) := by
  refine le_trans (cutDist_le_cutNorm U W) ?_
  refine le_trans (cutNorm_le_L1 (U.toSymmKernel - W.toSymmKernel)) ?_
  rw [dist_toLpFun]
  apply le_of_eq
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp [SymmKernel.sub_apply]

/-! ### Building a graphon from a measurable function

Given any measurable `g : α × α → ℝ`, the symmetrized-and-clamped function
`gphFun g x y := max 0 (min 1 ((g (x,y) + g (y,x)) / 2))` is everywhere symmetric and
`[0,1]`-valued, hence assembles into a `Graphon α ρ`. -/

/-- The symmetrized, `[0,1]`-clamped version of a two-variable function. -/
noncomputable def gphFun (g : α × α → ℝ) (x y : α) : ℝ :=
  max 0 (min 1 ((g (x, y) + g (y, x)) / 2))

theorem gphFun_symm (g : α × α → ℝ) (x y : α) : gphFun g x y = gphFun g y x := by
  unfold gphFun; rw [add_comm]

theorem gphFun_nonneg (g : α × α → ℝ) (x y : α) : 0 ≤ gphFun g x y := le_max_left _ _

theorem gphFun_le_one (g : α × α → ℝ) (x y : α) : gphFun g x y ≤ 1 := by
  unfold gphFun
  rcases le_total (min 1 ((g (x, y) + g (y, x)) / 2)) 0 with h | h
  · rw [max_eq_left h]; exact zero_le_one
  · rw [max_eq_right h]; exact min_le_left _ _

theorem measurable_gphFun {g : α × α → ℝ} (hg : Measurable g) :
    Measurable (Function.uncurry (gphFun g)) := by
  have hswap : Measurable (fun p : α × α => g (p.2, p.1)) :=
    hg.comp (measurable_snd.prodMk measurable_fst)
  have : Measurable (fun p : α × α => (g p + g (p.2, p.1)) / 2) :=
    ((hg.add hswap).div_const 2)
  exact (measurable_const.max (measurable_const.min this))

/-- A `Graphon α ρ` built from a measurable function by symmetrizing and clamping to `[0,1]`. -/
noncomputable def graphonOf {g : α × α → ℝ} (hg : Measurable g) : Graphon α ρ :=
  Graphon.mk' (gphFun g) (gphFun_symm g) (measurable_gphFun hg)
    (gphFun_nonneg g) (gphFun_le_one g)

@[simp] theorem graphonOf_apply {g : α × α → ℝ} (hg : Measurable g) (x y : α) :
    (graphonOf (ρ := ρ) hg).toFun x y = gphFun g x y := rfl

/-- If `g` is a.e. symmetric (under `Prod.swap`) and a.e. `[0,1]`-valued, then the symmetrized,
clamped function `Function.uncurry (gphFun g)` agrees with `g` almost everywhere — so the
graphon `graphonOf hg` represents the same `L¹` class as `g`. -/
theorem uncurry_gphFun_ae_eq {g : α × α → ℝ} (hg : Measurable g)
    (hsym : ∀ᵐ p ∂(ρ.prod ρ), g p = g p.swap)
    (hmem : ∀ᵐ p ∂(ρ.prod ρ), g p ∈ Set.Icc (0 : ℝ) 1) :
    Function.uncurry (gphFun g) =ᵐ[ρ.prod ρ] g := by
  filter_upwards [hsym, hmem] with p hps hpm
  obtain ⟨x, y⟩ := p
  simp only [Function.uncurry, gphFun]
  have hswap : g (y, x) = g (x, y) := hps.symm
  rw [hswap]
  have : (g (x, y) + g (x, y)) / 2 = g (x, y) := by ring
  rw [this, min_eq_right hpm.2, max_eq_right hpm.1]

/-- The integrand of `graphonOf hg` is a.e. equal to `g`, under the a.e. symmetry and `[0,1]`
hypotheses. -/
theorem toLpFun_graphonOf_ae_eq {g : α × α → ℝ} (hg : Measurable g)
    (hsym : ∀ᵐ p ∂(ρ.prod ρ), g p = g p.swap)
    (hmem : ∀ᵐ p ∂(ρ.prod ρ), g p ∈ Set.Icc (0 : ℝ) 1) :
    toLpFun (graphonOf (ρ := ρ) hg) =ᵐ[ρ.prod ρ] g := by
  have h1 : (toLpFun (graphonOf (ρ := ρ) hg) : α × α → ℝ)
      =ᵐ[ρ.prod ρ] Function.uncurry (graphonOf (ρ := ρ) hg).toFun :=
    coeFn_toLpFun _
  have h2 : Function.uncurry (graphonOf (ρ := ρ) hg).toFun =ᵐ[ρ.prod ρ] g :=
    uncurry_gphFun_ae_eq hg hsym hmem
  exact h1.trans h2

/-! ### A.e. properties of graphon integrands -/

/-- The integrand of a graphon is a.e. `[0,1]`-valued. -/
theorem toLpFun_mem_Icc_ae (W : Graphon α ρ) :
    ∀ᵐ p ∂(ρ.prod ρ), (toLpFun W : α × α → ℝ) p ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [coeFn_toLpFun W] with p hp
  rw [hp]
  exact ⟨W.nonneg' p.1 p.2, W.le_one' p.1 p.2⟩

/-- The integrand of a graphon is a.e. swap-symmetric. -/
theorem toLpFun_symm_ae (W : Graphon α ρ) :
    ∀ᵐ p ∂(ρ.prod ρ), (toLpFun W : α × α → ℝ) p = (toLpFun W : α × α → ℝ) p.swap := by
  -- swap is measure-preserving on `ρ.prod ρ`, so the coercion a.e.-eq pulls back along swap
  have hmp : MeasurePreserving Prod.swap (ρ.prod ρ) (ρ.prod ρ) := by
    have := Measure.measurePreserving_swap (μ := ρ) (ν := ρ)
    simpa using this
  have hc := coeFn_toLpFun W
  have hcswap : (fun p => (toLpFun W : α × α → ℝ) p.swap)
      =ᵐ[ρ.prod ρ] (fun p => Function.uncurry W.toFun p.swap) := by
    have := (hc.comp_tendsto (hmp.quasiMeasurePreserving.tendsto_ae))
    simpa [Function.comp] using this
  filter_upwards [hc, hcswap] with p hp hpswap
  rw [hp, hpswap]
  obtain ⟨x, y⟩ := p
  exact (W.symm' x y)

/-! ### The carrier-internal limit graphon -/

/-- **A.e. closure properties pass to the `Lp` limit.**  If `toLpFun (W n) → F` in `Lp 1`, then the
limit `F` is a.e. `[0,1]`-valued and a.e. swap-symmetric. -/
theorem limit_ae_props (W : ℕ → Graphon α ρ) {F : Lp ℝ 1 (ρ.prod ρ)}
    (hF : Tendsto (fun n => toLpFun (W n)) atTop (𝓝 F)) :
    (∀ᵐ p ∂(ρ.prod ρ), (F : α × α → ℝ) p ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ᵐ p ∂(ρ.prod ρ), (F : α × α → ℝ) p = (F : α × α → ℝ) p.swap) := by
  -- a.e. convergent subsequence
  have htim : TendstoInMeasure (ρ.prod ρ) (fun n => (toLpFun (W n) : α × α → ℝ)) atTop F :=
    tendstoInMeasure_of_tendsto_Lp hF
  obtain ⟨ns, hns_mono, hns_ae⟩ := htim.exists_seq_tendsto_ae
  -- swap is measure-preserving
  have hmp : MeasurePreserving Prod.swap (ρ.prod ρ) (ρ.prod ρ) := by
    have := Measure.measurePreserving_swap (μ := ρ) (ν := ρ); simpa using this
  constructor
  · -- membership: each subsequence value is a.e. in `[0,1]`, limit in closed `[0,1]`
    have hall : ∀ᵐ p ∂(ρ.prod ρ), ∀ i,
        (toLpFun (W (ns i)) : α × α → ℝ) p ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ae_all_iff]; exact fun i => toLpFun_mem_Icc_ae (W (ns i))
    filter_upwards [hns_ae, hall] with p hp hpall
    exact isClosed_Icc.mem_of_tendsto hp (Filter.Eventually.of_forall hpall)
  · -- symmetry: subsequence is a.e. swap-symmetric AND converges a.e. at swapped points
    have hsym_all : ∀ᵐ p ∂(ρ.prod ρ), ∀ i,
        (toLpFun (W (ns i)) : α × α → ℝ) p = (toLpFun (W (ns i)) : α × α → ℝ) p.swap := by
      rw [ae_all_iff]; exact fun i => toLpFun_symm_ae (W (ns i))
    -- a.e. convergence at swapped points (pull back the a.e. set along the measure-preserving swap)
    have hns_ae_swap : ∀ᵐ p ∂(ρ.prod ρ),
        Tendsto (fun i => (toLpFun (W (ns i)) : α × α → ℝ) p.swap) atTop
          (𝓝 ((F : α × α → ℝ) p.swap)) := by
      have := (hmp.quasiMeasurePreserving.tendsto_ae).eventually hns_ae
      simpa [Function.comp] using this
    filter_upwards [hns_ae, hns_ae_swap, hsym_all] with p hp hpswap hpsym
    -- `f(ns i) p = f(ns i) p.swap` for all i, lhs → F p, rhs → F p.swap, so F p = F p.swap
    have hlim : Tendsto (fun i => (toLpFun (W (ns i)) : α × α → ℝ) p) atTop
        (𝓝 ((F : α × α → ℝ) p.swap)) := by
      refine hpswap.congr (fun i => (hpsym i).symm)
    exact tendsto_nhds_unique hp hlim

variable [StandardBorelSpace α]

/-- **Carrier-internal completeness (the analytic core).**  If the integrands `toLpFun (W n)` form
a Cauchy sequence in `Lp 1 (ρ.prod ρ)`, then there is a limit graphon `W∞ : Graphon α ρ` with
`cutDist (W n) W∞ → 0`.  The limit is the symmetrized-clamped representative of the `Lp` limit
(`Lp.instCompleteSpace`), which lands back in `Graphon` via `graphonOf`. -/
theorem exists_graphon_cutDist_tendsto_of_lpCauchy (W : ℕ → Graphon α ρ)
    (hCauchy : CauchySeq (fun n => toLpFun (W n))) :
    ∃ Wlim : Graphon α ρ, Tendsto (fun n => cutDist (W n) Wlim) atTop (𝓝 0) := by
  -- `Lp 1` is complete: extract the limit `F`.
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hCauchy
  -- a measurable representative `g` of `F`
  set g : α × α → ℝ := (Lp.aestronglyMeasurable F).mk _ with hg_def
  have hg_meas : Measurable g := (Lp.aestronglyMeasurable F).measurable_mk
  have hgF : (F : α × α → ℝ) =ᵐ[ρ.prod ρ] g := (Lp.aestronglyMeasurable F).ae_eq_mk
  -- a.e. properties of `F`, transported to `g`
  obtain ⟨hFmem, hFsym⟩ := limit_ae_props W hF
  have hgmem : ∀ᵐ p ∂(ρ.prod ρ), g p ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hFmem, hgF] with p hpm hpg; rwa [hpg] at hpm
  have hgsym : ∀ᵐ p ∂(ρ.prod ρ), g p = g p.swap := by
    have hgFswap : (fun p => (F : α × α → ℝ) p.swap) =ᵐ[ρ.prod ρ] (fun p => g p.swap) := by
      have hmp : MeasurePreserving Prod.swap (ρ.prod ρ) (ρ.prod ρ) := by
        have := Measure.measurePreserving_swap (μ := ρ) (ν := ρ); simpa using this
      exact hgF.comp_tendsto (hmp.quasiMeasurePreserving.tendsto_ae)
    filter_upwards [hFsym, hgF, hgFswap] with p hps hpg hpgs
    rw [← hpg, ← hpgs, hps]
  -- the limit graphon
  refine ⟨graphonOf (ρ := ρ) hg_meas, ?_⟩
  -- `toLpFun (graphonOf hg) = F` in `Lp`, because both equal `g` a.e.
  have htoLp_eq : toLpFun (graphonOf (ρ := ρ) hg_meas) = F := by
    apply Lp.ext
    refine (toLpFun_graphonOf_ae_eq hg_meas hgsym hgmem).trans hgF.symm
  -- the `Lp` distance to the limit tends to 0
  have hdist : Tendsto (fun n => dist (toLpFun (W n)) (toLpFun (graphonOf (ρ := ρ) hg_meas)))
      atTop (𝓝 0) := by
    rw [htoLp_eq]
    exact tendsto_iff_dist_tendsto_zero.mp hF
  -- squeeze `cutDist`
  refine squeeze_zero (fun n => cutDist_nonneg _ _) (fun n => cutDist_le_dist_toLpFun _ _) hdist

/-- **Carrier-internal completeness, fast-sequence form.**  A sequence of graphons on `(α, ρ)`
whose integrands are `Lp 1`-Cauchy has a `δ□`-limit *point* in `GraphonSpace α ρ`. -/
theorem exists_tendsto_class_of_lpCauchy (W : ℕ → Graphon α ρ)
    (hCauchy : CauchySeq (fun n => toLpFun (W n))) :
    ∃ z : GraphonSpace α ρ,
      Tendsto (fun n => (Quotient.mk (graphonSetoid α ρ) (W n) : GraphonSpace α ρ))
        atTop (nhds (X := GraphonSpace α ρ) z) := by
  obtain ⟨Wlim, hWlim⟩ := exists_graphon_cutDist_tendsto_of_lpCauchy W hCauchy
  refine ⟨(Quotient.mk (graphonSetoid α ρ) Wlim : GraphonSpace α ρ), ?_⟩
  refine (tendsto_iff_dist_tendsto_zero (α := GraphonSpace α ρ) (β := ℕ)
    (f := fun n => (Quotient.mk (graphonSetoid α ρ) (W n) : GraphonSpace α ρ))
    (x := atTop) (a := (Quotient.mk (graphonSetoid α ρ) Wlim : GraphonSpace α ρ))).mpr ?_
  refine hWlim.congr (fun n => ?_)
  exact (GraphonSpace.dist_mk (W n) Wlim).symm

/-! ### The concrete unit-interval carrier `(ℝ, unitMeasure)`

`ℝ` is a standard Borel space and `unitMeasure` is a probability measure, so all of the
carrier-internal `Lp`-limit machinery above applies.

Completeness of `GraphonSpace ℝ unitMeasure` is the deep half of the Lovász–Szegedy compactness
theorem.  We split it into TWO honest classical facts, each absent from Mathlib v4.30.0, and
*build* the rest of the limit from them.

**WHY NOT `L¹`-Cauchy reps?**  A previous draft tried to produce `δ□`-equivalent representatives
whose integrands are `L¹`-Cauchy (`CauchySeq (toLpFun (W' n))`).  THAT IS FALSE.  Counterexample:
quasirandom `0/1` step-graphons converge in `δ□` to the constant `½`, but `cutDist = 0` preserves
the value distribution, so *every* representative `W'ₙ` keeps `‖W'ₙ − ½‖₁ = ½`; hence no
representative sequence can be `L¹`-convergent (or `L¹`-Cauchy with limit a graphon) while staying
`δ□`-equivalent.  The genuine classical alignment is **cut-norm** alignment, not `L¹`.

So below:
* `cutNorm_alignment_unit` produces **cut-norm-Cauchy** reps (TRUE — Birkhoff–vN / Rokhlin);
* `dyadic_l1Cauchy_approx_unit` replaces cut-norm-Cauchy reps by a *different* sequence of
  graphons `S` that ARE `L¹`-Cauchy and `δ□`-close (TRUE — dyadic conditional expectations + Lévy;
  the `Sₙ` are the block-averages `E[W'ₙ | 𝒢_{k(n)}]`, NOT the reps themselves, so the
  counterexample above does not apply: a block-average's value distribution is free to concentrate
  at `½`).
The `L¹`-Cauchy `S` is then fed to the carrier-internal `exists_graphon_cutDist_tendsto_of_lpCauchy`
and combined with the `δ□`-closeness by the triangle inequality. -/

/-- The cut-norm Cauchy condition for a sequence of graphons over a fixed carrier: the kernel
differences are cut-norm Cauchy. -/
def CutNormCauchy {α : Type*} [MeasurableSpace α] {ρ : Measure α} [IsProbabilityMeasure ρ]
    (W : ℕ → Graphon α ρ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, cutNorm ((W n).toSymmKernel - (W m).toSymmKernel) ≤ ε

/-- **AXIOM 1 — Cut-norm alignment on `([0,1], Lebesgue)`.**
(Birkhoff–von Neumann coupling realization / Rokhlin isomorphism of an atomless standard
probability space with `([0,1], Leb)`.)

Given a fast `δ□`-Cauchy sequence of graphons on the concrete carrier `([0,1], Lebesgue)`, there
exist `δ□`-equivalent representatives `W'ₙ` (same `δ□`-class as `Wₙ`) whose kernels are
**cut-norm-Cauchy** over the fixed carrier.

Mathematically (Lovász, *Large Networks and Graph Limits*, 2012, §9, esp. Thm 9.23 and the
coupling/overlay description of `δ□`): a coupling `π` realizing `cutDist (Wₙ) (Wₘ) ≈ cutNorm(overlay)`
can, on `([0,1], Leb)` — an atomless standard Borel probability space — be realized (up to arbitrary
cut-norm error) by a *measure-preserving rearrangement* of `[0,1]`, because every coupling of
`(Leb, Leb)` is approximated in cut-norm by graphs of measure-preserving maps (the Birkhoff /
doubly-stochastic-by-permutations approximation, transported to `[0,1]` via Rokhlin's theorem).
Pulling each `Wₙ` back along such a rearrangement to a common copy of `[0,1]` makes the kernels
cut-norm-Cauchy while preserving the `δ□`-class.

**TRUE — counterexample check.**  This asserts only **cut-norm** Cauchyness, which is exactly the
mode in which `δ□`-Cauchy sequences DO align on `[0,1]` (cut-norm `δ→0` matches `δ□→0` since the
extra rearrangement freedom is the coupling that `δ□` already optimizes over).  It does **not**
assert any `L¹`/`toLpFun` convergence of the reps (the quasirandom counterexample only rules out the
`L¹` form, which we deliberately avoid).  To be discharged later. -/
axiom cutNorm_alignment_unit (W : ℕ → Graphon ℝ unitMeasure)
    (hfast : ∀ k, cutDist (W k) (W (k + 1)) ≤ (1 / 2 : ℝ) ^ k) :
    ∃ W' : ℕ → Graphon ℝ unitMeasure,
      (∀ n, cutDist (W n) (W' n) = 0) ∧ CutNormCauchy W'

/-- **AXIOM 2 — Dyadic `L¹`-Cauchy approximation on `([0,1], Lebesgue)`.**
(Conditional expectation onto the dyadic filtration of `[0,1]²` + Lévy's upward martingale
convergence theorem; the convergence of the filtration's `σ`-algebras to the Borel `σ`-algebra.)

Given a **cut-norm-Cauchy** sequence of graphons `W'` on `([0,1], Lebesgue)`, there is a sequence
`S` of graphons on the same carrier whose integrands are `L¹`-Cauchy (`CauchySeq (toLpFun (S n))`)
and which is `δ□`-close to `W'` in the sense `cutDist (W'ₙ) (Sₙ) → 0`.

Construction (Lovász, §9.2; classical): let `𝒢_k` be the `σ`-algebra of the `2^k × 2^k` dyadic
grid on `[0,1]²` and `Pₖ` the corresponding block-average (conditional-expectation) projection.
For a slowly growing schedule `k(n) → ∞`, set `Sₙ := graphonOf (E[W'ₙ | 𝒢_{k(n)}])`.  Then:
* **`L¹`-Cauchy:** for fixed `k`, `‖PₖW'ₙ − PₖW'ₘ‖₁ ≤ cutNorm(W'ₙ − W'ₘ)` because dyadic-block
  indicators are cut-norm test functions (`|∫_{S×T}(W'ₙ−W'ₘ)| ≤ cutNorm`), so `PₖW'ₙ` is `L¹`-Cauchy
  in `n`; the `(k(n))` martingale tail is uniformly small, giving a diagonal `L¹`-Cauchy `Sₙ`;
* **`δ□`-close:** `cutDist(W'ₙ, Sₙ) ≤ cutNorm(W'ₙ − E[W'ₙ|𝒢_{k(n)}]) → 0` by Lévy's theorem
  (`MeasureTheory.tendsto_eLpNorm_condExp`) since `⋃_k 𝒢_k` generates the Borel `σ`-algebra of
  `[0,1]²`.

**TRUE — counterexample check.**  The `L¹`-Cauchy sequence here is the block-average sequence `S`,
NOT the reps `W'`.  Block averages are honestly free to converge in `L¹` (e.g. for quasirandom
inputs the dyadic block-averages flatten toward the constant `½`, which is genuinely `L¹`-Cauchy),
so the quasirandom counterexample that kills `L¹`-Cauchy *reps* does not apply.  The two conclusions
are the standard content of bounded-martingale `L¹`-convergence.  To be discharged later. -/
axiom dyadic_l1Cauchy_approx_unit (W' : ℕ → Graphon ℝ unitMeasure)
    (hcn : CutNormCauchy W') :
    ∃ S : ℕ → Graphon ℝ unitMeasure,
      CauchySeq (fun n => toLpFun (S n)) ∧
        Tendsto (fun n => cutDist (W' n) (S n)) atTop (𝓝 0)

/-- A fast `δ□`-Cauchy sequence of graphons on `([0,1], Lebesgue)` has a `δ□`-limit class.

This BUILDS the limit from the two TRUE axioms: cut-norm alignment gives `δ□`-equivalent
cut-norm-Cauchy reps `W'`; the dyadic step gives an `L¹`-Cauchy `δ□`-approximant `S`; the
carrier-internal `Lp`-limit gives a limit graphon `Wlim` with `cutDist (Sₙ) Wlim → 0`; the cut
metric's triangle inequality then yields `cutDist (Wₙ) Wlim → 0`, and the `δ□`-classes match. -/
theorem exists_tendsto_of_fast_unit (W : ℕ → Graphon ℝ unitMeasure)
    (hfast : ∀ k, cutDist (W k) (W (k + 1)) ≤ (1 / 2 : ℝ) ^ k) :
    ∃ z : GraphonSpace ℝ unitMeasure,
      Tendsto (fun n => (Quotient.mk (graphonSetoid ℝ unitMeasure) (W n) : GraphonSpace ℝ unitMeasure))
        atTop (nhds (X := GraphonSpace ℝ unitMeasure) z) := by
  -- AXIOM 1: cut-norm-Cauchy `δ□`-equivalent reps.
  obtain ⟨W', hW'eq, hW'cn⟩ := cutNorm_alignment_unit W hfast
  -- AXIOM 2: an `L¹`-Cauchy `δ□`-approximant `S`.
  obtain ⟨S, hScauchy, hSclose⟩ := dyadic_l1Cauchy_approx_unit W' hW'cn
  -- BUILD: carrier-internal `Lp`-limit graphon of the `L¹`-Cauchy `S`.
  obtain ⟨Wlim, hWlim⟩ := exists_graphon_cutDist_tendsto_of_lpCauchy S hScauchy
  -- BUILD: `cutDist (W'ₙ) Wlim → 0` by triangle: `≤ cutDist (W'ₙ) (Sₙ) + cutDist (Sₙ) Wlim`.
  have hW'lim : Tendsto (fun n => cutDist (W' n) Wlim) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => cutDist (W' n) (S n) + cutDist (S n) Wlim) atTop (𝓝 0) := by
      simpa using hSclose.add hWlim
    refine squeeze_zero (fun n => cutDist_nonneg _ _) (fun n => ?_) hsum
    exact cutDist_triangle (W' n) (S n) Wlim
  -- BUILD: the limit class is `⟦Wlim⟧`; the `Wₙ` converge to it in `GraphonSpace`.
  refine ⟨(Quotient.mk (graphonSetoid ℝ unitMeasure) Wlim : GraphonSpace ℝ unitMeasure), ?_⟩
  -- `⟦Wₙ⟧ = ⟦W'ₙ⟧` since `cutDist (Wₙ) (W'ₙ) = 0`.
  have hclass : ∀ n, (Quotient.mk (graphonSetoid ℝ unitMeasure) (W n) : GraphonSpace ℝ unitMeasure)
      = Quotient.mk (graphonSetoid ℝ unitMeasure) (W' n) :=
    fun n => Quotient.sound (show GraphonEquiv (W n) (W' n) from hW'eq n)
  refine (tendsto_iff_dist_tendsto_zero (α := GraphonSpace ℝ unitMeasure) (β := ℕ)
    (f := fun n => (Quotient.mk (graphonSetoid ℝ unitMeasure) (W n) : GraphonSpace ℝ unitMeasure))
    (x := atTop)
    (a := (Quotient.mk (graphonSetoid ℝ unitMeasure) Wlim : GraphonSpace ℝ unitMeasure))).mpr ?_
  refine hW'lim.congr (fun n => ?_)
  rw [hclass n]
  exact (GraphonSpace.dist_mk (W' n) Wlim).symm

end CompletenessUnit

/-- **Completeness of the concrete graphon space `GraphonSpace ℝ unitMeasure`.**  Every `δ□`-Cauchy
sequence converges, via the carrier-internal `Lp`-limit construction on `[0,1]²`. -/
instance instCompleteSpaceGraphonSpaceUnit : CompleteSpace (GraphonSpace ℝ unitMeasure) := by
  refine Metric.complete_of_cauchySeq_tendsto fun x hx => ?_
  -- fast subsequence
  obtain ⟨φ, hφmono, hφ⟩ :=
    Metric.exists_subseq_bounded_of_cauchySeq x hx (fun n => (1 / 2 : ℝ) ^ n)
      (fun n => by positivity)
  set W : ℕ → Graphon ℝ unitMeasure := fun n => (x (φ n)).out with hW
  have hWout : ∀ n, Quotient.mk (graphonSetoid ℝ unitMeasure) (W n) = x (φ n) :=
    fun n => Quotient.out_eq _
  have hfast : ∀ k, cutDist (W k) (W (k + 1)) ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    have hd : dist (x (φ (k + 1))) (x (φ k)) < (1 / 2 : ℝ) ^ k :=
      hφ k (φ (k + 1)) (hφmono (Nat.lt_succ_self k)).le
    have hdist : dist (x (φ k)) (x (φ (k + 1))) = cutDist (W k) (W (k + 1)) := by
      rw [← hWout k, ← hWout (k + 1)]; show GraphonSpace.dist _ _ = _; rw [GraphonSpace.dist_mk]
    rw [dist_comm] at hd; rw [hdist] at hd; exact hd.le
  obtain ⟨z, hz⟩ := CompletenessUnit.exists_tendsto_of_fast_unit W hfast
  refine ⟨z, ?_⟩
  have hxφ : Tendsto (fun n => x (φ n)) atTop (𝓝 z) := hz.congr (fun n => hWout n)
  exact tendsto_nhds_of_cauchySeq_of_subseq hx hφmono.tendsto_atTop hxφ

/-- **Compactness of the concrete graphon space.**  Instantiate the general total-boundedness result
`graphonSpace_totallyBounded` at `unitMeasure` together with the completeness instance. -/
instance instCompactSpaceGraphonSpaceUnit : CompactSpace (GraphonSpace ℝ unitMeasure) := by
  rw [← isCompact_univ_iff]
  exact graphonSpace_totallyBounded.isCompact_of_isComplete complete_univ

end Graphons
