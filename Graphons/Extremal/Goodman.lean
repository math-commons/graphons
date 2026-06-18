/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier D, item D2 — **Goodman's bound** (Goodman 1959; Lovász,
"Large Networks and Graph Limits", §2.1 / Prop. 16.26 region description):

  t(K₃, W) ≥ 2·t(K₂, W)² − t(K₂, W).

The proof is the classical analytic one, fully elementary:
  1. pointwise, for `a,b,c ∈ [0,1]`: `a·b + a·c − a ≤ a·b·c`  (since `a(1−b)(1−c) ≥ 0`);
     applied with `a = W(x,y), b = W(x,z), c = W(y,z)` and integrated over `Ω³` this gives
     `t(K₃) ≥ t(P₃) + ∫∫∫ W(x,y)W(y,z) − t(K₂)`;
  2. both 2-edge terms are the cherry second moment `∫ deg²` (`integral_cherry_left`,
     `integral_cherry_mid` — the latter by a measure-preserving coordinate swap);
  3. `∫ deg² ≥ (∫ deg)² = t(K₂)²` (D1, `sq_integral_deg_le`).

Tier-D significance: a named extremal-graph-theory consequence that was never a design
target — it exercises `homDensity` along an axis the Tier A–C acceptance suite does not.
-/
import Graphons.Counting.Degree
import Graphons.AnchorChecks

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Measurability / integrability of the triple-space integrands -/

section TripleSpace

variable (W : Graphon Ω μ)

private lemma meas_a : Measurable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1) :=
  W.meas'.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

private lemma meas_b : Measurable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.2) :=
  W.meas'.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

private lemma meas_c : Measurable (fun p : Ω × Ω × Ω => W.toFun p.2.1 p.2.2) :=
  W.meas'.comp ((measurable_fst.comp measurable_snd).prodMk
    (measurable_snd.comp measurable_snd))

/-- Any product of (at most three) graphon slices on the triple space is integrable: it is
    measurable and bounded by `1`. -/
private lemma integrable_of_meas_le_one {f : Ω × Ω × Ω → ℝ} (hm : Measurable f)
    (h0 : ∀ p, 0 ≤ f p) (h1 : ∀ p, f p ≤ 1) :
    Integrable f (μ.prod (μ.prod μ)) :=
  SymmKernel.integrable_of_bdd hm (C := 1)
    (fun p => abs_le.2 ⟨by linarith [h0 p], h1 p⟩)

private lemma integrable_ab :
    Integrable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2)
      (μ.prod (μ.prod μ)) := by
  refine integrable_of_meas_le_one ((meas_a W).mul (meas_b W)) (fun p => ?_) (fun p => ?_)
  · exact mul_nonneg (W.nonneg' _ _) (W.nonneg' _ _)
  · exact mul_le_one₀ (W.le_one' _ _) (W.nonneg' _ _) (W.le_one' _ _)

private lemma integrable_ac :
    Integrable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.2.1 p.2.2)
      (μ.prod (μ.prod μ)) := by
  refine integrable_of_meas_le_one ((meas_a W).mul (meas_c W)) (fun p => ?_) (fun p => ?_)
  · exact mul_nonneg (W.nonneg' _ _) (W.nonneg' _ _)
  · exact mul_le_one₀ (W.le_one' _ _) (W.nonneg' _ _) (W.le_one' _ _)

private lemma integrable_a :
    Integrable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1) (μ.prod (μ.prod μ)) :=
  integrable_of_meas_le_one (meas_a W) (fun _ => W.nonneg' _ _) (fun _ => W.le_one' _ _)

private lemma integrable_abc :
    Integrable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2
      * W.toFun p.2.1 p.2.2) (μ.prod (μ.prod μ)) := by
  refine integrable_of_meas_le_one (((meas_a W).mul (meas_b W)).mul (meas_c W))
    (fun p => ?_) (fun p => ?_)
  · exact mul_nonneg (mul_nonneg (W.nonneg' _ _) (W.nonneg' _ _)) (W.nonneg' _ _)
  · exact mul_le_one₀
      (mul_le_one₀ (W.le_one' _ _) (W.nonneg' _ _) (W.le_one' _ _))
      (W.nonneg' _ _) (W.le_one' _ _)

end TripleSpace

/-! ### The mid-centered cherry: `∫∫∫ W(x,y)·W(y,z) = ∫ deg²` -/

/-- The 2-edge term sharing its center in the SECOND coordinate: `∫∫∫ W(x,y)W(y,z) = ∫ deg²`.
    Proved from `integral_cherry_left` by the measure-preserving coordinate permutation
    `(x,(y,z)) ↦ (y,(x,z))` plus symmetry of `W`. -/
theorem integral_cherry_mid (W : Graphon Ω μ) :
    ∫ p : Ω × Ω × Ω, W.toFun p.1 p.2.1 * W.toFun p.2.1 p.2.2 ∂(μ.prod (μ.prod μ))
      = ∫ x, (W.deg x) ^ 2 ∂μ := by
  -- the coordinate permutation `τ(x,(y,z)) = (y,(x,z))`
  set τ : (Ω × Ω × Ω) ≃ᵐ (Ω × Ω × Ω) :=
    (MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodComm : (Ω × Ω) ≃ᵐ (Ω × Ω)).prodCongr
        (MeasurableEquiv.refl Ω))).trans
      MeasurableEquiv.prodAssoc with hτ
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm :
      (Ω × Ω × Ω) ≃ᵐ ((Ω × Ω) × Ω)) (μ.prod (μ.prod μ)) ((μ.prod μ).prod μ) :=
    (measurePreserving_prodAssoc μ μ μ).symm _
  have h2 : MeasurePreserving
      (Prod.map (Prod.swap : Ω × Ω → Ω × Ω) (id : Ω → Ω))
      ((μ.prod μ).prod μ) ((μ.prod μ).prod μ) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id μ)
  have h3 : MeasurePreserving (MeasurableEquiv.prodAssoc : ((Ω × Ω) × Ω) ≃ᵐ (Ω × Ω × Ω))
      ((μ.prod μ).prod μ) (μ.prod (μ.prod μ)) :=
    measurePreserving_prodAssoc μ μ μ
  have hmpτ : MeasurePreserving τ (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) :=
    (h3.comp (h2.comp h1) : _)
  have key := hmpτ.integral_comp'
    (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.2.1 p.2.2)
  -- `τ p = (p.2.1, (p.1, p.2.2))`, so the composed integrand is `W(y,x)·W(x,z)`.
  have hτapp : ∀ p : Ω × Ω × Ω, τ p = (p.2.1, (p.1, p.2.2)) := fun p => rfl
  rw [← key]
  simp only [hτapp]
  -- symmetry turns `W(y,x)·W(x,z)` into the left-centered cherry integrand `W(x,y)·W(x,z)`
  have hsymm : ∀ p : Ω × Ω × Ω,
      W.toFun p.2.1 p.1 * W.toFun p.1 p.2.2 = W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2 := by
    intro p
    rw [W.symm' p.2.1 p.1]
  simp only [hsymm]
  exact integral_cherry_left W

/-! ### The 1-edge term: `∫∫∫ W(x,y) = t(K₂, W)` -/

/-- Marginalizing the unused third coordinate: `∫∫∫ W(x,y) = t(K₂, W)`. -/
theorem integral_edge_first (W : Graphon Ω μ) :
    ∫ p : Ω × Ω × Ω, W.toFun p.1 p.2.1 ∂(μ.prod (μ.prod μ))
      = homDensity (⊤ : SimpleGraph (Fin 2)) W := by
  rw [integral_prod _ (integrable_a W)]
  have hinner : ∀ x : Ω, (∫ q : Ω × Ω, W.toFun x q.1 ∂(μ.prod μ)) = W.deg x := by
    intro x
    rw [integral_fun_fst (f := W.toFun x)]
    simp [probReal_univ, Graphon.deg]
  simp only [hinner]
  exact integral_deg W

/-! ### D2 — Goodman's bound -/

/-- **Goodman's bound** (D2): `t(K₃, W) ≥ 2·t(K₂, W)² − t(K₂, W)`.

    Classical extremal consequence (Goodman 1959): the triangle density of a graphon is at
    least `2p² − p` where `p` is its edge density. Sanity anchor: for `W = const p` this reads
    `p³ ≥ 2p² − p`, i.e. `p(1−p)² ≥ 0`. -/
theorem goodman (W : Graphon Ω μ) :
    2 * (homDensity (⊤ : SimpleGraph (Fin 2)) W) ^ 2 - homDensity (⊤ : SimpleGraph (Fin 2)) W
      ≤ homDensity (⊤ : SimpleGraph (Fin 3)) W := by
  set p := homDensity (⊤ : SimpleGraph (Fin 2)) W with hp
  -- Step 1: `t(K₃) ≥ ∫(ab + ac − a)` pointwise (`a(1−b)(1−c) ≥ 0`), then split the integral.
  have hpoint : ∀ q : Ω × Ω × Ω,
      W.toFun q.1 q.2.1 * W.toFun q.1 q.2.2 + W.toFun q.1 q.2.1 * W.toFun q.2.1 q.2.2
        - W.toFun q.1 q.2.1
      ≤ W.toFun q.1 q.2.1 * W.toFun q.1 q.2.2 * W.toFun q.2.1 q.2.2 := by
    intro q
    nlinarith [mul_nonneg (mul_nonneg (W.nonneg' q.1 q.2.1)
        (sub_nonneg.2 (W.le_one' q.1 q.2.2))) (sub_nonneg.2 (W.le_one' q.2.1 q.2.2))]
  have hmono :
      ∫ q : Ω × Ω × Ω, (W.toFun q.1 q.2.1 * W.toFun q.1 q.2.2
          + W.toFun q.1 q.2.1 * W.toFun q.2.1 q.2.2 - W.toFun q.1 q.2.1) ∂(μ.prod (μ.prod μ))
        ≤ ∫ q : Ω × Ω × Ω, W.toFun q.1 q.2.1 * W.toFun q.1 q.2.2 * W.toFun q.2.1 q.2.2
            ∂(μ.prod (μ.prod μ)) :=
    integral_mono (((integrable_ab W).add (integrable_ac W)).sub (integrable_a W))
      (integrable_abc W) hpoint
  have hsplit :
      ∫ q : Ω × Ω × Ω, (W.toFun q.1 q.2.1 * W.toFun q.1 q.2.2
          + W.toFun q.1 q.2.1 * W.toFun q.2.1 q.2.2 - W.toFun q.1 q.2.1) ∂(μ.prod (μ.prod μ))
        = (∫ x, (W.deg x) ^ 2 ∂μ) + (∫ x, (W.deg x) ^ 2 ∂μ) - p := by
    have hab_ac : Integrable (fun q : Ω × Ω × Ω =>
        W.toFun q.1 q.2.1 * W.toFun q.1 q.2.2 + W.toFun q.1 q.2.1 * W.toFun q.2.1 q.2.2)
        (μ.prod (μ.prod μ)) := (integrable_ab W).add (integrable_ac W)
    rw [integral_sub hab_ac (integrable_a W),
      integral_add (integrable_ab W) (integrable_ac W),
      integral_cherry_left, integral_cherry_mid, integral_edge_first]
  -- Step 2: `∫ deg² ≥ (∫ deg)² = t(K₂)²` (D1).
  have hCS : p ^ 2 ≤ ∫ x, (W.deg x) ^ 2 ∂μ := by
    have h := sq_integral_deg_le W
    rwa [integral_deg, ← hp] at h
  -- Assemble.
  rw [homDensity_triangle]
  calc 2 * p ^ 2 - p
      ≤ (∫ x, (W.deg x) ^ 2 ∂μ) + (∫ x, (W.deg x) ^ 2 ∂μ) - p := by linarith
    _ = ∫ q : Ω × Ω × Ω, (W.toFun q.1 q.2.1 * W.toFun q.1 q.2.2
          + W.toFun q.1 q.2.1 * W.toFun q.2.1 q.2.2 - W.toFun q.1 q.2.1)
          ∂(μ.prod (μ.prod μ)) := hsplit.symm
    _ ≤ _ := hmono

end Graphons
