/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

The **W-random graph model** `𝔾(n, W)`, coin layer (EXTENDED_VALIDATION_PLAN.md WS3, pass 1).
Vertex positions `x : Fin n → Ω` are given; conditionally on `x`, each unordered pair `{i,j}`
is an edge independently with probability `W (x i) (x j)`. The coin space is
`CoinSpace n = Sym2 (Fin n) → Bool`, equipped with the HONEST product measure
`coinMeasure W x = Measure.pi (Bernoulli (edgeProb W x e))`. Independence of the edge
indicators (`integral_coin_prod`) is PROVED from `Measure.pi` via Fubini
(`integral_fintype_prod_eq_prod`), not built into a definition.

The conditional first sampling identity (`integral_coin_homDensity`) computes the expected
homomorphism density of `F` in `𝔾(n, W)` given `x` as an annealed sum over maps `ψ : V → Fin n`;
the inner product runs over the IMAGE of the edge set under `Sym2.map ψ` (duplicate target
pairs collapse — they share a single coin), which is what makes non-injective terms differ
from a plain `∏ W` product.
-/
import Graphons.Core.StepDensity

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Edge probabilities -/

/-- Probability that the unordered pair `e` is an edge of `𝔾(n,W)`, given positions `x`:
    `W (x i) (x j)` off the diagonal, `0` on it. Well-defined on `Sym2` because the diagonal
    test is symmetric and `W` is symmetric. -/
noncomputable def edgeProb (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω) (e : Sym2 (Fin n)) : ℝ :=
  Sym2.lift ⟨fun i j => if i = j then 0 else W.toFun (x i) (x j), fun i j => by
    rcases eq_or_ne i j with h | h
    · simp [h]
    · simp [h, h.symm, W.symm' (x i) (x j)]⟩ e

@[simp] theorem edgeProb_mk (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω) (i j : Fin n) :
    edgeProb W x s(i, j) = if i = j then 0 else W.toFun (x i) (x j) := rfl

theorem edgeProb_nonneg (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω) (e : Sym2 (Fin n)) :
    0 ≤ edgeProb W x e := by
  induction e with
  | _ i j =>
    rw [edgeProb_mk]
    split
    · exact le_refl 0
    · exact W.nonneg' (x i) (x j)

theorem edgeProb_le_one (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω) (e : Sym2 (Fin n)) :
    edgeProb W x e ≤ 1 := by
  induction e with
  | _ i j =>
    rw [edgeProb_mk]
    split
    · exact zero_le_one
    · exact W.le_one' (x i) (x j)

/-! ### The coin space and the product-Bernoulli coin measure -/

/-- The coin space: one Boolean per unordered pair. -/
abbrev CoinSpace (n : ℕ) := Sym2 (Fin n) → Bool

/-- The product-Bernoulli coin measure given positions `x`: an honest `Measure.pi` of
    Bernoulli coins, one per unordered pair, with success probability `edgeProb W x e`. -/
noncomputable def coinMeasure (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω) :
    Measure (CoinSpace n) :=
  Measure.pi fun e => (PMF.bernoulli (Real.toNNReal (edgeProb W x e))
    (Real.toNNReal_le_one.mpr (edgeProb_le_one W x e))).toMeasure

instance (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω) :
    IsProbabilityMeasure (coinMeasure W x) := by
  rw [coinMeasure]; infer_instance

/-! ### The realized graph -/

/-- The realized graph of a coin outcome: `i ~ j` iff `i ≠ j` and the coin of `{i,j}` is heads. -/
def coinGraph {n : ℕ} (ω : CoinSpace n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ω s(i, j) = true
  symm := fun i j h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless := ⟨fun i h => h.1 rfl⟩

@[simp] theorem coinGraph_adj {n : ℕ} (ω : CoinSpace n) (i j : Fin n) :
    (coinGraph ω).Adj i j ↔ i ≠ j ∧ ω s(i, j) = true := Iff.rfl

instance {n : ℕ} (ω : CoinSpace n) : DecidableRel (coinGraph ω).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ω s(i, j) = true))

/-! ### Independence, proved from the product measure -/

/-- Integral of the heads indicator against a single Bernoulli coin. -/
private theorem integral_bernoulli_indicator {q : ℝ} (hq : 0 ≤ q) (h : Real.toNNReal q ≤ 1) :
    ∫ b, (if b then (1 : ℝ) else 0) ∂((PMF.bernoulli (Real.toNNReal q) h).toMeasure) = q := by
  rw [PMF.integral_eq_sum]
  simp [smul_eq_mul, Real.coe_toNNReal q hq]

/-- Fubini for the coin measure: an integral of a product over all coordinates factorizes. -/
private theorem integral_coin_pi (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω)
    (f : Sym2 (Fin n) → Bool → ℝ) :
    ∫ ω, ∏ e, f e (ω e) ∂(coinMeasure W x)
      = ∏ e, ∫ b, f e b ∂((PMF.bernoulli (Real.toNNReal (edgeProb W x e))
          (Real.toNNReal_le_one.mpr (edgeProb_le_one W x e))).toMeasure) := by
  rw [coinMeasure]
  exact MeasureTheory.integral_fintype_prod_eq_prod f

/-- **Independence, proved**: the probability that all pairs in `S` are simultaneously edges
    is the product of the individual edge probabilities. -/
theorem integral_coin_prod (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω)
    (S : Finset (Sym2 (Fin n))) :
    ∫ ω, (∏ e ∈ S, (if ω e then (1 : ℝ) else 0)) ∂(coinMeasure W x)
      = ∏ e ∈ S, edgeProb W x e := by
  have key : ∀ ω : CoinSpace n,
      (∏ e ∈ S, (if ω e then (1 : ℝ) else 0))
        = ∏ e, (if e ∈ S then (if ω e then (1 : ℝ) else 0) else 1) :=
    fun ω => (Fintype.prod_ite_mem S fun e => if ω e then (1 : ℝ) else 0).symm
  simp_rw [key]
  have hpi := integral_coin_pi W x fun e b => if e ∈ S then (if b then (1 : ℝ) else 0) else 1
  rw [hpi, ← Fintype.prod_ite_mem S fun e => edgeProb W x e]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases he : e ∈ S
  · simp only [if_pos he]
    exact integral_bernoulli_indicator (edgeProb_nonneg W x e) _
  · simp only [if_neg he]
    rw [integral_const, probReal_univ, one_smul]

/-! ### The conditional first sampling identity -/

/-- The edge indicator of a coin outcome on unordered pairs: `0` on the diagonal regardless
    of the coin, the heads indicator off it. -/
private def coinInd {n : ℕ} (ω : CoinSpace n) (e : Sym2 (Fin n)) : ℝ :=
  if e.IsDiag then 0 else if ω e then 1 else 0

private theorem coinInd_eq_mul {n : ℕ} (ω : CoinSpace n) (e : Sym2 (Fin n)) :
    coinInd ω e = (if e.IsDiag then 0 else 1) * (if ω e then (1 : ℝ) else 0) := by
  by_cases hd : e.IsDiag <;> simp [coinInd, hd]

private theorem coinInd_zero_or_one {n : ℕ} (ω : CoinSpace n) (e : Sym2 (Fin n)) :
    coinInd ω e = 0 ∨ coinInd ω e = 1 := by
  unfold coinInd
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- Per-edge value: the step graphon of the realized graph, evaluated along `ψ`, is the coin
    indicator of the image pair. -/
private theorem edgeVal_step_coinGraph {V : Type*} {n : ℕ} [NeZero n] (ω : CoinSpace n)
    (ψ : V → Fin n) (e : Sym2 V) :
    edgeVal (Graphon.step (coinGraph ω)) ψ e = coinInd ω (Sym2.map ψ e) := by
  induction e with
  | _ a b =>
    rw [Sym2.map_mk]
    show (if (coinGraph ω).Adj (ψ a) (ψ b) then (1 : ℝ) else 0)
      = if Sym2.IsDiag s(ψ a, ψ b) then 0 else if ω s(ψ a, ψ b) then 1 else 0
    rcases eq_or_ne (ψ a) (ψ b) with h | h
    · simp [h, Sym2.mk_isDiag_iff]
    · cases hω : ω s(ψ a, ψ b) <;>
        simp [coinGraph_adj, h, hω, Sym2.mk_isDiag_iff]

/-- Collapse the product over the edges of `F` to a product over the IMAGE of the edge set:
    duplicate target pairs share a coin, and the values are `0`/`1`, so powers collapse. -/
private theorem prod_edgeVal_step_coinGraph {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {n : ℕ} [NeZero n]
    (ω : CoinSpace n) (ψ : V → Fin n) :
    (∏ e ∈ F.edgeFinset, edgeVal (Graphon.step (coinGraph ω)) ψ e)
      = ∏ e ∈ F.edgeFinset.image (Sym2.map ψ), coinInd ω e := by
  calc (∏ e ∈ F.edgeFinset, edgeVal (Graphon.step (coinGraph ω)) ψ e)
      = ∏ e ∈ F.edgeFinset, coinInd ω (Sym2.map ψ e) :=
        Finset.prod_congr rfl fun e _ => edgeVal_step_coinGraph ω ψ e
    _ = ∏ e' ∈ F.edgeFinset.image (Sym2.map ψ),
          coinInd ω e' ^ (F.edgeFinset.filter fun a => Sym2.map ψ a = e').card :=
        Finset.prod_comp (coinInd ω) (Sym2.map ψ)
    _ = ∏ e' ∈ F.edgeFinset.image (Sym2.map ψ), coinInd ω e' := by
        refine Finset.prod_congr rfl fun e' he' => ?_
        have hne : (F.edgeFinset.filter fun a => Sym2.map ψ a = e').Nonempty := by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he'
          exact ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
        rcases coinInd_zero_or_one ω e' with h | h <;> rw [h]
        · exact zero_pow (Finset.card_pos.mpr hne).ne'
        · exact one_pow _

/-- The deterministic diagonal indicator is absorbed by `edgeProb` (which already vanishes on
    the diagonal). -/
private theorem diag_indicator_mul_edgeProb (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω)
    (e : Sym2 (Fin n)) :
    (if e.IsDiag then (0 : ℝ) else 1) * edgeProb W x e = edgeProb W x e := by
  induction e with
  | _ i j => rcases eq_or_ne i j with h | h <;> simp [Sym2.mk_isDiag_iff, h]

/-- Expected product of coin indicators over any finite set of pairs (diagonal pairs allowed:
    both sides then vanish). -/
private theorem integral_coinInd_prod (W : Graphon Ω μ) {n : ℕ} (x : Fin n → Ω)
    (T : Finset (Sym2 (Fin n))) :
    ∫ ω, (∏ e ∈ T, coinInd ω e) ∂(coinMeasure W x) = ∏ e ∈ T, edgeProb W x e := by
  have key : ∀ ω : CoinSpace n,
      (∏ e ∈ T, coinInd ω e)
        = (∏ e ∈ T, (if e.IsDiag then (0 : ℝ) else 1))
            * ∏ e ∈ T, (if ω e then (1 : ℝ) else 0) := by
    intro ω
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun e _ => coinInd_eq_mul ω e
  simp_rw [key]
  rw [integral_const_mul, integral_coin_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => diag_indicator_mul_edgeProb W x e

/-- **Conditional first sampling identity**: the expected hom density of `F` in `𝔾(n,W)`
    given positions `x`, as an explicit annealed sum. The inner product is over the IMAGE
    of the edge set (duplicate target pairs collapse — same coin!), which is what makes the
    non-injective terms differ from `∏ W`. -/
theorem integral_coin_homDensity {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ} [NeZero n]
    (x : Fin n → Ω) :
    ∫ ω, homDensity F (Graphon.step (coinGraph ω)) ∂(coinMeasure W x)
      = (∑ ψ : V → Fin n, ∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
          / (n : ℝ) ^ (Fintype.card V) := by
  have hpt : ∀ ω : CoinSpace n,
      homDensity F (Graphon.step (coinGraph ω))
        = (∑ ψ : V → Fin n, ∏ e ∈ F.edgeFinset.image (Sym2.map ψ), coinInd ω e)
            / (n : ℝ) ^ (Fintype.card V) := by
    intro ω
    rw [homDensity_step]
    congr 1
    exact Finset.sum_congr rfl fun ψ _ => prod_edgeVal_step_coinGraph F ω ψ
  simp_rw [hpt]
  rw [integral_div, integral_finsetSum _ fun ψ _ => Integrable.of_finite]
  congr 1
  exact Finset.sum_congr rfl fun ψ _ => integral_coinInd_prod W x _

end Graphons
