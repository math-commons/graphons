/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md M1 — **executable differential tests**.

Concrete numeric identities for `homDensity`, pinned against values computed by the
INDEPENDENT brute-force reference script `scripts/hom_density_reference.py` (run it to
re-derive every expected value below). These catch encoding bugs (vertex-ordering, `Sym2`
lifts, normalization) that proofs about an abstract `W` never touch.

Reference values (from `scripts/hom_density_reference.py`):
  * t(K₂, const p)    = p          (1 edge)
  * t(P₃, const p)    = p²         (2 edges — exercises `cherry`)
  * t(K₃, const p)    = p³         (3 edges)
  * t(K₂, step K₄)    = 12/16 = 3/4   (12 of the 16 maps `Fin 2 → Fin 4` hit an edge)
  * t(K₃, step C₅)    = 0             (C₅ is triangle-free)
-/
import Graphons.Core.StepDensity
import Graphons.Extremal.Goodman
import Graphons.Extremal.Sidorenko
import Graphons.Extremal.Mantel

open MeasureTheory

namespace Graphons.Tests

open Graphons

/-! ### Erdős–Rényi numerics: `t(F, const p) = p^{e(F)}` at concrete `p`, `F` -/

/-- `t(K₂, const ½) = ½` — edge count 1. -/
example : homDensity (⊤ : SimpleGraph (Fin 2))
    (Graphon.const (μ := unitMeasure) (1/2) (by norm_num)) = 1/2 := by
  rw [homDensity_const, show (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1 from by decide]
  norm_num

/-- `t(P₃, const ½) = ¼` — the `cherry` has exactly 2 edges (pins the `cherry` encoding). -/
example : homDensity cherry
    (Graphon.const (μ := unitMeasure) (1/2) (by norm_num)) = 1/4 := by
  rw [homDensity_const]
  norm_num [show cherry.edgeFinset.card = 2 from by decide]

/-- `t(K₃, const ½) = ⅛` — edge count 3. -/
example : homDensity (⊤ : SimpleGraph (Fin 3))
    (Graphon.const (μ := unitMeasure) (1/2) (by norm_num)) = 1/8 := by
  rw [homDensity_const, show (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 from by decide]
  norm_num

/-! ### Step-graphon numerics: the graphon side equals the finite count -/

/-- `t(K₂, step K₄) = 3/4`: of the `16` maps `Fin 2 → Fin 4`, exactly `12` land on an edge
    of `K₄` (reference script: `4·3 = 12` ordered adjacent pairs). -/
example :
    homDensity (⊤ : SimpleGraph (Fin 2)) (Graphon.step (⊤ : SimpleGraph (Fin 4))) = 3/4 := by
  rw [homDensity_step]
  have hedge : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
  have hcard : ((Finset.univ : Finset (Fin 2 → Fin 4)).filter
      fun φ => (⊤ : SimpleGraph (Fin 4)).Adj (φ 0) (φ 1)).card = 12 := by decide
  simp only [hedge, Finset.prod_singleton, edgeVal, Sym2.lift_mk, Graphon.step_apply]
  rw [Finset.sum_boole, hcard, Fintype.card_fin]
  norm_num

/-- `t(K₃, step C₅) = 0`: the 5-cycle is triangle-free, so every map `Fin 3 → Fin 5` kills
    at least one edge factor. -/
example :
    homDensity (⊤ : SimpleGraph (Fin 3)) (Graphon.step (SimpleGraph.cycleGraph 5)) = 0 := by
  rw [homDensity_step]
  have htri : ∀ a b c : Fin 5, ¬((SimpleGraph.cycleGraph 5).Adj a b
      ∧ (SimpleGraph.cycleGraph 5).Adj a c ∧ (SimpleGraph.cycleGraph 5).Adj b c) := by decide
  have hzero : ∀ φ : Fin 3 → Fin 5,
      ∏ e ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset,
        edgeVal (Graphon.step (SimpleGraph.cycleGraph 5)) φ e = 0 := by
    intro φ
    have hedge : (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
      decide
    rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    simp only [edgeVal, Sym2.lift_mk, Graphon.step_apply]
    by_cases h1 : (SimpleGraph.cycleGraph 5).Adj (φ 0) (φ 1)
    · by_cases h2 : (SimpleGraph.cycleGraph 5).Adj (φ 0) (φ 2)
      · have h3 : ¬(SimpleGraph.cycleGraph 5).Adj (φ 1) (φ 2) :=
          fun h3 => htri (φ 0) (φ 1) (φ 2) ⟨h1, h2, h3⟩
        simp [h1, h2, h3]
      · simp [h2]
    · simp [h1]
  simp only [hzero, Finset.sum_const_zero, zero_div]

/-! ### Goodman statement-orientation checks (D2 anchors) -/

/-- Goodman at `W = const p` reads `2p² − p ≤ p³`; at `p = 9/10` this is `0.72 ≤ 0.729` —
    a NUMERICALLY TIGHT instance (gap `0.009`), so a sign/orientation slip in the statement
    would flip it. Checked here through the actual `goodman` theorem. -/
example :
    2 * (homDensity (⊤ : SimpleGraph (Fin 2))
        (Graphon.const (μ := unitMeasure) (9/10) (by norm_num))) ^ 2
      - homDensity (⊤ : SimpleGraph (Fin 2))
          (Graphon.const (μ := unitMeasure) (9/10) (by norm_num))
    ≤ homDensity (⊤ : SimpleGraph (Fin 3))
        (Graphon.const (μ := unitMeasure) (9/10) (by norm_num)) :=
  goodman _

/-- The same instance with both sides evaluated numerically (independent of `goodman`):
    LHS `= 2·(81/100)/... = 18/25`, RHS `= 729/1000`. -/
example :
    2 * ((9:ℝ)/10) ^ 2 - 9/10 ≤ ((9:ℝ)/10) ^ 3 := by norm_num

/-- And the RHS pin: `t(K₃, const (9/10)) = 729/1000`. -/
example : homDensity (⊤ : SimpleGraph (Fin 3))
    (Graphon.const (μ := unitMeasure) (9/10) (by norm_num)) = 729/1000 := by
  rw [homDensity_const, show (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 from by decide]
  norm_num

/-- Cherry bound D1 at the step graphon of `K₄` is consistent:
    `t(K₂, step K₄)² = 9/16 ≤ t(P₃, step K₄)` (the theorem applies at any graphon). -/
example :
    (homDensity (⊤ : SimpleGraph (Fin 2)) (Graphon.step (⊤ : SimpleGraph (Fin 4)))) ^ 2
      ≤ homDensity cherry (Graphon.step (⊤ : SimpleGraph (Fin 4))) :=
  homDensity_cherry_ge _

/-! ### Sidorenko-C₄ checks (D3 anchors) -/

/-- `t(C₄, const ½) = 1/16` — `cycleGraph 4` has exactly 4 edges (pins the C₄ encoding). -/
example : homDensity (SimpleGraph.cycleGraph 4)
    (Graphon.const (μ := unitMeasure) (1/2) (by norm_num)) = 1/16 := by
  rw [homDensity_const, show (SimpleGraph.cycleGraph 4).edgeFinset.card = 4 from by decide]
  norm_num

/-- Mantel at `step C₅`: the 5-cycle is triangle-free (`t(K₃, step C₅) = 0`, proved above),
    so `mantel` applies and bounds its edge density by `1/2` (true value `2/5`, reference
    script) — a consistency check through the actual D4 theorem. -/
example :
    homDensity (⊤ : SimpleGraph (Fin 2)) (Graphon.step (SimpleGraph.cycleGraph 5)) ≤ 1/2 := by
  refine mantel _ ?_
  rw [homDensity_step]
  have htri : ∀ a b c : Fin 5, ¬((SimpleGraph.cycleGraph 5).Adj a b
      ∧ (SimpleGraph.cycleGraph 5).Adj a c ∧ (SimpleGraph.cycleGraph 5).Adj b c) := by decide
  have hzero : ∀ φ : Fin 3 → Fin 5,
      ∏ e ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset,
        edgeVal (Graphon.step (SimpleGraph.cycleGraph 5)) φ e = 0 := by
    intro φ
    have hedge : (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
      decide
    rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    simp only [edgeVal, Sym2.lift_mk, Graphon.step_apply]
    by_cases h1 : (SimpleGraph.cycleGraph 5).Adj (φ 0) (φ 1)
    · by_cases h2 : (SimpleGraph.cycleGraph 5).Adj (φ 0) (φ 2)
      · have h3 : ¬(SimpleGraph.cycleGraph 5).Adj (φ 1) (φ 2) :=
          fun h3 => htri (φ 0) (φ 1) (φ 2) ⟨h1, h2, h3⟩
        simp [h1, h2, h3]
      · simp [h2]
    · simp [h1]
  simp only [hzero, Finset.sum_const_zero, zero_div]

/-- Sidorenko-C₄ at `step K₄` is a NUMERICALLY TIGHT instance (reference script:
    `t(K₂)⁴ = 81/256 ≤ t(C₄) = 84/256`, gap `3/256`) — checked through the actual theorem. -/
example :
    (homDensity (⊤ : SimpleGraph (Fin 2)) (Graphon.step (⊤ : SimpleGraph (Fin 4)))) ^ 4
      ≤ homDensity (SimpleGraph.cycleGraph 4) (Graphon.step (⊤ : SimpleGraph (Fin 4))) :=
  sidorenko_C4 _

end Graphons.Tests
