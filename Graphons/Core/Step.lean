/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

Step graphons: the graphon associated to a finite simple graph `G : SimpleGraph (Fin n)`,
carried over `Fin n` with the uniform probability measure. The adjacency `[0,1]`-indicator
`fun a b => if G.Adj a b then 1 else 0` is a graphon. (Only the definition + validity here;
the homomorphism-density EQUALITY to the finite density is deferred.)
-/
import Graphons.Core.Basic

open MeasureTheory

namespace Graphons

/-- The **uniform probability measure** on `Fin n` (`n ≠ 0`). -/
noncomputable def unifFin (n : ℕ) [NeZero n] : Measure (Fin n) :=
  (PMF.uniformOfFintype (Fin n)).toMeasure

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (unifFin n) := by
  rw [unifFin]; infer_instance

namespace Graphon

/-- The **step graphon** associated to a finite simple graph `G : SimpleGraph (Fin n)`:
    the `[0,1]`-valued adjacency indicator over `(Fin n, unifFin n)`. -/
noncomputable def step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [NeZero n] :
    Graphon (Fin n) (unifFin n) :=
  mk' (fun a b => if G.Adj a b then (1 : ℝ) else 0)
    (fun a b => by simp [G.adj_comm])
    (by measurability)
    (fun a b => by dsimp only; split <;> norm_num)
    (fun a b => by dsimp only; split <;> norm_num)

@[simp] theorem step_apply {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [NeZero n]
    (a b : Fin n) : (Graphon.step G).toFun a b = if G.Adj a b then 1 else 0 := rfl

end Graphon

end Graphons
