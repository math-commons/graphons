/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG targets (random-fields roadmap, layer L9 — dense graph limits):
  C11303 "Cut distance δ□" induces a genuine metric on graphon space.
  Sources: Lovász, "Large Networks and Graph Limits" (2012).

**The cut metric on graphon space.** The cut distance `δ□` is nonnegative, symmetric, satisfies
the triangle inequality, and vanishes exactly on the equivalence `GraphonEquiv` used to build
`GraphonSpace Ω μ`. We show `δ□` is well-defined on the quotient (`cutDist_congr`), lift it to a
distance `GraphonSpace.dist`, and assemble the `MetricSpace (GraphonSpace Ω μ)` instance — the
topological foundation for compactness/completeness of graphon space.
-/
import Graphons.Space.GraphonSpace
import Graphons.CutMetric.Gluing

open MeasureTheory

namespace Graphons

/-! ### Well-definedness of `cutDist` on the quotient

All carriers here are the *same* standard Borel `(Ω, μ)`. If `GraphonEquiv U U'` and
`GraphonEquiv W W'` (i.e. `δ□(U,U') = 0` and `δ□(W,W') = 0`), then `δ□(U,W) = δ□(U',W')`: two
applications of the triangle inequality bound `δ□(U,W)` by `δ□(U,U') + δ□(U',W') + δ□(W',W) =
δ□(U',W')`, and symmetrically. -/

section Congr

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [StandardBorelSpace Ω]

/-- `cutDist` respects `GraphonEquiv` in both arguments (same carrier `(Ω, μ)`): equivalent inputs
give equal cut distances. This is the well-definedness needed to lift `δ□` to `GraphonSpace`. -/
theorem cutDist_congr {U U' W W' : Graphon Ω μ}
    (hU : GraphonEquiv U U') (hW : GraphonEquiv W W') :
    cutDist U W = cutDist U' W' := by
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  rw [GraphonEquiv] at hU hW
  -- `δ□(U,W) ≤ δ□(U',W')`: route U → U' → W' → W.
  have h₁ : cutDist U W ≤ cutDist U' W' := by
    calc cutDist U W
        ≤ cutDist U U' + cutDist U' W := cutDist_triangle U U' W
      _ = cutDist U' W := by rw [hU, zero_add]
      _ ≤ cutDist U' W' + cutDist W' W := cutDist_triangle U' W' W
      _ = cutDist U' W' := by rw [cutDist_comm W' W, hW, add_zero]
  -- `δ□(U',W') ≤ δ□(U,W)`: the symmetric route, using `GraphonEquiv` is symmetric.
  have hU' : cutDist U' U = 0 := by rw [cutDist_comm]; exact hU
  have hW' : cutDist W' W = 0 := by rw [cutDist_comm]; exact hW
  have h₂ : cutDist U' W' ≤ cutDist U W := by
    calc cutDist U' W'
        ≤ cutDist U' U + cutDist U W' := cutDist_triangle U' U W'
      _ = cutDist U W' := by rw [hU', zero_add]
      _ ≤ cutDist U W + cutDist W W' := cutDist_triangle U W W'
      _ = cutDist U W := by rw [cutDist_comm W W', hW', add_zero]
  exact le_antisymm h₁ h₂

end Congr

/-! ### The lifted distance -/

section Dist

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [StandardBorelSpace Ω]

/-- The cut distance lifted to graphon space, via `Quotient.liftOn₂` and well-definedness
`cutDist_congr`. -/
noncomputable def GraphonSpace.dist (x y : GraphonSpace Ω μ) : ℝ :=
  Quotient.liftOn₂ x y (fun U W => cutDist U W) (fun _ _ _ _ hU hW => cutDist_congr hU hW)

/-- On representatives, `GraphonSpace.dist` is just `cutDist`. -/
@[simp]
theorem GraphonSpace.dist_mk (U W : Graphon Ω μ) :
    GraphonSpace.dist (Quotient.mk (graphonSetoid Ω μ) U) (Quotient.mk (graphonSetoid Ω μ) W)
      = cutDist U W :=
  rfl

end Dist

/-! ### The metric space structure

`GraphonSpace.dist` inherits nonnegativity, reflexivity, symmetry and the triangle inequality from
`cutDist`, and separates points: `dist x y = 0` means the representatives are `GraphonEquiv`, i.e.
related by the setoid, so `x = y` by `Quotient.sound`. We provide the four `dist` laws and the
separation field; the `edist`/`uniformity`/`bornology` fields take their auto-param defaults. -/

section Metric

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [StandardBorelSpace Ω]

noncomputable instance : MetricSpace (GraphonSpace Ω μ) where
  dist := GraphonSpace.dist
  dist_self x := by
    induction x using Quotient.inductionOn with
    | _ U => exact cutDist_self_eq_zero U
  dist_comm x y := by
    induction x using Quotient.inductionOn with
    | _ U =>
      induction y using Quotient.inductionOn with
      | _ W => exact cutDist_comm U W
  dist_triangle x y z := by
    haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
    induction x using Quotient.inductionOn with
    | _ U =>
      induction y using Quotient.inductionOn with
      | _ W =>
        induction z using Quotient.inductionOn with
        | _ V => exact cutDist_triangle U W V
  eq_of_dist_eq_zero {x y} h := by
    induction x using Quotient.inductionOn with
    | _ U =>
      induction y using Quotient.inductionOn with
      | _ W =>
        -- `h : GraphonSpace.dist ⟦U⟧ ⟦W⟧ = 0`, i.e. `cutDist U W = 0`, i.e. `GraphonEquiv U W`.
        exact Quotient.sound (show GraphonEquiv U W from h)

end Metric

end Graphons
