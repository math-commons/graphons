/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG targets (random-fields roadmap, layer L9 — dense graph limits):
  C11303 "Cut distance δ□" (induces the equivalence on graphon space),
  C12954/C13065 "Homomorphism density t(F,W)" (descends to the quotient).
  Sources: Lovász, "Large Networks and Graph Limits" (2012).

**Graphon space.** Now that the cut metric satisfies the triangle inequality
(`cutDist_triangle`), `GraphonEquiv` is a genuine equivalence relation. We package this as a
`Setoid` on the graphons over a fixed standard Borel carrier `(Ω, μ)` and form the quotient
`GraphonSpace Ω μ`. Homomorphism density, being a cut-distance invariant, descends to a
well-defined function on the quotient — the universal separating functional realizing the map
`GraphonSpace → [0,1]^{graphs}`.
-/
import Graphons.CutMetric.Gluing
import Graphons.Counting.CountingLemmaCutDist
import Graphons.Core.Properties

open MeasureTheory

namespace Graphons

/-! ### Transitivity of graphon equivalence

With the triangle inequality `cutDist_triangle` in hand, `GraphonEquiv` is transitive: if
`δ□(U, V) = 0` and `δ□(V, W) = 0`, then `δ□(U, W) ≤ δ□(U, V) + δ□(V, W) = 0`, and nonnegativity
forces equality. The triangle inequality needs `StandardBorelSpace` and `Nonempty` on all three
carriers; the latter follow from the probability measures. -/

section Trans

variable {Ω₁ Ω₂ Ω₃ : Type*}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃]
variable [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] [StandardBorelSpace Ω₃]

/-- `GraphonEquiv` is transitive (cross-carrier), via the cut-metric triangle inequality. -/
theorem graphonEquiv_trans {U : Graphon Ω₁ μ₁} {V : Graphon Ω₂ μ₂} {W : Graphon Ω₃ μ₃}
    (h₁ : GraphonEquiv U V) (h₂ : GraphonEquiv V W) : GraphonEquiv U W := by
  -- `Nonempty` carriers (needed by the triangle inequality) follow from the probability measures.
  haveI : Nonempty Ω₁ := nonempty_of_isProbabilityMeasure μ₁
  haveI : Nonempty Ω₂ := nonempty_of_isProbabilityMeasure μ₂
  haveI : Nonempty Ω₃ := nonempty_of_isProbabilityMeasure μ₃
  -- Triangle with middle point `V`: `cutDist U W ≤ cutDist U V + cutDist V W`.
  have htri : cutDist U W ≤ cutDist U V + cutDist V W := cutDist_triangle U V W
  rw [GraphonEquiv] at h₁ h₂ ⊢
  refine le_antisymm ?_ (cutDist_nonneg U W)
  calc cutDist U W ≤ cutDist U V + cutDist V W := htri
    _ = 0 := by rw [h₁, h₂, add_zero]

end Trans

/-! ### The setoid and the quotient

On a fixed standard Borel carrier `(Ω, μ)`, `GraphonEquiv` is reflexive, symmetric and transitive,
so it is a `Setoid`. Graphon space is the quotient. -/

section Quotient

variable (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [StandardBorelSpace Ω]

/-- The equivalence relation `δ□(·, ·) = 0` packaged as a `Setoid` on graphons over `(Ω, μ)`. -/
def graphonSetoid : Setoid (Graphon Ω μ) where
  r := GraphonEquiv
  iseqv := ⟨graphonEquiv_refl, graphonEquiv_symm, graphonEquiv_trans⟩

/-- **Graphon space**: the quotient of graphons over `(Ω, μ)` by cut-distance-zero equivalence. -/
def GraphonSpace : Type _ := Quotient (graphonSetoid Ω μ)

end Quotient

/-! ### Homomorphism density on graphon space

Because equivalent graphons have equal homomorphism densities
(`homDensity_eq_of_cutDist_eq_zero`), `t(F, ·)` descends to a well-defined function on graphon
space. The family `(t(F, ·))_F` over all finite simple graphs `F` is the universal separating
functional, i.e. the map `GraphonSpace Ω μ → [0,1]^{graphs}`. -/

section HomDensity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [StandardBorelSpace Ω]

/-- Homomorphism density `t(F, ·)` descends to graphon space. -/
noncomputable def GraphonSpace.homDensity {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (x : GraphonSpace Ω μ) : ℝ :=
  Quotient.liftOn x (fun W => _root_.Graphons.homDensity F W)
    (fun U W h => homDensity_eq_of_cutDist_eq_zero F U W h)

/-- On a representative, `GraphonSpace.homDensity` agrees with `homDensity`. -/
@[simp]
theorem GraphonSpace.homDensity_mk {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (W : Graphon Ω μ) :
    GraphonSpace.homDensity F (Quotient.mk (graphonSetoid Ω μ) W)
      = _root_.Graphons.homDensity F W :=
  rfl

end HomDensity

end Graphons
