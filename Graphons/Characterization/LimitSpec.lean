/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier E, items E0/E1 — **the independent axiomatic specification
of "a dense graph limit theory"**.

E0 (the finite side): `FinWeighted` — finite weighted graphs, packaged as graphons on finite
uniform carriers, with the cut premetric `finCutDist` (a `PseudoMetricSpace`: distinct
weighted graphs can be at distance 0, e.g. blow-ups) and the finite homomorphism densities
`finHomDensity`. Simple graphs embed via `FinWeighted.ofSimple` (= `Graphon.step`), and on
them `finHomDensity` is the combinatorial homomorphism density (`homDensity_step`).

E1 (the spec): `IsDenseGraphLimitTheory X ι t` — a complete metric space `X`, a distance-
preserving map `ι` from finite weighted graphs with dense range (not injective: weakly
isomorphic weighted graphs collapse), and continuous density functionals `t F : X → ℝ`
pinned to the finite densities on the image. This is the textbook-reviewable definition of
"the space of dense graph limits": it can be audited against Lovász (chapters 8, 11)
WITHOUT reading any implementation file of this repo. A point of an abstract model `X` is
not literally a kernel; it is identified with a graphon equivalence class (a point of
`GraphonSpace`) only through the E2/E3 theorems below. Independently reviewed:
an independent spec review (verdict: spec correct; E2 + its axiom guard are the
outstanding validation steps).

The validation payoff (targets E2/E3, after the spec passes independent review):
  * E2 (existence)  : `GraphonSpace ℝ unitMeasure` with the step-transport `ι` and the
    descended `homDensity` satisfies the spec [inherits axioms #1, #2 via completeness].
  * E3 (uniqueness) : any two instances are canonically isometric, via Mathlib's
    `AbstractCompletion.compareEquiv` (a complete space with an isometric dense copy of
    `FinWeighted` IS its completion, and completions are unique) — so the spec has ONE
    model: the definitions are forced, not merely consistent.

Spec-sanity lemmas (`t_mem_Icc`) show the axioms already force the right structure on ANY
model — evidence the spec is neither vacuous nor over-constrained.
-/
import Graphons.Core.StepDensity
import Graphons.CutMetric.Gluing

open MeasureTheory

namespace Graphons

/-! ### E0 — the finite side -/

/-- A **finite weighted graph**: a graphon on the finite uniform carrier
    `(Fin (n+1), unifFin (n+1))` for some `n` (i.e. an edge-weight matrix with entries in
    `[0,1]`, symmetric, on `n+1` vertices). Simple graphs embed via `FinWeighted.ofSimple`. -/
def FinWeighted : Type :=
  Σ n : ℕ, Graphon (Fin (n + 1)) (unifFin (n + 1))

/-- The **cut premetric on finite weighted graphs**: the (cross-carrier, coupling-infimum)
    cut distance between the associated graphons. -/
noncomputable def finCutDist (G H : FinWeighted) : ℝ := cutDist G.2 H.2

/-- The **finite homomorphism density** `t(F, G)` of a simple graph `F` in a finite
    weighted graph `G`. On embedded simple graphs this is the combinatorial homomorphism
    density (`homDensity_step`). -/
noncomputable def finHomDensity {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (G : FinWeighted) : ℝ :=
  homDensity F G.2

/-- Embed a simple graph as a finite weighted graph (its `0/1` step graphon). -/
noncomputable def FinWeighted.ofSimple {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] : FinWeighted :=
  ⟨n, Graphon.step G⟩

/-- Finite weighted graphs form a **pseudometric space** under the cut distance (only a
    PSEUDOmetric: weakly isomorphic weighted graphs — e.g. blow-ups — are at distance 0). -/
noncomputable instance : PseudoMetricSpace FinWeighted where
  dist G H := finCutDist G H
  dist_self G := cutDist_self_eq_zero G.2
  dist_comm G H := cutDist_comm G.2 H.2
  dist_triangle G H K := cutDist_triangle G.2 H.2 K.2

@[simp] theorem dist_finWeighted (G H : FinWeighted) : dist G H = finCutDist G H := rfl

theorem finHomDensity_mem_Icc {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (G : FinWeighted) : finHomDensity F G ∈ Set.Icc (0 : ℝ) 1 :=
  Graphon.homDensity_mem_Icc F G.2

/-! ### E1 — the abstract specification -/

/-- **The dense-graph-limit-theory specification** (Lovász, *Large Networks and Graph
    Limits*, the LSZ completion picture of Ch. 8/11, stated abstractly):

    a complete metric space `X`, together with
    * a map `ι` from finite weighted graphs that is **distance-preserving** for the cut
      premetric and has **dense range** ("`X` completes the finite graphs"; NOT injective —
      weakly isomorphic weighted graphs, being at cut distance `0`, must collapse), and
    * for every finite simple graph `F` a **continuous** density functional `t F : X → ℝ`
      that restricts to the **finite homomorphism density** on the image of `ι`.

    Any such `(X, ι, t)` is "a theory of dense graph limits". The validation theorems:
    `GraphonSpace` is one (E2), and all of them are canonically isometric (E3) — so the
    spec pins the object up to unique isomorphism. -/
structure IsDenseGraphLimitTheory (X : Type*) [MetricSpace X] [CompleteSpace X]
    (ι : FinWeighted → X)
    (t : ∀ ⦃n : ℕ⦄ (F : SimpleGraph (Fin n)), DecidableRel F.Adj → X → ℝ) : Prop where
  /-- finite weighted graphs are dense in `X` -/
  dense_range : DenseRange ι
  /-- `ι` preserves the cut distance (hence is uniform-inducing: `X` completes `FinWeighted`) -/
  dist_ι : ∀ G H : FinWeighted, dist (ι G) (ι H) = finCutDist G H
  /-- each density functional is continuous on `X` -/
  continuous_t : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) (inst : DecidableRel F.Adj),
    Continuous (t F inst)
  /-- the density functionals restrict to the finite homomorphism densities -/
  compat_t : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) (inst : DecidableRel F.Adj)
    (G : FinWeighted), t F inst (ι G) = @finHomDensity n F inst G

namespace IsDenseGraphLimitTheory

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
  {ι : FinWeighted → X} {t : ∀ ⦃n : ℕ⦄ (F : SimpleGraph (Fin n)), DecidableRel F.Adj → X → ℝ}

/-! #### Spec-sanity: consequences forced on EVERY model

These are not extra axioms — they follow from the four fields. Proving them certifies the
spec is strong enough to force the basic structure (and is therefore a meaningful test for
E2/E3), while keeping the axiom list minimal. -/

/-- In any model, the density functionals take values in `[0,1]`: the bound holds on the
    dense image (where `t` is a finite homomorphism density) and passes to the closure by
    continuity. -/
theorem t_mem_Icc (h : IsDenseGraphLimitTheory X ι t) {n : ℕ} (F : SimpleGraph (Fin n))
    (inst : DecidableRel F.Adj) (x : X) : t F inst x ∈ Set.Icc (0 : ℝ) 1 := by
  have hclosed : IsClosed {y : X | t F inst y ∈ Set.Icc (0 : ℝ) 1} :=
    IsClosed.preimage (h.continuous_t n F inst) isClosed_Icc
  have hsub : Set.range ι ⊆ {y : X | t F inst y ∈ Set.Icc (0 : ℝ) 1} := by
    rintro - ⟨G, rfl⟩
    have := h.compat_t n F inst G
    simp only [Set.mem_setOf_eq, this]
    exact finHomDensity_mem_Icc F G
  have hx : x ∈ closure (Set.range ι) := h.dense_range x
  exact hclosed.closure_subset_iff.2 hsub hx

end IsDenseGraphLimitTheory

/-! ### Targets (stated informally; proved in later passes — `main` stays sorry-free)

* **E2 (existence).** `IsDenseGraphLimitTheory (GraphonSpace ℝ unitMeasure) stepTransport
  descendedHomDensity` — needs the interval step-transport `ι` (pullback of a finite
  weighted graph along the measure-preserving interval map `[0,1] → Fin (n+1)`), `dist_ι`
  from cut-distance invariance under measure-preserving pullbacks, density from
  `exists_stepGraphon_cutDist_le`, and continuity from `continuous_homDensity`.
  [Inherits axioms #1, #2 through `instCompleteSpaceGraphonSpaceUnit`.]
* **E3 (uniqueness).** Any two models are canonically isometric, compatibly with `ι` and
  `t`: package each model as an `AbstractCompletion FinWeighted` (`dist_ι` ⟹ `Isometry ι`
  ⟹ `IsUniformInducing`), compare via `AbstractCompletion.compareEquiv`, upgrade to an
  `IsometryEquiv` and transport `t` by `Continuous.ext_on` over the dense image.
  [Axiom-free.]
-/

end Graphons
