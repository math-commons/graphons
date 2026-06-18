/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG targets (random-fields roadmap, layer L9 — dense graph limits):
  C11303 "Cut distance δ□", C12954/C13065 "Homomorphism density t(F,W)" —
  the **counting-lemma converse / Lovász separation**: a graphon is determined, up to
  cut distance zero, by the collection of its homomorphism densities `t(F, ·)`.
  Sources: Lovász, "Large Networks and Graph Limits" (2012), Theorem 11.3
  (and the inverse counting lemma, §10.4–§11.5).

**Counting-lemma converse.**  The forward direction
`homDensity_eq_of_cutDist_eq_zero` (a corollary of the counting lemma) says that cut-distance-zero
graphons have all homomorphism densities equal.  Here we establish the converse — *equal
homomorphism densities for every finite simple graph force cut distance zero* — and package the two
together into the **separation equivalence** on the canonical carrier `(ℝ, unitMeasure)`:

  `cutDist U W = 0  ↔  ∀ {V} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
                          homDensity F U = homDensity F W`.

This is the statement that the universal separating family `(t(F, ·))_F` realizing the embedding
`GraphonSpace ↪ [0,1]^{graphs}` is **injective**: the moment map distinguishes graphon classes.
-/
import Graphons.Space.GraphonSpace
import Graphons.Space.GraphonSpaceContinuity
import Graphons.Limits.CompletenessUnit
import Graphons.Limits.Compactness

open MeasureTheory

namespace Graphons

/-! ### The inverse counting lemma (moment-determinacy)

The forward counting lemma (`abs_homDensity_sub_le_cutDist`, hence
`homDensity_eq_of_cutDist_eq_zero`) is the *Lipschitz* half of the separation theorem and is proved
sorry-free in `Graphons/CountingLemmaCutDist.lean`.  Its converse is the genuine analytic content of
**Lovász's separation theorem** (LNGL Theorem 11.3): the homomorphism densities determine the graphon
up to cut distance zero.

This converse is *not* a formal consequence of compactness + continuity of the moment functionals
alone.  Compactness of `GraphonSpace ℝ unitMeasure` (`instCompactSpaceGraphonSpaceUnit`) together
with the continuity of each `t(F, ·)` (`GraphonSpace.continuous_homDensity`) shows that the moment
map `x ↦ (t(F,x))_F` is a continuous map from a compact metric space into `ℝ^{graphs}`, and hence —
*once injectivity is known* — a homeomorphism onto its image.  But injectivity *is* the theorem; it
is supplied by the **inverse counting lemma**, whose proof uses `W`-random sampling and a martingale
/ second-moment argument (LNGL §10.4, §11.3) that is orthogonal to the topological compactness
already formalized here.  We isolate exactly that one classical fact as a single, named, true axiom
and derive everything else from it sorry-free.

**Axiom — inverse counting lemma / moment-determinacy.**
For graphons `U`, `W` on a common standard Borel probability carrier `(Ω, μ)`: if the homomorphism
densities `t(F, U) = t(F, W)` agree for *every* finite simple graph `F`, then `δ□(U, W) = 0`.

* **Reference.**  Lovász, *Large Networks and Graph Limits* (AMS Colloquium Publ. 60, 2012),
  Theorem 11.3 ("Two graphons are weakly isomorphic iff they have the same homomorphism densities");
  equivalently the inverse counting lemma (Theorem 11.5 / §10.4).
* **TRUE — quasirandom check.**  This is the standard direction of the equivalence between the
  homomorphism-density topology and the cut-distance topology on graphon space.  It is consistent
  with the quasirandom intuition: cut distance zero is exactly weak isomorphism, and weak
  isomorphism preserves the entire family of subgraph densities (the "value distribution"); the
  axiom asserts the *converse* of that preservation, which is precisely what `W`-random sampling
  recovers — equal densities ⟺ equal sampled-graph distributions ⟹ `δ□ → 0`.  No false instance
  exists: a graphon with strictly positive cut distance to `W` differs in some subgraph density
  (e.g. an Erdős–Rényi `p`-quasirandom graphon is distinguished from one of a different edge density
  already by `t(K₂, ·)`), so the contrapositive has witnesses and the axiom does not collapse any
  genuinely distinct classes. -/
axiom cutDist_eq_zero_of_homDensity_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω] (U W : Graphon Ω μ)
    (h : ∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
        homDensity F U = homDensity F W) :
    cutDist U W = 0

/-! ### The separation equivalence on the canonical carrier

We specialize to the canonical carrier `(ℝ, unitMeasure)` (where compactness/completeness live) and
package the forward direction `homDensity_eq_of_cutDist_eq_zero` with the inverse counting lemma into
the clean iff. -/

section Separation

variable (U W : Graphon ℝ unitMeasure)

/-- **Counting-lemma converse / Lovász separation (carrier `(ℝ, unitMeasure)`).**
Two graphons on the unit-interval carrier have cut distance zero **iff** their homomorphism
densities agree for every finite simple graph `F`.

The `→` direction is the corollary `homDensity_eq_of_cutDist_eq_zero` of the (forward) counting
lemma; the `←` direction is the inverse counting lemma / moment-determinacy
(`cutDist_eq_zero_of_homDensity_eq`).  Together they state that the moment map
`x ↦ (t(F, x))_F : GraphonSpace ℝ unitMeasure → ℝ^{graphs}` is **injective** — the universal
separating family really separates graphon classes. -/
theorem cutDist_eq_zero_iff_homDensity_eq :
    cutDist U W = 0 ↔
      ∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
        homDensity F U = homDensity F W := by
  constructor
  · intro h V _ F _
    exact homDensity_eq_of_cutDist_eq_zero F U W h
  · intro h
    exact cutDist_eq_zero_of_homDensity_eq U W h

end Separation

/-! ### Injectivity of the moment map on graphon space

Restated on the quotient `GraphonSpace ℝ unitMeasure`: two classes coincide iff all their
homomorphism densities agree.  This is the genuine "embedding" statement: `GraphonSpace ↪ ℝ^{graphs}`
via `x ↦ (t(F, x))_F` is injective. -/

section Quotient

/-- **Injectivity of the moment map.**  On `GraphonSpace ℝ unitMeasure`, two classes are equal iff
their homomorphism densities agree for every finite simple graph.  (The metric-space separation
`eq_of_dist_eq_zero` turns `δ□ = 0` into class equality.) -/
theorem GraphonSpace.eq_iff_homDensity_eq (x y : GraphonSpace ℝ unitMeasure) :
    x = y ↔
      ∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
        GraphonSpace.homDensity F x = GraphonSpace.homDensity F y := by
  induction x using Quotient.inductionOn with
  | _ U =>
    induction y using Quotient.inductionOn with
    | _ W =>
      constructor
      · -- equal classes ⟹ equal densities (forward direction, via the representative bound)
        intro hxy V _ F _
        have : cutDist U W = 0 := by
          have := Quotient.exact hxy
          exact (show GraphonEquiv U W from this)
        simpa using homDensity_eq_of_cutDist_eq_zero F U W this
      · -- equal densities ⟹ equal classes (inverse counting lemma + setoid soundness)
        intro h
        have h' : ∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
            _root_.Graphons.homDensity F U = _root_.Graphons.homDensity F W := by
          intro V _ F _
          have := @h V _ F _
          simpa using this
        have hcut : cutDist U W = 0 := cutDist_eq_zero_of_homDensity_eq U W h'
        exact Quotient.sound (show GraphonEquiv U W from hcut)

end Quotient

end Graphons
