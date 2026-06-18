/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

Multiplicativity of homomorphism densities over disjoint graph unions
(VALIDATION.md Tier B; needed for representability).

For finite simple graphs `F₁ : SimpleGraph V₁`, `F₂ : SimpleGraph V₂` and a graphon `W`,
  t(F₁ ⊕g F₂, W) = t(F₁, W) · t(F₂, W),
where `F₁ ⊕g F₂ : SimpleGraph (V₁ ⊕ V₂)` is `SimpleGraph.sum`, the disjoint union.

Proof: `(V₁ ⊕ V₂) → Ω` is measure-preservingly equivalent to `(V₁ → Ω) × (V₂ → Ω)` via
`MeasurableEquiv.sumPiEquivProdPi` (`measurePreserving_sumPiEquivProdPi`); the edge set of the
disjoint union splits as the (disjoint) union of the images of the two factor edge sets under
`Sym2.map Sum.inl` / `Sym2.map Sum.inr`, so the integrand factors; Fubini (`integral_prod_mul`)
turns the product integral into the product of integrals.
-/
import Graphons.Core.Basic

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section EdgeSplit

variable {V₁ V₂ : Type*} (F₁ : SimpleGraph V₁) (F₂ : SimpleGraph V₂)

/-- Adjacency in the disjoint union is decidable when both factors have decidable adjacency. -/
instance instDecidableRelSumAdj [DecidableRel F₁.Adj] [DecidableRel F₂.Adj] :
    DecidableRel (F₁.sum F₂).Adj := by
  rintro (a | a) (b | b) <;> simp only [SimpleGraph.sum_adj] <;> infer_instance

/-- `Sym2.map Sum.inl` as an embedding (injective since `Sum.inl` is). -/
def sym2InlEmb : Sym2 V₁ ↪ Sym2 (V₁ ⊕ V₂) :=
  ⟨Sym2.map Sum.inl, Sym2.map.injective Sum.inl_injective⟩

/-- `Sym2.map Sum.inr` as an embedding. -/
def sym2InrEmb : Sym2 V₂ ↪ Sym2 (V₁ ⊕ V₂) :=
  ⟨Sym2.map Sum.inr, Sym2.map.injective Sum.inr_injective⟩

/-- Membership in the edge set of the disjoint union: an edge is either an `inl`-image of an
`F₁`-edge or an `inr`-image of an `F₂`-edge. -/
theorem mem_edgeSet_sum (e : Sym2 (V₁ ⊕ V₂)) :
    e ∈ (F₁.sum F₂).edgeSet ↔
      (∃ e₁ ∈ F₁.edgeSet, Sym2.map Sum.inl e₁ = e) ∨
        (∃ e₂ ∈ F₂.edgeSet, Sym2.map Sum.inr e₂ = e) := by
  induction e with
  | _ a b =>
    rcases a with a | a <;> rcases b with b | b
    · -- inl a, inl b
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.sum_adj]
      constructor
      · intro h; exact Or.inl ⟨s(a, b), h, by simp⟩
      · rintro (⟨e₁, he₁, heq⟩ | ⟨e₂, he₂, heq⟩)
        · induction e₁ with
          | _ c d =>
            rw [Sym2.map_mk, Sym2.eq_iff] at heq
            rcases heq with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
              (simp only [Sum.inl.injEq] at hc hd; subst hc; subst hd)
            · exact he₁
            · exact he₁.symm
        · induction e₂ with
          | _ c d => rw [Sym2.map_mk, Sym2.eq_iff] at heq; simp at heq
    · -- inl a, inr b : no edge
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.sum_adj]
      constructor
      · exact fun h => absurd h (by simp)
      · rintro (⟨e₁, he₁, heq⟩ | ⟨e₂, he₂, heq⟩)
        · induction e₁ with
          | _ c d => rw [Sym2.map_mk, Sym2.eq_iff] at heq; simp at heq
        · induction e₂ with
          | _ c d => rw [Sym2.map_mk, Sym2.eq_iff] at heq; simp at heq
    · -- inr a, inl b : no edge
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.sum_adj]
      constructor
      · exact fun h => absurd h (by simp)
      · rintro (⟨e₁, he₁, heq⟩ | ⟨e₂, he₂, heq⟩)
        · induction e₁ with
          | _ c d => rw [Sym2.map_mk, Sym2.eq_iff] at heq; simp at heq
        · induction e₂ with
          | _ c d => rw [Sym2.map_mk, Sym2.eq_iff] at heq; simp at heq
    · -- inr a, inr b
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.sum_adj]
      constructor
      · intro h; exact Or.inr ⟨s(a, b), h, by simp⟩
      · rintro (⟨e₁, he₁, heq⟩ | ⟨e₂, he₂, heq⟩)
        · induction e₁ with
          | _ c d => rw [Sym2.map_mk, Sym2.eq_iff] at heq; simp at heq
        · induction e₂ with
          | _ c d =>
            rw [Sym2.map_mk, Sym2.eq_iff] at heq
            rcases heq with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
              (simp only [Sum.inr.injEq] at hc hd; subst hc; subst hd)
            · exact he₂
            · exact he₂.symm

variable [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
  [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]

omit [DecidableEq V₁] [DecidableEq V₂] in
/-- The two summand-images of edge sets in the disjoint union are disjoint as Finsets. -/
theorem disjoint_edgeFinset_sum :
    Disjoint (F₁.edgeFinset.map (sym2InlEmb (V₂ := V₂)))
      (F₂.edgeFinset.map (sym2InrEmb (V₁ := V₁))) := by
  rw [Finset.disjoint_left]
  rintro e he₁ he₂
  rw [Finset.mem_map] at he₁ he₂
  obtain ⟨a, _, ha⟩ := he₁
  obtain ⟨b, _, hb⟩ := he₂
  rw [← ha] at hb
  simp only [sym2InlEmb, sym2InrEmb, Function.Embedding.coeFn_mk] at hb
  induction a with
  | _ p q =>
    induction b with
    | _ r s => rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at hb; simp at hb

/-- The edge `Finset` of the disjoint union splits as the disjoint union of the `inl`/`inr` images
of the factor edge sets. -/
theorem edgeFinset_sum :
    (F₁.sum F₂).edgeFinset =
      (F₁.edgeFinset.map (sym2InlEmb (V₂ := V₂))) ∪ (F₂.edgeFinset.map (sym2InrEmb (V₁ := V₁))) := by
  ext e
  rw [Finset.mem_union, SimpleGraph.mem_edgeFinset, mem_edgeSet_sum]
  simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset, sym2InlEmb, sym2InrEmb,
    Function.Embedding.coeFn_mk]

end EdgeSplit

section Integrand

variable {V₁ V₂ : Type*} (W : Graphon Ω μ)

/-- `edgeVal` of an `inl`-mapped edge only depends on the `inl` coordinates of `x`. -/
theorem edgeVal_map_inl (x : (V₁ ⊕ V₂) → Ω) (e : Sym2 V₁) :
    edgeVal W x (Sym2.map Sum.inl e) = edgeVal W (x ∘ Sum.inl) e := by
  induction e with
  | _ a b => simp only [Sym2.map_mk, edgeVal, Sym2.lift_mk, Function.comp_apply]

/-- `edgeVal` of an `inr`-mapped edge only depends on the `inr` coordinates of `x`. -/
theorem edgeVal_map_inr (x : (V₁ ⊕ V₂) → Ω) (e : Sym2 V₂) :
    edgeVal W x (Sym2.map Sum.inr e) = edgeVal W (x ∘ Sum.inr) e := by
  induction e with
  | _ a b => simp only [Sym2.map_mk, edgeVal, Sym2.lift_mk, Function.comp_apply]

variable (F₁ : SimpleGraph V₁) (F₂ : SimpleGraph V₂)
  [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
  [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]

/-- The homomorphism-density integrand of the disjoint union factors: it is the product of the
`F₁`-integrand on the `inl` coordinates and the `F₂`-integrand on the `inr` coordinates. -/
theorem homDensityIntegrand_sum (x : (V₁ ⊕ V₂) → Ω) :
    homDensityIntegrand (F₁.sum F₂) W x =
      homDensityIntegrand F₁ W (x ∘ Sum.inl) * homDensityIntegrand F₂ W (x ∘ Sum.inr) := by
  unfold homDensityIntegrand
  rw [edgeFinset_sum F₁ F₂, Finset.prod_union (disjoint_edgeFinset_sum F₁ F₂),
    Finset.prod_map, Finset.prod_map]
  congr 1
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    simp only [sym2InlEmb, Function.Embedding.coeFn_mk, edgeVal_map_inl]
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    simp only [sym2InrEmb, Function.Embedding.coeFn_mk, edgeVal_map_inr]

end Integrand

section Main

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]

/-- **Multiplicativity of homomorphism densities over disjoint graph unions.**
For finite simple graphs `F₁`, `F₂` and a graphon `W`,
  `t(F₁ ⊕g F₂, W) = t(F₁, W) · t(F₂, W)`. -/
theorem homDensity_sum
    (F₁ : SimpleGraph V₁) [DecidableRel F₁.Adj] (F₂ : SimpleGraph V₂) [DecidableRel F₂.Adj]
    (W : Graphon Ω μ) :
    homDensity (F₁.sum F₂) W = homDensity F₁ W * homDensity F₂ W := by
  classical
  -- The measure-preserving equivalence `((V₁ ⊕ V₂) → Ω) ≃ᵐ (V₁ → Ω) × (V₂ → Ω)`.
  set e : ((V₁ ⊕ V₂) → Ω) ≃ᵐ ((V₁ → Ω) × (V₂ → Ω)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ => Ω) with he
  have hmp : MeasurePreserving e (piMeasure (V₁ ⊕ V₂) μ)
      ((piMeasure V₁ μ).prod (piMeasure V₂ μ)) := by
    rw [piMeasure, piMeasure, piMeasure]
    exact measurePreserving_sumPiEquivProdPi (fun _ => μ)
  -- Push the integral through `e`, factor the integrand, then apply Fubini.
  set g : (V₁ → Ω) × (V₂ → Ω) → ℝ := fun p =>
    homDensityIntegrand F₁ W p.1 * homDensityIntegrand F₂ W p.2 with hg
  have hfac : ∀ x : (V₁ ⊕ V₂) → Ω,
      homDensityIntegrand (F₁.sum F₂) W x = g (e x) := by
    intro x
    simpa [he, hg, MeasurableEquiv.sumPiEquivProdPi, Function.comp_def] using
      homDensityIntegrand_sum W F₁ F₂ x
  calc homDensity (F₁.sum F₂) W
      = ∫ x, g (e x) ∂(piMeasure (V₁ ⊕ V₂) μ) := by
        rw [homDensity]; exact integral_congr_ae (ae_of_all _ hfac)
    _ = ∫ y, g y ∂((piMeasure V₁ μ).prod (piMeasure V₂ μ)) := hmp.integral_comp' g
    _ = homDensity F₁ W * homDensity F₂ W := by
        rw [hg, integral_prod_mul]; rfl

end Main

end Graphons

-- Verified axiom-clean: `#print axioms Graphons.homDensity_sum` →
-- depends only on [propext, Classical.choice, Quot.sound].
