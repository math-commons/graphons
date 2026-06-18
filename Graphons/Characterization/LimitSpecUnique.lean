/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier E, item E3 — **uniqueness of models of the
dense-graph-limit-theory spec**.

Any two structures satisfying `IsDenseGraphLimitTheory` are canonically isometric,
compatibly with the embeddings `ι` and the density functionals `t`. The proof packages
each model as an `AbstractCompletion FinWeighted` (`dist_ι` makes `ι` an isometry, hence
uniform-inducing), compares them with `AbstractCompletion.compareEquiv` (the universal
property of metric completions), upgrades the uniform equivalence to an `IsometryEquiv`
by a density argument, and transports the density functionals over the dense image.

Combined with E2 (`isDenseGraphLimitTheory_graphonSpace`), the spec therefore has exactly
ONE model up to canonical isometry: graphon space.
-/
import Graphons.Characterization.LimitSpecModel

open Set Function

namespace Graphons

namespace IsDenseGraphLimitTheory

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
  {ι : FinWeighted → X}
  {t : ∀ ⦃n : ℕ⦄ (F : SimpleGraph (Fin n)), DecidableRel F.Adj → X → ℝ}

/-- In any model, `ι` is an isometry (from the cut pseudometric to `X`). -/
private theorem isometry_ι (h : IsDenseGraphLimitTheory X ι t) : Isometry ι :=
  Isometry.of_dist_eq fun G H => (h.dist_ι G H).trans (dist_finWeighted G H).symm

/-- Any model of the spec, packaged as an abstract completion of `FinWeighted`. -/
private noncomputable def completionPkg (h : IsDenseGraphLimitTheory X ι t) :
    AbstractCompletion FinWeighted where
  space := X
  coe := ι
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := h.isometry_ι.isUniformInducing
  dense := h.dense_range

end IsDenseGraphLimitTheory

/-- E3: any two models of the spec are canonically isometric, compatibly with ι and t. -/
theorem isDenseGraphLimitTheory_unique
    {X₁ : Type*} [MetricSpace X₁] [CompleteSpace X₁]
    {X₂ : Type*} [MetricSpace X₂] [CompleteSpace X₂]
    {ι₁ : FinWeighted → X₁} {ι₂ : FinWeighted → X₂}
    {t₁ : ∀ ⦃n : ℕ⦄ (F : SimpleGraph (Fin n)), DecidableRel F.Adj → X₁ → ℝ}
    {t₂ : ∀ ⦃n : ℕ⦄ (F : SimpleGraph (Fin n)), DecidableRel F.Adj → X₂ → ℝ}
    (h₁ : IsDenseGraphLimitTheory X₁ ι₁ t₁) (h₂ : IsDenseGraphLimitTheory X₂ ι₂ t₂) :
    ∃ e : X₁ ≃ᵢ X₂, (∀ G : FinWeighted, e (ι₁ G) = ι₂ G) ∧
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) (inst : DecidableRel F.Adj) (x : X₁),
        t₂ F inst (e x) = t₁ F inst x := by
  -- Package both models as abstract completions of `FinWeighted` and compare them.
  let e₀ : X₁ ≃ᵤ X₂ := h₁.completionPkg.compareEquiv h₂.completionPkg
  have he₀_coe : ∀ G : FinWeighted, e₀ (ι₁ G) = ι₂ G := fun G =>
    h₁.completionPkg.compare_coe h₂.completionPkg G
  have hcont : Continuous e₀ := e₀.continuous
  -- Upgrade the uniform equivalence to an isometry by density.
  have hdist : ∀ x y : X₁, dist (e₀ x) (e₀ y) = dist x y := by
    have hf : Continuous fun p : X₁ × X₁ => dist (e₀ p.1) (e₀ p.2) :=
      (hcont.comp continuous_fst).dist (hcont.comp continuous_snd)
    have hg : Continuous fun p : X₁ × X₁ => dist p.1 p.2 := continuous_dist
    have hd : DenseRange (Prod.map ι₁ ι₁) := h₁.dense_range.prodMap h₁.dense_range
    have heq : (fun p : X₁ × X₁ => dist (e₀ p.1) (e₀ p.2)) = fun p : X₁ × X₁ => dist p.1 p.2 := by
      refine hd.equalizer hf hg (funext fun GH => ?_)
      obtain ⟨G, H⟩ := GH
      show dist (e₀ (ι₁ G)) (e₀ (ι₁ H)) = dist (ι₁ G) (ι₁ H)
      rw [he₀_coe, he₀_coe, h₂.dist_ι, h₁.dist_ι]
    exact fun x y => congrFun heq (x, y)
  refine ⟨⟨e₀.toEquiv, Isometry.of_dist_eq hdist⟩, fun G => he₀_coe G, ?_⟩
  -- Transport the density functionals over the dense image.
  intro n F inst x
  have hf : Continuous fun y : X₁ => t₂ F inst (e₀ y) := (h₂.continuous_t n F inst).comp hcont
  have heq : (fun y : X₁ => t₂ F inst (e₀ y)) = t₁ F inst := by
    refine h₁.dense_range.equalizer hf (h₁.continuous_t n F inst) (funext fun G => ?_)
    show t₂ F inst (e₀ (ι₁ G)) = t₁ F inst (ι₁ G)
    rw [he₀_coe, h₂.compat_t n F inst G, h₁.compat_t n F inst G]
  exact congrFun heq x

/-- Every model of the spec is canonically isometric to graphon space. -/
theorem isDenseGraphLimitTheory_unique_graphonSpace
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {ι : FinWeighted → X}
    {t : ∀ ⦃n : ℕ⦄ (F : SimpleGraph (Fin n)), DecidableRel F.Adj → X → ℝ}
    (h : IsDenseGraphLimitTheory X ι t) :
    ∃ e : X ≃ᵢ GraphonSpace ℝ unitMeasure, ∀ G : FinWeighted, e (ι G) = FinWeighted.toSpace G := by
  obtain ⟨e, he, -⟩ := isDenseGraphLimitTheory_unique h isDenseGraphLimitTheory_graphonSpace
  exact ⟨e, he⟩

end Graphons
