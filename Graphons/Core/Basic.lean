/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG targets (random-fields roadmap, layer L9 — dense graph limits):
  C11313 "Graphon" (def), C12954/C13065 "Homomorphism density t(F,W)" (def),
  C12957 "Kernel" (signed superobject).
  Sources: Lovász, "Large Networks and Graph Limits" (2012); Borgs–Chayes–Lovász–
  Sós–Vesztergombi (2007); Janson (2010).

Foundational layer for graphons over an ABSTRACT probability space `(Ω, μ)` (DESIGN.md §8).
A `SymmKernel` is a symmetric, measurable, bounded (signed) kernel `W : Ω → Ω → ℝ`; it carries
an `AddCommGroup`/`Module ℝ` structure (pointwise) so that `U - W` and `c • W` make sense for the
cut metric. A `Graphon` extends `SymmKernel` with `[0,1]`-valued constraints. The homomorphism
density of a finite graph `F` into a graphon `W` is
  t(F, W) = ∫_{Ω^{V(F)}} ∏_{ij ∈ E(F)} W (x i) (x j)  dμ^{⊗V(F)},
against the product probability measure. Basic target: 0 ≤ t(F,W) ≤ 1.
-/
import Mathlib

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A **symmetric kernel**: a symmetric, measurable, bounded (but possibly signed) kernel
    `Ω → Ω → ℝ`. This is the signed superobject of `Graphon`; differences of graphons are
    `SymmKernel`s, which is what the cut metric needs. The `μ` argument is carried so that the
    type records the ambient probability space, even though the fields do not mention it. -/
structure SymmKernel (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  toFun : Ω → Ω → ℝ
  symm' : ∀ x y, toFun x y = toFun y x
  meas' : Measurable (Function.uncurry toFun)
  bdd'  : ∃ C, ∀ x y, |toFun x y| ≤ C

namespace SymmKernel

instance : CoeFun (SymmKernel Ω μ) (fun _ => Ω → Ω → ℝ) where coe W := W.toFun

@[ext]
theorem ext {U W : SymmKernel Ω μ} (h : ∀ x y, U x y = W x y) : U = W := by
  cases U; cases W
  congr
  funext x y
  exact h x y

/-! ### Algebraic structure (pointwise on `toFun`)

We equip `SymmKernel Ω μ` with `Zero`, `Neg`, `Add`, `Sub`, `SMul ℝ`, and assemble these into
`AddCommGroup` and `Module ℝ` instances. Each operation preserves symmetry, measurability, and
boundedness; the closure proofs use the triangle inequality and `Measurable.add` etc. -/

instance : Zero (SymmKernel Ω μ) where
  zero :=
    { toFun := fun _ _ => 0
      symm' := fun _ _ => rfl
      meas' := measurable_const
      bdd' := ⟨0, fun _ _ => by simp⟩ }

instance : Neg (SymmKernel Ω μ) where
  neg W :=
    { toFun := fun x y => -W x y
      symm' := fun x y => by rw [W.symm']
      meas' := W.meas'.neg
      bdd' := by
        obtain ⟨C, hC⟩ := W.bdd'
        exact ⟨C, fun x y => by simpa using hC x y⟩ }

instance : Add (SymmKernel Ω μ) where
  add U W :=
    { toFun := fun x y => U x y + W x y
      symm' := fun x y => by rw [U.symm', W.symm']
      meas' := U.meas'.add W.meas'
      bdd' := by
        obtain ⟨C₁, h₁⟩ := U.bdd'
        obtain ⟨C₂, h₂⟩ := W.bdd'
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        exact (abs_add_le (U x y) (W x y)).trans (add_le_add (h₁ x y) (h₂ x y)) }

instance : Sub (SymmKernel Ω μ) where
  sub U W :=
    { toFun := fun x y => U x y - W x y
      symm' := fun x y => by rw [U.symm', W.symm']
      meas' := U.meas'.sub W.meas'
      bdd' := by
        obtain ⟨C₁, h₁⟩ := U.bdd'
        obtain ⟨C₂, h₂⟩ := W.bdd'
        refine ⟨C₁ + C₂, fun x y => ?_⟩
        calc |U x y - W x y| ≤ |U x y| + |W x y| := abs_sub _ _
          _ ≤ C₁ + C₂ := add_le_add (h₁ x y) (h₂ x y) }

instance : SMul ℝ (SymmKernel Ω μ) where
  smul c W :=
    { toFun := fun x y => c * W x y
      symm' := fun x y => by rw [W.symm']
      meas' := W.meas'.const_mul c
      bdd' := by
        obtain ⟨C, hC⟩ := W.bdd'
        refine ⟨|c| * C, fun x y => ?_⟩
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg c) }

@[simp] theorem zero_apply (x y : Ω) : (0 : SymmKernel Ω μ) x y = 0 := rfl
@[simp] theorem neg_apply (W : SymmKernel Ω μ) (x y : Ω) : (-W) x y = -W x y := rfl
@[simp] theorem add_apply (U W : SymmKernel Ω μ) (x y : Ω) : (U + W) x y = U x y + W x y := rfl
@[simp] theorem sub_apply (U W : SymmKernel Ω μ) (x y : Ω) : (U - W) x y = U x y - W x y := rfl
@[simp] theorem smul_apply (c : ℝ) (W : SymmKernel Ω μ) (x y : Ω) : (c • W) x y = c * W x y := rfl

instance : AddCommGroup (SymmKernel Ω μ) where
  add_assoc U V W := by ext x y; simp [add_assoc]
  zero_add W := by ext x y; simp
  add_zero W := by ext x y; simp
  neg_add_cancel W := by ext x y; simp
  add_comm U W := by ext x y; simp [add_comm]
  sub_eq_add_neg U W := by ext x y; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℝ (SymmKernel Ω μ) where
  one_smul W := by ext x y; simp
  mul_smul a b W := by ext x y; simp [mul_assoc]
  smul_zero c := by ext x y; simp
  smul_add c U W := by ext x y; simp [mul_add]
  add_smul a b W := by ext x y; simp [add_mul]
  zero_smul W := by ext x y; simp

/-! ### Integrability (load-bearing)

`bdd'` makes a `SymmKernel` integrand integrable against any finite (in particular probability)
measure. These are reusable lemmas: Lean's Bochner integral silently returns `0` without an
`Integrable` witness. -/

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_bdd {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f ν := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simpa [Real.norm_eq_abs] using hC x

/-- The "uncurried" two-variable integrand of a `SymmKernel` is integrable against the product
    measure `μ ×ˢ μ` on `Ω × Ω`. -/
theorem integrable_uncurry [IsFiniteMeasure μ] (W : SymmKernel Ω μ) :
    Integrable (Function.uncurry W.toFun) (μ.prod μ) := by
  obtain ⟨C, hC⟩ := W.bdd'
  exact integrable_of_bdd W.meas' (C := C) (fun p => by
    obtain ⟨x, y⟩ := p; exact hC x y)

/-! ### Nonnegative bound helper (P2)

`bdd'` only supplies *some* bound `C`, which need not be nonnegative.  For cut-norm estimates
(`cutNorm W ≤ W.bound`, scalar bounds, monotonicity) it is convenient to have a *canonical
nonnegative* bound.  `SymmKernel.bound` returns `max (Classical.choose W.bdd') 0`. -/

/-- A canonical **nonnegative** bound on `|W x y|`, extracted from `bdd'`. -/
noncomputable def bound (W : SymmKernel Ω μ) : ℝ := max (Classical.choose W.bdd') 0

/-- `W.bound` is nonnegative. -/
theorem bound_nonneg (W : SymmKernel Ω μ) : 0 ≤ W.bound := le_max_right _ _

/-- `|W x y| ≤ W.bound` for all `x y`. -/
theorem abs_le_bound (W : SymmKernel Ω μ) (x y : Ω) : |W.toFun x y| ≤ W.bound :=
  (Classical.choose_spec W.bdd' x y).trans (le_max_left _ _)

end SymmKernel

/-- A **graphon**: a symmetric, measurable, `[0,1]`-valued kernel on an abstract probability
    space `(Ω, μ)`. It `extends SymmKernel` (so `U - W`, `c • W` are available via the coercion);
    `bdd'` follows automatically with `C = 1`. (C11313.) -/
structure Graphon (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    extends SymmKernel Ω μ where
  nonneg' : ∀ x y, 0 ≤ toFun x y
  le_one' : ∀ x y, toFun x y ≤ 1

namespace Graphon

variable [IsProbabilityMeasure μ]

instance : CoeFun (Graphon Ω μ) (fun _ => Ω → Ω → ℝ) where coe W := W.toFun

@[simp] theorem coe_toSymmKernel (W : Graphon Ω μ) (x y : Ω) :
    W.toSymmKernel x y = W x y := rfl

/-- **Smart constructor** for `Graphon` (P2): build a graphon from `toFun`, symmetry,
    measurability, and the `[0,1]`-valued constraints, filling the inherited `bdd' := ⟨1, …⟩`
    automatically (since `0 ≤ W ≤ 1 ⇒ |W| ≤ 1`). -/
def mk' (toFun : Ω → Ω → ℝ) (symm' : ∀ x y, toFun x y = toFun y x)
    (meas' : Measurable (Function.uncurry toFun)) (nonneg' : ∀ x y, 0 ≤ toFun x y)
    (le_one' : ∀ x y, toFun x y ≤ 1) : Graphon Ω μ where
  toFun := toFun
  symm' := symm'
  meas' := meas'
  bdd' := ⟨1, fun x y => abs_le.2 ⟨by linarith [nonneg' x y], le_one' x y⟩⟩
  nonneg' := nonneg'
  le_one' := le_one'

@[simp] theorem mk'_apply (toFun : Ω → Ω → ℝ) (symm' meas' nonneg' le_one') (x y : Ω) :
    (mk' (μ := μ) toFun symm' meas' nonneg' le_one') x y = toFun x y := rfl

/-- A graphon is integrable (its uncurried integrand against `μ ×ˢ μ`). -/
theorem integrable_uncurry (W : Graphon Ω μ) :
    Integrable (Function.uncurry W.toFun) (μ.prod μ) :=
  W.toSymmKernel.integrable_uncurry

end Graphon

/-- The value `W` assigns to an (unordered) edge `e : Sym2 V` given a point `x : V → Ω`.
    Well-defined because `W` is symmetric, packaged via `Sym2.lift`. -/
noncomputable def edgeVal {V : Type*} [IsProbabilityMeasure μ] (W : Graphon Ω μ) (x : V → Ω)
    (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun a b => W (x a) (x b), fun a b => by simpa using W.symm' (x a) (x b)⟩ e

namespace Graphon

variable [IsProbabilityMeasure μ]

theorem edgeVal_nonneg {V : Type*} (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) :
    0 ≤ edgeVal W x e := by
  induction e with
  | _ a b => exact W.nonneg' (x a) (x b)

theorem edgeVal_le_one {V : Type*} (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) :
    edgeVal W x e ≤ 1 := by
  induction e with
  | _ a b => exact W.le_one' (x a) (x b)

/-- `edgeVal W · e` is a measurable function of the point `x : V → Ω`. -/
theorem measurable_edgeVal {V : Type*} [MeasurableSpace V] (W : Graphon Ω μ) (e : Sym2 V) :
    Measurable (fun x : V → Ω => edgeVal W x e) := by
  induction e with
  | _ a b =>
    simp only [edgeVal, Sym2.lift_mk]
    have h : Measurable (fun x : V → Ω => (Function.uncurry W.toFun) (x a, x b)) :=
      W.meas'.comp ((measurable_pi_apply a).prodMk (measurable_pi_apply b))
    exact h

end Graphon

/-- The integrand of the homomorphism density: the product over the edges of `F` of the
    graphon values at the endpoints. -/
noncomputable def homDensityIntegrand {V : Type*} [Fintype V] [IsProbabilityMeasure μ]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) (x : V → Ω) : ℝ :=
  ∏ e ∈ F.edgeFinset, edgeVal W x e

namespace Graphon

variable [IsProbabilityMeasure μ]

theorem homDensityIntegrand_nonneg {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (W : Graphon Ω μ) (x : V → Ω) : 0 ≤ homDensityIntegrand F W x :=
  Finset.prod_nonneg (fun e _ => edgeVal_nonneg W x e)

theorem homDensityIntegrand_le_one {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (W : Graphon Ω μ) (x : V → Ω) : homDensityIntegrand F W x ≤ 1 :=
  Finset.prod_le_one (fun e _ => edgeVal_nonneg W x e) (fun e _ => edgeVal_le_one W x e)

theorem measurable_homDensityIntegrand {V : Type*} [Fintype V] [MeasurableSpace V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    Measurable (homDensityIntegrand F W) := by
  unfold homDensityIntegrand
  exact Finset.measurable_prod _ (fun e _ => measurable_edgeVal W e)

end Graphon

/-- The product probability measure `μ^{⊗V}` on `V → Ω`. -/
noncomputable def piMeasure (V : Type*) [Fintype V] (μ : Measure Ω) : Measure (V → Ω) :=
  Measure.pi (fun _ : V => μ)

instance (V : Type*) [Fintype V] [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (piMeasure V μ) := by
  rw [piMeasure]; infer_instance

/-- The **homomorphism density** of a finite simple graph `F` (on vertex type `V`) into a
    graphon `W` over `(Ω, μ)`: integrate the product of `W` over the edges of `F`, against the
    product probability measure `μ^{⊗V}` on `V → Ω`. (C12954/C13065.) -/
noncomputable def homDensity {V : Type*} [Fintype V] [IsProbabilityMeasure μ]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) : ℝ :=
  ∫ x, homDensityIntegrand F W x ∂(piMeasure V μ)

namespace Graphon

variable [IsProbabilityMeasure μ]

theorem integrable_homDensityIntegrand {V : Type*} [Fintype V] [MeasurableSpace V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    Integrable (homDensityIntegrand F W) (piMeasure V μ) := by
  refine Integrable.mono' (integrable_const 1) ?_ ?_
  · exact (measurable_homDensityIntegrand F W).aestronglyMeasurable
  · refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_of_nonneg (homDensityIntegrand_nonneg F W x)]
    exact homDensityIntegrand_le_one F W x

/-- Homomorphism densities are bounded in `[0,1]`. -/
theorem homDensity_mem_Icc {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (W : Graphon Ω μ) : homDensity F W ∈ Set.Icc (0:ℝ) 1 := by
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  refine ⟨?_, ?_⟩
  · exact integral_nonneg (fun x => homDensityIntegrand_nonneg F W x)
  · calc homDensity F W
        ≤ ∫ _ : V → Ω, (1 : ℝ) ∂(piMeasure V μ) := by
          refine integral_mono (integrable_homDensityIntegrand F W) (integrable_const 1) ?_
          exact fun x => homDensityIntegrand_le_one F W x
      _ = 1 := by simp

end Graphon

/-! ### Concrete unit-interval specialization (optional model)

The classical Lovász carrier `([0,1], Lebesgue)` as a concrete instance of the abstract API:
`Ω = ℝ` with the uniform probability measure on `[0,1]`. -/

open scoped ENNReal

/-- Lebesgue measure restricted to the unit interval `[0,1]`; a probability measure since
    `volume (Set.Icc 0 1) = 1`. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := by
  refine ⟨?_⟩
  rw [unitMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  simp

end Graphons
