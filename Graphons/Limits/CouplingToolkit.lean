/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

**Coupling toolkit — Phase 0 (the GATE): sequential gluing onto a common carrier.**

Given a chain of couplings `π n` of `(μ, μ)` on a standard Borel carrier `(Ω, μ)`, we glue them
sequentially into a single measure `seqGlue π` on `Ω^ℕ` using the Mathlib Ionescu–Tulcea trajectory
measure (`ProbabilityTheory.Kernel.trajMeasure`). The make-or-break lemma is
`seqGlue_map_consecutive`: the law of consecutive coordinates `(x n, x (n+1))` under `seqGlue π`
equals the prescribed coupling `(π n).1`.

See `COUPLING_TOOLKIT.md` §2 Group 2 and §3 Phase 0.
-/
import Graphons.CutMetric.Gluing

open MeasureTheory ProbabilityTheory Finset Preorder

namespace Graphons

namespace CouplingToolkit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [Nonempty Ω]

/-! ### General adapter: mapping the first coordinate of a `compProd` against a `comap` kernel.

`(ν.map e) ⊗ₘ κ = (ν ⊗ₘ (κ.comap e he)).map (Prod.map e id)`. This lets us transport the
trajectory consecutive-marginal identity (stated with `frestrictLe`/`comap` kernels) onto plain
coordinate pairs. -/
theorem compProd_comap_map_prodMap {α α' β : Type*} [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] (ν : Measure α') [SFinite ν] (κ : Kernel α β) [IsSFiniteKernel κ]
    {e : α' → α} (he : Measurable e) :
    (ν.map e) ⊗ₘ κ = (ν ⊗ₘ (κ.comap e he)).map (Prod.map e id) := by
  have hpm : Measurable (Prod.map e (id : β → β)) := he.prodMap measurable_id
  ext s hs
  rw [Measure.map_apply hpm hs, Measure.compProd_apply hs,
    Measure.compProd_apply (hpm hs)]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) he]
  refine lintegral_congr fun a' => ?_
  rw [Kernel.comap_apply]
  congr 1

/-! ### The iterated step kernel -/

instance instProbCoupling (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) (n : ℕ) :
    IsProbabilityMeasure (π n).1 := (π n).2.isProbabilityMeasure

/-- The one-step conditional kernel `rightCondKernel (π n)`, lifted to consume the whole prefix
`Π i : Iic n, Ω` by reading off its last coordinate `n`. -/
noncomputable def itKernel (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, Ω) Ω :=
  (rightCondKernel (π n).1).comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (by fun_prop)

instance (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) (n : ℕ) :
    IsMarkovKernel (itKernel π n) := by
  unfold itKernel; infer_instance

/-! ### The sequentially glued measure on `Ω^ℕ` -/

/-- The sequentially glued measure on `Ω^ℕ`: start with `μ` and iterate the step kernels
`itKernel π`. The constant family `X n := Ω`. -/
noncomputable def seqGlue (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) :
    Measure (Π _ : ℕ, Ω) :=
  Kernel.trajMeasure (X := fun _ => Ω) μ (itKernel π)

instance (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) :
    IsProbabilityMeasure (seqGlue π) := by
  unfold seqGlue; infer_instance

/-! ### The coordinate-0 marginal -/

/-- Coordinate `0` of `seqGlue π` has law `μ`: the trajectory starts from `μ`. -/
theorem seqGlue_map_coord_zero (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) :
    (seqGlue π).map (fun x => x 0) = μ := by
  set κ := itKernel π with hκ
  have hf : (fun x : Π _ : ℕ, Ω ↦ x 0) =
      (fun x : Π i : Finset.Iic 0, Ω ↦ x ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘ frestrictLe 0 := rfl
  rw [seqGlue, Kernel.trajMeasure, hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

/-! ### THE GATE -/

/-- Gate, conditional on the coord-`n` marginal: if coordinate `n` of `seqGlue π` has law `μ`,
then the consecutive pair `(x n, x (n+1))` has law `(π n).1`. -/
theorem gate_of_coord (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) (n : ℕ)
    (hcoord : (seqGlue π).map (fun x => x n) = μ) :
    (seqGlue π).map (fun x => (x n, x (n + 1))) = (π n).1 := by
  set e : (Π i : Finset.Iic n, Ω) → Ω := fun p => p ⟨n, Finset.mem_Iic.2 le_rfl⟩ with he_def
  have he : Measurable e := by fun_prop
  -- Push the trajectory consecutive-marginal identity forward through `Prod.map e id`.
  have key := congrArg (fun ρ : Measure ((Π i : Finset.Iic n, Ω) × Ω) => ρ.map (Prod.map e id))
    (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => Ω) (μ₀ := μ) (κ := itKernel π) (a := n))
  simp only at key
  -- RHS of `key`: `(Prod.map e id) ∘ (frestrictLe n ·, · (n+1))` is `(· n, · (n+1))`.
  rw [seqGlue]
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at key
  -- LHS of `key`: unfold `itKernel` as a `comap` and use the adapter in reverse.
  rw [show itKernel π n = (rightCondKernel (π n).1).comap e he from rfl,
    ← compProd_comap_map_prodMap _ _ he, Measure.map_map he (by fun_prop)] at key
  -- Now `key : (trajMeasure …).map (e ∘ frestrictLe n) ⊗ₘ rightCondKernel = (trajMeasure …).map (· n, · (n+1))`.
  have hcoord' : (Kernel.trajMeasure (X := fun _ => Ω) μ (itKernel π)).map (e ∘ frestrictLe n)
      = μ := by
    have : (e ∘ frestrictLe n) = (fun x : Π _ : ℕ, Ω => x n) := rfl
    rw [this]; rw [← seqGlue]; exact hcoord
  rw [hcoord', compProd_rightCondKernel (π n).2] at key
  exact key.symm

/-! ### Coordinate marginals (all `n`) and the unconditional gate -/

/-- Every coordinate of `seqGlue π` has law `μ`. By induction on `n`: base case is
`seqGlue_map_coord_zero`; the step pushes the gate at level `n` to the second coordinate, which is
the second `IsCoupling` marginal `(π n).1.map Prod.snd = μ`. -/
theorem seqGlue_map_coord (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) (n : ℕ) :
    (seqGlue π).map (fun x => x n) = μ := by
  induction n with
  | zero => exact seqGlue_map_coord_zero π
  | succ k ih =>
    have hgate := gate_of_coord π k ih
    have : (fun x : Π _ : ℕ, Ω => x (k + 1)) = Prod.snd ∘ (fun x => (x k, x (k + 1))) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), hgate]
    exact (π k).2.2

/-- **THE GATE.** The law of consecutive coordinates `(x n, x (n+1))` under `seqGlue π` is exactly
the prescribed coupling `(π n).1`. -/
theorem seqGlue_map_consecutive (π : ℕ → {p : Measure (Ω × Ω) // IsCoupling μ μ p}) (n : ℕ) :
    (seqGlue π).map (fun x => (x n, x (n + 1))) = (π n).1 :=
  gate_of_coord π n (seqGlue_map_coord π n)

end CouplingToolkit

end Graphons
