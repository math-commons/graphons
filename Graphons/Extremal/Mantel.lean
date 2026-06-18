/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md Tier D, item D4 (K₃ case) — **Mantel's theorem for graphons**:
a triangle-free graphon has edge density at most `1/2`.

The proof is the classical co-degree argument:
  1. `t(K₃, W) = ∫∫ W(x,y)·coDeg(x,y)` (Fubini normal form, `integral_triangle_coDeg`);
  2. triangle-freeness gives `W(x,y)·coDeg(x,y) = 0` a.e. on `Ω × Ω`;
  3. pointwise, `coDeg(y,z) = 0` forces `deg(y) + deg(z) ≤ 1` (for a.e. `u` one of
     `W(y,u)`, `W(z,u)` vanishes, so the sum is ≤ 1 a.e.);
  4. hence `∫∫ W(x,y)·(deg x + deg y) ≤ ∫∫ W = t(K₂)`;
  5. the left side equals `2·∫ deg²` and `∫ deg² ≥ (∫ deg)² = t(K₂)²` (Cauchy–Schwarz),
     so `2·t(K₂)² ≤ t(K₂)`, i.e. `t(K₂) ≤ 1/2`.
-/
import Graphons.Counting.CoDegree
import Graphons.AnchorChecks

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Measurability / integrability helpers -/

section Helpers

variable (W : Graphon Ω μ)

private lemma meas_a : Measurable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1) :=
  W.meas'.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

private lemma meas_b : Measurable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.2) :=
  W.meas'.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

private lemma meas_c : Measurable (fun p : Ω × Ω × Ω => W.toFun p.2.1 p.2.2) :=
  W.meas'.comp ((measurable_fst.comp measurable_snd).prodMk
    (measurable_snd.comp measurable_snd))

/-- The triangle integrand `W(x,y)·W(x,z)·W(y,z)` is integrable on `Ω³`
    (re-proved locally; the Goodman.lean version is `private`). -/
private lemma integrable_abc :
    Integrable (fun p : Ω × Ω × Ω => W.toFun p.1 p.2.1 * W.toFun p.1 p.2.2
      * W.toFun p.2.1 p.2.2) (μ.prod (μ.prod μ)) := by
  refine SymmKernel.integrable_of_bdd (((meas_a W).mul (meas_b W)).mul (meas_c W))
    (C := 1) (fun p => abs_le.2 ⟨?_, ?_⟩)
  · have h := mul_nonneg (mul_nonneg (W.nonneg' p.1 p.2.1) (W.nonneg' p.1 p.2.2))
      (W.nonneg' p.2.1 p.2.2)
    linarith
  · exact mul_le_one₀
      (mul_le_one₀ (W.le_one' _ _) (W.nonneg' _ _) (W.le_one' _ _))
      (W.nonneg' _ _) (W.le_one' _ _)

/-- The uncurried graphon on the pair space (as a `fun p => …` lambda, for `Measurable.mul`
    compositions). -/
private lemma meas_pair : Measurable (fun p : Ω × Ω => W.toFun p.1 p.2) :=
  W.meas'.comp (measurable_fst.prodMk measurable_snd)

/-- The integrand `W(x,y)·coDeg(x,y)` is integrable on `Ω²`. -/
private lemma integrable_mul_coDeg :
    Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * W.coDeg p.1 p.2) (μ.prod μ) :=
  SymmKernel.integrable_of_bdd ((meas_pair W).mul W.measurable_coDeg) (C := 1)
    (fun p => abs_le.2
      ⟨by nlinarith [W.nonneg' p.1 p.2, W.coDeg_nonneg p.1 p.2],
        mul_le_one₀ (W.le_one' p.1 p.2) (W.coDeg_nonneg p.1 p.2) (W.coDeg_le_one p.1 p.2)⟩)

/-- The integrand `W(x,y)·deg(x)` is integrable on `Ω²`. -/
private lemma integrable_mul_deg_fst :
    Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * W.deg p.1) (μ.prod μ) :=
  SymmKernel.integrable_of_bdd ((meas_pair W).mul (W.measurable_deg.comp measurable_fst))
    (C := 1) (fun p => abs_le.2
      ⟨by nlinarith [W.nonneg' p.1 p.2, W.deg_nonneg p.1],
        mul_le_one₀ (W.le_one' p.1 p.2) (W.deg_nonneg p.1) (W.deg_le_one p.1)⟩)

/-- The integrand `W(x,y)·deg(y)` is integrable on `Ω²`. -/
private lemma integrable_mul_deg_snd :
    Integrable (fun p : Ω × Ω => W.toFun p.1 p.2 * W.deg p.2) (μ.prod μ) :=
  SymmKernel.integrable_of_bdd ((meas_pair W).mul (W.measurable_deg.comp measurable_snd))
    (C := 1) (fun p => abs_le.2
      ⟨by nlinarith [W.nonneg' p.1 p.2, W.deg_nonneg p.2],
        mul_le_one₀ (W.le_one' p.1 p.2) (W.deg_nonneg p.2) (W.deg_le_one p.2)⟩)

end Helpers

/-! ### Step 1: the co-degree normal form of the triangle density -/

/-- **Co-degree normal form of the triangle density**:
    `t(K₃, W) = ∫∫ W(x,y)·coDeg(x,y)`. -/
theorem integral_triangle_coDeg (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W
      = ∫ p : Ω × Ω, W.toFun p.1 p.2 * W.coDeg p.1 p.2 ∂(μ.prod μ) := by
  rw [homDensity_triangle, integral_prod _ (integrable_abc W)]
  -- swap the order of integration: `∫_x ∫_{(y,z)} = ∫_{(y,z)} ∫_x`
  have hswap := integral_integral_swap
    (f := fun (x : Ω) (q : Ω × Ω) => W.toFun x q.1 * W.toFun x q.2 * W.toFun q.1 q.2)
    (integrable_abc W)
  rw [hswap]
  -- at fixed `(y,z)`, the inner integral over `x` is `coDeg(y,z) · W(y,z)`
  have hinner : ∀ q : Ω × Ω,
      (∫ x, W.toFun x q.1 * W.toFun x q.2 * W.toFun q.1 q.2 ∂μ)
        = W.toFun q.1 q.2 * W.coDeg q.1 q.2 := by
    intro q
    rw [integral_mul_const]
    have hsymm : ∀ x, W.toFun x q.1 * W.toFun x q.2 = W.toFun q.1 x * W.toFun q.2 x := by
      intro x
      rw [W.symm' x q.1, W.symm' x q.2]
    simp only [hsymm]
    rw [mul_comm]
    rfl
  simp only [hinner]

/-! ### Step 2: triangle-freeness kills `W·coDeg` almost everywhere -/

/-- If `t(K₃, W) = 0` then `W(x,y)·coDeg(x,y) = 0` for a.e. `(x,y)`. -/
theorem ae_mul_coDeg_eq_zero (W : Graphon Ω μ)
    (h : homDensity (⊤ : SimpleGraph (Fin 3)) W = 0) :
    (fun p : Ω × Ω => W.toFun p.1 p.2 * W.coDeg p.1 p.2) =ᵐ[μ.prod μ] 0 := by
  have h0 : (0 : Ω × Ω → ℝ) ≤ fun p => W.toFun p.1 p.2 * W.coDeg p.1 p.2 :=
    fun p => mul_nonneg (W.nonneg' p.1 p.2) (W.coDeg_nonneg p.1 p.2)
  refine (integral_eq_zero_iff_of_nonneg h0 (integrable_mul_coDeg W)).1 ?_
  rw [← integral_triangle_coDeg]
  exact h

/-! ### Step 3: vanishing co-degree forces small degree sum -/

/-- If `coDeg(y,z) = 0` then `deg(y) + deg(z) ≤ 1`: for a.e. `u`, one of `W(y,u)`, `W(z,u)`
    vanishes and the other is at most `1`. -/
theorem add_deg_le_one_of_coDeg_eq_zero (W : Graphon Ω μ) (y z : Ω)
    (h0 : W.coDeg y z = 0) : W.deg y + W.deg z ≤ 1 := by
  have hae : (fun u => W.toFun y u * W.toFun z u) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun u => mul_nonneg (W.nonneg' y u) (W.nonneg' z u))
      (W.integrable_coDeg_slice y z)).1 h0
  have hsum : W.deg y + W.deg z = ∫ u, (W.toFun y u + W.toFun z u) ∂μ :=
    (integral_add (W.integrable_toFun_left y) (W.integrable_toFun_left z)).symm
  rw [hsum]
  have hle : (fun u => W.toFun y u + W.toFun z u) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [hae] with u hu
    simp only [Pi.zero_apply] at hu
    rcases mul_eq_zero.mp hu with hyu | hzu
    · have := W.le_one' z u
      linarith
    · have := W.le_one' y u
      linarith
  calc ∫ u, (W.toFun y u + W.toFun z u) ∂μ
      ≤ ∫ _, (1 : ℝ) ∂μ :=
        integral_mono_ae
          ((W.integrable_toFun_left y).add (W.integrable_toFun_left z))
          (integrable_const 1) hle
    _ = 1 := by simp

/-! ### Step 4: the key integral inequality -/

/-- For a triangle-free graphon, `∫∫ W(x,y)·(deg x + deg y) ≤ t(K₂, W)`. -/
theorem integral_mul_add_deg_le (W : Graphon Ω μ)
    (h : homDensity (⊤ : SimpleGraph (Fin 3)) W = 0) :
    ∫ p : Ω × Ω, W.toFun p.1 p.2 * (W.deg p.1 + W.deg p.2) ∂(μ.prod μ)
      ≤ homDensity (⊤ : SimpleGraph (Fin 2)) W := by
  rw [homDensity_edge]
  have hintL : Integrable
      (fun p : Ω × Ω => W.toFun p.1 p.2 * (W.deg p.1 + W.deg p.2)) (μ.prod μ) :=
    SymmKernel.integrable_of_bdd
      ((meas_pair W).mul ((W.measurable_deg.comp measurable_fst).add
        (W.measurable_deg.comp measurable_snd)))
      (C := 2) (fun p => abs_le.2
        ⟨by nlinarith [W.nonneg' p.1 p.2, W.deg_nonneg p.1, W.deg_nonneg p.2],
          by nlinarith [W.nonneg' p.1 p.2, W.le_one' p.1 p.2, W.deg_nonneg p.1,
            W.deg_nonneg p.2, W.deg_le_one p.1, W.deg_le_one p.2]⟩)
  have hintR : Integrable (fun p : Ω × Ω => W.toFun p.1 p.2) (μ.prod μ) :=
    W.integrable_uncurry
  refine integral_mono_ae hintL hintR ?_
  filter_upwards [ae_mul_coDeg_eq_zero W h] with p hp
  simp only [Pi.zero_apply] at hp
  rcases mul_eq_zero.mp hp with hW | hco
  · rw [hW]
    simp
  · exact mul_le_of_le_one_right (W.nonneg' p.1 p.2)
      (add_deg_le_one_of_coDeg_eq_zero W p.1 p.2 hco)

/-! ### Step 5: the left side is twice the degree second moment -/

/-- `∫∫ W(x,y)·(deg x + deg y) = 2·∫ deg²`. -/
theorem integral_mul_add_deg (W : Graphon Ω μ) :
    ∫ p : Ω × Ω, W.toFun p.1 p.2 * (W.deg p.1 + W.deg p.2) ∂(μ.prod μ)
      = 2 * ∫ x, (W.deg x) ^ 2 ∂μ := by
  have hsplit : ∀ p : Ω × Ω, W.toFun p.1 p.2 * (W.deg p.1 + W.deg p.2)
      = W.toFun p.1 p.2 * W.deg p.1 + W.toFun p.1 p.2 * W.deg p.2 :=
    fun p => mul_add _ _ _
  simp only [hsplit]
  rw [integral_add (integrable_mul_deg_fst W) (integrable_mul_deg_snd W)]
  -- first piece: `∫∫ W(x,y)·deg(x) = ∫ deg²`
  have h1 : ∫ p : Ω × Ω, W.toFun p.1 p.2 * W.deg p.1 ∂(μ.prod μ)
      = ∫ x, (W.deg x) ^ 2 ∂μ := by
    rw [integral_prod _ (integrable_mul_deg_fst W)]
    have hinner : ∀ x : Ω, (∫ y, W.toFun x y * W.deg x ∂μ) = (W.deg x) ^ 2 := by
      intro x
      rw [integral_mul_const, sq]
      rfl
    simp only [hinner]
  -- second piece: `∫∫ W(x,y)·deg(y) = ∫ deg²` (swap, then use symmetry of `W`)
  have h2 : ∫ p : Ω × Ω, W.toFun p.1 p.2 * W.deg p.2 ∂(μ.prod μ)
      = ∫ x, (W.deg x) ^ 2 ∂μ := by
    rw [integral_prod _ (integrable_mul_deg_snd W)]
    have hswap := integral_integral_swap
      (f := fun (x y : Ω) => W.toFun x y * W.deg y) (integrable_mul_deg_snd W)
    rw [hswap]
    have hinner : ∀ y : Ω, (∫ x, W.toFun x y * W.deg y ∂μ) = (W.deg y) ^ 2 := by
      intro y
      rw [integral_mul_const]
      have hsl : (fun x => W.toFun x y) = W.toFun y := by
        funext x
        exact W.symm' x y
      rw [hsl, sq]
      rfl
    simp only [hinner]
  rw [h1, h2]
  ring

/-! ### Step 6: D4, the K₃ case -/

/-- **Mantel's theorem for graphons** (D4, K₃ case): a triangle-free graphon has edge
    density at most `1/2`. -/
theorem mantel (W : Graphon Ω μ) (h : homDensity (⊤ : SimpleGraph (Fin 3)) W = 0) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W ≤ 1 / 2 := by
  set p := homDensity (⊤ : SimpleGraph (Fin 2)) W with hp
  -- `2·∫ deg² ≤ t(K₂)` (Steps 4 + 5)
  have hkey : 2 * ∫ x, (W.deg x) ^ 2 ∂μ ≤ p := by
    rw [← integral_mul_add_deg W]
    exact integral_mul_add_deg_le W h
  -- `t(K₂)² ≤ ∫ deg²` (Cauchy–Schwarz, D1)
  have hCS : p ^ 2 ≤ ∫ x, (W.deg x) ^ 2 ∂μ := by
    have h2 := sq_integral_deg_le W
    rwa [integral_deg] at h2
  have hp0 : 0 ≤ p := (Graphon.homDensity_mem_Icc _ W).1
  nlinarith

end Graphons
