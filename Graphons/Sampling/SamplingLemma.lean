/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

The **first sampling lemma, expectation form** (EXTENDED_VALIDATION_PLAN.md WS3, pass 2):
the expected homomorphism density of the W-random graph `𝔾(n, W)` equals `t(F, W)` up to
the non-injectivity defect `k(k-1)/n`, where `k = |V(F)|`.

The engine is the EXACT identity on injective placements
(`integral_edgeProb_image_of_injective`): for injective `ψ : V → Fin n`, the annealed edge
product integrates to exactly `t(F, W)` — no error term, any `n`, any carrier. This rests on
the marginalization fact (`measurePreserving_comp_injective`) that selecting coordinates along
an injection is measure-preserving between product probability measures.
-/
import Graphons.Sampling.WRandom

open MeasureTheory

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Marginalization along an injection -/

/-- Marginalization: selecting coordinates along an injective map is measure-preserving
    between product probability measures. -/
theorem measurePreserving_comp_injective {V : Type} [Fintype V] [DecidableEq V] {n : ℕ}
    {ψ : V → Fin n} (hψ : Function.Injective ψ) :
    MeasurePreserving (fun x : Fin n → Ω => x ∘ ψ) (piMeasure (Fin n) μ) (piMeasure V μ) := by
  classical
  have hmeas : Measurable fun x : Fin n → Ω => x ∘ ψ :=
    measurable_pi_lambda _ fun v => measurable_pi_apply (ψ v)
  refine ⟨hmeas, ?_⟩
  unfold piMeasure
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  -- The preimage of the box `Π_v s v` is the box over `Fin n` that puts `s v` at `ψ v` and
  -- `univ` off the range of `ψ`.
  have hpre : (fun x : Fin n → Ω => x ∘ ψ) ⁻¹' Set.pi Set.univ s
      = Set.pi Set.univ fun i : Fin n =>
          if h : ∃ v, ψ v = i then s h.choose else Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
    constructor
    · intro hx i
      by_cases h : ∃ v, ψ v = i
      · rw [dif_pos h]
        have := hx h.choose
        rwa [h.choose_spec] at this
      · rw [dif_neg h]
        trivial
    · intro hx v
      have := hx (ψ v)
      rw [dif_pos ⟨v, rfl⟩,
        show (⟨v, rfl⟩ : ∃ u, ψ u = ψ v).choose = v from
          hψ ((⟨v, rfl⟩ : ∃ u, ψ u = ψ v).choose_spec)] at this
      exact this
  rw [hpre, Measure.pi_pi]
  calc (∏ i : Fin n, μ (if h : ∃ v, ψ v = i then s h.choose else Set.univ))
      = ∏ i ∈ Finset.univ.image ψ, μ (if h : ∃ v, ψ v = i then s h.choose else Set.univ) := by
        refine (Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
        rw [dif_neg, measure_univ]
        rintro ⟨v, hv⟩
        exact hi (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩)
    _ = ∏ v : V, μ (if h : ∃ u, ψ u = ψ v then s h.choose else Set.univ) :=
        Finset.prod_image fun a _ b _ hab => hψ hab
    _ = ∏ v : V, μ (s v) := by
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [dif_pos ⟨v, rfl⟩,
          show (⟨v, rfl⟩ : ∃ u, ψ u = ψ v).choose = v from
            hψ ((⟨v, rfl⟩ : ∃ u, ψ u = ψ v).choose_spec)]

/-! ### The exact identity on injective placements -/

/-- Per-edge value: on a non-diagonal pair, the edge probability of the image pair under an
    injective placement is the graphon edge value at the pulled-back point. -/
private theorem edgeProb_map_eq_edgeVal {V : Type} (W : Graphon Ω μ) {n : ℕ}
    {ψ : V → Fin n} (hψ : Function.Injective ψ) (x : Fin n → Ω) {e : Sym2 V}
    (he : ¬e.IsDiag) :
    edgeProb W x (Sym2.map ψ e) = edgeVal W (x ∘ ψ) e := by
  induction e with
  | _ a b =>
    have hab : a ≠ b := fun h => he (Sym2.mk_isDiag_iff.mpr h)
    rw [Sym2.map_mk, edgeProb_mk, if_neg fun h => hab (hψ h)]
    rfl

/-- **The exact sampling identity**: for an INJECTIVE placement `ψ`, the annealed edge
    product integrates to exactly `t(F, W)` — no error term, any `n`, any carrier. -/
theorem integral_edgeProb_image_of_injective {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ}
    {ψ : V → Fin n} (hψ : Function.Injective ψ) :
    ∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e) ∂(piMeasure (Fin n) μ)
      = homDensity F W := by
  classical
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  have hptwise : ∀ x : Fin n → Ω,
      (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
        = homDensityIntegrand F W (x ∘ ψ) := by
    intro x
    rw [Finset.prod_image fun a _ b _ h => Sym2.map.injective hψ h]
    exact Finset.prod_congr rfl fun e he =>
      edgeProb_map_eq_edgeVal W hψ x (F.not_isDiag_of_mem_edgeFinset he)
  have hmp := measurePreserving_comp_injective (μ := μ) hψ
  have hmeas : Measurable fun x : Fin n → Ω => x ∘ ψ :=
    measurable_pi_lambda _ fun v => measurable_pi_apply (ψ v)
  have hsm : AEStronglyMeasurable (homDensityIntegrand F W)
      ((piMeasure (Fin n) μ).map fun x => x ∘ ψ) := by
    rw [hmp.map_eq]
    exact (Graphon.measurable_homDensityIntegrand F W).aestronglyMeasurable
  calc ∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e) ∂(piMeasure (Fin n) μ)
      = ∫ x, homDensityIntegrand F W (x ∘ ψ) ∂(piMeasure (Fin n) μ) :=
        integral_congr_ae (ae_of_all _ hptwise)
    _ = ∫ y, homDensityIntegrand F W y ∂((piMeasure (Fin n) μ).map fun x => x ∘ ψ) :=
        (integral_map hmeas.aemeasurable hsm).symm
    _ = homDensity F W := by rw [hmp.map_eq]; rfl

/-! ### Integrability of the annealed edge products -/

/-- `edgeProb W · e` is a measurable function of the positions. -/
private theorem measurable_edgeProb (W : Graphon Ω μ) {n : ℕ} (e : Sym2 (Fin n)) :
    Measurable fun x : Fin n → Ω => edgeProb W x e := by
  induction e with
  | _ i j =>
    simp only [edgeProb_mk]
    rcases eq_or_ne i j with h | h
    · simp [h]
    · simp only [if_neg h]
      have hm : Measurable (fun x : Fin n → Ω => (Function.uncurry W.toFun) (x i, x j)) :=
        W.meas'.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact hm

/-- The annealed edge product over any pair set is integrable (bounded and measurable on a
    probability space). -/
private theorem integrable_prod_edgeProb (W : Graphon Ω μ) {n : ℕ}
    (S : Finset (Sym2 (Fin n))) :
    Integrable (fun x => ∏ e ∈ S, edgeProb W x e) (piMeasure (Fin n) μ) := by
  refine Integrable.mono' (integrable_const 1) ?_ (ae_of_all _ fun x => ?_)
  · exact (Finset.measurable_prod _ fun e _ => measurable_edgeProb W e).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Finset.prod_nonneg fun e _ => edgeProb_nonneg W x e)]
    exact Finset.prod_le_one (fun e _ => edgeProb_nonneg W x e)
      (fun e _ => edgeProb_le_one W x e)

/-! ### Counting non-injective placements -/

/-- For `a ≠ b`, at most `n ^ (|V| - 1)` maps `ψ : V → Fin n` satisfy `ψ a = ψ b`
    (restriction away from `a` is injective on this set). -/
private theorem card_filter_apply_eq_le {V : Type} [Fintype V] [DecidableEq V] {n : ℕ}
    {a b : V} (hab : a ≠ b) :
    (Finset.univ.filter fun ψ : V → Fin n => ψ a = ψ b).card
      ≤ n ^ (Fintype.card V - 1) := by
  classical
  have key : (Finset.univ.filter fun ψ : V → Fin n => ψ a = ψ b).card
      ≤ (Finset.univ : Finset ({c : V // c ≠ a} → Fin n)).card := by
    refine Finset.card_le_card_of_injOn (fun ψ c => ψ c.1)
      (fun ψ _ => Finset.mem_univ _) ?_
    intro ψ hψ φ hφ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hψ hφ
    funext c
    rcases eq_or_ne c a with rfl | hc
    · rw [hψ, hφ]
      exact congrFun h ⟨b, hab.symm⟩
    · exact congrFun h ⟨c, hc⟩
  have hcard : Fintype.card {c : V // c ≠ a} = Fintype.card V - 1 := by
    simp
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard] at key

/-- At most `(k² - k) · n^(k-1)` maps `ψ : V → Fin n` are non-injective, `k = |V|`. -/
private theorem card_noninjective_le (V : Type) [Fintype V] [DecidableEq V] (n : ℕ) :
    (Finset.univ.filter fun ψ : V → Fin n => ¬Function.Injective ψ).card
      ≤ (Fintype.card V * Fintype.card V - Fintype.card V) * n ^ (Fintype.card V - 1) := by
  classical
  have hsub : (Finset.univ.filter fun ψ : V → Fin n => ¬Function.Injective ψ)
      ⊆ (Finset.univ : Finset V).offDiag.biUnion
          (fun p => Finset.univ.filter fun ψ : V → Fin n => ψ p.1 = ψ p.2) := by
    intro ψ hψ
    have hni : ¬Function.Injective ψ := (Finset.mem_filter.mp hψ).2
    rw [Function.not_injective_iff] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact Finset.mem_biUnion.mpr ⟨(a, b),
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
  calc (Finset.univ.filter fun ψ : V → Fin n => ¬Function.Injective ψ).card
      ≤ ((Finset.univ : Finset V).offDiag.biUnion
          (fun p => Finset.univ.filter fun ψ : V → Fin n => ψ p.1 = ψ p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ (Finset.univ : Finset V).offDiag,
          (Finset.univ.filter fun ψ : V → Fin n => ψ p.1 = ψ p.2).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ (Finset.univ : Finset V).offDiag, n ^ (Fintype.card V - 1) :=
        Finset.sum_le_sum fun p hp =>
          card_filter_apply_eq_le (Finset.mem_offDiag.mp hp).2.2
    _ = (Fintype.card V * Fintype.card V - Fintype.card V) * n ^ (Fintype.card V - 1) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.offDiag_card, Finset.card_univ]

/-! ### The first sampling lemma, expectation form -/

/-- Per-placement bound: the annealed integral is exactly `t(F,W)` on injective `ψ`, and lies
    in `[0,1]` (hence within `1` of `t(F,W)`) otherwise. -/
private theorem abs_integral_sub_homDensity_le {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ} (ψ : V → Fin n) :
    |(∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e) ∂(piMeasure (Fin n) μ))
        - homDensity F W|
      ≤ if Function.Injective ψ then 0 else 1 := by
  by_cases h : Function.Injective ψ
  · simp [integral_edgeProb_image_of_injective F W h, h]
  · rw [if_neg h, abs_sub_le_iff]
    have h0 : 0 ≤ ∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
        ∂(piMeasure (Fin n) μ) :=
      integral_nonneg fun x => Finset.prod_nonneg fun e _ => edgeProb_nonneg W x e
    have h1 : (∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
        ∂(piMeasure (Fin n) μ)) ≤ 1 := by
      calc (∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
            ∂(piMeasure (Fin n) μ))
          ≤ ∫ _x, (1 : ℝ) ∂(piMeasure (Fin n) μ) :=
            integral_mono (integrable_prod_edgeProb W _) (integrable_const 1)
              (fun x => Finset.prod_le_one (fun e _ => edgeProb_nonneg W x e)
                (fun e _ => edgeProb_le_one W x e))
        _ = 1 := by simp
    have ht := Graphon.homDensity_mem_Icc F W
    constructor <;> linarith [ht.1, ht.2]

/-- The expected homomorphism density of the W-random graph (vertex sample + edge coins). -/
noncomputable def expectedHomDensity {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) (n : ℕ) [NeZero n] : ℝ :=
  ∫ x, (∫ ω, homDensity F (Graphon.step (coinGraph ω)) ∂(coinMeasure W x))
    ∂(piMeasure (Fin n) μ)

/-- **First sampling lemma, expectation form**: the expected hom density of `𝔾(n,W)` is
    `t(F,W)` up to the non-injectivity defect `k(k−1)/n`. -/
theorem abs_expectedHomDensity_sub_le {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ} [NeZero n] :
    |expectedHomDensity F W n - homDensity F W|
      ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / (n : ℝ) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hnk : (0 : ℝ) < (n : ℝ) ^ (Fintype.card V) := pow_pos hnpos _
  -- Closed form for the expectation, by the conditional identity plus the sum split.
  have hE : expectedHomDensity F W n
      = (∑ ψ : V → Fin n,
          ∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
            ∂(piMeasure (Fin n) μ)) / (n : ℝ) ^ (Fintype.card V) := by
    simp only [expectedHomDensity, integral_coin_homDensity]
    rw [integral_div, integral_finsetSum _ fun ψ _ => integrable_prod_edgeProb W _]
  -- Center the sum at `t(F,W)`.
  have hcardfun : ((Finset.univ : Finset (V → Fin n)).card : ℝ)
      = (n : ℝ) ^ (Fintype.card V) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rfl
  have hsplit : expectedHomDensity F W n - homDensity F W
      = (∑ ψ : V → Fin n,
          ((∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
            ∂(piMeasure (Fin n) μ)) - homDensity F W)) / (n : ℝ) ^ (Fintype.card V) := by
    rw [hE, Finset.sum_sub_distrib, sub_div]
    congr 1
    rw [Finset.sum_const, nsmul_eq_mul, hcardfun,
      mul_div_cancel_left₀ (homDensity F W) hnk.ne']
  -- Sum the per-placement bounds over the non-injective placements.
  have hsumb : (∑ ψ : V → Fin n,
        |(∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
          ∂(piMeasure (Fin n) μ)) - homDensity F W|)
      ≤ ((Finset.univ.filter fun ψ : V → Fin n => ¬Function.Injective ψ).card : ℝ) := by
    calc (∑ ψ : V → Fin n,
          |(∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
            ∂(piMeasure (Fin n) μ)) - homDensity F W|)
        ≤ ∑ ψ : V → Fin n, (if Function.Injective ψ then (0 : ℝ) else 1) :=
          Finset.sum_le_sum fun ψ _ => abs_integral_sub_homDensity_le F W ψ
      _ = ((Finset.univ.filter fun ψ : V → Fin n => ¬Function.Injective ψ).card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
            nsmul_eq_mul, mul_one]
  -- The counting bound, cast to `ℝ`.
  have hcount : ((Finset.univ.filter fun ψ : V → Fin n => ¬Function.Injective ψ).card : ℝ)
      ≤ ((Fintype.card V * Fintype.card V - Fintype.card V : ℕ) : ℝ)
          * (n : ℝ) ^ (Fintype.card V - 1) := by
    calc ((Finset.univ.filter fun ψ : V → Fin n => ¬Function.Injective ψ).card : ℝ)
        ≤ (((Fintype.card V * Fintype.card V - Fintype.card V)
            * n ^ (Fintype.card V - 1) : ℕ) : ℝ) :=
          Nat.cast_le.mpr (card_noninjective_le V n)
      _ = ((Fintype.card V * Fintype.card V - Fintype.card V : ℕ) : ℝ)
            * (n : ℝ) ^ (Fintype.card V - 1) := by push_cast; ring
  -- Final arithmetic.
  calc |expectedHomDensity F W n - homDensity F W|
      ≤ (∑ ψ : V → Fin n,
          |(∫ x, (∏ e ∈ F.edgeFinset.image (Sym2.map ψ), edgeProb W x e)
            ∂(piMeasure (Fin n) μ)) - homDensity F W|) / (n : ℝ) ^ (Fintype.card V) := by
        rw [hsplit, abs_div, abs_of_pos hnk]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((Fintype.card V * Fintype.card V - Fintype.card V : ℕ) : ℝ)
          * (n : ℝ) ^ (Fintype.card V - 1) / (n : ℝ) ^ (Fintype.card V) := by
        gcongr
        exact hsumb.trans hcount
    _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / (n : ℝ) := by
        rcases Nat.eq_zero_or_pos (Fintype.card V) with hk0 | hkpos
        · simp [hk0]
        · have hsub : ((Fintype.card V * Fintype.card V - Fintype.card V : ℕ) : ℝ)
              = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) - (Fintype.card V : ℝ) := by
            rw [Nat.cast_sub (Nat.le_mul_of_pos_left (Fintype.card V) hkpos)]
            push_cast
            ring
          have hpow : (n : ℝ) ^ (Fintype.card V)
              = (n : ℝ) * (n : ℝ) ^ (Fintype.card V - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [hsub, hpow, mul_comm (n : ℝ) ((n : ℝ) ^ (Fintype.card V - 1)), ← div_div,
            mul_div_cancel_right₀ _ (pow_pos hnpos (Fintype.card V - 1)).ne', mul_sub, mul_one]

/-- The expected hom densities converge to `t(F,W)` as `n → ∞`. -/
theorem tendsto_expectedHomDensity {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    Filter.Tendsto (fun n : ℕ => expectedHomDensity F W (n + 1)) Filter.atTop
      (nhds (homDensity F W)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  refine squeeze_zero
    (g := fun m : ℕ => (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / ((m + 1 : ℕ) : ℝ))
    (fun m => abs_nonneg _) (fun m => abs_expectedHomDensity_sub_le F W) ?_
  exact (Filter.tendsto_add_atTop_iff_nat 1).mpr
    (tendsto_const_div_atTop_nhds_zero_nat ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)))

end Graphons
