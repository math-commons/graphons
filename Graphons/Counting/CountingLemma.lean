/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits):
  The **counting lemma inequality** (the cut-norm ↔ homomorphism-density bridge):
    |t(F, U) − t(F, W)| ≤ e(F) · ‖U − W‖□.
  Sources: Lovász, "Large Networks and Graph Limits" (2012), Lemma 10.23 ("Counting Lemma");
  Borgs–Chayes–Lovász–Sós–Vesztergombi (2007).

The proof telescopes the product over the edges of `F`, replacing one edge factor at a time, so
that the difference `t(F,U) − t(F,W)` is a sum of `e(F)` terms, each of which replaces a single
edge's factor by `(U − W)`.  Each such term is bounded by `‖U − W‖□` using the cut-norm test-
function inequality `le_cutNorm` (this step crucially uses that `F` is a *simple* graph, so no two
distinct edges join the same pair of vertices, which lets the remaining product factor through the
two endpoints of the chosen edge).
-/
import Graphons.CutMetric.CutNorm
import Graphons.Core.Basic

open MeasureTheory

namespace Graphons

open Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {V : Type*} [Fintype V]

/-- The "mixed product" over a set `T` of edges: `U`-values on `Tu`, `W`-values on the rest.
    This is the integrand factor that multiplies the difference at the telescoped edge. -/
noncomputable def mixedProd (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) : ℝ :=
  (∏ e ∈ Tu, edgeVal U x e) * ∏ e ∈ Tw, edgeVal W x e

theorem mixedProd_nonneg (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) :
    0 ≤ mixedProd U W Tu Tw x :=
  mul_nonneg (Finset.prod_nonneg fun e _ => edgeVal_nonneg U x e)
    (Finset.prod_nonneg fun e _ => edgeVal_nonneg W x e)

theorem mixedProd_le_one (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) :
    mixedProd U W Tu Tw x ≤ 1 := by
  have h1 : (∏ e ∈ Tu, edgeVal U x e) ≤ 1 :=
    Finset.prod_le_one (fun e _ => edgeVal_nonneg U x e) (fun e _ => edgeVal_le_one U x e)
  have h2 : (∏ e ∈ Tw, edgeVal W x e) ≤ 1 :=
    Finset.prod_le_one (fun e _ => edgeVal_nonneg W x e) (fun e _ => edgeVal_le_one W x e)
  have h1' : 0 ≤ (∏ e ∈ Tu, edgeVal U x e) := Finset.prod_nonneg fun e _ => edgeVal_nonneg U x e
  calc mixedProd U W Tu Tw x ≤ 1 * 1 :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun e _ => edgeVal_nonneg W x e) zero_le_one
    _ = 1 := by ring

/-! ### Telescoping the product over edges

We telescope `∏ f − ∏ g` over a finset into a sum of single-factor differences.  We carry, for each
edge `e`, an explicit pair of finsets `(Tu e, Tw e) ⊆ s.erase e` describing which of the remaining
factors use `U` and which use `W`, so that the per-edge term is
`(edgeVal U x e − edgeVal W x e) · mixedProd U W (Tu e) (Tw e) x`.
This `mixedProd` factor lies in `[0,1]`, and (since `Tu e, Tw e ⊆ s.erase e`) involves only edges
distinct from `e` — the property the cut-norm bound needs. -/

/-- The telescoping data: for the difference of products `∏_{e∈s} f − ∏_{e∈s} g` (with `f, g` the
    edge-values of `U, W`), there exist edge-indexed finsets `Tu, Tw` with `Tu e, Tw e ⊆ s.erase e`
    such that the difference equals `Σ_{e∈s} (f e − g e) · mixedProd U W (Tu e) (Tw e) x` for all
    `x`.  Proved by induction on `s`. -/
theorem exists_edge_telescope [DecidableEq V] (U W : Graphon Ω μ) (s : Finset (Sym2 V)) :
    ∃ Tu Tw : Sym2 V → Finset (Sym2 V),
      (∀ e ∈ s, Tu e ⊆ s.erase e) ∧ (∀ e ∈ s, Tw e ⊆ s.erase e) ∧
      ∀ x : V → Ω,
        (∏ e ∈ s, edgeVal U x e) - ∏ e ∈ s, edgeVal W x e =
          ∑ e ∈ s, (edgeVal U x e - edgeVal W x e) * mixedProd U W (Tu e) (Tw e) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact ⟨fun _ => ∅, fun _ => ∅, by simp, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨Tu, Tw, hTu, hTw, hsum⟩ := ih
    -- For the new edge `a`: factor `∏_{s} f` (all of `s` uses `U`).
    -- For old edges `e ∈ s`: prepend the constant factor `g a = edgeVal W x a`, i.e. add `a` to Tw.
    refine ⟨fun e => if e = a then s else Tu e,
            fun e => if e = a then ∅ else insert a (Tw e), ?_, ?_, ?_⟩
    · intro e he
      rcases eq_or_ne e a with rfl | hea
      · simp only [if_pos rfl]
        intro y hy
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_insert_of_mem hy⟩
        rintro rfl; exact ha hy
      · simp only [if_neg hea]
        refine (hTu e (Finset.mem_of_mem_insert_of_ne he hea)).trans ?_
        exact Finset.erase_subset_erase _ (Finset.subset_insert _ _)
    · intro e he
      rcases eq_or_ne e a with rfl | hea
      · simp
      · simp only [if_neg hea]
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy'
        · refine Finset.mem_erase.2 ⟨fun h => hea h.symm, ?_⟩
          exact Finset.mem_insert_self _ _
        · have := hTw e (Finset.mem_of_mem_insert_of_ne he hea) hy'
          rw [Finset.mem_erase] at this ⊢
          exact ⟨this.1, Finset.mem_insert_of_mem this.2⟩
    · intro x
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have key : (edgeVal U x a) * ∏ e ∈ s, edgeVal U x e
            - (edgeVal W x a) * ∏ e ∈ s, edgeVal W x e
          = (edgeVal U x a - edgeVal W x a) * (∏ e ∈ s, edgeVal U x e)
            + (edgeVal W x a) * ((∏ e ∈ s, edgeVal U x e) - ∏ e ∈ s, edgeVal W x e) := by
        ring
      rw [key, hsum x]
      -- First summand: matches the `a` term with Tu a = s, Tw a = ∅.
      simp only [if_pos rfl]
      congr 1
      · rw [mixedProd]; simp
      -- Second summand: distribute `edgeVal W x a` into each old term, absorbing into Tw via insert.
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e he => ?_)
        have hne : e ≠ a := fun h => ha (h ▸ he)
        rw [if_neg hne, if_neg hne]
        have hnotin : a ∉ Tw e := fun h => ha (Finset.mem_of_mem_erase (hTw e he h))
        rw [mixedProd, mixedProd, Finset.prod_insert hnotin]
        ring

/-! ### The per-edge cut-norm bound (the factorization step)

For a single edge `e₀ = s(a, b)` of a *simple* graph `F`, and any `[0,1]`-valued `mixedProd` factor
over edges `≠ e₀`, the integral of `(U − W)(x_a, x_b) · mixedProd …` over `V → Ω` is bounded by
`cutNorm (U − W)`.

The proof fixes all coordinates other than `x_a, x_b` (Fubini on `piMeasure`), at which point the
`mixedProd` factor becomes `γ · α(x_a) · β(x_b)` with `α, β` test functions of a single variable
(`α` collects the edges incident to `a`, `β` those incident to `b`, `γ` the rest — these are
disjoint *because `F` is simple*, so no edge `≠ e₀` joins `a` and `b`).  Then `le_cutNorm` bounds the
inner double integral by `cutNorm (U − W)`, and integrating the outer `γ ∈ [0,1]` against the
probability measure keeps the bound.

This is the genuine analytic crux of the counting lemma. -/

/-- The single-edge integrand: the difference `(U − W)` evaluated at the endpoints of `e₀`, times the
    mixed product over the remaining edges. -/
noncomputable def perEdgeIntegrand (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (e₀ : Sym2 V)
    (x : V → Ω) : ℝ :=
  (edgeVal U x e₀ - edgeVal W x e₀) * mixedProd U W Tu Tw x

/-! ### Factorization of the mixed product at the two endpoints

Fix `x : V → Ω`, two distinct vertices `a ≠ b`, and a finset of edges none of which contains both
`a` and `b`.  Updating `x` at `a` to `s` and at `b` to `t`, the mixed product factors as
`γ · α s · β t`, where `α` (resp. `β`) collects the factors from edges incident to `a` (resp. `b`),
and `γ` the factors from edges incident to neither.  These three groups partition the edge set
because no edge contains both `a` and `b`. -/

variable [DecidableEq V]

/-- `restAt x a b s t` is `x` with the `a`-coordinate set to `s` and the `b`-coordinate set to `t`. -/
noncomputable def restAt (x : V → Ω) (a b : V) (s t : Ω) : V → Ω :=
  Function.update (Function.update x a s) b t

/-- **Single-coordinate re-randomization (integral).**  Re-drawing one coordinate `i` of a point
    from the product measure does not change the integral of an integrable function.  Proved by
    splitting off the `i`-coordinate via `piEquivPiSubtypeProd (· = i)` (so the product measure
    becomes `μ^{⊗{i}} × μ^{⊗{≠i}}`), `integral_prod_symm`, and collapsing the singleton factor with
    `measurePreserving_piUnique` (bridging the two `Fintype {j // j = i}` instances by
    `Subsingleton.elim`). -/
theorem integral_rerandomize_one (i : V) (g : (V → Ω) → ℝ)
    (hg : Integrable g (piMeasure V μ)) :
    ∫ x, g x ∂(piMeasure V μ)
      = ∫ x, (∫ s, g (Function.update x i s) ∂μ) ∂(piMeasure V μ) := by
  classical
  rw [piMeasure]
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) (· = i)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => Ω) (· = i) with he
  have hsymm : ∀ (a : {x : V // x = i} → Ω) (b : {x : V // ¬ x = i} → Ω) (j : V),
      e.symm (a, b) j = if h : j = i then a ⟨j, h⟩ else b ⟨j, h⟩ := fun a b j => rfl
  have hupdate : ∀ (a : {x : V // x = i} → Ω) (b : {x : V // ¬ x = i} → Ω) (s : Ω),
      Function.update (e.symm (a, b)) i s = e.symm ((fun _ => s), b) := by
    intro a b s
    funext j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, hsymm]; simp
    · rw [Function.update_of_ne hj, hsymm, hsymm]; simp [hj]
  have lhs : ∫ x, g x ∂(Measure.pi (fun _ : V => μ))
      = ∫ y, g (e.symm y) ∂((Measure.pi (fun _ : V => μ)).map e) := by
    rw [integral_map_equiv]; simp
  have rhs : ∫ x, (∫ s, g (Function.update x i s) ∂μ) ∂(Measure.pi (fun _ : V => μ))
      = ∫ y, (∫ s, g (Function.update (e.symm y) i s) ∂μ)
          ∂((Measure.pi (fun _ : V => μ)).map e) := by
    rw [integral_map_equiv]; simp
  rw [lhs, rhs, hmp.map_eq]
  have hF : Integrable (fun y => g (e.symm y)) ((Measure.pi (fun _ : V => μ)).map e) := by
    rw [show (fun y => g (e.symm y)) = g ∘ e.symm from rfl, integrable_map_equiv]
    have : (g ∘ ⇑e.symm) ∘ ⇑e = g := by funext x; simp
    rw [this]; exact hg
  rw [hmp.map_eq] at hF
  rw [integral_prod_symm _ hF]
  have hRsnd : (fun y : ({x : V // x = i} → Ω) × ({x : V // ¬ x = i} → Ω) =>
        ∫ s, g (Function.update (e.symm y) i s) ∂μ)
      = (fun y => (fun b => ∫ s, g (e.symm ((fun _ => s), b)) ∂μ) y.2) := by
    funext y
    apply integral_congr_ae
    filter_upwards with s
    rw [hupdate]
  rw [hRsnd, integral_fun_snd (f := fun b => ∫ s, g (e.symm ((fun _ => s), b)) ∂μ)]
  simp only [measureReal_univ_eq_one, one_smul]
  apply integral_congr_ae
  filter_upwards with b
  have hcollapse : ∀ (Φ : ({x : V // x = i} → Ω) → ℝ),
      ∫ a, Φ a ∂(@Measure.pi {x : V // x = i} (fun _ => Ω) (Subtype.fintype _) _ (fun _ => μ))
        = ∫ s, Φ (fun _ => s) ∂μ := by
    intro Φ
    have hinst : (Subtype.fintype (fun x => x = i) : Fintype {x : V // x = i})
        = Fintype.subtypeEq i := Subsingleton.elim _ _
    rw [hinst]
    have hmpu := measurePreserving_piUnique (fun _ : {x : V // x = i} => μ)
    rw [← hmpu.integral_comp' (g := fun s => Φ (fun _ => s))]
    refine integral_congr_ae (G := ℝ) (Filter.Eventually.of_forall fun a => ?_)
    exact congrArg Φ (funext fun j => congrArg a (Subsingleton.elim _ _))
  exact hcollapse (fun a => g (e.symm (a, b)))

/-- **Single-coordinate re-randomization (integrability).**  The function obtained by integrating out
    one coordinate of an integrable function is again integrable against the product measure. -/
theorem integrable_rerandomize_one (i : V) (g : (V → Ω) → ℝ)
    (hg : Integrable g (piMeasure V μ)) :
    Integrable (fun x => ∫ s, g (Function.update x i s) ∂μ) (piMeasure V μ) := by
  classical
  rw [piMeasure] at hg ⊢
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) (· = i)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => Ω) (· = i) with he
  have hsymm : ∀ (a : {x : V // x = i} → Ω) (b : {x : V // ¬ x = i} → Ω) (j : V),
      e.symm (a, b) j = if h : j = i then a ⟨j, h⟩ else b ⟨j, h⟩ := fun a b j => rfl
  have hupdate : ∀ (a : {x : V // x = i} → Ω) (b : {x : V // ¬ x = i} → Ω) (s : Ω),
      Function.update (e.symm (a, b)) i s = e.symm ((fun _ => s), b) := by
    intro a b s
    funext j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, hsymm]; simp
    · rw [Function.update_of_ne hj, hsymm, hsymm]; simp [hj]
  have hF : Integrable (fun y => g (e.symm y)) ((Measure.pi (fun _ : V => μ)).map e) := by
    rw [show (fun y => g (e.symm y)) = g ∘ e.symm from rfl, integrable_map_equiv]
    have : (g ∘ ⇑e.symm) ∘ ⇑e = g := by funext x; simp
    rw [this]; exact hg
  rw [hmp.map_eq] at hF
  rw [show (fun x => ∫ s, g (Function.update x i s) ∂μ)
        = (fun y => ∫ s, g (Function.update (e.symm y) i s) ∂μ) ∘ e by funext x; simp,
      ← integrable_map_equiv e _, hmp.map_eq]
  have hHint : Integrable
      (fun b => ∫ a, g (e.symm (a, b))
        ∂(@Measure.pi {x : V // x = i} (fun _ => Ω) (Subtype.fintype _) _ (fun _ => μ)))
      (Measure.pi (fun _ : {x : V // ¬ x = i} => μ)) :=
    hF.integral_prod_right
  refine (hHint.comp_snd
    (@Measure.pi {x : V // x = i} (fun _ => Ω) (Subtype.fintype _) _ (fun _ => μ))).congr ?_
  filter_upwards with y
  have hinst : (Subtype.fintype (fun x => x = i) : Fintype {x : V // x = i})
      = Fintype.subtypeEq i := Subsingleton.elim _ _
  show ∫ a, g (e.symm (a, y.2))
        ∂(@Measure.pi {x : V // x = i} (fun _ => Ω) (Subtype.fintype _) _ (fun _ => μ))
      = ∫ s, g (Function.update (e.symm y) i s) ∂μ
  rw [hinst]
  have hmpu := measurePreserving_piUnique (fun _ : {x : V // x = i} => μ)
  rw [← hmpu.integral_comp' (g := fun s => g (Function.update (e.symm y) i s))]
  refine integral_congr_ae (G := ℝ) (Filter.Eventually.of_forall fun a => ?_)
  show g (e.symm (a, y.2)) = g (Function.update (e.symm y) i ((MeasurableEquiv.piUnique fun _ => Ω) a))
  have hy : e.symm y = e.symm (y.1, y.2) := rfl
  rw [hy, hupdate]
  exact congrArg (fun z => g (e.symm (z, y.2))) (funext fun j => congrArg a (Subsingleton.elim _ _))

/-- The `α`-factor: the part of the mixed product from edges incident to `a`, as a function of the
    `a`-coordinate `s` (we only update `a`, since these edges do not contain `b`). -/
noncomputable def mixedAlpha (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (a : V)
    (s : Ω) : ℝ :=
  (∏ e ∈ Tu.filter (a ∈ ·), edgeVal U (Function.update x a s) e) *
    ∏ e ∈ Tw.filter (a ∈ ·), edgeVal W (Function.update x a s) e

/-- The `β`-factor: the part of the mixed product from edges incident to `b`, as a function of the
    `b`-coordinate `t`. -/
noncomputable def mixedBeta (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (b : V)
    (t : Ω) : ℝ :=
  (∏ e ∈ Tu.filter (b ∈ ·), edgeVal U (Function.update x b t) e) *
    ∏ e ∈ Tw.filter (b ∈ ·), edgeVal W (Function.update x b t) e

/-- The `γ`-factor: the part of the mixed product from edges incident to neither `a` nor `b`. -/
noncomputable def mixedGamma (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (a b : V) :
    ℝ :=
  (∏ e ∈ Tu.filter (fun e => a ∉ e ∧ b ∉ e), edgeVal U x e) *
    ∏ e ∈ Tw.filter (fun e => a ∉ e ∧ b ∉ e), edgeVal W x e

/-- `edgeVal` depends only on the values of `x` at the two endpoints of the edge: if `y` and `z`
    agree on every vertex contained in `e`, then `edgeVal G y e = edgeVal G z e`. -/
theorem edgeVal_congr (G : Graphon Ω μ) {y z : V → Ω} {e : Sym2 V}
    (h : ∀ v ∈ e, y v = z v) : edgeVal G y e = edgeVal G z e := by
  induction e with
  | _ c d =>
    simp only [edgeVal, Sym2.lift_mk]
    rw [h c (Sym2.mem_mk_left c d), h d (Sym2.mem_mk_right c d)]

/-- For an edge containing `a` but not `b`, the `restAt` update agrees with updating only `a`. -/
theorem edgeVal_restAt_of_mem_left (G : Graphon Ω μ) (x : V → Ω) {a b : V} (hab : a ≠ b)
    {s t : Ω} {e : Sym2 V} (hb : b ∉ e) :
    edgeVal G (restAt x a b s t) e = edgeVal G (Function.update x a s) e := by
  refine edgeVal_congr G (fun v hv => ?_)
  have hvb : v ≠ b := fun h => hb (h ▸ hv)
  simp [restAt, Function.update_of_ne hvb]
  -- target: `update (update x a s) b t v = update x a s v` with `v ≠ b`; the outer `b`-update drops.

/-- For an edge containing `b` but not `a`, the `restAt` update agrees with updating only `b`. -/
theorem edgeVal_restAt_of_mem_right (G : Graphon Ω μ) (x : V → Ω) {a b : V} (hab : a ≠ b)
    {s t : Ω} {e : Sym2 V} (ha : a ∉ e) :
    edgeVal G (restAt x a b s t) e = edgeVal G (Function.update x b t) e := by
  refine edgeVal_congr G (fun v hv => ?_)
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  simp only [restAt, Function.update_apply]
  by_cases hvb : v = b <;> simp [hvb, hva]

/-- For an edge containing neither `a` nor `b`, the `restAt` update agrees with `x`. -/
theorem edgeVal_restAt_of_not_mem (G : Graphon Ω μ) (x : V → Ω) {a b : V}
    {s t : Ω} {e : Sym2 V} (ha : a ∉ e) (hb : b ∉ e) :
    edgeVal G (restAt x a b s t) e = edgeVal G x e := by
  refine edgeVal_congr G (fun v hv => ?_)
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  have hvb : v ≠ b := fun h => hb (h ▸ hv)
  simp [restAt, Function.update_of_ne hva, Function.update_of_ne hvb]

/-- Single-graphon product factorization: over a finset `T` of edges, none containing both `a` and
    `b`, the product of `edgeVal G (restAt …)` splits into the `a`-incident, `b`-incident, and
    neither-incident sub-products (each evaluated with the appropriate single/no update). -/
theorem prod_edgeVal_restAt_factor (G : Graphon Ω μ) (x : V → Ω) {a b : V} (hab : a ≠ b)
    (s t : Ω) (T : Finset (Sym2 V)) (hT : ∀ e ∈ T, ¬(a ∈ e ∧ b ∈ e)) :
    (∏ e ∈ T, edgeVal G (restAt x a b s t) e) =
      (∏ e ∈ T.filter (a ∈ ·), edgeVal G (Function.update x a s) e) *
      ((∏ e ∈ T.filter (b ∈ ·), edgeVal G (Function.update x b t) e) *
        (∏ e ∈ T.filter (fun e => a ∉ e ∧ b ∉ e), edgeVal G x e)) := by
  classical
  -- Group the three filters: a-incident, b-incident (⇒ a∉e), neither.  Since no edge has both
  -- `a` and `b`, the b-incident filter `(b ∈ ·)` over T coincides with `(a ∉ · ∧ b ∈ ·)`.
  have hb_filter : T.filter (b ∈ ·) = T.filter (fun e => a ∉ e ∧ b ∈ e) := by
    apply Finset.filter_congr
    intro e he
    have := hT e he
    constructor
    · intro hb; exact ⟨fun ha => this ⟨ha, hb⟩, hb⟩
    · rintro ⟨_, hb⟩; exact hb
  -- Split T into a-incident and not-a-incident.
  rw [← Finset.prod_filter_mul_prod_filter_not T (a ∈ ·)]
  congr 1
  · -- a-incident edges: b ∉ e, so restAt = update x a s.
    refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    have hb : b ∉ e := fun hbe => hT e he.1 ⟨he.2, hbe⟩
    exact edgeVal_restAt_of_mem_left G x hab hb
  · -- remaining edges (a ∉ e): split into b-incident and neither.
    rw [hb_filter]
    rw [← Finset.prod_filter_mul_prod_filter_not (T.filter (¬ a ∈ ·)) (b ∈ ·)]
    rw [Finset.filter_filter, Finset.filter_filter]
    congr 1
    · -- b-incident edges (with a ∉ e): restAt = update x b t.
      refine Finset.prod_congr (Finset.filter_congr (fun e _ => by simp [and_comm])) (fun e he => ?_)
      rw [Finset.mem_filter] at he
      exact edgeVal_restAt_of_mem_right G x hab he.2.1
    · -- neither-incident edges.
      refine Finset.prod_congr (Finset.filter_congr (fun e _ => by simp)) (fun e he => ?_)
      rw [Finset.mem_filter] at he
      exact edgeVal_restAt_of_not_mem G x he.2.1 he.2.2

/-- **Mixed-product factorization at the endpoints.**  When no edge in `Tu ∪ Tw` contains both `a`
    and `b`, updating `x` at `a → s`, `b → t` factors the mixed product as `γ · α s · β t`. -/
theorem mixedProd_restAt_factor (U W : Graphon Ω μ) (x : V → Ω) {a b : V} (hab : a ≠ b)
    (s t : Ω) (Tu Tw : Finset (Sym2 V))
    (hTu : ∀ e ∈ Tu, ¬(a ∈ e ∧ b ∈ e)) (hTw : ∀ e ∈ Tw, ¬(a ∈ e ∧ b ∈ e)) :
    mixedProd U W Tu Tw (restAt x a b s t) =
      mixedGamma U W Tu Tw x a b * mixedAlpha U W Tu Tw x a s * mixedBeta U W Tu Tw x b t := by
  rw [mixedProd, prod_edgeVal_restAt_factor U x hab s t Tu hTu,
    prod_edgeVal_restAt_factor W x hab s t Tw hTw, mixedGamma, mixedAlpha, mixedBeta]
  ring

/-! ### The factors `α, β` are test functions and `γ ∈ [0,1]`. -/

section FactorBounds

variable [MeasurableSpace V]

theorem measurable_mixedAlpha (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (a : V) :
    Measurable (mixedAlpha U W Tu Tw x a) := by
  unfold mixedAlpha
  refine Measurable.mul (Finset.measurable_prod _ (fun e _ => ?_))
    (Finset.measurable_prod _ (fun e _ => ?_))
  · exact (measurable_edgeVal U e).comp (measurable_update x)
  · exact (measurable_edgeVal W e).comp (measurable_update x)

theorem measurable_mixedBeta (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (b : V) :
    Measurable (mixedBeta U W Tu Tw x b) := by
  unfold mixedBeta
  refine Measurable.mul (Finset.measurable_prod _ (fun e _ => ?_))
    (Finset.measurable_prod _ (fun e _ => ?_))
  · exact (measurable_edgeVal U e).comp (measurable_update x)
  · exact (measurable_edgeVal W e).comp (measurable_update x)

end FactorBounds

/-- `mixedAlpha` is `[0,1]`-valued, hence a test function. -/
theorem mixedAlpha_mem_Icc (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (a : V)
    (s : Ω) : mixedAlpha U W Tu Tw x a s ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg (Finset.prod_nonneg fun e _ => edgeVal_nonneg U _ e)
    (Finset.prod_nonneg fun e _ => edgeVal_nonneg W _ e), ?_⟩
  refine mul_le_one₀ (Finset.prod_le_one (fun e _ => edgeVal_nonneg U _ e)
      (fun e _ => edgeVal_le_one U _ e)) (Finset.prod_nonneg fun e _ => edgeVal_nonneg W _ e)
    (Finset.prod_le_one (fun e _ => edgeVal_nonneg W _ e) (fun e _ => edgeVal_le_one W _ e))

/-- `mixedBeta` is `[0,1]`-valued, hence a test function. -/
theorem mixedBeta_mem_Icc (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (b : V)
    (t : Ω) : mixedBeta U W Tu Tw x b t ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg (Finset.prod_nonneg fun e _ => edgeVal_nonneg U _ e)
    (Finset.prod_nonneg fun e _ => edgeVal_nonneg W _ e), ?_⟩
  refine mul_le_one₀ (Finset.prod_le_one (fun e _ => edgeVal_nonneg U _ e)
      (fun e _ => edgeVal_le_one U _ e)) (Finset.prod_nonneg fun e _ => edgeVal_nonneg W _ e)
    (Finset.prod_le_one (fun e _ => edgeVal_nonneg W _ e) (fun e _ => edgeVal_le_one W _ e))

/-- `mixedGamma ∈ [0,1]`. -/
theorem mixedGamma_mem_Icc (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (x : V → Ω) (a b : V) :
    mixedGamma U W Tu Tw x a b ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg (Finset.prod_nonneg fun e _ => edgeVal_nonneg U _ e)
    (Finset.prod_nonneg fun e _ => edgeVal_nonneg W _ e), ?_⟩
  refine mul_le_one₀ (Finset.prod_le_one (fun e _ => edgeVal_nonneg U _ e)
      (fun e _ => edgeVal_le_one U _ e)) (Finset.prod_nonneg fun e _ => edgeVal_nonneg W _ e)
    (Finset.prod_le_one (fun e _ => edgeVal_nonneg W _ e) (fun e _ => edgeVal_le_one W _ e))

/-- **Core analytic bound.**  For any symmetric kernel `D`, scalar `γ ∈ [0,1]`, and test functions
    `α, β`, the double integral `∫∫ D(s,t) γ α(s) β(t)` is bounded in absolute value by `cutNorm D`.
    Proof: `γ • α` is again a test function, so this is exactly `le_cutNorm`. -/
theorem abs_inner_integral_le_cutNorm (D : SymmKernel Ω μ) {γ : ℝ} (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    {α β : Ω → ℝ} (hα : IsTestFun α) (hβ : IsTestFun β) :
    |∫ p, D.toFun p.1 p.2 * (γ * α p.1 * β p.2) ∂(μ.prod μ)| ≤ cutNorm D := by
  -- Rewrite the integrand as `D(p.1,p.2) * (γ•α)(p.1) * β(p.2)`.
  have hγα : IsTestFun (fun s => γ * α s) := by
    refine ⟨measurable_const.mul hα.measurable, fun s => ⟨?_, ?_⟩⟩
    · exact mul_nonneg hγ.1 (hα.nonneg s)
    · calc γ * α s ≤ 1 * 1 := mul_le_mul hγ.2 (hα.le_one s) (hα.nonneg s) zero_le_one
        _ = 1 := one_mul 1
  have heq : (fun p : Ω × Ω => D.toFun p.1 p.2 * (γ * α p.1 * β p.2))
      = fun p : Ω × Ω => D.toFun p.1 p.2 * (γ * α p.1) * β p.2 := by
    funext p; ring
  rw [heq]
  exact le_cutNorm D hγα hβ

/-- The per-edge integrand is bounded by `2` in absolute value (the difference is in `[-1,1]`, the
    mixed product in `[0,1]`), hence integrable. -/
theorem integrable_perEdgeIntegrand [MeasurableSpace V] [MeasurableSingletonClass V]
    (U W : Graphon Ω μ) (Tu Tw : Finset (Sym2 V)) (e₀ : Sym2 V) :
    Integrable (perEdgeIntegrand U W Tu Tw e₀) (piMeasure V μ) := by
  refine SymmKernel.integrable_of_bdd ?_ (C := 2) (fun x => ?_)
  · refine ((measurable_edgeVal U e₀).sub (measurable_edgeVal W e₀)).mul ?_
    refine (Finset.measurable_prod _ (fun e _ => measurable_edgeVal U e)).mul ?_
    exact Finset.measurable_prod _ (fun e _ => measurable_edgeVal W e)
  · rw [perEdgeIntegrand, abs_mul]
    have h1 : |edgeVal U x e₀ - edgeVal W x e₀| ≤ 1 := by
      rw [abs_le]; constructor <;>
        [linarith [edgeVal_nonneg U x e₀, edgeVal_le_one W x e₀];
         linarith [edgeVal_nonneg W x e₀, edgeVal_le_one U x e₀]]
    have h2 : |mixedProd U W Tu Tw x| ≤ 1 := by
      rw [abs_of_nonneg (mixedProd_nonneg U W Tu Tw x)]; exact mixedProd_le_one U W Tu Tw x
    calc |edgeVal U x e₀ - edgeVal W x e₀| * |mixedProd U W Tu Tw x|
        ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ ≤ 2 := by norm_num

/-- **Re-randomization at two coordinates.**  For two distinct coordinates `a ≠ b`, re-randomizing
    the `a`- and `b`-coordinates of `x` inside the integral does not change the value of the integral
    of an integrable function against the product measure:
    `∫ x, f x = ∫ x, (∫ s, ∫ t, f (restAt x a b s t) dμ dμ)`.
    (Both sides equal the marginal of `f` integrated over all coordinates, using that the integrand
    on the RHS no longer depends on `x a` or `x b`.) -/
theorem integral_rerandomize_two {a b : V} (hab : a ≠ b) (f : (V → Ω) → ℝ)
    (hf : letI : MeasurableSpace V := ⊤; Integrable f (piMeasure V μ)) :
    letI : MeasurableSpace V := ⊤
    ∫ x, f x ∂(piMeasure V μ)
      = ∫ x, (∫ s, (∫ t, f (restAt x a b s t) ∂μ) ∂μ) ∂(piMeasure V μ) := by
  -- Re-randomize one coordinate at a time: first `b`, then `a`.  `restAt x a b s t` unfolds to
  -- `Function.update (Function.update x a s) b t`, so applying `integral_rerandomize_one` at `b`
  -- (to `f`) and then at `a` (to the `b`-marginal `f₁`, integrable by `integrable_rerandomize_one`)
  -- yields exactly the iterated integral on the right.
  classical
  have hf₁int : Integrable (fun x => ∫ t, f (Function.update x b t) ∂μ) (piMeasure V μ) :=
    integrable_rerandomize_one b f hf
  have h1 := integral_rerandomize_one b f hf
  have h2 := integral_rerandomize_one a (fun x => ∫ t, f (Function.update x b t) ∂μ) hf₁int
  rw [h1, h2]
  simp only [restAt]

/-- **Per-edge cut-norm bound** (factorization crux).  For an edge `e₀` of the simple graph `F` and
    finsets `Tu, Tw` of *other* edges of `F`, the per-edge integral is at most `cutNorm (U − W)`. -/
theorem abs_integral_perEdge_le_cutNorm [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon Ω μ) (e₀ : Sym2 V) (he₀ : e₀ ∈ F.edgeFinset)
    (Tu Tw : Finset (Sym2 V)) (hTu : Tu ⊆ F.edgeFinset.erase e₀)
    (hTw : Tw ⊆ F.edgeFinset.erase e₀) :
    letI : MeasurableSpace V := ⊤
    |∫ x, perEdgeIntegrand U W Tu Tw e₀ x ∂(piMeasure V μ)|
      ≤ cutNorm (U.toSymmKernel - W.toSymmKernel) := by
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  set D : SymmKernel Ω μ := U.toSymmKernel - W.toSymmKernel with hD
  -- Decompose `e₀ = s(a, b)`; `a ≠ b` since `e₀ ∈ edgeFinset` is non-diagonal.
  induction e₀ using Sym2.inductionOn with
  | hf a b =>
    have hab : a ≠ b := by
      intro h; exact F.not_isDiag_of_mem_edgeFinset he₀ (Sym2.mk_isDiag_iff.2 h)
    -- No edge in `Tu ∪ Tw` contains both `a` and `b` (only `s(a,b)` does, and it is erased).
    have hnoboth : ∀ (T : Finset (Sym2 V)), T ⊆ F.edgeFinset.erase s(a, b) →
        ∀ e ∈ T, ¬(a ∈ e ∧ b ∈ e) := by
      intro T hT e he hboth
      have : e = s(a, b) := (Sym2.mem_and_mem_iff hab).1 hboth
      exact (Finset.mem_erase.1 (hT he)).1 this
    have hTu' := hnoboth Tu hTu
    have hTw' := hnoboth Tw hTw
    -- The integrand: `D(x a, x b) · mixedProd`.
    have hintegrand : ∀ x : V → Ω, perEdgeIntegrand U W Tu Tw s(a, b) x
        = D.toFun (x a) (x b) * mixedProd U W Tu Tw x := by
      intro x
      simp only [perEdgeIntegrand, hD, SymmKernel.sub_apply, coe_toSymmKernel, edgeVal,
        Sym2.lift_mk]
    -- restAt evaluations at the two endpoints.
    have hra : ∀ (x : V → Ω) (s t : Ω), (restAt x a b s t) a = s := fun x s t => by
      simp [restAt, Function.update_of_ne hab]
    have hrb : ∀ (x : V → Ω) (s t : Ω), (restAt x a b s t) b = t := fun x s t => by
      simp [restAt]
    -- Inner double integral, for fixed `x`, equals a single `μ.prod μ` integral, bounded by cutNorm.
    have hinner : ∀ x : V → Ω,
        |∫ s, (∫ t, perEdgeIntegrand U W Tu Tw s(a, b) (restAt x a b s t) ∂μ) ∂μ|
          ≤ cutNorm D := by
      intro x
      -- Rewrite the iterated integral as a single `μ.prod μ` integral of `D(s,t)·γ·α(s)·β(t)`.
      have hpoint : ∀ s t : Ω, perEdgeIntegrand U W Tu Tw s(a, b) (restAt x a b s t)
          = D.toFun s t * (mixedGamma U W Tu Tw x a b * mixedAlpha U W Tu Tw x a s
              * mixedBeta U W Tu Tw x b t) := by
        intro s t
        rw [hintegrand, hra x s t, hrb x s t,
          mixedProd_restAt_factor U W x hab s t Tu Tw hTu' hTw']
      have hintble : Integrable (fun p : Ω × Ω => D.toFun p.1 p.2 *
          (mixedGamma U W Tu Tw x a b * mixedAlpha U W Tu Tw x a p.1
            * mixedBeta U W Tu Tw x b p.2)) (μ.prod μ) := by
          refine SymmKernel.integrable_of_bdd ?_ (C := D.bound) (fun p => ?_)
          · refine D.meas'.mul ?_
            exact ((measurable_const.mul
                ((measurable_mixedAlpha U W Tu Tw x a).comp measurable_fst)).mul
              ((measurable_mixedBeta U W Tu Tw x b).comp measurable_snd))
          · -- |D·(γ·α·β)| ≤ D.bound since γ,α,β ∈ [0,1]
            rw [abs_mul]
            have hγ := mixedGamma_mem_Icc U W Tu Tw x a b
            have hα := mixedAlpha_mem_Icc U W Tu Tw x a p.1
            have hβ := mixedBeta_mem_Icc U W Tu Tw x b p.2
            have hfac : |mixedGamma U W Tu Tw x a b * mixedAlpha U W Tu Tw x a p.1
                * mixedBeta U W Tu Tw x b p.2| ≤ 1 := by
              rw [abs_of_nonneg (mul_nonneg (mul_nonneg hγ.1 hα.1) hβ.1)]
              have hgα : mixedGamma U W Tu Tw x a b * mixedAlpha U W Tu Tw x a p.1 ≤ 1 :=
                mul_le_one₀ hγ.2 hα.1 hα.2
              calc mixedGamma U W Tu Tw x a b * mixedAlpha U W Tu Tw x a p.1
                    * mixedBeta U W Tu Tw x b p.2
                  ≤ 1 * 1 :=
                    mul_le_mul hgα hβ.2 hβ.1 zero_le_one
                _ = 1 := one_mul 1
            calc |D.toFun p.1 p.2| * _ ≤ D.bound * 1 :=
                  mul_le_mul (D.abs_le_bound p.1 p.2) hfac (abs_nonneg _) D.bound_nonneg
              _ = D.bound := mul_one _
      have hrw : (∫ s, (∫ t, perEdgeIntegrand U W Tu Tw s(a, b) (restAt x a b s t) ∂μ) ∂μ)
          = ∫ p : Ω × Ω, D.toFun p.1 p.2 *
              (mixedGamma U W Tu Tw x a b * mixedAlpha U W Tu Tw x a p.1
                * mixedBeta U W Tu Tw x b p.2) ∂(μ.prod μ) := by
        rw [integral_prod _ hintble]
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        exact integral_congr_ae (ae_of_all _ fun t => (hpoint s t))
      rw [hrw]
      exact abs_inner_integral_le_cutNorm D (mixedGamma_mem_Icc U W Tu Tw x a b)
        (⟨measurable_mixedAlpha U W Tu Tw x a, mixedAlpha_mem_Icc U W Tu Tw x a⟩)
        (⟨measurable_mixedBeta U W Tu Tw x b, mixedBeta_mem_Icc U W Tu Tw x b⟩)
    -- Assemble: re-randomize, push abs through the outer integral, bound by the constant `cutNorm D`.
    rw [integral_rerandomize_two hab _ (integrable_perEdgeIntegrand U W Tu Tw s(a, b))]
    calc |∫ x, (∫ s, (∫ t, perEdgeIntegrand U W Tu Tw s(a, b) (restAt x a b s t) ∂μ) ∂μ)
            ∂(piMeasure V μ)|
        ≤ ∫ x, |∫ s, (∫ t, perEdgeIntegrand U W Tu Tw s(a, b) (restAt x a b s t) ∂μ) ∂μ|
            ∂(piMeasure V μ) := abs_integral_le_integral_abs
      _ ≤ ∫ _ : V → Ω, cutNorm D ∂(piMeasure V μ) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
            (integrable_const _) (ae_of_all _ fun x => hinner x)
      _ = cutNorm D := by simp

/-! ### The counting lemma inequality -/

/-- **Counting lemma inequality** (cut-norm ↔ homomorphism-density bridge):
    `|t(F, U) − t(F, W)| ≤ e(F) · ‖U − W‖□`. -/
theorem abs_homDensity_sub_le {V} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon Ω μ) :
    |homDensity F U - homDensity F W| ≤
      (F.edgeFinset.card : ℝ) * cutNorm (U.toSymmKernel - W.toSymmKernel) := by
  classical
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  -- Telescoping data.
  obtain ⟨Tu, Tw, hTu, hTw, hsum⟩ := exists_edge_telescope U W F.edgeFinset
  -- Rewrite the difference of integrals as a single integral of the difference, then telescope.
  have hUint := Graphon.integrable_homDensityIntegrand F U (V := V)
  have hWint := Graphon.integrable_homDensityIntegrand F W (V := V)
  have hdiff : homDensity F U - homDensity F W
      = ∫ x, (∑ e ∈ F.edgeFinset, perEdgeIntegrand U W (Tu e) (Tw e) e x) ∂(piMeasure V μ) := by
    rw [homDensity, homDensity, ← integral_sub hUint hWint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [homDensityIntegrand]
    rw [hsum x]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [perEdgeIntegrand]
  rw [hdiff]
  -- Pull the integral through the finite sum.
  rw [integral_finsetSum F.edgeFinset
        (fun e _ => integrable_perEdgeIntegrand U W (Tu e) (Tw e) e)]
  -- Bound the sum of integrals.
  calc |∑ e ∈ F.edgeFinset, ∫ x, perEdgeIntegrand U W (Tu e) (Tw e) e x ∂(piMeasure V μ)|
      ≤ ∑ e ∈ F.edgeFinset, |∫ x, perEdgeIntegrand U W (Tu e) (Tw e) e x ∂(piMeasure V μ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ F.edgeFinset, cutNorm (U.toSymmKernel - W.toSymmKernel) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        exact abs_integral_perEdge_le_cutNorm F U W e he (Tu e) (Tw e) (hTu e he) (hTw e he)
    _ = (F.edgeFinset.card : ℝ) * cutNorm (U.toSymmKernel - W.toSymmKernel) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Graphons

