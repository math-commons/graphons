/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

KG target (random-fields roadmap, layer L9 — dense graph limits), Tier C:
  **Compactness of graphon space** `(GraphonSpace Ω μ, δ□)`.  The cut-metric space of graphons over
  a fixed standard Borel probability space is compact.  This is the central structural theorem of
  the theory of dense graph limits (Lovász–Szegedy).
  Source: Lovász, "Large Networks and Graph Limits" (2012), §9.3 (Thm 9.23) and §11.

PHASE 1 (this file): build the SCAFFOLD.  A metric space is compact iff it is complete and totally
bounded; we reduce `graphonSpace_compactSpace` to the two halves and prove the *reduction* and the
*density* step sorry-free, isolating the two genuinely-hard analytic cores as the fewest, finest,
precisely-stated `sorry`s:

  * CORE A — `graphonSpace_totallyBounded`: a finite ε-net.  By weak regularity every graphon is
    δ□-close to a step graphon, and δ□ mods out the labeling so a step graphon is determined up to
    δ□ by its k×k block-value matrix and its part-size vector; discretizing both to an ε-grid leaves
    finitely many δ□-classes.  The density half ("every point is ε-close to *a* step graphon") is
    proved here (`exists_stepGraphon_point_close`); the assembly of the literal FINITE net (a
    canonical [0,1]-representative of a discretized step graphon + δ□-continuity under
    value/part-measure rounding + the complexity bound `k(ε)` that `weak_regularity` only gives
    implicitly) is the isolated `sorry`.

  * CORE B — `instCompleteSpaceGraphonSpace`: every δ□-Cauchy sequence converges.  This is in
    substance the Lovász–Szegedy limit theorem: build the limit graphon from a Cauchy sequence via
    a martingale / L²-compactness (weak-* / regularity) argument on a common refining sequence of
    partitions.  Isolated as a `sorry`.

DESIGN.  Reduction lemmas used (all pure Mathlib glue):
  `isCompact_univ_iff`, `TotallyBounded.isCompact_of_isComplete`, `complete_univ`,
  `Metric.totallyBounded_iff`.
-/
import Graphons.Space.GraphonSpaceMetric
import Graphons.Core.Density
import Graphons.Limits.BlockCoupling
import Graphons.Core.Examples

open MeasureTheory Metric Set

namespace Graphons

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [StandardBorelSpace Ω]

/-! ## CORE A — total boundedness of graphon space

The density-based "every point is ε-close to a step graphon" step is proved sorry-free; the literal
finite ε-net is the isolated core. -/

/-- **Density step (proved sorry-free).**  Every point `x : GraphonSpace Ω μ` is within `δ□`-distance
`ε` of the class of *some* step graphon `stepGraphon W P`.  Immediate from
`exists_stepGraphon_cutDist_le`: pick a representative `W` of `x`, apply weak-regularity density.

This is the easy half of total boundedness — the genuinely hard part (CORE A) is that the step
graphons fall into FINITELY many δ□-classes once their block-value matrix and part-size vector are
discretized to an ε-grid. -/
theorem exists_stepGraphon_point_close (x : GraphonSpace Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (W : Graphon Ω μ) (P : MeasPartition Ω μ),
      dist x (Quotient.mk (graphonSetoid Ω μ) (stepGraphon W P)) ≤ ε := by
  -- Choose a representative `W` of the class `x`.
  induction x using Quotient.inductionOn with
  | _ W =>
    -- Weak-regularity density: a partition `P` with `δ□(W, stepGraphon W P) ≤ ε`.
    obtain ⟨P, hP⟩ := exists_stepGraphon_cutDist_le W hε
    refine ⟨W, P, ?_⟩
    -- `dist ⟦W⟧ ⟦stepGraphon W P⟧ = cutDist W (stepGraphon W P) ≤ ε`.
    rw [dist_comm]
    show GraphonSpace.dist _ _ ≤ ε
    rw [GraphonSpace.dist_mk, cutDist_comm]
    exact hP

/-- **Finite net from finite fibers.**  If a function `f : X → F` into a finite type separates the
elements of `S` to within `ε` (any two points of `S` with the same `f`-value are `< ε` apart), then
`S` has a finite `ε`-net.  (Choice of one witness per attained `f`-value.) -/
theorem finite_net_of_finite_fibers {X : Type*} [PseudoMetricSpace X] (S : Set X)
    {F : Type*} [Finite F] (f : X → F) {ε : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y → dist x y < ε) :
    ∃ t : Set X, t.Finite ∧ S ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  classical
  set A : Set F := {d : F | ∃ x ∈ S, f x = d} with hA
  refine ⟨Set.range (fun d : A => (d.2).choose), Set.finite_range _, ?_⟩
  intro x hx
  have hda : f x ∈ A := ⟨x, hx, rfl⟩
  set d : A := ⟨f x, hda⟩ with hd
  obtain ⟨wmem, wf⟩ := d.2.choose_spec
  refine Set.mem_iUnion₂.2 ⟨(d.2).choose, ⟨d, rfl⟩, ?_⟩
  rw [Metric.mem_ball, dist_comm]
  exact h _ wmem x hx wf

/-- The set of `GraphonSpace` classes representable by a step graphon with **at most `N` parts**.
A class lies in `stepClasses N` when some graphon `W` and partition `P` with `Fintype.card P.ι ≤ N`
have `⟦stepGraphon W P⟧ = x`. -/
def stepClasses (N : ℕ) : Set (GraphonSpace Ω μ) :=
  {x | ∃ (W : Graphon Ω μ) (P : MeasPartition Ω μ),
        Fintype.card P.ι ≤ N ∧ Quotient.mk (graphonSetoid Ω μ) (stepGraphon W P) = x}

/-! ### CORE A: the finite net via grid data

`stepClasses_finite_net` (below) is reduced — via `finite_net_of_finite_fibers` and the grid-data
map `gridDataOf` — to the single remaining fact `stepClasses_close_of_gridData_eq` (two step classes
sharing grid data are `< ε` apart).  Its analytic content is fully proved sorry-free in
`Graphons/BlockCoupling.lean`. -/

/-- The finite **grid data** of a step class with at most `N` parts on an `m`-grid: the number of
parts `k ≤ N` (as a `Fin (N+1)`), together with the `m`-grid-rounded block-value matrix and
part-measure vector, *padded* to the fixed index set `Fin (N+1)` (entries beyond the `k` real parts
are `0`).  Using a fixed, non-dependent index set avoids `Fin`-card `HEq` bookkeeping in the
closeness proof; it is a `Fintype`, so it indexes a finite net via `finite_net_of_finite_fibers`. -/
abbrev GridData (N m : ℕ) : Type :=
  Fin (N + 1) × (Fin (N + 1) → Fin (N + 1) → Fin (m + 1)) × (Fin (N + 1) → Fin (m + 1))

open Classical in
/-- A chosen step-graphon witness graphon for a class `x` (default `Graphon.const 0` off
`stepClasses N`). -/
noncomputable def witW (N : ℕ) (x : GraphonSpace Ω μ) : Graphon Ω μ :=
  if hx : x ∈ stepClasses N then hx.choose
  else Graphon.const (μ := μ) 0 ⟨le_refl 0, zero_le_one⟩

open Classical in
/-- A chosen step-graphon witness partition for a class `x` (default `trivialPartition`). -/
noncomputable def witP (N : ℕ) (x : GraphonSpace Ω μ) : MeasPartition Ω μ :=
  if hx : x ∈ stepClasses N then hx.choose_spec.choose else trivialPartition

/-- A `Fin (card)`-labelling of the witness partition's parts. -/
noncomputable def witEquiv (N : ℕ) (x : GraphonSpace Ω μ) :
    (witP (Ω := Ω) (μ := μ) N x).ι ≃ Fin (Fintype.card (witP (Ω := Ω) (μ := μ) N x).ι) :=
  Fintype.equivFin _

/-- Read the block index at a padded label `a : Fin (N+1)` (defaulting to the first part when `a` is
out of range — only the in-range values matter). -/
noncomputable def witUnlbl (N : ℕ) (x : GraphonSpace Ω μ) (hx : x ∈ stepClasses N)
    (a : Fin (N + 1)) : (witP (Ω := Ω) (μ := μ) N x).ι :=
  if h : a.val < Fintype.card (witP (Ω := Ω) (μ := μ) N x).ι then
    (witEquiv (Ω := Ω) (μ := μ) N x).symm ⟨a.val, h⟩
  else (witEquiv (Ω := Ω) (μ := μ) N x).symm ⟨0, by
    have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
    have : 0 < Fintype.card (witP (Ω := Ω) (μ := μ) N x).ι :=
      Fintype.card_pos_iff.2 ⟨(witP (Ω := Ω) (μ := μ) N x).block hne.some⟩
    omega⟩

open Classical in
/-- For `x ∈ stepClasses N`, the witness realizes `x`: `⟦stepGraphon (witW x) (witP x)⟧ = x`,
with `card (witP x).ι ≤ N`. -/
theorem witW_spec (N : ℕ) {x : GraphonSpace Ω μ} (hx : x ∈ stepClasses N) :
    Fintype.card (witP (Ω := Ω) (μ := μ) N x).ι ≤ N ∧
      Quotient.mk (graphonSetoid Ω μ)
        (stepGraphon (witW (Ω := Ω) (μ := μ) N x) (witP (Ω := Ω) (μ := μ) N x)) = x := by
  have h := hx.choose_spec.choose_spec
  rw [witW, witP, dif_pos hx, dif_pos hx]
  exact ⟨h.1, h.2⟩

open Classical in
/-- The grid data of a class `x` (on an `m`-grid): part count `≤ N` (as `Fin (N+1)`), the grid-
rounded block matrix and grid-rounded part-measure vector, *padded* to `Fin (N+1)` via `witUnlbl`.
Junk off `stepClasses N`. -/
noncomputable def gridDataOf (N m : ℕ) (x : GraphonSpace Ω μ) : GridData N m :=
  if hx : x ∈ stepClasses N then
    ⟨⟨Fintype.card (witP (Ω := Ω) (μ := μ) N x).ι, Nat.lt_succ_of_le (witW_spec N hx).1⟩,
      fun a c => Graphons.gridIdx m
        (blockAvg (witW (Ω := Ω) (μ := μ) N x).toSymmKernel (witP (Ω := Ω) (μ := μ) N x)
          (witUnlbl N x hx a) (witUnlbl N x hx c)),
      fun a => Graphons.gridIdx m
        ((μ ((witP (Ω := Ω) (μ := μ) N x).part (witUnlbl N x hx a))).toReal)⟩
  else ⟨0, fun _ _ => 0, fun _ => 0⟩

/-- **Same grid data ⟹ cut-close (remaining CORE-A wiring).**  Two step classes in `stepClasses N`
with equal `m`-grid data (`1 ≤ m`, `(4N+2)/m < ε`) are `< ε` apart in the cut metric.

All the analytic content this needs is proved sorry-free in `Graphons/BlockCoupling.lean`:
`cutDist_step_le_of_equiv` (the `δ + 2D` bound via the block coupling), `exists_nearDiag_coupling`
(the part-measure coupling with off-diagonal mass `≤ ½‖p−p'‖₁`) and `gridIdx_close` (the `1/m`
rounding error).  What remains here is the bookkeeping: extracting the common `k` and the matrix/
vector equalities from the `Σ`-typed grid-data equality, and feeding `δ := 2/m` (matched block
values share a grid cell) and `D ≤ 2k/m` (part measures share a grid cell) into
`cutDist_step_le_of_equiv`, then `2/m + 2·(2k/m) ≤ (4N+2)/m < ε`. -/
theorem stepClasses_close_of_gridData_eq (N m : ℕ) {ε : ℝ} (hm1 : 1 ≤ m)
    (hmε : (4 * N + 2 : ℝ) / m < ε)
    (x : GraphonSpace Ω μ) (hx : x ∈ stepClasses N)
    (y : GraphonSpace Ω μ) (hy : y ∈ stepClasses N)
    (hxy : gridDataOf N m x = gridDataOf N m y) :
    dist x y < ε := by
  classical
  have hmR : (0:ℝ) < m := by exact_mod_cast hm1
  -- Unfold both grid data, then fold witnesses.
  rw [gridDataOf, dif_pos hx, gridDataOf, dif_pos hy] at hxy
  set Wx := witW (Ω := Ω) (μ := μ) N x with hWx
  set Px := witP (Ω := Ω) (μ := μ) N x with hPx
  set Wy := witW (Ω := Ω) (μ := μ) N y with hWy
  set Py := witP (Ω := Ω) (μ := μ) N y with hPy
  set kx := Fintype.card Px.ι with hkx
  set ky := Fintype.card Py.ι with hky
  have hkxN : (kx : ℝ) ≤ N := by exact_mod_cast (witW_spec N hx).1
  have hkxpos : 0 < kx := by
    have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
    exact Fintype.card_pos_iff.2 ⟨Px.block hne.some⟩
  -- Extract the three plain (non-dependent) equalities from the `Prod` equality.
  have hfst : kx = ky := by
    have := congrArg (fun d : GridData N m => (d.1 : ℕ)) hxy; simpa using this
  have hGM : ∀ A B : Fin (N+1),
      Graphons.gridIdx m (blockAvg Wx.toSymmKernel Px (witUnlbl N x hx A) (witUnlbl N x hx B))
        = Graphons.gridIdx m (blockAvg Wy.toSymmKernel Py (witUnlbl N y hy A) (witUnlbl N y hy B)) := by
    intro A B
    have := congrFun (congrFun (congrArg (fun d : GridData N m => d.2.1) hxy) A) B
    simpa using this
  have hGV : ∀ A : Fin (N+1),
      Graphons.gridIdx m ((μ (Px.part (witUnlbl N x hx A))).toReal)
        = Graphons.gridIdx m ((μ (Py.part (witUnlbl N y hy A))).toReal) := by
    intro A
    have := congrFun (congrArg (fun d : GridData N m => d.2.2) hxy) A
    simpa using this
  -- Labellings and the common `Fin kx`.
  set ePx := witEquiv (Ω := Ω) (μ := μ) N x with hePx
  set ePy := witEquiv (Ω := Ω) (μ := μ) N y with hePy
  set eP' : Py.ι ≃ Fin kx := ePy.trans (finCongr hfst.symm) with heP'
  -- The padded label of a real index, and how `witUnlbl` inverts it.
  have hlblN : ∀ a : Fin kx, (a.val) < N + 1 := fun a => by
    have : kx ≤ N := (witW_spec N hx).1; omega
  -- `witUnlbl N x hx (castLE (ePx i)) = i`.
  have hunlx : ∀ i : Px.ι,
      witUnlbl N x hx ⟨(ePx i).val, hlblN (ePx i)⟩ = i := by
    intro i
    rw [witUnlbl]
    have hlt : (⟨(ePx i).val, hlblN (ePx i)⟩ : Fin (N+1)).val < kx := (ePx i).2
    rw [dif_pos hlt]
    simp only [hePx]
    rw [show (⟨(ePx i).val, hlt⟩ : Fin kx) = witEquiv N x i from Fin.ext rfl,
      Equiv.symm_apply_apply]
  -- `witUnlbl N y hy (castLE (ePx i)) = (eP'.symm (ePx i))` when `ePx i` viewed in `Fin ky`.
  have hunly : ∀ a : Fin kx,
      witUnlbl N y hy ⟨a.val, hlblN a⟩ = eP'.symm a := by
    intro a
    rw [witUnlbl]
    have hlt : (⟨a.val, hlblN a⟩ : Fin (N+1)).val < ky := by rw [← hfst]; exact a.2
    rw [dif_pos hlt]
    simp only [heP', hePy, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply]
    congr 1
  -- Matched block-value bound.
  have hδ : (0:ℝ) ≤ 2 / m := by positivity
  have hmatch : ∀ (i : Px.ι) (j : Py.ι) (k₂ : Px.ι) (l : Py.ι),
      ePx i = eP' j → ePx k₂ = eP' l →
      |blockAvg Wx.toSymmKernel Px i k₂ - blockAvg Wy.toSymmKernel Py j l| ≤ 2 / m := by
    intro i j k₂ l hij hkl
    have hb1 : blockAvg Wx.toSymmKernel Px i k₂ ∈ Set.Icc (0:ℝ) 1 := blockAvg_mem_Icc Wx Px i k₂
    have hb2 : blockAvg Wy.toSymmKernel Py j l ∈ Set.Icc (0:ℝ) 1 := blockAvg_mem_Icc Wy Py j l
    -- evaluate hGM at A = castLE (ePx i), B = castLE (ePx k₂).
    have hgrid := hGM ⟨(ePx i).val, hlblN (ePx i)⟩ ⟨(ePx k₂).val, hlblN (ePx k₂)⟩
    rw [hunlx i, hunlx k₂] at hgrid
    -- y-side: witUnlbl y at those indices = eP'.symm (ePx i) = j, eP'.symm (ePx k₂) = l.
    rw [show witUnlbl N y hy ⟨(ePx i).val, hlblN (ePx i)⟩ = j from by
          rw [hunly (ePx i), hij, eP'.symm_apply_apply],
        show witUnlbl N y hy ⟨(ePx k₂).val, hlblN (ePx k₂)⟩ = l from by
          rw [hunly (ePx k₂), hkl, eP'.symm_apply_apply]] at hgrid
    have hcx := Graphons.gridIdx_close hm1 hb1.1 hb1.2
    have hcy := Graphons.gridIdx_close hm1 hb2.1 hb2.2
    rw [hgrid] at hcx
    have htri := abs_sub_le (blockAvg Wx.toSymmKernel Px i k₂)
      (((Graphons.gridIdx m (blockAvg Wy.toSymmKernel Py j l)).val : ℝ) / m)
      (blockAvg Wy.toSymmKernel Py j l)
    have hcy' : |((Graphons.gridIdx m (blockAvg Wy.toSymmKernel Py j l)).val : ℝ) / m
        - blockAvg Wy.toSymmKernel Py j l| ≤ 1 / m := by rw [abs_sub_comm]; exact hcy
    have he : (1:ℝ)/m + 1/m = 2/m := by ring
    linarith [le_trans htri (add_le_add hcx hcy')]
  -- The cut-distance bound and the `D ≤ 2·kx/m` part-measure bound.
  have hkey := cutDist_step_le_of_equiv Wx Wy Px Py ePx eP' (2/m) hδ hmatch
  -- Part-measure grid closeness ⟹ each term `(av - min).toReal ≤ 2/m`.
  have hDterm : ∀ a : Fin kx,
      (μ (Px.part (ePx.symm a)) - min (μ (Px.part (ePx.symm a))) (μ (Py.part (eP'.symm a)))).toReal
        ≤ 2 / m := by
    intro a
    set u := (μ (Px.part (ePx.symm a))).toReal with hu
    set v := (μ (Py.part (eP'.symm a))).toReal with hv
    have hule : u ∈ Set.Icc (0:ℝ) 1 :=
      ⟨ENNReal.toReal_nonneg, by rw [hu]; exact measureReal_le_one⟩
    have hvle : v ∈ Set.Icc (0:ℝ) 1 :=
      ⟨ENNReal.toReal_nonneg, by rw [hv]; exact measureReal_le_one⟩
    -- grid equality of the two part measures (via hGV at A = castLE (ePx (ePx.symm a)) = castLE a).
    have hgrid := hGV ⟨a.val, hlblN a⟩
    rw [show witUnlbl N x hx ⟨a.val, hlblN a⟩ = ePx.symm a from by
          have := hunlx (ePx.symm a); rw [Equiv.apply_symm_apply] at this; exact this,
        hunly a] at hgrid
    -- |u - v| ≤ 2/m.
    have hcx : |u - ((Graphons.gridIdx m u).val : ℝ) / m| ≤ 1 / m :=
      Graphons.gridIdx_close hm1 hule.1 hule.2
    have hcy : |v - ((Graphons.gridIdx m v).val : ℝ) / m| ≤ 1 / m :=
      Graphons.gridIdx_close hm1 hvle.1 hvle.2
    rw [hgrid] at hcx
    have htri := abs_sub_le u
      (((Graphons.gridIdx m v).val : ℝ) / m) v
    have hcy' : |((Graphons.gridIdx m v).val : ℝ) / m - v| ≤ 1/m := by rw [abs_sub_comm]; exact hcy
    have huv : |u - v| ≤ 2/m := by
      have he : (1:ℝ)/m + 1/m = 2/m := by ring
      linarith [le_trans htri (add_le_add hcx hcy')]
    -- (av - min).toReal ≤ max (u - v) 0 ≤ |u-v| ≤ 2/m.
    have hfin1 := Px.measure_part_ne_top (ePx.symm a)
    rcases le_total (μ (Px.part (ePx.symm a))) (μ (Py.part (eP'.symm a))) with hle | hle
    · rw [min_eq_left hle, tsub_self]; simp; positivity
    · rw [min_eq_right hle, ENNReal.toReal_sub_of_le hle hfin1, ← hu, ← hv]
      have hle2 : u - v ≤ |u - v| := le_abs_self _
      linarith [huv]
  have hDbound : (∑ a : Fin kx, (μ (Px.part (ePx.symm a))
        - min (μ (Px.part (ePx.symm a))) (μ (Py.part (eP'.symm a)))).toReal)
      ≤ kx * (2 / m) := by
    refine le_trans (Finset.sum_le_sum (fun a _ => hDterm a)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Rewrite `dist` and combine.
  have hxrep := (witW_spec N hx).2
  have hyrep := (witW_spec N hy).2
  rw [← hxrep, ← hyrep]
  show GraphonSpace.dist _ _ < ε
  rw [GraphonSpace.dist_mk]
  calc cutDist (stepGraphon Wx Px) (stepGraphon Wy Py)
      ≤ 2/m + 2 * (∑ a : Fin kx, (μ (Px.part (ePx.symm a))
          - min (μ (Px.part (ePx.symm a))) (μ (Py.part (eP'.symm a)))).toReal) := hkey
    _ ≤ 2/m + 2 * (kx * (2/m)) := by gcongr
    _ ≤ (4 * N + 2) / m := by
        rw [le_div_iff₀ hmR]
        have h1 : (2:ℝ)/m * m = 2 := by field_simp
        have h2 : (2:ℝ) * (kx * (2/m)) * m = 4 * kx := by field_simp; ring
        nlinarith [hkxN, hmR, h1, h2]
    _ < ε := hmε

theorem stepClasses_finite_net (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set (GraphonSpace Ω μ), t.Finite ∧ stepClasses N ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  classical
  -- Grid resolution: `m` large enough that `(4N+2)/m < ε`.
  obtain ⟨m, hm1, hmε⟩ : ∃ m : ℕ, 1 ≤ m ∧ ((4 * N + 2 : ℝ) / m < ε) := by
    obtain ⟨m, hm⟩ := exists_nat_gt ((4 * N + 2) / ε + 1)
    refine ⟨m, ?_, ?_⟩
    · have : (1:ℝ) ≤ m := by
        have h0 : (0:ℝ) ≤ (4 * N + 2) / ε := by positivity
        linarith
      exact_mod_cast this
    · have hmpos : (0:ℝ) < m := by
        have h0 : (0:ℝ) ≤ (4 * N + 2) / ε := by positivity
        linarith
      rw [div_lt_iff₀ hmpos]
      have hlt : (4 * N + 2 : ℝ) / ε < m := by linarith
      rw [div_lt_iff₀ hε] at hlt
      linarith [hlt]
  -- Finite net via the finite grid-data fibers; the single remaining fact is the closeness lemma.
  exact finite_net_of_finite_fibers (stepClasses N) (F := GridData N m) (gridDataOf N m)
    (fun x hx y hy hxy => stepClasses_close_of_gridData_eq N m hm1 hmε x hx y hy hxy)

/-- **Total boundedness of graphon space (CORE A).**  The metric space `(GraphonSpace Ω μ, δ□)` is
totally bounded: for every `ε > 0` there is a finite `ε`-net.

The reduction (proved here): by `exists_stepGraphon_point_close` together with the part-count bound
`weak_regularity_card`, every point of `GraphonSpace` is `ε/2`-close to a step-graphon class with at
most `N := 4 ^ ⌈1/(ε/2)²⌉` parts, i.e. to a point of `stepClasses N`.  A finite `ε/2`-net of
`stepClasses N` (CORE A proper, `stepClasses_finite_net`) is then, after fattening the balls to
radius `ε`, a finite `ε`-net of all of `univ`. -/
theorem graphonSpace_totallyBounded :
    TotallyBounded (Set.univ : Set (GraphonSpace Ω μ)) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Work at radius `ε/2`.
  have hε2 : 0 < ε / 2 := by linarith
  -- Part bound from weak regularity at scale `ε/2`.
  set N : ℕ := 4 ^ ⌈1 / (ε / 2) ^ 2⌉₊ with hN
  -- A finite `(ε/2)`-net `t` of the bounded-complexity step classes (ISOLATED CORE A).
  obtain ⟨t, htfin, htcov⟩ := stepClasses_finite_net (Ω := Ω) (μ := μ) N hε2
  refine ⟨t, htfin, ?_⟩
  -- Every point of `univ` is within `ε` of some net point.
  intro x _
  -- `x` is `ε/2`-close to a step-graphon class `y` with ≤ N parts (density + card bound).
  obtain ⟨y, hy_mem, hxy⟩ : ∃ y ∈ stepClasses N, dist x y ≤ ε / 2 := by
    induction x using Quotient.inductionOn with
    | _ W =>
      obtain ⟨P, hPcard, hPcut⟩ := weak_regularity_card W hε2
      refine ⟨Quotient.mk (graphonSetoid Ω μ) (stepGraphon W P), ⟨W, P, hPcard, rfl⟩, ?_⟩
      -- `dist ⟦W⟧ ⟦stepGraphon W P⟧ = cutDist W (stepGraphon W P) ≤ ε/2`.
      show GraphonSpace.dist _ _ ≤ ε / 2
      rw [GraphonSpace.dist_mk]
      exact le_trans (le_trans (cutDist_le_cutNorm W (stepGraphon W P))
        (by rw [stepGraphon_toSymmKernel])) hPcut
  -- `y` lies in some net ball of radius `ε/2`; the triangle inequality gives `dist x · < ε`.
  obtain ⟨z, hz_mem, hyz⟩ := Set.mem_iUnion₂.1 (htcov hy_mem)
  refine Set.mem_iUnion₂.2 ⟨z, hz_mem, ?_⟩
  rw [Metric.mem_ball] at hyz ⊢
  calc dist x z ≤ dist x y + dist y z := dist_triangle x y z
    _ < ε / 2 + ε / 2 := by linarith [hxy, hyz]
    _ = ε := by ring

end Graphons
