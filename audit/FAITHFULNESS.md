# FAITHFULNESS — a dictionary between graphon theory and the Lean formalization

This document is addressed to a mathematician who knows the basic theory of graphons and dense
graph limits as in Lovász, *Large Networks and Graph Limits* (AMS Colloquium Publications 60,
2012; "LNGL" below), and who wants to judge whether this Lean library is a **correct
formalization of that theory** — without learning Lean. It has four parts:

1. **How to read Lean statements, and what you must trust** (§1);
2. **The dictionary**: each primary object — Lovász's definition, the Lean rendering, and an
   *encoding note* for every place the two differ, with the proved theorem that reconciles
   them (§2);
3. **The theorem inventory**: the statements proved about these objects, with LNGL references
   and one-line proof ideas (§3);
4. **The four assumed axioms**, stated in full mathematical language, with what does and does
   not depend on them (§4), and a concrete audit recipe (§5).

The companion document [`VALIDATION.md`](VALIDATION.md) makes the *argument* that these
definitions are the right ones; this document supplies the raw correspondence it argues from.

---

## §1 What a Lean theorem certifies, and what you must trust

A Lean theorem that compiles is checked by a small proof kernel down to the axioms of the
underlying type theory. The practical consequences for a reader:

- **You need not read or trust the proofs.** If `lake build` succeeds, every proof is correct
  relative to the *statements* and the axioms. Proof scripts, however they were produced, are
  not part of the trust base.
- **You must read the statements** — a formalization can only be wrong in its definitions and
  theorem statements, never in its proofs. That is what §2–§3 are for: every load-bearing
  definition and statement is reproduced here next to its informal meaning. The Lean
  statements are short; the corresponding source files are named so you can confirm the
  transcription.
- **You must know the axioms.** The command `#print axioms <theorem>` lists everything a
  theorem ultimately assumes. For this library the answer is: Mathlib's three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound` — i.e. ordinary classical mathematics) for
  *every* result, plus, for exactly four deep results, four explicitly declared classical
  theorems assumed as axioms (§4). There are **no `sorry`s** (unproven placeholders) anywhere.
  The file `Graphons/Tests/AxiomGuard.lean` pins the *exact* axiom list of every flagship
  theorem; the build fails if any list ever changes.

Notation used below: `(Ω, μ)` is a probability space, formalized as
`{Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`; results about the
metric/limit theory additionally assume `Ω` is a standard Borel space
(`[StandardBorelSpace Ω]`), as does LNGL Ch. 13.

---

## §2 The dictionary of primary objects

### 2.1 Kernels and graphons (LNGL §7.1–7.2)

**Lovász.** A *kernel* is a bounded symmetric measurable function `W : Ω × Ω → ℝ`; a
*graphon* is a kernel with values in `[0,1]`.

**Lean** (`Graphons/Core/Basic.lean`):
```lean
structure SymmKernel (Ω) [MeasurableSpace Ω] (μ : Measure Ω) where
  toFun : Ω → Ω → ℝ
  symm' : ∀ x y, toFun x y = toFun y x
  meas' : Measurable (Function.uncurry toFun)
  bdd'  : ∃ C, ∀ x y, |toFun x y| ≤ C

structure Graphon (Ω) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    extends SymmKernel Ω μ where
  nonneg' : ∀ x y, 0 ≤ toFun x y
  le_one' : ∀ x y, toFun x y ≤ 1
```
`SymmKernel` carries an ℝ-vector-space structure (pointwise), so differences `U − W` and
scalar multiples exist — needed for the cut norm.

**Encoding notes.**
- *Everywhere-defined, not a.e.-classes.* A `Graphon` is an honest function, with symmetry and
  bounds holding at every point, not almost everywhere. Lovász works with a.e.-classes; the
  reconciliation is that the a.e. identification happens **once, at the metric level**: two
  graphons equal μ⊗μ-a.e. satisfy `cutDist U W = 0` (immediate from the two proved lemmas
  `cutDist_le_cutNorm` and `cutNorm_le_L1`), hence become *equal* in the quotient space
  `GraphonSpace` (§2.5). Nothing downstream distinguishes a.e.-equal graphons.
- *Abstract carrier.* The carrier is an arbitrary probability space, not hardcoded `[0,1]`
  (LNGL Ch. 13 generality). The classical carrier appears as the instance
  `unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)`. Two results — compactness and
  completeness — are currently proved only over this carrier (see §3, V.15–V.16); everything
  else is carrier-general.

### 2.2 Homomorphism density `t(F, W)` (LNGL §7.2; finite case Ch. 5)

**Lovász.** For a finite simple graph `F` with vertex set `V` and a graphon `W`:
`t(F, W) = ∫_{Ω^V} ∏_{ij ∈ E(F)} W(x_i, x_j) dμ^{⊗V}(x)`.

**Lean** (`Graphons/Core/Basic.lean`):
```lean
noncomputable def homDensity (F : SimpleGraph V) [Fintype V] [DecidableRel F.Adj]
    (W : Graphon Ω μ) : ℝ :=
  ∫ x, ∏ e ∈ F.edgeFinset, edgeVal W x e ∂(piMeasure V μ)
```
where `piMeasure V μ = μ^{⊗V}` and `edgeVal W x e` evaluates `W (x i) (x j)` on the unordered
edge `e = {i, j}` (well-defined by symmetry of `W`; packaged via Mathlib's `Sym2.lift`).

**Encoding notes.**
- *Unordered edges.* Mathlib's `SimpleGraph` stores edges as unordered pairs (`Sym2`); the
  product runs over the edge *set*, each edge counted once, exactly as in the displayed
  integral. The edge count `e(F)` is `F.edgeFinset.card`.
- *Sanity of the encoding* is not taken on faith: V.1–V.3 below verify that this definition
  computes `0 ≤ t ≤ 1`, `t(F, W_p) = p^{e(F)}` for the constant graphon (Erdős–Rényi),
  `t(K₂, W) = ∫∫ W`, and `t(K₃, W) = ∫∫∫ W(x,y)W(x,z)W(y,z)`, and the executable test suite
  pins concrete rational values against an independent brute-force implementation.

### 2.3 Cut norm (LNGL §8.1)

**Lovász.** `‖W‖□ = sup_{S,T ⊆ Ω measurable} |∫_{S×T} W dμ×dμ|`.

**Lean** (`Graphons/CutMetric/CutNorm.lean`, `CutNormSet.lean`): the primary definition takes
the supremum over `[0,1]`-valued measurable test functions,
```lean
noncomputable def cutNorm (W : SymmKernel Ω μ) : ℝ :=
  ⨆ (u v : Ω → ℝ) (_ : IsTestFun u) (_ : IsTestFun v),
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|
```
with `IsTestFun u ↔ u` measurable and `[0,1]`-valued.

**Encoding notes.** Three formulations circulate in the literature; all three are reconciled
by proved theorems, so nothing depends on the choice:
- **set form** = test-function form, *exactly* (no constant): `cutNorm_eq_cutNormSet`
  (V.5; the bang-bang argument);
- **signed test functions** (`[−1,1]`-valued, the `∞→1` operator-norm formulation): equivalent
  within the classical factor 4 — `cutNorm ≤ cutNormSigned ≤ 4·cutNorm`
  (`Graphons/CutMetric/Robustness.lean`);
- the seminorm laws (V.4) and `cutNorm W = t(K₂, W)` for a graphon pin the normalization.

### 2.4 Cut distance `δ□` (LNGL §8.2)

**Lovász.** `δ□(U, W) = inf_φ ‖U − W^φ‖□` over measure-preserving maps, or equivalently an
infimum over couplings of the two carriers.

**Lean** (`Graphons/CutMetric/CutDist.lean`): the **coupling** formulation is primary —
```lean
def IsCoupling (μ₁ μ₂) (π : Measure (Ω₁ × Ω₂)) : Prop :=
  π.map Prod.fst = μ₁ ∧ π.map Prod.snd = μ₂

noncomputable def cutDist (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : ℝ :=
  ⨅ π : {π // IsCoupling μ₁ μ₂ π}, cutNorm (overlay U W π)
```
where `overlay U W π` is the kernel `(p, q) ↦ U(p₁, q₁) − W(p₂, q₂)` on the coupled space.
Note `δ□` is defined between graphons on *different* carriers.

**Encoding notes.**
- *Couplings vs maps.* The two textbook formulations agree on atomless standard Borel spaces
  (LNGL Lemma 8.13), but that equivalence needs the measure-isomorphism theorem, which Mathlib
  does not yet have. The library therefore takes couplings as primary and proves the relations
  that are available without it (`Graphons/CutMetric/Robustness.lean`): every pair of
  measure-preserving maps from a common space yields an upper bound for the coupling infimum
  (`cutDist_le_cutNorm_pullback_sub`), pulling back along a measure-preserving map changes a
  graphon by cut distance 0 (`cutDist_pullback_self`), and pulling *both* graphons back along
  one map preserves `δ□` exactly (`cutDist_pullback_pullback`). All uses of `δ□` downstream are
  insensitive to the formulation choice through these lemmas.
- The triangle inequality for this coupling formulation is a genuine theorem (the Gluing
  Lemma, V.6), proved by disintegration; it needs the standard-Borel hypothesis, as in the
  classical treatment.

### 2.5 Graphon space (LNGL §8.2, Ch. 11, weak isomorphism Ch. 13)

**Lovász.** The space of graphons modulo weak isomorphism (`δ□ = 0`), a compact metric space
under `δ□`, on which all `t(F, ·)` are well-defined and continuous.

**Lean** (`Graphons/Space/`):
```lean
def GraphonSpace (Ω) (μ) [StandardBorelSpace Ω] := Quotient (graphonSetoid Ω μ)  -- W ∼ W' ↔ δ□ = 0
noncomputable instance : MetricSpace (GraphonSpace Ω μ)            -- dist = δ□, now a true metric
noncomputable def GraphonSpace.homDensity (F) : GraphonSpace Ω μ → ℝ  -- descended t(F,·)
```
Descent of `t(F, ·)` to the quotient is legitimate because `δ□(U, W) = 0` implies
`t(F, U) = t(F, W)` for all `F` — the forward counting lemma (V.8), proved axiom-free.

### 2.6 Step graphons and finite graphs (LNGL §7.1)

**Lovász.** A finite graph `G` on `n` vertices is identified with its step graphon `W_G`; a
weighted graph likewise; `t(F, W_G)` equals the (normalized) homomorphism density of `F` in `G`.

**Lean** (`Graphons/Core/Step.lean`, `StepDensity.lean`): `Graphon.step G` is the adjacency
indicator on the carrier `Fin n` with the uniform measure, and
```lean
theorem homDensity_step :
  homDensity F (Graphon.step G) = (∑ φ : V → Fin n, ∏ e ∈ F.edgeFinset, …) / n ^ |V|
```
identifies it with the combinatorial count `hom(F, G)/n^{|V(F)|}`. Note the carrier of `W_G`
is the *finite* set `Fin n`, not `[0,1]`; the cross-carrier `δ□` (§2.4) and the transport
results (§3, V.22) connect the two — in particular the interval step transport of a finite
(weighted) graph to a graphon on `[0,1]` is proved to move it by cut distance zero
(`cutDist_toUnit`, `Graphons/Characterization/IntervalTransport.lean`).

### 2.7 Finite weighted graphs and the limit-theory specification (LNGL Ch. 8 + 11)

For the axiomatic characterization (V.22) the finite side is packaged as
`FinWeighted := Σ n, Graphon (Fin (n+1)) (unifFin (n+1))` — finite vertex sets with the
uniform measure and `[0,1]` edge weights — carrying the cut premetric `δ□` (only a
*pseudo*metric: weak isomorphs, e.g. blow-ups, are at distance 0) and the finite homomorphism
densities. See §3, V.22 for the specification `IsDenseGraphLimitTheory` built on it.

---

## §3 The theorem inventory

Each item: the mathematical statement (with LNGL reference), the Lean theorem name (the file
is discoverable by searching the name under `Graphons/`), a one-line proof idea — included so
an expert can check the formal proof is *the standard proof*, not an artifact — and its axiom
status. "Axiom-free" = standard three axioms only; "mod axioms #k" = additionally uses the
numbered axioms of §4. Everything below is `sorry`-free and compiles.

### Encoding anchors (does `t(F,W)` compute the right numbers?)

- **V.1** `0 ≤ t(F,W) ≤ 1` — `homDensity_mem_Icc`. Axiom-free.
- **V.2** `t(F, W_p) = p^{e(F)}` for the constant graphon `W_p` (the Erdős–Rényi limit) —
  `homDensity_const`. The single cleanest correctness check. Axiom-free.
- **V.3** `t(K₂,W) = ∫∫ W` and `t(K₃,W) = ∫∫∫ W(x,y)W(x,z)W(y,z)` — `homDensity_edge`,
  `homDensity_triangle`. *Idea:* compute the edge set, transport `μ^{⊗k}` to the iterated
  product. Axiom-free.
- Executable instances (`Graphons/Tests/Concrete.lean`): `t(K₂, W_{K₄}) = 3/4`,
  `t(K₃, W_{C₅}) = 0`, `t(P₃, W_{1/2}) = 1/4`, `t(C₄, W_{1/2}) = 1/16`, … — each proved in
  Lean *and* matching the independent brute-force reference
  `scripts/hom_density_reference.py`.

### The cut norm and cut distance are the right objects

- **V.4** `‖·‖□` is a seminorm — `cutNorm_nonneg`, `cutNorm_smul`, `cutNorm_add_le`,
  `cutNorm_neg`. Axiom-free.
- **V.5** Test-function form = set form, exactly — `cutNorm_eq_cutNormSet` (LNGL §8.1).
  *Idea:* indicators are test functions; conversely bang-bang extremality plus Fubini in each
  slot. Also `cutNorm ≤ ∫∫|W|` (`cutNorm_le_L1`) and `cutNorm W = t(K₂,W)` for graphons.
  Axiom-free. The signed/factor-4 comparison is in `Robustness.lean` (§2.3).
- **V.6** `δ□` is a pseudometric; the triangle inequality across three carriers is the
  **Gluing Lemma** — `cutDist_triangle` (LNGL §8.2). *Idea:* disintegrate the two couplings
  over the shared middle marginal, glue conditionally-independently, and telescope the overlay.
  Axiom-free; standard-Borel hypotheses as in the classical statement.

### The Counting Lemma (LNGL §10.2, Lemma 10.22–10.24)

- **V.7** `|t(F,U) − t(F,W)| ≤ e(F)·‖U − W‖□` (same carrier) — `abs_homDensity_sub_le`.
  *Idea:* telescope edge by edge; for each edge, freezing the other coordinates exhibits the
  integrand as `γ·α(x_a)·β(x_b)` (simpleness of `F` is used here), bounded by the cut norm.
  Axiom-free.
- **V.8** Cross-carrier version `|t(F,U) − t(F,W)| ≤ e(F)·δ□(U,W)`, hence
  `δ□(U,W) = 0 ⇒ ∀F, t(F,U) = t(F,W)` — `abs_homDensity_sub_le_cutDist`,
  `homDensity_eq_of_cutDist_eq_zero`. *Idea:* both marginal pullbacks onto the coupled space
  preserve hom densities; apply V.7 there; take the infimum. Axiom-free.
- **V.13** Each `t(F,·)` is `e(F)`-Lipschitz, hence continuous, on `GraphonSpace` —
  `GraphonSpace.lipschitzWith_homDensity`, `continuous_homDensity`. Axiom-free.

### Structural laws

- **V.9** Multiplicativity over disjoint unions, `t(F₁ ⊔ F₂, W) = t(F₁,W)·t(F₂,W)` —
  `homDensity_sum` (LNGL §5.2/7.2). Axiom-free.
- **V.10** Finite-graph compatibility (§2.6) — `homDensity_step`. Axiom-free.

### The limit theory (LNGL Ch. 9 and 11)

- **V.11** **Weak (Frieze–Kannan) Regularity Lemma** — `weak_regularity` (∀ε ∃ partition `P`
  with `‖W − W_P‖□ ≤ ε`) and `weak_regularity_card` (with `|P| ≤ 4^{⌈1/ε²⌉}`) (LNGL ≈Lemma
  9.9). *Idea:* energy increment. Axiom-free.
- **V.12** Step graphons are `δ□`-dense — `exists_stepGraphon_cutDist_le`. Axiom-free.
- **V.14** `(GraphonSpace, δ□)` is totally bounded — `graphonSpace_totallyBounded` (LNGL,
  toward Thm 9.23). *Idea:* finite ε-net of value-discretized step graphons via block
  couplings. Axiom-free.
- **V.15** **Completeness** of `GraphonSpace` over `([0,1], Leb)` —
  `instCompleteSpaceGraphonSpaceUnit`. **Mod axioms #1–2** (§4): the proof reduces a fast
  `δ□`-Cauchy sequence to cut-norm-Cauchy representatives (axiom #1), then to an L¹ limit of
  dyadic conditional expectations (axiom #2); the assembly around the two axioms is proved.
- **V.16** **Compactness** of `GraphonSpace` over `[0,1]` (the LSZ theorem, LNGL ≈Thm 9.23) —
  `instCompactSpaceGraphonSpaceUnit` = V.14 + V.15. **Mod axioms #1–2.**
- **V.17** **Counting lemma, both directions**: `δ□(U,W) = 0 ⇔ ∀F, t(F,U) = t(F,W)` —
  `cutDist_eq_zero_iff_homDensity_eq`; hence the moment map `W ↦ (t(F,W))_F` is injective on
  `GraphonSpace` (`GraphonSpace.eq_iff_homDensity_eq`) (LNGL Ch. 11/13, inverse counting =
  Thm 11.3). Forward direction axiom-free (V.8); the converse is exactly **axiom #3**.
- **V.18** **Lovász–Szegedy representability** (LNGL ≈Thm 5.54/14.31): a graph parameter `f`
  is `t(·,W)` for some graphon `W` iff it is multiplicative, normalized, reflection-positive,
  and `[0,1]`-bounded — `representability`. The "only if" direction is proved (Gram-matrix
  argument); the "if" direction is exactly **axiom #4**.

### Classical consequences (never design targets; see VALIDATION.md §4)

- **V.19** Degree and co-degree calculus: `deg_W(x) = ∫ W(x,y)dy`,
  `coDeg_W(x,y) = ∫ W(x,u)W(y,u)du`, with the normal forms `∫ deg = t(K₂)`,
  `t(P₃) = ∫ deg²`, `∫∫ coDeg = ∫ deg²`, `t(C₄) = ∫∫ coDeg²`,
  `t(K₃) = ∫∫ W·coDeg`. Axiom-free.
- **V.20** **Goodman's bound** `t(K₃,W) ≥ 2t(K₂,W)² − t(K₂,W)` — `goodman` (Goodman 1959;
  LNGL §2.1). Axiom-free.
- **V.21** **Sidorenko's inequality for C₄** `t(C₄,W) ≥ t(K₂,W)⁴` — `sidorenko_C4` (the `C₄`
  case of Sidorenko's conjecture). *Idea:* two Cauchy–Schwarz applications through V.19.
  Axiom-free. Numerically tight at `W_{K₄}`: `81/256 ≤ 84/256`.
- **(V.20′)** **Mantel's theorem for graphons** `t(K₃,W) = 0 ⇒ t(K₂,W) ≤ 1/2` — `mantel`.
  *Idea:* triangle-freeness forces a.e. disjoint neighborhoods (`coDeg = 0 ⇒
  deg x + deg y ≤ 1`); integrate against `W` and close with Cauchy–Schwarz. Axiom-free.

### The axiomatic characterization (V.22; see VALIDATION.md §5 for why this matters most)

A **dense graph limit theory** is axiomatized, independently of this library's definitions, as:
a complete metric space `X`; a distance-preserving map `ι` from the finite weighted graphs
(with their cut premetric) with dense image; and for each finite simple graph `F` a continuous
functional `t_F : X → ℝ` restricting to the finite homomorphism density on the image. In Lean
(`Graphons/Characterization/LimitSpec.lean`):
```lean
structure IsDenseGraphLimitTheory (X) [MetricSpace X] [CompleteSpace X]
    (ι : FinWeighted → X) (t : …) : Prop where
  dense_range  : DenseRange ι
  dist_ι       : ∀ G H, dist (ι G) (ι H) = finCutDist G H
  continuous_t : ∀ n F inst, Continuous (t F inst)
  compat_t     : ∀ n F inst G, t F inst (ι G) = finHomDensity F G
```
This four-line specification was reviewed independently against LNGL Ch. 8/11
([`LIMIT_SPEC_REVIEW.md`](LIMIT_SPEC_REVIEW.md)). The theorems:

- **Existence** — `isDenseGraphLimitTheory_graphonSpace`: `GraphonSpace` over `[0,1]`, with
  the interval step transport and the descended densities, satisfies the specification.
  **Mod axioms #1–2** (only through completeness, V.15); all the new ingredients —
  the transport is `δ□`-invisible, densities are transport-invariant, finite weighted graphs
  are `δ□`-dense among `[0,1]`-graphons — are axiom-free.
- **Uniqueness** — `isDenseGraphLimitTheory_unique`: *any two* structures satisfying the
  specification are canonically isometric, compatibly with `ι` and with every `t_F`.
  **Axiom-free** (uniqueness of metric completions). Corollary: every model is canonically
  isometric to `GraphonSpace`.

*Caveat:* the dense finite objects are weighted graphs; sharpening to simple graphs requires
the (weighted → simple) approximation, a known open item here (VALIDATION.md §8).

### Sampling (LNGL Ch. 10)

The W-random graph `G(n, W)` is formalized honestly: vertex positions `x₁,…,xₙ` i.i.d. `μ`,
then conditionally independent edge coins with `P({i,j} edge) = W(x_i, x_j)`, as a genuine
product-Bernoulli measure (`Graphons/Sampling/WRandom.lean`) — independence is *proved* from
the product structure, not assumed (`integral_coin_prod`). Then
(`Graphons/Sampling/SamplingLemma.lean`, all axiom-free):

- **exact identity**: for any *injective* placement of `V(F)` into the `n` vertices, the
  annealed probability that all of `F`'s edges appear integrates to exactly `t(F, W)`;
- **first sampling lemma, expectation form**:
  `|E[t(F, G(n,W))] − t(F,W)| ≤ k(k−1)/n` where `k = |V(F)|`
  (`abs_expectedHomDensity_sub_le`), so `E[t(F, G(n,W))] → t(F,W)`
  (`tendsto_expectedHomDensity`). The deficit is exactly the non-injective placement mass.

The almost-sure statement (LNGL Lemma 10.16) is not yet formalized (VALIDATION.md §8).

---

## §4 The four assumed axioms — full disclosure

Four classical theorems, each absent from Mathlib v4.30.0, are assumed as named axioms. Each
was independently reviewed for *truth and exact formulation* before being admitted (one earlier
candidate axiom was found to be **false as stated** during such review and was rejected and
redesigned — see `HISTORY.md` items 36–37 — which is evidence the vetting has teeth). Their
informal statements:

1. **`cutNorm_alignment_unit`** *(measure-theoretic).* If `(Wₙ)` are graphons on
   `([0,1], Leb)` with `δ□(Wₙ, Wₙ₊₁) ≤ 2⁻ⁿ`, there exist graphons `Wₙ'` with
   `δ□(Wₙ, Wₙ') = 0` such that `(Wₙ')` is Cauchy in the **cut norm** (not just the cut
   distance). Classically: realign by measure-preserving transformations; Birkhoff–von
   Neumann / Rokhlin-type arguments (cf. LNGL proof of Thm 9.23).
2. **`dyadic_l1Cauchy_approx_unit`** *(measure-theoretic).* A cut-norm-Cauchy sequence of
   graphons on `[0,1]` admits dyadic conditional-expectation approximants that are Cauchy in
   `L¹` and `δ□`-close to the originals. Classically: martingale (Lévy upward) convergence
   along the dyadic filtration; the required ingredients exist in Mathlib, so this is
   considered buildable.
3. **`cutDist_eq_zero_of_homDensity_eq`** *(probabilistic).* If `t(F,U) = t(F,W)` for all
   finite simple `F`, then `δ□(U,W) = 0` — the **inverse counting lemma** (LNGL Thm 11.3 /
   Ch. 13). Classically: W-random sampling plus a martingale/second-moment argument.
4. **`lovasz_szegedy_representability`** *(algebraic).* A multiplicative, normalized,
   reflection-positive, `[0,1]`-bounded graph parameter is `t(·,W)` for some graphon `W`
   (LNGL Thm 5.54/14.31). Owned by the sibling project `reflection-positivity`.

**What depends on what.** Axioms #1–2 enter only through completeness/compactness of
`GraphonSpace[0,1]` (V.15, V.16) and through anything quoting completeness (the Tier-E
existence theorem and its corollary). Axiom #3 enters only the *converse* half of V.17.
Axiom #4 enters only the *if* half of V.18. **Everything else in §3 — including the entire
counting lemma forward theory, weak regularity, total boundedness, all extremal theorems,
the sampling lemmas, the robustness theorems, and the uniqueness theorem of V.22 — is
axiom-free.** You can confirm any particular claim with `#print axioms <name>`, or trust the
pinned lists in `Graphons/Tests/AxiomGuard.lean`.

---

## §5 How to audit this library yourself

1. **Check the statements** (the only thing that can be wrong): read §2's definitions against
   the named files, and any theorem of §3 you care about — searching the theorem name in
   `Graphons/` finds a statement usually under 10 lines.
2. **Build it**: `lake exe cache get && lake build` (Mathlib v4.30.0). Success certifies
   every proof.
3. **Check the axioms**: open any file and run `#print axioms <theorem>`, or read
   `Graphons/Tests/AxiomGuard.lean`, where the expected output of `#print axioms` for every
   flagship is pinned verbatim — the build fails on any drift.
4. **Check the numbers**: `python3 scripts/hom_density_reference.py` recomputes, by brute
   force and independently of Lean, every concrete density pinned in
   `Graphons/Tests/Concrete.lean`.
5. **Check the discriminating power**: `bash scripts/mutation_test.sh` deliberately breaks the
   core definitions one at a time (product→sum in the density integrand, complemented step
   graphon, …) and confirms the suite rejects each mutant ([`MUTATION_MATRIX.md`](MUTATION_MATRIX.md)).

Provenance (how the library was built, including the knowledge-graph target selection and the
AI plan-loop) is documented in [`METHODOLOGY.md`](METHODOLOGY.md) and the dated narrative
[`HISTORY.md`](HISTORY.md); none of it is part of the trust base — only the statements, the
build, and the four axioms above are.
