# Sketch: a Tau Ceti roadmap entry for graphons / dense graph limits

This is a **draft of the roadmap entry** we would propose for
[`FormalFrontier/TauCetiRoadmap`](https://github.com/FormalFrontier/TauCetiRoadmap) as
`TauCetiRoadmap/DenseGraphLimits/` (a `README.md` plus a `Targets.lean`). It lives in *our*
repo as a working sketch; it is written to the roadmap repo's own conventions ("build the
library not the theorem", "everything grounded in Mathlib/Tau Ceti", "use Mathlib's
vocabulary", "specify the mathematics not your code", "nothing is optional", "pin conventions
up front", "write Lean signatures").

**The binding constraint.** Tau Ceti `main` enforces, in CI: **no `sorry`, and no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`** (`TauCeti/AGENTS.md`). The roadmap repo itself
allows `sorry` in `Targets.lean` because those are *goals*. So every milestone below is a
discharge target stated with `sorry`; what lands in `TauCeti/` must be fully proved with only
the three kernel axioms. Concretely this means **neither source repo's deep tier upstreams
as-is** — `math-commons/graphons` is `sorry`-free but carries four custom axioms, and
`cameronfreer/graphon` has no custom axioms but three `sorry`s. The axiom-free / `sorry`-free
cores migrate first; the axioms and the `sorry`s become the discharge-gated milestones (Layers
3–5).

---

# Roadmap: graphons and dense graph limits (Lovász)

Mathlib has `SimpleGraph`, `Sym2`, homomorphism counts, probability measures, `AEEqFun`,
product/pi measures, conditional expectation, and `StandardBorelSpace`, but **no theory of
dense graph limits**: no graphon, no homomorphism density `t(F, W)`, no cut norm or cut
distance, no weak regularity, no graphon space, no counting/inverse-counting lemmas. We build
that theory here, after Part 3 of Lovász, *Large Networks and Graph Limits* (LNGL), culminating
in the equivalence of cut-distance convergence with convergence of all homomorphism densities.

The spine is: `Graphon → homDensity → cutNorm → cutDist → GraphonSpace → counting →
regularity → compactness → separation → convergence`. Named theorems (weak regularity, the
counting lemma, compactness, separation) are milestones inside the fuller development, not the
whole of it; each object gets its complete basic API.

**Suggested home:** `TauCeti/Combinatorics/DenseGraphLimits/`.

## Conventions (pinned up front)

These are decided now so implementors don't drift. Rationale for each lives in the two design
records in `math-commons/graphons/docs/` (carrier encoding; coupling-primary cut distance).

1. **Carrier — strict measurable function, quotient on top.** A graphon is an honest
   `W : Ω → Ω → ℝ` on a probability space `(Ω, μ)`, symmetric/measurable/`[0,1]`-valued
   *everywhere*, carrying a pointwise `Module ℝ` on the underlying symmetric kernels (so `U − W`
   is literal, for the cut metric). The a.e. / weak-isomorphism identification is taken **once**,
   at `GraphonSpace`. The explicit `AEEqFun` bridge is a named deliverable (Layer 3), built where
   the a.e. view is first needed — the conditional-expectation arguments of Layer 4 — and is also
   the interop point with a natively-`AEEqFun` development; earlier layers consume only the strict
   carrier. Rule: **construction may be representative-based; every user-facing theorem must be
   quotient-stable.**
2. **Cut distance — coupling-primary.** `cutDist` is `⨅` over couplings of the cut-norm of the
   overlay; the triangle inequality is the gluing lemma. Agreement with the classical
   measure-preserving-map infimum is a **named milestone** (Layer 5), not the definition.
3. **Finite graphs — simple, `Sym2` edges.** `SimpleGraph V` with `[Fintype V]`; edges via
   `SimpleGraph.edgeFinset` / `Sym2`; density normalized `t(F, W_G) = hom(F,G)/|V(G)|^{|V(F)|}`.
   Weighted graphs appear only as the technically convenient dense subset for the
   characterization layer, never as the primary object.
4. **Carrier generality.** Core definitions over an arbitrary probability space; conditioning
   and sampling over `StandardBorelSpace`; compactness/separation over atomless standard Borel
   (≅ `[0,1]`), with explicit transport. Flagship results get a general statement and a `[0,1]`
   corollary.
5. **Vocabulary.** Neutral namespace `DenseGraphLimits.{Kernel, Graphon, HomDensity, CutNorm,
   CutMetric, GraphonSpace, StepGraphon, Sampling}`; reuse Mathlib names wherever they exist.

## What Mathlib already has (consume)

- **Finite graphs:** `Combinatorics/SimpleGraph/*` (`SimpleGraph`, `edgeFinset`, `Hom`), `Sym2`.
- **Measure/probability:** `MeasureTheory.Measure`, `IsProbabilityMeasure`, `Measure.prod`,
  `Measure.pi`, `MeasureTheory.AEEqFun`, `Lp`; `MeasureTheory.condExp` (conditional
  expectation); `MeasureTheory.MeasurePreserving`; `MeasurableSpace`, `StandardBorelSpace`,
  `PolishSpace`.
- **Topology of the target:** conditionally-complete-lattice / `iInf` API for the cut-norm and
  cut-distance infima; `Metric`/`PseudoMetric`/`UniformSpace` for `GraphonSpace`.
- **Known gap to consume-or-build:** the **measure-preserving** isomorphism of atomless
  standard Borel spaces with `([0,1], vol)`. Mathlib has `PolishSpace.measurableEquiv` but not
  the measure-preserving version; this is the input to Layer 5 (and to Cameron's
  `exists_common_extension`).

## What is missing (build here)

Everything graphon-specific: the `Graphon` object and kernel algebra, `homDensity`, `cutNorm`
(seminorm + set form), the coupling `cutDist` and its gluing triangle, `GraphonSpace`, the
counting lemma (both directions), step approximation / weak regularity, total
boundedness/completeness/compactness, inverse counting / separation, and the convergence
equivalence. None of it is upstream.

---

## The build, in layers

As each layer makes the next layer's *types* expressible in `TauCeti/`, state its milestones in
`Targets.lean` (with `sorry`). Status tags: **[migrate]** = axiom-free/`sorry`-free in a source
repo, port it; **[discharge]** = currently an axiom in `math-commons/graphons` and/or a `sorry`
in `cameronfreer/graphon`, must be genuinely proved to land in `TauCeti/`.

### Layer 0 — finite-graph + measure scaffolding **[migrate]**
The `Sym2`-edge density helpers, product/pi-measure curry/uncurry lemmas, and the
`StandardBorelSpace` plumbing both repos already have. Reconcile names with Mathlib; drop any
wrapper that duplicates an existing predicate.

### Layer 1 — core objects and the axiom-free spine **[migrate]**
`Graphon`/`SymmKernel` (carrier convention §1), `homDensity` with its full basic API
(`homDensity_mem_Icc`, `homDensity_const = p^{e(F)}`, `homDensity_edge`, multiplicativity over
disjoint unions, finite-graph compatibility `homDensity_step`), `cutNorm` (seminorm laws,
`cutNorm_le_L1`, the set form `cutNorm = sup |∫_{S×T} W|`), the coupling `cutDist` with the
**gluing-lemma triangle** (`cutDist` a pseudometric), and `GraphonSpace`. All of this is
`sorry`-free and axiom-free in both repos today; it is the launch pad.

### Layer 2 — counting, regularity, total boundedness **[migrate]**
The **forward counting lemma** `|t(F,U) − t(F,W)| ≤ e(F)·‖U−W‖□` and its `cutDist` form;
descent of `t(F,·)` to `GraphonSpace`; **Frieze–Kannan weak regularity** with the `4^{⌈1/ε²⌉}`
complexity bound; step graphons are `δ□`-dense and `(GraphonSpace, δ□)` is **totally bounded**.
Axiom-free in `math-commons/graphons` today.

### Layer 3 — the L⁰ / `AEEqFun` bridge **[build]**
A round-trip adapter between the strict carrier and Mathlib's `AEEqFun`: a map
`Graphon Ω μ → ((Ω × Ω) →ₘ[μ ⊗ μ] ℝ)` and a measurable-representative section back, with
`homDensity`, `cutNorm`, and `cutDist` proved to factor through the a.e. class. This is where
the a.e. view enters the development — explicitly, in one place — so the conditional-expectation
and martingale arguments of Layer 4 run in `L⁰` and transport back to the strict object, and so
a natively-`AEEqFun` development (Cameron's) interoperates with this one. Built here as the
prerequisite for Layer 4; Layers 1–2 consume only the strict carrier. Genuinely new — neither
source repo has a cross-carrier bridge (one is strict-only, the other `AEEqFun`-only).

### Layer 4 — completeness and compactness **[discharge]**
Completeness and compactness of `GraphonSpace` over atomless standard Borel (the
Lovász–Szegedy compactness theorem). Discharges the two measure-theoretic axioms
`cutNorm_alignment_unit` and `dyadic_l1Cauchy_approx_unit` (Birkhoff–von Neumann / Rokhlin
realignment; dyadic conditional-expectation + martingale `L¹`-Cauchy). Mathlib's `condExp` and
martingale convergence are the engine.

### Layer 5 — coupling ↔ map equivalence **[discharge]**
`cutDist_coupling = cutDist_pullback` under atomless standard Borel. **Single milestone that
clears a gap on both sides**: `math-commons/graphons`' open "maps attain the coupling infimum"
direction *and* `cameronfreer/graphon`'s `exists_common_extension` / Rokhlin `sorry`. Gated on
the missing Mathlib measure-isomorphism theorem, so run it **in parallel**, not on the critical
path.

### Layer 6 — separation / inverse counting (the summit) **[discharge]**
`δ□(U,W) = 0 ⟺ ∀ F, t(F,U) = t(F,W)`; hence the moment map is injective on `GraphonSpace`; hence
the convergence equivalence `δ□(Wₙ, W) → 0 ⟺ ∀F, t(F,Wₙ) → t(F,W)`. Discharges
`math-commons/graphons`' axiom `cutDist_eq_zero_of_homDensity_eq` and is exactly
`cameronfreer/graphon`'s active `InverseCounting` / `MatrixDetermination` / `CycleKrylov` work
(issue #70). **Highest-leverage self-contained target.**

### Layer 7 — applications and validation **[migrate]**
Extremal consequences as acceptance tests (Goodman, Mantel, Sidorenko-`C₄`), the W-random
sampling-expectation lemma `E[t(F, G(n,W))] → t(F,W)`, and the concrete rational density tests.
These keep the definitions honest and give visible checkpoints before Layers 4–6 close.

### Layer 8 — Lovász–Szegedy representability **[discharge]**
Graph parameters are `= t(·, W)` iff multiplicative / normalized / reflection-positive /
`[0,1]`-bounded — the fourth `math-commons/graphons` axiom (`lovasz_szegedy_representability`).
Best discharged in coordination with a reflection-positivity development rather than re-proved
here; sequenced late because it depends on that external track, but it is work we want, not
optional.

### Layer 9 — sampling and exchangeable arrays **[build]**
The almost-sure first sampling lemma and the second sampling lemma `δ□(G(n,W), W) → 0`
(LNGL Lemma 10.16), then the exchangeable-arrays / Aldous–Hoover bridge connecting graphons to
Cameron's `exchangeability` project. The natural long-horizon endpoint; later than the spine,
but on the roadmap.

### Upstream to Mathlib **[defer]**
Several prerequisites are reusable beyond graphons and are upstream candidates — but only once
the API has stabilized here; premature upstreaming churns against Mathlib review. Deferred, not
omitted. Initial inventory:
- the **measure-preserving** isomorphism of an atomless standard Borel space with `([0,1], vol)`
  (the Layer 5 gate; Mathlib has only the measurable-equiv version);
- reusable **conditional-expectation / dyadic-martingale `L¹`-convergence** lemmas (Layer 4);
- **finite product / `Measure.pi` curry–uncurry** lemmas (Layer 0);
- **`AEEqFun` ergonomics** exercised by the Layer 3 bridge.
No upstreaming is scheduled before Layers 1–4 are `sorry`-free in `TauCeti/`.

---

## Prototype target signatures (excerpt for `Targets.lean`)

```lean
import Mathlib

namespace TauCetiRoadmap.DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Layer 1. A graphon: strict symmetric measurable `[0,1]`-valued kernel (carrier §1). -/
structure Graphon (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] where
  toFun  : Ω → Ω → ℝ
  symm'  : ∀ x y, toFun x y = toFun y x
  meas'  : Measurable (Function.uncurry toFun)
  mem01' : ∀ x y, toFun x y ∈ Set.Icc (0:ℝ) 1

/-- Layer 1. Homomorphism density `t(F, W)`, edges via `Sym2`. -/
noncomputable def homDensity {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) : ℝ := sorry

/-- Layer 1. Erdős–Rényi sanity value (acceptance gate). -/
example {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (W : Graphon Ω μ) :
    homDensity μ F W = p ^ F.edgeFinset.card := sorry  -- for the constant-p graphon

/-- Layer 2. Forward counting lemma. -/
example {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (U W : Graphon Ω μ) :
    |homDensity μ F U - homDensity μ F W| ≤ F.edgeFinset.card * cutNorm μ (U - W) := sorry

/-- Layer 2. Frieze–Kannan weak regularity, standard complexity bound. -/
example (W : Graphon Ω μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Partition Ω, P.card ≤ 4 ^ ⌈1 / ε ^ 2⌉₊ ∧ cutNorm μ (W - stepW W P) ≤ ε := sorry

/-- Layer 3 [build]. L⁰ bridge: `homDensity` (and `cutNorm`/`cutDist`) factor through the
    a.e. class, so the strict carrier and the `AEEqFun` carrier agree on all observables. -/
example {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj] (U W : Graphon Ω μ)
    (h : toAEEqFun U = toAEEqFun W) : homDensity μ F U = homDensity μ F W := sorry

/-- Layer 4 [discharge]. Compactness of graphon space over `[0,1]`
    (discharges `cutNorm_alignment_unit`, `dyadic_l1Cauchy_approx_unit`). -/
example : CompactSpace (GraphonSpace (volume.restrict (Set.Icc (0:ℝ) 1))) := sorry

/-- Layer 5 [discharge]. Coupling ↔ map cut distance (atomless standard Borel).
    Discharges this repo's open direction and Cameron's `exists_common_extension`. -/
example [StandardBorelSpace Ω] (U W : Graphon Ω μ) :
    cutDistCoupling μ U W = cutDistPullback μ U W := sorry

/-- Layer 6 [discharge]. Separation / inverse counting — the summit.
    Discharges `cutDist_eq_zero_of_homDensity_eq`; = Cameron's issue #70. -/
example [StandardBorelSpace Ω] (U W : Graphon Ω μ) :
    cutDist μ U W = 0 ↔
      ∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
        homDensity μ F U = homDensity μ F W := sorry

end TauCetiRoadmap.DenseGraphLimits
```

## Worked examples (acceptance gates)

Non-negotiable, independent of implementation: `homDensity_const` (`p^{e(F)}`); finite-graph
compatibility `t(F, W_G) = hom(F,G)/|V(G)|^{|V(F)|}`; cut-norm set/test-function equivalence;
the counting lemma; weak regularity; `cutDist` a pseudometric; compactness; separation;
`E[t(F,G(n,W))] → t(F,W)`; and at least Goodman + Mantel + Sidorenko-`C₄`. "Done" means the
result **descends to the intended quotient and passes the gates**, not merely compiles.

## Ordering

Layers 0–2 and 7 first (all `[migrate]`, axiom-free today) — they validate the pipeline and
give visible checkpoints. The L⁰ bridge (Layer 3) lands next, as the prerequisite for the
analytic layers. Then Layer 6 (separation) as the highest-leverage self-contained summit, with
Layer 4 (compactness) alongside it. Layer 5 (coupling↔map) runs in parallel, gated on the
Mathlib measure-isomorphism theorem, and must not block the others. Representability (Layer 8),
sampling/exchangeable arrays (Layer 9), and the Mathlib upstreaming follow.

## Provenance (secondary — reviewers judge the math, not this map)

Two independent sources, to be migrated then discharged, not imported wholesale:
- [`math-commons/graphons`](https://github.com/math-commons/graphons) — `sorry`-free, four
  audited axioms (`cutNorm_alignment_unit`, `dyadic_l1Cauchy_approx_unit`,
  `cutDist_eq_zero_of_homDensity_eq`, `lovasz_szegedy_representability`); broad packaged theory
  (`GraphonSpace`, extremal consequences, sampling, characterization), coupling `cutDist`,
  strict carrier. Supplies Layers 0–2, 7 and the axiom→discharge tickets for 4–6, 8.
- [`cameronfreer/graphon`](https://github.com/cameronfreer/graphon) — no custom axioms, three
  `sorry`s (`exists_common_extension`, algebraic determination, the determination theorem);
  blueprint + dependency graph; `AEEqFun` carrier, measure-preserving-map `cutDist`; active
  spectral/determination work (issue #70). Supplies the proof routes for Layers 3, 5–6 and the
  blueprint dependency spine.

## References

- L. Lovász, *Large Networks and Graph Limits* (2012), Part 3 (§7.1, §8.2, §9.2, Ch. 11,
  Ch. 13).
- C. Borgs, J. Chayes, L. Lovász, V. Sós, K. Vesztergombi, *Convergent sequences of dense
  graphs I–II*.
```
