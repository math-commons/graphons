# graphons

A Lean 4 / Mathlib formalization of **graphons and dense graph limits** (Lovász,
*Large Networks and Graph Limits*). AI-authored; targets derived from a
knowledge-graph-driven backlog and proved under an autonomous plan-loop with
adversarial review.

**Mathlib v4.30.0.** Build: `lake exe cache get && lake build`.

**Status: the library is `sorry`-free.** Every result compiles with only the standard axioms
`propext, Classical.choice, Quot.sound` — **except** the four deepest Tier-C results, which additionally
rest on **four documented, independently-vetted TRUE classical axioms** (each absent from Mathlib, slated
for discharge): `cutNorm_alignment_unit` + `dyadic_l1Cauchy_approx_unit` (*measure-theoretic*; compactness/
completeness on `[0,1]` — Birkhoff–vN/Rokhlin; dyadic conditional expectation + Lévy), `cutDist_eq_zero_of_homDensity_eq`
(*probabilistic*; the inverse counting lemma / separation), and `lovasz_szegedy_representability` (*algebraic*;
Lovász–Szegedy representability, owned by a sibling `reflection-positivity` development). The axiom audit is
in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md); `#print axioms` transparently shows each result's dependencies —
and the exact axiom list of every flagship theorem is **pinned in CI** by
[`Graphons/Tests/AxiomGuard.lean`](Graphons/Tests/AxiomGuard.lean) (`lake build` fails if any list drifts).

**Beyond the acceptance theorems, the library passed an extended validation campaign:** named extremal
consequences that were never design targets (**Goodman**, **Sidorenko-C₄** — Tier D); an
independently-reviewed **axiomatic characterization** with existence *and* uniqueness — the
spec of "a dense graph limit theory" has **exactly one model, and it is this construction**
(Tier E); the **first sampling lemma** connecting `homDensity` to W-random graphs, with independence
proved from an honest product measure (Tier F); **robustness equivalences** (pullback invariance,
couplings-vs-maps, the signed/factor-4 cut-norm sandwich); and executable differential tests against an
independent brute-force reference ([`scripts/hom_density_reference.py`](scripts/hom_density_reference.py)).
The acceptance/characterization argument is written up in [`audit/VALIDATION.md`](audit/VALIDATION.md).

## Design

Carrier is an **abstract probability space** `(Ω, μ)` (`[MeasurableSpace Ω] [IsProbabilityMeasure μ]`),
not hardcoded `[0,1]`. Core objects (`Graphons/Core/Basic.lean`):

- `SymmKernel Ω μ` — symmetric, measurable, bounded `ℝ`-kernel; an `AddCommGroup` + `Module ℝ`
  (so differences `U - W` are clean for the cut metric).
- `Graphon Ω μ extends SymmKernel` — additionally `[0,1]`-valued.
- `homDensity F W = ∫_{Ω^{V(F)}} ∏_{e∈E(F)} W(x_i,x_j) ∂(μ.pi)` — the homomorphism density `t(F,W)`,
  edges via `Sym2.lift`.

## What's proved

| Theme | Theorem(s) | File |
|---|---|---|
| Density basics | `homDensity_mem_Icc` (`0≤t≤1`), `homDensity_bot`, `homDensity_edge`, **`homDensity_const`** (Erdős–Rényi `p^{e(F)}`) | `Basic`, `Examples` |
| Cut norm | seminorm (`nonneg`/`smul`/`add_le`/`zero`/`neg`); `cutNorm_le_L1`; `cutNorm_graphon = ∫∫W = t(K₂,W)`; **set-form** `cutNorm = sup_{S,T}|∫_{S×T}W|` | `CutNorm*`  |
| Cut distance | couplings + `overlay`; **`cutDist` is a pseudometric** (`nonneg`/`comm`/`self`/**`triangle`** via the Gluing Lemma, `[StandardBorelSpace]`) | `CutDist`, `Gluing` |
| Counting lemma | **`abs_homDensity_sub_le`** `|t(F,U)−t(F,W)| ≤ e(F)·cutNorm(U−W)`; **forward** `abs_homDensity_sub_le_cutDist`, `homDensity_eq_of_cutDist_eq_zero` (`cutDist=0 ⇒ ∀F equal`) | `CountingLemma*` |
| Multiplicativity | `homDensity_sum` `t(F₁⊕F₂,W)=t(F₁,W)·t(F₂,W)` | `Multiplicativity` |
| Finite graphs | `Graphon.step`, **`homDensity_step`** (= finite hom density) | `Step`, `StepDensity` |
| Graphon space | `GraphonEquiv` (equivalence), **`GraphonSpace`** quotient, descended `GraphonSpace.homDensity` | `GraphonSpace` |
| **Weak regularity** | **`weak_regularity`**: `∀ε>0 ∃P, cutNorm(W − stepW W P) ≤ ε` (energy-increment) | `WeakRegularity` |
| **Compactness / completeness** (mod 2 axioms) | `instCompactSpaceGraphonSpaceUnit`, `instCompleteSpaceGraphonSpaceUnit` (on `[0,1]`); `graphonSpace_totallyBounded` (axiom-free) | `Compactness`, `CompletenessUnit`, `BlockCoupling` |
| **Counting-lemma converse** (mod 1 axiom) | **`cutDist_eq_zero_iff_homDensity_eq`** (Lovász separation), `GraphonSpace.eq_iff_homDensity_eq` (moment map injective) | `CountingConverse` |
| **Representability** (mod 1 axiom) | **`representability`**: realized by graphon ↔ multiplicative ∧ normalized ∧ reflection-positive ∧ `[0,1]`-bounded (forward proved) | `Representability` |
| **Extremal applications** (Tier D) | **`goodman`** `t(K₃) ≥ 2t(K₂)²−t(K₂)`; **`sidorenko_C4`** `t(C₄) ≥ t(K₂)⁴`; degree/co-degree normal forms `t(P₃)=∫deg²`, `t(C₄)=∫∫coDeg²` | `Counting/Degree`, `Counting/CoDegree`, `Extremal/*` |
| **Axiomatic characterization** (Tier E) | spec `IsDenseGraphLimitTheory` (independently reviewed); **existence** `isDenseGraphLimitTheory_graphonSpace` (mod axioms #1–2); **uniqueness** `isDenseGraphLimitTheory_unique` (axiom-free) — *the spec has exactly one model: this one* | `Characterization/LimitSpec*`, `IntervalTransport` |
| **Sampling** (Tier F) | W-random graphs `G(n,W)` with **proved** independence; exact identity on injective placements; **`abs_expectedHomDensity_sub_le`** `\|E[t(F,G(n,W))]−t(F,W)\| ≤ k(k−1)/n`; `tendsto_expectedHomDensity` | `Sampling/WRandom`, `Sampling/SamplingLemma` |
| **Robustness** (Tier B ext) | `Graphon.pullback` δ□-invisible (`cutDist_pullback_self`); transport invariance; couplings dominate maps; **factor-4 sandwich** `cutNorm ≤ cutNormSigned ≤ 4·cutNorm` | `CutMetric/Robustness` |
| **Hardening** | axiom guard (exact lists pinned, CI-enforced); executable differential tests vs independent Python reference | `Tests/AxiomGuard`, `Tests/Concrete`, `scripts/` |

## Verification trail

Correctness can be checked **end-to-end, from informal mathematics to machine-checked proof**:

1. **[`audit/FAITHFULNESS.md`](audit/FAITHFULNESS.md) — the dictionary.** Written for a mathematician who
   knows Lovász (2012) but not Lean: how to read Lean statements and what to trust; each primary object
   with Lovász's definition, the exact Lean form, and an **encoding note** for every place the two differ
   (with the proved theorem reconciling them); the full theorem inventory (V.1–V.22) with LNGL references
   and one-line proof ideas; the four assumed axioms stated in full; and a concrete audit recipe.
2. **[`audit/VALIDATION.md`](audit/VALIDATION.md) — the argument.** Six independent lines of evidence that
   the definitions are LNGL's objects and not a look-alike: correct computed values (cross-checked outside
   Lean) · the structural laws + robustness of every encoding choice · the named theorems of the theory ·
   classical extremal consequences never designed for (Goodman, Sidorenko-C₄, Mantel) · an
   independently-reviewed **axiomatic characterization with exactly one model** (existence + axiom-free
   uniqueness) · the first sampling lemma. Plus adversarial hardening (axiom guard, mutation testing) and
   an explicit honest-limitations section.
3. **The Lean files (`Graphons/*.lean`) — the machine-checked proofs.** Ground truth: `lake build` is
   clean and `main` is `sorry`-free. `#print axioms` shows only `propext, Classical.choice, Quot.sound`
   for every result **except** the four Tier-C theorems, which additionally cite the four documented true
   axioms (see [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md)).

## Assurance conventions

This project follows
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance)
(verification / validation / faithfulness, axiom vetting, `formalization.yaml`,
comparator). Local settings:

| Setting | Where |
|---|---|
| Project card | [`formalization.yaml`](formalization.yaml) (repo root) |
| Axiom audit | [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) (repo root) — 4 active axioms |
| Vetting strictness | [`audit/vetting/policy.yml`](audit/vetting/policy.yml) — `L1` |
| Per-axiom vetting records | [`audit/vetting/`](audit/vetting/) |
| Faithfulness (informal↔formal) | [`audit/FAITHFULNESS.md`](audit/FAITHFULNESS.md) |
| Acceptance / characterization | [`audit/VALIDATION.md`](audit/VALIDATION.md) |
| Kernel axiom gate | [`Graphons/Tests/AxiomGuard.lean`](Graphons/Tests/AxiomGuard.lean) (pins `#print axioms`, CI-enforced) + [`audit/axiom_report.lean`](audit/axiom_report.lean) (report generator) |
| CI assurance gate | [`.github/workflows/assurance.yml`](.github/workflows/assurance.yml) → the hub's reusable `assure.yml` (build + axiom-report-in-sync + sorry-confinement; warn-only at `L1`) |
| Numeric cross-validation | [`scripts/hom_density_reference.py`](scripts/hom_density_reference.py) — independent brute-force `homDensity` oracle, per the hub's [`NUMERICAL_VALIDATION.md`](https://github.com/math-commons/formalization-assurance/blob/main/NUMERICAL_VALIDATION.md) |

> Machine-gate TODO: commit the golden `audit/axiom-report.txt` from a build
> (`lake env lean audit/axiom_report.lean > audit/axiom-report.txt`) and raise the
> policy from `L1` to `L2` to enforce — see [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md).

## Reference

L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012) — the
source for every definition and theorem above (cut metric §8, counting lemma §10, compactness §9,
separation Thm 11.3, representability Thm 5.54).
