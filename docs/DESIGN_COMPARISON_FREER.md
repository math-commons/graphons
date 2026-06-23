# Design record: graphon kernel encoding — strict function vs L⁰ class

- **Status:** accepted   <!-- the strict-function carrier; resolved in DESIGN.md §1–§2 -->
- **Date:** 2026-06-21   <!-- standardized to the design-record format; decision itself resolved earlier (Basic.lean refactor f83cd73) -->
- **Affects:** `Graphons/Core/Basic.lean`, `Graphons/CutMetric/CutDist.lean`,
  `Graphons/Space/GraphonSpace.lean`; the `SymmKernel` / `Graphon` / `GraphonSpace` objects.

*(Format: `math-commons/formalization-assurance` → `DESIGN_RECORDS.md`.)*

## Context

There are two independent Lean 4 / Mathlib formalizations of dense graph limit theory (Lovász,
*Large Networks and Graph Limits*): this one (`math-commons/graphons`) and Cameron Freer's
(`cameronfreer/graphon`, started 2026-01). They formalize the **same mathematics** — graphons
over an abstract probability space, cut norm/distance, weak regularity, the counting and
inverse counting lemmas, compactness, convergence equivalence — but they make the opposite
choice on the single most basic design question: **how the graphon object is encoded.** This
record fixes that choice and its rationale so it is not rediscovered each time the two repos
are compared.

## Decision

Encode the kernel as a **strict curried function** `toFun : Ω → Ω → ℝ` with the structural
conditions (symmetry, measurability, bound) holding **everywhere**, and build the
a.e. / weak-isomorphism quotient **explicitly on top** (`GraphonEquiv` → `GraphonSpace`).
This is chosen over Freer's `AEEqFun` (L⁰-class) carrier.

## Alternatives considered

The one decision that drives everything: strict function vs L⁰ class.

| | this library (chosen) | `cameronfreer/graphon` |
|---|---|---|
| Kernel field | `toFun : Ω → Ω → ℝ` — an honest curried function | `toAEEqFun : (α×α) →ₘ[μ.prod μ] ℝ` — an `AEEqFun` (L⁰ class) |
| Symmetry | `∀ x y, W x y = W y x` (**everywhere**) | `∀ᵐ p, W p.swap = W p` (**a.e.**) |
| Measurability | explicit field `Measurable (uncurry toFun)` | intrinsic to `AEEqFun` |
| Bound | `∃ C, ∀ x y, |W x y| ≤ C`; `Graphon` adds pointwise `0 ≤ W ≤ 1` | `ae_mem_Icc` (∈ [0,1] a.e.); separate `SignedGraphon` for `|·| ≤ 1` a.e. |
| Differences `U − W` | full `AddCommGroup` + `Module ℝ` on `SymmKernel` (pointwise) | no module; a dedicated `SignedGraphon` type with a `sub` operation |
| A.e. quotient | **explicit, on top**: `GraphonEquiv` → `GraphonSpace` | **native to the carrier**: `AEEqFun` is already L⁰ |

`homDensity` is essentially the same object in both: `∫_{V→Ω} ∏_{e∈E(F)} W(x_i,x_j)`. This
library lifts edges through `Sym2.lift`/`edgeVal` over a custom `piMeasure`; Freer iterates
`F.edgeFinset` with `Quot.out` over `Measure.pi`. Same `t(F,W)`.

Relevant files — here: `Graphons/Core/Basic.lean`, `Graphons/CutMetric/CutDist.lean`,
`Graphons/Space/GraphonSpace.lean`. Freer: `Graphon/Basic.lean`, `Graphon/CutDistance.lean`,
`Graphon/Convergence.lean`.

## Consequences

Neither encoding is more general in the **domain** — both are parametric in an arbitrary
probability space `(Ω, μ)` with `[IsProbabilityMeasure μ]`, and both specialize to the unit
interval (our `unitMeasure`; his `GraphonI`). The trade-off is in the **object encoding**:

- **Buys (our strict-function carrier).** `W x y` is a real number at a real point, so
  pointwise algebra is literal and `simp`-friendly; concrete graphons are easy to build
  (`mk'`, `Examples.lean`); and a genuine `Module ℝ` makes `U − W` and `c • W` first-class —
  exactly what cut-norm/cut-distance estimates need.
- **Costs.** We carry measurability/symmetry/bound proofs explicitly and owe the a.e. quotient
  by hand, once, at `GraphonSpace`.
- **The canonical alternative (Freer's `AEEqFun`).** The object *is* the a.e.-equivalence
  class, so a.e.-equal kernels are already equal, measurability is automatic, and the existing
  Mathlib L⁰ API (integration, pushforward/pullback, the "right" equality) comes for free. It
  points straight at the limit object, at the cost of painful pointwise work on each estimate.

This is the textbook L⁰-vs-honest-function tension: a.e.-classes give the right equality but
are painful pointwise; honest functions give painless pointwise algebra but owe the quotient.
Plausibly it explains the divergence in coverage — the ergonomic carrier let this library
sweep broad explicit results quickly (extremal consequences, the validation campaign), while
the canonical carrier sits closer to the true objects but adds friction to each estimate.

**The quotient is the same in both.** Both libraries ultimately study **graphon space modulo
weak isomorphism (`δ□ = 0`)**, not mere a.e. equality — the correct identification (LNGL §8.2
/ Ch. 11 / Ch. 13). Here that is `GraphonEquiv U W := cutDist U W = 0`, packaged as a `Setoid`,
with `δ□` defined via couplings; see [`../audit/FAITHFULNESS.md`](../audit/FAITHFULNESS.md) §2.5
and [`../audit/VALIDATION.md`](../audit/VALIDATION.md) §3. Our strict carrier's over-fineness
washes out at exactly one point: a.e.-equal graphons satisfy `δ□ = 0` (`cutDist_le_cutNorm` +
`cutNorm_le_L1`) and so become equal in `GraphonSpace`. Freer reaches the same quotient from a
carrier that has already collapsed a.e. equality.

## Bridging / migration

The translation between the two encodings is asymmetric:

- **Ours → his is easy.** Our strict `toFun` with everywhere-conditions maps cleanly into
  `AEEqFun.mk`; the strict symmetry/bounds imply his a.e. versions for free.
- **His → ours is the hard direction (lossy).** Recovering an honest `Ω → Ω → ℝ` with symmetry
  and bounds holding *everywhere* from an L⁰ class requires choosing a measurable strict
  representative — the classic lossy step.

So a clean combination keeps our strict carrier as the working layer and bridges *up* into his
L⁰ layer for the canonical statements: ergonomics for the proofs, canonical equality for the
final theorems.

## Where the repos can actually help each other

Our deepest debt is **axiom #3** (`cutDist_eq_zero_of_homDensity_eq`, inverse counting / the
separation direction, LNGL Thm 11.3) — the converse that makes homomorphism densities
*characterize* the quotient. Freer is actively proving exactly this in
`Graphon/InverseCounting.lean` and the spectral/determination machinery
(`Spectral.lean`, `MatrixDetermination.lean`, `CycleKrylov.lean`; issue #70, axiom-clean,
following the book proof). That is the single most valuable point of contact between the two
projects.
