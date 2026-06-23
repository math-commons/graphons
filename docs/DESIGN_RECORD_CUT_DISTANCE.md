# Design record: cut distance — coupling-primary, with the map equivalence as a milestone

- **Status:** accepted   <!-- coupling formulation is primary in CutDist.lean -->
- **Date:** 2026-06-23
- **Affects:** `Graphons/CutMetric/CutDist.lean`, `Graphons/CutMetric/Gluing.lean`,
  `Graphons/CutMetric/Robustness.lean`, `Graphons/Space/GraphonSpace.lean`; the `cutDist`
  definition, the `GraphonEquiv`/`GraphonSpace` quotient, and every δ□-level theorem.

*(Format: `math-commons/formalization-assurance` → `DESIGN_RECORDS.md`. Companion to
[`DESIGN_COMPARISON_FREER.md`](DESIGN_COMPARISON_FREER.md), which records the kernel-encoding
choice.)*

## Context

Cut distance `δ□(U, W)` between graphons admits two standard definitions, and the two
independent Lean formalizations of dense graph limit theory split on which to take as primary:
this library (`math-commons/graphons`) uses **couplings**, Cameron Freer's
(`cameronfreer/graphon`) uses **measure-preserving maps**. The two definitions agree on the
spaces that matter, but only as a theorem with hypotheses — not definitionally. This record
fixes our choice and, crucially, records *how* the disagreement with the map formulation is to
be resolved (a named target theorem, not a fork).

### The two definitions

**Map / pullback formulation** (classical Lovász, LNGL §8.2; Cameron's choice):
```
δ□(U, W) = inf over measure-preserving φ, ψ from a common space of ‖Uᵠ − Wᵠ‖□
```
Align the two graphons by relabeling vertices via measure-preserving maps, then take the
cut-norm of the difference, minimized over alignments.

**Coupling formulation** (this library; `Graphons/CutMetric/CutDist.lean`):
```
def IsCoupling (μ₁ μ₂) (π : Measure (Ω₁ × Ω₂)) : Prop :=
  π.map Prod.fst = μ₁ ∧ π.map Prod.snd = μ₂

noncomputable def cutDist (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) : ℝ :=
  ⨅ π : {π // IsCoupling μ₁ μ₂ π}, cutNorm (overlay U W π)
```
where `overlay U W π` is the kernel `((x,x'),(y,y')) ↦ U(x,y) − W(x',y')` on the coupled
space. Join the two carriers by a coupling and take the cut-norm of the difference on the
joined space.

## Decision

Take the **coupling formulation as the primary definition** of `δ□`, and define
`GraphonEquiv U W := cutDist U W = 0` and `GraphonSpace` on top of it. State the agreement
with the classical map/pullback formula — `cutDist_coupling = cutDist_pullback` under atomless
standard-Borel hypotheses — as a **named milestone theorem**, not as a definitional commitment.

## Rationale

1. **Carrier-general.** The coupling definition is well-posed and well-behaved for graphons on
   *arbitrary, possibly different* probability spaces, with no atomlessness or standardness
   assumption needed merely to state it. The product measure `μ₁ ×ˢ μ₂` is always a coupling,
   so the `⨅` ranges over a nonempty, bounded-below index and the conditionally-complete-lattice
   API applies cleanly (no junk-`sInf` = 0 pathology). The map formulation needs a common
   source space and measure-preserving maps, which is awkward in general and only behaves like
   "the right" notion on atomless standard Borel spaces.

2. **Gluing triangle.** The triangle inequality `δ□(U,W) ≤ δ□(U,V) + δ□(V,W)` falls out in the
   coupling picture via the **Gluing Lemma** (`Graphons/CutMetric/Gluing.lean`, `cutDist_triangle`):
   given a coupling of `(U,V)` and one of `(V,W)`, glue them along the shared `V`-marginal by
   disintegration to produce a coupling of `(U,W)`. It needs the standard-Borel hypothesis, as
   in the classical treatment. In the map formulation the same step requires common
   refinements/extensions — exactly where Cameron's `exists_common_extension` / Rokhlin `sorry`
   sits.

3. **The equivalence is a theorem with hypotheses, not a free identity.** On atomless standard
   Borel spaces every carrier is measure-isomorphic to `([0,1], Leb)`, so couplings and
   measure-preserving maps coincide and the two infima are equal (LNGL Lemma 8.13). On spaces
   with atoms the map infimum can misbehave while couplings stay robust — another reason
   couplings are the better primary object.

## Alternatives considered

| Cut-metric presentation | Advantages | Risks |
|---|---|---|
| **Couplings (chosen)** | Carrier-general; clean triangle via gluing; nonempty/bounded index; transport-style. | Needs a bridge theorem to recover the textbook map formula; user may ask "is this exactly Lovász's δ□?" |
| **Measure-preserving maps** | Closest to many textbook statements; natural for weak isomorphism. | Heavy common-extension / Rokhlin / measure-isomorphism infrastructure up front (Cameron's repo lists this as a remaining `sorry`). |
| **Definitional fork (each repo picks one, silently)** | No work. | The two libraries disagree on what `δ□` *means*; no interop; perpetual "which is the real one" argument. |

## Consequences

- **The quotient is correct without the equivalence.** `GraphonSpace = Quotient (δ□ = 0)` is
  weak isomorphism (LNGL §8.2 / Ch. 11 / Ch. 13) and all downstream theory — compactness,
  total boundedness, separation, descent of `t(F,·)` — is well-defined and provable on the
  coupling definition *without* first proving `cutDist_coupling = cutDist_pullback`. The
  equivalence is therefore a **faithfulness/compatibility result, not on the critical path**.
- **Relations available without the equivalence are already proved** (`Graphons/CutMetric/Robustness.lean`):
  maps bound couplings (`cutDist_le_cutNorm_pullback_sub`); pullback along a measure-preserving
  map is δ□-invisible (`cutDist_pullback_self`); transport of both graphons along one map
  preserves δ□ exactly (`cutDist_pullback_pullback`). Downstream uses of δ□ are insensitive to
  the formulation through these.
- **The open direction is documented.** That maps *attain* the coupling infimum on atomless
  standard Borel spaces is the one classical equivalence not yet proved here — blocked on the
  missing Mathlib measure-isomorphism theorem. Disclosed in
  [`../audit/FAITHFULNESS.md`](../audit/FAITHFULNESS.md) §2.4 and
  [`../audit/VALIDATION.md`](../audit/VALIDATION.md), not hidden.
- **One milestone discharges a gap on both sides.** Proving `cutDist_coupling = cutDist_pullback`
  closes this library's open direction *and* Cameron's `exists_common_extension` / Rokhlin
  `sorry` at once — a single jointly-owned deliverable rather than a disagreement.

## Sequencing note

Because the coupling↔map equivalence is gated on Mathlib infrastructure neither project
controls (the measure-isomorphism theorem), it should be a **parallel** milestone, not the
headline one. The higher-leverage, more self-contained target is the **separation direction** —
this library's axiom `cutDist_eq_zero_of_homDensity_eq` (inverse counting, LNGL Thm 11.3),
which Cameron is actively proving in `InverseCounting` / `MatrixDetermination` / `CycleKrylov`
(issue #70). See [`DESIGN_COMPARISON_FREER.md`](DESIGN_COMPARISON_FREER.md) for that point of
contact.
