# Axiom audit — graphons

*Last updated 2026-06-16.*

## Purpose

In this project an **axiom** is a *vetted, true classical theorem with a vetted
discharge plan* — a staging point, not a fundamental assumption. Format +
conventions:
[`math-commons/formalization-assurance/AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md).
Per-axiom *evidence* (model + reasoning) is under [`audit/vetting/`](audit/vetting/).

---

**Declared axioms: 4 — all 4 `declared-on-closure`; 0 discharged, 0 off-closure.**
Three measure-theoretic/probabilistic facts behind compactness + separation of
graphon space on the canonical `([0,1], Leb)` carrier, and one algebraic
representability theorem owned by `reflection-positivity`. Each flagship theorem's
`#print axioms` is therefore standard-3 **+ exactly its own axiom(s)** — *not*
standard-3 alone. (Closure status per
[`AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md#closure-status-orthogonal-to-the-rating)
— orthogonal to rating.)
*(Both numbers — declared count and on-closure count — are kernel facts; derive them
from the generated `audit/axiom-report.txt` + the headline closures, do not hand-edit
once that gate is live.)*

---

## Active axioms

### `cutDist_eq_zero_of_homDensity_eq`

**File**: `Graphons/Characterization/CountingConverse.lean:67`
**Statement** (informal): the **inverse counting lemma** / moment-determinacy — if
two graphons have equal homomorphism densities `t(F,·)` for *every* finite simple
graph `F`, then their cut distance is `0` (weak isomorphism). The converse half of
Lovász separation.
**Vetting**: **Likely correct** (`SA`, `GR`) — Lovász, *Large Networks and Graph
Limits* (2012), Thm 11.3 (≡ inverse counting lemma, §10.4 / Thm 11.5). Red-teamed
TRUE: faithful/conservative, non-vacuous (distinct edge densities are already
separated by `t(K₂,·)`), and *not* a corollary of the compactness axioms — it is
the separation theorem itself. → [vetting](audit/vetting/cutDist_eq_zero_of_homDensity_eq.md)
**Closure**: `declared-on-closure` — in the `#print axioms` of
`cutDist_eq_zero_iff_homDensity_eq` / `GraphonSpace.eq_iff_homDensity_eq`.
**Strategy / Plan**: `W`-random sampling + a second-moment/martingale argument
(LNGL §10.4–§11.5); orthogonal to the topological compactness already formalized.
**Consumers**: `cutDist_eq_zero_iff_homDensity_eq`, `GraphonSpace.eq_iff_homDensity_eq`
(moment-map injectivity / separation; V.17).

### `lovasz_szegedy_representability`

**File**: `Graphons/Characterization/Representability.lean:152`
**Statement** (informal): the genuine **Lovász–Szegedy graphon theorem** — a graph
parameter that is multiplicative, normalized, reflection-positive **and**
`[0,1]`-bounded is `t(·,W)` for some graphon `W`.
**Vetting**: **Likely correct** (`SA`, `GR`) — Lovász–Szegedy, *Limits of dense
graph sequences* (JCTB 96, 2006) = LNGL Thm 5.54 / §5.6 / Thm 14.31. Vetting
**caught a too-strong first version** (without the `[0,1]` bound, `f=2^{e(F)}` is
mult+norm+RP but `f(K₂)=2∉[0,1]` and is not graphon-realizable); the `IsBounded`
hypothesis was added before merge. Distinct from the finite rank-bounded FLS (JAMS
2007, Thm 2.4). → [vetting](audit/vetting/lovasz_szegedy_representability.md)
**Closure**: `declared-on-closure` — in the `#print axioms` of `representability`.
**Strategy / Plan**: owned and to be discharged in
`reflection-positivity` (`Graph.FLS.main` connection-matrix RP track
+ the cut-distance limit), not re-proved here.
**Consumers**: `representability` (the `RealizedByGraphon f ↔ …` iff; V.18).

### `cutNorm_alignment_unit`

**File**: `Graphons/Limits/CompletenessUnit.lean:311`
**Statement** (informal): on `([0,1], Leb)`, a fast `δ□`-Cauchy graphon sequence has
`δ□`-equivalent representatives that are **cut-norm**-Cauchy.
**Vetting**: **Likely correct** (`SA`) — Birkhoff–von Neumann coupling realization /
Rokhlin isomorphism (LNGL §9, Thm 9.23). Red-teamed TRUE: asserts only *cut-norm*
Cauchyness (the mode in which `δ□`-Cauchy sequences align on `[0,1]`), explicitly
**not** any `L¹`/`toLpFun` convergence of the reps (avoids the quasirandom
`L¹`-trap). → [vetting](audit/vetting/cutNorm_alignment_unit.md)
**Closure**: `declared-on-closure` — in the `#print axioms` of
`instCompactSpaceGraphonSpaceUnit` / `exists_tendsto_of_fast_unit`.
**Strategy / Plan**: formalize Rokhlin / Birkhoff–von Neumann measure-preserving
rearrangement approximation of couplings on `[0,1]` (measure theory; absent from
Mathlib).
**Consumers**: `exists_tendsto_of_fast_unit` → completeness/compactness of
`GraphonSpace ℝ unitMeasure` (V.15/V.16).

### `dyadic_l1Cauchy_approx_unit`

**File**: `Graphons/Limits/CompletenessUnit.lean:339`
**Statement** (informal): a cut-norm-Cauchy graphon sequence on `([0,1], Leb)` has
an `L¹`-Cauchy block-average sequence `S` that is `δ□`-close to it.
**Vetting**: **Likely correct** (`SA`) — dyadic conditional-expectation block
averages + Lévy upward martingale convergence (LNGL §9.2). Red-teamed TRUE: the
`L¹`-Cauchy object is the *block-average* sequence `S`, not the reps, so the
quasirandom counterexample to `L¹`-Cauchy *reps* does not apply.
→ [vetting](audit/vetting/dyadic_l1Cauchy_approx_unit.md)
**Closure**: `declared-on-closure` — in the `#print axioms` of
`instCompactSpaceGraphonSpaceUnit` / `exists_tendsto_of_fast_unit`.
**Strategy / Plan**: **dischargeable from Mathlib** — `condExp`,
`MeasureTheory.tendsto_eLpNorm_condExp`, `Lp` completeness; diagonalize over a
dyadic filtration whose σ-algebras generate the Borel σ-algebra of `[0,1]²`.
**Consumers**: `exists_tendsto_of_fast_unit` (with `cutNorm_alignment_unit`) →
completeness/compactness (V.15/V.16).

---

## Recently discharged

*(none yet — all four are active. The forward separation direction
`homDensity_eq_of_cutDist_eq_zero` is proved, not an axiom.)*

| Axiom | Discharged via | Where the proof lives |
|---|---|---|
| — | — | — |

---

## Verification

Audit the axiom **set**, not per-name patterns (per-name greps are a footgun: `-E`
silently drops `\b`, and a trailing-space pattern misses names that end a line — see
[`AXIOM_AUDIT_FORMAT.md`](https://github.com/math-commons/formalization-assurance/blob/main/AXIOM_AUDIT_FORMAT.md#auditing-presence--guarding-drift)).

```bash
# the live axiom set (ground truth) — extract once, then set-match tracked names:
git grep -hE "^(noncomputable )?axiom " -- 'Graphons' \
  | sed -E 's/^(noncomputable )?axiom +([A-Za-z0-9_]+).*/\2/' | sort -u
# authoritative form, when a build exists: enumerate from `#print axioms` of the headlines
```

> **Machine-gate status.** The shared reusable assurance gate is wired:
> `.github/workflows/assurance.yml` calls
> `math-commons/formalization-assurance/.github/workflows/assure.yml` (build →
> axiom-report-in-sync → sorry-confinement), with the generator at
> [`audit/axiom_report.lean`](audit/axiom_report.lean) and an empty
> [`audit/sorry-allowlist.txt`](audit/sorry-allowlist.txt) (graphons is sorry-free).
> Per `audit/vetting/policy.yml` strictness `L1`, the gate **warns** rather than
> blocks. Also `Graphons/Tests/AxiomGuard.lean` pins the flagship `#print axioms`
> traces inline (build fails if they drift). Remaining (need a build, so staged not
> faked): (1) commit the golden `audit/axiom-report.txt`
> (`lake env lean audit/axiom_report.lean > audit/axiom-report.txt`) and derive the
> counts/closure above from it, then raise the policy to `L2` to **enforce**;
> (2) the **drift guard** — a CI check failing on any axiom name in prose docs / open
> issue titles that is *absent* from the live set (a follow-up upstream too). See
> [`audit/vetting/policy.yml`](audit/vetting/policy.yml).
