# Vetting — `cutDist_eq_zero_of_homDensity_eq`

Captured soundness-review records for `cutDist_eq_zero_of_homDensity_eq`
(`Graphons/Characterization/CountingConverse.lean:67`). Linked from `AXIOM_AUDIT.md`.

---

```yaml
---
axiom: cutDist_eq_zero_of_homDensity_eq
file: Graphons/Characterization/CountingConverse.lean:67
statement_hash: null            # populate at L3
model: n/a                      # in-repo red-team; verbatim transcript not retained
tool: n/a
source_code: LP, SA             # literature proof (Lovász Thm 11.3) + self-audit
date: 2026-06-16
questions: [typing, strength, non-vacuity, satisfiability]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Axiom statement vetted (verbatim):**
```lean
axiom cutDist_eq_zero_of_homDensity_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω] (U W : Graphon Ω μ)
    (h : ∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
        homDensity F U = homDensity F W) :
    cutDist U W = 0
```

**Reference:** Lovász, *Large Networks and Graph Limits* (AMS Coll. Publ. 60,
2012), Thm 11.3 ("two graphons are weakly isomorphic iff they have the same
homomorphism densities") ≡ the inverse counting lemma (§10.4 / Thm 11.5).

**Reasoning digest:** `SATISFIABLE` — this is the standard direction of the
equivalence between the homomorphism-density topology and the cut-distance topology.
**Non-vacuous:** distinct graphons differ in some subgraph density (an Erdős–Rényi
`p`-quasirandom graphon is separated from another edge density already by `t(K₂,·)`),
so the contrapositive has witnesses; the axiom collapses no genuinely distinct
classes. **Right strength / not circular:** it is *not* a corollary of the
compactness axioms — it is the separation theorem itself; it does not load-bear on
`cutNorm_alignment_unit`/`dyadic_l1Cauchy_approx_unit`. Hypotheses (standard Borel,
probability carrier) match the sampling proof's needs.

**Conditions / follow-ups:** discharge via `W`-random sampling + a
second-moment/martingale argument (LNGL §10.4–§11.5). Re-vet if the carrier
hypotheses are weakened.
