# Vetting — `lovasz_szegedy_representability`

Captured soundness-review records for `lovasz_szegedy_representability`
(`Graphons/Characterization/Representability.lean:152`). Linked from `AXIOM_AUDIT.md`.

---

```yaml
---
axiom: lovasz_szegedy_representability
file: Graphons/Characterization/Representability.lean:152
statement_hash: null            # populate at L3
model: n/a                      # in-repo red-team; verbatim transcript not retained
tool: n/a
source_code: LP, SA             # literature proof (Lovász–Szegedy) + self-audit
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
axiom lovasz_szegedy_representability (f : GraphParam)
    (hm : IsMultiplicative f) (hn : IsNormalized f) (hrp : ReflectionPositive f) (hb : IsBounded f) :
    RealizedByGraphon f
```

**Reference:** Lovász–Szegedy, *Limits of dense graph sequences* (JCTB 96, 2006);
Lovász, *Large Networks and Graph Limits* (2012), Thm 5.54 / §5.6, Thm 14.31.

**Reasoning digest:** `SATISFIABLE` — the genuine graphon representability
theorem. **Vetting caught a too-strong first version:** without the `[0,1]` value
bound `hb : IsBounded f`, the parameter `f F = 2^{e(F)}` is multiplicative,
normalized and reflection-positive yet `f(K₂) = 2 ∉ [0,1]` and is **not**
graphon-realizable — so `IsBounded` is essential and was added before merge.
**Distinctness:** this is the `[0,1]`-bounded graphon theorem, *not* the
finite-weighted **rank-bounded** Freedman–Lovász–Schrijver theorem (JAMS 2007,
Thm 2.4), which allows unbounded weights — a separate statement. Forward direction
(`t(·,W)` is mult/norm/RP/bounded) is proved in-repo; only the converse is axiomatized.

**Conditions / follow-ups:** owned and to be discharged in
`reflection-positivity` (`Graph.FLS.main` connection-matrix RP track +
the cut-distance limit), not re-proved here. Re-vet if the `IsBounded`/`ReflectionPositive`
definitions change.
