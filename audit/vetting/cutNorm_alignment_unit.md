# Vetting — `cutNorm_alignment_unit`

Captured soundness-review records for `cutNorm_alignment_unit`
(`Graphons/Limits/CompletenessUnit.lean:311`). Linked from `AXIOM_AUDIT.md`.

---

```yaml
---
axiom: cutNorm_alignment_unit
file: Graphons/Limits/CompletenessUnit.lean:311
statement_hash: null            # populate at L3
model: n/a                      # in-repo red-team; verbatim transcript not retained
tool: n/a
source_code: LP, SA             # literature (Lovász LNGL §9) + self-audit
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
axiom cutNorm_alignment_unit (W : ℕ → Graphon ℝ unitMeasure)
    (hfast : ∀ k, cutDist (W k) (W (k + 1)) ≤ (1 / 2 : ℝ) ^ k) :
    ∃ W' : ℕ → Graphon ℝ unitMeasure,
      (∀ n, cutDist (W n) (W' n) = 0) ∧ CutNormCauchy W'
```

**Reference:** Lovász, *Large Networks and Graph Limits* (2012), §9 (esp. Thm 9.23
and the coupling/overlay description of `δ□`); Birkhoff–von Neumann coupling
realization / Rokhlin isomorphism on `([0,1], Leb)`.

**Reasoning digest:** `SATISFIABLE` — every coupling of `(Leb, Leb)` on the
atomless standard-Borel space `[0,1]` is cut-norm-approximated by graphs of
measure-preserving rearrangements (Birkhoff/doubly-stochastic-by-permutations,
transported via Rokhlin); pulling each `Wₙ` back along such a rearrangement makes the
kernels cut-norm-Cauchy while preserving the `δ□`-class. **No L¹-trap (key check):**
the conclusion asserts only **cut-norm** Cauchyness — exactly the mode in which
`δ□`-Cauchy sequences align on `[0,1]` — and *deliberately not* any `L¹`/`toLpFun`
convergence of the reps (the quasirandom counterexample rules out only the L¹ form,
which is avoided). Carrier fixed to `([0,1], unitMeasure)` where this holds.

**Conditions / follow-ups:** discharge by formalizing Rokhlin / Birkhoff–von Neumann
measure-preserving rearrangement approximation of couplings (measure theory; absent
from Mathlib). Re-vet if generalized off the `[0,1]` carrier.
