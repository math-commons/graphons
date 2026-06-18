# Vetting — `dyadic_l1Cauchy_approx_unit`

Captured soundness-review records for `dyadic_l1Cauchy_approx_unit`
(`Graphons/Limits/CompletenessUnit.lean:339`). Linked from `AXIOM_AUDIT.md`.

---

```yaml
---
axiom: dyadic_l1Cauchy_approx_unit
file: Graphons/Limits/CompletenessUnit.lean:339
statement_hash: null            # populate at L3
model: n/a                      # in-repo red-team; verbatim transcript not retained
tool: n/a
source_code: LP, SA             # literature (Lovász LNGL §9.2) + self-audit
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
axiom dyadic_l1Cauchy_approx_unit (W' : ℕ → Graphon ℝ unitMeasure)
    (hcn : CutNormCauchy W') :
    ∃ S : ℕ → Graphon ℝ unitMeasure,
      CauchySeq (fun n => toLpFun (S n)) ∧
        Tendsto (fun n => cutDist (W' n) (S n)) atTop (𝓝 0)
```

**Reference:** Lovász, *Large Networks and Graph Limits* (2012), §9.2 — dyadic
conditional-expectation block averages + Lévy upward martingale convergence.

**Reasoning digest:** `SATISFIABLE` — with `𝒢_k` the σ-algebra of the
`2^k×2^k` dyadic grid on `[0,1]²` and `Pₖ` the block-average projection: for fixed
`k`, `‖PₖW'ₙ − PₖW'ₘ‖₁ ≤ cutNorm(W'ₙ − W'ₘ)` (dyadic-block indicators are cut-norm
test functions), so a diagonal schedule `k(n)→∞` gives an `L¹`-Cauchy `Sₙ`;
`cutDist(W'ₙ, Sₙ) → 0` by Lévy (`MeasureTheory.tendsto_eLpNorm_condExp`) since
`⋃_k 𝒢_k` generates the Borel σ-algebra. **No L¹-trap (key check):** the `L¹`-Cauchy
object is the *block-average* sequence `S`, **not** the reps `W'` — block averages
honestly converge in `L¹` (quasirandom inputs flatten toward the constant ½), so the
quasirandom counterexample to `L¹`-Cauchy *reps* does not apply.

**Conditions / follow-ups:** **dischargeable from Mathlib** (`condExp`,
`tendsto_eLpNorm_condExp`, `Lp` completeness) by building the diagonal martingale
argument — the most tractable of the four. Re-vet if `toLpFun`/`CutNormCauchy`
definitions change.
