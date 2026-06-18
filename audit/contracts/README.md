# Object contracts

One card per **constructed object** (not per theorem). A contract lets a reviewer judge
whether the object is the right one — and where it is *proven* vs *asserted* — **without
reading any Lean proof**. Format + rationale:
[`math-commons/formalization-assurance`](https://github.com/math-commons/formalization-assurance).

Each card carries the informal description + source, the Lean *signature only*, a
`characterization` (id'd claims including ≥1 **anti-degeneracy** clause), and a
`known_values` **test matrix** (`instance → expected → theorem → status`) whose status is
read from `#print axioms` (so it can't be fudged).

## Cards

- [`homDensity.md`](homDensity.md) — the homomorphism density `t(F, W)`. Seven kernel-checked
  `known_values` rows (Erdős–Rényi `p^{e(F)}`, edge/triangle integrals, multiplicativity,
  step-graphon agreement, the `[0,1]` range); anti-degeneracy clause = agreement with the
  finite homomorphism density on step graphons.

## Backlog (objects still worth a card)

`Graphon` / `SymmKernel`, `cutNorm`, `cutDist`, `GraphonSpace`.
