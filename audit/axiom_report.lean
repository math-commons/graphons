/-
Kernel axiom report generator (math-commons/formalization-assurance, ADOPTION.md §3).

The reusable assurance workflow runs `lake env lean audit/axiom_report.lean` and diffs
its output against the committed golden `audit/axiom-report.txt` (regenerate + commit
when a flagship's axiom set changes). Unlike `Graphons/Tests/AxiomGuard.lean` (which
*pins* the traces via `#guard_msgs`), this file *emits* them to stdout so they can be
captured as the golden trace.

Covers the headline declarations whose `#print axioms` closures contain all four
project axioms (the `declared-on-closure` set in AXIOM_AUDIT.md): compactness pulls
in `cutNorm_alignment_unit` + `dyadic_l1Cauchy_approx_unit`, the separation iff pulls
in `cutDist_eq_zero_of_homDensity_eq`, and representability pulls in
`lovasz_szegedy_representability`. Names match `Graphons/Tests/AxiomGuard.lean`.
-/
import Graphons.Limits.CompletenessUnit
import Graphons.Characterization.CountingConverse
import Graphons.Characterization.Representability

#print axioms Graphons.instCompactSpaceGraphonSpaceUnit
#print axioms Graphons.cutDist_eq_zero_iff_homDensity_eq
#print axioms Graphons.representability
