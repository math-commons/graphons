/-
Copyright (c) 2026 The graphons contributors. Released under Apache 2.0.

EXTENDED_VALIDATION_PLAN.md M3 — **axiom guard**.

Pins the EXACT axiom dependencies of the flagship theorems using `#guard_msgs in #print axioms`.
If any change lands that silently grows a theorem's axiom set (a new `sorry`-replacing axiom, an
accidental dependency on one of the ledger axioms, or a new custom axiom anywhere upstream), the
expected message no longer matches and `lake build` FAILS on this file.

Contract (see HISTORY.md "Axiom Ledger"):
  * Tier A/B flagships depend on the standard three axioms ONLY
    (`propext`, `Classical.choice`, `Quot.sound`).
  * The Tier-C theorems additionally cite EXACTLY their documented ledger axioms:
      - compactness/completeness: `cutNorm_alignment_unit`, `dyadic_l1Cauchy_approx_unit`
      - counting converse:        `cutDist_eq_zero_of_homDensity_eq`
      - representability:         `lovasz_szegedy_representability`

When a ledger axiom is legitimately discharged, update the corresponding expected block here
(shrinking it) in the same commit — the guard then enforces the new, smaller ledger.
-/
import Graphons.Core.Examples
import Graphons.Core.Multiplicativity
import Graphons.Core.StepDensity
import Graphons.Core.Density
import Graphons.AnchorChecks
import Graphons.CutMetric.CutNormSet
import Graphons.CutMetric.Gluing
import Graphons.Counting.CountingLemma
import Graphons.Limits.WeakRegularity
import Graphons.Limits.CompletenessUnit
import Graphons.Characterization.CountingConverse
import Graphons.Characterization.Representability
import Graphons.Extremal.Goodman
import Graphons.Extremal.Sidorenko
import Graphons.Extremal.Mantel
import Graphons.Characterization.LimitSpecModel
import Graphons.Characterization.LimitSpecUnique
import Graphons.Sampling.SamplingLemma
import Graphons.CutMetric.Robustness

/-! ### Tier A — encoding flagships (standard axioms only) -/

/-- info: 'Graphons.homDensity_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.homDensity_const

/-- info: 'Graphons.homDensity_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.homDensity_edge

/--
info: 'Graphons.homDensity_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.homDensity_triangle

/-- info: 'Graphons.homDensity_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.homDensity_sum

/-- info: 'Graphons.homDensity_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.homDensity_step

/-! ### Tier B — interaction flagships (standard axioms only) -/

/--
info: 'Graphons.cutNorm_eq_cutNormSet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.cutNorm_eq_cutNormSet

/--
info: 'Graphons.abs_homDensity_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.abs_homDensity_sub_le

/-- info: 'Graphons.cutDist_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.cutDist_triangle

/-- info: 'Graphons.weak_regularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.weak_regularity

/--
info: 'Graphons.exists_stepGraphon_cutDist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.exists_stepGraphon_cutDist_le

/-! ### Tier D — extremal applications (standard axioms only) -/

/-- info: 'Graphons.integral_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.integral_deg

/-- info: 'Graphons.homDensity_cherry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.homDensity_cherry

/--
info: 'Graphons.homDensity_cherry_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.homDensity_cherry_ge

/-- info: 'Graphons.goodman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.goodman

/-- info: 'Graphons.integral_coDeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.integral_coDeg

/-- info: 'Graphons.homDensity_C4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.homDensity_C4

/-- info: 'Graphons.sidorenko_C4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.sidorenko_C4

/-- info: 'Graphons.integral_triangle_coDeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.integral_triangle_coDeg

/-- info: 'Graphons.mantel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.mantel

/-! ### Tier E — axiomatic-spec model (E2): ingredients axiom-free, model cites EXACTLY #1–2 -/

/-- info: 'Graphons.cutDist_toUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.cutDist_toUnit

/-- info: 'Graphons.homDensity_toUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.homDensity_toUnit

/--
info: 'Graphons.exists_finWeighted_cutDist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.exists_finWeighted_cutDist_le

/--
info: 'Graphons.FinWeighted.dist_toSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.FinWeighted.dist_toSpace

/--
info: 'Graphons.isDenseGraphLimitTheory_graphonSpace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Graphons.CompletenessUnit.cutNorm_alignment_unit,
 Graphons.CompletenessUnit.dyadic_l1Cauchy_approx_unit]
-/
#guard_msgs in
#print axioms Graphons.isDenseGraphLimitTheory_graphonSpace

/--
info: 'Graphons.isDenseGraphLimitTheory_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.isDenseGraphLimitTheory_unique

/--
info: 'Graphons.isDenseGraphLimitTheory_unique_graphonSpace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Graphons.CompletenessUnit.cutNorm_alignment_unit,
 Graphons.CompletenessUnit.dyadic_l1Cauchy_approx_unit]
-/
#guard_msgs in
#print axioms Graphons.isDenseGraphLimitTheory_unique_graphonSpace

/-! ### Tier B extension — robustness equivalences (WS4): all standard-axioms-only -/

/-- info: 'Graphons.cutDist_pullback_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.cutDist_pullback_self

/--
info: 'Graphons.cutDist_le_cutNorm_pullback_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.cutDist_le_cutNorm_pullback_sub

/--
info: 'Graphons.cutDist_pullback_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.cutDist_pullback_pullback

/--
info: 'Graphons.cutNorm_le_cutNormSigned' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.cutNorm_le_cutNormSigned

/--
info: 'Graphons.cutNormSigned_le_four_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.cutNormSigned_le_four_mul

/-! ### Tier F — sampling (W-random graphs): all standard-axioms-only -/

/-- info: 'Graphons.integral_coin_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graphons.integral_coin_prod

/--
info: 'Graphons.integral_coin_homDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.integral_coin_homDensity

/--
info: 'Graphons.integral_edgeProb_image_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.integral_edgeProb_image_of_injective

/--
info: 'Graphons.abs_expectedHomDensity_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.abs_expectedHomDensity_sub_le

/--
info: 'Graphons.tendsto_expectedHomDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.tendsto_expectedHomDensity

/-! ### Tier C — flagships citing EXACTLY their ledger axioms -/

/--
info: 'Graphons.instCompactSpaceGraphonSpaceUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Graphons.CompletenessUnit.cutNorm_alignment_unit,
 Graphons.CompletenessUnit.dyadic_l1Cauchy_approx_unit]
-/
#guard_msgs in
#print axioms Graphons.instCompactSpaceGraphonSpaceUnit

/--
info: 'Graphons.instCompleteSpaceGraphonSpaceUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Graphons.CompletenessUnit.cutNorm_alignment_unit,
 Graphons.CompletenessUnit.dyadic_l1Cauchy_approx_unit]
-/
#guard_msgs in
#print axioms Graphons.instCompleteSpaceGraphonSpaceUnit

/--
info: 'Graphons.cutDist_eq_zero_iff_homDensity_eq' depends on axioms: [propext,
 Classical.choice,
 Graphons.cutDist_eq_zero_of_homDensity_eq,
 Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.cutDist_eq_zero_iff_homDensity_eq

/--
info: 'Graphons.representability' depends on axioms: [propext,
 Classical.choice,
 Graphons.lovasz_szegedy_representability,
 Quot.sound]
-/
#guard_msgs in
#print axioms Graphons.representability
