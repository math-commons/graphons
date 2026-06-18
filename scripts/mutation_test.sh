#!/usr/bin/env bash
# =============================================================================
# mutation_test.sh — M2 mutation testing of the graphons validation suite
# (EXTENDED_VALIDATION_PLAN.md WS5)
#
# For each catalogued mutation: apply a single exactly-once literal text edit
# to ONE definition, build only the designated catcher modules, record
# KILLED/SURVIVED + the first error line, restore the file via
# `git checkout --`, and verify the tree is clean before the next mutant.
#
# A mutant is KILLED if the catcher build fails (anywhere in the transitive
# rebuild — the first failing module is recorded). If the primary catchers
# pass, an optional escalation target (full suite) is built; only if that
# also passes is the mutant recorded as SURVIVED.
#
# Exit status: 0 iff every mutant was killed AND the final clean-tree build
# is green. Safe to interrupt: a trap restores any in-flight mutation.
#
# Usage:  bash scripts/mutation_test.sh [MUTATION_NAME ...]
#         (no args = run the whole catalog)
# =============================================================================
set -u
cd "$(dirname "$0")/.." || exit 1

LOGDIR="$(mktemp -d /tmp/mutation_test.XXXXXX)"
RESULTS="$LOGDIR/results.tsv"
: > "$RESULTS"

# ---------------------------------------------------------------------------
# Safety: restore the currently mutated file on any exit/interrupt.
# ---------------------------------------------------------------------------
MUTATED_FILE=""
restore_current() {
  if [[ -n "$MUTATED_FILE" ]]; then
    git checkout -- "$MUTATED_FILE"
    echo "[trap] restored $MUTATED_FILE"
    MUTATED_FILE=""
  fi
}
trap restore_current EXIT INT TERM

# ---------------------------------------------------------------------------
# Mutation catalog (parallel arrays). To add a mutation, append one entry to
# each array. OLD must occur EXACTLY ONCE in FILE (checked before applying;
# multi-line literals are allowed). ESCALATE may be empty.
# ---------------------------------------------------------------------------
NAMES=();  FILES=();  OLDS=();  NEWS=();  CATCHERS=();  ESCALATE=()

NAMES+=("M-PROD")
FILES+=("Graphons/Core/Basic.lean")
OLDS+=('∏ e ∈ F.edgeFinset, edgeVal W x e')
NEWS+=('∑ e ∈ F.edgeFinset, edgeVal W x e')
CATCHERS+=("Graphons.Tests.Concrete Graphons.AnchorChecks")
ESCALATE+=("")

NAMES+=("M-STEP")
FILES+=("Graphons/Core/Step.lean")
OLDS+=('if G.Adj a b then (1 : ℝ) else 0)')
NEWS+=('if G.Adj a b then (0 : ℝ) else 1)')
CATCHERS+=("Graphons.Tests.Concrete")
ESCALATE+=("")

NAMES+=("M-ABS")
FILES+=("Graphons/CutMetric/CutNorm.lean")
OLDS+=('noncomputable def cutNorm (W : SymmKernel Ω μ) : ℝ :=
  ⨆ (u : Ω → ℝ) (v : Ω → ℝ) (_ : IsTestFun u) (_ : IsTestFun v),
    |∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ)|')
NEWS+=('noncomputable def cutNorm (W : SymmKernel Ω μ) : ℝ :=
  ⨆ (u : Ω → ℝ) (v : Ω → ℝ) (_ : IsTestFun u) (_ : IsTestFun v),
    (∫ p, W.toFun p.1 p.2 * u p.1 * v p.2 ∂(μ.prod μ))')
CATCHERS+=("Graphons.CutMetric.CutNorm")
ESCALATE+=("")

NAMES+=("M-CONST")
FILES+=("Graphons/Core/Examples.lean")
OLDS+=('Graphon.mk'"'"' (μ := μ) (fun _ _ => p)')
NEWS+=('Graphon.mk'"'"' (μ := μ) (fun _ _ => 1 - p)')
CATCHERS+=("Graphons.Tests.Concrete")
ESCALATE+=("")

NAMES+=("M-SUB")
FILES+=("Graphons/Core/Basic.lean")
OLDS+=('toFun := fun x y => U x y - W x y')
NEWS+=('toFun := fun x y => U x y + W x y')
CATCHERS+=("Graphons.Counting.CountingLemma Graphons.Tests.Concrete")
ESCALATE+=("Graphons.Tests.AxiomGuard")

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# apply_edit FILE OLD NEW : literal exactly-once replacement (multi-line ok)
apply_edit() {
  OLD="$2" NEW="$3" python3 - "$1" <<'PY'
import os, sys
path = sys.argv[1]
old, new = os.environ["OLD"], os.environ["NEW"]
src = open(path, encoding="utf-8").read()
n = src.count(old)
if n != 1:
    sys.exit(f"pattern occurs {n} times (expected 1) in {path}")
open(path, "w", encoding="utf-8").write(src.replace(old, new))
PY
}

# build_catchers LOGFILE MODULES... : returns lake's exit status
build_catchers() {
  local log="$1"; shift
  lake build "$@" >"$log" 2>&1
}

first_error() {
  grep -m1 -E "error" "$1" | sed 's/^[[:space:]]*//' | cut -c1-160
}

verify_clean() {
  if [[ -n "$(git diff --stat)" ]]; then
    echo "FATAL: working tree dirty after restore:" >&2
    git diff --stat >&2
    exit 2
  fi
}

# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------
ONLY=("$@")
ANY_SURVIVED=0
verify_clean

for i in "${!NAMES[@]}"; do
  name="${NAMES[$i]}"
  if [[ ${#ONLY[@]} -gt 0 ]]; then
    keep=0
    for o in "${ONLY[@]}"; do [[ "$o" == "$name" ]] && keep=1; done
    [[ $keep -eq 1 ]] || continue
  fi
  file="${FILES[$i]}"
  log="$LOGDIR/$name.log"

  echo "=============================================================="
  echo "[$name] mutating $file"

  MUTATED_FILE="$file"
  if ! apply_edit "$file" "${OLDS[$i]}" "${NEWS[$i]}"; then
    echo "[$name] PATTERN-ERROR: could not apply mutation (see message above)"
    printf '%s\t%s\t%s\t%s\n' "$name" "$file" "PATTERN-ERROR" "-" >> "$RESULTS"
    git checkout -- "$file"; MUTATED_FILE=""; verify_clean
    ANY_SURVIVED=1
    continue
  fi

  # shellcheck disable=SC2086
  echo "[$name] building catchers: ${CATCHERS[$i]}"
  if build_catchers "$log" ${CATCHERS[$i]}; then
    status="SURVIVED-PRIMARY"
    if [[ -n "${ESCALATE[$i]}" ]]; then
      echo "[$name] primary catchers PASSED — escalating to: ${ESCALATE[$i]}"
      # shellcheck disable=SC2086
      if build_catchers "$LOGDIR/$name.escalate.log" ${ESCALATE[$i]}; then
        status="SURVIVED"
      else
        status="KILLED-ESCALATED"
        log="$LOGDIR/$name.escalate.log"
      fi
    else
      status="SURVIVED"
    fi
  else
    status="KILLED"
  fi

  err="-"
  if [[ "$status" == KILLED* ]]; then
    err="$(first_error "$log")"
    echo "[$name] KILLED — first error: $err"
  else
    echo "[$name] *** SURVIVED *** (no catcher failed)"
    ANY_SURVIVED=1
  fi
  printf '%s\t%s\t%s\t%s\n' "$name" "$file" "$status" "$err" >> "$RESULTS"

  git checkout -- "$file"
  MUTATED_FILE=""
  verify_clean
  echo "[$name] restored; tree clean."
done

# ---------------------------------------------------------------------------
# Final clean-tree sanity build
# ---------------------------------------------------------------------------
echo "=============================================================="
echo "[final] rebuilding acceptance suite on the clean tree ..."
FINAL_OK=1
if ! lake build Graphons.Tests.AxiomGuard Graphons.Tests.Concrete Graphons.AnchorChecks \
     >"$LOGDIR/final.log" 2>&1; then
  FINAL_OK=0
  echo "[final] FAILED — clean tree does not build! See $LOGDIR/final.log"
  tail -30 "$LOGDIR/final.log"
else
  echo "[final] clean tree builds green."
fi

echo "=============================================================="
echo "Kill matrix (TSV: name / file / status / first error):"
column -t -s $'\t' "$RESULTS" 2>/dev/null || cat "$RESULTS"
echo "Logs in: $LOGDIR"

if [[ $ANY_SURVIVED -ne 0 || $FINAL_OK -ne 1 ]]; then
  exit 1
fi
exit 0
