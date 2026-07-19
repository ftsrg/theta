#!/usr/bin/env bash
#
# run_canaries.sh — run the canary regression suite against a built
# Theta-svcomp archive.
#
# Usage:
#   ./run_canaries.sh [THETA_DIR] [parse|full] [TSV_FILE]
#
#   THETA_DIR   Path to an *extracted* Theta-svcomp directory (the one
#               containing theta-start.sh). Default:
#               <repo>/subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp
#               If that directory doesn't exist but a sibling
#               Theta-svcomp.zip does, it is auto-extracted there.
#
#   parse|full  Mode (default: parse).
#                 parse — frontend-only smoke test via `--backend NONE`.
#                         Fast (parsing only, no analysis). FAIL = the
#                         output contains "Frontend failed!", the process
#                         times out, or exits nonzero.
#                 full  — full --portfolio STABLE run with a 90s timeout
#                         per task. Compares the printed
#                         "(SafetyResult Safe|Unsafe|Unknown)" verdict
#                         against the task's expected_verdict.
#                         WARNING: do not run this over the whole
#                         canaries.tsv casually — it is the real,
#                         possibly-slow verifier. Use TSV_FILE to point
#                         at a small subset (e.g. output of spot_check.py)
#                         or guard_set.tsv.
#
#   TSV_FILE    A canaries.tsv-shaped TSV (also accepts guard_set.tsv —
#               columns are looked up by name, extra leading columns are
#               ignored). Default: canaries.tsv next to this script.
#
# Environment overrides:
#   SV_BENCHMARKS_ROOT   sv-benchmarks checkout root
#                        (default: <repo>/../sv-benchmarks)
#   PARALLEL_JOBS        parallelism (default: 4)
#   PARSE_TIMEOUT         per-task timeout in parse mode, seconds (default: 60)
#   FULL_TIMEOUT           per-task timeout in full mode, seconds (default: 90)
#
# Exit code: nonzero if any task FAILed (parse mode: "Frontend failed!" /
# crash / timeout; full mode: wrong verdict or crash). TIMEOUT/UNKNOWN in
# full mode do not by themselves cause a nonzero exit.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# ---------------------------------------------------------------------
# Worker mode: invoked recursively (once per task, possibly in parallel
# via xargs) as: run_canaries.sh __worker__ <mode> <theta_dir> <sv_root> <tsv_line>
# ---------------------------------------------------------------------
if [[ "${1:-}" == "__worker__" ]]; then
  mode="$2"
  theta_dir="$3"
  sv_root="$4"
  line="$5"

  IFS=$'\t' read -r task_yml input_relpath property prop_relpath expected data_model cputime subfolder <<<"$line"

  input_abs="$sv_root/$input_relpath"
  prop_abs="$sv_root/$prop_relpath"

  if [[ "$mode" == "parse" ]]; then
    out=$(cd "$theta_dir" && timeout "${PARSE_TIMEOUT:-60}" ./theta-start.sh "$input_abs" \
      --svcomp --backend NONE --loglevel RESULT --property "$prop_abs" \
      --architecture "$data_model" 2>&1)
    rc=$?
    if [[ $rc -eq 124 ]]; then
      status="FAIL"; detail="parse timeout (${PARSE_TIMEOUT:-60}s)"
    elif grep -q "Frontend failed!" <<<"$out"; then
      status="FAIL"; detail="Frontend failed!"
    elif [[ $rc -ne 0 ]]; then
      status="FAIL"; detail="nonzero exit $rc"
    elif grep -q "ParsingResult Success" <<<"$out"; then
      status="PASS"; detail="ok"
    else
      status="FAIL"; detail="no ParsingResult Success in output"
    fi
  else
    out=$(cd "$theta_dir" && timeout "${FULL_TIMEOUT:-90}" ./theta-start.sh "$input_abs" \
      --svcomp --portfolio STABLE --loglevel RESULT --property "$prop_abs" \
      --architecture "$data_model" 2>&1)
    rc=$?
    if [[ $rc -eq 124 ]]; then
      status="TIMEOUT"; detail="full timeout (${FULL_TIMEOUT:-90}s)"
    else
      if grep -q "(SafetyResult Safe)" <<<"$out"; then
        got="true"
      elif grep -q "(SafetyResult Unsafe" <<<"$out"; then
        got="false"
      elif grep -q "(SafetyResult Unknown)" <<<"$out"; then
        got="unknown"
      else
        got="error"
      fi
      if [[ "$got" == "$expected" ]]; then
        status="PASS"; detail="expected=$expected got=$got"
      elif [[ "$got" == "unknown" ]]; then
        status="UNKNOWN"; detail="expected=$expected got=$got"
      elif [[ "$got" == "error" ]]; then
        status="ERROR"; detail="expected=$expected got=$got rc=$rc"
      else
        status="FAIL"; detail="expected=$expected got=$got"
      fi
    fi
  fi

  printf '%s\t%s\t%s\t%s\t%s\n' "$status" "$task_yml" "$property" "$data_model" "$detail"
  exit 0
fi

# ---------------------------------------------------------------------
# Main driver
# ---------------------------------------------------------------------
THETA_DIR="${1:-$REPO_ROOT/subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp}"
MODE="${2:-parse}"
TSV_FILE="${3:-$SCRIPT_DIR/canaries.tsv}"
SV_BENCHMARKS_ROOT="${SV_BENCHMARKS_ROOT:-$(cd "$REPO_ROOT/../sv-benchmarks" 2>/dev/null && pwd)}"
PARALLEL_JOBS="${PARALLEL_JOBS:-4}"

if [[ "$MODE" != "parse" && "$MODE" != "full" ]]; then
  echo "error: mode must be 'parse' or 'full', got: $MODE" >&2
  exit 2
fi

if [[ ! -x "$THETA_DIR/theta-start.sh" ]]; then
  zip_candidate="$(dirname "$THETA_DIR")/Theta-svcomp.zip"
  if [[ -f "$zip_candidate" ]]; then
    echo "note: $THETA_DIR not found; auto-extracting $zip_candidate ..." >&2
    unzip -q -o "$zip_candidate" -d "$(dirname "$THETA_DIR")"
  fi
fi

if [[ ! -x "$THETA_DIR/theta-start.sh" ]]; then
  echo "error: no theta-start.sh at $THETA_DIR" >&2
  echo "       build it with: (cd '$REPO_ROOT' && ./gradlew buildArchiveTheta-svcomp)" >&2
  echo "       then extract subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp.zip" >&2
  exit 2
fi

if [[ -z "$SV_BENCHMARKS_ROOT" || ! -d "$SV_BENCHMARKS_ROOT" ]]; then
  echo "error: sv-benchmarks root not found (tried: ${SV_BENCHMARKS_ROOT:-<unset>})" >&2
  echo "       set SV_BENCHMARKS_ROOT explicitly" >&2
  exit 2
fi

if [[ ! -f "$TSV_FILE" ]]; then
  echo "error: TSV file not found: $TSV_FILE" >&2
  exit 2
fi

if [[ "$MODE" == "full" ]]; then
  n_tasks=$(($(wc -l <"$TSV_FILE") - 1))
  echo "note: full mode runs the REAL verifier (90s timeout/task, $PARALLEL_JOBS parallel)." >&2
  echo "      about to run $n_tasks task(s) from $TSV_FILE." >&2
fi

export PARSE_TIMEOUT="${PARSE_TIMEOUT:-60}"
export FULL_TIMEOUT="${FULL_TIMEOUT:-90}"

# Normalize input: extract the 8 canaries columns by name so this also
# works unmodified against guard_set.tsv (which has 2 extra leading
# columns) or any TSV superset of the canaries.tsv schema.
normalized_lines=$(awk -F'\t' '
  NR==1 {
    for (i = 1; i <= NF; i++) col[$i] = i
    next
  }
  {
    print $col["task_yml_relpath"] "\t" $col["input_file_relpath"] "\t" \
          $col["property"] "\t" $col["property_file_relpath"] "\t" \
          $col["expected_verdict"] "\t" $col["data_model"] "\t" \
          $col["cputime"] "\t" $col["subfolder"]
  }
' "$TSV_FILE")

if [[ -z "$normalized_lines" ]]; then
  echo "error: no data rows found in $TSV_FILE" >&2
  exit 2
fi

results=$(printf '%s\n' "$normalized_lines" | xargs -d '\n' -P "$PARALLEL_JOBS" -I{} \
  bash "$SCRIPT_DIR/run_canaries.sh" __worker__ "$MODE" "$THETA_DIR" "$SV_BENCHMARKS_ROOT" {})

echo "$results" | sort -k2,2 | awk -F'\t' 'BEGIN{OFS="\t"} {printf "%-8s %-70s %-14s %-6s %s\n", $1, $2, $3, $4, $5}'

echo
echo "Summary:"
echo "$results" | cut -f1 | sort | uniq -c | sort -rn

n_fail=$(echo "$results" | cut -f1 | grep -c '^FAIL$')
n_error=$(echo "$results" | cut -f1 | grep -c '^ERROR$')

# In parse mode, also run the feature-guard fixtures (each isolates one frontend/grammar
# modification, so a reverted fix turns them red). Only when the default TSV is used, so a
# targeted `run_canaries.sh <dir> parse subset.tsv` stays focused.
fixtures_failed=0
if [[ "$MODE" == "parse" && "$TSV_FILE" == "$SCRIPT_DIR/canaries.tsv"
      && -x "$SCRIPT_DIR/run_fixtures.sh" ]]; then
  echo
  echo "=== feature-guard fixtures ==="
  if ! THETA_DIR="$THETA_DIR" "$SCRIPT_DIR/run_fixtures.sh" "$THETA_DIR"; then
    fixtures_failed=1
  fi
fi

if [[ "$n_fail" -gt 0 || "$n_error" -gt 0 || "$fixtures_failed" -ne 0 ]]; then
  echo
  msg="RESULT: $((n_fail + n_error)) task(s) FAILed/ERRORed"
  [[ "$fixtures_failed" -ne 0 ]] && msg="$msg; feature-guard fixtures diverged"
  echo "$msg." >&2
  exit 1
fi

echo
echo "RESULT: all tasks passed."
exit 0
