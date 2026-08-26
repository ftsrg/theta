#!/usr/bin/env bash
#
# run_fixtures.sh — feature-guard canaries.
#
# Each fixture under fixtures/ is a minimal program that isolates one frontend/grammar
# modification (see fixtures/fixtures.tsv). Unlike the sampled canaries.tsv
# tasks (which only *happen* to exercise a feature), a fixture builds iff its modification is
# present, so reverting the fix flips its outcome and this suite goes red.
#
# Runs the frontend only (`--backend NONE`) with each fixture's arithmetic/architecture and
# checks the actual outcome against the expected one:
#   PARSE-OK       the frontend built the XCFA ("ParsingResult Success")
#   FRONTEND-FAIL  the frontend rejected it (a documented, not-yet-supported feature)
#
# A fixture may instead expect a *verdict*, which runs the real verifier
# (`--portfolio STABLE`) rather than the frontend:
#   SAFE           the program is correct and must verify as such
#   UNSAFE         the program has the bug it names and must be caught
# Either may name the property to check after a colon (`UNSAFE:no-overflow`); the
# default is unreach-call. Instrumentation-shaped fixes need this -- overflow checks
# are only emitted at all when no-overflow is the property being verified.
# Use these for fixes that change values rather than what parses -- a miswritten
# memory cell parses perfectly and only shows up as a wrong verdict. Keep such a
# fixture small enough to verify in a few seconds; this suite runs on every gate.
#
# Usage: ./run_fixtures.sh [THETA_DIR]
# Exit nonzero if any fixture's outcome differs from its expectation.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
THETA_DIR="${1:-$REPO_ROOT/subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp}"
TSV="$SCRIPT_DIR/fixtures/fixtures.tsv"
PROP="${PROP:-$(cd "$REPO_ROOT/../sv-benchmarks" 2>/dev/null && pwd)/c/properties/unreach-call.prp}"
TIMEOUT="${FIXTURE_TIMEOUT:-90}"
VERDICT_TIMEOUT="${FIXTURE_VERDICT_TIMEOUT:-180}"

if [[ ! -x "$THETA_DIR/theta-start.sh" ]]; then
  zip="$(dirname "$THETA_DIR")/Theta-svcomp.zip"
  [[ -f "$zip" ]] && { echo "note: extracting $zip" >&2; unzip -q -o "$zip" -d "$(dirname "$THETA_DIR")"; }
fi
[[ -x "$THETA_DIR/theta-start.sh" ]] || { echo "error: no theta-start.sh at $THETA_DIR" >&2; exit 2; }
[[ -f "$PROP" ]] || { echo "error: property file not found: $PROP" >&2; exit 2; }

pass=0 fail=0
while IFS=$'\t' read -r fixture arithmetic architecture expect feature; do
  [[ "$fixture" == "fixture" || -z "$fixture" ]] && continue
  input="$SCRIPT_DIR/fixtures/$fixture"
  verdict="${expect%%:*}"
  if [[ "$verdict" == "SAFE" || "$verdict" == "UNSAFE" ]]; then
    prop="$PROP"
    [[ "$expect" == *:* ]] && prop="$(dirname "$PROP")/${expect#*:}.prp"
    # A verdict fixture: run the real verifier. `timeout` kills theta-start.sh but not
    # the JVM it launched, which would keep the pipe open forever, so reap it by hand.
    out=$(cd "$THETA_DIR" && timeout -k 5 "$VERDICT_TIMEOUT" ./theta-start.sh "$input" \
      --svcomp --portfolio STABLE --loglevel RESULT --property "$prop" \
      --architecture "$architecture" --arithmetic "$arithmetic" 2>&1)
    pkill -f "theta.jar.*$fixture" 2>/dev/null
    if grep -q "(SafetyResult Safe)" <<<"$out"; then actual="SAFE"
    elif grep -q "(SafetyResult Unsafe" <<<"$out"; then actual="UNSAFE"
    else actual="OTHER"; fi
    [[ "$actual" == "$verdict" ]] && actual="$expect"
  else
    out=$(cd "$THETA_DIR" && timeout "$TIMEOUT" ./theta-start.sh "$input" \
      --svcomp --backend NONE --loglevel RESULT --property "$PROP" \
      --architecture "$architecture" --arithmetic "$arithmetic" 2>&1)
    if grep -q "ParsingResult Success" <<<"$out"; then actual="PARSE-OK"
    elif grep -q "Frontend failed!" <<<"$out"; then actual="FRONTEND-FAIL"
    else actual="OTHER"; fi
  fi

  if [[ "$actual" == "$expect" ]]; then
    printf 'PASS  %-34s %s\n' "$fixture" "$feature"; ((pass++))
  else
    printf 'FAIL  %-26s expected=%s actual=%s -- %s\n' "$fixture" "$expect" "$actual" "$feature"; ((fail++))
  fi
done < "$TSV"

echo
echo "Fixtures: $pass PASS, $fail FAIL"
[[ $fail -eq 0 ]] && { echo "RESULT: all fixtures matched expectations."; exit 0; }
echo "RESULT: $fail fixture(s) diverged."; exit 1
