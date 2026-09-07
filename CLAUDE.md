# Theta — working notes for Claude

## Writing code here

- **Keep comments short.** A comment states what is not obvious from the code; it is not a place for
  the history of a bug, a measurement, or a rationale essay. One or two lines is the norm, and a
  KDoc/Javadoc block on a class or a pass should fit in a short paragraph. Never reference benchmark
  runs, batches or dates.
- Never run `spotlessApply` on the whole repo; it is configured `ratchetFrom("origin/master")`, so
  run `spotlessCheck` and fix what it reports.
- `checkCopyright` derives the expected year from a file's last commit date, so run `applyCopyright`
  *after* committing, never before.

## Local verification loop

⚠️ **`timeout N ./theta-start.sh …` does NOT kill the verifier.** The script `exec`s nothing — it
launches a child JVM — so the timeout kills the *script* and leaves the JVM orphaned, still holding
the pipe. Any caller reading that pipe (a `$(...)` capture, a `while read` loop) then hangs
**forever**, long after the timeout should have fired, and the run looks stuck rather than timed out.
Kill the JVM itself (`pkill -f 'theta.jar.*<input path>'`) to release it. This is why batched local
suites appear to wedge on one task; it is not the task being slow.

- Fat jar for fast iteration: `./gradlew :theta-xcfa-cli:shadowJar`
  → `subprojects/xcfa/xcfa-cli/build/libs/theta-xcfa-cli-<version>-all.jar`.
- Running the jar directly needs `LD_LIBRARY_PATH=<dist>/lib` (legacy Z3) and
  `--smt-home <dist>/solvers`; `theta-start.sh` sets these but hardcodes `-Xmx14210m`.
- Full distribution: `./gradlew buildArchiveTheta-svcomp -x test`
  → `subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp.zip`. After any rebuild also
  `rm -rf subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp` — a stale extracted directory
  is silently reused.
- Parse-only smoke test: `--svcomp --backend NONE --loglevel RESULT --property <prp> --architecture ILP32|LP64`
  (success marker: `ParsingResult Success`).
- Canary suite: `subprojects/xcfa/xcfa-cli/canaries/` (README + `run_canaries.sh` header
  comment for the traps). Run it as `./gradlew :theta-xcfa-cli:canaryTest`.
