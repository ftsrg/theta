# Canary regression suite

Run it from Gradle as `./gradlew :theta-xcfa-cli:canaryTest`, which builds the distribution first and
reports one JUnit result per canary. `-Ptheta.canary.mode=full` checks verdicts instead of only that
the frontend builds each task; `-Ptheta.canary.jobs=N` lowers the parallelism on a machine short of
memory (the largest canaries need several GB each, and one that is OOM-killed is reported as
`nonzero exit 137`).

**This suite is the gate.** Frontend and pass changes are expected to be run against it before they
land, together with the affected module's unit tests. A fix whose effect a fixture cannot show is a
fix nothing will protect: when you add one, check that it *fails* before your change and passes
after, or it guards nothing.

Fast checks run after a Theta-svcomp build to catch frontend/analysis regressions before a
full benchmark. Point them at an extracted `Theta-svcomp` dir (or let them auto-extract the
sibling `Theta-svcomp.zip`). Java 21+ must be on `PATH` (the launcher uses `theta-start.sh`).

## `run_canaries.sh [THETA_DIR] [parse|full] [TSV]`

- **parse** (default): frontend-only smoke test (`--backend NONE`) over `canaries.tsv` — 268
  real sv-benchmarks tasks, one PASS per `ParsingResult Success`. The frontend *builds the
  XCFA* under `--backend NONE`, so this catches c2xcfa regressions, not just ANTLR ones. In
  this mode it also runs the feature-guard fixtures (below) and folds their result into the
  exit status.
- **full**: real `--portfolio STABLE` run comparing the printed verdict against
  `expected_verdict`. Slow — pass a small `TSV` subset rather than the whole list.

`canaries.tsv` is a broad ~3-per-subfolder sample: good at detecting *general* breakage, but a
given task only *happens* to exercise a feature. That is what the fixtures are for.

## `run_fixtures.sh [THETA_DIR]` — feature guards

Each file under `fixtures/` is a minimal program that isolates one frontend/grammar
modification, so it builds **iff** that modification is present; reverting the fix flips its
outcome and the suite goes red. `fixtures/fixtures.tsv` maps each fixture to its arithmetic,
architecture, expected outcome (`PARSE-OK` / `FRONTEND-FAIL`), and the feature it guards. Run
directly, or automatically as part of `run_canaries.sh ... parse`.

Add a fixture whenever a change adds a frontend/grammar capability: write the smallest program that
needs it, confirm it *fails* before the change and passes after, and add a row. A fixture that does
not discriminate guards nothing.

For a verdict-level bug — where a fix changes the *answer* rather than whether the program builds —
a fixture with a `SAFE`/`UNSAFE` expectation is the right home; it runs in full mode.
