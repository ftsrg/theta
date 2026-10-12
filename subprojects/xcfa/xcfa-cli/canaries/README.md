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
full benchmark. The task extracts the sibling `Theta-svcomp.zip` when the directory is missing and
restores the execute bits a zip cannot carry, so it needs nothing but a JVM. Java 21+ must be on
`PATH`.

## Modes

- **parse** (default): frontend-only smoke test (`--backend NONE`) over `canaries.tsv` — 268
  real sv-benchmarks tasks, one PASS per `ParsingResult Success`. The frontend *builds the
  XCFA* under `--backend NONE`, so this catches c2xcfa regressions, not just ANTLR ones.
- **full** (`-Ptheta.canary.mode=full`): real `--portfolio STABLE` run comparing the printed
  verdict against `expected_verdict`. Slow — point `-Ptheta.canary.tsv=<file>` at a small subset
  rather than the whole list.

Both suites are plain JUnit (`CanarySuiteTest`, `FixtureSuiteTest`) sharing `SuiteSupport`, so they
run wherever Gradle does. They invoke the shipped `theta-start.sh` — the entry point SV-COMP itself
uses — and fall back to launching `theta.jar` directly where there is no POSIX shell.

`canaries.tsv` is a broad ~3-per-subfolder sample: good at detecting *general* breakage, but a
given task only *happens* to exercise a feature. That is what the fixtures are for.

## Feature guards — `gradle :theta-xcfa-cli:fixtureTest`

Each file under `fixtures/` is a minimal program that isolates one frontend/grammar modification,
so it builds **iff** that modification is present; reverting the fix flips its outcome and the task
goes red. `fixtures/fixtures.tsv` maps each fixture to its arithmetic, architecture, expected
outcome (`PARSE-OK` / `FRONTEND-FAIL` / `SAFE` / `UNSAFE`, optionally `:property`) and the feature
it guards.

Add a fixture whenever a change adds a frontend/grammar capability: write the smallest program that
needs it, confirm it *fails* before the change and passes after, and add a row. A fixture that does
not discriminate guards nothing.
