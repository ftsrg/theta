# xcfa/xcfa-cli — notes for editing this module

Gradle module: `:theta-xcfa-cli`, main class `hu.bme.mit.theta.xcfa.cli.XcfaCli`. This is the user-facing verifier: option parsing, the frontend and its fallbacks, checker construction, portfolios, witnesses, and the SV-COMP and CHC-COMP distributions (the `archivePackaging` variants in [build.gradle.kts](build.gradle.kts)). Usage and the config object model: [README.md](README.md).

## Build and test

- `./gradlew :theta-xcfa-cli:test` runs the unit and end-to-end tests. A test that needs an SMT-LIB solver skips itself when the solver cannot be installed, and the root `verifySolverInstallations` task then fails the build.
- The canary gate is kept out of `test`. `:theta-xcfa-cli:fixtureTest` runs the feature-guard fixtures, `-Ptheta.fixture.jobs` at once (default 4), in about ten minutes. `:theta-xcfa-cli:canaryTest` runs the sv-benchmarks sample in `canaries.tsv` and depends on `fixtureTest`. Both build `buildArchiveTheta-svcomp` first and need an sv-benchmarks checkout: `../sv-benchmarks` beside the repository, or `-Ptheta.canary.svBenchmarks=<dir>`. Modes, and how to add a fixture: [canaries/README.md](canaries/README.md).
- **One fixture per issue.** A potential bug is guarded once: by one program that must hold (`SAFE`/`PARSE-OK`) and at most one that must fail (`UNSAFE`/`FRONTEND-FAIL`). Before adding a fixture, search `fixtures.tsv` for the mechanism. If one exists, extend it or leave it, rather than adding another syntax for the same thing (`p++`/`++p`/`p += 1`, `break`/`continue`/`goto`, `malloc` through a wrapper or directly). Only a different memory model (`multi`, `flat`, `bytes`) is a different issue. A row with no `--memory-model` repeats the `multi` row unless the program falls back.
- Each fixture finishes within 60 s (the suite's timeout). A program that needs longer is too large to be a fixture; shrink it or drop it.
- The suites re-extract `build/distributions/Theta-svcomp.zip` into `Theta-svcomp/` when that directory is missing or older than the zip.

## Layout

Paths are relative to [src/main/java/hu/bme/mit/theta/xcfa/cli/](src/main/java/hu/bme/mit/theta/xcfa/cli/).

- `XcfaCli.kt` calls `runConfig` in `ExecuteConfig.kt`, which validates the input, runs `frontend` and `backend`, maps the result and writes the witness.
- `params/`: `XcfaConfig.kt` (the config tree, with one `SpecBackendConfig` per backend), `ParamValues.kt` (the `Backend`, `Domain`, `Refinement`, `POR`, ... enums, which carry their factories), `ExitCodes.kt`.
- `checkers/`: `ConfigToChecker.kt` dispatches on `Backend` to a `ConfigTo<X>Checker.kt`. `ConfigToPortfolio.kt` maps `--portfolio` names to `portfolio/` (`STABLE` is `complex27`).
- `utils/XcfaParser.kt` (one parser per input type), `witnesstransformation/` (trace concretization, witness application), `utils/*WitnessWriter.kt`.

## Invariants / gotchas

1. **The frontend fallbacks rebuild in-process.** They apply only when no `--memory-model` was given. `UnsupportedPointerSplitException` rebuilds under `flat` and `RequiresByteAddressedMemoryException` under `bytes`. An arithmetic the frontend chose itself is retried as bitvector. A fallback pins its model in the config, because the portfolio re-runs the frontend from that config. The `bytes` model requires bitvector arithmetic; if it cannot represent the input, restore the requested arithmetic before falling back to `flat`.
2. **New backend:** add it to `Backend`. The exhaustive `when`s in `BackendConfig.createSpecConfig` and `getSafetyChecker` then need a spec config and a `ConfigTo<X>Checker` for it.
3. Invalid domain/refinement combinations are rejected while the checker is built: `UNSAT_CORE` needs a `Domain` with a `varsPrecRefiner` (currently only EXPL).
4. `ConfigToAsgCegarChecker` passes `traceEnricher = ::threadWriteTriples` so that lassos see pointer writes. Any new consumer of paths needs the same enrichment ([xcfa-analysis AGENTS.md](../xcfa-analysis/AGENTS.md)).
5. Frontend failures normally log and exit. Re-throw only the specific typed limitations that the caller can recover from; do not turn unrelated frontend failures into fallback attempts.
6. **An Unsafe result that depends on an over-approximated value becomes Unknown** (`utils/OverApproximationGuard.kt`, called in the result mapping of `ExecuteConfig.kt`). The check slices the counterexample backward from its assumptions over `XCFA.overApproximatedVars`; a data race also from the guards and addresses of the edges enabled in its last state. The trace names per-process instances of the variables, so it maps them through the states' `varLookup` and compares names, with an OC trace's per-thread copy `T<pid>::_::x` standing for `x`. It runs only where the real checker ran (not for `PORTFOLIO` or an in-process parent), because the parent sees only the child's printed result. Without an XCFA trace, any recorded havoc left in the model counts. In a portfolio step it exits with `UNRELIABLE_UNSAFE` instead, so that the portfolio tries its next config; `ConfigToPortfolio` reports Unknown if none gives a reliable verdict.
7. `utils/CInvariantExport.kt` exports loop invariants only over names declared once at file scope and in the function (`FunctionVisitor.variablesInScope`). This is a workaround, not a C rule: Goblint binds a re-declared name to another declaration, so it confirms false invariants and refutes true ones ([goblint#747](https://github.com/goblint/analyzer/issues/747)). The cost is that validators which resolve these names correctly get no invariant for those loops. Remove the restriction when Goblint resolves such names correctly.
