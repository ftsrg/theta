# xcfa/xcfa-cli — notes for editing this module

Gradle module: `:theta-xcfa-cli`, main class `hu.bme.mit.theta.xcfa.cli.XcfaCli`. This is the user-facing verifier: option parsing, the frontend and its fallbacks, checker construction, portfolios, witnesses, and the SV-COMP and CHC-COMP distributions (the `archivePackaging` variants in [build.gradle.kts](build.gradle.kts)). Usage and the config object model: [README.md](README.md).

## Build and test

- `./gradlew :theta-xcfa-cli:test` runs the unit and end-to-end tests. A test that needs an SMT-LIB solver skips itself when the solver cannot be installed, and the root `verifySolverInstallations` task then fails the build.
- The canary gate is kept out of `test`. `:theta-xcfa-cli:fixtureTest` runs the feature-guard fixtures and takes a few minutes. `:theta-xcfa-cli:canaryTest` runs the sv-benchmarks sample in `canaries.tsv` and depends on `fixtureTest`. Both build `buildArchiveTheta-svcomp` first and need an sv-benchmarks checkout: `../sv-benchmarks` beside the repository, or `-Ptheta.canary.svBenchmarks=<dir>`. Modes, and how to add a fixture: [canaries/README.md](canaries/README.md).
- The suites unpack `build/distributions/Theta-svcomp.zip` only when `Theta-svcomp/theta-start.sh` is missing, so delete that directory after a rebuild.

## Layout

Paths are relative to [src/main/java/hu/bme/mit/theta/xcfa/cli/](src/main/java/hu/bme/mit/theta/xcfa/cli/).

- `XcfaCli.kt` calls `runConfig` in `ExecuteConfig.kt`, which validates the input, runs `frontend` and `backend`, maps the result and writes the witness.
- `params/`: `XcfaConfig.kt` (the config tree, with one `SpecBackendConfig` per backend), `ParamValues.kt` (the `Backend`, `Domain`, `Refinement`, `POR`, ... enums, which carry their factories), `ExitCodes.kt`.
- `checkers/`: `ConfigToChecker.kt` dispatches on `Backend` to a `ConfigTo<X>Checker.kt`. `ConfigToPortfolio.kt` maps `--portfolio` names to `portfolio/` (`STABLE` is `complex26`).
- `utils/XcfaParser.kt` (one parser per input type), `witnesstransformation/` (trace concretization, witness application), `utils/*WitnessWriter.kt`.

## Invariants / gotchas

1. **The frontend fallbacks rebuild in-process.** They apply only when no `--memory-model` was given. `UnsupportedPointerSplitException` rebuilds under `flat` and `RequiresByteAddressedMemoryException` under `bytes`. An arithmetic the frontend chose itself is retried as bitvector. A fallback pins its model in the config, because the portfolio re-runs the frontend from that config.
2. **New backend:** add it to `Backend`. The exhaustive `when`s in `BackendConfig.createSpecConfig` and `getSafetyChecker` then need a spec config and a `ConfigTo<X>Checker` for it.
3. Invalid domain/refinement combinations are rejected while the checker is built: `UNSAT_CORE` needs a `Domain` with a `varsPrecRefiner` (currently only EXPL).
4. `ConfigToAsgCegarChecker` passes `traceEnricher = ::threadWriteTriples` so that lassos see pointer writes. Any new consumer of paths needs the same enrichment ([xcfa-analysis AGENTS.md](../xcfa-analysis/AGENTS.md)).
