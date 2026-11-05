# XCFA CLI

## Build and test

- Build or run the CLI with `./gradlew :theta-xcfa-cli:build` or
  `./gradlew :theta-xcfa-cli:run --args="..."`.
- Run module tests with `./gradlew :theta-xcfa-cli:test`.
- Run the feature regressions with `./gradlew :theta-xcfa-cli:fixtureTest`; run
  `./gradlew :theta-xcfa-cli:canaryTest` for the fixture gate plus the broader SV-Benchmarks
  smoke suite.
- Semantic frontend changes need a discriminating verdict fixture under `canaries/fixtures/` and a
  matching row in `canaries/fixtures/fixtures.tsv`. Use `PARSE-OK` only for parse/build changes;
  use `SAFE` or `UNSAFE` when the change affects program meaning.
- The canary suite uses the sibling `sv-benchmarks` checkout for property files. It re-extracts
  `build/distributions/Theta-svcomp` when the zip is newer than the extracted `theta.jar`.

## Integration points and invariants

- `XcfaCli.kt` parses command-line options, `params/XcfaConfig.kt` defines them, and
  `ExecuteConfig.kt` orchestrates parsing, analysis, and output. `utils/XcfaParser.kt` wires the
  language frontend and XCFA passes.
- Automatic C memory-model fallback is allowed only when `--memory-model` was not specified.
  Pin any selected fallback in the shared config because portfolio configurations may rebuild the
  frontend. The `bytes` model requires bitvector arithmetic; if it cannot represent the input,
  restore the requested arithmetic before falling back to `flat`.
- Frontend failures normally log and exit. Re-throw only the specific typed limitations that the
  caller can recover from; do not convert unrelated frontend failures into fallback attempts.
- `utils/CInvariantExport.kt` exports loop invariants only over names that are declared once at
  file scope and in the function (`FunctionVisitor.variablesInScope`). This is a workaround, not a C
  rule: Goblint binds a re-declared name to another declaration, so it confirms false invariants and
  refutes true ones ([goblint#747](https://github.com/goblint/analyzer/issues/747)). The cost is that
  validators which resolve these names correctly get no invariant for those loops. Remove the
  restriction when Goblint resolves such names correctly.
