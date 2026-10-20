# xcfa-dss-analysis

Building blocks of one DSS block analysis: block extraction, violation conditions, postconditions,
solver-backed operators, precisions, the checker roster. Design: `dss/DSS.md`.

## Build and test
- `./gradlew :theta-xcfa-dss-analysis:test` (real Z3 and `xcfa-cli` checkers, needs the native
  libraries).

## Invariants
- No dependency on `xcfa-cli` in production code (only in tests).
- Build checkers and solvers inside `withSolverConstructionLock` and run them inside
  `runWorkerConfig`, whose solver scope releases them; otherwise the heap fills up.
- Violation conditions are exact; a per-path condition may under-approximate, never
  over-approximate.
- Every violation condition goes through `DssAuxVars.canonicalize`: repeated conditions are
  recognized by structural equality.
- An undecided query of `DssPredicateOperators` throws `DssUndecidedQueryException`, never a
  default answer.
- Checker-selection strategies index factories by position and must be thread-safe.

## Change recipes
- New label kind in a block: violation conditions come from `WpState.wep` on `label.toStmt()`;
  allow the label in `checkSupported` (`ViolationConditions.kt`) only if `toStmt` is exact, and add
  a case in `BlockAnalysisPrimitivesTest`.
- New `--dss-*` option: `DssConfig.kt` in `xcfa-cli`, wired in `ConfigToDssChecker.kt`; add it to
  `dss/DSS.md` and `XcfaCliDssTest`.
