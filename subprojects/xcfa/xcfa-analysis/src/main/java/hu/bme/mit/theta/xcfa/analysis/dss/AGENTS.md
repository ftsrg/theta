# xcfa-analysis: `dss` package

Distributed summary synthesis (design: `README.md` here). `decomposition` splits a procedure into
blocks, `analysis` holds one block's analysis (block extraction, violation conditions,
postconditions, operators, precisions, the checker roster), and `actor` runs the blocks as a
message-passing network with its executors. The `--backend DSS` wiring lives in `xcfa-cli`.

## Build and test
- `./gradlew :theta-xcfa-analysis:test --tests 'hu.bme.mit.theta.xcfa.analysis.dss.*'` (needs the
  native libraries).
- Tests with real checkers use `xcfa-cli` (a test-only dependency); keep them here rather than in
  `xcfa-cli`, as Sonar only counts a module's own tests towards its coverage.
- End-to-end verdicts are one table in `DssVerdictTest`, run with `runDssActorsSequentially` (legacy
  Z3 is not thread-safe). Keep its loop bounds small: DSS unrolls a loop up to the violation.

## Invariants
- Checkers are injected factories (`(XCFA) -> XcfaChecker`); this package never builds one itself.
- Build checkers and solvers inside `withSolverConstructionLock` and run them inside
  `runWorkerConfig`, whose solver scope releases them; otherwise the heap fills up.
- Violation conditions are exact; a per-path condition may under-approximate, never
  over-approximate.
- Every violation condition goes through `DssAuxVars.canonicalize`: repeated conditions are
  recognized by structural equality.
- An undecided query of `DssPredicateOperators` throws `DssUndecidedQueryException`, never a
  default answer.
- Checker-selection strategies index factories by position and must be thread-safe.
- Routing belongs to `DssBlockActor`, analysis to `DssBlockBehavior`; behaviors return messages,
  they never send them.
- SAFE is quiescence: every message must be processed inside `DssWorker`'s `active` marker.
- Every block answers `RESULT`/`EXCEPTION` with exactly one `STATISTIC`.
- A stored precondition may only be replaced by a stronger one from the same sender, or SAFE
  becomes unsound.
- Message and witness contents must survive `DssExprCodec` (`PROCESS` executor): only program
  variables and `DssAuxVars`; locations travel by index. New fields need matching changes in
  `DssProcessExecutor.kt`.

## Change recipes
- New label kind in a block: violation conditions come from `WpState.wep` on `label.toStmt()`;
  allow the label in `checkSupported` (`ViolationConditions.kt`) only if `toStmt` is exact, and add
  a case in `BlockAnalysisPrimitivesTest`.
- New `--dss-*` option: `DssConfig.kt` in `xcfa-cli`, wired in `ConfigToDssChecker.kt`; add it to
  `README.md` here and `XcfaCliDssTest`.
