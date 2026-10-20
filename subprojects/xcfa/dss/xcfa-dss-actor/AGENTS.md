# xcfa-dss-actor

The DSS actor network: `DssBlockActor` + `PredicateBlockBehavior` per block, the observer, the
quiescence monitor and the executors. Design: `dss/DSS.md`.

## Build and test
- `./gradlew :theta-xcfa-dss-actor:test` (needs the native libraries).
- End-to-end verdicts are one table in `DssVerdictTest`, run with `runDssActorsSequentially` (legacy
  Z3 is not thread-safe). Keep its loop bounds small: DSS unrolls a loop up to the violation.

## Invariants
- No dependency on `xcfa-cli` in production code; checkers are injected factories.
- Routing belongs to `DssBlockActor`, analysis to `DssBlockBehavior`; behaviors return messages,
  they never send them.
- SAFE is quiescence: every message must be processed inside `DssWorker`'s `active` marker.
- Every block answers `RESULT`/`EXCEPTION` with exactly one `STATISTIC`.
- A stored precondition may only be replaced by a stronger one from the same sender, or SAFE
  becomes unsound.
- Message and witness contents must survive `DssExprCodec` (`PROCESS` executor): only program
  variables and `DssAuxVars`; locations travel by index. New fields need matching changes in
  `DssProcessExecutor.kt`.
