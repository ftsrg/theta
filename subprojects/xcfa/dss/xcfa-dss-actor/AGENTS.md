# xcfa-dss-actor

The DSS actor network: one `DssBlockActor` per block running `PredicateBlockBehavior` (the block
analysis), the observer, the quiescence monitor, the two executors, and the diagnostic trace. The
design and its CPAchecker counterparts are in `doc/DSS.md` (sections 7, 8, 9, 11); read the
relevant section before changing behavior.

## Build and test
- `./gradlew :theta-xcfa-dss-actor:test`
- The end-to-end tests run real checkers (`xcfa-cli`, Z3) under `assertTimeoutPreemptively` and
  need the native libraries. They are timing-sensitive: on a loaded machine, a timeout of
  `NestedLoopActorTest` is not necessarily a regression; rerun it on its own before concluding.
- Run every new end-to-end case with both executors (`runDssActors` and
  `runDssActorsSequentially`), as the existing tests do. `DssProcessExecutorTest` starts real
  worker JVMs (`DssProcessTestWorker`, the test classpath) and rebuilds its fixture there.

## Invariants
- **No dependency on `xcfa-cli`** in production code (same reason as in `xcfa-dss-analysis`);
  checkers are injected factories.
- **Routing belongs to `DssBlockActor`, analysis to `DssBlockBehavior`**: postconditions go
  forward to successors, violation conditions backward to predecessors, and a violation condition
  at the root becomes `RESULT(UNSAFE)`. Behaviors return messages; they never send them.
- **SAFE is quiescence**, detected by `DssThreadMonitor` (concurrent) or by empty queues
  (sequential). Every message must be processed inside the `active` marker of `DssWorker`, or
  the monitor can declare SAFE while a message is still being handled.
- **Every block answers `RESULT`/`EXCEPTION` with exactly one `STATISTIC`**; the observer waits
  for all of them, in any arrival order.
- **Stored preconditions must keep covering the entry states**: a state may only be replaced by a
  stronger one from the same sender (`storePrecondition`). Weakening this rule makes SAFE unsound
  (`doc/DSS.md` section 9).
- **Repeated violation conditions** are detected by structural equality, which relies on
  `DssAuxVars.canonicalize` in `xcfa-dss-analysis`.
- Legacy Z3 is not thread-safe; the concurrent executor needs a thread-safe solver (`Z3:new`). The
  process executor (`runDssActorsInProcesses`) runs any solver in parallel.
- **Message expressions must survive `DssExprCodec`** (process executor): only program variables
  and `DssAuxVars`, no quantifiers if equality matters. A new message field needs a matching
  change in `DssProcessExecutor.kt`'s `writeMessage`/`readMessage`.

## Trace (`--dss-trace`, `--dss-trace-expressions`)
- `DssTrace` is process-wide and off by default; emit through `DssTrace` only, never through
  `println`, as the CLI routes it to the logger.
- Line format: `DSS-TRACE <ms> <event> key=value...`. Values must not contain spaces; the only
  exception is `expr=`, which must stay the last field (`traceContent` guarantees it).
- New events or fields belong in the `--dss-trace` row of the option table in `doc/DSS.md`.

## Integration points
- Entry points `runDssActors` / `runDssActorsSequentially` / `runDssActorsInProcesses`, called by
  `xcfa-cli` (`ConfigToDssChecker.kt`, `--dss-executor`); xcfa-cli also starts the worker
  processes and runs `serveDssBlocks` in them (hidden `--dss-worker-*` options).
- Consumes `xcfa-dss-analysis` (block-analysis primitives) and `xcfa-dss-decomposition` (block
  graph).
