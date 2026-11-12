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
- Run `DssVerdictTest`'s methods in separate Gradle invocations: its JVM's native memory grows by
  about 1 GB per 10 s and the whole class needs over 16 GB.

## Invariants
- Checkers are injected factories (`(XCFA) -> XcfaChecker`); this package never builds one itself.
- Build checkers and solvers inside `withSolverConstructionLock` and run them inside
  `runWorkerConfig`, whose solver scope releases them; otherwise the heap fills up.
- A checker budget is only enforced at solver calls (refused past the deadline, interrupted by
  `DssDeadline`'s watchdog while running): budgeted checkers must take their solvers from
  `DeadlineSolverManager` (`blockCheckers` in `xcfa-cli` does), and no wrapper may turn a
  `DssBudgetExceededException` into a result or a checker failure (`BoundedChecker` falls back to
  its uninterpolated proof when interpolation runs out, which is still a proof).
- A `DssBlockCutRequest` must reach `getDssChecker`, which restarts with the block cut (`PROCESS`
  rebuilds it by class name, and its workers redo the cuts from `DssConfig.workerCuts`), or the
  sequential executor, which replaces the block in place when it has a `DssBlockCutter`. There a
  piece must hear the latest message of every outer neighbor (`DssMessageBroadcaster` keeps them),
  the neighbors must re-key what they stored from the block to the adjacent pieces
  (`onNeighborReplaced`) and its queued messages be dropped, or a stale entry under the old id
  would outlive the block.
- A block cut is a decomposition run on a copy of the block (`cloneBlock`, shared with
  `extractBlockXcfa`), and must keep the block's paths: every piece takes all of the block's edges
  out of each location it passes through, and a piece reaching an exit that has successors ends
  there. `keepsPaths` refuses anything else, so a new decomposition needs no cut-specific code.
- In `BIDIRECTIONAL` a cut is of a forward block (a backward block's request cuts the forward
  block it reverses, `cutTargetOf`), and the backward graph is rebuilt from the cut forward one,
  so the two directions keep sharing their block boundaries.
- Sent violation conditions are exact; a per-path condition may under-approximate, never
  over-approximate. A generalization (`Generalizers`) over-approximates, so it is only a probe
  target or a conjecture: a probe's UNSAFE result is discarded, and a generalization never reaches a
  message, a witness record or a path condition. A conjecture's condition and its may violations
  (`DssMayViolationMessage`) never become a violation condition, a record or a verdict either; a
  root that reaches one sends `CONJECTURE_FAILED`.
- A behavior must not ignore `CONJECTURE` or `MAY_VIOLATION` (the defaults throw): an assumed
  conjecture is sound only because every block ending at its location checks it, and every block
  before those passes the may violations on. A block that cannot (per-path conditions, a failed
  run) refutes the conjecture instead.
- Every violation condition goes through `DssAuxVars.canonicalize`: repeated conditions are
  recognized by structural equality.
- An undecided query of `DssPredicateOperators` throws `DssUndecidedQueryException`, never a
  default answer.
- A block run's postcondition and precision pass through `quantifierFree`
  (`--dss-quantified-predicates`), which may only weaken them. Its witness states may only be
  replaced by equivalents (`quantifierFreeIfEquivalent`): `backwardInvariants` complements them.
- Checker-selection strategies index factories by position and must be thread-safe.
- Routing belongs to `DssBlockActor`, analysis to `DssBlockBehavior`; behaviors return messages,
  they never send them.
- SAFE is quiescence: every message must be processed inside `DssWorker`'s `active` marker. With
  conjectures the coordinator is part of it, so they need a single network (the concurrent
  monitor then waits for the coordinator's thread too).
- Every block answers `RESULT`/`EXCEPTION` with exactly one `STATISTIC`.
- A postcondition message replaces everything stored from its sender, and every analysis starts
  from all stored preconditions (plus top while a predecessor has not sent): analyzing only the new
  states, or skipping a state covered by an older one, makes SAFE unsound.
- Message and witness contents must survive `DssExprCodec` (`PROCESS` executor): only program
  variables and `DssAuxVars`; locations travel by index. New fields need matching changes in
  `DssProcessExecutor.kt`. Each block has the codec of its own program; the reversed program has
  its own variables (temporaries) and locations.
- A bounded checker's proof is over program variables only when interpolated
  (`--dss-interpolate-bounded-proofs`); otherwise it has fresh, implicitly existential variables,
  unique to each proof, so solver checks over several such states stay sound but are incomplete.
- A postcondition's `inputs` must name exactly the stored versions its analysis started from, it
  must cover every exit state of those (a start state whose run yields no summary fails the
  analysis), and an analysis without exit states must still report `false` (`observerOnly`):
  `DssMeetingActor`'s SAFE relies on all three (`trackSummaries`).
- `DssMeetingActor` intersects summaries of different runs, so they may only contain program
  variables, temporaries and `DssAuxVars`; this is why `BIDIRECTIONAL` takes CEGAR checkers only,
  except for a bounded finisher, whose blocks are `DssMeetingSide.uncertified`.
- A `DssRestrictionMessage` only ever strengthens a block's start states, while a conjecture's
  invariant is dropped again when it is retracted; neither enters a violation condition. A block
  under either, or fed by one, reports no witness invariants, and records them only without both.
- `backwardInvariants` complements the reached states, which is valid only if they exclude the
  entry's states (the reversed program's error): it takes `errorFreeInvariants`, recorded by runs
  that kept the error targets. A targetless run's states are valid forward invariants only.
- Networks of one run need unique block ids (the backward network uses `R.`). A failure reaches
  only its own network (`DssConnection.failureScope`), and a network with a shut-down block is
  never SAFE.

## Change recipes
- New label kind in a block: violation conditions come from `WpState.wep` on `label.toStmt()`;
  allow the label in `checkSupported` (`ViolationConditions.kt`) only if `toStmt` is exact, and add
  a case in `BlockAnalysisPrimitivesTest`. The backward direction needs an exact inverse in
  `ProgramReversal.kt` (otherwise it must throw), with a case in `ProgramReversalTest`.
- New `--dss-*` option: `DssConfig.kt` in `xcfa-cli`, wired in `ConfigToDssChecker.kt`, with a
  case in `XcfaCliDssTest`. Keep it `hidden = true` until it is stable (master keeps few public
  options); only public ones go into `README.md`'s table.
- New generalization method: a `DssGeneralizerKind` entry and its cases in `Generalizers`
  (`generalize`, `failed`); it can only use what `GeneralizationContext` offers. Add a
  `DssVerdictTest` matrix for it, and run it alone first: a case it fails to help can diverge.
