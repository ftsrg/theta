# xcfa/xcfa-analysis — notes for editing this module

Gradle module: `:theta-xcfa-analysis`. Binds XCFAs to the generic algorithms of [common/analysis](../../common/analysis/AGENTS.md). Checkers are assembled from these parts in [xcfa-cli](../xcfa-cli/AGENTS.md)'s `checkers/`. The module has no README of its own; the papers behind `por/` and `coi/` are listed in [xcfa/README.md](../xcfa/README.md).

## Layout

Paths are relative to [src/main/java/hu/bme/mit/theta/xcfa/analysis/](src/main/java/hu/bme/mit/theta/xcfa/analysis/).

- `XcfaState` (per-process location stacks and variable lookups), `XcfaAction` (a `PtrAction` over one edge), `XcfaPrec`.
- `XcfaAnalysis.kt`: the LTS (`getXcfaLts`), the abstract analyses (`ExplXcfaAnalysis`, `PredXcfaAnalysis`, ...), the abstractor and `getBoundedXcfaChecker`.
- Refinement: `XcfaSingleExprTraceRefiner`, `XcfaPrecRefiner`, `XcfaVarsRefutation.kt`. Error detection: `XcfaErrorDetector.kt`, `XcfaDataRaceCheck.kt`.
- `por/` (partial-order reduction LTSs), `coi/` (cone of influence), `oc/` (the OC checker), `monolithic/` (XCFA to `MonolithicExpr` for the bounded and other monolithic checkers), `autoexpl/`, `proof/`.

## Build and test

`./gradlew :theta-xcfa-analysis:test`. Tests parse the C programs in `src/test/resources/` with c2xcfa's `getXcfaFromC` (a test-only dependency) and run on the legacy Z3 (`Z3LegacySolverFactory`), whose native libraries the Gradle test task puts on the library path from `lib/`. The default, parse-only `canaryTest` never reaches this module. The verdict fixtures of `:theta-xcfa-cli:fixtureTest` do, as they run the STABLE portfolio, and so does `canaryTest` with `-Ptheta.canary.mode=full`.

## Invariants / gotchas

1. **Memory writes must be threaded along a path.** An abstract `XcfaAction` knows only its own writes. On a concrete path, a memory read therefore binds to the unconstrained initial memory unless the path's write triples are re-threaded. Every consumer of a path does this:
   - the ARG refiner, through `threadWriteTriples(Trace)`;
   - the liveness refiner, through `threadWriteTriples(ASGTrace)` passed as its `traceEnricher`;
   - `getBoundedXcfaChecker`, through its `actionEnricher`;
   - xcfa-cli's `XcfaTraceConcretizer`.

   A new trace checker or concretizer must do the same (`XcfaAction.withLastWrites`).
2. **Refutation indices are trace positions.** `XcfaPrecRefiner` maps procedure-local variable instances back through the `varLookup` of the state at each index, and pruning uses the index as a node position. Refutations indexed by SSA version, as the UNSAT_CORE checker's are, are converted with `withTracePositionIndices()` ([XcfaVarsRefutation.kt](src/main/java/hu/bme/mit/theta/xcfa/analysis/XcfaVarsRefutation.kt)).
3. `findDataRace` must return null on bottom states, because the ARG builder tests those as targets too. Its address query reads nested dereferences at uniqueness index 0 on a repatched state. It answers "may alias" only on `UnknownSolverStatusException`; do not widen that catch, or an encoding error turns into a race that refinement can never remove.
4. A Safe result on a model with `unsafeUnrollUsed` is unreliable. `XcfaPipelineChecker` and `XcfaOcChecker` check the flag before they report Safe.
