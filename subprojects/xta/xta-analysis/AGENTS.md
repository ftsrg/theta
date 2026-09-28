# xta/xta-analysis — notes for editing this module

Gradle module: `:theta-xta-analysis`. Binds Uppaal timed automata (an `XtaSystem` from [xta](../xta/README.md)) to the analyses of [common/analysis](../../common/analysis/AGENTS.md). Its only production consumer is [xta-cli](../xta-cli/README.md), through `LazyXtaCheckerFactory`. Overview: [README.md](README.md); the papers behind the lazy algorithms are listed in [xta/README.md](../xta/README.md).

## Build and test

- `./gradlew :theta-xta-analysis:test`. The tests load the `.xta` models in `src/test/resources/` with `XtaDslManager.createSystem`. `:theta-xta-cli` has no tests, so this is the whole XTA suite.
- The analyses need no SMT solver (explicit values and DBMs). `LazyXtaCheckerTest` runs every `DataStrategy` × `ClockStrategy` pair on each model and checks the resulting ARG with `ArgChecker.isWellLabeled` on the legacy Z3, so a new enum value is covered automatically.

## Layout

Paths are relative to [src/main/java/hu/bme/mit/theta/xta/analysis/](src/main/java/hu/bme/mit/theta/xta/analysis/).

- `XtaState` (location vector plus an inner state; `isCommitted()`/`isUrgent()` derive from the locations), `XtaAction` (basic, binary and broadcast synchronization), `XtaLts`, and the `XtaAnalysis` wrapper that lifts an inner analysis.
- `zone/`: DBM semantics in `XtaZoneUtils.post`/`pre`, with LU-bound (`lu/`) and interpolating (`itp/`) zone states. `expl/`: explicit data variables, with `itp/`.
- `lazy/`: `LazyXtaChecker` and `LazyXtaCheckerFactory`. A checker combines one `DataStrategy` and one `ClockStrategy`, each an `AlgorithmStrategy` that sees its half of the `Prod2State` through a `Lens`.

## Invariants / gotchas

1. **Time may elapse only if every location of the vector is NORMAL.** The rule is implemented twice: in `XtaZoneUtils` (successor zones, and the initial zone in `XtaZoneInitFunc`) and in `XtaAction.getStmts()` (the `_delay` havoc of the statement view, which `toExpr()` and `ArgChecker` read). Change both together.
2. **Initial states must not be bottom.** `LazyXtaChecker` puts initial states into the ARG unchecked, and the strategies read both components of the product state, which a bottom `Prod2State` does not have. This is why `XtaZoneInitFunc` does not apply the initial invariants: `post` applies the source invariants anyway.
3. `XtaZoneAnalysis` is created per system (`XtaZoneAnalysis.create(system)`) because its initial zone depends on the initial locations. The `lu/` and `itp/` init funcs only wrap it.
4. Clock guards on the receiving edges of a broadcast are not supported: `XtaZoneUtils` throws `UnsupportedOperationException`.

## Change recipe: a new data or clock strategy

Add the value to `DataStrategy` or `ClockStrategy` (xta-cli exposes them as `--discrete` and `--clock`). Add a factory method to `DataStrategies` or `ClockStrategies` that returns an `AlgorithmStrategy` over the left or right lens, and a case to every nested `switch` in `LazyXtaCheckerFactory.combineStrategies`, whose defaults throw `AssertionError`.
