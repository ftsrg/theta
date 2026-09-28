# xsts/xsts-analysis — notes for editing this module

Gradle module: `:theta-xsts-analysis`. Binds XSTS models ([xsts](../xsts/README.md)) to the algorithms of [common/analysis](../../common/analysis/AGENTS.md): CEGAR through `XstsConfigBuilder`, the monolithic checkers (bounded, IC3, MDD) through `XstsToMonolithicAdapter`, CHC through `XSTS.toRelations()`, and trace generation. The user-facing tool is [xsts-cli](../xsts-cli/README.md). Overview: [README.md](README.md).

## Build and test

- `./gradlew :theta-xsts-analysis:test`. Most tests parse a `src/test/resources/model/*.xsts` file concatenated with a `property/*.prop` file (`XstsDslManager.createXsts`). The checker tests are parameterized over a `data()` table, so a regression model is a new pair plus a row there. They run on the bundled Z3. `XstsHornTest` installs SMT-LIB solvers (z3, eldarica, golem) and skips when it cannot; the root `verifySolverInstallations` task then fails the build.
- The tests of `:theta-analysis`, `:theta-ltl`, `:theta-multi-tests` and `:theta-petrinet-xsts` also use this module. Run them after an API change.

## Layout

The package `hu.bme.mit.theta.xsts.analysis` is split across [src/main/java/](src/main/java/hu/bme/mit/theta/xsts/analysis/) and [src/main/kotlin/](src/main/kotlin/hu/bme/mit/theta/xsts/analysis/), and both hold Kotlin files: search both.

- `XstsState`, `XstsAction`, `XstsLts`, and the `XstsAnalysis` wrapper (with `XstsOrd`, `XstsInitFunc`, `XstsTransFunc`) that lifts a `StmtAction` analysis to XSTS.
- `config/` (`XstsConfigBuilder`: CEGAR domains and refinements, init precisions from `initprec/`, `autoexpl/`), `concretizer/`, `tracegeneration/`, `pipeline/` (`XstsPipelineChecker` over `XstsToMonolithicAdapter`).
- Kotlin side: `XstsToRelations.kt` (CHC encoding), `XstsToMonolithicAdapter.kt`, `passes/` (XSTS-to-XSTS transformers such as `XstsStmtFlatteningTransformer`).

## Invariants / gotchas

1. **A run is `init`, then `env` and `tran` alternating.** `XstsState` carries `isInitialized()` and `lastActionWasEnv()`, `XstsLts` picks the statement set from them, and `XstsOrd` compares only states with equal flags. `XstsToMonolithicAdapter` fuses one `env; tran` pair into one monolithic step, and `XstsTraceConcretizerUtil.concretize` expands such a trace back. A change to the step structure must update all of these.
2. **Declaration initializers live in `xsts.getInitFormula()`, not in the `init` statement.** Seed every analysis, trace checker and encoding with it, as `XstsConfigBuilder`, `XstsTracegenBuilder`, the concretizers, `toRelations()` and `XstsToMonolithicAdapter` do. Seeding with `True()` loses the declared initial values: every variable starts at top.
3. **Locals are not state.** `getVars()` also holds the transition-scoped locals; concretized traces go through `VarFilter`, which keeps only `getStateVars()`. A pass that rebuilds an XSTS uses the 8-argument constructor with `stateVars` and `localVars`, as those in `passes/` do: the 6-argument one treats every variable as state.
4. **Names are not identities.** Two locals, or a local and a global, may share a name, so never key a variable by name. `toRelations()` suffixes each CHC parameter with the variable's position (`|a_1|`, `|a_1_new|`), because solvers identify bound parameters by name.

## Change recipe: a new CEGAR domain or refinement

Add the value to `XstsConfigBuilder.Domain` or `Refinement` (xsts-cli exposes both enums directly as options). List it in `getSupportedDomains()`/`getSupportedRefinements()` of the `BuilderStrategy` that handles it (the strategy constructors reject anything else), and dispatch to that strategy in `build()`. A new precision type also needs a method on `XstsInitPrec` and in each of its implementations under `initprec/`.
