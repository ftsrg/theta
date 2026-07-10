# common/analysis — notes for editing this module

(Not a conceptual overview — that's the README/wiki. This file holds what you need when *changing* code here: invariants, conventions, change recipes.)

Gradle module: `:theta-analysis`. Build/tests: `./gradlew :theta-analysis:build` / `:theta-analysis:test` (native solvers in tests need `LD_LIBRARY_PATH=$PROJECT_DIR/lib/`). Formatting/copyright: see root [CLAUDE.md](../../../CLAUDE.md).

Conceptual background: [README.md](README.md) (thin) and [doc/CEGAR-algorithms.md](../../../doc/CEGAR-algorithms.md) (user-level CEGAR config concepts — read before changing CEGAR behavior).

**Consuming this module from a formalism?** Read [USING.md](USING.md) instead — this file is about editing analysis itself.

Paths below relative to [src/main/java/hu/bme/mit/theta/analysis/](src/main/java/hu/bme/mit/theta/analysis/).

## Vocabulary — the root interfaces

Everything is generic over `<S extends State, A extends Action, P extends Prec>`; a "domain" is an implementation triple bundled by an `Analysis`.

| Concept | What |
|---|---|
| [State](src/main/java/hu/bme/mit/theta/analysis/State.java) | root interface of all abstract states (domain states like `ExplState`/`PredState`, formalism states like `CfaState`, products, …). The only operation *shared by all* is `isBottom()` (is this the contradictory/unreachable state); everything else lives in subinterfaces — most importantly [ExprState](src/main/java/hu/bme/mit/theta/analysis/expr/ExprState.java) (`toExpr()`) |
| [Action](src/main/java/hu/bme/mit/theta/analysis/Action.java) | empty marker — formalisms define real actions |
| [Prec](src/main/java/hu/bme/mit/theta/analysis/Prec.java) | abstraction precision; `getUsedVars()` |
| [Analysis](src/main/java/hu/bme/mit/theta/analysis/Analysis.java) | bundle: `PartialOrd<S>` + `InitFunc<S,P>` + `TransFunc<S,A,P>` |
| [LTS](src/main/java/hu/bme/mit/theta/analysis/LTS.java) | `getEnabledActionsFor(state)` — the formalism side of exploration |
| [Trace](src/main/java/hu/bme/mit/theta/analysis/Trace.java) | immutable; **invariant: #states = #actions + 1** |

## The Proof-generic checker layer ([algorithm/](src/main/java/hu/bme/mit/theta/analysis/algorithm/))

`Checker<Pr extends Proof, I>` → `Result<Pr>`; `SafetyChecker<Pr, C extends Cex, I>` → `SafetyResult<Pr,C>` (`Safe`/`Unsafe`/`Unknown` via static factories). **CEGAR is generic over `Proof`, not ARG**: `Abstractor<P,Pr>` (`createProof()` + `check(proof, prec)`), `Refiner<P,Pr,C>` (`refine(proof, prec)`). ARG-bound aliases: `ArgAbstractor`/`ArgRefiner`/`ArgCegarChecker`; `AsgCegarChecker` is the ASG/liveness variant.

## Invariants — violating these breaks distant code

1. **The `Proof` is mutable shared state.** [CegarChecker](src/main/java/hu/bme/mit/theta/analysis/algorithm/cegar/CegarChecker.java) creates it once (`abstractor.createProof()`) and hands the *same instance* to abstractor and refiner every iteration — the refiner prunes it in place. A new `Abstractor`/`Refiner` pair must agree on incremental semantics (re-expansion after prune, covering invalidation).
2. **`Trace` shape**: #states = #actions + 1, at least one state — checked in the ctor, relied on by every trace checker.
3. **New checker algorithms implement `SafetyChecker`** (or `Checker` for non-safety) and return `SafetyResult` via the static factories — don't subclass `SafetyResult`.
4. **[ExprAction](src/main/java/hu/bme/mit/theta/analysis/expr/ExprAction.java) is the SMT bridge**: `toExpr()` + `nextIndexing()` (core `VarIndexing`); trace checkers unfold these via core `PathUtils`. An action whose `toExpr`/`nextIndexing` disagree (e.g. primes not covered by the indexing) fails deep inside refinement, not at the call site.
5. **Domain conventions** (from `expl`/`pred`): Analysis impls have private ctor + `create(...)`, singleton `PartialOrd`s (`ExplOrd.getInstance()`); states are immutable values.

## The refinement pipeline ([expr/refinement/](src/main/java/hu/bme/mit/theta/analysis/expr/refinement/))

`ExprTraceChecker<R>` (SeqItp/FwBinItp/BwBinItp/Newton/UCB/UnsatCore variants) checks feasibility of a `Trace<ExprState,ExprAction>` → `ExprTraceStatus`: feasible (with `Valuation`) or infeasible (with `Refutation`, which has `getPruneIndex()`) → a `PrecRefiner` (e.g. `JoiningPrecRefiner.create(refToPrec)`) maps it into the domain's `Prec` via [RefutationToPrec](src/main/java/hu/bme/mit/theta/analysis/expr/refinement/RefutationToPrec.java) (`ItpRefToExplPrec`, `ItpRefToPredPrec`, …) → `SingleExprTraceRefiner`/`MultiExprTraceRefiner` implement `ArgRefiner`, prune the ARG per `PruneStrategy`.

**Binding a new formalism to CEGAR** (the recurring task; verified against [CfaConfigBuilder](../../cfa/cfa-analysis/src/main/java/hu/bme/mit/theta/cfa/analysis/config/CfaConfigBuilder.java)): implement `ExprAction` + `LTS`, supply init expr + target predicate, wrap a domain (`expl`/`pred`, or `prod2/` products) in your `Analysis`, then assemble: `ArgBuilder.create(lts, analysis, target)` → `BasicArgAbstractor.builder(argBuilder)` (projection/waitlist/stopCriterion/logger) → `SingleExprTraceRefiner.create(traceChecker, precRefiner, pruneStrategy, logger)` → `ArgCegarChecker.create(abstractor, refiner, logger)`. Reference consumers: `cfa-analysis` (config/), `xsts-analysis`, `xcfa-analysis`.

## Package map (verified)

⚠ **Two source roots**: most code is under `src/main/java/` (Java *and* Kotlin mixed), but `multi/` has additional Kotlin files under [src/main/kotlin/](src/main/kotlin/hu/bme/mit/theta/analysis/) — search both when editing `multi`.

- [algorithm/](src/main/java/hu/bme/mit/theta/analysis/algorithm/) (134 files) — all checking algorithms (CEGAR/ARG, BMC/k-ind/IMC, IC3, MDD, CHC, liveness/ASG, oc, mcm, tracegeneration). **Has its own [CLAUDE.md](src/main/java/hu/bme/mit/theta/analysis/algorithm/CLAUDE.md)** — read it before editing there.
- [expr/](src/main/java/hu/bme/mit/theta/analysis/expr/) (46) — ExprState/ExprAction + the `refinement/` pipeline above. `StmtAction` (abstract) derives `toExpr`/`nextIndexing` from `getStmts()` automatically — the easiest `ExprAction` base for formalisms. Note `ExprState extends InvariantProof`, so every expr-state can serve as a `Proof`.
- [expl/](src/main/java/hu/bme/mit/theta/analysis/expl/) — explicit-value domain. `ExplState` = partial valuation or bottom singleton; `ExplStmtTransFunc` fast-paths deterministic stmts via `StmtApplier`, falls back to SMT enumeration, and **beyond `maxSuccToEnumerate` returns an approximate (havoc-like) successor rather than failing**.
- [pred/](src/main/java/hu/bme/mit/theta/analysis/pred/) — predicate domain. `PredAbstractors`: boolean / booleanSplit / cartesian. ⚠ `PredState.isBottom()` is syntactic (`{False()}` only) while `PredOrd` is solver-semantic.
- [prod2/](src/main/java/hu/bme/mit/theta/analysis/prod2/) — product domain. ⚠ The plain `Prod2Analysis.create(a1,a2)` installs **no joint-satisfiability strengthening** — components can be locally consistent but globally infeasible; use the operator-taking overload (`prod2explpred/` has the real one). `prod3/`/`prod4/` exist but have no consumers.
- [unit/](src/main/java/hu/bme/mit/theta/analysis/unit/) — trivial singleton domain (location-only tracking). [ptr/](src/main/java/hu/bme/mit/theta/analysis/ptr/) — pointer/memory-write tracking wrapper over an inner analysis (Kotlin, consumed by xcfa).
- [zone/](src/main/java/hu/bme/mit/theta/analysis/zone/) — DBM zone domain over core `clock/`; index 0 is the implicit zero-clock (ops on it throw); closure (`close()`) is a load-bearing invariant. LU-abstraction lives in `xta-analysis`; this package only provides `BoundFunc` + `isLeq(that, boundFunc)`. Consumed by `xta` only.
- [multi/](src/main/java/hu/bme/mit/theta/analysis/multi/) — two-formalism product over a shared data state (`MultiAnalysisSide`, `NextSideFunctions`: alternating/nondet). Backbone of LTL checking (system × Büchi) for cfa/xsts via `common/ltl`.
- [waitlist/](src/main/java/hu/bme/mit/theta/analysis/waitlist/) (FIFO/LIFO/Priority/Random), [reachedset/](src/main/java/hu/bme/mit/theta/analysis/reachedset/) (`Partition` = CEGAR's coverage lookup; `ReachedSet` iface = Impact-only), [stmtoptimizer/](src/main/java/hu/bme/mit/theta/analysis/stmtoptimizer/), [runtimemonitor/](src/main/java/hu/bme/mit/theta/analysis/runtimemonitor/) (`CexMonitor` divergence detection via `MonitorCheckpoint` registry), [utils/](src/main/java/hu/bme/mit/theta/analysis/utils/) (`ProofVisualizer` impls → `common.visualization.Graph`), [impl/](src/main/java/hu/bme/mit/theta/analysis/impl/) (`PrecMappingAnalysis` — present a different Prec type via a mapping function).

## Build-level notes (dependency audit, grep-verified)

Direct deps and why: `Deps.delta` (BME MDD library) → `algorithm/mdd` + MDD visualizers; `graph-solver` → `algorithm/mcm`; `javasmt` → `algorithm/oc/UserPropagatorOcChecker` only (Z3 user propagators).
