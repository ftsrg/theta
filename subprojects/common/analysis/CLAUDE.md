# common/analysis — edit-time notes

Gradle module: `:theta-analysis`. Build/tests: `./gradlew :theta-analysis:build` / `:theta-analysis:test` (native solvers in tests need `LD_LIBRARY_PATH=$PROJECT_DIR/lib/`). Formatting/copyright: see root [CLAUDE.md](../../../CLAUDE.md).

Conceptual background: [README.md](README.md) (thin) and [doc/CEGAR-algorithms.md](../../../doc/CEGAR-algorithms.md) (user-level CEGAR config concepts — read before changing CEGAR behavior).

Paths below relative to [src/main/java/hu/bme/mit/theta/analysis/](src/main/java/hu/bme/mit/theta/analysis/).

## Vocabulary — the root interfaces

Everything is generic over `<S extends State, A extends Action, P extends Prec>`; a "domain" is an implementation triple bundled by an `Analysis`.

| Concept | What |
|---|---|
| [State](src/main/java/hu/bme/mit/theta/analysis/State.java) | `isBottom()` only |
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

`ExprTraceChecker<R>` (SeqItp/FwBinItp/BwBinItp/Newton/UCB/UnsatCore variants) checks feasibility of a `Trace<ExprState,ExprAction>` → `ExprTraceStatus`: feasible (with `Valuation`) or infeasible (with `Refutation`, which has `getPruneIndex()`) → [RefutationToPrec](src/main/java/hu/bme/mit/theta/analysis/expr/refinement/RefutationToPrec.java) maps it into the domain's `Prec` (`ItpRefToExplPrec`, `ItpRefToPredPrec`, …) → `JoiningPrecRefiner`/`MultiExprTraceRefiner` implement `Refiner` and prune the ARG.

**Binding a new formalism to CEGAR** (the recurring task): implement `ExprAction` + `LTS`, supply init expr + target predicate, wrap a domain (`expl`/`pred`, or `prod2/` products) in your `Analysis`, then assemble `ArgBuilder.create(lts, analysis, target)` → `BasicArgAbstractor.builder(...)` (projection/waitlist/stopCriterion) → trace checker + `RefutationToPrec` → `JoiningPrecRefiner` → `CegarChecker.create(...)`. Reference consumers: `cfa-analysis`, `xsts-analysis`, `xcfa-analysis`.

## Package map (one-liners; sizes in files)

- [algorithm/](src/main/java/hu/bme/mit/theta/analysis/algorithm/) (134) — checkers: `arg/` (ARG + builder + debug), `cegar/`, `bounded/` (BMC/k-induction/IMC), `mdd/` (decision-diagram reachability), `ic3/`, `oc/` (ordering-consistency), `loopchecker/` + `asg/` (liveness), `mcm/` (memory models), `chc/`, `tracegeneration/`.
- [expr/](src/main/java/hu/bme/mit/theta/analysis/expr/) (46) — ExprState/ExprAction + `refinement/` pipeline above.
- [expl/](src/main/java/hu/bme/mit/theta/analysis/expl/) (14), [pred/](src/main/java/hu/bme/mit/theta/analysis/pred/) (10) — the two base domains.
- [prod2/](src/main/java/hu/bme/mit/theta/analysis/prod2/) (19), `prod3/`, `prod4/`, [unit/](src/main/java/hu/bme/mit/theta/analysis/unit/) — product/unit domains; [ptr/](src/main/java/hu/bme/mit/theta/analysis/ptr/) — pointer tracking.
- [zone/](src/main/java/hu/bme/mit/theta/analysis/zone/) (11) — DBM/zone domain (consumes core `clock/`; used by `xta`).
- [multi/](src/main/java/hu/bme/mit/theta/analysis/multi/) (15) — composed multi-formalism analyses.
- [waitlist/](src/main/java/hu/bme/mit/theta/analysis/waitlist/), [reachedset/](src/main/java/hu/bme/mit/theta/analysis/reachedset/), [stmtoptimizer/](src/main/java/hu/bme/mit/theta/analysis/stmtoptimizer/), [runtimemonitor/](src/main/java/hu/bme/mit/theta/analysis/runtimemonitor/), [utils/](src/main/java/hu/bme/mit/theta/analysis/utils/) (visualizers), [impl/](src/main/java/hu/bme/mit/theta/analysis/impl/) (prec-mapping adapters) — infrastructure.

## Oddities (build-level)

`build.gradle.kts` declares direct deps on `solver-javasmt`, `solver-z3-legacy` (twice!), `graph-solver`, and local jars `Deps.delta`/`Deps.hoaf` — the "generic" module is not solver-agnostic in practice.
