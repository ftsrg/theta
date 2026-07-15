# Using theta-analysis: verifying a formalism — API cookbook

Consumer-facing counterpart of [CLAUDE.md](CLAUDE.md) (which covers *editing* this module). Read this when binding a formalism/model to Theta's checking algorithms. Every chain below is verified against a real consumer (cited).

```kotlin
implementation(project(":theta-analysis"))
```

There are three main entry paths, by decreasing generality of what you must implement:

## Path A — CEGAR (the classic; reference: `cfa-analysis/config/CfaConfigBuilder`)

You provide four things:

1. **An action** implementing `ExprAction`. Easiest: extend [StmtAction](src/main/java/hu/bme/mit/theta/analysis/expr/StmtAction.java) — implement `getStmts()` and it derives `toExpr()`/`nextIndexing()` for you (via core `StmtUtils.toExpr`).
2. **An `LTS<S, A>`** — which actions are enabled in a state (your formalism's structure).
3. **An `Analysis<S, A, P>`** — usually by wrapping an existing domain: `ExplStmtAnalysis.create(solver, initExpr, maxEnum)`, `PredAnalysis.create(solver, predAbstractor, initExpr)`, or `Prod2Analysis`/`prod2explpred` for products. Wrap with your formalism's location structure if needed (cfa wraps states as `CfaState<S>`).
4. **A target predicate** `Predicate<? super S>` (what "unsafe" means).

Then assemble (this exact chain is `CfaConfigBuilder`, EXPL + SEQ_ITP):

```java
ArgBuilder<S, A, P> argBuilder = ArgBuilder.create(lts, analysis, target, true);
ArgAbstractor<S, A, P> abstractor = BasicArgAbstractor.builder(argBuilder)
        .projection(S::getLoc)                       // coverage-candidate grouping
        .waitlist(PriorityWaitlist.create(comparator))
        .stopCriterion(StopCriterions.firstCex())
        .logger(logger).build();

ArgRefiner<S, A, P> refiner = SingleExprTraceRefiner.create(
        ExprTraceSeqItpChecker.create(True(), True(), itpSolver),
        JoiningPrecRefiner.create(new ItpRefToExplPrec()),   // RefutationToPrec → PrecRefiner
        PruneStrategy.LAZY,
        logger);

SafetyChecker<ARG<S, A>, Trace<S, A>, P> checker =
        ArgCegarChecker.create(abstractor, refiner, logger);
SafetyResult<ARG<S, A>, Trace<S, A>> result = checker.check(initPrec);
```

Knobs: trace checkers (`ExprTraceSeqItpChecker`/`FwBinItp`/`BwBinItp`/`Newton`/`UCB`/`UnsatCoreChecker` — the last produces `VarsRefutation` + `VarsRefToExplPrec` instead of interpolants), `PruneStrategy.LAZY` (prune one node at the refutation index) vs `FULL` (restart the ARG), `MultiExprTraceRefiner` for multi-cex refinement, a custom `NodePruner` for POR-style pruning (see xcfa's `AtomicNodePruner`).

The same chain scales to the most complex consumer, `xcfa-cli/checkers/ConfigToCegarChecker.kt`: same five steps, same final `ArgCegarChecker.create(abstractor, refiner, logger)`, with the pieces swapped at the extension points rather than the shape changed. What it adds, in order of usefulness as a template:

- **Factories on the `Domain` enum** instead of a `switch`: `domain.abstractor(...)`, `domain.itpPrecRefiner(...)`, `domain.nodePruner` each return the domain-appropriate piece, so the assembly code is domain-agnostic.
- **A custom abstractor** (subclasses `BasicArgAbstractor`, overriding the covering policy for multithreaded stack-covering) and **`XcfaSingleExprTraceRefiner`** in place of `SingleExprTraceRefiner`.
- **Refiner decoration**: with `POR.AASPOR`, the finished refiner is wrapped — `AasporRefiner.create(refiner, pruneStrategy, ignoredVarRegistry)` — which re-expands ARG nodes whose partial-order-reduction assumptions the new precision invalidated. Orthogonal to the `NodePruner` (`AtomicNodePruner`) it also passes.
- **Result post-processing**: the `ArgCegarChecker` is wrapped in an outer `SafetyChecker` that converts the `ARG` proof into `LocationInvariants` for witness output — a clean way to present a formalism-level proof without touching the CEGAR loop.
- **Monitor registration** right after the checker is built (`MonitorCheckpoint.register(CexMonitor(...), "CegarChecker.unsafeARG")`), gated by config — see [CLAUDE.md](CLAUDE.md) on the checkpoint mechanism.

## Path B — BMC / k-induction / IMC / IC3 / MDD (reference: `sts-analysis/StsToMonolithicAdapter`)

If your model reduces to a single init/trans/prop triple, implement a `ModelToMonolithicAdapter` producing a [MonolithicExpr](src/main/java/hu/bme/mit/theta/analysis/algorithm/bounded/MonolithicExpr.kt) (`initExpr`, `transExpr`, `propExpr`, `transOffsetIndex`) plus trace/proof mapping back to your model. Then any of `BoundedChecker` (BMC/k-ind/IMC toggles), `Ic3Checker`, `MddChecker(iterationStrategy)` accepts it. The `bounded/pipeline/` passes can lower models first (liveness→safety, predicate abstraction, reversal). Adapters for sts/xsts/cfa/xcfa exist in their `-analysis` modules — copy the nearest one.

## Path C — Liveness/LTL (reference: `common/ltl/LtlChecker`)

LTL checking = product of your system with a Büchi automaton (`multi/` framework + `common/ltl`'s `Ltl2BuchiTransformer`) checked by lasso-CEGAR (`AsgCegarChecker` with `ASGAbstractor` + `SingleASGTraceRefiner`). If you already have Path A pieces, `LtlChecker` composes them.

## Consumer gotchas (all verified)

- **`Trace` invariant**: #states = #actions + 1 — constructing traces by hand fails fast otherwise.
- **`SafetyResult`**: construct only via `SafetyResult.safe(proof)` / `unsafe(cex, proof)` / `unknown()`; query via `isSafe()`/`asUnsafe().getCex()`.
- **Explicit domain**: past `maxSuccToEnumerate`, `ExplStmtTransFunc` silently returns an *approximate* (havoc-like) successor — sound, but don't expect failure on non-determinism.
- **Products**: plain `Prod2Analysis.create(a1, a2)` does **not** check joint satisfiability of component states — pass a `StrengtheningOperator` (cf. `prod2explpred`) if you need it.
- **The `Proof` handed to CEGAR is mutable shared state** — don't hold references to its parts across iterations.
- **Solvers**: abstraction and refinement should use separate solver instances (`BoundedChecker` even asserts distinctness); itp-based trace checkers need an `ItpSolver`, unsat-core ones a `UCSolver`.
- **Visualization**: wrap results with `ArgVisualizer`/`TraceVisualizer` (→ `common.visualization.Graph` → `GraphvizWriter`).
