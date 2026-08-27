# analysis/algorithm — the checker landscape

Supplements [analysis's CLAUDE.md](../../../../../../../../../CLAUDE.md) with algorithm-package detail. All claims verified against source (2026-07).

## Checkers at a glance

| Package | Algorithm | Input | Proof / Cex |
|---|---|---|---|
| [cegar/](cegar/) + [arg/](arg/) | CEGAR (abstraction refinement) | `Analysis` + `LTS` + initial `Prec` | `ARG` / `Trace` |
| [bounded/](bounded/) | BMC, k-induction, IMC (one loop, each toggleable) | `MonolithicExpr` | `PredState` (via `ExprState`→`InvariantProof`) / `Trace<ExplState,ExprAction>` |
| [ic3/](ic3/) | IC3/PDR, frames + UNSAT-core generalization | `MonolithicExpr` | `PredState` / concretized `Trace` |
| [mdd/](mdd/) | Symbolic reachability (BFS/SAT/GSAT saturation) + CTL (`mdd/ctl`) | `MonolithicExpr` | `MddProof` / `Trace`. Its API is stated in the external delta library's types (`MddProof.getMdd(): MddHandle`), so consumers import delta directly |
| [chc/](chc/) | Constrained Horn Clauses via `HornSolver` (Z3/Golem/Eldarica) | `List<Relation>` (core `ChcUtils`) | `Invariant` / `CexTree` (a derivation DAG, **not** a `Trace`) |
| [loopchecker/](loopchecker/) + [asg/](asg/) | Liveness CEGAR (lasso search: GDFS/NDFS) | `Analysis` + `LTS` + `AcceptancePredicate` | `ASG` / `ASGTrace` (lasso) |
| [oc/](oc/) | Ordering consistency for weak-memory executions | events + po/rf/ws relations | solver status + happens-before |
| [mcm/](mcm/) | Memory-model graph matching (⚠ WiP: builds the candidate-execution graph but the solving step is commented out — verdict hardcoded unsafe; no consumers) | — | — |
| [tracegeneration/](tracegeneration/) | Abstraction-only trace enumeration (no refiner, plain `Checker`) | via `BasicArgAbstractor` | `AbstractTraceSet` |

Büchi automata for liveness come from `common/ltl` (which also owns the jhoafparser dependency); `loopchecker` itself only sees an `AcceptancePredicate`.

## CEGAR mechanics (cegar/ + arg/)

- `CegarChecker` owns ONE `Proof` from `abstractor.createProof()` and hands the *same instance* to abstractor and refiner each iteration. `ArgCegarChecker` adds nothing algorithmic — it fixes `Pr=ARG`, `C=Trace` and plugs `ArgVisualizer`.
- `BasicArgAbstractor.check`: seeds a `reachedset/Partition` (keyed by the `projection` function — that's what projection is for: coverage-candidate lookup) and the `Waitlist` from `arg.getIncompleteNodes()`. Main loop: take the next node from the waitlist, try to cover it (`close` — **leaf nodes only**; `mayCoverStandard` skips ancestor checks), expand it if it wasn't covered and isn't a target, and stop when the waitlist is empty or `stopCriterion.canStop` fires. Returns safe only after `checkState(arg.isComplete())`.
- **Covering**: needs `partialOrd.isLeq(covered, coverer)`; `cover()` flattens transitive chains eagerly. Formalisms override `close` for custom policies (xcfa does, for multithreaded stack-covering).
- **`prune(node)` vs `markForReExpansion(node)`**: prune removes the subtree and clears coverage *on both sides* (descendants lose their coverer; outside nodes covered by the subtree become uncovered — picked up on the *next* `check()` via a fresh incomplete-nodes scan). markForReExpansion only clears `expanded`, keeps child edges, and `ArgBuilder.expand` skips already-explored actions.
- `StopCriterions`: `firstCex` / `fullExploration` / `atLeastNCexs(n)`, each with whole-ARG and incremental variants.
- `reachedset/` bundles two unrelated things: `Partition` (what CEGAR actually uses) and `ReachedSet` (only the cfa Impact algorithm implements it).
- **Runtime-monitor hook**: `CegarChecker` executes the checkpoint `"CegarChecker.unsafeARG"` on *every* CEGAR run, whatever the formalism — but a monitor only runs if something registered one, and today the only registration site repo-wide is `xcfa-cli/ConfigToCegarChecker.kt` (`CexMonitor`, divergence detection, gated by a config flag). So in cfa/xsts/sts runs the checkpoint fires and does nothing. Checkpoint names are a closed set declared in `MonitorCheckpoint.kt` — a new call site must add its name there or it fails loudly.

## The MonolithicExpr subsystem (bounded/, shared by ic3/ and mdd/)

`MonolithicExpr` = `initExpr`/`transExpr`/`propExpr` + `transOffsetIndex: VarIndexing` (+ `vars`, `ctrlVars` for MDD ordering). Formalisms bind via `ModelToMonolithicAdapter` implementations living in **their own** `*-analysis` modules (sts/xsts/cfa/xcfa) — not here. `bounded/pipeline/` lowers models before checking (`L2SMEPass` liveness→safety, `PredicateAbstractionMEPass`, `ReverseMEPass`, bound/stall passes); ⚠ passes keep `lateinit` state between forward/backward calls — **not reentrant**, strict alternation assumed.

`BoundedChecker` requires distinct solver instances per engine (asserted) and k-induction requires BMC enabled.

## ASG specifics (asg/ + loopchecker/)

- `ASG` permits cycles; `ASGTrace` is a lasso (tail → "honda" node → loop). `ASGNode.expanded` is write-once-true — re-expansion goes through `ASG.pruneAll()`, there is no per-node re-expansion.
- `SingleASGTraceRefiner` inspects only `traces[0]` and prunes the whole ASG on spurious — no LAZY/FULL distinction like ARG.
- Refinement strategies: `DIRECT_REFINEMENT` (default) or `BOUNDED_UNROLLING` (bound hardcoded 100, silently falls back).

## Editing recipes

- **New checking algorithm**: implement `SafetyChecker<Pr, C, Input>` (or plain `Checker`), return results only via `SafetyResult.safe/unsafe/unknown` factories. If you need a new proof structure, implement the `Proof` marker + a `ProofVisualizer` (see `utils/`).
- **New abstractor/refiner pair**: the proof is not rebuilt between iterations, so the two sides must agree on what the proof looks like after a refine — what got pruned, which nodes count as incomplete/re-expandable, which coverings survived. (Example of the contract: `SingleExprTraceRefiner` prunes so that `BasicArgAbstractor`'s next `arg.getIncompleteNodes()` scan finds exactly the work to redo.) Copy that pair's behavior as reference.
- **New formalism on BMC/IC3/MDD**: implement `ModelToMonolithicAdapter` in the formalism's `-analysis` module — see `StsToMonolithicAdapter` (simplest) or `XcfaSingleThreadToMonolithicAdapter`.
