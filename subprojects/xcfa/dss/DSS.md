# Distributed Summary Synthesis (DSS) in Theta

This document describes Theta's implementation of **distributed summary synthesis** in full:
the algorithm, every component, how to run it, how it was validated, and - in detail - where and
why it differs from the reference implementation in CPAchecker.

* Paper: D. Beyer, M. Kettl, T. Lemberger: *Decomposing Software Verification using Distributed
  Summary Synthesis*. Proc. ACM Softw. Eng. 1 (FSE), Article 59, 2024.
* Reference implementation: CPAchecker, package
  `org.sosy_lab.cpachecker.core.algorithm.distributed_summaries`, configuration
  `config/dss.properties`. The port was made against CPAchecker **4.2.2-2420-g2749ad7234**
  (commit `2749ad7234`, July 2026). Where CPAchecker and the paper disagree, Theta follows
  CPAchecker (see [CPAchecker vs. the paper](#13-cpachecker-vs-the-paper)).

Contents

1. [Overview](#1-overview)
2. [Running DSS](#2-running-dss)
3. [Concepts](#3-concepts)
4. [Architecture](#4-architecture)
5. [Decomposition (`xcfa-dss-decomposition`)](#5-decomposition-xcfa-dss-decomposition)
6. [Block-analysis building blocks (`xcfa-dss-analysis`)](#6-block-analysis-building-blocks-xcfa-dss-analysis)
7. [The block analysis (`PredicateBlockBehavior`)](#7-the-block-analysis-predicateblockbehavior)
8. [Actor runtime (`xcfa-dss-actor`)](#8-actor-runtime-xcfa-dss-actor)
9. [Soundness and termination](#9-soundness-and-termination)
10. [Theta vs. CPAchecker: component map](#10-theta-vs-cpachecker-component-map)
11. [Theta vs. CPAchecker: differences](#11-theta-vs-cpachecker-differences)
12. [Empirical comparison](#12-empirical-comparison)
13. [CPAchecker vs. the paper](#13-cpachecker-vs-the-paper)
14. [Tests](#14-tests)
15. [Known limitations](#15-known-limitations)

---

## 1. Overview

DSS splits the control-flow graph of a program into **blocks** and verifies every block on its own,
as an independent worker (actor). Workers only talk through messages:

* a **postcondition** describes the states a block can end in; it is sent *forward*, to the
  successor blocks, which use it as their **precondition**;
* a **violation condition** describes the states at a block's entry from which a specification
  violation is reachable; it is sent *backward*, to the predecessor blocks, which try to refute it
  under their own preconditions.

A violation condition that reaches the **root** block (the block containing the program entry)
cannot be refuted anymore - the program is **unsafe**. When no worker has anything left to do
(quiescence), every violation condition was refuted - the program is **safe**.

In Theta, a worker checks its block with an ordinary Theta checker (predicate-abstraction CEGAR by
default) on a small, standalone XCFA extracted from the block. DSS itself is a thin orchestration
layer around that checker.

## 2. Running DSS

```
theta-xcfa-cli --input program.c --backend DSS [--dss-... options]
```

DSS works on programs with a single XCFA procedure (the CLI rejects others).

| Option | Default | Meaning | CPAchecker counterpart |
|---|---|---|---|
| `--dss-decomposition {LINEAR,MERGE,MERGE_ABSORB_SELF_LOOPS,MERGE_ACYCLIC,MIN_CUT,MIN_CUT_ABSORB_SELF_LOOPS,MIN_CUT_ACYCLIC,NONE}` | `MERGE` | How the procedure is cut into blocks (`MERGE_ABSORB_SELF_LOOPS`: 5.4, `MERGE_ACYCLIC`: 5.5, `MIN_CUT*`: 5.6) | `decompositionType` (`MERGE_DECOMPOSITION` by default); the Theta-only ones have none |
| `--dss-target-block-count N` | `2` | Target block count of `MERGE`, `MERGE_ABSORB_SELF_LOOPS` and `MERGE_ACYCLIC` | hardcoded `2` in `DssDecompositionOptions` |
| `--dss-largest-horizontal-merge N` | `-1` | Skip a horizontal merge if more than one of its blocks has more than `N` locations (`-1`: no limit) | `largestHorizontalMerge` |
| `--dss-cut-block-count N` | `2` | Number of blocks of the `MIN_CUT*` decompositions (fewer if no valid cut has `N`) | none |
| `--dss-allow-single-block-decomposition` | off | With `MERGE` and a target of at most 1, use a single block | `allowSingleBlockDecompositionWhenMerging` |
| `--dss-reset-precision` | off | Analyze every start state with the initial precision | `resetPrecisionForEveryRun` |
| `--dss-reuse-block-precision` | off | Add the predicates a block's earlier CEGAR runs ended with to the initial precision of its next runs (11.2) | none |
| `--dss-executor {SEQUENTIAL,CONCURRENT,PROCESS}` | `SEQUENTIAL` | Actor driver; `PROCESS` analyzes every block in a worker process of its own (8.4) | `executorType` (`DSS`, i.e. concurrent, by default) |
| `--dss-max-processes N` | `0` | `PROCESS`: at most `N` worker processes (`0`: one per block); a worker serving several blocks analyzes them one at a time | none |
| `--dss-worker-heap SIZE` | same as this JVM | `PROCESS`: `-Xmx` of every worker process | none |
| `--dss-solver NAME` | `Z3` | Solver of the block checkers and of DSS's own SMT checks | the solver of the PredicateCPA (MathSAT5) |
| `--dss-solver-fallback` | off | Repeat a DSS coverage/satisfiability check that `--dss-solver` fails on (unknown result or crash) with `--dss-fallback-solver` (11.3); without it, such a failure gives an unknown verdict | none |
| `--dss-checker-solver-fallback` | off | Repeat a block checker's check that throws (e.g. Z3 `unknown` on nonlinear arithmetic) with the same checker over `--dss-fallback-solver`, before `--dss-checker-fallback` moves on (11.3) | none |
| `--dss-fallback-solver NAME` | `JavaSMT:MATHSAT5` | Solver of `--dss-solver-fallback` and `--dss-checker-solver-fallback` | none |
| `--dss-global-predicate-pool BOOL` | `true` | Seed every block's precision with all assume conditions of the program | none (similar in effect to `performInitialStaticRefinement`, see 11.4) |
| `--dss-checker-backends LIST` | `CEGAR_PRED_CART` | Checkers used for block analyses (CEGAR with a predicate domain, or bounded model checkers) | none (always the predicate CPA) |
| `--dss-checker-selection {ROUND_ROBIN,PRIORITY,FASTEST}` | `ROUND_ROBIN` | How a checker is picked from that list for every block analysis: `ROUND_ROBIN` cycles the list; `PRIORITY` always starts with the first entry and uses the others only as fallbacks, in order; `FASTEST` runs every entry on a block's first analysis, then starts that block's later analyses with the entry that finished fastest there, the others following as fallbacks in order (even without `--dss-checker-fallback`) | none |
| `--dss-checker-fallback` | off | If a block analysis's checker throws or is inconclusive, repeat the analysis with the next checker (chosen by the selection policy), at most once per list entry | none |
| `--dss-trace` | off | Log a `DSS-TRACE` line per processed message, block analysis try, and sent or received postcondition/violation condition (`pc-in`, `pc-out`, `vc-in`, `vc-out` with the formula's disjuncts, nodes, atoms and variables; `pc-dedup`, `path-vcs`; `fastest-checker` with `FASTEST` selection) | none |
| `--dss-trace-expressions` | off | `--dss-trace`, with the formula itself at the end of the `pc-*`/`vc-*` lines (`expr=...`) | none |

**Why the executor defaults to `SEQUENTIAL`.** Theta's default solver binding (`Z3`, the "legacy"
Z3 binding) crashes inside its native library when several threads use it at the same time, even
though every block analysis has its own solver context (`EXCEPTION_ACCESS_VIOLATION` in
`Native.solverAssert`). This was reproduced on every C program of section 12 with the concurrent
executor - also with the code before this port, and also with garbage collection disabled. The
newer binding (`--dss-solver Z3:new`) is safe to use concurrently, but its interpolation, which
goes through a Horn query, fails on some C arithmetic ("cannot process EXISTS quantifier"). So the
robust default is sequential with the legacy binding, and
`--dss-executor CONCURRENT --dss-solver Z3:new` gives CPAchecker's concurrent execution wherever
that solver works. `JavaSMT:MATHSAT5` (CPAchecker's solver) also crashed natively under
concurrency on Windows; `JavaSMT:Z3` has no interpolation. `--dss-executor PROCESS` runs the
blocks in parallel with any of these solvers, legacy Z3 included: every block analysis runs in a
worker process of its own, so no native solver is ever used by two threads of one process (8.4).

## 3. Concepts

The paper's running example, `while (n()) { x++; y++; } assert(x == y);`, under the linear
decomposition (Theta's block ids):

```
            L0: x := 0; y := 0
   init ----------------------------> head <-----------------------+
                                       |   |                       |
          L1: [n() == 0]               |   |  L2: [n() != 0]; x++; y++ (entry = exit = head)
   check <-----------------------------+   +-----------------------+
     |  \
     |   \  L4: [x != y]
     |    +------------> err
     |  L3: [x == y]
     +-----------> final
```

* **Block** - a part of the CFA with one entry (`initialLocation`) and one exit
  (`finalLocation`); a loop body starts and ends at the loop head. Blocks meet at boundary
  locations.
* **Block graph** - block `Y` is a successor of `X` iff `Y` starts where `X` ends. The block without
  predecessors is the **root**. Cycles are allowed: above, `L2` is its own predecessor and
  successor.
* **Postcondition** - an over-approximation of the states at the block exit, computed from the
  block's preconditions. Above, `L0` sends `x == 0 && y == 0` to `L1` and `L2`.
* **Violation condition** - a condition on the states at the block entry from which a target (an
  error location, or a successor's violation condition at the block exit) is reachable inside the
  block. `L4` sends `x != y` to `L1`, `L1` sends the weakest precondition of that through its own
  edges to `L0` and `L2`, and so on.
* **Verdict** - UNSAFE as soon as the root block reports a violation condition; SAFE when the
  network is quiescent.

## 4. Architecture

```
 xcfa-cli (ConfigToDssChecker.kt)        --backend DSS, --dss-* options
   |  decomposition -> block graph; checker roster; solver
   v
 xcfa-dss-actor        actor runtime + block analysis
   runDssActors / runDssActorsSequentially
     DssBlockActor (one per block) -- PredicateBlockBehavior (CPAchecker's DssBlockAnalysis)
     DssObserverActor, DssVisualizationActor, DssThreadMonitor
   |
   v
 xcfa-dss-analysis     block-analysis building blocks
   extractBlockXcfa, computeViolationCondition / DssAuxVars, packPostcondition,
   DssPredicateOperators, collectPreds / combinePredPrecs, collectAssumePreds,
   runWorkerConfig (solver lock and scopes), DssCheckerRoster
   |
   v
 xcfa-dss-decomposition
   Block, BlockGraph, LinearBlockDecomposition, MergeBlockDecomposition (BlockGraphMerging.kt),
   SingleBlockDecomposition, BlockGraphInstrumentation, BlockGraph.toDot()
```

`xcfa-cli` depends on the DSS modules, not the other way round: the DSS modules receive checkers
as injected factories (`CheckerFactory = (XCFA) -> XcfaChecker`).

## 5. Decomposition (`xcfa-dss-decomposition`)

### 5.1 `Block` and `BlockGraph`

`Block(id, initialLocation, finalLocation, locations, edges, predecessorIds, successorIds,
violationConditionLocation = finalLocation)` references the procedure's own `XcfaLocation`s and
`XcfaEdge`s. `isRoot` = no predecessors; `isAbstractionPossible` = a dedicated
violation-condition location exists (only after instrumentation).

`BlockGraph(blocks)` requires exactly one root. `fromBlocksWithoutEdges` wires predecessor and
successor ids by matching exits to entries (CPAchecker's `fromBlockNodesWithoutGraphInformation`).
`checkConsistency()` checks that every block contains its own entry, exit and violation-condition
locations and that the id relations are symmetric.

### 5.2 `LinearBlockDecomposition` (`LINEAR`)

A depth-first traversal from the procedure entry that cuts a block whenever an edge reaches a
**block end**: by default every location that does not have exactly one incoming and one outgoing
edge - branch points, join points and dead ends, as CPAchecker's `dss.properties` block operator
(`alwaysAtJoin`, `alwaysAtBranch`, `alwaysAtProgramExit`). Blocks are named `L0`, `L1`, ... in
traversal order. The block-end predicate is injectable (`isBlockEnd`).

### 5.3 `MergeBlockDecomposition` (`MERGE`, default)

CPAchecker's `MergeBlockNodesDecomposition` loop, starting from the linear decomposition:

```
while (blocks > target):
    horizontal pass;  if (blocks <= target) break
    vertical pass;    if (no progress in this round) break
```

* **Horizontal pass** (`horizontalMergePass`, CPAchecker's `HorizontalMergeDecomposition`): groups
  blocks with the same `(predecessors, successors, exit)` - e.g. the two arms of an `if`/`else` -
  and merges each group into one block `MH<n>`. Groups are visited in id order; the pass stops as
  soon as the target is reached. A group is skipped when more than one of its blocks has more
  locations than `largestHorizontalMerge`.
* **Vertical pass** (`verticalMergePass`, CPAchecker's `VerticalMergeDecomposition`): walks the
  id-sorted blocks once and merges a block with its only successor if that successor has only this
  predecessor, into `MV<n>`. Every block takes part in at most one merge per pass; the pass stops at
  the target.
* Merged ids keep counting across passes (`MergeIdGenerator`), and references to merged blocks are
  rewritten (CPAchecker's `MergeIDTracker`). `horizontalMerge`/`verticalMerge` repeat one kind of
  pass, like CPAchecker's standalone horizontal/vertical decompositions.
* With `allowSingleBlockDecomposition` and a target of at most one, the result is the
  `SingleBlockDecomposition`.

The default target is 2 (`DEFAULT_TARGET_BLOCK_COUNT`), CPAchecker's hardcoded value (its option
documentation speaks of "the number of functions", but the code passes 2).

### 5.4 `SelfLoopAbsorbingDecomposition` (`MERGE_ABSORB_SELF_LOOPS`, Theta-only)

`MERGE`, then every **self loop** (a block whose entry and exit are the same loop head `h`) is
merged into a neighbouring block `ML<n>` (`absorbSelfLoops`), so the loop runs inside one block
analysis instead of as postconditions and violation conditions the block keeps sending to itself:

* All self loops at `h` go into the single other block that **ends** at `h` (the block entering the
  loop; its exit `h` then yields the loop invariant as postcondition), or, if there are several,
  into the single other block that **starts** at `h` (the loop exit). A loop head with several of
  both keeps its self loop, since absorbing it would duplicate the loop.
* Absorbing an inner loop can turn the outer loop into a self loop, so `MERGE` and absorbing
  alternate until neither changes the graph.

The resulting blocks contain a whole loop, which the analysis handles with per-path violation
conditions (6.3).

### 5.5 `AcyclicMergeDecomposition` (`MERGE_ACYCLIC`, Theta-only)

`MERGE`, then every **cycle** of the block graph - a self loop or a cycle through many blocks - is
collapsed into one block `MC<n>` (`collapseCycles`), smallest strongly connected component first,
so the block graph is acyclic. A block needs one entry and one exit location, so the region of a
component grows until it has them:

* several entry locations: add the predecessor blocks outside the region;
* several exit locations (a `break`, an error inside the loop): add the successor blocks;
* the entry is also the exit: add the predecessors - a block that starts and ends at the same
  location is extracted with a split head (6.1) and could not iterate its loop.

A region without successors ends at one of its dead ends (preferably not an error location). A
region can always grow to the whole procedure, a valid single block, so collapsing terminates;
merging a region can close a new cycle through outside blocks, which a later round collapses.
`MERGE` and collapsing alternate until neither changes the graph. Collapsed regions can be coarse
(a loop with an error inside takes its exits along), and the strongly-connected-component rule of
the analysis (7.7) never applies.

### 5.6 `MinCutDecomposition` (`MIN_CUT`, `MIN_CUT_ABSORB_SELF_LOOPS`, `MIN_CUT_ACYCLIC`, Theta-only)

Cuts the procedure directly (no `LINEAR`/`MERGE` first) into `--dss-cut-block-count` blocks (default
2) with as few edges between blocks as possible and, second, block sizes as equal as possible.

* A cut is a set of **cut locations**. Each of them, and the procedure entry, starts one block:
  everything reachable from it without passing another cut location. A cut is valid if no edge falls
  into two blocks and every block reaches at most one cut location, its exit (a block reaching none
  ends at one of its dead ends, preferably not an error location). A block that returns to its own
  start therefore ends there: a self loop.
* **Cut edges** are the edges entering a cut location - control passes into another block (or a new
  run of the same block) along each of them - so their number is the cut locations' summed
  in-degree, known before the blocks are built.
* **Balance:** the smallest difference between the largest and the smallest block (in locations),
  then the smallest summed deviation from the mean.
* **Search:** branch and bound over location sets, cheapest locations first; a set is only built
  if it can still be at most as cheap as the best valid cut. It stops after
  `DEFAULT_CUT_SEARCH_BUDGET` edge visits and keeps the best cut so far (logged as "stopped at the
  budget"). If no valid cut has the requested number of blocks, fewer are tried.
* **Versions** (`CutLoopHandling`): `MIN_CUT` takes any valid cut; `MIN_CUT_ABSORB_SELF_LOOPS` takes
  the same cut, then collapses its self-loop blocks as `MERGE_ACYCLIC` does (`collapseCycles(...,
  onlySelfLoops = true)`, which can lower the block count); `MIN_CUT_ACYCLIC` only accepts cuts with an
  acyclic block graph. If no valid cut into at least two blocks exists, `MIN_CUT` returns a single
  block - e.g. on a straight-line program, which after the frontend's large-block encoding has no
  location to cut at.
* **Fallback:** when the cut of `MIN_CUT_ABSORB_SELF_LOOPS` or `MIN_CUT_ACYCLIC` is not possible (no
  acyclic cut into at least two blocks; collapsing the self loops leaves a single block) or
  computing it throws, the decomposition falls back to the `MIN_CUT` cut and logs why, so neither
  fails where `MIN_CUT` succeeds.
* The CLI logs the chosen cut (INFO, RESULT with `--dss-block-graph-stats-only`): a summary line, one
  line per cut edge, and one per block with its location count and names (the first 40); with two
  blocks they are marked "before the cut" and "after the cut".

Blocks with a whole loop inside get per-path violation conditions (6.3).

### 5.7 `SingleBlockDecomposition` (`NONE`)

One block `SB1` from the entry to the last location without outgoing edges that a breadth-first
traversal finds, as in CPAchecker.

### 5.8 `BlockGraphInstrumentation`

CPAchecker's `BlockGraphModification.instrumentCFA`: every block end with outgoing edges gets a
"ghost" `NopLabel` edge (marked with `GhostEdgeMetadata`) to a fresh location, which becomes the
block's `violationConditionLocation`; a single-block graph is left unchanged. The CLI does **not**
run it - see 11.1.

### 5.9 `BlockGraph.toDot()`

Graphviz rendering for debugging: the root has a double border, blocks with a dedicated
violation-condition location a dashed one.

## 6. Block-analysis building blocks (`xcfa-dss-analysis`)

### 6.1 `extractBlockXcfa` - a block as a standalone program

Clones the block's locations and edges into a new XCFA (necessary: an `XcfaLocation`'s edge sets
contain the edges of the whole procedure). Parameters:

* `precondition` - an `assume(precondition)` edge from a synthetic entry location to the block
  entry; `null` starts from top.
* `violationCondition` - an edge from the block exit (`exitLocation`) into an error location,
  labelled `havoc a1; ...; havoc ak; assume(vc)` where `a1..ak` are the condition's existential
  auxiliary variables (6.3). Reaching that error location means reaching the block end in a state
  satisfying the condition. The block's own error location is reused if it has one.
* `keepSpecificationTargets` - `false` clears the error flag of the block's own error locations.

If the block starts and ends at the same location (a loop body), that location gets **two clones**:
the entry clone keeps the outgoing body edges, the exit clone the incoming ones. This is
CPAchecker's `INITIAL` vs. `FINAL` block state: the block end is not reachable before the first
edge, and one analysis covers exactly one iteration. A block of `MERGE_ABSORB_SELF_LOOPS` (5.4) or
`MERGE_ACYCLIC` (5.5) or `MIN_CUT*` (5.6) may instead contain a whole loop, possibly through its exit; it is extracted as it is, so one analysis
covers every iteration.

The result also returns the two synthetic edges (`preconditionEdge`, `violationConditionEdge`),
which the per-path violation conditions (6.3) need to recognize in a counterexample.

### 6.2 `packPostcondition`

Reads a postcondition off a safe result: the disjunction of the `toExpr()` of every state that the
checker's proof (`LocationInvariants`) holds for the exit location; `False()` if there is none.

### 6.3 `computeViolationCondition` and `DssAuxVars`

The weakest existential precondition, at the block entry, of reaching one of the given targets
(`location -> condition`: `True()` for error locations, the received condition for the exit),
computed over the block's paths by memoized recursion:

| Label | Rule |
|---|---|
| `assume c` | `c && φ` |
| `x := e` | `φ[e/x]` |
| `havoc x` | `φ[a/x]` with a fresh auxiliary variable `a` |
| `skip`, `NopLabel` | `φ` |
| sequence | right-to-left composition |
| nondeterministic choice | disjunction |
| anything else (calls, memory operations, ...) | `UnsupportedOperationException` |

* From the exit, only a ghost edge is followed; a loop-body block is entered from its head exactly
  once, so blocks are acyclic for this purpose (a real cycle is reported as an error).
* **Blocks with an internal cycle** (`hasInternalCycle`, only from the Theta-only decompositions, 5.4-5.6) have
  infinitely many paths, so they get **per-path** violation conditions instead (Theta-only):
  `computePathViolationCondition` is the weakest precondition along the counterexample of the run,
  after the synthetic precondition edge. CEGAR's counterexamples use per-process copies of the
  variables (`T0::_::x`), which are renamed back via the states' `varLookup`; a condition over any
  other variable is rejected. A block sends the **disjunction of all** path conditions it found so
  far: a predecessor keeps only the last condition per sender (7.5), so one path at a time would let
  it forget the paths it already refuted, and the conditions could alternate until one repeats and
  is dropped - a wrong SAFE verdict, observed while building this.
* `(c1 && φ) || (c2 && φ)` is built as `(c1 || c2) && φ`: two branches with the same continuation
  would otherwise double the condition at every unrolling.
* **Auxiliary variables** (`DssAuxVars`) stand for the existentially quantified values of havocs.
  They are interned by `(index, type)`, and every condition is renumbered canonically (first
  occurrence = index 0), so identical conditions are structurally equal. A fresh index never occurs
  in the condition it is substituted into, so existentials are never captured.

### 6.4 `DssPredicateOperators`

The solver-backed operators of CPAchecker's distributed predicate CPA: `isUnsat(e)`
(`ProceedPredicateStateOperator.processBackward`; the root's check in
`PredicateViolationConditionOperator`) and `isLeq(a, b)`, i.e. `a => b`
(`PredicateStateCoverageOperator`). The solver is created lazily on the worker's thread, under the
same lock as checker construction.

### 6.5 Precision: `collectPreds`, `combinePredPrecs`, `getPredPrec`

* `exprs.collectPreds()` - the atoms of the expressions, without `true`/`false` and auxiliary
  variables; approximates a block's final precision (11.2).
* `combinePredPrecs(precisions)` - CPAchecker's `CombinePredicatePrecisionOperator`: the
  union, restricted to predicates over variables that occur in every precision if such a variable
  exists, otherwise the plain union.
* `getPredPrec(predicates)` - the `XcfaPrec(PtrPrec(PredPrec))` a predicate checker starts
  with.

### 6.6 `collectAssumePreds` (optional, Theta-only)

Every assume condition of the whole program; the start precision with
`--dss-global-predicate-pool`.

### 6.7 `runWorkerConfig`, solver lock and solver scopes

Runs one block XCFA through a checker built by the given factory, optionally with an initial
precision. Checker construction (which creates native solver contexts) is serialized with a global
lock; concurrent construction of legacy Z3 contexts crashed. The run happens inside a
`SolverManager.withSolverScope`: the solvers created during it belong to the scope and are
released when it ends (closed under the same lock, and no longer referenced by their solver
manager). Solver managers otherwise keep every solver until `SolverManager.closeAll()`, which
exhausted the heap after a few thousand block analyses.

### 6.8 `DssCheckerRoster`

A list of interchangeable checker factories plus a selection strategy (round-robin by default,
thread-safe). One roster is shared by all blocks of a run; every block analysis asks it for a
checker.

With `FASTEST`, the ranking is per block and kept by the block analysis: its first successful
analysis runs every checker in list order and continues with the result of the fastest one (wall
clock time). Later analyses try that checker first and the others in list order. If every checker
fails, the next analysis runs all of them again. The trace logs the choice as `fastest-checker`
(`checker=<index>`, `ms=<time per checker>`), and every `analysis` line gets `checker=<index>`.

## 7. The block analysis (`PredicateBlockBehavior`)

A port of CPAchecker's `DssBlockAnalysis`, driven like `DssAnalysisWorker.processMessage`. The
method names follow CPAchecker's.

### 7.1 State of a block

| Field | Meaning |
|---|---|
| `preconditions: senderId -> [Summary]` | received postconditions (CPAchecker's multimap); a `Summary` is a state, its precision and the SCC flag |
| `violationConditions: senderId -> [condition]` | the last violation condition of every successor |
| `relevant` | the start states the next `analyzePrecondition` analyzes |
| `containsViolationInsideBlock` | the block's own error location is reachable (set by the initial analysis) |
| `reportedFromTop` | received conditions a violation condition was already reported for from the top state |

The **top** state is `true` with the start precision (CPAchecker's most general block entry state).
`isTop` is a syntactic check; postconditions are normalized so that valid ones are `true`.

### 7.2 One analysis run

`run(start, violationCondition, keepSpecificationTargets)` extracts the block with `start` as
precondition (none for top) and the violation condition as target, and runs a checker from the
roster with the start state's precision. UNSAFE means a target is reachable. SAFE yields the
postcondition at the exit (simplified; `true` if valid) and, as the block's precision, the
predicates of all reached states plus the start precision.

### 7.3 `runInitialAnalysis` (on start-up)

Analyze from top. SAFE: send the postcondition (nothing if it is `false`). UNSAFE: set
`containsViolationInsideBlock`, send `true` as postcondition if the block has successors, and send
the violation condition of the block's own targets.

### 7.4 Receiving a postcondition: `storePrecondition` + `analyzePrecondition`

`storePrecondition`, state by state, as in CPAchecker:

* the first message of a sender is stored; all its states are relevant;
* otherwise, a new state removes the sender's stored states it implies (a refined, stronger state
  replaces older ones), is *not relevant* if a stored state of the sender implies it, and is stored;
* if nothing is relevant, the analysis stops here;
* `appendTopToRelevantIfNecessary`: if some predecessor has not reported yet, or another
  predecessor's states include top, top is relevant too, so intermediate results never
  under-approximate.

`analyzePrecondition` does nothing unless the block contains a violation or holds violation
conditions (postconditions are only needed to refute something - CPAchecker's laziness). Otherwise
it analyzes the relevant start states with all violation conditions attached and sends the new
violation condition (if any), then the postconditions.

### 7.5 Receiving a violation condition: `storeViolationCondition` + `analyzeViolationCondition`

`storeViolationCondition` replaces the sender's previous condition; the analysis stops if the
condition is unsatisfiable or equal to the previous one. `analyzeViolationCondition(sender)`
analyzes **all** stored preconditions (only top for the root; nothing for a non-root block without
preconditions) with that sender's condition attached, and sends the postconditions, then the new
violation condition.

### 7.6 The core loop (`analyzeViolationCondition(violations, checkOnlyRelevant)`)

1. Start states: the relevant ones, or all stored preconditions except those skipped by the SCC
   rules (7.7).
2. Non-top start states first (7.8); top is analyzed at most once.
3. Precision of a run: the start precision for top states and with `--dss-reset-precision`,
   otherwise the combined precision of all stored preconditions plus the start precision; always
   plus the atoms of the start state itself, and with `--dss-reuse-block-precision` the predicates
   of the block's earlier CEGAR runs (11.2).
4. SAFE run: a summary (the postcondition). UNSAFE run: a summary from a second run without targets
   (11.1), and the received violation conditions are to be propagated - except, as in CPAchecker,
   for a top start state in `analyzePrecondition` when other start states are analyzed too and the
   same condition was already reported from top (11.5).
5. If any run was UNSAFE, the new violation condition is `computeViolationCondition` over the
   block's own error locations (if `containsViolationInsideBlock`) and the received conditions at
   the exit (if they are to be propagated).

Postconditions are deduplicated before sending (a state covered by one kept before it is dropped,
CPAchecker's `deduplicateStates`) and sent in one message with the union of their precisions. The
root only reports satisfiable violation conditions; one that arrives means UNSAFE.

### 7.7 Strongly connected components

The paper does not join the initial (top) postconditions of predecessors in the same SCC, because
otherwise a loop block could never become more precise than top. CPAchecker implements this with a
flag on every summary ("computed while every predecessor had a non-trivial precondition") and skips
flagged top states once every predecessor provided a non-trivial state. Theta does the same, and
only that: non-top states are never skipped.

Theta used to extend the rule to states computed (transitively) from a top start state of a
non-root block ("derived from top", 11.5). That extension was unsound: a derived state can be the
only one that already carries the entry states a loop reaches in later iterations. On SV-COMP's
`LIN_INT/stateful_check` (a violation after four loop iterations), the block after the loop kept
only the non-derived states of the first iterations, refuted the violation condition from them, and
DSS reported SAFE. Without the extension, Cartesian abstraction (and the global predicate pool) can
produce coarse non-top summaries from top that sustain themselves around a loop, so DSS may not
terminate on such programs (e.g. `paper_true` of section 12, which took about 2 s with the
extension).

### 7.8 Start state order

CPAchecker iterates its multimap in hash order. Theta analyzes non-top states first: a top summary
first would cover, and thus deduplicate away, every other summary of the same analysis.

## 8. Actor runtime (`xcfa-dss-actor`)

### 8.1 Messages

`POST_CONDITION` (`DssPostConditionMessage`: states, precision, SCC flag),
`VIOLATION_CONDITION` (`DssViolationConditionMessage`: one, possibly disjunctive, condition),
`RESULT` (`SAFE`/`UNSAFE`), `EXCEPTION` (the `Throwable`), `STATISTIC`. Messages are in-memory
objects.

### 8.2 Inboxes

`createDssMessageQueue()` is CPAchecker's `DssDefaultQueue`: `RESULT`/`EXCEPTION`/`STATISTIC` first,
otherwise creation order. The visualization actor uses a plain FIFO queue so that it logs everything
before the final messages end its run.

### 8.3 Actors

* `DssWorker` - the loop: take a message, process it, route the answers; any `Throwable` becomes an
  `EXCEPTION` message to everyone (CPAchecker catches `Exception | Error`).
* `DssBlockActor` - one per block, routing like `DssAnalysisWorker.broadcast`: postconditions to
  the observer and the successors; violation conditions to the observer and the predecessors, or,
  from the root, `RESULT(UNSAFE)` to everyone; `RESULT`/`EXCEPTION` make it shut down and answer
  with `STATISTIC`. The analysis itself is a `DssBlockBehavior` (`PredicateBlockBehavior`, or the
  stub `EchoBlockAnalysis` used to test the runtime).
* `DssObserverActor` - waits for a `RESULT` (or an `EXCEPTION`, rethrown with its cause) and one
  `STATISTIC` per block.
* `DssVisualizationActor` - optional; logs every message it sees with a timestamp
  (`renderTextLog`, `renderAnsiColoredLog`).
* `DssThreadMonitor` - detects quiescence (all block threads waiting, all queues empty, nobody
  processing) and sends `RESULT(SAFE)`.

### 8.4 Executors

* `runDssActors` (`CONCURRENT`, CPAchecker's `MultithreadingDssExecutor`): one platform thread per
  block, plus the monitor. Its CEGAR block checkers run without CEGAR's counterexample monitor,
  whose registry (`MonitorCheckpoint`) is global and would mix up concurrent checkers.
* `runDssActorsSequentially` (`SEQUENTIAL`, CPAchecker's `SequentialDssExecutor`): one thread,
  round-robin, one message per actor per round; quiescence is "all queues empty". Actors that shut
  down discard their remaining messages.
* `runDssActorsInProcesses` (`PROCESS`, Theta-only): `runDssActors`, but every block's behavior is a
  proxy for a worker process that holds the real `PredicateBlockBehavior` and answers one request
  at a time over a loopback socket (`DssProcessExecutor.kt`). xcfa-cli starts the workers as the
  same JVM with this run's config (`-c`, like `InProcessChecker`), with the hidden
  `--dss-worker-*` settings filled in; each parses the program, checks that its block graph has the
  same fingerprint, and serves its blocks. Messages travel as text
  (`DssExprCodec`: program variables by name, `DssAuxVars` as `(index, type)`), so they must not
  refer to other declarations. A worker that dies (e.g. a native solver crash) fails its block with
  a `DssWorkerException` instead of the whole JVM. Each worker has its own checker roster, so
  `ROUND_ROBIN` cycles per worker instead of across all blocks, and its own solver statistics,
  which the main process does not collect.

### 8.5 Witnesses (Theta-only)

After the run, `getDssChecker` asks every block for its `DssBlockWitness` (`DssWitness.kt`;
`PredicateBlockBehavior.witness`, over the worker protocol for `PROCESS`, see
`DssExprCodec.writeLocation`):

* **SAFE - correctness witness.** Every safe block analysis records the states it reached at each
  original location (`extraction.originalLocations`), per start state. A block's invariants come
  from start states that cover its real entries: its stored preconditions once every predecessor
  sent one (the argument behind DSS's SAFE verdict, section 9), else its analysis from top; null
  if neither was analyzed safely. `combineInvariants` joins the blocks of each location and leaves
  a location unknown if any of them is. The result is the `DssInvariants` proof, which the YAML
  writer turns into `location_invariant`s at the C statements that start an edge (there the
  program point is the edge's source), skipping positions that also start a label inside an edge
  or whose states are unknown. Only conjuncts over variables with an unambiguous C name are kept,
  which weakens each state, so the invariants stay valid.
* **UNSAFE - violation witness.** Every block records how it computed each violation condition
  (`DssViolationRecord`): the targets and received conditions of an all-paths condition, or the
  original edges of the counterexample behind a per-path condition, saved when it is found.
  `stitchViolationPath` starts at the root's reported condition in the program's initial state
  and goes block by block: an acyclic block is followed edge by edge along its exact backward
  conditions (`findBlockRun`), a cyclic one along a saved path whose condition holds
  (`followPath`); the state reached satisfies one successor's condition, where the next block
  continues. The path becomes a trace, which the YAML writer concretizes as for any other
  backend. Without complete records, the trace is empty: UNSAFE, but without steps to show.

## 9. Soundness and termination

**UNSAFE.** Violation conditions are exact: the weakest precondition through every path of the
block (there is no abstraction in a violation condition), conjoined with the successor's
condition. A condition reported by the root is satisfiable at the program entry, so a concrete path
to the error exists. (With bounded checkers in the roster a block analysis can miss a reachable
target, but never invent one.)

**SAFE.** Quiescence means that every block's last analysis from its stored preconditions found no
target, or that its violation condition was refuted further up. This is sound as long as the
analyzed preconditions cover the reachable entry states. Missing predecessors count as top, and
stored states are only replaced by stronger states of the same sender, which keeps them covering -
with one caveat inherited from CPAchecker: the SCC rule skips top start states once non-trivial
states exist, relying on those being the
fixed point of the component. This is the paper's argument ("we can only find valid proofs if all
postconditions in the SCC reached a fixed point"); the implementation does not check it.

**Per-path violation conditions** (6.3, blocks with an internal cycle) are under-approximations:
each disjunct is the weakest precondition of one concrete path, so UNSAFE stays sound. For SAFE,
a predecessor that refutes the union `U` keeps `post ∧ U` unsatisfiable in every later run (it keeps
`U` as its target), so the block's next counterexample must start outside `U`; its path condition
is then a new disjunct, and the union grows strictly while a target stays reachable - it cannot
fall silent.

**Termination** is not guaranteed, neither in CPAchecker (section 12). A loop block can keep
receiving and refuting ever longer violation conditions while interpolation discovers new
predicates (e.g. `y >= -1`, `y >= -2`, ...). Unsafe programs whose counterexample unrolls a loop `n`
times need about `n` rounds of violation conditions through the loop. If the branches of a loop
body are separate blocks (`LINEAR`), every combination of branch choices yields its own violation
condition, which can grow exponentially; `MERGE` folds such branches into one block.

## 10. Theta vs. CPAchecker: component map

| CPAchecker (`distributed_summaries.*`) | Theta |
|---|---|
| `DistributedSummarySynthesis` | `getDssChecker` (`xcfa-cli`, `ConfigToDssChecker.kt`) |
| `decomposition.DssDecompositionOptions`, `worker.DssAnalysisOptions` | `DssConfig` (`--dss-*` options) |
| `decomposition.linear_decomposition.LinearBlockNodeDecomposition` | `LinearBlockDecomposition` |
| `decomposition.MergeBlockNodesDecomposition`, `HorizontalMergeDecomposition`, `VerticalMergeDecomposition`, `MergeIDTracker` | `MergeBlockDecomposition`, `horizontalMergePass`/`horizontalMerge`, `verticalMergePass`/`verticalMerge`, `MergeIdGenerator` |
| `decomposition.SingleBlockDecomposition` | `SingleBlockDecomposition` |
| `decomposition.graph.BlockGraph`, `BlockNode` | `BlockGraph`, `Block` |
| `decomposition.graph.BlockGraphModification` | `BlockGraphInstrumentation` (not used by the CLI, 11.1) |
| `cpa.block.BlockCPA`, `BlockState`, `BlockTransferRelation` | `extractBlockXcfa` (11.1) |
| `block_analysis.DssBlockAnalysis` | `PredicateBlockBehavior` |
| `block_analysis.DssBlockAnalyses.runAlgorithm` | `PredicateBlockBehavior.run`, `runWorkerConfig` |
| `distributed_cpa.predicate.PredicateViolationConditionOperator`, `distributed_block_cpa.BlockViolationConditionOperator` | `computeViolationCondition`, `DssAuxVars` |
| `PredicateStateCoverageOperator`, `ProceedPredicateStateOperator` | `DssPredicateOperators` |
| `CombinePredicatePrecisionOperator` | `combinePredPrecs` |
| `PredicateStateCombineViolationConditionOperator` (`combineVcsByHash`) | one disjunctive condition per message |
| `Serialize*` / `Deserialize*` operators, `ContentBuilder` / `ContentReader` | none (in-memory messages) |
| `communication.messages.*` | `DssMessage` and its subclasses |
| `communication.DssDefaultQueue` | `createDssMessageQueue` |
| `communication.infrastructure.DssMessageBroadcaster`, `DssConnection` | `DssMessageBroadcaster`, `DssConnection` |
| `worker.DssAnalysisWorker` | `DssBlockActor` + `PredicateBlockBehavior` |
| `worker.DssObserverWorker`, `DssVisualizationWorker`, `DssThreadMonitor` | `DssObserverActor`, `DssVisualizationActor`, `DssThreadMonitor` |
| `executors.MultithreadingDssExecutor`, `SequentialDssExecutor` | `runDssActors`, `runDssActorsSequentially` |

## 11. Theta vs. CPAchecker: differences

### 11.1 Architecture of the block analysis

1. **Standalone block programs instead of `BlockCPA`.** CPAchecker restricts one shared CFA to a
   block with `BlockCPA` and abstracts only at the block end (`cpa.predicate.blk.alwaysAtGivenNodes`
   set to the block's final node, on top of `predicateAnalysis-PredAbsRefiner-ABEl`). Theta's
   checkers cannot be told where to abstract (Theta's predicate CEGAR abstracts after every edge;
   large blocks are a static property of the XCFA), so every block is extracted into its own XCFA
   (`extractBlockXcfa`) and checked by an unmodified checker. Abstracting inside the block is sound,
   but a postcondition can be coarser than CPAchecker's with the same predicates.
2. **No ghost edges.** CPAchecker instruments block ends with ghost edges so that a block's
   abstraction/target location is not shared with the next block's entry, and its `BlockState`
   types separate `INITIAL` from `FINAL` at a loop head. An extracted block has private locations
   anyway, and a loop head gets separate entry and exit clones. `BlockGraphInstrumentation` exists,
   but the CLI does not run it (it would modify the input XCFA in place; CPAchecker instruments a
   copy). Consequently CPAchecker's "no abstraction possible" case (block ends at function calls)
   does not arise, and its `standardVcs=false` (witness traversal) and `trackHistory` options have
   no counterpart.
3. **One counterexample instead of an ARG.** Theta's checkers stop at the first counterexample, so
   violation conditions are computed from the block's own paths (6.3) instead of the ARG paths to
   the target states. Inside a block CPAchecker does not abstract either, so these are the same
   paths, except that CPAchecker's ARG can already omit paths that are infeasible together with the
   start state (harmless extra disjuncts in Theta, since conditions never contain the
   precondition). The checker does not say *which* target it reached, so a new condition covers the
   block's own targets (if it contains a violation) and the received conditions together.
4. **Postconditions of unsafe runs** come from a second run without targets; CPAchecker reads them
   off the same ARG.
5. **Initial analysis with a reachable target:** CPAchecker sends top if the block end was reached,
   Theta if the block has successors.
6. **Violation conditions are formulas with auxiliary variables**, not SSA path formulas (6.3);
   repeated conditions are recognized by structural equality instead of `ViolationWitness`
   equality.
7. **Messages are objects** - no serialization. Precision and the SCC flag are per message where
   CPAchecker serializes them per state (one analysis attaches the same values to all its states).

### 11.2 Precision

* A block sends the atoms of all states it reached plus its start precision instead of its
  `PredicatePrecision`; precisions are global sets of predicates, not location-specific.
* `--dss-reuse-block-precision` (Theta-specific, off by default): every analysis run builds a fresh
  checker, so a block normally re-learns by refinement what its earlier runs already found. With
  the flag, a block keeps the predicates its CEGAR runs ended with (`CegarChecker.getLastPrec`,
  reported through `XcfaLastPrecProvider`, after the last refinement, for safe and unsafe runs
  alike) and adds all of them to the initial precision of every later run of the same block.
  Bounded checkers report no precision and ignore it, so the flag only affects CEGAR runs.
* The atoms of a start state are added to the precision of the run from it. A CPAchecker state is
  an abstraction over the predicates of the precision it travels with, so they are always available
  there; in Theta the combination operator can drop them. Without this, the block-end abstraction
  forgot e.g. a loop counter's lower bound, and loop blocks unrolled their violation conditions
  forever.

### 11.3 Solvers

* Every analysis run builds a fresh checker with fresh solvers (construction serialized, solvers
  released by a solver scope); CPAchecker keeps one `PredicateCPA` per worker. DSS's own coverage
  checks use one solver per block.
* CPAchecker uses MathSAT5. Theta uses `--dss-solver` (legacy `Z3` by default) and therefore the
  sequential executor by default (section 2).
* Z3 cannot decide some of DSS's own checks on nonlinear arithmetic (`unknown`). Without
  `--dss-solver-fallback` such a check ends DSS with an unknown verdict. With it, the check is
  repeated with `--dss-fallback-solver`; if that fails too, a coverage check counts as not covered
  and a dropped violation condition is kept (both only cost work), but the root's check of its
  violation condition, which decides the verdict, still gives an unknown verdict. The default
  fallback, `JavaSMT:MATHSAT5`, is not safe for the concurrent executor (section 2).
* Most such failures are in the block checkers themselves (CEGAR's abstraction, BMC/k-induction),
  not in DSS's own checks. `--dss-checker-solver-fallback` repeats a check that throws with the same
  checker over `--dss-fallback-solver` (CEGAR: abstraction and refinement solver; bounded family:
  BMC, induction and interpolation solver); if that throws too, `--dss-checker-fallback` moves on
  to the next backend. With the Z3 -> `JavaSMT:MATHSAT5` fallback, MathSAT crashes natively
  (access violation in `msat_solve`) on some nonlinear programs after a few fallback checks; MathSAT
  alone does not crash on them. `Z3:new` as fallback does not crash there.
* `DSS solver statistics: queries=… solverFailed=… fallbackDecided=… fallbackFailed=…
  checkerFailed=… checkerFallbackDecided=… checkerFallbackFailed=…` (RESULT level) counts both
  kinds over all blocks: logged after every failure of the first solver (so a run killed by a
  timeout keeps its last counts) and once when DSS ends.
* The newer Z3 binding's Horn-based interpolation had two bugs that DSS exposed, fixed in
  `solver-z3` (`InterpolationMetadata`): a partition without constants was encoded as a quantifier
  without bound variables (rejected by Z3), and a nullary interpolant was read as a function
  interpretation. A failed Horn query now raises a descriptive error instead of a
  `NullPointerException`.

### 11.4 Theta-only features

* **Global predicate pool** (`--dss-global-predicate-pool`, on by default): all assume conditions
  of the program in every block's start precision. CPAchecker's blocks start with an empty
  precision, but its refiner uses `performInitialStaticRefinement=true` (the first refinement adds
  predicates extracted statically from the program) - similar in spirit. On the programs of
  section 12 the pool did not change any verdict; turn it off for CPAchecker's behavior.
* **Checker roster** (`--dss-checker-backends`, `--dss-checker-selection`): block analyses can use
  predicate CEGAR with the cartesian, boolean or split domain, or bounded model checkers (which
  ignore precisions and may miss targets).
* **Self-loop absorbing, acyclic and min-cut decompositions** (`--dss-decomposition
  MERGE_ABSORB_SELF_LOOPS`, `MERGE_ACYCLIC`, `MIN_CUT*`, 5.4-5.6): blocks that contain a whole loop,
  with per-path violation conditions (6.3). CPAchecker's blocks never
  contain a cycle besides the split loop head.
* **Witnesses** (8.5): correctness witnesses from the block analyses' invariants, violation
  witnesses from a path stitched along the violation conditions. CPAchecker's DSS reports none.

### 11.5 Deviations in the analysis logic

1. **Valid postconditions become `true`.** CPAchecker's canonical BDD abstractions are `true` when
   valid; Theta's packed cube disjunctions are not. Without the normalization the SCC rule never
   fired for a loop body that branches on a nondeterministic value.
2. **Start state order:** non-top first (7.8).
3. **No longer a deviation: derived-from-top states.** Theta used to skip non-top states computed
   from top like flagged top states, to stop coarse Cartesian summaries from sustaining themselves
   around a loop. It was removed because it made DSS unsound (7.7); the SCC rule is CPAchecker's
   again.
4. **"The same vc must have been sent already"** is checked, not assumed. CPAchecker's
   `analyzePrecondition` does not report a violation condition reached from the top state when
   other start states are analyzed too. That loses the condition if it arrived while the block had
   no precondition yet (then `analyzeViolationCondition` returned without analyzing anything): a
   wrong SAFE verdict, observed in Theta on two sequential loops under some message orders
   (regression test in `PredicateBlockBehaviorStepTest`). Theta
   records which received conditions were reported from top and only suppresses those.
5. **Factored disjunctions** in violation conditions (6.3).

### 11.6 Runtime

* Inbox priority uses creation sequence numbers instead of buffered deques;
  `DssPrioritizeViolationConditionQueue` is not ported.
* No `SINGLE_WORKER` executor. The sequential executor waits for the observer's `STATISTIC`
  messages instead of returning at the first `RESULT`.
* The default executor is `SEQUENTIAL` instead of CPAchecker's concurrent one (section 2).
* The visualization actor reads its inbox in arrival order (8.2); it is not wired into the CLI.
* Not ported: `AlgorithmStatus` tracking, statistics contents, block graph JSON export/import
  (`ImportDecomposition`; Theta has DOT export), `INLINING_DECOMPOSITION` and the function-call handling
  (`CallstackCPA`, `FunctionPointerCPA`, `mergeFunctionCalls`) - Theta's DSS is single-procedure.

## 12. Empirical comparison

Thirteen small C programs (SV-COMP style, `reach_error()` as specification; safe and unsafe
variants of: the paper's example, a loop with a constant bound, two sequential loops, nested loops,
a loop whose body branches on a nondeterministic value, a branch-join, and a nondeterministic
counting loop) were run through both tools on one machine, 120 s limit each.

* CPAchecker 4.2.2-2420-g2749ad7234 with `config/dss.properties` (MERGE decomposition, concurrent
  executor, MathSAT5), `sv-comp-reachability.spc`, in WSL (Ubuntu, OpenJDK 21). Its limit is CPU
  time over all threads, so its timeouts appear after 55-90 s of wall time. Times include about 5 s
  of start-up.
* Theta (this branch, `theta-xcfa-cli --backend DSS`), OpenJDK 21 on Windows. Times include about
  1 s of start-up. Theta's C frontend unrolls loops with a statically known bound (`--unroll`,
  default 1000) before DSS sees the program, so the constant-bound loops arrive loop-free with the
  default settings; `--unroll 0` keeps them.

| Program | Expected | CPAchecker | Theta default | Theta, no pool | Theta, `--unroll 0` | Theta, `--unroll 0`, no pool | Theta concurrent + `Z3:new` |
|---|---|---|---|---|---|---|---|
| `paper_true` | safe | safe 5.6 s | safe 1.4 s | safe 1.4 s | safe 1.8 s | safe 1.4 s | safe 1.5 s |
| `paper_false` | unsafe | unsafe 5.6 s | unsafe 1.4 s | unsafe 1.2 s | unsafe 1.4 s | unsafe 1.4 s | unsafe 1.7 s |
| `xy_bounded_true` | safe | timeout | safe 1.2 s | safe 1.2 s | safe 1.4 s | timeout | safe 1.2 s |
| `xy_bounded_false` | unsafe | unsafe 7.6 s | unsafe 1.1 s | unsafe 1.1 s | unsafe 3.9 s | unsafe 6.7 s | unsafe 1.1 s |
| `two_loops_true` | safe | safe 5.9 s | safe 1.3 s | safe 1.3 s | safe 1.5 s | timeout | safe 1.2 s |
| `two_loops_false` | unsafe | unsafe 6.4 s | unsafe 1.2 s | unsafe 1.2 s | unsafe 3.9 s | unsafe 3.0 s | unsafe 1.3 s |
| `nested_true` | safe | timeout | safe 1.3 s | safe 1.2 s | safe 2.3 s | timeout | safe 1.3 s |
| `nested_false` | unsafe | unsafe 9.1 s | unsafe 1.2 s | unsafe 1.1 s | timeout | unsafe 6.6 s | unsafe 1.2 s |
| `branch_body_true` | safe | safe 6.8 s | safe 1.5 s | safe 4.1 s | safe 1.5 s | safe 4.1 s | safe 1.5 s |
| `join_true` | safe | safe 5.5 s | safe 1.2 s | safe 1.2 s | safe 1.2 s | safe 1.3 s | safe 1.4 s |
| `join_false` | unsafe | unsafe 5.2 s | unsafe 1.3 s | unsafe 1.1 s | unsafe 1.2 s | unsafe 1.7 s | unsafe 1.3 s |
| `sum_true` | safe | timeout | safe 1.7 s | safe 1.4 s | safe 1.7 s | safe 1.8 s | safe 1.9 s |
| `sum_false` | unsafe | unsafe 6.0 s | unsafe 2.6 s | unsafe 2.0 s | unsafe 2.5 s | unsafe 2.0 s | error (interpolation) |
| **correct** | | **10/13** | **13/13** | **13/13** | **12/13** | **9/13** | **12/13** |

Observations:

* **No wrong verdict** in any configuration of either tool; the failures are timeouts (and one
  solver error).
* The configuration closest to CPAchecker (loops kept, no predicate pool) behaves like CPAchecker:
  it does not converge on the same safe loop programs (`xy_bounded_true`, `nested_true`) - the
  non-termination discussed in section 9 is a property of the algorithm, not of either
  implementation. The two differ on `sum_true` (CPAchecker times out) and `two_loops_true` (Theta
  times out).
* With loops kept, the global predicate pool decides convergence on three of the four safe loop
  programs; it costs one unsafe program (`nested_false`, a longer unrolling with more predicates).
* Theta's default frontend unrolling removes the constant-bound loops entirely, which is why the
  default configuration solves everything quickly; this is a property of Theta's frontend, not of
  DSS.
* Every Theta configuration with the legacy `Z3` and the concurrent executor crashes natively on
  these programs (section 2); the concurrent column therefore uses `Z3:new`, whose Horn-based
  interpolation fails on `sum_false`.

## 13. CPAchecker vs. the paper

Theta follows CPAchecker where it differs from Algorithm 3 of the paper:

* Preconditions are lists of states per sender with coverage checks, not one least upper bound of
  the most recent messages of the predecessors.
* Postconditions are recomputed lazily, only when there is something to refute.
* A violation condition is checked from every stored precondition separately.
* The SCC strategy is the summary flag (7.7), not Tarjan's algorithm.
* There are five message types instead of two, routed to predecessors, successors and an observer
  instead of being broadcast to every block.

## 14. Tests

| Module | Test class | Covers |
|---|---|---|
| decomposition | `LinearBlockDecompositionTest` | linear blocks, ids, loops |
| | `BlockGraphTest` | wiring, root, consistency |
| | `BlockGraphMergingTest` | horizontal/vertical passes, ids, single-pass and early-stop semantics, cycles |
| | `MergeBlockDecompositionTest` | target counts, merge size limit |
| | `SelfLoopAbsorbingDecompositionTest` | absorbing into the entering or the leaving block, nested loops, loop heads left alone, coverage |
| | `MinCutDecompositionTest` | cut at the loop exit, balance, more blocks than possible, the three loop handlings, fallback to `MIN_CUT`, report, search budget |
| | `AcyclicMergeDecompositionTest` | multi-block cycles with several exits (`break`, error inside the loop), nested cycles, growth over predecessors, no split-head blocks |
| | `SingleBlockDecompositionTest` | `SB1`, single-block merging, default target, instrumentation no-op |
| | `BlockGraphInstrumentationTest`, `BlockGraphDotTest` | ghost edges, DOT |
| analysis | `BlockXcfaExtractionTest` | isolation of extracted blocks |
| | `BlockAnalysisPrimitivesTest` | WP rules (assume, assign, sequence, nondet, havoc), unsupported labels, linear growth, preconditions, cleared targets, havoc of auxiliary variables, predicate operators, `collectPreds` |
| | `ViolationConditionTest` | path conditions, canonical auxiliary variables, one loop iteration per analysis, violation-condition targets, precision combination, internal cycles, per-path conditions |
| | `PostconditionPackingTest`, `WorkerConfigDelegatorTest`, `DssCheckerRosterTest` | packing, checker delegation, rosters |
| | `UndecidedQueryTest`, `CheckerSolverFallbackTest` | undecided operator queries with and without the fallback solver, checker solver fallback |
| actor | `PredicateBlockBehaviorStepTest` | every step of the block analysis: initial analysis, precondition coverage, storing violation conditions, laziness, refutation vs. propagation at the root and inside, the lost-violation-condition regression |
| | `PredicateBlockBehaviorTest`, `DiverseProgramsActorTest`, `CyclicBlockGraphAnalysisTest`, `NestedLoopActorTest`, `MergeDecompositionActorTest` | end-to-end verdicts with the sequential executor (legacy Z3 is not thread-safe) on branches, joins, loops, nested and sequential loops, merged and cyclic graphs, self-loop-absorbed, acyclic and min-cut graphs with per-path violation conditions (root and non-root loop blocks) |
| | `CheckerFallbackTest`, `ReuseBlockPrecisionTest` | `--dss-checker-fallback`, `--dss-reuse-block-precision` |
| | `DssTraceContentTest` | content fields of the trace, `expr=` last |
| | `DssActorRuntimeTest`, `SequentialDssExecutorTest`, `DssMessageBroadcasterTest`, `DssMessageQueueTest`, `DssVisualizationActorTest` | routing, termination, priorities, visualization |
| solver | `SolverScopeTest` | solver scopes own, close and nest |
| cli (in `xcfa-dss-actor`'s tests) | `XcfaCliDssTest`, `DefaultConfigsTest` | every option, the decomposition x executor grid, checker rosters, witnesses (validated with Theta's `--witness`) |

## 15. Known limitations

* Single procedure only; labels without a weakest-precondition rule (function calls, memory
  operations, fences) make the block analysis fail.
* Termination is not guaranteed (section 9); the SAFE case of `NestedLoopActorTest` is disabled
  because DSS does not terminate on it.
* Concurrent execution needs a thread-safe solver (`Z3:new`), whose interpolation does not support
  all C arithmetic.
* Block analyses abstract at every location (11.1) and rebuild their checker every time (11.3).
* Witness invariants appear only at C statements that start an XCFA edge (8.5); after large-block
  encoding, many locations have none. A violation witness needs every block's records; without
  them DSS reports UNSAFE without a trace.
