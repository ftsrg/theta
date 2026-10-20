# Distributed Summary Synthesis (DSS)

A port of CPAchecker's distributed summary synthesis (package
`org.sosy_lab.cpachecker.core.algorithm.distributed_summaries`, ported against commit
`2749ad7234`) to Theta's XCFA. Paper: D. Beyer, M. Kettl, T. Lemberger, *Decomposing Software
Verification using Distributed Summary Synthesis*, FSE 2024. Where CPAchecker and the paper
disagree, Theta follows CPAchecker.

## Algorithm

The procedure is cut into **blocks** (one entry, one exit location); every block is analyzed by its
own actor, which talks to the others only through messages:

* a **postcondition** over-approximates the states at a block's exit and is sent to the successors,
  which use it as their precondition;
* a **violation condition** is the weakest precondition, at a block's entry, of reaching an error
  location (or a successor's violation condition) inside the block; it is sent to the predecessors,
  which try to refute it under their own preconditions.

A violation condition reported by the **root** block means UNSAFE; quiescence of the network
means SAFE. Each block is extracted into a standalone XCFA and checked by an ordinary Theta checker
(predicate CEGAR by default).

## Running

```
theta-xcfa-cli --input program.c --backend DSS [--dss-... options]
```

Only single-procedure programs and error-location reachability are supported.

| Option | Default | Meaning |
|---|---|---|
| `--dss-decomposition` | `MERGE` | `LINEAR`, `MERGE` (CPAchecker's default), `NONE` (single block), and the Theta-only `MERGE_ABSORB_SELF_LOOPS`, `MERGE_ACYCLIC`, `MIN_CUT`, `MIN_CUT_ABSORB_SELF_LOOPS`, `MIN_CUT_ACYCLIC` |
| `--dss-checker-backends` | `CEGAR` | Block checkers, as `--backend` values: `CEGAR` (predicate Cartesian), `BMC`, `KIND`, `IMC`, `KINDIMC`, `BOUNDED`; a failing checker is retried with the next one |
| `--dss-checker-selection` | `ROUND_ROBIN` | `ROUND_ROBIN`, `PRIORITY` (first entry, the others as fallbacks), `FASTEST` (per block, after trying all once) |
| `--dss-executor` | `SEQUENTIAL` | `SEQUENTIAL`, `CONCURRENT` (one thread per block, uses `Z3:new`), `PROCESS` (one worker process per block) |
| `--dss-global-predicate-pool` | `true` | Seed every block's precision with all assume conditions of the program |
| `--dss-reset-precision` | off | Start every analysis with the initial precision (CPAchecker's `resetPrecisionForEveryRun`) |
| `--dss-reuse-block-precision` | off | Add the predicates of a block's earlier CEGAR runs to its next runs |

The executor defaults to `SEQUENTIAL` because the default legacy Z3 binding crashes natively when
used by several threads. `Z3:new` is thread-safe, but its interpolation fails on some C arithmetic.
`PROCESS` runs any solver in parallel, at the price of one JVM per worker.

## Packages

* `dss.decomposition` — `Block`, `BlockGraph` and the decompositions.
* `dss.analysis` — block extraction (`extractBlockXcfa`), violation conditions
  (`computeViolationCondition`, `DssAuxVars`), postconditions, solver-backed operators,
  precisions, the checker roster.
* `dss.actor` — the actor network: `DssBlockActor` + `PredicateBlockBehavior` (CPAchecker's
  `DssBlockAnalysis`), observer, quiescence monitor, executors, witnesses.
* `xcfa-cli` — `--backend DSS` (`ConfigToDssChecker.kt`, `DssConfig`).

Checkers are injected as `(XCFA) -> XcfaChecker`, so these packages do not depend on `xcfa-cli`.

## Differences from CPAchecker

* **Standalone block programs instead of `BlockCPA`.** Theta's checkers abstract at every location,
  so a postcondition can be coarser than CPAchecker's with the same predicates. A loop head that is
  both entry and exit of a block gets separate entry and exit clones; no ghost edges are needed.
* **One counterexample instead of an ARG.** Violation conditions are computed from the block's own
  paths, covering all of its targets at once. The postcondition of an unsafe run comes from a second
  run without targets.
* **Blocks with an internal cycle** (Theta-only decompositions) get per-path violation conditions:
  the weakest precondition along each counterexample, accumulated as a disjunction.
* **Precision** is the set of atoms of the reached states plus the start precision, not
  location-specific; the start state's own atoms are always added.
* **Valid postconditions are normalized to `true`**, and non-top start states are analyzed first;
  without either, the SCC rule never applies to loop blocks.
* **A violation condition reached from top is only suppressed** if it was already reported from top;
  CPAchecker assumes this and can lose the condition (a wrong SAFE).
* **Witnesses**: correctness witnesses from the block invariants, violation witnesses stitched along
  the violation conditions. CPAchecker's DSS reports none.

## Soundness and termination

Violation conditions are exact (no abstraction), so UNSAFE is sound; bounded checkers may miss a
target but never invent one. SAFE relies on the stored preconditions covering the reachable entry
states: missing predecessors count as top, and a stored state is only replaced by a stronger one
from the same sender. As in CPAchecker, the SCC rule assumes a fixed point without checking it.

Termination is not guaranteed, in CPAchecker either: a loop block can keep refuting ever longer
violation conditions while refinement finds new predicates.

## Known limitations

* Error-location reachability only: other properties are supported when a pass rewrites them to it
  (assertions, overflow, memory safety), the rest (e.g. termination) are rejected.
* Single procedure only; labels without a weakest-precondition rule (calls, memory operations,
  fences) make the block analysis fail.
* A solver query DSS itself cannot decide gives an unknown verdict.
* Witness invariants appear only at C statements that start an XCFA edge; without every block's
  records, an UNSAFE verdict has an empty trace.
