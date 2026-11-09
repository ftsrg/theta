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
| `--dss-direction` | `FORWARD` | `FORWARD`, `BACKWARD` (DSS on the reversed program), `BIDIRECTIONAL` (both at once, see [Directions](#directions)) |
| `--dss-share-invariants` | `true` | `BIDIRECTIONAL`: conjoin each direction's converged summaries to the other direction's preconditions |
| `--dss-checker-backends` | `CEGAR` | Block checkers, as `--backend` values: `CEGAR` (predicate Cartesian), `BMC`, `KIND`, `IMC`, `KINDIMC`, `BOUNDED`; a failing checker is retried with the next one. `BIDIRECTIONAL` accepts `CEGAR` only, except for the finisher of `FINISHER` |
| `--dss-checker-selection` | `PRIORITY` | `PRIORITY` (first entry, the others as fallbacks), `ROUND_ROBIN`, `FASTEST` (per block, after trying all once), `FINISHER` (the last entry runs, first, only on blocks whose postconditions no block builds on: forward the last blocks, backward the program's first ones; the others go by priority) |
| `--dss-cegar-domain` | `PRED_CART` | Domain of the `CEGAR` checkers: `PRED_CART`, or `EXPL` tracking the variables of the predicates DSS passes as precision (reported back as `v = v` atoms) |
| `--dss-interpolate-bounded-proofs` | `true` | Turn the proofs of the bounded checkers (`BMC`, `KIND`, `IMC`, ...) into invariants over the program variables, by interpolating them against the states one step from an error; otherwise (and where interpolation fails) they are path formulas over fresh, implicitly existential variables |
| `--dss-executor` | `SEQUENTIAL` | `SEQUENTIAL`, `CONCURRENT` (one thread per block, uses `Z3:new`), `PROCESS` (one worker process per block) |
| `--dss-max-parallel-blocks` | `0` | `CONCURRENT`: at most this many block analyses at a time (`0`: no limit) |
| `--dss-global-predicate-pool` | `true` | Seed every block's precision with all assume conditions of the program |
| `--dss-reset-precision` | off | Start every analysis with the initial precision (CPAchecker's `resetPrecisionForEveryRun`) |
| `--dss-reuse-block-precision` | off | Add the predicates of a block's earlier CEGAR runs to its next runs |
| `--dss-generalize-violations` | off | Before each analysis, try to refute a generalization of the received violation conditions (see [Generalized violation conditions](#generalized-violation-conditions)) |
| `--dss-generalization-gas` | `2` | Failed probes per sender and condition shape before that shape is no longer generalized |
| `--dss-conjecture-invariants` | off | Conjecture invariants where violation conditions keep drifting at a block boundary; the blocks check them, and a broken one is retracted (see [Conjectured invariants](#conjectured-invariants)). `FORWARD` or `BACKWARD`, not with `PROCESS` |
| `--dss-conjecture-gas` | `2` | Retracted conjectures per location before it gets no more |

The executor defaults to `SEQUENTIAL` because the default legacy Z3 binding crashes natively when
used by several threads. `Z3:new` is thread-safe, but its interpolation fails on some C arithmetic.
`PROCESS` runs any solver in parallel, at the price of one JVM per worker.

## Directions

**Backward** is DSS on the reversed program (`reverseProgram`, `ProgramReversal.kt`). There,
`__rev_init` leads to every error location, and the original entry is the error location (if
edges enter it, a dead-end `__rev_err` follows it instead); locations that cannot reach an error
are left out. An assignment `x := e` becomes
`assume x == e; havoc x`, and with `x` in `e`, `havoc t; assume x == e[t/x]; x := t; havoc t`.
The weakest existential precondition of a reversed label is the strongest postcondition of the
original, so:

* the reversed program's violation conditions are exact sets of states that the entry reaches;
* its postconditions over-approximate the states that can reach an error.

Labels without an exact reversal throw. The complements of the backward invariants are the SAFE
witness invariants (those over temporaries are left out), and violation paths are mapped back to
the program.

**Bidirectional** runs both networks in one run (`runDssNetworks`, `runDssNetworksSequentially`,
`runDssNetworksInProcesses`). Backward block ids are prefixed with `R.`, and the backward blocks
are the forward ones reversed (`reverseBlockGraph`), so the two share every block boundary.

* Each network reaches SAFE by its own quiescence.
* A failing network leaves the other one running.
* The first verdict wins; a contradicting one fails the run.

`DssMeetingActor` sees both networks' messages:

* **UNSAFE** where a forward and a backward violation condition intersect at one location. Their
  auxiliary variables are kept apart.
* **Certified summaries.** Postconditions carry a version number and the version of each input
  they were computed from, and cover every state those inputs reach at the exit: a block whose run
  without targets is not safe fails instead of dropping those states. Take a region of blocks that contains every predecessor of its members,
  where each member's latest postcondition was computed from inputs that cover its predecessors'
  latest ones. This region is a fixpoint, so it covers every error path's states at each location
  whose incoming blocks all belong to it.
* **SAFE** when locations where certified summaries are disjoint, together with those that cannot
  reach an error, cut every path from the entry to an error.
* **Shared invariants.** With `--dss-share-invariants`, a certified summary is sent
  (`DssRestrictionMessage`) to the other direction's blocks that start at the same location, and
  they conjoin it to their start states. The error paths stay the same, and violation conditions
  are unaffected, as they are computed from a block's own paths. A postcondition under a restriction
  is no program invariant, so such blocks report no witness invariants.

A SAFE verdict from a cut comes without invariants. The bounded block checkers are rejected here:
their summaries keep free path variables whose names recur across runs, which the intersections
above would conflate. The one exception is a bounded finisher (`FINISHER`): the meeting actor
ignores the finishing blocks' postconditions (`DssMeetingSide.uncertified`), so it certifies no
summary where they end.

## Packages

* `dss.decomposition` — `Block`, `BlockGraph` and the decompositions.
* `dss.analysis` — block extraction (`extractBlockXcfa`), violation conditions
  (`computeViolationCondition`, `DssAuxVars`), postconditions, solver-backed operators,
  precisions, the checker roster, the program reversal (`reverseProgram`, `reverseBlockGraph`).
* `dss.actor` — the actor network: `DssBlockActor` + `PredicateBlockBehavior` (CPAchecker's
  `DssBlockAnalysis`), observer, quiescence monitor, executors, witnesses, and for several
  networks `DssNetwork` and `DssMeetingActor`.
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
  the weakest precondition along each counterexample, accumulated as a disjunction `U`. A run yields
  one path, possibly a known one, so a known path triggers a run from `pre ∧ ¬U`, and a block that
  found a new path re-analyzes even an unchanged postcondition; it stops after a run without one.
* **Precision** is the set of atoms of the reached states plus the start precision, not
  location-specific; the start state's own atoms are always added.
* **Valid postconditions are normalized to `true`**, and non-top start states are analyzed first.
* **A sender's repeated postcondition is detected by its union**, not state by state: Theta's
  predicate states are not canonical, so the same entry states can arrive split differently.
* **A violation condition reached from top is always reported**, also when it was sent before: the
  predecessor replaces its stored condition with each new one, so suppressing it would lose it.
* **Witnesses**: correctness witnesses from the block invariants, violation witnesses stitched along
  the violation conditions. CPAchecker's DSS reports none. A block's states at its entry are left
  out unless it is the root or re-enters its entry: they are its preconditions, which the
  predecessors' exits cover, and a bounded checker's interpolant may leave them unconstrained.

## Soundness and termination

Violation conditions are exact (no abstraction), so UNSAFE is sound; bounded checkers may miss a
target but never invent one. SAFE relies on the stored preconditions covering the reachable entry
states. As in CPAchecker's `AlwaysReplacePreconditionHandler`, a postcondition replaces everything
stored from its sender, every analysis starts from all stored preconditions, and a predecessor that
has not sent anything yet counts as top; a block stops only when a sender repeats its states.

The meeting actor trusts only message contents: the versions of a certified region, never timing,
so its SAFE holds under every executor. A query it cannot decide disables it, never the networks.

Termination is not guaranteed, in CPAchecker either: a loop block can keep refuting ever longer
violation conditions while refinement finds new predicates.

## Generalized violation conditions

With `--dss-generalize-violations`, a block refutes the conditions a sender keeps sending one
loop iteration longer in one go, following GSpacer's global guidance (Krishnan et al., *Global
guidance for local generalization in model checking*, FMSD 2024). `ViolationGeneralizer` keeps
every sender's conditions as cubes in linear normal form, clustered by shape. When the bounds of
a shape drift, it conjectures their convex hull, widened in the direction of the drift (with the
hull's parameters eliminated by Fourier-Motzkin), or else the cube without its drifting literals.
For example, `x == -2 - k && n >= -1` for `k = 0, 1, 2` becomes `x <= -2 && n >= -1`.

A generalization may contain states that reach no error, so it is only a probe. A start state is
first analyzed against the received conditions or the generalization. If that run is SAFE, the
received conditions are refuted from that start state, and its postcondition is used. If it is
UNSAFE, the result is discarded and the exact analysis runs. A generalization is never sent,
never enters a path condition or witness, and never causes an UNSAFE verdict. Each failed probe
costs its shape gas.

This helps where the refuting block is not on the cycle that produces the conditions. Blocks on
the cycle start from their own summaries, which can be too weak to refute any generalization.

## Conjectured invariants

With `--dss-conjecture-invariants`, `DssConjectureActor` handles the cycle case. It clusters the
violation conditions arriving at each block boundary L, as `ViolationGeneralizer` does, and for a
generalization G it conjectures the invariant `!G` at L:

* The blocks starting at L conjoin `!G` to their start states, so their postconditions get
  stronger, and so do those of the blocks around the cycle.
* The blocks ending at L must not reach G at their exit. A block that does sends the weakest
  precondition of reaching it, over all its paths, to its predecessors (`DssMayViolationMessage`).
  They search for it in a separate pass from the same start states and pass it on in the same way.
* When the root reaches such a condition, a real path breaks `!G`, and the conjecture is retracted:
  every block drops it, and the blocks that assumed it analyze again. A chain longer than twice
  the number of blocks retracts it too, as does a block that cannot check it.

Nothing of this becomes a violation condition, a witness record or a verdict, so UNSAFE stays
sound. SAFE is still quiescence, now with conjectures live. Suppose a path from the entry breaks one,
and take the first block boundary where it leaves a conjectured invariant. Up to there it is a path
of the restricted program, so the stored preconditions cover it: the block ending there reaches G,
and every block before it on the path reaches the condition sent back, up to the root, which
retracts the conjecture. This needs the coordinator in the quiescence check, which only a single
network gives it (not `BIDIRECTIONAL`), and in-process blocks (not `PROCESS`). A location is
never conjectured where a block needs per-path conditions, which the may violations lack.

## Known limitations

* Error-location reachability only: other properties are supported when a pass rewrites them to it
  (assertions, overflow, memory safety), the rest (e.g. termination) are rejected.
* Single procedure only; labels without a weakest-precondition rule (calls, memory operations,
  fences) make the block analysis fail.
* A solver query DSS itself cannot decide gives an unknown verdict.
* Witness invariants appear only at C statements that start an XCFA edge; without every block's
  records, an UNSAFE verdict has an empty trace.
* `BACKWARD` and `BIDIRECTIONAL` reject a program whose labels have no exact reversal, also where
  `FORWARD` would not compute a violation condition over them.
* A SAFE verdict proven by a bidirectional cut, or by a network under restrictions or live
  conjectures, carries few or no witness invariants.
* `BACKWARD` can diverge on a safe program whose reversed loop stays a cycle of the block graph:
  the loop's postcondition, first computed from top, need not be the least fixpoint, so it admits
  every unrolling of the backward violation conditions. The tests see it with `LINEAR` and `MERGE`,
  also with `--dss-conjecture-invariants`; `BIDIRECTIONAL` may still finish by a cut.
* `BIDIRECTIONAL` takes `CEGAR` block checkers only, except for a `FINISHER`'s finisher (see
  [Directions](#directions)).
