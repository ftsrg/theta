# Algorithms

!!! abstract
    This page gives an architectural overview of the analysis algorithms implemented in [`subprojects/common/analysis`](https://github.com/ftsrg/theta/tree/master/subprojects/common/analysis). For the configuration options of the CEGAR-based tools (abstract domains, refinement strategies, best practices), see the [CEGAR algorithms guide](https://github.com/ftsrg/theta/blob/master/doc/CEGAR-algorithms.md).

## Building blocks

Theta separates *what* is verified from *how*. A formalism (CFA, XCFA, XSTS, ...) provides:

* **States** and **actions**: abstract states of the system, and the transitions leaving them (the `LTS` interface answers "which actions are enabled in this state").
* An **analysis**: an abstract domain binding for the formalism, consisting of an initial-state function, a transfer function (successor computation), and a partial order over abstract states (for coverage checks).
* A **precision** describing how fine the abstraction currently is (e.g., which variables or predicates are tracked).

The generic abstract domains live in `common/analysis`: **explicit-value** (`expl`), **predicate** (`pred`, with Cartesian/Boolean/split abstraction variants), their **products** (`prod2`/`prod3`/`prod4`), and **zones** (for timed systems). Actions bridge to the SMT world by exposing their semantics as a first-order formula (`ExprAction`).

## CEGAR

The main safety-checking algorithm is counterexample-guided abstraction refinement, implemented as a loop of two generic components:

* The **abstractor** builds a *proof* of safety at the current precision. The default proof structure is an **abstract reachability graph (ARG)**: nodes are abstract states, edges are actions, and already-covered states are not re-expanded. The search order (BFS/DFS/error-distance) and stopping criterion are configurable.
* If the proof contains an abstract counterexample, the **refiner** checks whether it is feasible in the concrete system — typically by unfolding the trace into an SMT formula and checking satisfiability. A feasible counterexample means the system is unsafe. An infeasible one yields a *refutation* (e.g., from sequence/binary interpolation, unsat cores, or Newton-style reasoning), which is mapped back into a refined precision, and the affected part of the proof is pruned and re-explored.

The loop terminates with either a proof of safety or a concrete counterexample trace. Since the proof structure is generic (the CEGAR loop is parametrized over it, not hard-wired to ARGs), the same loop also drives other proof representations (e.g., abstract state graphs for liveness checking).

## Beyond CEGAR

`common/analysis` also implements other checking algorithms, selectable in the tools where applicable:

* **Bounded model checking** variants (BMC, k-induction, IMC) in `algorithm/bounded`.
* **Symbolic (decision-diagram) model checking** in `algorithm/mdd`.
* **IC3/PDR** in `algorithm/ic3`.
* **Liveness/LTL checking** in `algorithm/loopchecker` (abstract state graphs).
* **Memory-model-aware analyses** (`algorithm/mcm`, `algorithm/oc`) for weak-memory concurrency.

!!! info
    Written 2026-07 based on the current source; if you extend the algorithms, please keep this page in sync.
