This project contains the analysis algorithms and their components, e.g., abstract domains, abstract
reachability graphs, refinement strategies, precisions, etc. The formalism specific components (
e.g., the interpreter) are implemented in separate projects for the given formalism.

## Building blocks

Theta separates *what* is verified from *how*. A formalism (CFA, XCFA, XSTS, ...) provides:

* **States** and **actions**: abstract states of the system, and the transitions leaving them (the
  `LTS` interface answers "which actions are enabled in this state").
* An **analysis**: an abstract domain binding for the formalism, consisting of an initial-state
  function, a transfer function (successor computation), and a partial order over abstract states
  (used for coverage checks).
* A **precision** describing how fine the abstraction currently is (e.g., which variables or
  predicates are tracked).

The generic abstract domains live here: **explicit-value** (`expl`), **predicate** (`pred`, with
Cartesian/Boolean/split abstraction variants), their **products** (`prod2`), and **zones** (for
timed systems). Actions bridge to the SMT world by exposing their semantics as a first-order
formula (`ExprAction`).

## CEGAR

The main safety-checking algorithm is counterexample-guided abstraction refinement, implemented as
a loop of two generic components:

* The **abstractor** builds a *proof* of safety at the current precision. The default proof
  structure is an **abstract reachability graph (ARG)**: nodes are abstract states, edges are
  actions, and already-covered states are not re-expanded. The search order (BFS/DFS/error-distance)
  and the stopping criterion are configurable.
* If the proof contains an abstract counterexample, the **refiner** checks whether it is feasible in
  the concrete system, by unfolding the trace into an SMT formula and checking satisfiability. A
  feasible counterexample means the system is unsafe. An infeasible one yields a *refutation* (from
  sequence/binary interpolation, unsat cores, or Newton-style reasoning), which is mapped back into
  a refined precision; the affected part of the proof is then pruned and re-explored.

The loop terminates with either a proof of safety or a concrete counterexample trace. The CEGAR loop
is parametrized over the proof structure rather than hard-wired to ARGs, so the same loop also drives
other proof representations (e.g., abstract state graphs for liveness checking).

The user-facing configuration options of the CEGAR algorithms (domains, refinement strategies, search
orders, and best practices) are documented in [CEGAR-algorithms.md](../../../doc/CEGAR-algorithms.md).

## Beyond CEGAR

This project also implements other checking algorithms, selectable in the tools where applicable:

* **Bounded model checking** variants (BMC, k-induction, IMC) in `algorithm/bounded`.
* **Symbolic (decision-diagram) model checking** in `algorithm/mdd`.
* **IC3/PDR** in `algorithm/ic3`.
* **Liveness/LTL checking** in `algorithm/loopchecker` (abstract state graphs).
* **Memory-model-aware analyses** (`algorithm/mcm`, `algorithm/oc`) for weak-memory concurrency.
