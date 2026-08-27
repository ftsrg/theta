# Using theta-solver — getting and driving SMT solvers

Consumer-facing counterpart of [CLAUDE.md](CLAUDE.md). For *building the expressions* you feed solvers, see [core USING.md](../../common/core/USING.md) (especially the `PathUtils.unfold` round-trip — solvers only see constants, never `VarDecl`s).

```kotlin
implementation(project(":theta-solver"))            // interfaces
runtimeOnly(project(":theta-solver-z3-legacy"))     // ...plus at least one backend
```

## Getting a solver

Two routes, both verified in production code:

```java
// 1. Direct factory (tests, single-backend tools):
Solver solver = Z3LegacySolverFactory.getInstance().createSolver();

// 2. Name-based via the manager registry (CLIs, user-configurable tools):
SolverManager.registerSolverManager(Z3SolverManager.create());   // once, at startup
SolverFactory factory = SolverManager.resolveSolverFactory("Z3");
```

Native backends (z3, z3-legacy) need `LD_LIBRARY_PATH=<repo>/lib/`. Call `SolverManager.closeAll()` when done — the registry is static. ⚠ Both Z3 backends name their manager `Z3SolverManager`; they differ only in package (`solver.z3legacy` vs `solver.z3`).

Backend cheat-sheet (resolution strings verified): **`"Z3"`** → solver-z3-legacy — the historical default, native, tree-capable interpolation. **`"Z3:new"`** → solver-z3 — modern Z3; sequence-only (derived) interpolation, plus Horn. **`"JavaSMT:<SOLVER>"`** (a JavaSMT `Solvers` enum name, e.g. `JavaSMT:PRINCESS`) → solver-javasmt — many solvers behind one API; capabilities depend on the underlying solver. **`"<name>:<version>"`** (e.g. `mathsat:5.6.10`, `golem:latest`) → solver-smtlib — external processes installed under `~/.theta` via `theta-solver-smtlib-cli`; per-solver capability/interpolation matrix in [solver-smtlib's CLAUDE.md](../solver-smtlib/CLAUDE.md). **solver-eldarica** — in-JVM Horn solver (no factory; constructed directly).

## Basic satisfiability

```java
solver.add(PathUtils.unfold(phi, 0));
if (solver.check().isSat()) {                 // SolverStatus: isSat()/isUnsat()
    Valuation model = solver.getModel();      // ⚠ only valid after a SAT check()
}
```

Scoped assertions — prefer the try-with-resources helper over manual push/pop:

```java
try (var wpp = new WithPushPop(solver)) {
    solver.add(extraAssertion);
    ... solver.check() ...
}                                             // pops automatically
// One-liner entailment: SolverUtils.entails(solver, antecedent, consequent)
```

Solvers are `AutoCloseable`; `reset()` clears all state. `NullSolver` is the no-op stand-in.

## Unsat cores — `UCSolver`

`factory.createUCSolver()`; use `track(expr)` instead of `add(expr)`, then after an UNSAT `check()`: `getUnsatCore()` returns the tracked exprs responsible. (This backs `--refinement UNSAT_CORE` / Newton / UCB.)

## Interpolation — `ItpSolver`

```java
ItpSolver solver = factory.createItpSolver();
ItpMarker A = solver.createMarker();
ItpMarker B = solver.createMarker();
ItpPattern pattern = solver.createBinPattern(A, B);
solver.add(A, exprA);
solver.add(B, exprB);
if (solver.check().isUnsat()) {
    Expr<BoolType> itp = solver.getInterpolant(pattern).eval(A);
}
```

Sequence (`createSeqPattern(markers)`) and tree patterns generalize this — that's what `ExprTraceSeqItpChecker` & co. use. Not every backend interpolates (notably not over bitvectors/FP with Z3 — see [doc/CEGAR-algorithms.md](../../../doc/CEGAR-algorithms.md)).

## Horn clauses — `HornSolver`

`factory.createHornSolver()` (throws on unsupported backends). `add(Relation)` (core `ChcUtils` types), `check()`; SAT → `getModel()` holds relation interpretations (the safety invariant), UNSAT → `getProof(): ProofNode` is the counterexample **derivation DAG** (not a linear trace). Used by `analysis`'s `HornChecker`.

## Many short-lived solvers — `SolverPool`

`new SolverPool(factory)` hands out and recycles solver instances (`requestSolver()`/return); used by MddChecker's expression-node enumeration where thousands of small queries occur. `ClosingMode.ALL` (default) closes everything on pool close.

## Debugging a suspect backend

`validator/SolverValidatorWrapperFactory` wraps a named backend so results can be cross-checked; `UnknownSolverStatusException` is what backends throw when the underlying tool answers "unknown".

## The interpolation idiom in one place

For a full worked CEGAR example of ItpSolver + markers + refutations, read `analysis`'s [ExprTraceFwBinItpChecker](../../common/analysis/src/main/java/hu/bme/mit/theta/analysis/expr/refinement/ExprTraceFwBinItpChecker.java) — it's the reference consumer.
