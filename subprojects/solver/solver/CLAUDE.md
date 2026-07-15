# solver/solver — notes for editing this module

Gradle module: `:theta-solver`. This is the **interface-only layer** — no backend code lives here. 26 other modules depend on it; the backends implementing it are `solver-z3-legacy`, `solver-z3`, `solver-javasmt`, `solver-smtlib`, `solver-eldarica`.

## Invariants

1. **Extending the solver interfaces — two failure modes, pick consciously.** An *abstract* method on `Solver`/`SolverBase`/`UCSolver`/`ItpSolver` is a compile error in every implementor (the five backends, [impl/NullSolver.java](src/main/java/hu/bme/mit/theta/solver/impl/NullSolver.java), the [validator/](src/main/java/hu/bme/mit/theta/solver/validator/) wrappers) — loud, and the compiler enumerates the work. A *default* method breaks nothing at compile time, which is its own hazard: backends silently "support" the method via a possibly-throwing fallback (the `SolverFactory.createHornSolver()` pattern — fine when opt-in is the intent), and the validator wrappers delegate method-by-method, so they won't forward a new default unless updated by hand.
2. **`SolverManager` keeps a static global registry** (`registerSolverManager`/`resolveSolverFactory`/`closeAll`). Registration is the CLIs' job at startup; anything long-running or test-shaped must `closeAll()` or leak native handles. Two backends both name their manager `Z3SolverManager` — `solver.z3legacy` vs `solver.z3` packages — so resolution strings and imports, not class names, distinguish them.
3. **`getModel()` is only valid after `check()` returned SAT** (documented contract; backends may throw or return garbage otherwise).
4. **`ItpPattern` is a tree** (`ItpMarkerTree`); `createBinPattern(A, B)` and `createSeqPattern(list)` are conveniences that fold into the tree form. Backend interpolation code consumes the tree — new pattern shapes must keep that folding consistent.
5. `Stack<T>` (with [impl/StackImpl.java](src/main/java/hu/bme/mit/theta/solver/impl/StackImpl.java)) is the push/pop bookkeeping helper backends use to mirror assertion scopes — keep its semantics aligned with `SolverBase.push/pop`.

## Change recipes

- **New backend**: implement `SolverFactory` (+ `Solver`, and `UCSolver`/`ItpSolver`/`HornSolver` as supported) and a `SolverManager` subclass; register it from the CLIs' solver-registration utilities (e.g. `xcfa-cli/utils/SolverRegistration.kt`). Internally every existing backend follows an `{Expr,Term,Type}Transformer` structure — copy the nearest one.
- **New expression/type in core** ripples here indirectly: every backend's transformers must learn it (verified precedent: the EnumType addition touched all four solver stacks — see `common/core`'s CLAUDE.md).
- [validator/](src/main/java/hu/bme/mit/theta/solver/validator/) wraps a real solver behind the same interfaces for cross-checking — keep wrappers in sync when interfaces change (they don't inherit defaults usefully).

## Package map

- root — `SolverBase` (check/push/pop/reset, `AutoCloseable`), `Solver` (add/getModel), `UCSolver` (track/getUnsatCore), `ItpSolver` (markers + patterns + `getInterpolant`), `HornSolver` (`add(Relation)`, `getProof(): ProofNode`, default `interpolate`), `SolverFactory`, `SolverManager`, `SolverPool`, `SolverStatus` (SAT/UNSAT), `Interpolant`, `ItpMarker`/`ItpPattern`/`ItpMarkerTree`, `ProofNode`, `UnknownSolverStatusException`.
- [utils/](src/main/java/hu/bme/mit/theta/solver/utils/) — `WithPushPop` (try-with-resources push/pop scope), `SolverUtils` (`entails`, model streaming).
- [impl/](src/main/java/hu/bme/mit/theta/solver/impl/) — `NullSolver`, `StackImpl`. [validator/](src/main/java/hu/bme/mit/theta/solver/validator/) — validating wrappers.
