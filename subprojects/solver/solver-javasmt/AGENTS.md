# solver/solver-javasmt — notes for editing this module

Gradle module: `:theta-solver-javasmt`. Backend multiplexer over [JavaSMT](https://github.com/sosy-lab/java-smt) — one Theta backend exposing many underlying solvers. Resolves solver names matching **`JavaSMT:<solver>`**, where `<solver>` must be a JavaSMT `Solvers` enum constant (e.g. `JavaSMT:PRINCESS`, `JavaSMT:SMTINTERPOL`, `JavaSMT:CVC5`); `JavaSMTSolverManager` instantiates via `Solvers.valueOf`. JavaSMT + per-solver artifacts are pinned together in [Deps.kt](../../../buildSrc/src/main/kotlin/Deps.kt) (`javasmt` + `javasmtDeps`, hard-coded pairs — bump them in sync).

## Structure

Standard backend skeleton (`{Decl,Expr,Term,Type}Transformer` + `JavaSMTTransformationManager`/`JavaSMTTermTransformer` + `JavaSMTSymbolTable`) plus:

- `JavaSMTSolver` (Solver/UCSolver) and `JavaSMTItpSolver` — interpolation availability depends on the *underlying* solver (SMTInterpol/Princess yes; not all).
- **`JavaSMTUserPropagator`** — the only user-propagator entry point in Theta (Z3-specific feature surfaced through JavaSMT); sole consumer is `analysis`'s `oc/UserPropagatorOcChecker`. Changing its callback signatures breaks weak-memory checking in xcfa.
- `JavaSMTSolverException` — wraps underlying-solver failures.

## Invariants / gotchas

1. **Capabilities are per-underlying-solver**, not per this module: a config that requests `JavaSMT:X` with interpolation must know X interpolates. Failures surface at factory/solve time, not at registration.
2. New core types/exprs: teach the transformers here too (fifth stack besides z3, z3-legacy, smtlib — grep precedent: EnumType).
3. JavaSMT bundles native libs per solver via the `javasmtDeps` artifacts — version drift between `javasmt` and `javasmtDeps` breaks at runtime, which is why Deps.kt hard-codes them together.
