# solver/solver-eldarica — notes for editing this module

Gradle module: `:theta-solver-eldarica`. **In-JVM Horn solver** backend: [Eldarica](https://github.com/uuverifiers/eldarica) is Scala and runs in-process (`Deps.eldarica` Maven artifact) — no external binary, unlike the Eldarica support in `solver-smtlib` (`impl/eldarica/`, which drives an installed executable).

## Structure

`EldaricaHornSolver` (Kotlin, implements `HornSolver` only — no plain `Solver`/`ItpSolver`) + the standard transformer skeleton (`{Decl,Expr,Term,Type}Transformer`, `EldaricaTransformationManager`, `EldaricaSymbolTable`, `Utils`) targeting Eldarica's Princess-based API instead of an SMT-LIB text stream.

## Invariants / gotchas

1. **No `SolverFactory`/`SolverManager` here** — `EldaricaHornSolver` is constructed directly (transformation manager + term transformer). Currently its only instantiation is its own test; production Horn solving resolves Eldarica through `solver-smtlib`'s installer route instead (status tracked in `possible-issues.md`).
2. Scala interop: the transformers build Princess/Eldarica Scala structures — Scala collection conversions live in `Utils.java`; type errors here are runtime, not compile-time, on version bumps.
3. New core types/exprs: transformers here must learn them too, but only Horn-relevant fragments matter (no bv/fp expected by Eldarica).
