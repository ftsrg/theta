# solver/solver-z3-legacy — notes for editing this module

Gradle module: `:theta-solver-z3-legacy`. Backend for the **interpolating legacy Z3** shipped as a checked-in jar ([lib/com.microsoft.z3legacy.jar](../../../lib/) via `Deps.z3legacy`) + native libs from `lib/` (`LD_LIBRARY_PATH`). Resolves as solver name **`"Z3"`** in `SolverManager` — it is the historical default; the modern backend is [solver-z3](../solver-z3/CLAUDE.md) (`"Z3:new"`). ⚠ Both modules name classes identically (`Z3SolverManager`, `Z3Solver`, …) — packages `solver.z3legacy` vs `solver.z3` are the only distinction; check imports before editing.

## Structure (the standard backend skeleton)

`{Decl,Expr,Term,Type}Transformer` + `Z3TransformationManager` (Theta→Z3 AST) and `Z3TermTransformer` (Z3→Theta, model extraction) + `Z3SymbolTable`/`Z3TypeSymbolTable` + `Z3Solver` (Solver+UCSolver) + **`Z3ItpSolver`** (native Z3 interpolation API — the reason this backend still exists) + `Z3LegacySolverFactory` + `Z3SolverManager`.

## Invariants / gotchas

1. **This is the most-consumed backend in the repo** (18 modules, mostly as the test/default solver via `Z3LegacySolverFactory.getInstance()`). Behavior changes here move every test suite.
2. **New core types/exprs must be taught to the transformers here AND in solver-z3** — the two modules mirror each other; historically they were updated in the same commits (e.g. the EnumType addition). Don't fix one and forget the other.
3. The legacy jar is pinned/vendored — no version bumps; if the native lib and jar drift apart, everything breaks at load time.
4. Native context/solver objects are manually managed — leaked contexts = leaked native memory; factories/tests must close solvers.
