# solver/solver-z3 — notes for editing this module

Gradle module: `:theta-solver-z3`. Backend for **modern Z3** (native libs via the Maven artifact `org.sosy-lab:javasmt-solver-z3`, version in [Deps.kt](../../../buildSrc/src/main/kotlin/Deps.kt)). Resolves as solver name **`"Z3:new"`** (deprecated alias `"Z3:4.13"`); plain `"Z3"` goes to [solver-z3-legacy](../solver-z3-legacy/CLAUDE.md). ⚠ Class names are identical to the legacy module (`Z3SolverManager`, `Z3Solver`, …) — only the package (`solver.z3`) differs.

## Structure

Standard backend skeleton (`{Decl,Expr,Term,Type}Transformer` + `Z3TransformationManager`/`Z3TermTransformer` + `Z3SymbolTable`) with two notable extras:

- **`Z3Solver` implements `Solver`, `UCSolver`, and `ItpSolver` in one class.** Modern Z3 dropped the native interpolation API, so `getInterpolant` computes **sequence interpolants as per-cut binary interpolants** via [InterpolationMetadata.java](src/main/java/hu/bme/mit/theta/solver/z3/InterpolationMetadata.java) — only sequence-shaped `Z3ItpPattern`s are supported (tree patterns throw `UnsupportedOperationException`), and the last marker's interpolant is hardwired `False()`. This routes through `:theta-solver-smtlib` (see the build.gradle comment "necessary for interpolation right now").
- **`Z3HornSolver`** — Horn/CHC support (this module, not legacy, backs `HornChecker` for native Z3).

## Invariants / gotchas

1. **Mirror obligation with solver-z3-legacy**: new core types/exprs must be taught to both modules' transformers (same-commit precedent: EnumType).
2. Interpolation here is *derived*, not native — refinement configs that assume tree interpolation must not resolve to this backend.
3. Z3 version bumps go through `Deps.kt` (artifact carries the natives) — no vendored jar to update, but check the deprecated name alias when bumping.
