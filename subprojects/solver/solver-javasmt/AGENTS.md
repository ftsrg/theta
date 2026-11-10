# solver/solver-javasmt — notes for editing this module

Gradle module: `:theta-solver-javasmt`. Backend multiplexer over [JavaSMT](https://github.com/sosy-lab/java-smt) — one Theta backend exposing many underlying solvers. Resolves solver names matching **`JavaSMT:<solver>`**, where `<solver>` must be a JavaSMT `Solvers` enum constant (e.g. `JavaSMT:PRINCESS`, `JavaSMT:SMTINTERPOL`, `JavaSMT:CVC5`); `JavaSMTSolverManager` instantiates via `Solvers.valueOf`. JavaSMT + per-solver artifacts are pinned together in [Deps.kt](../../../buildSrc/src/main/kotlin/Deps.kt) (`javasmt` + `javasmtDeps`, hard-coded pairs — bump them in sync).

## Structure

Standard backend skeleton (`{Decl,Expr,Term,Type}Transformer` + `JavaSMTTransformationManager`/`JavaSMTTermTransformer` + `JavaSMTSymbolTable`) plus:

- `JavaSMTSolver` (Solver/UCSolver) and `JavaSMTItpSolver` — interpolation availability depends on the *underlying* solver (SMTInterpol/Princess yes; not all).
- **`JavaSMTUserPropagator`** — the only backend implementing `SolverFactory.createSolverWithPropagators` (Z3 through JavaSMT): adapts a solver-agnostic `UserPropagator` to JavaSMT's propagator interface. Its sole consumer is `analysis`'s `oc/UserPropagatorOcChecker`, which `xcfa-analysis` gives a JavaSMT Z3 factory.
- `JavaSMTSolverException` — wraps underlying-solver failures.

## Invariants / gotchas

1. **Capabilities are per-underlying-solver**, not per this module: a config that requests `JavaSMT:X` with interpolation must know X interpolates. Failures surface at factory/solve time, not at registration.
2. New core types/exprs: teach the transformers here too (fifth stack besides z3, z3-legacy, smtlib — grep precedent: EnumType).
3. JavaSMT bundles native libs per solver via the `javasmtDeps` artifacts — version drift between `javasmt` and `javasmtDeps` breaks at runtime, which is why Deps.kt hard-codes them together.
4. JavaSMT's FP mantissa size excludes the hidden bit, Theta's `FpType` significand includes it: build sorts with `getFloatingPointTypeFromSizesWithoutHiddenBit(e, getSignificand() - 1)`, read them back with `getMantissaSizeWithoutHiddenBit() + 1`. Term printing differs per solver (Z3 `(_ extract 5 2)`, MathSAT `bvextract_5_2_8`), so a read-back that parses `term.toString()` needs every solver's form (`EXTRACT_INDICES` covers both); the Z3-based round-trip test does not catch MathSAT-only breaks (see `JavaSMTMathsatTransformerTest`).
5. Interpolating solvers get their own options (`JavaSMTSolverFactory.create(solver, args, interpolationOptions)`, set through the configuration builder, as `fromCmdLineArguments` rejects values containing `=`). MathSAT's gets `theory.fp.mode=2`: its default, eager FP solver produces no proofs, so it fails every interpolation over floats ("eager fp solver does not support proof generation"); see `testFpInterpolation`.
