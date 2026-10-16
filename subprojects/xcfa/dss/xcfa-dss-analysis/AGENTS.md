# xcfa-dss-analysis

Building blocks of one DSS block analysis: extracting a block as a standalone XCFA, violation
conditions, postconditions, solver-backed operators, precisions, and running an injected checker.
The design and its CPAchecker counterparts are in `doc/DSS.md` (sections 6, 9, 11); read the
relevant section before changing behavior.

## Build and test
- `./gradlew :theta-xcfa-dss-analysis:test`
- Tests use real Z3 (`theta-solver-z3`) and `xcfa-cli` checkers, so they need the native libraries
  (`lib/` on the library path, as for every Theta solver test).

## Invariants
- **No dependency on `xcfa-cli`** in production code: `xcfa-cli` depends on this module for
  `--backend DSS`. Checkers arrive as `CheckerFactory = (XCFA) -> XcfaChecker`; only tests may use
  `xcfa-cli` (see `build.gradle.kts`).
- **Native solver construction is serialized**: build checkers and solvers inside
  `withSolverConstructionLock`, and run them inside `runWorkerConfig`, whose solver scope releases
  them afterwards. Solvers created outside a scope stay referenced until `SolverManager.closeAll()`,
  which exhausts the heap after a few thousand block analyses.
- **Violation conditions are exact** (weakest preconditions, no abstraction); a per-path condition
  may under-approximate but must never over-approximate (`doc/DSS.md` section 9).
- **Auxiliary variables are canonical**: every violation condition goes through
  `DssAuxVars.canonicalize`. The actor module recognizes repeated conditions by structural
  equality, so a new way to build a condition that skips it breaks deduplication silently.
- **Undecided solver queries fail loudly**: `DssPredicateOperators.isUnsat` must throw
  `DssUndecidedQueryException` when neither solver decides, never answer "sat" or "unsat" by
  default; `isKnownUnsat` may treat undecided as "not unsat".
- Checker-selection strategies index factories by list position, not by value (lambdas have no
  structural equality), and must be thread-safe: one roster is shared by all blocks of a run.

## Change recipes
- **New label kind in a block**: add its `wep` rule in `ViolationConditions.kt`
  and a case in `BlockAnalysisPrimitivesTest`; labels without a rule must keep failing explicitly.
- **New solver fallback or operator**: keep the statistics in `DssSolverStatistics` in sync, as
  the CLI prints them (`DSS solver statistics:`).
- **New `--dss-*` option**: the flag lives in `xcfa-cli` (`XcfaConfig.kt`, wired in
  `ConfigToDssChecker.kt`); add it to the option table of `doc/DSS.md` and to `XcfaCliDssTest`.

## Integration points
- Used by `xcfa-dss-actor` (`PredicateBlockBehavior`) and wired by `xcfa-cli`
  (`ConfigToDssChecker.kt`).
- Consumes `xcfa-dss-decomposition` (`Block`, `BlockGraph`).
