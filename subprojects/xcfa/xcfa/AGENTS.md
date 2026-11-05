# xcfa/xcfa — notes for editing this module

Gradle module: `:theta-xcfa`. It contains:

- the XCFA model in `model/`: `XCFA`, the builders, the `XcfaLabel`s and the Kotlin DSL in `Dsl.kt`;
- the procedure passes in `passes/`, which normalize, lower and instrument a model;
- shared utilities (`utils/`), the witness formats (`witnesses/`) and `XcfaToC.kt`.

The formalism is described in [README.md](README.md). The C pass pipeline, phase by phase with its ordering constraints, is in [passes/README.md](src/main/java/hu/bme/mit/theta/xcfa/passes/README.md). Read it before adding or moving a pass.

## Build and test

- `./gradlew :theta-xcfa:test`. The pass tests build small XCFAs with the DSL (`passes/PassTests.kt`, `UnrollExitsTest.kt`).
- A pass that runs on C input is also exercised by `:theta-c2xcfa:test`, because its `getXcfaFromC` runs the whole `CPasses` pipeline. It must also pass the canary gate, `:theta-xcfa-cli:fixtureTest` and `canaryTest` ([canaries/README.md](../xcfa-cli/canaries/README.md)). The fixture harness runs only `--portfolio STABLE` or `--backend NONE` with fixed options, so behaviour reachable only under other flags (e.g. `--force-unroll`) needs a unit test here instead. A pass refusal is expected there as `FRONTEND-FAIL`.

## Invariants / gotchas

1. **Passes run in phases.** Each inner list of a `ProcedurePassManager` is a phase. The `XCFA` constructor runs phase *n* on every procedure before it starts phase *n+1*. `XcfaProcedureBuilder.optimize(phase)` refuses to skip a phase (`check(phase == lastOptimized + 1)`, "Wrong optimization phase!"), so a procedure builder added after phase 0 cannot join the pipeline as it stands. A pass that copies a procedure during its phase marks the copy as having completed that phase (`completeOptimizationPhaseOf`), as `ThreadResultPass` and `CloneProcedureForStaticThreadsPass` do. `InlineProceduresPass` brings each callee to the inlining phase (`procedure.optimize(inlineIndex)`) before it splices the callee in.
2. **The order of passes is part of the contract.** `CPasses` states each ordering constraint in a comment at that point, and the passes README has them in a table. A new or moved pass updates both.
3. Run passes through `ProcedurePass.runChecked`, which asserts that every edge still connects two locations of the procedure. The check is by identity: `XcfaLocation` is a data class, so an equal copy of a location does not count. A builder accepts no new elements once it is optimized.
4. **`cType` metadata is identity-keyed** (`FrontendMetadata`). A pass that rebuilds an expression must re-stamp its C type (`parseContext.metadata.create(newExpr, "cType", type)`), as `ReferenceElimination` does.
5. `InlineProceduresPass` splices the callee's own `VarDecl`s (`inlineCallSite` without `freshFrame`), so all inlined calls of a procedure share one set of locals. A value that must be fresh on every call needs an explicit havoc.
6. With a force bound, `UnrollPass` unrolls every countable loop before it forces one. A forced unroll marks the procedure `unsafeUnrollUsed`, and xcfa-cli then reports a Safe result as Unknown unless `--accept-unreliable-safe` is given.
7. **The passes run inside the frontend build** (`getXcfaFromC` calls `build()`, which runs `optimize()`), so an exception thrown by a pass is a frontend failure ("Frontend failed!", printed after "ParsingResult Success").
8. **A pass that cannot model a construct exactly must refuse it.** Never approximate. Use `check`/`error` (the convention in `CLibraryFunctionsPass`), or leave the `InvokeLabel` in place so that it fails later as "No such method …". The one exception is a sound over-approximation that calls `XcfaProcedureBuilder.setOverApproximation()`: xcfa-cli then reports an Unsafe result as Unknown (`FpFunctionsToExprsPass` does this for math functions such as `exp` and `sin`). If byte addressing would make the construct exact, throw `RequiresByteAddressedMemoryException` instead: the CLI rebuilds under `--memory-model bytes` (`MemoryFunctionsPass.giveUp` does this).
9. **A pass sees every memory model** (`parseContext.memoryModel`). Under `multi`/`flat`, a dereference has to be `Dereference(base, index)`: `Dereference(p + k, i)` names no object, and writes through it are silently lost. Fold `p + k` into the index the way `MemoryFunctionsPass.splitOffset` does. Under `bytes`, addresses are resolved later by `ByteMemoryPass`.
10. **Labels are a sequence of flat labels** after `NormalizePass`. Iterate them with `getFlatLabels()` and rebuild with `SequenceLabel`.
