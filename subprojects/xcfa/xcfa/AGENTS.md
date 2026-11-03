# xcfa/xcfa — notes for editing this module

Gradle module: `:theta-xcfa`. The XCFA model (procedures, locations, edges, labels), its builders, the procedure passes that lower a freshly built XCFA into what the analyses consume, and witness I/O. Input comes from [c2xcfa](../c2xcfa/AGENTS.md) (C), and from the CHC, BTOR2 and litmus frontends.

## Structure

- `model/`: `XCFA`, `XcfaProcedure`, `XcfaEdge`, `XcfaLocation`, the label hierarchy (`XcfaLabel.kt`: `InvokeLabel`, `StmtLabel`, `SequenceLabel`, `NondetLabel`, `StartLabel`/`JoinLabel`, fence and mutex labels), `Builders.kt` (`XcfaBuilder`, `XcfaProcedureBuilder`) and the Kotlin DSL (`Dsl.kt`) that tests use.
- `passes/`: one `ProcedurePass` per rewrite. `ProcedurePassManager.kt` fixes the order: `CPasses` for C, and smaller managers for the other inputs. [passes/README.md](src/main/java/hu/bme/mit/theta/xcfa/passes/README.md) explains every phase and its ordering constraints. Read it before adding or moving a pass.
- `utils/`: queries over labels and expressions (`getFlatLabels`, the `AssignStmtLabel` helpers, access, pointer and data-race utilities, `AllocationUtils`).
- `witnesses/`: GraphML and YAML witness models.

## Invariants / gotchas

1. **The passes run inside the frontend build.** `XcfaProcedureBuilder.build()` calls `optimize()`, which runs the manager's passes, and `getXcfaFromC` calls `build()`. So an exception thrown by a pass is a frontend failure ("Frontend failed!", printed after "ParsingResult Success"). After `optimize()` the builder refuses every further edit.
2. **A pass that cannot model a construct exactly must refuse it.** Never approximate. Use `check`/`error` (the convention in `CLibraryFunctionsPass`), or leave the `InvokeLabel` in place so that it fails later as "No such method …".
   - If byte addressing would make the construct exact, throw `RequiresByteAddressedMemoryException` instead. The CLI catches it and rebuilds under `--memory-model bytes` (`ExecuteConfig.frontend`). `MemoryFunctionsPass.giveUp` does this.
3. **A pass sees every memory model.** Check `parseContext.memoryModel` (`byteAddressed()`, `flat`).
   - Under `multi`/`flat`, a dereference has to be `Dereference(base, index)`. `Dereference(p + k, i)` names no object, and writes through it are silently lost. Fold `p + k` into the index the way the frontend does (`MemoryFunctionsPass.splitOffset`).
   - Under `bytes`, addresses are resolved later by `ByteMemoryPass`.
4. **Passes run in order, and some order constraints are easy to miss.** Anything that reads `&x` as a reference must run before `ReferenceElimination`. A loop emitted after `UnrollPass` stays a loop. `MemoryFunctionsPass` must precede `UnresolvedInvokeToHavocPass`, which havocs every call still left.
5. **`ProcedurePass.runChecked` asserts that every edge still runs between listed locations.** A pass that replaces an edge has to `removeEdge` the old one and add the new ones, and register any new locations or variables with `addLoc`/`addVar`.
6. **Labels are a sequence of flat labels** after `NormalizePass`. Iterate them with `getFlatLabels()` and rebuild with `SequenceLabel`. Many passes assume this shape.

## Tests

- `./gradlew :theta-xcfa:test`. `PassTests` is the table-driven pattern: build an input procedure with the DSL, run the pass, compare against the expected output. Per-pass tests (`ByteMemoryPassTest`, `LibraryStubsTest`, `NondetMemoryTest`, …) follow it.
- Verdict-level behaviour goes into an `xcfa-cli` fixture (`subprojects/xcfa/xcfa-cli/canaries/fixtures`, `:theta-xcfa-cli:fixtureTest`). A pass refusal is expected as `FRONTEND-FAIL`.
