# xcfa/c2xcfa — notes for editing this module

Gradle module: `:theta-c2xcfa`. Turns the C frontend's `CProgram` into an XCFA. Nearly all of it is [FrontendXcfaBuilder.kt](src/main/java/hu/bme/mit/theta/c2xcfa/FrontendXcfaBuilder.kt), a `CStatementVisitorBase<ParamPack, XcfaLocation>` over the frontend's statement tree. [Utils.kt](src/main/java/hu/bme/mit/theta/c2xcfa/Utils.kt) has the entry point `getXcfaFromC`. How C objects, cells, base ids and the three memory models are represented is in [README.md](README.md). Read it before touching assignments, initializers or pointers.

## Build and test

- `./gradlew :theta-c2xcfa:test`. Tests compile C snippets with `getXcfaFromC`. Every procedure builder gets a `CPasses` manager, so a test here exercises the frontend, this module and the C pass pipeline together. `TestFrontendXcfaBuilder` smoke-builds the numbered programs in `src/test/resources/`; add a focused `*Test.kt` for new behaviour.
- Also run `:theta-c-frontend:test` and the canary gate, `:theta-xcfa-cli:fixtureTest` and `canaryTest` ([canaries/README.md](../xcfa-cli/canaries/README.md)). A change that alters values rather than what parses needs a `SAFE`/`UNSAFE` fixture: a miswritten cell parses fine.
- Frontend-side conventions (two-pass parse, `cType` metadata, static registries): [c-frontend AGENTS.md](../../frontends/c-frontend/AGENTS.md).

## Invariants / gotchas

1. **One JVM builds the same program more than once.** The memory-model and arithmetic fallbacks and the portfolio re-parse in-process, so keep no static state in the builder. `RepeatedBuildTest` builds a program twice to guard this.
2. **Initialization writes exactly the cells that accesses read.** An array of structs is laid out inline (`a[i].f` at cell `i*unitCount + f`, see `ExpressionVisitor#rowOf`). Its initializer therefore writes each element's units in place (`initializeInlineElements` calls `initializeStructUnits`) and mints nested-aggregate bases into those cells. It never creates a separate object per element.
3. A `CAssume` with `getHavocked()` present becomes `SequenceLabel(havoc x; assume range(x))` on the declaration edge. Inlining shares the callee's variables between calls, so this havoc is what gives an uninitialized local a fresh value on every activation.
4. Re-stamp `cType` on any lvalue or expression you rebuild. Deriving the type from the SMT sort cannot tell `struct S *` from `unsigned int`.
5. Refuse rather than approximate: throw `UnsupportedFrontendElementException` for a construct that cannot be modelled exactly (see "When in doubt, refuse" in the README). Throw `UnsupportedPointerSplitException` (as this builder and `ReferenceElimination` do) only for what `flat` can express, and `RequiresByteAddressedMemoryException` only for what `bytes` can. When no memory model was requested, xcfa-cli rebuilds under that model on exactly these exceptions.
6. **Every expression that global-initialization writes go through is registered in `staticObjectBases`**, a nested struct field's cell expression too (the `storageGiven` branch). The removal of unread writes finds objects by that expression, so for an unregistered one it drops the base write but keeps the writes through it, which then land at an unknown address. `GlobalSubObjectBaseTest` guards this.
