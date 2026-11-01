# xcfa/c2xcfa — notes for editing this module

Gradle module: `:theta-c2xcfa`. Translates the [c-frontend](../../frontends/c-frontend/AGENTS.md) model into an `XcfaBuilder`. The [README](README.md) covers how C objects map to memory (cells, base ids, memory models, the refusal principle). Read it before changing anything about assignments, initialization or aggregates.

## Structure

- `Utils.kt`: `getXcfaFromC(stream, parseContext, …)` is the entry point (parse, `FunctionVisitor`, `FrontendXcfaBuilder.buildXcfa`, `build()`). `getExpressionFromC` parses a single C expression against existing variables (used for witness/invariant input).
- `FrontendXcfaBuilder.kt`: a `CStatementVisitorBase` that emits one procedure per `CFunction`. Global initialization is the first edge of `main`. Most of the code is about lvalues and aggregates: struct and array copies, bitfield writes, global initialization (`initializeGlobalVariable`, which initializes only accessed members), and stack storage (`alloca`, `allocateStackStruct` / `allocateStackArray`).
- `CMetaData.kt`: source positions attached to edges (used by witnesses).

## Invariants / gotchas

1. Library functions and intrinsics (`malloc`, `alloca`, `pthread_*`, `__VERIFIER_*`, scope ends) are emitted here as `InvokeLabel`s and resolved later by the passes in `:theta-xcfa` (`xcfa/passes`). Changing what an intrinsic means usually belongs in the pass, not here.
2. An lvalue that is not handled must fail with a message (`unhandledLhs`), not be dropped or approximated.
3. A rebuilt lvalue loses its `cType` (identity-keyed metadata; see the c-frontend notes). Re-stamp it.
4. Every memory model must keep working (`multi`, `flat`, `bytes`; `ParseContext.memoryModel`). Code that reasons about cells has to say which models it supports.

## Tests

- `./gradlew :theta-c2xcfa:test`. The usual shape is a C source string passed to `getXcfaFromC(src.byteInputStream(), ParseContext(), false, XcfaProperty(ErrorDetection.ERROR_LOCATION), NullLogger.getInstance())`, then assertions on the built XCFA's labels. See `SwitchWidthTest` for a minimal one.
- `TestFrontendXcfaBuilder` only checks that the programs in `src/test/resources` build.
- For verdict-level behaviour, add an `xcfa-cli` fixture (`:theta-xcfa-cli:fixtureTest`).
