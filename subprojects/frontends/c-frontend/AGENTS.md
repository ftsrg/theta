# frontends/c-frontend — notes for editing this module

Gradle module: `:theta-c-frontend`. Parses preprocessed C with ANTLR into the *IM* (a `CStatement` tree plus a C type model), which [c2xcfa](../../xcfa/c2xcfa/README.md) turns into an XCFA. Pipeline overview: [README.md](README.md) and [transformation/Readme.md](src/main/java/hu/bme/mit/theta/frontend/transformation/Readme.md).

## Build and test

- `./gradlew :theta-c-frontend:test` covers the type model, object layouts and the typedef-aware parse ([src/test/kotlin/hu/bme/mit/theta/frontend/](src/test/kotlin/hu/bme/mit/theta/frontend/)). Most frontend behaviour is tested from `./gradlew :theta-c2xcfa:test` (e.g. `CLiteralTypingTest`, `ShortCircuitTest`), whose `getXcfaFromC` parses, builds and runs the C pass pipeline. Run both.
- Grammar and visitor changes must also pass `:theta-xcfa-cli:fixtureTest` and `canaryTest`, with a new fixture that fails before the change and passes after ([canaries/README.md](../../xcfa/xcfa-cli/canaries/README.md)).

## Layout

Paths below are relative to [src/main/java/hu/bme/mit/theta/frontend/](src/main/java/hu/bme/mit/theta/frontend/).

- [C.g4](src/main/antlr/C.g4) — the grammar, generated into `hu.bme.mit.theta.c.frontend.dsl.gen` (ANTLR runs with `-Werror`).
- `transformation/grammar/` — the visitors: `function/FunctionVisitor` (statements; entry point `visitCompilationUnit`), `expression/ExpressionVisitor`, `type/TypeVisitor` and `DeclarationVisitor`, `preprocess/` (typedefs, globals reachable from `main`, arithmetic traits), and `CParseUtils.kt` (`parseTypeAware`).
- `transformation/model/` — the IM: `statements/` (`CStatementVisitor` plus one class per statement), `types/simple/` (declared specifiers such as `Struct`, `Enum`, `NamedType`; `getActualType()` resolves them), `types/complex/` (the resolved `CComplexType`s: integers, reals, `CPointer`, `CArray`, `CStruct`, object layouts).
- [ParseContext.java](src/main/java/hu/bme/mit/theta/frontend/ParseContext.java) — per-build settings (architecture, arithmetic, memory model) and the `FrontendMetadata`. `stdlib/` holds the built-in contents of the supported `#include <...>` headers.

## Invariants / gotchas

1. **Parsing is two-pass.** `parseTypeAware` first harvests typedef names with a permissive, error-tolerant parse, then parses with `BailErrorStrategy`, accepting only those names as types. There is deliberately no permissive fallback. Never run the frontend's visitors in the first pass: they register struct tags and write `cType` metadata.
2. **An expression's C type is metadata, not part of the `Expr`.** It is stored under `"cType"` in `ParseContext.getMetadata()`, keyed by object identity. `CComplexType.getType(expr, ctx)` falls back to a type derived from the SMT sort when it is missing, so stamp every expression you build from a typed one (`metadata.create(newExpr, "cType", type)`).
3. **Static registries are per build.** `Struct` (tag registry), `Enum` (constants) and `FunctionIds` are static and are reset in `FunctionVisitor.visitCompilationUnit`, because one JVM can build the same input several times (the memory-model and arithmetic fallbacks, portfolio re-parses). Reset any new static per-program state there too.
4. Side effects inside an expression are lowered to `preStatements` (run before it) and `postStatements` (run at the end of the full expression). Statements emitted by an operand of `&&`/`||` must run only when that operand is evaluated (`guardShortCircuited` in `ExpressionVisitor`).
5. A local declared without an initializer inside a loop or outside `main` yields a `CAssume` carrying the variable (`getHavocked()`). c2xcfa lowers it to a havoc plus the range assume, so every re-execution gets a fresh value; a declaration that runs once keeps the backend's initial value, which explicit-state backends such as MDD rely on.
6. `CStatementVisitor` has two implementors: `StatisticsCollectorVisitor` ([CStatistics.kt](src/main/java/hu/bme/mit/theta/frontend/CStatistics.kt)) and c2xcfa's `FrontendXcfaBuilder` (through `CStatementVisitorBase`, whose defaults throw). A new statement class needs both.
7. Unsupported constructs throw `UnsupportedFrontendElementException`. Throw the subclass `RequiresByteAddressedMemoryException` only when `--memory-model bytes` can express the construct: when no memory model was requested, xcfa-cli retries under `bytes` on exactly that type.
