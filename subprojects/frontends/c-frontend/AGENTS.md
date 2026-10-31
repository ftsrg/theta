# frontends/c-frontend — notes for editing this module

Gradle module: `:theta-c-frontend`. Parses preprocessed C (ANTLR grammar `src/main/antlr/C.g4`) into the intermediate model under `transformation/model/statements` (`CProgram`, `CFunction`, `CAssignment`, …). It does not build any formalism; [c2xcfa](../../xcfa/c2xcfa/README.md) turns the model into an XCFA, and its README explains the memory representation (cells, base ids, memory models) that most of this module's lowering targets.

## Pipeline

1. **`parseTypeAware`** ([CParseUtils.kt](src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/CParseUtils.kt)) — two parses. The first one is permissive and only harvests typedef names, following `#include`s of the bundled headers. The second accepts only those names as types (`parser.typedefNames`, `permissiveTypeNames = false` in `C.g4`), with `BailErrorStrategy`. The second parse has no fallback on purpose; a file it rejects is an error.
2. **`FunctionVisitor.visitCompilationUnit`** — typedefs (`TypedefVisitor`), then the reachable global declarations (`GlobalDeclUsageVisitor`: only what `main` transitively uses is processed), then `SourceTraitCollector` and, under `--arithmetic efficient`, `BitwiseChecker` picks `integer` or `bitvector` and sets `arithmeticAutoSelected`. Function names are created up front, before any global initializer is visited.
3. **`FunctionVisitor`** (statements, declarations), **`ExpressionVisitor`** (expressions, `__builtin_*`), and **`TypeVisitor`** / **`DeclarationVisitor`** (types, declarators) build the model.

`ParseContext` is the shared state for one file: architecture, arithmetic, memory model, the `FrontendMetadata` store, and the object tables (atomic cells, accessed struct members, static object parents). Use a fresh `ParseContext` per parse.

## Invariants / gotchas

1. **`cType` metadata is identity-keyed** (`FrontendMetadata` keys it on `System.identityHashCode`). An expression you rebuild has no C type until you `create(expr, "cType", t)` it again. Re-stamp it; do not derive a C type back from an SMT sort.
2. **Two arithmetic backends.** `types/complex/visitors/{integer,bitvector}` each implement the cast, limit, null/unit value and SMT-type visitors. A new `CComplexType`, or a change to one's semantics, has to be made in both.
3. **Headers are bundled, not read from disk.** `stdlib/HeaderFile.kt` maps a header name to a Kotlin string of declarations. Add a new header there and to the enum; an unknown `#include <x>` expands to nothing.
4. **Unsupported constructs throw.** Use `UnsupportedFrontendElementException`, or `RequiresByteAddressedMemoryException` when the construct needs byte cells. `xcfa-cli` catches the latter and rebuilds under `--memory-model bytes` (only when the model was not set explicitly). Do not model something approximately to avoid throwing (see "When in doubt, refuse" in the c2xcfa README).
5. **Stack objects go through `alloca`.** Local aggregates and VLAs become `alloca` calls, and leaving a block emits `FunctionVisitor.SCOPE_END` (`__theta_scope_end`). Both are lowered by `AllocaFunctionPass` in `:theta-xcfa`. A VLA size is in cells, not bytes.

## Tests

- `./gradlew :theta-c-frontend:test`: unit tests under `src/test/kotlin` parse a source string with `parseTypeAware(...).accept(FunctionVisitor(ParseContext(), NullLogger.getInstance()))` and inspect the `CProgram` or `ParseContext`.
- End-to-end behaviour is covered from c2xcfa (`getXcfaFromC` tests) and by the `xcfa-cli` fixtures (`:theta-xcfa-cli:fixtureTest`). A frontend change needs a fixture there that fails before the change; see the root `AGENTS.md`.
