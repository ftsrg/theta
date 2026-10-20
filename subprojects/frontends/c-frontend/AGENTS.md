# frontends/c-frontend — notes for editing this module

Gradle module: `:theta-c-frontend`.

- Build/tests: `./gradlew :theta-c-frontend:build` · `./gradlew :theta-c-frontend:test` (unit tests in `src/test/kotlin`). Most behaviour is only observable once c2xcfa has built an XCFA, so a change here also has to pass `:theta-c2xcfa:test` and the canary gate (`:theta-xcfa-cli:canaryTest`, see [canaries/README.md](../../xcfa/xcfa-cli/canaries/README.md)).
- Overview: [README.md](README.md) here; how the frontend's types become memory cells and base ids: [c2xcfa/README.md](../../xcfa/c2xcfa/README.md).

Paths below are relative to [src/main/java/hu/bme/mit/theta/frontend/](src/main/java/hu/bme/mit/theta/frontend/).

## Vocabulary

| Concept | Where | What |
|---|---|---|
| grammar | [src/main/antlr/C.g4](src/main/antlr/C.g4) | parsed by `parseTypeAware` ([transformation/grammar/CParseUtils.kt](src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/CParseUtils.kt)) |
| visitors | [transformation/grammar/](src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/) | `FunctionVisitor` (statements, the `CProgram`), `ExpressionVisitor` (C expressions to core `Expr`s), `TypeVisitor`/`DeclarationVisitor`; `preprocess/` collects typedefs and arithmetic/source traits first |
| IM | [transformation/model/statements/](src/main/java/hu/bme/mit/theta/frontend/transformation/model/statements/) | the `CStatement` tree, consumed through `CStatementVisitorBase` (c2xcfa's `FrontendXcfaBuilder`) |
| `CSimpleType` | [transformation/model/types/simple/](src/main/java/hu/bme/mit/theta/frontend/transformation/model/types/simple/) | the type as declared (qualifiers, pointer levels, `Struct`, `Typedef`); `actualType` gives its `CComplexType` |
| `CComplexType` | [transformation/model/types/complex/](src/main/java/hu/bme/mit/theta/frontend/transformation/model/types/complex/) | the type an expression has: width, `castTo`, `smtType`, literals; a sealed Kotlin hierarchy |
| `ParseContext` | [ParseContext.kt](src/main/java/hu/bme/mit/theta/frontend/ParseContext.kt) | one parse's configuration (architecture, arithmetic, memory model) and what the parse found |
| `ArchitectureConfig` | [transformation/ArchitectureConfig.java](src/main/java/hu/bme/mit/theta/frontend/transformation/ArchitectureConfig.java) | `ArchitectureType`, `ArithmeticType`, `MemoryModelType`, and the per-arithmetic visitor factories |

## Invariants

1. **A C type is attached to an expression, not derived from it.** `CComplexType.withType` wraps the expression in a `TraceableWrapperExpr`; `getKnownType` reads it back, and `getType` falls back to guessing from the SMT sort, which cannot tell `struct S *` from `unsigned int`. A variable's canonical `ref` is never wrapped: `withType(decl.ref, T)` sets `VarDecl.traceability`, i.e. retypes the variable, so a use typed differently goes through a `Pos` node. Matching on an expression class must look through the wrapper (`unwrapTraceable()`).
2. **Two arithmetics, two visitor sets.** `ArchitectureConfig.get*Visitor(parseContext)` returns the visitor from `types/complex/visitors/bitvector/` when `parseContext.arithmetic` is `bitvector` and from `visitors/integer/` otherwise (`FunctionVisitor` resolves `efficient` before it matters). A change to what a type means (casts, limits, literals, SMT type) is made in both sets.
3. **Nothing is global to the JVM.** The frontend runs more than once per JVM (the memory-model fallbacks in xcfa-cli rebuild it), so per-program state lives in `ParseContext`; struct and union tags, for example, resolve through `ParseContext.definedStructs`.
4. **`ParseContext` is serialized with the XCFA.** A new field is written by default. Mark state that only parsing (or c2xcfa's build) reads `@Transient`: `XcfaSerializationCoverageTest` in xcfa lists the transient fields and fails until you place the new one.
5. **C types are serialized model classes.** A concrete `CComplexType` is `@Serializable`, with `@Transient override val origin` and `@Serializable(with = ParseContextSerializer::class) override val parseContext`. Every property holding a C type names `@Serializable(with = CComplexTypeReferenceSerializer::class)`, so the type is written once and referred to by index. Each class is listed in [FrontendTableClasses.kt](src/main/java/hu/bme/mit/theta/frontend/FrontendTableClasses.kt), which spares the object table any reflection. `XcfaSerializationCoverageTest.everyCTypeIsWrittenOnceAndReferredTo` checks both.
6. **Record facts as typed fields.** A new fact belongs on `ParseContext`, a C type or `VarDecl.traceability`, not under a `FrontendMetadata` key: metadata is keyed by object identity, which neither a rewrite nor serialization keeps.
7. **Unsupported means refused.** Throw `UnsupportedFrontendElementException` instead of modelling a construct approximately (see "When in doubt, refuse" in the c2xcfa README).

## Change recipes

**New C type class:** add it under `types/complex/` (the hierarchy is sealed, so it stays in that package), make it serializable as in invariant 5, and list it in `FrontendTableClasses`. Then add a `visit` overload to `CComplexTypeVisitor` that delegates to the supertype's overload, as the existing ones do, and implement it in every visitor of both sets that must treat it differently.

**New `ParseContext` field:** decide whether later stages read it. If they do, it is serialized; otherwise it is `@Transient` and goes into the coverage test's set.

**New grammar or visitor capability:** add a program to `xcfa-cli/canaries/fixtures/` that fails before the change and passes after, with its `fixtures.tsv` row (root [AGENTS.md](../../../AGENTS.md)).
