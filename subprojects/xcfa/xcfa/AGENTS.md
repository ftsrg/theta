# xcfa/xcfa — notes for editing this module

Gradle module: `:theta-xcfa`.

- Build/tests: `./gradlew :theta-xcfa:build` · `./gradlew :theta-xcfa:test`. A pass change also has to pass the canary gate (`:theta-xcfa-cli:canaryTest`, see the root [AGENTS.md](../../../AGENTS.md)).
- Model overview: [README.md](README.md). The C pass pipeline phase by phase, and the rules every pass follows: [passes/README.md](src/main/java/hu/bme/mit/theta/xcfa/passes/README.md). Read it before adding or moving a pass.

Paths below are relative to [src/main/java/hu/bme/mit/theta/xcfa/](src/main/java/hu/bme/mit/theta/xcfa/).

## Vocabulary

| Concept | Where | What |
|---|---|---|
| `XcfaBuilder`, `XcfaProcedureBuilder` | [model/Builders.kt](src/main/java/hu/bme/mit/theta/xcfa/model/Builders.kt) | the mutable form that frontends and passes work on; each procedure builder carries its `ProcedurePassManager` |
| `XCFA` | [model/XCFA.kt](src/main/java/hu/bme/mit/theta/xcfa/model/XCFA.kt) | its constructor runs every builder's passes, phase by phase, then builds the immutable `XcfaProcedure`s |
| `XcfaLabel` | [model/XcfaLabel.kt](src/main/java/hu/bme/mit/theta/xcfa/model/XcfaLabel.kt) | sealed: `StmtLabel`, `InvokeLabel`/`ReturnLabel`, `StartLabel`/`JoinLabel`, fence, mutex and rwlock labels, `SequenceLabel`/`NondetLabel`, `NopLabel` |
| `ProcedurePass`, `ProcedurePassManager` | [passes/](src/main/java/hu/bme/mit/theta/xcfa/passes/) | one rewrite of one procedure builder; a manager fixes the order (`CPasses` for C) |
| `MetaData` | [model/MetaData.kt](src/main/java/hu/bme/mit/theta/xcfa/model/MetaData.kt) | source information on locations and labels; frontends subclass it (c2xcfa's `CMetaData`) |
| serialization | [model/serialization/](src/main/java/hu/bme/mit/theta/xcfa/model/serialization/) | `XcfaSerialization` writes an XCFA with its parse context: `XcfaSurrogate` for the XCFA itself, `Session` for the object table |

## Invariants

1. **The pass order is part of the contract.** passes/README.md gives the reason for each constraint. Outside a manager, run a pass through `ProcedurePass.runChecked`, which checks that the procedure is still well-formed.
2. **Labels arrive normalized.** After `NormalizePass` an edge label is a `SequenceLabel` of flat labels, and later passes and the analyses rely on that shape (`getFlatLabels()`). Several passes assert the `metaData["deterministic"]` flag that `DeterministicPass` sets.
3. **Passes see the C-type wrappers; analyses do not.** A pass matching on an expression class looks through `TraceableWrapperExpr` (`unwrapTraceable()`). xcfa-cli hands checkers `XCFA.withoutTraceability()` ([utils/TraceabilityUtils.kt](src/main/java/hu/bme/mit/theta/xcfa/utils/TraceabilityUtils.kt)).
4. **Serialization coverage is enforced by tests.** `XcfaLabel` is a sealed `@Serializable` hierarchy, and `XcfaSerializationCoverageTest.everyLabelIsInTheSealedSerializer` fails for a label left out of it. A new field on `XCFA` goes into `XcfaSurrogate.COVERED_FIELDS` (serialized) or `DERIVED_FIELDS` (rebuilt); the same test compares those sets against the class. In a `@Serializable` class, a body property with a backing field is serialized unless it is `@Transient`.
5. **A decoded XCFA is not re-optimized.** `XcfaSurrogate.toXcfa` rebuilds through builders with an empty `ProcedurePassManager`, so the passes run once, before encoding.
6. **No reflection at runtime.** The object table finds classes and their serializers in `XcfaSerialization.tableClasses` (core's, c-frontend's and this module's lists). The output starts with a format hash that a build whose serialized shapes differ refuses instead of misreading. `computeFormatHash` loads every serialized class, so encode and decode are given its result; xcfa-cli computes it when building.

## Change recipes

**New pass:** implement `ProcedurePass` (copy the closest sibling). Place it in the managers that need it, at a position justified against the passes/README table, and add a row there. Test it in `src/test/.../passes/`: `PassTests` runs a pass on a small builder and compares the result with an expected builder.

**New label:** add a `@Serializable` subclass in `model/XcfaLabel.kt`, then handle it where labels are interpreted. That includes `getFlatLabels` and the other helpers in `utils/`, `XcfaToC`, and xcfa-analysis (`XcfaAnalysis`, `XcfaState`, the data-race and OC encodings). Grep for an existing sibling such as `is FenceLabel` to find them.

**New expression defined in this module** (like `MallocLitExpr` in [utils/PointerUtils.kt](src/main/java/hu/bme/mit/theta/xcfa/utils/PointerUtils.kt)): extend core's `ForeignExpr`/`ForeignLitExpr`, make it `@Serializable`, and list it in `XcfaSerialization.tableClasses`. `XcfaSerializationCoverageTest.everyForeignExpressionIsATableClass` checks it.
