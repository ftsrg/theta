# xcfa/c2xcfa — notes for editing this module

Gradle module: `:theta-c2xcfa`.

- Build/tests: `./gradlew :theta-c2xcfa:build` · `./gradlew :theta-c2xcfa:test`. A change here also has to pass the canary gate (`:theta-xcfa-cli:canaryTest`, see the root [AGENTS.md](../../../AGENTS.md)).
- Read [README.md](README.md) first. It covers objects, cells, base ids and the memory models, which explain most of the surprising code here. C types and the parse context come from [c-frontend](../../frontends/c-frontend/AGENTS.md); the passes that run on the result are in [xcfa](../xcfa/AGENTS.md).

Paths below are relative to [src/main/java/hu/bme/mit/theta/c2xcfa/](src/main/java/hu/bme/mit/theta/c2xcfa/).

## Vocabulary

| Concept | Where | What |
|---|---|---|
| `getXcfaFromC` | [Utils.kt](src/main/java/hu/bme/mit/theta/c2xcfa/Utils.kt) | the entry point: parse, run `FunctionVisitor`, build with `FrontendXcfaBuilder`, then `XcfaBuilder.build()`, whose `XCFA` runs the procedure passes |
| `FrontendXcfaBuilder` | [FrontendXcfaBuilder.kt](src/main/java/hu/bme/mit/theta/c2xcfa/FrontendXcfaBuilder.kt) | a `CStatementVisitorBase<ParamPack, XcfaLocation>`: one `visit` per `CStatement`, returning the location the statement ends in. Each procedure builder gets `CPasses` |
| `CMetaData` | [CMetaData.kt](src/main/java/hu/bme/mit/theta/c2xcfa/CMetaData.kt) | the source position and text of a location or label, plus the `sourceStatements` it came from. It is a `MetaData` subclass, registered for serialization in xcfa-cli's `XcfaFiles` |
| `SourceStatement` | [SourceStatement.kt](src/main/java/hu/bme/mit/theta/c2xcfa/SourceStatement.kt) | a serialized record of one C statement (kind, spans, and a call's function and return variable), made by `SourceStatement.Registry`. The witness writers and trace concretizers read these, not the parsed `CStatement`s |

## Invariants

1. **The memory representation is the contract with every pass.** Cells, base ids, aggregate values that are their base addresses, and the three memory models are described in the README. A change to how an object is laid out or addressed changes what the xcfa passes and the analyses read.
2. **Typing goes through the wrapper, never the canonical ref.** Use `CComplexType.withType` on the expression being built. On a `decl.ref` it retypes the variable itself, so a differently typed use needs a `Pos` node (the README, and invariant 1 of c-frontend).
3. **Everything later stages need is in the XCFA or the serialized `ParseContext`.** A worker process gets the XCFA decoded from a file, without the `CStatement` tree. Keep what the witness writers or analyses read in `CMetaData`/`SourceStatement` (or another serialized field), not in transient parse state.
4. **Refuse rather than approximate.** An unsupported construct throws, and a partly modelled write havocs the object rather than leaving its old value (the README's last section).

## Testing

Most tests feed an inline C program to `getXcfaFromC` with a fresh `ParseContext`, then assert on the labels of the result (`getFlatLabels()`); `StructCopyTest` is a compact example. `TestFrontendXcfaBuilder` only checks that each program under `src/test/resources` builds. Pin a change with a test of the first kind, and with a canary fixture when the behaviour is user-visible.
