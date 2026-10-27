# xcfa/xcfa-cli — notes for editing this module

Gradle module: `:theta-xcfa-cli`; main class `hu.bme.mit.theta.xcfa.cli.XcfaCli`.

- Build/tests: `./gradlew :theta-xcfa-cli:test` (unit and CLI tests; the suites are excluded) · fat jar `:theta-xcfa-cli:shadowJar` · distribution `buildArchiveTheta-svcomp` (native: needs `-Ptheta.graalvm`, see [README.md](README.md#native-executable)). The canary gate `:theta-xcfa-cli:canaryTest` (with `fixtureTest`) runs against the built distribution: [canaries/README.md](canaries/README.md).
- Options and the configuration entities: [README.md](README.md). Running and smoke-testing locally: root [AGENTS.md](../../../AGENTS.md).

Paths below are relative to [src/main/java/hu/bme/mit/theta/xcfa/cli/](src/main/java/hu/bme/mit/theta/xcfa/cli/).

## Vocabulary

| Concept | Where | What |
|---|---|---|
| `XcfaConfig` | [params/XcfaConfig.kt](src/main/java/hu/bme/mit/theta/xcfa/cli/params/XcfaConfig.kt) | every option, grouped (`InputConfig`, `FrontendConfig`, `BackendConfig`, `OutputConfig`, `DebugConfig`, ...); fields are JCommander `@Parameter`s in `@Serializable` classes |
| `runConfig` | [ExecuteConfig.kt](src/main/java/hu/bme/mit/theta/xcfa/cli/ExecuteConfig.kt) | one run: options to static pass switches, frontend (with the `flat`/`bytes` memory-model fallbacks), pre-analysis output, backend, post-analysis output |
| checkers | [checkers/](src/main/java/hu/bme/mit/theta/xcfa/cli/checkers/) | `ConfigToChecker.kt` turns a config into a checker; `InProcessChecker` runs a configuration in a worker JVM |
| portfolios | [portfolio/](src/main/java/hu/bme/mit/theta/xcfa/cli/portfolio/) | state machines over configurations (`stm.kt`); `ConfigToPortfolio.kt` maps `--portfolio` names (`STABLE` is `complex27`) |
| `XcfaFiles` | [serialization/XcfaFiles.kt](src/main/java/hu/bme/mit/theta/xcfa/cli/serialization/XcfaFiles.kt) | a built XCFA as ProtoBuf (worker handover, `--xcfa-file`) or JSON (`xcfa.json`); its `formatHash` is a resource that the build's `xcfaFormatHash` task writes |
| witnesses | [utils/](src/main/java/hu/bme/mit/theta/xcfa/cli/utils/)`*WitnessWriter.kt`, [witnesstransformation/](src/main/java/hu/bme/mit/theta/xcfa/cli/witnesstransformation/) | write, apply and validate witnesses, reading `CMetaData.sourceStatements` |

## Invariants

1. **A worker JVM gets its configuration as JSON.** `InProcessChecker` serializes the `XcfaConfig` and starts `XcfaCli -c <config.json>`. A new option has to survive that round trip (`XcfaConfigSerializationTest`); one that only makes sense inside the JVM is `@Transient`, like `InputConfig.xcfaWCtx` and `builtXcfa`.
2. **Workers reuse the XCFA the portfolio built.** `getPortfolioChecker` stores it as `InputConfig.builtXcfa`, tagged with the frontend config's string. `InProcessChecker` writes it for a worker whose frontend config matches, and the worker loads it through `--xcfa-file` without parsing or running passes. A configuration that changes a frontend option parses again.
3. **Pass switches are static.** `propagateInputOptions` sets pass flags from the config before the frontend runs (`LbePass.defaultLevel`, `StaticCoiPass.enabled`, `MemsafetyPass.enabled`, ...), so a JVM handles one input at a time.
4. **The printed markers are an interface.** The suites and `InProcessChecker` (which reads a worker's verdict from its stdout) match `ParsingResult Success`, `Frontend failed!` and `(SafetyResult ...)`. Don't reword them; a failure that should fail the parse gate must print `Frontend failed!`.
5. **An explicit option is never overridden.** The memory-model and arithmetic fallbacks in `frontend()` apply only to defaults (its KDoc and the c2xcfa README).
6. **The format hash is built, not computed.** Computing it loads every serialized class, which would slow down every worker start. Run from a Gradle-built classpath: without the resource, encoding and decoding fail. `XcfaSerializationTest.theBuiltFormatHashIsCurrent` checks that the resource is up to date.
7. **Reflection and JNI have to be declared for the native image.** Only JCommander (the options) and the solvers' native code (callbacks into their Java bindings) need them, and [nativeimage/ThetaNativeImageFeature.kt](src/main/java/hu/bme/mit/theta/xcfa/cli/nativeimage/ThetaNativeImageFeature.kt) registers both by rule: everything in `params`, every JCommander converter, the binding packages it lists. A new option needs nothing; a new native library needs its binding package listed; anything else reflective (prefer not to) needs an entry under `src/main/resources/META-INF/native-image/`. A missing one only fails in the native image, which is what the SV-COMP archives ship and what the canary gate runs; unit tests on the JVM do not catch it.

## Change recipes

**New option:** add an `@Parameter` field with a default to the right group in `params/XcfaConfig.kt`, and update that entity in README.md.

**New backend:** add a `Backend` value ([params/ParamValues.kt](src/main/java/hu/bme/mit/theta/xcfa/cli/params/ParamValues.kt)), a `ConfigTo<X>Checker.kt`, and its cases in `ConfigToChecker.kt`.

**New portfolio:** a file under `portfolio/` that builds an `STM`, and its name in `ConfigToPortfolio.kt`.

**Anything that changes what is serialized** (model classes, `ParseContext`, metadata): run the gate with `-Ptheta.canary.extraArgs=--serialization-roundtrip`. Every task then encodes its XCFA, decodes it, checks that it encodes to the same bytes, and continues on the decoded one.
