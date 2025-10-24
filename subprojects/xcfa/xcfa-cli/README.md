## Overview

This project contains an executable tool (command line) for running analyses on XCFAs.

### Related projects

* [`xcfa`](../xcfa/README.md): Classes to represent XCFAs.
* [`xcfa-analysis`](../xcfa-analysis/README.md): XCFA specific analysis modules enabling the
  algorithms to operate on them.

## Tool

First, [build](../../doc/Build.md) the projects. The runnable jar file will appear under
_build/libs/_ with the name _
theta-xcfa-cli-\<VERSION\>-all.jar_. You can simply rename it to _theta-xcfa-cli.jar_.

The tool can be run with `java -jar theta-xcfa-cli.jar [arguments]`. If no arguments are given, a
help screen is
displayed about the arguments and their possible values. For
example `java -jar theta-xcfa-cli.jar --input program.c --loglevel INFO` runs the default analysis
with logging on
the `program.c` input file.

## Configuration

<details><summary>UML Source</summary>

``` plantuml
@startuml

!theme plain
skinparam linetype ortho

interface SpecBackendConfig << interface >>
interface SpecFrontendConfig << interface >>

entity  ArgConfig << data >> {
   disable: Boolean
}
entity  BMCConfig << data >> {
   bmcSolver: String
   nonLfPath: Boolean
   validateBMCSolver: Boolean
   disable: Boolean
}
entity  BackendConfig<T> << data >> {
   inProcess: Boolean
   backend: Backend
   timeoutMs: Long
   specConfig: SpecBackendConfig
   solverHome: String
}
entity  BoundedConfig << data >> {
   maxBound: Int
   objects: Set<Config>
   bmcConfig: BMCConfig
   indConfig: InductionConfig
   itpConfig: InterpolationConfig
}
entity  CFrontendConfig << data >> {
   arithmetic: ArithmeticType
}
entity  CHCFrontendConfig << data >> {
   chcTransformation: ChcTransformation
}
entity  COutputConfig << data >> {
   useExArr: Boolean
   useRange: Boolean
   disable: Boolean
   useArr: Boolean
}
entity  CegarAbstractorConfig << data >> {
   search: Search
   maxEnum: Int
   validateAbstractionSolver: Boolean
   abstractionSolver: String
   domain: Domain
}
entity  CegarConfig << data >> {
   coi: ConeOfInfluenceMode
   refinerConfig: CegarRefinerConfig
   por: POR
   objects: Set<Config>
   initPrec: InitPrec
   abstractorConfig: CegarAbstractorConfig
   porSeed: Int
   cexMonitor: CexMonitorOptions
}
entity  CegarRefinerConfig << data >> {
   pruneStrategy: PruneStrategy
   exprSplitter: ExprSplitterOptions
   refinement: Refinement
   validateRefinementSolver: Boolean
   refinementSolver: String
}
entity  DebugConfig << data >> {
   logLevel: Level
   argdebug: Boolean
   debug: Boolean
   argToFile: Boolean
   stacktrace: Boolean
}
entity  FrontendConfig<T> << data >> {
   lbeLevel: LbeLevel
   loopUnroll: Int
   specConfig: SpecFrontendConfig
   inputType: InputType
}
entity  InductionConfig << data >> {
   indMinBound: Int
   indSolver: String
   disable: Boolean
   indFreq: Int
   validateIndSolver: Boolean
}
entity  InputConfig << data >> {
   property: ErrorDetection
   catFile: File?
   propertyFile: File?
   input: File?
   xcfaWCtx: Triple<XCFA, Collection<GraphConstraint>, ParseContext>?
   parseCtx: File?
}
entity  InterpolationConfig << data >> {
   disable: Boolean
   validateItpSolver: Boolean
   itpSolver: String
}
entity  OutputConfig << data >> {
   versionInfo: Boolean
   COutputConfig: COutputConfig
   resultFolder: File
   objects: Set<Config>
   xcfaOutputConfig: XcfaOutputConfig
   argConfig: ArgConfig
   witnessConfig: WitnessConfig
}
entity  PortfolioConfig << data >> {
   portfolio: String
}
entity  WitnessConfig << data >> {
   disable: Boolean
   validateConcretizerSolver: Boolean
   concretizerSolver: String
}
entity  XcfaConfig<F, B> << data >> {
   objects: Set<Config>
   debugConfig: DebugConfig
   inputConfig: InputConfig
   outputConfig: OutputConfig
   frontendConfig: FrontendConfig<F>
   backendConfig: BackendConfig<B>
}
entity  XcfaOutputConfig << data >> {
   disable: Boolean
}

BackendConfig         "1" *-[#595959,plain]d->  "specConfig\n1" SpecBackendConfig
BoundedConfig          -[#008200,dashed]u-^  SpecBackendConfig
BoundedConfig         "1" *-[#595959,plain]d-> "bmcConfig\n1" BMCConfig
BoundedConfig         "1" *-[#595959,plain]d-> "indConfig\n1" InductionConfig
BoundedConfig         "1" *-[#595959,plain]d-> "itpConfig\n1" InterpolationConfig
CFrontendConfig        -[#008200,dashed]u-^  SpecFrontendConfig
CHCFrontendConfig      -[#008200,dashed]u-^  SpecFrontendConfig
CegarConfig            -[#008200,dashed]u-^  SpecBackendConfig
CegarConfig           "1" *-[#595959,plain]d-> "abstractorConfig\n1" CegarAbstractorConfig
CegarConfig           "1" *-[#595959,plain]d-> "refinerConfig\n1" CegarRefinerConfig
FrontendConfig        "1" *-[#595959,plain]d-> "specConfig\n1" SpecFrontendConfig
OutputConfig          "1" *-[#595959,plain]d-> "argConfig\n1" ArgConfig
OutputConfig          "1" *-[#595959,plain]d-> "cOutputConfig\n1" COutputConfig
OutputConfig          "1" *-[#595959,plain]d-> "witnessConfig\n1" WitnessConfig
OutputConfig          "1" *-[#595959,plain]d-> "xcfaOutputConfig\n1" XcfaOutputConfig
PortfolioConfig        -[#008200,dashed]u-^  SpecBackendConfig
XcfaConfig            "1" *-[#595959,plain]d-> "backendConfig\n1" BackendConfig
XcfaConfig            "1" *-[#595959,plain]d-> "debugConfig\n1" DebugConfig
XcfaConfig            "1" *-[#595959,plain]d-> "frontendConfig\n1" FrontendConfig
XcfaConfig            "1" *-[#595959,plain]d-> "inputConfig\n1" InputConfig
XcfaConfig            "1" *-[#595959,plain]d-> "outputConfig\n1" OutputConfig
@enduml
```

</details>

![](config_diagram.svg)
